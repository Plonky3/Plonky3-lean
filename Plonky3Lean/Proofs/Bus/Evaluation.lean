module

public import Plonky3Lean.Proofs.Bus.Plan
public import Plonky3Lean.Proofs.MultilinearUtil.Mle

@[expose] public section

/-!
# The leaf factor of a declaration

A declaration is flattened into nodes, each operand before its user.

One forward pass evaluates them.

Its factor is the offset minus the fingerprint of its padded tuple.

Its activation interpolates that factor with the identity:

```text
    factor = 1 + ((gamma - fingerprint(tuple, r)) - 1) s      (s = 1 always active)
```

The identity bits are folded into the offset once, so the pass only sums the payload slots.
-/

namespace Plonky3Lean.Proofs.Bus

open p3_bus.evaluation.mirror p3_bus.plan.mirror p3_bus.mirror p3_air.symbolic.mirror

set_option linter.unusedSectionVars false

variable {F EF : Type} [Field F] [Field EF] [Algebra F EF]

/-- The value of a symbolic expression at a point.

It is none for an access no opening answers. -/
def exprValue (values : BusEvaluation F EF) : SymbolicExpression F → Option EF
  | .Leaf (.Variable v) => match v.entry with
    | .Main 0 => values.main[v.index]?
    | .Preprocessed 0 => values.preprocessed[v.index]?
    | .Public => values.«public»[v.index]?.map (algebraMap F EF)
    | .Periodic => values.periodic[v.index]?
    | _ => none
  | .Leaf .IsFirstRow => some values.is_first_row
  | .Leaf .IsLastRow => some values.is_last_row
  | .Leaf .IsTransition => some values.is_transition
  | .Leaf (.Constant c) => some (algebraMap F EF c)
  | .Add x y _ => do pure ((← exprValue values x) + (← exprValue values y))
  | .Sub x y _ => do pure ((← exprValue values x) - (← exprValue values y))
  | .Mul x y _ => do pure ((← exprValue values x) * (← exprValue values y))
  | .Neg x _ => do pure (-(← exprValue values x))

/-- The forward pass over a node list. -/
def evalNodes (values : BusEvaluation F EF) (nodes : List (BusNode F)) :
    Except BusEvaluationError (List EF) :=
  nodes.foldlM (fun scratch node => do pure (scratch ++ [← nodeValue values scratch node])) []

theorem evalNodes_snoc (values : BusEvaluation F EF) (nodes : List (BusNode F)) (n : BusNode F)
    {sc : List EF} (h : evalNodes values nodes = .ok sc) :
    evalNodes values (nodes ++ [n]) = (nodeValue values sc n).map (sc ++ [·]) := by
  unfold evalNodes at h ⊢
  rw [List.foldlM_append, h]
  simp only [bind, Except.bind, List.foldlM_cons, List.foldlM_nil, pure, Except.pure]
  cases nodeValue values sc n <;> rfl

theorem length_evalNodes {values : BusEvaluation F EF} :
    ∀ {nodes : List (BusNode F)} {sc : List EF}, evalNodes values nodes = .ok sc →
      sc.length = nodes.length := by
  intro nodes
  induction nodes using List.reverseRecOn with
  | nil => intro sc h; simp [evalNodes, pure, Except.pure] at h; subst h; rfl
  | append_singleton nodes n ih =>
    intro sc h
    unfold evalNodes at h
    rw [List.foldlM_append] at h
    cases hp : evalNodes values nodes with
    | error e => unfold evalNodes at hp; rw [hp] at h; cases h
    | ok sc₀ =>
      unfold evalNodes at hp
      rw [hp] at h
      simp only [bind, Except.bind, List.foldlM_cons, List.foldlM_nil, pure, Except.pure] at h
      cases hv : nodeValue values sc₀ n with
      | error e => rw [hv] at h; cases h
      | ok v =>
        rw [hv] at h; cases h
        simp [ih hp]

theorem nodeValue_leaf (values : BusEvaluation F EF) (sc : List EF) {l : BaseLeaf F}
    {n : BusNode F} {v : EF} (hc : compile_leaf l = .ok n) (hv : exprValue values (.Leaf l) = some v) :
    nodeValue values sc n = .ok v := by
  cases l with
  | Variable var =>
    rcases var with ⟨entry, idx⟩
    cases entry with
    | Main o =>
      cases o <;> simp_all [compile_leaf, exprValue]
      subst hc; simp [nodeValue, hv]
    | Preprocessed o =>
      cases o <;> simp_all [compile_leaf, exprValue]
      subst hc; simp [nodeValue, hv]
    | Public =>
      simp only [compile_leaf, Except.ok.injEq] at hc; subst hc
      simp only [exprValue, Option.map_eq_some_iff] at hv
      obtain ⟨a, ha, rfl⟩ := hv
      simp [nodeValue, ha]
    | Periodic =>
      simp only [compile_leaf, Except.ok.injEq] at hc; subst hc
      simp only [exprValue] at hv
      simp [nodeValue, hv]
  | IsFirstRow => simp_all [compile_leaf, exprValue]; subst hc; simp [nodeValue, hv]
  | IsLastRow => simp_all [compile_leaf, exprValue]; subst hc; simp [nodeValue, hv]
  | IsTransition => simp_all [compile_leaf, exprValue]; subst hc; simp [nodeValue, hv]
  | Constant c => simp_all [compile_leaf, exprValue]; subst hc; simp [nodeValue, hv]

/-- The pass after appending one binary node over two earlier operands. -/
theorem eval_snoc_bin (values : BusEvaluation F EF) {nodes : List (BusNode F)} {sc : List EF}
    (h : evalNodes values nodes = .ok sc) (n : BusNode F) (v : EF)
    (hn : nodeValue values sc n = .ok v) :
    evalNodes values (nodes ++ [n]) = .ok (sc ++ [v]) := by
  rw [evalNodes_snoc values nodes n h, hn]; rfl

theorem getD_append_left {l l' : List EF} {i : ℕ} (h : i < l.length) :
    (l ++ l').getD i 0 = l.getD i 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

/-- **Flattening is faithful.**

Compiling an expression after some evaluated nodes appends new nodes.

Their pass extends the earlier values.

It puts the expression's value at the returned position. -/
theorem compile_eval (values : BusEvaluation F EF) : ∀ (e : SymbolicExpression F)
    (nodes nodes' : List (BusNode F)) (i : ℕ) (sc : List EF) (v : EF),
    compile_expression nodes e = .ok (nodes', i) → evalNodes values nodes = .ok sc →
    exprValue values e = some v →
    ∃ sc', evalNodes values nodes' = .ok sc' ∧ sc <+: sc' ∧ i < sc'.length ∧ sc'.getD i 0 = v
  | .Leaf l, nodes, nodes', i, sc, v, hc, he, hv => by
    simp only [compile_expression, bind, Except.bind] at hc
    cases hl : compile_leaf l with
    | error err => rw [hl] at hc; cases hc
    | ok n =>
      rw [hl] at hc
      simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hc
      obtain ⟨rfl, rfl⟩ := hc
      have hlen := length_evalNodes he
      refine ⟨sc ++ [v], eval_snoc_bin values he n v (nodeValue_leaf values sc hl hv),
        List.prefix_append _ _, by simp [hlen], by simp [List.getD_eq_getElem?_getD, hlen]⟩
  | .Add x y _, nodes, nodes', i, sc, v, hc, he, hv => by
    simp only [compile_expression] at hc
    obtain ⟨⟨n1, ix⟩, h1, hc⟩ := except_bind_ok hc
    obtain ⟨⟨n2, iy⟩, h2, hc⟩ := except_bind_ok hc
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hc
    obtain ⟨rfl, rfl⟩ := hc
    simp only [exprValue, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at hv
    obtain ⟨vx, hvx, vy, hvy, rfl⟩ := hv
    obtain ⟨sc1, e1, p1, l1, g1⟩ := compile_eval values x nodes n1 ix sc vx h1 he hvx
    obtain ⟨sc2, e2, p2, l2, g2⟩ := compile_eval values y n1 n2 iy sc1 vy h2 e1 hvy
    have gx : sc2.getD ix 0 = vx := by
      obtain ⟨t, rfl⟩ := p2; rw [getD_append_left l1, g1]
    have hlen := length_evalNodes e2
    refine ⟨sc2 ++ [(vx + vy)], eval_snoc_bin values e2 _ _ (by simp only [nodeValue, gx, g2]),
      p1.trans (p2.trans (List.prefix_append _ _)), by simp [hlen],
      by simp [List.getD_eq_getElem?_getD, hlen]⟩
  | .Sub x y _, nodes, nodes', i, sc, v, hc, he, hv => by
    simp only [compile_expression] at hc
    obtain ⟨⟨n1, ix⟩, h1, hc⟩ := except_bind_ok hc
    obtain ⟨⟨n2, iy⟩, h2, hc⟩ := except_bind_ok hc
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hc
    obtain ⟨rfl, rfl⟩ := hc
    simp only [exprValue, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at hv
    obtain ⟨vx, hvx, vy, hvy, rfl⟩ := hv
    obtain ⟨sc1, e1, p1, l1, g1⟩ := compile_eval values x nodes n1 ix sc vx h1 he hvx
    obtain ⟨sc2, e2, p2, l2, g2⟩ := compile_eval values y n1 n2 iy sc1 vy h2 e1 hvy
    have gx : sc2.getD ix 0 = vx := by
      obtain ⟨t, rfl⟩ := p2; rw [getD_append_left l1, g1]
    have hlen := length_evalNodes e2
    refine ⟨sc2 ++ [(vx - vy)], eval_snoc_bin values e2 _ _ (by simp only [nodeValue, gx, g2]),
      p1.trans (p2.trans (List.prefix_append _ _)), by simp [hlen],
      by simp [List.getD_eq_getElem?_getD, hlen]⟩
  | .Mul x y _, nodes, nodes', i, sc, v, hc, he, hv => by
    simp only [compile_expression] at hc
    obtain ⟨⟨n1, ix⟩, h1, hc⟩ := except_bind_ok hc
    obtain ⟨⟨n2, iy⟩, h2, hc⟩ := except_bind_ok hc
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hc
    obtain ⟨rfl, rfl⟩ := hc
    simp only [exprValue, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at hv
    obtain ⟨vx, hvx, vy, hvy, rfl⟩ := hv
    obtain ⟨sc1, e1, p1, l1, g1⟩ := compile_eval values x nodes n1 ix sc vx h1 he hvx
    obtain ⟨sc2, e2, p2, l2, g2⟩ := compile_eval values y n1 n2 iy sc1 vy h2 e1 hvy
    have gx : sc2.getD ix 0 = vx := by
      obtain ⟨t, rfl⟩ := p2; rw [getD_append_left l1, g1]
    have hlen := length_evalNodes e2
    refine ⟨sc2 ++ [(vx * vy)], eval_snoc_bin values e2 _ _ (by simp only [nodeValue, gx, g2]),
      p1.trans (p2.trans (List.prefix_append _ _)), by simp [hlen],
      by simp [List.getD_eq_getElem?_getD, hlen]⟩
  | .Neg x _, nodes, nodes', i, sc, v, hc, he, hv => by
    simp only [compile_expression] at hc
    obtain ⟨⟨n1, ix⟩, h1, hc⟩ := except_bind_ok hc
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hc
    obtain ⟨rfl, rfl⟩ := hc
    simp only [exprValue, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at hv
    obtain ⟨vx, hvx, rfl⟩ := hv
    obtain ⟨sc1, e1, p1, l1, g1⟩ := compile_eval values x nodes n1 ix sc vx h1 he hvx
    have hlen := length_evalNodes e1
    refine ⟨sc1 ++ [-vx], eval_snoc_bin values e1 _ _ (by simp only [nodeValue, g1]),
      p1.trans (List.prefix_append _ _), by simp [hlen],
      by simp [List.getD_eq_getElem?_getD, hlen]⟩

/-- Compiling the fields in order puts each field's value at its recorded position. -/
theorem compile_fields (values : BusEvaluation F EF) :
    ∀ (fields : List (SymbolicExpression F)) (acc : List (BusNode F) × List ℕ) (sc : List EF)
      (vals : List EF) (out : List (BusNode F) × List ℕ),
    evalNodes values acc.1 = .ok sc → fields.mapM (exprValue values) = some vals →
    fields.foldlM (fun (acc : List (BusNode F) × List ℕ) e => do
      let (nodes, i) ← compile_expression acc.1 e
      pure (nodes, acc.2 ++ [i])) acc = .ok out →
    ∃ sc', evalNodes values out.1 = .ok sc' ∧ sc <+: sc' ∧ out.2.length = acc.2.length + fields.length ∧
      out.2.take acc.2.length = acc.2 ∧
      ∀ k, k < fields.length → acc.2.length + k < out.2.length ∧
        out.2.getD (acc.2.length + k) 0 < sc'.length ∧
        sc'.getD (out.2.getD (acc.2.length + k) 0) 0 = vals.getD k 0
  | [], acc, sc, vals, out, he, _, hf => by
    simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at hf; subst hf
    exact ⟨sc, he, List.prefix_rfl, by simp, by simp, fun k hk => by simp at hk⟩
  | e :: fields, acc, sc, vals, out, he, hv, hf => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at hv
    obtain ⟨v, hv1, vs, hvs, rfl⟩ := hv
    rw [List.foldlM_cons] at hf
    obtain ⟨acc', h1, hf⟩ := except_bind_ok hf
    obtain ⟨⟨n1, i1⟩, hc, h1⟩ := except_bind_ok h1
    simp only [pure, Except.pure, Except.ok.injEq] at h1; subst h1
    obtain ⟨sc1, e1, p1, l1, g1⟩ := compile_eval values e acc.1 n1 i1 sc v hc he hv1
    obtain ⟨sc2, e2, p2, hlen2, htake2, hk2⟩ := compile_fields values fields (n1, acc.2 ++ [i1]) sc1
      vs out e1 hvs hf
    simp only [List.length_append, List.length_singleton] at hlen2 htake2 hk2
    refine ⟨sc2, e2, p1.trans p2, by simp [hlen2]; omega, ?_, fun k hk => ?_⟩
    · have := congrArg (List.take acc.2.length) htake2
      rwa [List.take_take, min_eq_left (by omega), List.take_left'] at this
    · rcases k with _ | k
      · have hi : out.2.getD acc.2.length 0 = i1 := by
          have := congrArg (fun l => l.getD acc.2.length 0) htake2
          simpa [List.getD_eq_getElem?_getD, List.getElem?_take] using this
        rw [Nat.add_zero, hi]
        refine ⟨by omega, by obtain ⟨t, rfl⟩ := p2; simp; omega, ?_⟩
        obtain ⟨t, rfl⟩ := p2; rw [getD_append_left l1, g1]; simp
      · obtain ⟨a, b, c⟩ := hk2 k (by simpa using hk)
        refine ⟨by omega, by rw [show acc.2.length + (k + 1) = acc.2.length + 1 + k by omega]; exact b,
          ?_⟩
        rw [show acc.2.length + (k + 1) = acc.2.length + 1 + k by omega, c]; simp

open Finset in
/-- The slots of a tuple split into the payload and the identity bits. -/
theorem slot_sum_split {p : BusPlan} (hp : LayoutWF p) {b : ℕ} (hb : b < p.domains.length)
    (vals weights : List EF) :
    ∑ slot ∈ range p.fingerprint_width, weights.getD slot 0 * slotValue vals (p.tuple_slot b slot) =
      ∑ k ∈ range p.domains[b].payload_width, weights.getD k 0 * vals.getD k 0 +
      ∑ slot ∈ range p.fingerprint_width,
        if p.tuple_slot b slot = some (.DomainBit true) then weights.getD slot 0 else 0 := by
  have hw := hp.width _ (List.getElem_mem hb)
  have hfw : p.domains[b].payload_width ≤ p.fingerprint_width := by
    have := hp.logical; have := hp.fingerprint; omega
  rw [← sum_range_add_sum_Ico _ hfw, ← sum_range_add_sum_Ico (fun slot =>
    if p.tuple_slot b slot = some (.DomainBit true) then weights.getD slot 0 else 0) hfw]
  have h1 : ∑ k ∈ range p.domains[b].payload_width,
      weights.getD k 0 * slotValue vals (p.tuple_slot b k) =
      ∑ k ∈ range p.domains[b].payload_width, weights.getD k 0 * vals.getD k 0 :=
    sum_congr rfl fun k hk => by rw [tuple_slot_payload hb hfw (mem_range.1 hk)]; rfl
  have h2 : ∑ k ∈ range p.domains[b].payload_width,
      (if p.tuple_slot b k = some (.DomainBit true) then weights.getD k 0 else 0) = 0 :=
    sum_eq_zero fun k hk => by rw [tuple_slot_payload hb hfw (mem_range.1 hk)]; simp
  have h3 : ∑ k ∈ Ico p.domains[b].payload_width p.fingerprint_width,
      weights.getD k 0 * slotValue vals (p.tuple_slot b k) =
      ∑ k ∈ Ico p.domains[b].payload_width p.fingerprint_width,
        (if p.tuple_slot b k = some (.DomainBit true) then weights.getD k 0 else 0) :=
    sum_congr rfl fun slot hs => by
      obtain ⟨l1, l2⟩ := mem_Ico.1 hs
      have hrest : p.tuple_slot b slot = some .Zero ∨
          ∃ bit, p.tuple_slot b slot = some (.DomainBit bit) := by
        unfold BusPlan.tuple_slot
        simp only [List.getElem?_eq_getElem hb, Option.bind_eq_bind, Option.bind_some,
          show ¬ p.fingerprint_width ≤ slot by omega,
          show ¬ slot < p.domains[b].payload_width by omega]
        split_ifs <;> simp_all [pure]
      rcases hrest with h | ⟨bit, h⟩
      · rw [h]; simp [slotValue]
      · rw [h]; cases bit <;> simp [slotValue]
  rw [h1, h2, h3, zero_add]

theorem foldl_add_eq_sum (l : List EF) (a : EF) : l.foldl (· + ·) a = a + l.sum := by
  induction l generalizing a with
  | nil => simp
  | cons x l ih => simp [ih, add_assoc]

theorem foldl_fst (l : List (EF × ℕ)) (a : EF) :
    l.foldl (fun (acc : EF) (q : EF × ℕ) => acc + q.1) a = a + (l.map (·.1)).sum := by
  induction l generalizing a with
  | nil => simp
  | cons x l ih => simp [ih, add_assoc]

open Finset in
theorem filter_zipIdx_sum (P : ℕ → Prop) [DecidablePred P] : ∀ (l : List EF) (k : ℕ),
    (((l.zipIdx k).filter fun q => decide (P q.2)).map (·.1)).sum
      = ∑ j ∈ range l.length, if P (k + j) then l.getD j 0 else 0
  | [], k => by simp
  | x :: l, k => by
    have ih := filter_zipIdx_sum P l (k + 1)
    simp only [show ∀ i, k + 1 + i = k + (i + 1) by intro i; ring] at ih
    rw [List.zipIdx_cons, List.length_cons, sum_range_succ']
    by_cases h : P k
    · simp [h, ih, add_comm]
    · simp [h, ih]

open Finset in
theorem domain_constant_eq (p : BusPlan) (b : ℕ) (weights : List EF) :
    ((weights.zipIdx).filter fun (q : EF × ℕ) => p.tuple_slot b q.2 = some (.DomainBit true)).foldl
      (fun (acc : EF) (q : EF × ℕ) => acc + q.1) 0 =
    ∑ slot ∈ range weights.length,
      if p.tuple_slot b slot = some (.DomainBit true) then weights.getD slot 0 else 0 := by
  rw [foldl_fst, zero_add]
  have := filter_zipIdx_sum (fun slot => p.tuple_slot b slot = some (.DomainBit true)) weights 0
  simpa using this

open Finset in
theorem sum_map_range {α M : Type _} [AddCommMonoid M] (l : List α) (g : α → M) (d : α) :
    (l.map g).sum = ∑ i ∈ range l.length, g (l.getD i d) := by
  induction l with
  | nil => simp
  | cons x l ih => rw [List.map_cons, List.sum_cons, ih, List.length_cons, sum_range_succ']; simp [add_comm]

open Finset in
/-- The payload inner product of a compiled declaration. -/
theorem payload_sum {ps : List ℕ} {ws sc vals : List EF} {w : ℕ} (hps : ps.length = w)
    (hws : w ≤ ws.length) (h : ∀ k < w, sc.getD (ps.getD k 0) 0 = vals.getD k 0) :
    ((ps.zip (ws.take w)).map fun (q : ℕ × EF) => q.2 * sc.getD q.1 0).foldl (· + ·) 0 =
      ∑ k ∈ range w, ws.getD k 0 * vals.getD k 0 := by
  rw [foldl_add_eq_sum, zero_add, sum_map_range _ _ (0, 0)]
  have hlen : (ps.zip (ws.take w)).length = w := by simp [hps]; omega
  rw [hlen]
  refine sum_congr rfl fun k hk => ?_
  have hk' := mem_range.1 hk
  rw [List.getD_eq_getElem _ _ (by omega), ← h k hk', List.getD_eq_getElem ps 0 (by omega),
    List.getD_eq_getElem ws 0 (by omega)]
  simp only [List.getElem_zip, List.getElem_take]

/-- The activation's value:

- none for an always-active declaration
- the boundary selector for a boundary declaration
- the caller's selector otherwise. -/
def actValue (values : BusEvaluation F EF) : BusActivation (SymbolicExpression F) → Option (Option EF)
  | .Always => some none
  | .Boundary .First => some (some values.is_first_row)
  | .Boundary .Last => some (some values.is_last_row)
  | .Boolean e => (exprValue values e).map some

/-- 1 + (x - 1) s for an activation s, and x itself without one. -/
def gateOpt : Option EF → EF → EF
  | none, x => x
  | some s, x => 1 + (x - 1) * s

/-- The evaluation of a compiled factor, from its forward pass. -/
theorem evaluate_eq (f : BusFactorPlan F EF) (values : BusEvaluation F EF) {sc : List EF}
    (h : evalNodes values f.nodes = .ok sc) :
    f.evaluate values = .ok (gateOpt (f.activation.map fun n => sc.getD n 0)
      (f.shifted_offset - ((f.payload.zip f.payload_weights).map fun (q : ℕ × EF) =>
        q.2 * sc.getD q.1 0).foldl (· + ·) 0)) := by
  unfold BusFactorPlan.evaluate
  unfold evalNodes at h
  rw [h]
  cases f.activation <;> rfl

open Finset in
/-- **The leaf factor.**

On a valid plan, a compiled declaration evaluates to its activation applied to one value.

That value is the offset minus the weighted sum of its padded tuple's slots. -/
theorem factor_eq {p : BusPlan} (hp : LayoutWF p) {b : ℕ} (hb : b < p.domains.length)
    {interaction : SymbolicBusInteraction F} (hw : interaction.fields.length = p.domains[b].payload_width)
    {weights : List EF} (hwl : weights.length = p.fingerprint_width) (offset : EF)
    (values : BusEvaluation F EF) {vals : List EF}
    (hvals : interaction.fields.mapM (exprValue values) = some vals) {sOpt : Option EF}
    (hact : actValue values interaction.activation = some sOpt) {f : BusFactorPlan F EF}
    (hf : p3_bus.evaluation.mirror.BusPlan.compile_factor p b interaction weights offset = .ok f) :
    f.evaluate values = .ok (gateOpt sOpt (offset - ∑ slot ∈ range p.fingerprint_width,
      weights.getD slot 0 * slotValue vals (p.tuple_slot b slot))) := by
  unfold p3_bus.evaluation.mirror.BusPlan.compile_factor at hf
  simp only [List.getElem?_eq_getElem hb, hw, ne_eq, not_true_eq_false, ite_false, hwl] at hf
  obtain ⟨⟨nodes1, ps⟩, hfold, hf⟩ := except_bind_ok hf
  obtain ⟨sc1, e1, -, hpl, -, hk1⟩ := compile_fields values interaction.fields ([], []) [] vals
    (nodes1, ps) (by rfl) hvals hfold
  simp only [List.length_nil, zero_add] at hpl hk1
  have hfw : p.domains[b].payload_width ≤ weights.length := by
    rw [hwl]; have := hp.logical; have := hp.fingerprint; have := hp.width _ (List.getElem_mem hb)
    omega
  -- The value of the slot sum, through the identity bits folded into the offset.
  have hsplit := slot_sum_split hp hb vals weights
  have hdom := domain_constant_eq p b weights
  rw [hwl] at hdom
  have hpay : ∀ sc : List EF, sc1 <+: sc →
      ((ps.zip (weights.take p.domains[b].payload_width)).map fun (q : ℕ × EF) =>
        q.2 * sc.getD q.1 0).foldl (· + ·) 0 =
      ∑ k ∈ range p.domains[b].payload_width, weights.getD k 0 * vals.getD k 0 :=
    fun sc hsc => payload_sum (by rw [hpl, hw]) hfw fun k hk => by
      obtain ⟨-, l, g⟩ := hk1 k (by omega)
      obtain ⟨t, rfl⟩ := hsc
      rw [getD_append_left l, g]
  cases ha : interaction.activation with
  | Always =>
    rw [ha] at hf hact
    simp only [pure, Except.pure, bind, Except.bind, Except.ok.injEq] at hf
    subst hf
    simp only [actValue, Option.some.injEq] at hact; subst hact
    rw [evaluate_eq _ values e1]
    simp only [Option.map_none, gateOpt]
    rw [hpay sc1 List.prefix_rfl, hsplit, hdom]; ring_nf
  | Boundary bd =>
    rw [ha] at hf hact
    have hlen := length_evalNodes e1
    cases bd <;>
    · simp only [pure, Except.pure, bind, Except.bind, Except.ok.injEq] at hf
      subst hf
      simp only [actValue, Option.some.injEq] at hact; subst hact
      rw [evaluate_eq _ values (eval_snoc_bin values e1 _ _ rfl)]
      simp only [Option.map_some, gateOpt]
      rw [hpay _ (List.prefix_append _ _), hsplit, hdom]
      have hget : ∀ x : EF, (sc1 ++ [x]).getD nodes1.length 0 = x := fun x => by
        simp [List.getD_eq_getElem?_getD, show nodes1.length = sc1.length from hlen.symm]
      rw [hget]; ring_nf
  | Boolean e =>
    rw [ha] at hf hact
    simp only [pure, Except.pure, bind, Except.bind] at hf
    obtain ⟨⟨n2, i⟩, hc, hf⟩ := except_bind_ok hf
    simp only [Except.ok.injEq] at hf
    subst hf
    simp only [actValue, Option.map_eq_some_iff] at hact
    obtain ⟨sv, hsv, rfl⟩ := hact
    obtain ⟨sc2, e2, p2, -, g2⟩ := compile_eval values e nodes1 n2 i sc1 sv hc e1 hsv
    rw [evaluate_eq _ values e2]
    simp only [Option.map_some, gateOpt, g2]
    rw [hpay _ p2, hsplit, hdom]; ring_nf

open Finset Plonky3Lean.Spec.MultilinearUtil in
/-- **The factor is the specified leaf.**

Take the equality table of the fingerprint point as weights.

A compiled declaration then evaluates to its activation applied to one value.

That value is gamma minus the multilinear extension of its padded tuple at the point. -/
theorem factor_eq_leaf {p : BusPlan} (hp : LayoutWF p) {b : ℕ} (hb : b < p.domains.length)
    {interaction : SymbolicBusInteraction F} (hw : interaction.fields.length = p.domains[b].payload_width)
    {r : List EF} (hr : r.length = p.geometry.tuple_variables) (γ : EF)
    (values : BusEvaluation F EF) {vals : List EF}
    (hvals : interaction.fields.mapM (exprValue values) = some vals) {sOpt : Option EF}
    (hact : actValue values interaction.activation = some sOpt) {f : BusFactorPlan F EF}
    (hf : p3_bus.evaluation.mirror.BusPlan.compile_factor p b interaction (eqTable r) γ = .ok f) :
    f.evaluate values = .ok (gateOpt sOpt (Plonky3Lean.Spec.Bus.leaf γ r (tupleOf p b vals))) := by
  have hlen : (eqTable r).length = p.fingerprint_width := by
    rw [Plonky3Lean.Proofs.MultilinearUtil.length_eqTable, hr, ← hp.pow]
  rw [factor_eq hp hb hw hlen γ values hvals hact hf, Plonky3Lean.Spec.Bus.leaf,
    Plonky3Lean.Spec.Bus.fingerprint, Plonky3Lean.Proofs.MultilinearUtil.mle_eq_sum, hr, ← hp.pow]
  congr 3
  refine sum_congr rfl fun slot hs => ?_
  simp [tupleOf, List.getD_eq_getElem?_getD, mem_range.1 hs]

end Plonky3Lean.Proofs.Bus
