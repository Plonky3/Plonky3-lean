module

public import Plonky3Lean.Proofs.Lookup.Degree

@[expose] public section

/-!
# The prover's tuple combiner

The prover combines a tuple with a table of powers of beta, the verifier with Horner's rule.

Both compute the fingerprint, so prover and verifier agree on every denominator.
-/

namespace Plonky3Lean.Proofs.Lookup

open Plonky3Lean.Spec.Lookup Finset p3_lookup.mirror p3_air.symbolic.mirror p3_air.air.mirror

set_option linter.unusedSectionVars false

variable {F : Type} [Field F] [DecidableEq F] {K : Type} [Field K] [Algebra F K] [DecidableEq K]

/-- The power table [1, beta, ..., beta^(W - 1)]. -/
def powerTable (β : K) (W : ℕ) : List K := (List.range W).map fun j => β ^ j

theorem high_powers_eq (β : K) {W k : ℕ} (hk : k ≤ W) :
    (((powerTable β W).drop 1).take (k - 1)).reverse = (List.range (k - 1)).map fun i => β ^ (k - 1 - i) := by
  apply List.ext_getElem
  · simp [powerTable]; omega
  · intro i h1 h2
    simp only [List.getElem_reverse, List.getElem_take, List.getElem_drop, powerTable,
      List.getElem_map, List.getElem_range, List.length_take, List.length_drop, List.length_map,
      List.length_range]
    congr 1; simp at h2; omega

/-- The fingerprint as the last entry plus each leading entry times beta^(k - 1 - i). -/
theorem fingerprint_eq_last_add (β : K) (v : List K) (hv : v ≠ []) :
    fingerprint β v = v.getLast hv + ∑ i ∈ range (v.length - 1), v.getD i 0 * β ^ (v.length - 1 - i) := by
  obtain ⟨u, x, rfl⟩ : ∃ u x, v = u ++ [x] :=
    ⟨v.dropLast, v.getLast hv, (List.dropLast_append_getLast hv).symm⟩
  rw [← foldl_horner_zero, List.foldl_append, List.foldl_cons, List.foldl_nil, foldl_horner_zero,
    List.getLast_append_singleton, List.length_append, List.length_singleton, Nat.add_sub_cancel]
  rw [add_comm]; congr 1
  unfold fingerprint
  rw [← sum_range_reflect, sum_mul]
  refine sum_congr rfl fun i hi => ?_
  have hi := mem_range.1 hi
  rw [mul_assoc, ← pow_succ]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_reverse (by omega : u.length - 1 - i < u.length),
    List.getElem?_append_left (by omega : i < u.length)]
  rw [show u.length - 1 - (u.length - 1 - i) = i by omega, show u.length - 1 - i + 1 = u.length - i by omega]

theorem dot_product_eq (l : List K) (r : List F) (h : l.length = r.length) :
    dot_product l r = ∑ i ∈ range l.length, l.getD i 0 * algebraMap F K (r.getD i 0) := by
  unfold dot_product
  rw [list_sum_map_eq_sum_range _ _ (0, 0), List.length_zip, h, min_self]
  refine sum_congr rfl fun i hi => ?_
  have hi := mem_range.1 hi
  simp [List.getD_eq_getElem?_getD, hi, h ▸ hi]

/-- **The prover's combiner is the fingerprint.**

Take entries resolving to v and a power table at least as wide.

The combiner computes fingerprint(v) in the extension. -/
theorem combine_tuple_eq (elts : List (SymbolicExpression F)) (β : K) {W : ℕ}
    (ctx : p3_air.builder.mirror.AirBuilder F F Unit) {v : List F}
    (hv : elts.mapM (resolve ctx ()) = some v) (hW : elts.length ≤ W) :
    combine_tuple elts (powerTable β W) ctx = some (fingerprint β (v.map (algebraMap F K))) := by
  rcases elts.eq_nil_or_concat' with rfl | ⟨d, l, rfl⟩
  · simp at hv; subst hv; simp [combine_tuple, fingerprint]
  · simp only [List.mapM_append, List.mapM_cons, List.mapM_nil, Option.bind_eq_bind,
      Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at hv
    obtain ⟨vd, hd, _, ⟨a, ha, _, rfl, rfl⟩, rfl⟩ := hv
    have hdl := length_of_mapM_some hd
    rcases d.eq_nil_or_concat' with rfl | ⟨d', l', rfl⟩
    · simp at hd; subst hd
      simp [combine_tuple, ha, fingerprint]
    · have hne : d' ++ [l'] ≠ [] := by simp
      unfold combine_tuple
      simp only [List.getLast?_append, List.getLast?_singleton, Option.some_or,
        List.dropLast_concat]
      split <;> simp_all
      · simp [powerTable] at *; omega
      · have hk : vd.length = (d'.length + 1) := hdl
        have hp := high_powers_eq β (W := W) (k := vd.length + 1) (by omega)
        simp only [Nat.add_sub_cancel, List.drop_one] at hp
        rw [hk] at hp
        rw [hp, dot_product_eq _ _ (by simp [hk]), fingerprint_eq_last_add β _ (by simp)]
        simp only [List.getLast_append_singleton, List.length_append, List.length_map,
          List.length_singleton, Nat.add_sub_cancel, List.length_range, hk]
        congr 1
        refine sum_congr rfl fun i hi => ?_
        have hi := mem_range.1 hi
        simp [List.getD_eq_getElem?_getD, List.getElem?_append_left (by simp; omega : i < (vd.map _).length),
          hi, hk ▸ hi, mul_comm]

/-- The prover's pairs of an additive lookup on a row.

The denominator is 1 for a zero count, else alpha - fingerprint. -/
def proverTerms (α β : K) (ev : List (List F)) (mv : List F) : List (K × F) :=
  (ev.zip mv).map fun x => (if x.2 = 0 then 1 else α - fingerprint β (x.1.map (algebraMap F K)), x.2)

theorem mapM_some {α β : Type _} {f : α → Option β} (g : α → β) :
    ∀ {l : List α}, (∀ x ∈ l, f x = some (g x)) → l.mapM f = some (l.map g)
  | [], _ => rfl
  | a :: l, h => by
    simp only [List.mapM_cons, h a List.mem_cons_self, Option.bind_eq_bind, Option.bind_some,
      mapM_some g fun x hx => h x (List.mem_cons_of_mem _ hx), Option.pure_def, List.map_cons]

theorem mapM_getElem {α β : Type _} {f : α → Option β} {l : List α} {v : List β}
    (h : l.mapM f = some v) {i : ℕ} (hi : i < l.length) :
    f l[i] = some (v[i]'(by rw [length_of_mapM_some h]; exact hi)) := by
  induction l generalizing v i with
  | nil => simp at hi
  | cons a l ih =>
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨b, hb, w, hw, rfl⟩ := h
    cases i with
    | zero => simpa using hb
    | succ i => simpa using ih hw (by simpa using hi)

/-- **The prover's pairs on a row**, for an additive lookup.

Its entries resolve to ev and its counts to mv.

The power table is at least as wide as every tuple. -/
theorem lookup_row_terms_additive (ctx : p3_air.builder.mirror.AirBuilder F F Unit)
    (lookup : Lookup F) (hflags : lookup.flags = none) (α β : K) {W : ℕ}
    (hW : ∀ e ∈ lookup.elements, e.length ≤ W) {ev : List (List F)} {mv : List F}
    (hev : lookup.elements.mapM (fun e => e.mapM (resolve ctx ())) = some ev)
    (hmv : lookup.multiplicities.mapM (resolve ctx ()) = some mv)
    (hlen : lookup.multiplicities.length = lookup.elements.length) :
    lookup_row_terms ctx lookup α (powerTable β W) = some (proverTerms α β ev mv) := by
  have hevl := length_of_mapM_some hev
  have hmvl := length_of_mapM_some hmv
  unfold lookup_row_terms
  rw [hflags]
  dsimp only
  rw [mapM_some (fun x : List (SymbolicExpression F) × ℕ =>
    (if mv.getD x.2 0 = 0 then 1 else α - fingerprint β ((ev.getD x.2 []).map (algebraMap F K)),
      mv.getD x.2 0))]
  · congr 1
    unfold proverTerms
    apply List.ext_getElem
    · simp [hevl, hmvl, hlen]
    · intro i h1 h2
      simp only [List.length_map, List.length_zipIdx] at h1
      simp [List.getD_eq_getElem?_getD, hevl ▸ h1, show i < mv.length by omega]
  · rintro ⟨e, j⟩ hx
    obtain ⟨hj, hje⟩ := List.getElem?_eq_some_iff.1 (List.mem_zipIdx_iff_getElem?.1 hx)
    dsimp only at hj hje ⊢
    subst hje
    have hm := mapM_getElem hmv (i := j) (by omega)
    have he := mapM_getElem hev (i := j) hj
    simp only [List.getElem?_eq_getElem (show j < lookup.multiplicities.length by omega),
      Option.bind_eq_bind, Option.bind_some, hm, combine_tuple_eq _ β ctx he (hW _ (List.getElem_mem hj)),
      Option.pure_def, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem (show j < mv.length by omega),
      List.getElem?_eq_getElem (show j < ev.length by omega), Option.getD_some]
    split_ifs <;> rfl

/-- **The prover's fraction is the honest one.**

The inverses times the counts sum to the fraction of the true denominators.

This includes the zero-count skip. -/
theorem prover_fraction (α β : K) (ev : List (List F)) (mv : List F) (hlen : mv.length = ev.length) :
    dot_product ((proverTerms α β ev mv).map fun x => x.1⁻¹) ((proverTerms α β ev mv).map (·.2)) =
      fracSum (rowTerms (ev.map (·.map (algebraMap F K))) (mv.map (algebraMap F K)) α β) := by
  have hl : (proverTerms α β ev mv).length = ev.length := by simp [proverTerms, hlen]
  rw [dot_product_eq _ _ (by simp), List.length_map, hl]
  unfold fracSum
  rw [show (rowTerms (ev.map (·.map (algebraMap F K))) (mv.map (algebraMap F K)) α β).length =
    ev.length by simp [rowTerms, hlen]]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi := Finset.mem_range.1 hi
  rw [mul_rowTerms (by simp [hlen]) (by simpa using hi), den_rowTerms (by simp [hlen]) (by simpa using hi)]
  have hz : (ev.zip mv)[i]? = some (ev[i], mv[i]'(by omega)) := by
    rw [List.getElem?_eq_getElem (by simp; omega)]; simp
  simp only [proverTerms, List.getD_eq_getElem?_getD, List.getElem?_map, hz, Option.map_some,
    Option.getD_some]
  by_cases h0 : mv[i]'(by omega) = 0
  · simp [h0, List.getElem?_eq_getElem hi, List.getElem?_eq_getElem (show i < mv.length by omega)]
  · simp [h0, List.getElem?_eq_getElem hi, List.getElem?_eq_getElem (show i < mv.length by omega),
      div_eq_inv_mul]

end Plonky3Lean.Proofs.Lookup
