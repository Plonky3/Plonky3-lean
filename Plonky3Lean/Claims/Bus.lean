module

public import Plonky3Lean.Proofs.Bus.Ram
public import Plonky3Lean.Proofs.Bus.Verify
public import Plonky3Lean.Proofs.Bus.Evaluation
public import Plonky3Lean.Proofs.Bus.Timestamped
public import Plonky3Lean.Proofs.Bus.Security
public import CompPoly.Fields.BabyBear.Ext4
public import CompPoly.Fields.KoalaBear.Ext4

@[expose] public section

/-!
# p3-bus: claims

Nothing is extracted: the crate's dependencies do not compile in the extraction variant.

The declaration surface, the plan, the factor evaluation, the product-tree verifier, the read-write memory, the timestamped clock and the security accounting are transcribed.

The claims are stated at BabyBear F and its quartic extension K, where the challenges live.

The specification is offline memory checking after Blum, Evans, Gemmell, Kannan and Naor (FOCS 1991), in its grand-product form:

```text
    fingerprint(t, r) = sum_b eq(b, r) t_b           the tuple's multilinear extension
    leaf(t)           = gamma - fingerprint(t, r)
    prod_i leaf(a_i) = prod_j leaf(b_j)   <->   {a_i} = {b_j}, up to max(1, m) N / |K|

    a memory is consistent when every read returns the latest earlier write to its cell
```
-/

open Plonky3Lean.Spec.Bus Plonky3Lean.Spec.MultilinearUtil Plonky3Lean.Proofs.Bus Finset
  p3_bus.mirror p3_bus.ram.mirror p3_bus.product.mirror p3_bus.plan.mirror
  p3_bus.evaluation.mirror p3_bus.timestamped.mirror p3_bus.security.mirror
  p3_sumcheck.generic_degree.mirror p3_air.symbolic.mirror

set_option linter.unusedSectionVars false

namespace Plonky3Lean.Claims.Bus

local notation "F" => BabyBear.Field
local notation "K" => BabyBear.Ext4

/-! ## The grand product -/

/-- **The multiset identity.** Tuples of 2^m slots have equal grand-product polynomials exactly when the two lists are permutations of each other. -/
theorem multiset_identity {m : ℕ} {ts ss : List (List K)} (hts : ∀ t ∈ ts, t.length = 2 ^ m)
    (hss : ∀ s ∈ ss, s.length = 2 ^ m) : productPoly m ts = productPoly m ss ↔ ts.Perm ss :=
  productPoly_eq_iff hts hss

/-- **Soundness of the grand product.** Two lists of at most N tuples of 2^m slots, not permutations of each other, have equal grand products on at most max(1, m) N |K|^m of the |K|^(m + 1) pairs of an offset and a point. -/
theorem grand_product_soundness {m N : ℕ} {ts ss : List (List K)}
    (hts : ∀ t ∈ ts, t.length = 2 ^ m) (hss : ∀ s ∈ ss, s.length = 2 ^ m) (hperm : ¬ ts.Perm ss)
    (hN : ts.length ≤ N) (hN' : ss.length ≤ N) :
    #{x : K × (Fin m → K) | grandProduct x.1 (List.ofFn x.2) ts = grandProduct x.1 (List.ofFn x.2) ss}
      ≤ max 1 m * N * Fintype.card K ^ m :=
  card_bad_challenges_le hts hss hperm hN hN'

/-! ## The plan -/

/-- **The planner's layout.** A plan the planner returns gives the i-th bus in name order the identity i + 1, reserves enough identity bits for every bus, keeps every payload within the reserved width, and pads to a power of two. -/
theorem planner_layout {inputs : List (BusPlanInput F)} {p : BusPlan}
    (h : BusPlan.build inputs = .ok (some p)) : LayoutWF p :=
  build_wf h

/-- **The layout is injective.** On such a plan, a padded tuple determines its bus and its payload. -/
theorem layout_injective {p : BusPlan} (hp : LayoutWF p) {b b' : ℕ} (hb : b < p.domains.length)
    (hb' : b' < p.domains.length) {x y : List K} (hx : x.length = p.domains[b].payload_width)
    (hy : y.length = p.domains[b'].payload_width) (h : tupleOf p b x = tupleOf p b' y) :
    b = b' ∧ x = y :=
  tupleOf_injective hp hb hb' hx hy h

/-- **Soundness of the bus.** On a plan the planner returns, pushed declarations that are not a permutation of the pulled ones have equal grand products over their padded tuples on at most max(1, m) N |K|^m of the |K|^(m + 1) challenges. -/
theorem bus_soundness {p : BusPlan} (hp : LayoutWF p) {push pull : List (ℕ × List K)}
    (hpush : ∀ d ∈ push, Fits p d) (hpull : ∀ d ∈ pull, Fits p d) (hperm : ¬ push.Perm pull)
    {N : ℕ} (hN : push.length ≤ N) (hN' : pull.length ≤ N) :
    #{x : K × (Fin p.geometry.tuple_variables → K) |
      grandProduct x.1 (List.ofFn x.2) (push.map fun d => tupleOf p d.1 d.2) =
        grandProduct x.1 (List.ofFn x.2) (pull.map fun d => tupleOf p d.1 d.2)}
      ≤ max 1 p.geometry.tuple_variables * N * Fintype.card K ^ p.geometry.tuple_variables :=
  Plonky3Lean.Proofs.Bus.bus_soundness hp hpush hpull hperm hN hN'

/-! ## The leaf factor -/

/-- **The factor is the specified leaf.** With the equality table of the fingerprint point as weights, a compiled declaration evaluates to its activation applied to gamma minus the multilinear extension of its padded tuple. -/
theorem factor_is_leaf {p : BusPlan} (hp : LayoutWF p) {b : ℕ} (hb : b < p.domains.length)
    {interaction : SymbolicBusInteraction F} (hw : interaction.fields.length = p.domains[b].payload_width)
    {r : List K} (hr : r.length = p.geometry.tuple_variables) (γ : K) (values : BusEvaluation F K)
    {vals : List K} (hvals : interaction.fields.mapM (exprValue values) = some vals)
    {sOpt : Option K} (hact : actValue values interaction.activation = some sOpt)
    {f : BusFactorPlan F K}
    (hf : p3_bus.evaluation.mirror.BusPlan.compile_factor p b interaction (eqTable r) γ = .ok f) :
    f.evaluate values = .ok (gateOpt sOpt (leaf γ r (tupleOf p b vals))) :=
  factor_eq_leaf hp hb hw hr γ values hvals hact hf

/-- Flattening a declaration is faithful: the forward pass puts each expression's value at its position. -/
theorem flattening_faithful (values : BusEvaluation F K) (e : SymbolicExpression F)
    (nodes nodes' : List (BusNode F)) (i : ℕ) (sc : List K) (v : K)
    (hc : compile_expression nodes e = .ok (nodes', i)) (he : evalNodes values nodes = .ok sc)
    (hv : exprValue values e = some v) :
    ∃ sc', evalNodes values nodes' = .ok sc' ∧ sc <+: sc' ∧ i < sc'.length ∧ sc'.getD i 0 = v :=
  compile_eval values e nodes nodes' i sc v hc he hv

/-! ## The product-tree reduction -/

/-- **The schedule.** A height 2k contracts two levels per layer; a height 2k + 1 starts with one binary layer. -/
theorem schedule (s : ProductGkrShape) :
    s.layers = if s.log_height % 2 = 0 then
        (List.range (s.log_height / 2)).map fun j => (4, 2 * j)
      else (2, 0) :: (List.range (s.log_height / 2)).map fun j => (4, 1 + 2 * j) :=
  layers_eq s

/-- The layers contract the whole height, in ceil(h / 2) layers. -/
theorem schedule_dimensions (s : ProductGkrShape) :
    (s.layers.map fun l => Nat.log2 l.1).sum = s.log_height ∧
      s.layers.length = (s.log_height + 1) / 2 :=
  ⟨layers_branches s, layers_length s⟩

/-- **The identity padding.** On a point of the statement's dimension and a prefix that fits, the verifier's threshold evaluation is sum_(n <= i < 2^h) eq(i, r). -/
theorem identity_padding (s : ProductGkrShape) (n : ℕ) (point : List K)
    (hp : point.length = s.log_height) (hn : n ≤ 2 ^ s.log_height) :
    s.identity_padding_evaluation n point =
      some (∑ i ∈ Ico n (2 ^ s.log_height), eq (vertex s.log_height i) point) :=
  identity_padding_evaluation_eq s n point hp hn

/-- The padding evaluation panics exactly on a point of the wrong dimension or a prefix longer than the table. -/
theorem identity_padding.panics (s : ProductGkrShape) (n : ℕ) (point : List K) :
    s.identity_padding_evaluation n point = none ↔
      point.length ≠ s.log_height ∨ 2 ^ s.log_height < n :=
  identity_padding_evaluation_panics s n point

/-- **The verifier never panics.** On a statement its constructor accepts and six distinct interpolation nodes, it returns the output or an error for every proof. -/
theorem verifier_total {S : Type} (node : ℕ → K) (T : VerifierTranscript K S) (bits : ℕ)
    (p : ProductGkrProof K) {shape : ProductGkrShape}
    (hshape : shape.root_shape = .FirstTwoShared → 2 ≤ shape.num_trees)
    (hnodes : has_distinct_round_nodes bits node = true) :
    (p.verify node T bits shape).isSome :=
  verify_isSome node T bits p hshape hnodes

/-! ## Security -/

/-- **The charged numerators.** With two trees, the bus charges max(1, s) N for the fingerprint, then 5 R, L and h, each omitted when zero, with R = k(k - 1) or k^2 and L = ceil(h / 2). -/
theorem security_numerators (plan : BusPlan) (h2 : plan.product_shape.num_trees = 2) :
    components (p3_bus.security.mirror.BusPlan.security_dims plan) =
      [max 1 plan.geometry.tuple_variables * max plan.geometry.non_padding_leaf_counts.1
        plan.geometry.non_padding_leaf_counts.2] ++
      ([5 * (if plan.product_shape.log_height % 2 = 0 then
          (plan.product_shape.log_height / 2) * (plan.product_shape.log_height / 2 - 1)
        else (plan.product_shape.log_height / 2) ^ 2),
        (plan.product_shape.log_height + 1) / 2, plan.product_shape.log_height].filter (· ≠ 0)) :=
  components_eq plan h2

/-- The profile the bus passes to p3-security passes its constructor's checks. -/
theorem security_profile (s : ProductGkrShape) :
    (s.layers.map fun l => Nat.log2 l.1).sum = s.log_height ∧
      (s.log_height = 0 ↔ s.layers.length = 0) :=
  security_profile_valid s

/-! ## Read-write memory -/

/-- **Consistency of a sorted trace.** A trace sorted strictly by cell then time, whose first access and every read follow the read rule, is a consistent memory. -/
theorem sorted_trace_consistent (init : ℕ → List F) {accs : List (Access (List F))}
    (hs : accs.IsChain Before) (h0 : ∀ y ∈ accs.head?, y.write = false → y.value = init y.addr)
    (hc : accs.IsChain (ReadStep init)) : Consistent init accs :=
  consistent_of_sorted init hs h0 hc

/-- **The comparison is an unsigned strict order.** If its asserts vanish and its enabling factors are nonzero, the later key is the earlier one plus a nonzero gap, as k-digit numbers. -/
theorem strict_increase {c en : F} (hc : c ≠ 0) (hen : en ≠ 0)
    {left right delta carry nonzero : List F} (hk : 0 < left.length)
    (hl : ∀ i < left.length, IsBit (left.getD i 0)) (hd : ∀ i < left.length, IsBit (delta.getD i 0))
    (hz : ∀ x ∈ strictAsserts c en left right delta carry nonzero, x = 0) :
    pv right left.length = pv left left.length + pv delta left.length ∧ 0 < pv delta left.length :=
  strict_increase_sound hc hen hk hl hd hz

/-- **Memory consistency.** An accepted trace of a valid self-contained memory decodes to a consistent memory starting from zero. -/
theorem ram_consistent {st : RamStatement} (hsp : st.boundary = .SingleProof) {air : RamAir}
    (hair : RamAir.new st = .ok air) {rows : List (List F)} (hacc : Accepted air rows) :
    Consistent (fun _ => List.replicate st.value_width 0) (rows.map (decode air.layout)) :=
  accepted_consistent hsp hair hacc

/-- The same holds for the machine's accesses in issuing order, which balance makes a permutation of the sorted trace. -/
theorem ram_consistent_machine {st : RamStatement} (hsp : st.boundary = .SingleProof)
    {air : RamAir} (hair : RamAir.new st = .ok air) {rows : List (List F)} (hacc : Accepted air rows)
    {machine : List (Access (List F))} (hperm : (rows.map (decode air.layout)).Perm machine) :
    Consistent (fun _ => List.replicate st.value_width 0) machine :=
  accepted_consistent_perm hsp hair hacc hperm

/-! ## The timestamped clock -/

/-- **The gap factors.** A gap d from 1 to 2^32 is (j + 1) + 2^16 m with digits below 2^16, and its factors are the range-table entries of rows j and m. -/
theorem gap_factors_digits (g : K) {d : ℕ} (h1 : 1 ≤ d) (h2 : d ≤ 2 ^ 32) :
    ∃ j < 2 ^ 16, ∃ m < 2 ^ 16, d = j + 1 + 2 ^ 16 * m ∧
      gap_factors g d = some (ClockRangeAir.low g j, ClockRangeAir.high g m) :=
  gap_factors_spec g h1 h2

/-- **The gap check.** With range-table entries of rows j and m, prev lo = now hi exactly when now = prev g^((j + 1) + 2^16 m). -/
theorem gap_check {g : K} (hg : g ≠ 0) (j m : ℕ) (prev now : K) :
    prev * ClockRangeAir.low g j = now * ClockRangeAir.high g m ↔
      now = prev * g ^ (j + 1 + 2 ^ 16 * m) :=
  gap_sound hg j m prev now

/-- **No forged cycle.** Gaps from 1 to 2^32, fewer than the order of g over 2^32, never climb back to the start. -/
theorem forged_cycle {g : K} (ds : List ℕ) (hd : ∀ d ∈ ds, 1 ≤ d ∧ d ≤ 2 ^ 32) (hne : ds ≠ [])
    (hord : ds.length * 2 ^ 32 < orderOf g) : g ^ ds.sum ≠ 1 :=
  no_cycle ds hd hne hord

/-- The clock orbit check refuses BabyBear and KoalaBear themselves, whose orbits are below 2^32, and accepts their quartic extensions. -/
theorem clock_orbit_fields :
    check_orbit BabyBear.fieldSize ≠ .ok () ∧ check_orbit KoalaBear.fieldSize ≠ .ok () ∧
      check_orbit (BabyBear.fieldSize ^ 4) = .ok () ∧ check_orbit (KoalaBear.fieldSize ^ 4) = .ok () := by
  simp only [ne_eq, check_orbit_ok, BabyBear.fieldSize, KoalaBear.fieldSize]
  norm_num

end Plonky3Lean.Claims.Bus
