module

public import Plonky3Lean.Proofs.Bus.Ram
public import Plonky3Lean.Proofs.Bus.Verify
public import Plonky3Lean.Proofs.Bus.Evaluation
public import Plonky3Lean.Proofs.Bus.Timestamped
public import Plonky3Lean.Proofs.Bus.Security
public import Plonky3Lean.Proofs.Bus.Extracted
public import Plonky3Lean.Proofs.Bus.PlanBuild
public import CompPoly.Fields.BabyBear.Ext4
public import CompPoly.Fields.KoalaBear.Basic

@[expose] public section

/-!
# p3-bus: claims

The integer helpers are extracted: a direction's position, the boundary rows and the RAM payload widths.

These parts are transcribed:

- the declaration surface and the plan
- the factor evaluation
- the product-tree verifier
- the read-write memory and the timestamped clock
- the security accounting

The transcription claims are stated at BabyBear F and its quartic extension K, where the challenges live.

The specification is offline memory checking, in its grand-product form.

It follows Blum, Evans, Gemmell, Kannan and Naor (FOCS 1991):

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

/-- **The multiset identity.**

Take two lists of tuples of 2^m slots.

They have equal grand-product polynomials exactly when they are permutations of each other. -/
theorem multiset_identity {m : ℕ} {ts ss : List (List K)} (hts : ∀ t ∈ ts, t.length = 2 ^ m)
    (hss : ∀ s ∈ ss, s.length = 2 ^ m) : productPoly m ts = productPoly m ss ↔ ts.Perm ss :=
  productPoly_eq_iff hts hss

/-- **Soundness of the grand product.**

Take two lists of at most N tuples of 2^m slots, not permutations of each other.

A challenge is a pair of an offset and a point, and there are |K|^(m + 1) of them.

The grand products agree on at most max(1, m) N |K|^m challenges. -/
theorem grand_product_soundness {m N : ℕ} {ts ss : List (List K)}
    (hts : ∀ t ∈ ts, t.length = 2 ^ m) (hss : ∀ s ∈ ss, s.length = 2 ^ m) (hperm : ¬ ts.Perm ss)
    (hN : ts.length ≤ N) (hN' : ss.length ≤ N) :
    #{x : K × (Fin m → K) | grandProduct x.1 (List.ofFn x.2) ts = grandProduct x.1 (List.ofFn x.2) ss}
      ≤ max 1 m * N * Fintype.card K ^ m :=
  card_bad_challenges_le hts hss hperm hN hN'

/-! ## The plan -/

/-- **The planner's layout.**

A plan the planner returns:

- gives the i-th bus in name order the identity i + 1
- reserves enough identity bits for every bus
- keeps every payload within the reserved width
- pads to a power of two. -/
theorem planner_layout {inputs : List (BusPlanInput F)} {p : BusPlan}
    (h : BusPlan.build inputs = .ok (some p)) : LayoutWF p :=
  build_wf h

/-- **Every declaration's domain.**

In a plan the planner returns, each declared bus name is a domain of the plan.

That domain has the declaration's payload width, and the payload is nonempty. -/
theorem planner_domains {inputs : List (BusPlanInput F)} {p : BusPlan}
    (h : BusPlan.build inputs = .ok (some p)) {input : BusPlanInput F} (hin : input ∈ inputs)
    {i : SymbolicBusInteraction F} (hi : i ∈ input.interactions) :
    ∃ hb : busIndex p i.bus_name < p.domains.length,
      p.domains[busIndex p i.bus_name].«name» = i.bus_name ∧
      p.domains[busIndex p i.bus_name].payload_width = i.fields.length ∧ i.fields ≠ [] :=
  build_domain h hin hi

/-- **The blocks of a plan.**

In a plan the planner returns:

- the pushes lie on the push side and the pulls on the pull side
- forgetting offsets, the blocks are the declarations' requests, rearranged
- each side's blocks are laid end to end and end by the logical leaf count
- each block starts at a multiple of its own height, so the debug assertion never fails -/
theorem planner_blocks {inputs : List (BusPlanInput F)} {p : BusPlan}
    (h : BusPlan.build inputs = .ok (some p)) :
    (∀ b ∈ p.pushes, b.direction = .Push) ∧ (∀ b ∈ p.pulls, b.direction = .Pull) ∧
      ((p.pushes ++ p.pulls).map BusBlock.request).Perm (pendingOf p inputs) ∧
      Separated p.pushes p.geometry.logical_leaf_count ∧
      Separated p.pulls p.geometry.logical_leaf_count ∧
      ∀ b ∈ p.pushes ++ p.pulls, 2 ^ b.log_height ∣ b.offset :=
  build_blocks h

/-- **Every declaration owns exactly one block.**

Take the declaration j of AIR a.

The plan has exactly one block owned by it.

That block carries the declaration's bus and direction, and the AIR's height. -/
theorem planner_block_unique {inputs : List (BusPlanInput F)} {p : BusPlan}
    (h : BusPlan.build inputs = .ok (some p)) {a j : ℕ} {input : BusPlanInput F}
    {i : SymbolicBusInteraction F} (ha : inputs[a]? = some input) (hj : input.interactions[j]? = some i) :
    ((p.pushes ++ p.pulls).filter (·.owner = ⟨a, j⟩)).map BusBlock.request =
      [⟨busIndex p i.bus_name, i.direction, ⟨a, j⟩, input.log_height⟩] :=
  build_block_unique h ha hj

/-- **The layout is injective.**

On a plan the planner returns, a padded tuple determines its bus and its payload. -/
theorem layout_injective {inputs : List (BusPlanInput F)} {p : BusPlan}
    (h : BusPlan.build inputs = .ok (some p)) {b b' : ℕ} (hb : b < p.domains.length)
    (hb' : b' < p.domains.length) {x y : List K} (hx : x.length = p.domains[b].payload_width)
    (hy : y.length = p.domains[b'].payload_width) (he : tupleOf p b x = tupleOf p b' y) :
    b = b' ∧ x = y :=
  tupleOf_injective (build_wf h) hb hb' hx hy he

/-- **Soundness of the bus.**

Take the plan the planner returns for some declarations.

Take pushed and pulled named payloads those declarations allow, not a permutation of each other.

Their padded tuples have equal grand products on at most max(1, m) N |K|^m of the |K|^(m + 1) challenges. -/
theorem bus_soundness {inputs : List (BusPlanInput F)} {p : BusPlan}
    (h : BusPlan.build inputs = .ok (some p)) {push pull : List (String × List K)}
    (hpush : ∀ d ∈ push, Declared inputs d) (hpull : ∀ d ∈ pull, Declared inputs d)
    (hperm : ¬ push.Perm pull) {N : ℕ} (hN : push.length ≤ N) (hN' : pull.length ≤ N) :
    #{x : K × (Fin p.geometry.tuple_variables → K) |
      grandProduct x.1 (List.ofFn x.2) (push.map fun d => tupleOf p (busIndex p d.1) d.2) =
        grandProduct x.1 (List.ofFn x.2) (pull.map fun d => tupleOf p (busIndex p d.1) d.2)}
      ≤ max 1 p.geometry.tuple_variables * N * Fintype.card K ^ p.geometry.tuple_variables :=
  bus_soundness_of_build h hpush hpull hperm hN hN'

/-! ## The leaf factor -/

/-- **The factor is the specified leaf.**

Take a declaration of the inputs, compiled against the plan the planner returns.

The weights are the equality table of the fingerprint point.

A compiled declaration evaluates to gamma minus the multilinear extension of its padded tuple.

Its activation is then applied to that value. -/
theorem factor_is_leaf {inputs : List (BusPlanInput F)} {p : BusPlan}
    (h : BusPlan.build inputs = .ok (some p)) {input : BusPlanInput F} (hin : input ∈ inputs)
    {interaction : SymbolicBusInteraction F} (hi : interaction ∈ input.interactions)
    {r : List K} (hr : r.length = p.geometry.tuple_variables) (γ : K) (values : BusEvaluation F K)
    {vals : List K} (hvals : interaction.fields.mapM (exprValue values) = some vals)
    {sOpt : Option K} (hact : actValue values interaction.activation = some sOpt)
    {f : BusFactorPlan F K}
    (hf : p3_bus.evaluation.mirror.BusPlan.compile_factor p (busIndex p interaction.bus_name) interaction
      (eqTable r) γ = .ok f) :
    f.evaluate values = .ok (gateOpt sOpt (leaf γ r (tupleOf p (busIndex p interaction.bus_name) vals))) := by
  obtain ⟨hb, -, hw, -⟩ := build_domain h hin hi
  exact factor_eq_leaf (build_wf h) hb hw.symm hr γ values hvals hact hf

/-- Flattening a declaration is faithful.

The forward pass puts each expression's value at its position. -/
theorem flattening_faithful (values : BusEvaluation F K) (e : SymbolicExpression F)
    (nodes nodes' : List (BusNode F)) (i : ℕ) (sc : List K) (v : K)
    (hc : compile_expression nodes e = .ok (nodes', i)) (he : evalNodes values nodes = .ok sc)
    (hv : exprValue values e = some v) :
    ∃ sc', evalNodes values nodes' = .ok sc' ∧ sc <+: sc' ∧ i < sc'.length ∧ sc'.getD i 0 = v :=
  compile_eval values e nodes nodes' i sc v hc he hv

/-! ## The product-tree reduction -/

/-- **The schedule.**

A height 2k contracts two levels per layer.

A height 2k + 1 starts with one binary layer. -/
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

/-- **The identity padding.**

Take a point of the statement's dimension and a prefix that fits.

The verifier's threshold evaluation is sum_(n <= i < 2^h) eq(i, r). -/
theorem identity_padding (s : ProductGkrShape) (n : ℕ) (point : List K)
    (hp : point.length = s.log_height) (hn : n ≤ 2 ^ s.log_height) :
    s.identity_padding_evaluation n point =
      some (∑ i ∈ Ico n (2 ^ s.log_height), eq (vertex s.log_height i) point) :=
  identity_padding_evaluation_eq s n point hp hn

/-- The padding evaluation panics exactly in two cases:

- the point has the wrong dimension
- the prefix is longer than the table. -/
theorem identity_padding.panics (s : ProductGkrShape) (n : ℕ) (point : List K) :
    s.identity_padding_evaluation n point = none ↔
      point.length ≠ s.log_height ∨ 2 ^ s.log_height < n :=
  identity_padding_evaluation_panics s n point

/-- **The verifier never panics.**

Take a statement its constructor accepts and six distinct interpolation nodes.

For every proof, the verifier returns the output or an error. -/
theorem verifier_total {S : Type} (node : ℕ → K) (T : VerifierTranscript K S) (bits : ℕ)
    (p : ProductGkrProof K) {shape : ProductGkrShape}
    (hshape : shape.root_shape = .FirstTwoShared → 2 ≤ shape.num_trees)
    (hnodes : has_distinct_round_nodes bits node = true) :
    (p.verify node T bits shape).isSome :=
  verify_isSome node T bits p hshape hnodes

/-! ## Security -/

/-- **The charged numerators.**

With two trees, the bus charges max(1, s) N for the fingerprint.

It then charges 5 R, L and h, each omitted when zero.

Here R = k(k - 1) or k^2, and L = ceil(h / 2). -/
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

/-- **Consistency of a sorted trace.**

Take a trace sorted strictly by cell, then time.

If its first access and every read follow the read rule, it is a consistent memory. -/
theorem sorted_trace_consistent (init : ℕ → List F) {accs : List (Access (List F))}
    (hs : accs.IsChain Before) (h0 : ∀ y ∈ accs.head?, y.write = false → y.value = init y.addr)
    (hc : accs.IsChain (ReadStep init)) : Consistent init accs :=
  consistent_of_sorted init hs h0 hc

/-- **The comparison is an unsigned strict order.**

Assume its asserts vanish and its enabling factors are nonzero.

Then, as k-digit numbers, the later key is the earlier one plus a nonzero gap. -/
theorem strict_increase {c en : F} (hc : c ≠ 0) (hen : en ≠ 0)
    {left right delta carry nonzero : List F} (hk : 0 < left.length)
    (hl : ∀ i < left.length, IsBit (left.getD i 0)) (hd : ∀ i < left.length, IsBit (delta.getD i 0))
    (hz : ∀ x ∈ strictAsserts c en left right delta carry nonzero, x = 0) :
    pv right left.length = pv left left.length + pv delta left.length ∧ 0 < pv delta left.length :=
  strict_increase_sound hc hen hk hl hd hz

/-- **Memory consistency.**

An accepted trace of a valid self-contained memory decodes to a consistent memory starting from zero. -/
theorem ram_consistent {st : RamStatement} (hsp : st.boundary = .SingleProof) {air : RamAir}
    (hair : RamAir.new st = .ok air) {rows : List (List F)} (hacc : Accepted air rows) :
    Consistent (fun _ => List.replicate st.value_width 0) (rows.map (decode air.layout)) :=
  accepted_consistent hsp hair hacc

/-- The same holds for the machine's accesses in issuing order.

Balance makes them a permutation of the sorted trace. -/
theorem ram_consistent_machine {st : RamStatement} (hsp : st.boundary = .SingleProof)
    {air : RamAir} (hair : RamAir.new st = .ok air) {rows : List (List F)} (hacc : Accepted air rows)
    {machine : List (Access (List F))} (hperm : (rows.map (decode air.layout)).Perm machine) :
    Consistent (fun _ => List.replicate st.value_width 0) machine :=
  accepted_consistent_perm hsp hair hacc hperm

/-! ## The timestamped clock -/

/-- **The gap factors.**

A gap d from 1 to 2^32 is (j + 1) + 2^16 m, with digits j and m below 2^16.

Its factors are the range-table entries of rows j and m. -/
theorem gap_factors_digits (g : K) {d : ℕ} (h1 : 1 ≤ d) (h2 : d ≤ 2 ^ 32) :
    ∃ j < 2 ^ 16, ∃ m < 2 ^ 16, d = j + 1 + 2 ^ 16 * m ∧
      gap_factors g d = some (ClockRangeAir.low g j, ClockRangeAir.high g m) :=
  gap_factors_spec g h1 h2

/-- **The gap check.**

Take the range-table entries lo and hi of rows j and m.

Then prev lo = now hi exactly when now = prev g^((j + 1) + 2^16 m). -/
theorem gap_check {g : K} (hg : g ≠ 0) (j m : ℕ) (prev now : K) :
    prev * ClockRangeAir.low g j = now * ClockRangeAir.high g m ↔
      now = prev * g ^ (j + 1 + 2 ^ 16 * m) :=
  gap_sound hg j m prev now

/-- **No forged cycle.**

Gaps from 1 to 2^32 never climb back to the start.

This needs fewer gaps than the order of g divided by 2^32. -/
theorem forged_cycle {g : K} (ds : List ℕ) (hd : ∀ d ∈ ds, 1 ≤ d ∧ d ≤ 2 ^ 32) (hne : ds ≠ [])
    (hord : ds.length * 2 ^ 32 < orderOf g) : g ^ ds.sum ≠ 1 :=
  no_cycle ds hd hne hord

/-- The clock orbit check refuses BabyBear and KoalaBear themselves, whose orbits are below 2^32.

It accepts their quartic extensions. -/
theorem clock_orbit_fields :
    check_orbit BabyBear.fieldSize ≠ .ok () ∧ check_orbit KoalaBear.fieldSize ≠ .ok () ∧
      check_orbit (BabyBear.fieldSize ^ 4) = .ok () ∧ check_orbit (KoalaBear.fieldSize ^ 4) = .ok () := by
  simp only [ne_eq, check_orbit_ok, BabyBear.fieldSize, KoalaBear.fieldSize]
  norm_num

/-! ## The extracted integer helpers -/

section Extracted

open CoreModels Aeneas Aeneas.Std Plonky3Lean.Proofs.Bus.Extracted

/-- The shipped position of a direction is 0 for a push and 1 for a pull. -/
theorem direction.BusDirection.index.eq_mirror (d : p3_bus.direction.BusDirection) :
    ∃ n : Std.Usize, p3_bus.direction.BusDirection.index d = .ok n ∧ n.val = (dirMirror d).index :=
  index_eq d

/-- A first-row boundary holds row 0, and a last-row boundary holds the row r with r + 1 equal to the height.

The shipped check computes that for every row below the largest usize. -/
theorem builder.BusBoundary.contains_row.eq_mirror (b : p3_bus.builder.BusBoundary) (row height : Std.Usize)
    (hrow : row.val < Usize.max) :
    p3_bus.builder.BusBoundary.contains_row b row height =
      .ok ((boundaryMirror b).contains_row row.val height.val) :=
  contains_row_eq b row height hrow

/-- The shipped last-row check panics on the largest usize row, whose successor overflows. -/
theorem builder.BusBoundary.contains_row.panics (row height : Std.Usize) (hrow : row.val = Usize.max) :
    p3_bus.builder.BusBoundary.contains_row .Last row height = .fail .panic :=
  contains_row_max row height hrow

/-- An access payload is the operation, the address bits, the timestamp bits and the value.

Its shipped width is 1 + a + t + v whenever that fits a usize. -/
theorem ram.statement.RamStatement.access_payload_width.eq_spec (st : p3_bus.ram.statement.RamStatement)
    (h : 1 + st.address_bits.val + st.timestamp_bits.val + st.value_width.val ≤ Usize.max) :
    ∃ n : Std.Usize, p3_bus.ram.statement.RamStatement.access_payload_width st = .ok n ∧
      n.val = 1 + st.address_bits.val + st.timestamp_bits.val + st.value_width.val :=
  access_payload_width_eq st h

/-- The shipped access payload width panics exactly when 1 + a + t + v overflows a usize. -/
theorem ram.statement.RamStatement.access_payload_width.panics (st : p3_bus.ram.statement.RamStatement)
    (h : Usize.max < 1 + st.address_bits.val + st.timestamp_bits.val + st.value_width.val) :
    p3_bus.ram.statement.RamStatement.access_payload_width st = .fail .panic :=
  access_payload_width_fail st h

/-- An image payload is the address bits and the value.

Its shipped width is a + v whenever that fits a usize. -/
theorem ram.statement.RamStatement.image_payload_width.eq_spec (st : p3_bus.ram.statement.RamStatement)
    (h : st.address_bits.val + st.value_width.val ≤ Usize.max) :
    ∃ n : Std.Usize, p3_bus.ram.statement.RamStatement.image_payload_width st = .ok n ∧
      n.val = st.address_bits.val + st.value_width.val :=
  image_payload_width_eq st h

/-- The shipped image payload width panics exactly when a + v overflows a usize. -/
theorem ram.statement.RamStatement.image_payload_width.panics (st : p3_bus.ram.statement.RamStatement)
    (h : Usize.max < st.address_bits.val + st.value_width.val) :
    p3_bus.ram.statement.RamStatement.image_payload_width st = .fail .panic :=
  image_payload_width_fail st h

end Extracted

end Plonky3Lean.Claims.Bus
