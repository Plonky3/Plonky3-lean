module

public import P3MultiStark.Mirror.Lookup
public import Plonky3Lean.Proofs.MultiStark.LookupLink
public import Plonky3Lean.Proofs.MultilinearUtil.PointForms
public import Mathlib.Algebra.CharP.Basic

@[expose] public section

/-!
# The lookup layout

The plan sorts the active AIRs by decreasing height.

It then gives each one the running height as its offset.

Each tuple of an AIR of 2^n rows takes the next block of 2^n leaves:

```text
    heights 2^3, 2^3, 2^2:
    | t0 t1 (AIR a) | t0 (AIR b) | t0 t1 t2 (AIR c) | padding |
      0      8  16    16     24    24 28 32 36        ...
```

Every earlier AIR is at least as tall, so each offset is a multiple of the AIR's own height.

So the blocks are aligned, they never overlap, and they fit the next power of two.

Their equality weights are the ones the verifier computes from the hypercube vertex of each block.

The bus identifiers stay distinct modulo p exactly when there are at most p buses.
-/

namespace Plonky3Lean.Proofs.MultiStark

open p3_multi_stark.lookup.mirror p3_multilinear_util.point.mirror Plonky3Lean.Proofs.MultilinearUtil
  Plonky3Lean.Spec.MultilinearUtil Plonky3Lean.Spec.MultiStark Finset

set_option linter.unusedSectionVars false

/-! ## Bus identifiers -/

/-- **The bus capacity.**

The check passes exactly when the bus coefficients 1, ..., B are distinct in the field.

The prefixes alpha + (i + 1) beta^W then differ in their beta^W coefficient. -/
theorem bus_capacity_ok_iff {F : Type _} [Field F] (p : ℕ) [hp : Fact p.Prime] [CharP F p]
    (B : ℕ) : bus_capacity_ok p B = true ↔
      ∀ i < B, ∀ j < B, ((i : F) + 1 = (j : F) + 1 → i = j) := by
  simp only [bus_capacity_ok, Bool.not_eq_true', decide_eq_false_iff_not, not_lt, add_left_inj]
  constructor
  · intro hB i hi j hj h
    have hmod := (CharP.natCast_eq_natCast F p).mp h
    exact Nat.ModEq.eq_of_lt_of_lt hmod (by omega) (by omega)
  · intro h
    by_contra hlt
    push Not at hlt
    have := h 0 (by have := hp.out.pos; omega) p hlt (by simp)
    exact hp.out.ne_zero this.symm

/-! ## Placement -/

/-- The blocks of placed instances: per tuple, its height and its index at that height. -/
def planBlocks (insts : List LookupInstancePlan) : List (ℕ × ℕ) :=
  insts.flatMap fun i => (List.range i.tuple_counts.sum).map fun t =>
    (i.num_variables, i.base_offset / 2 ^ i.num_variables + t)

/-- The height after placing instances from a height. -/
theorem place_snd : ∀ (h : ℕ) (insts : List LookupInstancePlan),
    (place h insts).2 = h + (insts.map fun i => i.tuple_counts.sum * 2 ^ i.num_variables).sum
  | h, [] => by simp [place]
  | h, i :: is => by simp [place, place_snd _ is, Nat.add_assoc]

/-- The leaves of the blocks of one instance placed at a multiple of its height. -/
theorem mem_leaves_instance {n h cnt t x : ℕ} (hdvd : 2 ^ n ∣ h) (ht : t < cnt)
    (hx : x ∈ leavesOf n (h / 2 ^ n + t)) : h ≤ x ∧ x < h + cnt * 2 ^ n := by
  simp only [leavesOf, mem_Ico, add_mul, Nat.div_mul_cancel hdvd, one_mul] at hx
  constructor <;> nlinarith

/-- **Placement.**

Take instances sorted by decreasing height, from a height every one of them divides.

The blocks then have pairwise disjoint leaves, all between the start and end heights. -/
theorem place_blocks : ∀ (h : ℕ) (insts : List LookupInstancePlan),
    insts.Pairwise (fun a b => b.num_variables ≤ a.num_variables) →
    (∀ i ∈ insts, 2 ^ i.num_variables ∣ h) →
    (∀ nc ∈ planBlocks (place h insts).1, ∀ x ∈ leavesOf nc.1 nc.2, h ≤ x ∧ x < (place h insts).2) ∧
      (planBlocks (place h insts).1).Pairwise fun a b => Disjoint (leavesOf a.1 a.2) (leavesOf b.1 b.2)
  | h, [], _, _ => by simp [place, planBlocks]
  | h, i :: is, hs, hd => by
    rw [List.pairwise_cons] at hs
    obtain ⟨h', hh'⟩ : ∃ h', h + i.tuple_counts.sum * 2 ^ i.num_variables = h' := ⟨_, rfl⟩
    have hd' : ∀ j ∈ is, 2 ^ j.num_variables ∣ h' := fun j hj => hh' ▸
      Nat.dvd_add (hd j (List.mem_cons_of_mem _ hj))
        (Dvd.dvd.mul_left (pow_dvd_pow 2 (hs.1 j hj)) _)
    obtain ⟨ih1, ih2⟩ := place_blocks h' is hs.2 hd'
    have hdi := hd i List.mem_cons_self
    have hge : h' ≤ (place h' is).2 := by rw [place_snd]; omega
    have hown : ∀ nc ∈ (List.range i.tuple_counts.sum).map (fun t =>
        (i.num_variables, h / 2 ^ i.num_variables + t)), ∀ x ∈ leavesOf nc.1 nc.2, h ≤ x ∧ x < h' := by
      intro nc hnc x hx
      obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hnc
      have := mem_leaves_instance hdi (List.mem_range.mp ht) hx
      omega
    simp only [place, planBlocks, List.flatMap_cons, hh'] at ih1 ih2 ⊢
    refine ⟨fun nc hnc x hx => ?_, ?_⟩
    · rcases List.mem_append.mp hnc with h1 | h2
      · have := hown nc h1 x hx; omega
      · have := ih1 nc h2 x hx; omega
    · rw [List.pairwise_append]
      refine ⟨?_, ih2, fun a ha b hb => Finset.disjoint_left.mpr fun x hxa hxb => ?_⟩
      · rw [List.pairwise_map]
        refine List.pairwise_lt_range.imp_of_mem fun {t u} _ _ htu =>
          Finset.disjoint_left.mpr fun x hx hx' => ?_
        simp only [leavesOf, mem_Ico] at hx hx'
        have : (h / 2 ^ i.num_variables + t + 1) * 2 ^ i.num_variables ≤
            (h / 2 ^ i.num_variables + u) * 2 ^ i.num_variables :=
          Nat.mul_le_mul_right _ (by omega)
        omega
      · have := hown a ha x hxa; have := ih1 b hb x hxb; omega

/-- The blocks placed from zero fit 2^M for M the ceiling of log_2 of the height. -/
theorem le_two_pow_log2_ceil (n : ℕ) : n ≤ 2 ^ log2_ceil_usize n := by
  unfold log2_ceil_usize
  split
  · simp; omega
  · have := Nat.lt_log2_self (n := n - 1); omega

/-! ## Weights -/

section Weights

variable {F EF : Type _} [Field F] [Field EF] [Algebra F EF]

theorem tupleWeights_eq (pl : ℕ) (pp : List EF) (hpl : pl < 64) (hpp : pp.length = pl) :
    ∀ (c count : ℕ), c + count ≤ 2 ^ pl →
      tupleWeights (F := F) pl pp c count =
        some ((List.range count).map fun t => eq (vertex pl (c + t)) pp)
  | c, 0, _ => by simp [tupleWeights]
  | c, count + 1, h => by
    have hv : ((vertex pl c : List F).map (algebraMap F EF)) = vertex pl c := by
      simp [vertex, apply_ite]
    rw [tupleWeights, hypercube_eq hpl (show c < 2 ^ pl by omega)]
    simp only [Option.bind_eq_bind, Option.bind_some]
    rw [eval_eq_eq (p := (vertex pl c : List F)) (q := pp) (by simp [hpp]), hv]
    simp only [Option.bind_some, tupleWeights_eq pl pp hpl hpp (c + 1) count (by omega),
      List.range_succ_eq_map, List.map_cons, List.map_map, Nat.add_zero, pure]
    congr 2
    exact List.map_congr_left fun t _ => by simp [Function.comp, Nat.add_assoc, Nat.add_comm 1]

theorem foldlM_tupleWeights (pl : ℕ) (pp : List EF) (hpl : pl < 64) (hpp : pp.length = pl) :
    ∀ (counts : List ℕ) (pre : List (List EF)) (idx : ℕ), idx + counts.sum ≤ 2 ^ pl →
      ∃ chunks, counts.foldlM (fun (acc : List (List EF) × ℕ) count => do
          let ws ← tupleWeights (F := F) pl pp acc.2 count
          pure (acc.1 ++ [ws], acc.2 + count)) (pre, idx) = some (pre ++ chunks, idx + counts.sum) ∧
        chunks.flatten = (List.range counts.sum).map fun t => eq (vertex pl (idx + t)) pp
  | [], pre, idx, _ => ⟨[], by simp⟩
  | c :: cs, pre, idx, h => by
    simp only [List.sum_cons] at h
    obtain ⟨chunks, hf, hfl⟩ := foldlM_tupleWeights pl pp hpl hpp cs
      (pre ++ [(List.range c).map fun t => eq (vertex pl (idx + t)) pp]) (idx + c) (by omega)
    refine ⟨((List.range c).map fun t => eq (vertex pl (idx + t)) pp) :: chunks, ?_, ?_⟩
    · simp only [Option.bind_eq_bind, pure] at hf
      simp only [List.foldlM_cons, tupleWeights_eq (F := F) pl pp hpl hpp idx c (by omega),
        Option.bind_eq_bind, Option.bind_some, pure, hf]
      simp [Nat.add_assoc]
    · rw [List.flatten_cons, hfl, List.sum_cons, List.range_add, List.map_append, List.map_map]
      congr 1
      exact List.map_congr_left fun t _ => by simp [Function.comp, Nat.add_assoc]

/-- **The verifier's weights.**

Take an instance at an offset its height divides, whose blocks fit the point's prefix.

The verifier's weights are then eq(vertex c, prefix), for the blocks c in order. -/
theorem blockWeights_eq {M : ℕ} {point : List EF} {inst : LookupInstancePlan}
    (hn : inst.num_variables ≤ M) (hlen : point.length = M) (hpl : M - inst.num_variables < 64)
    (hfit : inst.base_offset / 2 ^ inst.num_variables + inst.tuple_counts.sum ≤
      2 ^ (M - inst.num_variables)) :
    ∃ ws, blockWeights (F := F) M point inst = some ws ∧
      ws.flatten = (List.range inst.tuple_counts.sum).map fun t =>
        eq (vertex (M - inst.num_variables) (inst.base_offset / 2 ^ inst.num_variables + t))
          (point.take (M - inst.num_variables)) := by
  obtain ⟨chunks, hf, hfl⟩ := foldlM_tupleWeights (F := F) (M - inst.num_variables)
    (point.take (M - inst.num_variables)) hpl (by simp; omega) inst.tuple_counts []
    (inst.base_offset / 2 ^ inst.num_variables) hfit
  refine ⟨chunks, ?_, hfl⟩
  simp only [blockWeights, show ¬ M < inst.num_variables by omega,
    show ¬ point.length < M - inst.num_variables by omega, ↓reduceIte, Nat.shiftRight_eq_div_pow, hf,
    Option.map_some, List.nil_append]

end Weights

/-! ## The link of a placed plan -/

section Link

variable {K : Type _} [Field K]

/-- The blocks of a plan, each with its own multiplicity and denominator tables.

Placed blocks never share a height and an index, so the tables are keyed by both. -/
def planFracBlocks (insts : List LookupInstancePlan) (m d : ℕ → ℕ → ℕ → K) : List (FracBlock K) :=
  (planBlocks insts).map fun nc => ⟨nc.1, nc.2, m nc.1 nc.2, d nc.1 nc.2⟩

/-- The plan's blocks, placed from zero, are placed in the padded table of 2^M leaves. -/
theorem plan_placed (insts : List LookupInstancePlan)
    (hs : insts.Pairwise fun a b => b.num_variables ≤ a.num_variables) (m d : ℕ → ℕ → ℕ → K) :
    Placed (planFracBlocks (place 0 insts).1 m d) (log2_ceil_usize (place 0 insts).2) := by
  obtain ⟨h1, h2⟩ := place_blocks 0 insts hs fun _ _ => dvd_zero _
  have hle := le_two_pow_log2_ceil (place 0 insts).2
  refine ⟨fun b hb x hx => ?_, ?_⟩
  · obtain ⟨nc, hnc, rfl⟩ := List.mem_map.mp hb
    exact mem_range.mpr (lt_of_lt_of_le (h1 nc hnc x hx).2 hle)
  · exact List.pairwise_map.mpr (h2.imp fun h => h)

/-- **The lookup link of the plan.**

Take active instances sorted by decreasing height, placed from zero.

Take the padded tables of 2^M leaves they define, and a point q of M coordinates.

The folded claim N(q) + theta (D(q) - 1) is the sum, over the blocks, of each block's share. -/
theorem plan_link (insts : List LookupInstancePlan)
    (hs : insts.Pairwise fun a b => b.num_variables ≤ a.num_variables) (m d : ℕ → ℕ → ℕ → K)
    (q : List K) (hq : q.length = log2_ceil_usize (place 0 insts).2) (θ : K) :
    claimed_sum (rowExt (numTable (planFracBlocks (place 0 insts).1 m d)) q)
        (rowExt (denTable (planFracBlocks (place 0 insts).1 m d)) q) θ =
      ((planBlocks (place 0 insts).1).map fun nc =>
        eq (vertex (q.length - nc.1) nc.2) (q.take (q.length - nc.1)) *
          (rowExt (m nc.1 nc.2) (q.drop (q.length - nc.1)) +
            θ * (rowExt (d nc.1 nc.2) (q.drop (q.length - nc.1)) - 1))).sum := by
  have hp := plan_placed insts hs m d
  rw [claimed_sum, link_claim _ q θ fun b hb => ?_, planFracBlocks, List.map_map]
  · rfl
  · -- A placed block of 2^n leaves at index c fits: n <= M and c < 2^(M - n).
    have hsub := hp.1 b hb
    have hlast : (b.c + 1) * 2 ^ b.n - 1 ∈ b.leaves := by
      simp only [FracBlock.leaves, leavesOf, mem_Ico, add_mul, one_mul]
      have := Nat.one_le_two_pow (n := b.n)
      generalize b.c * 2 ^ b.n = A; omega
    have hlt := mem_range.mp (hsub hlast)
    rw [← hq] at hlt
    have hle : (b.c + 1) * 2 ^ b.n ≤ 2 ^ q.length := by omega
    have hn : b.n ≤ q.length := by
      by_contra h
      have : 2 ^ q.length < 2 ^ b.n := Nat.pow_lt_pow_right (by norm_num) (by omega)
      nlinarith
    refine ⟨hn, ?_⟩
    rw [show 2 ^ q.length = 2 ^ (q.length - b.n) * 2 ^ b.n by rw [← pow_add]; congr 1; omega] at hle
    exact Nat.lt_of_succ_le (Nat.le_of_mul_le_mul_right hle (by positivity))

end Link

end Plonky3Lean.Proofs.MultiStark
