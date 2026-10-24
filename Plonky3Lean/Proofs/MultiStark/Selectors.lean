module

public import Plonky3Lean.Proofs.MultiStark.Ext
public import P3MultiStark.Mirror.Selectors

@[expose] public section

/-!
# The boundary selectors are the extensions of their row indicators

The verifier evaluates the three selectors at the bound point in closed form:

```text
    first(r)       = prod_i (1 - r_i)        = eq(0, r)
    last(r)        = prod_i r_i              = eq(1...1, r)
    transition(r)  = 1 - last(r)
```

Each is the multilinear extension of its row indicator.

So on a row of the cube each selector is exactly 0 or 1.

These are true indicators, not scaled ones.

The prover folds the same selectors one coordinate at a time.

Its prefix-aware form agrees with the closed form.
-/

namespace Plonky3Lean.Proofs.MultiStark

open Plonky3Lean.Spec.MultiStark Plonky3Lean.Spec.MultilinearUtil Plonky3Lean.Proofs.MultilinearUtil
  p3_multi_stark.selectors.mirror Finset

variable {K : Type _} [Field K]

theorem foldl_atStep (rs : List K) (a b : K) :
    rs.foldl atStep (a, b) = (a * (rs.map (1 - ·)).prod, b * rs.prod) := by
  induction rs generalizing a b with
  | nil => simp
  | cons r rs ih => simp only [List.foldl_cons, atStep, ih]; simp [mul_assoc]

theorem eq_vertex_zero (r : List K) : eq (vertex r.length 0) r = (r.map (1 - ·)).prod := by
  induction r with
  | nil => simp [vertex]
  | cons c r ih => rw [List.length_cons, vertex_zero_succ, eq_cons, ih]; simp

theorem eq_vertex_allOnes (r : List K) : eq (vertex r.length (2 ^ r.length - 1)) r = r.prod := by
  induction r with
  | nil => simp [vertex]
  | cons c r ih => rw [List.length_cons, vertex_allOnes_succ, eq_cons, ih]; simp

theorem rowExt_firstRow (r : List K) : rowExt firstRow r = eq (vertex r.length 0) r := by
  unfold rowExt
  rw [sum_eq_single_of_mem 0 (mem_range.mpr (Nat.two_pow_pos _)) fun b _ hb => by simp [firstRow, hb]]
  simp [firstRow]

theorem rowExt_lastRow (r : List K) :
    rowExt (lastRow r.length) r = eq (vertex r.length (2 ^ r.length - 1)) r := by
  have h1 := Nat.one_le_two_pow (n := r.length)
  unfold rowExt
  rw [sum_eq_single_of_mem (2 ^ r.length - 1) (mem_range.mpr (by omega)) fun b _ hb => by
    simp [lastRow, show b + 1 ≠ 2 ^ r.length by omega]]
  simp [lastRow, show 2 ^ r.length - 1 + 1 = 2 ^ r.length by omega]

theorem rowExt_transitionRow (r : List K) :
    rowExt (transitionRow r.length) r = 1 - rowExt (lastRow r.length) r := by
  rw [← sum_eq_vertex r]
  unfold rowExt
  rw [← sum_sub_distrib]
  exact sum_congr rfl fun b hb => by
    simp only [mem_range] at hb
    by_cases h : b + 1 < 2 ^ r.length
    · simp [transitionRow, lastRow, h, show b + 1 ≠ 2 ^ r.length by omega]
    · simp [transitionRow, lastRow, show b + 1 = 2 ^ r.length by omega]

/-- **The selectors are extensions.**

At any point, the closed form is the multilinear extension of the row indicators.

These are the first-row, last-row and transition indicators. -/
theorem at_eq_rowExt (rs : List K) :
    BoundaryEvals.at rs =
      ⟨rowExt firstRow rs, rowExt (lastRow rs.length) rs, rowExt (transitionRow rs.length) rs⟩ := by
  rw [rowExt_transitionRow, rowExt_lastRow, rowExt_firstRow, eq_vertex_zero, eq_vertex_allOnes]
  simp [BoundaryEvals.at, foldl_atStep]

/-- **The selectors are 0/1 on the cube.**

At row b of 2^n rows, the closed form is the row's three indicators. -/
theorem at_vertex {n b : ℕ} (hb : b < 2 ^ n) :
    BoundaryEvals.at (vertex n b : List K) = BoundaryEvals.from_row b (2 ^ n) := by
  rw [at_eq_rowExt, length_vertex, ext_vertex _ hb, ext_vertex _ hb, ext_vertex _ hb]
  simp [BoundaryEvals.from_row, firstRow, lastRow, transitionRow]

theorem prod_one_sub_vertex {n b : ℕ} (hb : b < 2 ^ n) :
    ((vertex n b : List K).map (1 - ·)).prod = if b = 0 then 1 else 0 := by
  have h := eq_vertex_zero (vertex n b : List K)
  rw [length_vertex, eq_vertex_vertex (Nat.two_pow_pos n) hb] at h
  rw [← h]; simp [eq_comm]

theorem prod_vertex {n b : ℕ} (hb : b < 2 ^ n) :
    (vertex n b : List K).prod = if b + 1 = 2 ^ n then 1 else 0 := by
  have h1 := Nat.one_le_two_pow (n := n)
  have h := eq_vertex_allOnes (vertex n b : List K)
  rw [length_vertex, eq_vertex_vertex (by omega) hb] at h
  rw [← h]
  by_cases hbe : b + 1 = 2 ^ n
  · simp [hbe, show 2 ^ n - 1 = b by omega]
  · simp [hbe, show 2 ^ n - 1 ≠ b by omega]

/-- **The prover's prefix-aware selectors.**

Bind the prefix p, and take row b of the residual cube.

The selectors there are the closed form at p followed by the row's vertex. -/
theorem from_row_with_prefix_at (p : List K) {n b : ℕ} (hb : b < 2 ^ n) :
    BoundaryEvals.from_row_with_prefix b (2 ^ n) (BoundaryEvals.at p) =
      BoundaryEvals.at (p ++ vertex n b) := by
  simp only [BoundaryEvals.from_row_with_prefix, BoundaryEvals.from_row, BoundaryEvals.at,
    List.foldl_append, foldl_atStep, one_mul,
    prod_one_sub_vertex hb, prod_vertex hb]
  by_cases hb1 : b + 1 = 2 ^ n
  · simp [hb1]
  · by_cases h0 : b = 0
    · subst h0
      have hn : n ≠ 0 := by rintro rfl; simp at hb1
      simp_all
    · simp [hb1, h0, show b + 1 < 2 ^ n by omega]

end Plonky3Lean.Proofs.MultiStark
