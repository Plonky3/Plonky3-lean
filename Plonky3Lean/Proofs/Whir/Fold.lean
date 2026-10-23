module

public import Plonky3Lean.Spec.Whir

@[expose] public section

/-!
# The fold of a queried row

The verifier folds the 2^k opened values of a row at the folding challenges.

On the interleaved codeword of P this gives the folded table's polynomial at the folded domain point.
-/

namespace Plonky3Lean.Proofs.Whir

open Finset Plonky3Lean.Spec.MultilinearUtil Plonky3Lean.Spec.Whir

variable {K : Type _} [CommRing K]

theorem block_end {n k j : ℕ} (hk : k ≤ n) (hj : j < 2 ^ k) : (j + 1) * 2 ^ (n - k) ≤ 2 ^ n :=
  (Nat.mul_le_mul_right _ hj).trans (by rw [← pow_add, Nat.add_sub_cancel' hk])

omit [CommRing K] in
theorem length_block (P : List K) {n k j : ℕ} (hP : P.length = 2 ^ n) (hk : k ≤ n) (hj : j < 2 ^ k) :
    (block P n k j).length = 2 ^ (n - k) := by
  have := block_end hk hj
  simp only [block, List.length_take, List.length_drop, hP]
  rw [add_mul, one_mul] at this; omega

omit [CommRing K] in
theorem getD_block [Zero K] (P : List K) {n k j c : ℕ} (hc : c < 2 ^ (n - k)) : (block P n k j).getD c 0 = P.getD (j * 2 ^ (n - k) + c) 0 := by
  simp [block, List.getD_eq_getElem?_getD, hc, List.getElem?_drop, add_comm]

/-- The fold of row i at r is the folded table's polynomial at omega^i. -/
theorem mle_row (P : List K) {n : ℕ} (hP : P.length = 2 ^ n) (r : List K) (hk : r.length ≤ n) (ω : K)
    (i : ℕ) : mle (row P n r.length ω i) r = uni (foldTable P n r) (ω ^ i) := by
  simp only [mle, uni, row, foldTable, List.length_map, List.length_range]
  rw [sum_congr rfl fun j hj => by
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range (mem_range.mp hj),
      Option.map_some, Option.getD_some, length_block P hP hk (mem_range.mp hj), mul_sum]]
  rw [sum_comm]
  refine sum_congr rfl fun c hc => ?_
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range (mem_range.mp hc),
    Option.map_some, Option.getD_some, sum_mul]
  refine sum_congr rfl fun j hj => ?_
  rw [getD_block P (mem_range.mp hc), mul_assoc]

end Plonky3Lean.Proofs.Whir
