module

public import Plonky3Lean.Proofs.UniStark.Recompose
public import Plonky3Lean.Proofs.Air.Degree

@[expose] public section

/-!
# The zero-knowledge variant

- The randomized trace doubles the trace's degree.

  The sizing adds one to the constraint degree and doubles the chunk count.

  That leaves room: a constraint of degree multiple d on a randomized trace fits the doubled chunks.

- The quotient chunks are masked by multiples of their own vanishing polynomials.

  The last mask is chosen to cancel the others.

  The verifier's recombination is unchanged by such masks.
-/

set_option linter.unusedSectionVars false

namespace Plonky3Lean.Proofs.UniStark

open Polynomial Finset
open p3_air.air.mirror p3_commit.domain.mirror p3_field.coset.mirror p3_dft.mirror
open Plonky3Lean.Proofs.Commit Plonky3Lean.Proofs.Air Plonky3Lean.Proofs.Dft

/-! ## The doubled chunk count -/

/-- Take the zero-knowledge bit, and let L be the sizing of d + 1.

Then a degree d (2n - 1) + 1 fits 2^(L + 1) chunks of n, plus one. -/
theorem zk_fits (d : ℕ) {n : ℕ} (hn : 1 ≤ n) {D : ℕ} (hD : D ≤ d * (2 * n - 1) + 1) :
    D < (2 ^ (log2_ceil_usize (max (d + 1) 2 - 1) + 1) + 1) * n := by
  have hL := le_two_pow_log2_ceil (max (d + 1) 2 - 1)
  rw [pow_succ]
  generalize 2 ^ log2_ceil_usize (max (d + 1) 2 - 1) = c at hL ⊢
  have hd : d ≤ c := le_trans (by omega) hL
  have : d * (2 * n - 1) ≤ c * (2 * n - 1) := Nat.mul_le_mul_right _ hd
  have h2n : c * (2 * n - 1) + c = c * 2 * n := by
    rw [← Nat.mul_succ, Nat.succ_eq_add_one, Nat.sub_add_cancel (by omega)]; ring
  have hc : 1 ≤ c := le_trans (by omega) hL
  nlinarith

/-! ## Masked quotient chunks -/

variable {K : Type _} [Field K] [DecidableEq K] {G : Gen K} (hV : GenValid G) (qd : Coset G) (l : ℕ)

/-- The normalization of chunk i: the product over the other chunks j of 1 / Z_j(s_i). -/
noncomputable def chunkWeight (i : ℕ) : K :=
  ∏ j ∈ (range (2 ^ l)).erase i,
    (Coset.vanishing_poly_at_point G (chunk G hV qd l j) (chunk G hV qd l i).shift)⁻¹

theorem chunkWeight_ne_zero (hl : l ≤ qd.log_size) {i : ℕ} (hi : i < 2 ^ l) :
    chunkWeight hV qd l i ≠ 0 :=
  prod_ne_zero_iff.mpr fun _ hj => inv_ne_zero fun h =>
    (mem_erase.mp hj).1 ((vanishing_chunk_first hV qd l hi (mem_range.mp (mem_erase.mp hj).2) hl).mp
      h).symm

/-- L_i Z_i is the weight of chunk i times the product of every chunk's vanishing polynomial. -/
theorem chunkL_mul_chunkZ {i : ℕ} (hi : i < 2 ^ l) :
    chunkL hV qd l i * chunkZ hV qd l i =
      C (chunkWeight hV qd l i) * ∏ j ∈ range (2 ^ l), chunkZ hV qd l j := by
  rw [chunkL, prod_mul_distrib, ← map_prod, chunkWeight, mul_assoc,
    prod_erase_mul _ _ (mem_range.mpr hi)]

/-- The masks: t_i on every chunk but the last.

The last gets minus the weighted sum of the others. -/
noncomputable def mask (t : ℕ → K[X]) (i : ℕ) : K[X] :=
  if i < 2 ^ l - 1 then t i
  else -∑ j ∈ range (2 ^ l - 1),
    C (chunkWeight hV qd l j / chunkWeight hV qd l (2 ^ l - 1)) * t j

/-- Masking chunk i by Z_i times its mask leaves the recombination polynomial unchanged. -/
theorem recombination_masked (hl : l ≤ qd.log_size) (q t : ℕ → K[X]) :
    ∑ i ∈ range (2 ^ l), chunkL hV qd l i * (q i + chunkZ hV qd l i * mask hV qd l t i) =
      ∑ i ∈ range (2 ^ l), chunkL hV qd l i * q i := by
  have hlast : 2 ^ l - 1 < 2 ^ l := Nat.sub_lt Nat.one_le_two_pow one_pos
  have hw := chunkWeight_ne_zero hV qd l hl hlast
  simp only [mul_add, sum_add_distrib, add_eq_left]
  have : ∀ i ∈ range (2 ^ l), chunkL hV qd l i * (chunkZ hV qd l i * mask hV qd l t i) =
      (∏ j ∈ range (2 ^ l), chunkZ hV qd l j) * (C (chunkWeight hV qd l i) * mask hV qd l t i) :=
    fun i hi => by rw [← mul_assoc, chunkL_mul_chunkZ hV qd l (mem_range.mp hi)]; ring
  rw [sum_congr rfl this, ← mul_sum, mul_eq_zero]
  right
  rw [show 2 ^ l = 2 ^ l - 1 + 1 by omega, sum_range_succ]
  simp only [mask, show ¬ 2 ^ l - 1 < 2 ^ l - 1 from lt_irrefl _, ↓reduceIte]
  rw [sum_congr rfl (g := fun i => C (chunkWeight hV qd l i) * t i) fun i hi => by
    simp only [mem_range.mp hi, ↓reduceIte], mul_neg, mul_sum]
  simp only [← mul_assoc, ← C_mul, mul_div_cancel₀ _ hw]
  exact add_neg_cancel _

/-- A mask of degree below m keeps a chunk below the randomized chunk's size 2m. -/
theorem natDegree_masked_lt {m : ℕ} (hm : m = 2 ^ (qd.log_size - l)) {q t : K[X]} {i : ℕ}
    (hq : q.natDegree < m) (ht : t.natDegree < m) :
    (q + chunkZ hV qd l i * t).natDegree < 2 * m := by
  refine (natDegree_add_le _ _).trans_lt (max_lt (by omega) ?_)
  refine (natDegree_mul_le).trans_lt ?_
  have := natDegree_chunkZ_le hV qd l i
  omega

end Plonky3Lean.Proofs.UniStark
