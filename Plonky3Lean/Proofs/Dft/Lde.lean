module

public import Plonky3Lean.Proofs.Dft.Basic

@[expose] public section

/-!
# What an extension computes

Evaluating the padded coefficients is evaluating the interpolant, column by column.

With nested generators and shift one, every 2^a-th row of the extension is a row of the input.
-/

set_option linter.unusedSectionVars false

namespace Plonky3Lean.Proofs.Dft

open Finset Polynomial Plonky3Lean.Spec.Dft

variable {K : Type _} [Field K] [DecidableEq K]

/-- Column c of a vector of rows. -/
def col {w : ℕ} (c : Fin w) : (Fin w → K) →ₗ[K] K := LinearMap.proj c

theorem idft_col {w : ℕ} (c : Fin w) (ω : K) (n : ℕ) (x : ℕ → Fin w → K) (j : ℕ) :
    idft ω n x j c = idft ω n (fun i => x i c) j := by
  simp [idft, Finset.sum_apply]

theorem cosetDft_col {w : ℕ} (c : Fin w) (s ω : K) (n : ℕ) (x : ℕ → Fin w → K) (r : ℕ) :
    cosetDft s ω n x r c = cosetDft s ω n (fun i => x i c) r := by
  simp [cosetDft, Finset.sum_apply]

/-- Column c of an extension is the interpolant of column c, evaluated at s g^r. -/
theorem lde_col_eval {ω g : K} {k : ℕ} (hω : IsPrimitiveRoot ω (2 ^ k)) {N : ℕ} (hN : 2 ^ k ≤ N)
    (s : K) {w : ℕ} (x : ℕ → Fin w → K) (c : Fin w) (r : ℕ) :
    cosetDft s g N (padCoeffs ω (2 ^ k) x) r c =
      (interpolant ω (2 ^ k) (fun i => x i c)).eval (s * g ^ r) := by
  rw [cosetDft_col, ← poly_idft_eq_interpolant hω, eval_poly, cosetDft]
  rw [← sum_subset (Finset.range_mono hN) (fun j _ hj => by
    simp only [mem_range, not_lt] at hj
    simp [padCoeffs, show ¬ j < 2 ^ k by omega])]
  refine sum_congr rfl fun j hj => ?_
  simp [padCoeffs, mem_range.mp hj, idft_col]

/-- The transform at omega is the polynomial of each column, evaluated at omega^i. -/
theorem dft_col_eval (ω : K) (n : ℕ) {w : ℕ} (x : ℕ → Fin w → K) (c : Fin w) (i : ℕ) :
    dft ω n x i c = (poly n (fun j => x j c)).eval (ω ^ i) := by
  rw [eval_poly]
  simp [dft, Finset.sum_apply, ← pow_mul]

/-- With g^(2^a) = omega and shift one, row i 2^a of the extension is row i of the input. -/
theorem lde_extends {V : Type _} [AddCommGroup V] [Module K V] {ω g : K} {k a : ℕ}
    (hω : IsPrimitiveRoot ω (2 ^ k)) (hg : g ^ 2 ^ a = ω) (x : ℕ → V) {i : ℕ} (hi : i < 2 ^ k) :
    cosetDft 1 g (2 ^ (k + a)) (padCoeffs ω (2 ^ k) x) (i * 2 ^ a) = x i := by
  have : NeZero (2 ^ k) := ⟨by positivity⟩
  rw [cosetDft_eq, dft]
  rw [← sum_subset (s₁ := range (2 ^ k)) (Finset.range_mono (Nat.pow_le_pow_right (by norm_num)
    (by omega))) (fun j _ hj => by
      simp only [mem_range, not_lt] at hj
      simp [padCoeffs, show ¬ j < 2 ^ k by omega])]
  rw [← dft_idft hω x hi, dft]
  refine sum_congr rfl fun j hj => ?_
  simp only [one_pow, one_smul, padCoeffs, mem_range.mp hj, ↓reduceIte]
  rw [← hg, ← pow_mul]
  congr 2
  ring

end Plonky3Lean.Proofs.Dft
