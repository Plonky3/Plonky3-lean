module

public import Plonky3Lean.Proofs.Stir.Horner
public import Plonky3Lean.Proofs.Stir.FoldPaper

@[expose] public section

/-!
# PolyFold

Fact 4.6 for q = X^k splits f into its k parts, f(X) = sum_{l < k} X^l f_l(X^k), with f_l reading the coefficients l, l + k, l + 2k, ....

PolyFold(f, k, r) = sum_l r^l f_l, and on the points x with x^k = y the fold of f is PolyFold(f, k, alpha)(y).
-/

namespace Plonky3Lean.Proofs.Stir

open Polynomial Finset Plonky3Lean.Spec.Stir p3_stir.mirror p3_stir.utils.mirror

set_option linter.unusedSectionVars false

variable {K : Type _} [Field K] [DecidableEq K]

theorem coeff_splitPart (f : K[X]) {k : ℕ} (hk : 0 < k) (l i : ℕ) :
    (splitPart f k l).coeff i = f.coeff (i * k + l) := by
  simp only [splitPart, finsetSum_coeff, coeff_C_mul_X_pow]
  rw [sum_eq_single i (fun b _ hb => by simp [Ne.symm hb]) (fun hi => ?_)]
  · simp
  · have := mem_range.not.1 hi
    simp only [↓reduceIte]
    exact coeff_eq_zero_of_natDegree_lt (by nlinarith)

theorem coeff_polyFold (f : K[X]) {k : ℕ} (hk : 0 < k) (r : K) (m : ℕ) :
    (polyFold f k r).coeff m = ∑ l ∈ range k, r ^ l * f.coeff (m * k + l) := by
  simp only [polyFold, finsetSum_coeff, coeff_C_mul, coeff_splitPart f hk]

/-- Fact 4.6: f(x) = sum_{l < k} x^l f_l(x^k). -/
theorem eval_eq_sum_splitPart (f : K[X]) {k : ℕ} (hk : 0 < k) (x : K) :
    f.eval x = ∑ l ∈ range k, x ^ l * (splitPart f k l).eval (x ^ k) := by
  have hD : f.natDegree < (f.natDegree + 1) * k := by nlinarith
  rw [eval_eq_sum_range' hD, sum_range_mul_split, sum_comm]
  refine sum_congr rfl fun l _ => ?_
  rw [eval_eq_sum_range' (n := f.natDegree + 1), mul_sum]
  · refine sum_congr rfl fun m _ => ?_
    rw [coeff_splitPart f hk]; ring
  · refine (natDegree_sum_le_of_forall_le _ _ fun i hi => ?_).trans_lt (Nat.lt_succ_self _)
    exact (natDegree_C_mul_X_pow_le _ _).trans (Nat.lt_succ_iff.1 (mem_range.1 hi))

/-- PolyFold lowers the degree bound by k: deg f < k d gives deg PolyFold(f, k, r) < d. -/
theorem degree_polyFold_lt {f : K[X]} {k d : ℕ} (hk : 0 < k) (hf : f.degree < (k * d : ℕ))
    (r : K) : (polyFold f k r).degree < d := by
  rw [degree_lt_iff_coeff_zero]
  intro m hm
  rw [coeff_polyFold f hk]
  refine sum_eq_zero fun l _ => ?_
  rw [coeff_eq_zero_of_degree_lt (hf.trans_le ?_), mul_zero]
  exact_mod_cast (by nlinarith : k * d ≤ m * k + l)

/-- On a fiber of exactly k points x with x^k = y, the fold of f at alpha is PolyFold(f, k, alpha)(y). -/
theorem eval_interpolate_fiber {k : ℕ} (hk : 0 < k) {v : ℕ → K} (hv : Set.InjOn v (range k : Set ℕ))
    {y : K} (hy : ∀ l < k, v l ^ k = y) (f : K[X]) (α : K) :
    (Lagrange.interpolate (range k) v fun l => f.eval (v l)).eval α = (polyFold f k α).eval y := by
  set p : K[X] := ∑ l ∈ range k, C ((splitPart f k l).eval y) * X ^ l
  have hp : p = Lagrange.interpolate (range k) v fun l => f.eval (v l) := by
    refine Lagrange.eq_interpolate_of_eval_eq _ hv ?_ fun l hl => ?_
    · rw [card_range]
      refine (degree_sum_le _ _).trans_lt ((Finset.sup_lt_iff (WithBot.bot_lt_coe _)).2 fun i hi => ?_)
      exact (degree_C_mul_X_pow_le _ _).trans_lt (by exact_mod_cast mem_range.1 hi)
    · rw [eval_eq_sum_splitPart f hk, hy l (mem_range.1 hl)]
      simp only [p, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X]
      exact sum_congr rfl fun _ _ => mul_comm _ _
  rw [← hp]
  simp only [p, polyFold, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X]
  exact sum_congr rfl fun _ _ => mul_comm _ _

/-- fold_poly_coeffs: the coefficients of PolyFold(f, 2^a, gamma). -/
theorem fold_poly_coeffs_eq (coeffs : List K) (gamma : K) (a : ℕ) :
    ∃ out, fold_poly_coeffs coeffs gamma a = some out ∧
      coeffPoly out = polyFold (coeffPoly coeffs) (2 ^ a) gamma := by
  have hk : 0 < 2 ^ a := by positivity
  refine ⟨_, by simp [fold_poly_coeffs, chunks]; rfl, Polynomial.ext fun m => ?_⟩
  rw [coeff_coeffPoly, coeff_polyFold _ hk]
  simp only [coeff_coeffPoly]
  set n := (coeffs.length + 2 ^ a - 1) / 2 ^ a
  by_cases hm : m < n
  · rw [getD_map_range _ _ hm, Function.comp_apply, eval_poly_eq, eval_take_drop]
    refine sum_congr rfl fun l _ => ?_
    rw [mul_comm, mul_comm m]
  · rw [getD_of_le _ _ (by simpa using hm)]
    symm; refine sum_eq_zero fun l _ => ?_
    have : coeffs.length ≤ n * 2 ^ a := length_le_ceil_mul hk coeffs.length
    have h2 := Nat.mul_le_mul_right (2 ^ a) (Nat.le_of_not_lt hm)
    rw [getD_of_le _ _ (by omega), mul_zero]

end Plonky3Lean.Proofs.Stir
