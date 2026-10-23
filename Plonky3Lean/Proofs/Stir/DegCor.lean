module

public import Plonky3Lean.Proofs.Stir.Horner
public import Mathlib.Algebra.Field.GeomSum

@[expose] public section

/-!
# Degree correction

Fact 4.10 gives the geometric sum in closed form, with its own value at ratio one:

```text
    sum_{l <= e} q^l = (1 - q^(e+1)) / (1 - q)    for q != 1
                     = e + 1                       for q = 1
```
-/

namespace Plonky3Lean.Proofs.Stir

open Polynomial Finset Plonky3Lean.Spec.Stir p3_stir.mirror p3_stir.utils.mirror

set_option linter.unusedSectionVars false

variable {K : Type _} [Field K] [DecidableEq K]

/-- Fact 4.10. -/
theorem geom_sum_closed (q : K) (e : ℕ) :
    ∑ l ∈ range (e + 1), q ^ l = if q = 1 then ((e + 1 : ℕ) : K) else (1 - q ^ (e + 1)) / (1 - q) := by
  split_ifs with h
  · simp [h]
  · rw [geom_sum_eq h, ← neg_div_neg_eq, neg_sub, neg_sub]

/-- The degree-correction factor is the value times sum_{l <= gap} (x r)^l, the case x r = 1 included.

It never panics. -/
theorem eval_degree_correction_eq (value point r_comb : K) (gap : ℕ) :
    eval_degree_correction value point r_comb gap =
      some (value * ∑ l ∈ range (gap + 1), (point * r_comb) ^ l) := by
  rw [geom_sum_closed]
  unfold eval_degree_correction
  by_cases h : point * r_comb = 1
  · simp [h]
  · have : (1 : K) - point * r_comb ≠ 0 := sub_ne_zero.2 (Ne.symm h)
    simp [h, inverse, this, div_eq_mul_inv]

/-- The degree-correction factor is DegCor(d*, r, f, d) at x, for gap = d* - d. -/
theorem eval_degree_correction_degCor (f : K → K) (x r : K) (dstar d : ℕ) :
    eval_degree_correction (f x) x r (dstar - d) = some (degCor dstar d r f x) := by
  rw [eval_degree_correction_eq]; rfl

/-- Degree correction raises the degree bound by the gap: deg f < d gives deg DegCor(d*, r, f, d) < d*. -/
theorem degree_polyDegCor_lt {dstar d : ℕ} (hd : d ≤ dstar) (r : K) {f : K[X]}
    (hf : f.degree < d) : (polyDegCor dstar d r f).degree < dstar := by
  unfold polyDegCor
  by_cases hf0 : f = 0
  · simp [hf0]
  have hs : (∑ l ∈ range (dstar - d + 1), (C r * X) ^ l).degree ≤ ((dstar - d : ℕ) : WithBot ℕ) := by
    refine (degree_sum_le _ _).trans (Finset.sup_le fun l hl => ?_)
    refine (degree_pow_le _ _).trans ?_
    have h1 : (C r * X).degree ≤ 1 := (degree_C_mul_X_le r)
    have : (l : WithBot ℕ) ≤ (dstar - d : ℕ) := by exact_mod_cast Nat.lt_succ_iff.1 (mem_range.1 hl)
    calc l • (C r * X).degree ≤ l • (1 : WithBot ℕ) := nsmul_le_nsmul_right h1 l
      _ = l := by simp
      _ ≤ _ := this
  have hfn : f.natDegree < d := (natDegree_lt_iff_degree_lt hf0).2 hf
  calc (f * _).degree ≤ f.degree + _ := degree_mul_le _ _
    _ ≤ (f.natDegree : WithBot ℕ) + (dstar - d : ℕ) := add_le_add (degree_le_natDegree) hs
    _ < dstar := by
      exact_mod_cast (by omega : f.natDegree + (dstar - d) < dstar)

/-- The polynomial degree correction evaluates to DegCor pointwise. -/
theorem eval_polyDegCor (dstar d : ℕ) (r : K) (f : K[X]) (x : K) :
    (polyDegCor dstar d r f).eval x = degCor dstar d r (fun y => f.eval y) x := by
  simp [polyDegCor, degCor, eval_finsetSum, mul_comm r x]

end Plonky3Lean.Proofs.Stir
