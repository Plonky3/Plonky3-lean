module

public import Mathlib.LinearAlgebra.Lagrange

@[expose] public section

/-!
# Newton's divided differences

For distinct nodes v_0, v_1, ..., the divided difference f[v_a, ..., v_b] is the top coefficient of the interpolant P_{a,b} on the nodes a, ..., b.

Neville's identity gives the recurrence the table computes,

```text
    f[v_a..v_b] = (f[v_(a+1)..v_b] - f[v_a..v_(b-1)]) / (v_b - v_a)
```

and the Newton form rebuilds the interpolant one basis polynomial at a time:

```text
    P_{0,k} = sum_{m <= k} f[v_0..v_m] prod_{j < m} (X - v_j)
```
-/

namespace Plonky3Lean.Proofs.Stir

open Polynomial Finset

set_option linter.unusedSectionVars false

variable {K : Type _} [Field K] [DecidableEq K]

/-- The interpolant on the nodes a, ..., b. -/
noncomputable def interpAB (v r : ℕ → K) (a b : ℕ) : K[X] := Lagrange.interpolate (Icc a b) v r

/-- The divided difference f[v_a, ..., v_b]: the coefficient of X^(b - a) of the interpolant. -/
noncomputable def divDiff (v r : ℕ → K) (a b : ℕ) : K := (interpAB v r a b).coeff (b - a)

variable {v : ℕ → K} (r : ℕ → K)

theorem degree_interpAB_lt (hv : Set.InjOn v (Icc a b : Set ℕ)) :
    (interpAB v r a b).degree < (b + 1 - a : ℕ) := by
  have := Lagrange.degree_interpolate_lt r hv
  rwa [Nat.card_Icc] at this

theorem eval_interpAB (hv : Set.InjOn v (Icc a b : Set ℕ)) {i : ℕ} (hi : i ∈ Icc a b) :
    (interpAB v r a b).eval (v i) = r i :=
  Lagrange.eval_interpolate_at_node r hv hi

theorem coeff_interpAB_eq_zero (hv : Set.InjOn v (Icc a b : Set ℕ)) {m : ℕ} (hm : b + 1 - a ≤ m) :
    (interpAB v r a b).coeff m = 0 :=
  coeff_eq_zero_of_degree_lt ((degree_interpAB_lt r hv).trans_le (by exact_mod_cast hm))

theorem degree_X_sub_C_mul_lt {p : K[X]} {m : ℕ} (hp : p.degree < m) (c : K) :
    ((X - C c) * p).degree < ((m + 1 : ℕ) : WithBot ℕ) := by
  by_cases h0 : p = 0
  · simp [h0]
  rw [degree_mul, degree_X_sub_C, degree_eq_natDegree h0] at *
  have : p.natDegree < m := by exact_mod_cast hp
  exact_mod_cast (by omega : 1 + p.natDegree < m + 1)

/-- Neville's identity: the interpolant on a..b from those on a+1..b and a..b-1. -/
theorem interpAB_neville (hv : Set.InjOn v (Icc a b : Set ℕ)) (hab : a < b) :
    interpAB v r a b = C (v b - v a)⁻¹ *
      ((X - C (v a)) * interpAB v r (a + 1) b - (X - C (v b)) * interpAB v r a (b - 1)) := by
  have hv1 : Set.InjOn v (Icc (a + 1) b : Set ℕ) := hv.mono (by
    intro x hx; simp only [coe_Icc, Set.mem_Icc] at hx ⊢; omega)
  have hv2 : Set.InjOn v (Icc a (b - 1) : Set ℕ) := hv.mono (by
    intro x hx; simp only [coe_Icc, Set.mem_Icc] at hx ⊢; omega)
  have hba : v b - v a ≠ 0 := sub_ne_zero.2 fun h =>
    absurd (hv (by simp; omega) (by simp; omega) h) (by omega)
  symm
  refine Lagrange.eq_interpolate_of_eval_eq _ hv ?_ fun i hi => ?_
  · rw [Nat.card_Icc, ← smul_eq_C_mul]
    refine (degree_smul_le _ _).trans_lt ((degree_sub_le _ _).trans_lt (max_lt ?_ ?_))
    · have := degree_X_sub_C_mul_lt (degree_interpAB_lt r hv1) (v a)
      rwa [show b + 1 - (a + 1) + 1 = b + 1 - a by omega] at this
    · have := degree_X_sub_C_mul_lt (degree_interpAB_lt r hv2) (v b)
      rwa [show b - 1 + 1 - a + 1 = b + 1 - a by omega] at this
  · have hi' := mem_Icc.1 hi
    simp only [eval_mul, eval_C, eval_sub, eval_X]
    by_cases hia : i = a
    · subst hia
      rw [eval_interpAB r hv2 (by simp; omega)]
      field_simp; ring
    by_cases hib : i = b
    · subst hib
      rw [eval_interpAB r hv1 (by simp; omega)]
      simp only [sub_self, zero_mul, sub_zero]
      field_simp
    rw [eval_interpAB r hv1 (by simp; omega), eval_interpAB r hv2 (by simp; omega)]
    field_simp; ring

/-- The recurrence of divided differences. -/
theorem divDiff_succ (hv : Set.InjOn v (Icc a b : Set ℕ)) (hab : a < b) :
    divDiff v r a b = (divDiff v r (a + 1) b - divDiff v r a (b - 1)) * (v b - v a)⁻¹ := by
  have hv1 : Set.InjOn v (Icc (a + 1) b : Set ℕ) := hv.mono (by
    intro x hx; simp only [coe_Icc, Set.mem_Icc] at hx ⊢; omega)
  have hv2 : Set.InjOn v (Icc a (b - 1) : Set ℕ) := hv.mono (by
    intro x hx; simp only [coe_Icc, Set.mem_Icc] at hx ⊢; omega)
  have hk : b - a = (b - a - 1) + 1 := by omega
  unfold divDiff
  rw [interpAB_neville r hv hab, coeff_C_mul, coeff_sub, mul_comm (X - C (v a)),
    mul_comm (X - C (v b)), hk, coeff_mul_X_sub_C, coeff_mul_X_sub_C,
    coeff_interpAB_eq_zero r hv1 (m := b - a - 1 + 1) (by omega),
    coeff_interpAB_eq_zero r hv2 (m := b - a - 1 + 1) (by omega), show b - (a + 1) = b - a - 1 by omega, show b - 1 - a = b - a - 1 by omega]
  ring

/-- The basis polynomial prod_{j < m} (X - v_j). -/
noncomputable def newtonBasis (v : ℕ → K) (m : ℕ) : K[X] := ∏ j ∈ range m, (X - C (v j))

theorem newtonBasis_monic (m : ℕ) : (newtonBasis v m).Monic :=
  monic_prod_of_monic _ _ fun j _ => monic_X_sub_C (v j)

theorem natDegree_newtonBasis (m : ℕ) : (newtonBasis v m).natDegree = m := by
  rw [newtonBasis, natDegree_prod_of_monic _ _ fun j _ => monic_X_sub_C (v j)]; simp

/-- The Newton form: the interpolant on 0..k is sum_{m <= k} f[v_0..v_m] prod_{j < m} (X - v_j). -/
theorem interpAB_newton (k : ℕ) (hv : Set.InjOn v (Icc 0 k : Set ℕ)) :
    interpAB v r 0 k = ∑ m ∈ range (k + 1), C (divDiff v r 0 m) * newtonBasis v m := by
  induction k with
  | zero =>
    simp [interpAB, divDiff, newtonBasis]
  | succ k ih =>
    have hvk : Set.InjOn v (Icc 0 k : Set ℕ) := hv.mono (by
      intro x hx; simp only [coe_Icc, Set.mem_Icc] at hx ⊢; omega)
    rw [sum_range_succ, ← ih hvk]
    have hB := newtonBasis_monic (v := v) (k + 1)
    have hBd := natDegree_newtonBasis (v := v) (k + 1)
    rw [← sub_eq_zero, sub_add_eq_sub_sub]
    refine Polynomial.eq_zero_of_degree_lt_of_eval_index_eq_zero (s := Icc 0 k) (hvs := hvk) ?_ fun j hj => ?_
    · rw [Nat.card_Icc, degree_lt_iff_coeff_zero]
      intro m hm
      simp only [coeff_sub, coeff_C_mul]
      rw [coeff_interpAB_eq_zero r hvk (by omega)]
      rcases Nat.lt_or_ge (k + 1) m with hm' | hm'
      · rw [coeff_interpAB_eq_zero r hv (by omega),
          coeff_eq_zero_of_natDegree_lt (by omega : (newtonBasis v (k + 1)).natDegree < m)]
        ring
      · obtain rfl : m = k + 1 := by omega
        have hc : (newtonBasis v (k + 1)).coeff (k + 1) = 1 := by
          simpa [hBd] using hB.coeff_natDegree
        rw [hc]; simp [divDiff]
    · have hj' := mem_Icc.1 hj
      simp only [eval_sub, eval_mul, eval_C]
      rw [eval_interpAB r hv (by simp; omega), eval_interpAB r hvk hj]
      have : (newtonBasis v (k + 1)).eval (v j) = 0 := by
        rw [newtonBasis, eval_prod]
        exact prod_eq_zero (i := j) (mem_range.2 (by omega)) (by simp)
      rw [this]; ring

end Plonky3Lean.Proofs.Stir
