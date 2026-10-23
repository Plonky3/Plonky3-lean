module

public import Plonky3Lean.Proofs.Sumcheck.Decoded
public import P3Sumcheck
public import Mathlib.Tactic.ComputeDegree

@[expose] public section

/-!
# The quadratic round: two values on the wire

A round sends h(0) and the leading coefficient h(inf) of a quadratic h.

The verifier rebuilds h(1) = c - h(0) from the running claim c, and evaluates h at the challenge:

```text
    h(r) = h(0) (1 - r) + h(1) r + h(inf) r (r - 1)
```

Every quadratic with h(0) + h(1) = c has exactly one such message, so this is the verifier of Section 4.1 at d = 2.
-/

namespace Plonky3Lean.Proofs.Sumcheck

open Polynomial p3_sumcheck.mirror p3_sumcheck.lagrange.mirror

variable {F : Type _} [Field F]

/-- The quadratic with values e0, e1 at 0, 1 and coefficient e_inf on X^2. -/
noncomputable def quad (e0 e1 e_inf : F) : F[X] := C e0 * (1 - X) + C e1 * X + C e_inf * (X * (X - 1))

theorem eval_quad (e0 e1 e_inf r : F) : (quad e0 e1 e_inf).eval r = extrapolate_01inf e0 e1 e_inf r := by
  simp [quad, extrapolate_01inf, lagrange_weights_01inf]

theorem natDegree_quad (e0 e1 e_inf : F) : (quad e0 e1 e_inf).natDegree ≤ 2 := by
  unfold quad; compute_degree

theorem quad_eq (e0 e1 e_inf : F) : quad e0 e1 e_inf = C e0 + C (e1 - e0 - e_inf) * X + C e_inf * X ^ 2 := by
  simp only [quad, map_sub]; ring

theorem eval_zero_quad (e0 e1 e_inf : F) : (quad e0 e1 e_inf).eval 0 = e0 := by simp [quad]

theorem eval_one_quad (e0 e1 e_inf : F) : (quad e0 e1 e_inf).eval 1 = e1 := by simp [quad]

theorem coeff_two_quad (e0 e1 e_inf : F) : (quad e0 e1 e_inf).coeff 2 = e_inf := by
  simp [quad_eq]

/-- A polynomial of degree at most 2 is the quadratic through its values at 0, 1 and its X^2 coefficient. -/
theorem eq_quad {p : F[X]} (hp : p.natDegree ≤ 2) : p = quad (p.eval 0) (p.eval 1) (p.coeff 2) := by
  have h1 : p.eval 1 = p.coeff 0 + p.coeff 1 + p.coeff 2 := by
    simp [eval_eq_sum_range' (show p.natDegree < 3 by omega), Finset.sum_range_succ]
  rw [quad_eq, h1, ← coeff_zero_eq_eval_zero]
  ext (_ | _ | _ | n)
  · simp
  · simp [coeff_C]; ring
  · simp
  · simp [coeff_eq_zero_of_natDegree_lt (show p.natDegree < n + 3 by omega)]

/-- The X^2 coefficient of a product of two polynomials of degree at most 1 is the product of their slopes. -/
theorem coeff_two_mul_of_linear {p q : F[X]} (hp : p.natDegree ≤ 1) (hq : q.natDegree ≤ 1) :
    (p * q).coeff 2 = (p.eval 1 - p.eval 0) * (q.eval 1 - q.eval 0) := by
  rw [eq_X_add_C_of_natDegree_le_one hp, eq_X_add_C_of_natDegree_le_one hq,
    show (C (p.coeff 1) * X + C (p.coeff 0)) * (C (q.coeff 1) * X + C (q.coeff 0)) =
      C (p.coeff 1 * q.coeff 1) * X ^ 2 + (C (p.coeff 1 * q.coeff 0 + p.coeff 0 * q.coeff 1) * X +
        C (p.coeff 0 * q.coeff 0)) by simp only [map_mul, map_add]; ring]
  simp only [coeff_add, coeff_C_mul_X_pow, coeff_C_mul_X, coeff_C]
  simp

/-! ## The evaluation basis -/

/-- The polynomial a message [h(0), h(inf)] stands for under the claim c. -/
noncomputable def decEval (c : F) (m : F × F) : F[X] := quad m.1 (c - m.1) m.2

/-- The message of a quadratic: its value at 0 and its X^2 coefficient. -/
noncomputable def encEval (p : F[X]) : F × F := (p.eval 0, p.coeff 2)

theorem reduce_claim_evaluation (c_a c_inf r c : F) :
    Basis.Evaluation.reduce_claim c_a c_inf r c = (decEval c (c_a, c_inf)).eval r :=
  (eval_quad _ _ _ _).symm

theorem natDegree_decEval (c : F) (m : F × F) : (decEval c m).natDegree ≤ 2 := natDegree_quad _ _ _

theorem decEval_sum (c : F) (m : F × F) : (decEval c m).eval 0 + (decEval c m).eval 1 = c := by
  simp [decEval, eval_zero_quad, eval_one_quad]

theorem decEval_encEval {c : F} {p : F[X]} (hp : p.natDegree ≤ 2) (hc : p.eval 0 + p.eval 1 = c) :
    decEval c (encEval p) = p := by
  rw [eq_quad hp]
  simp [decEval, encEval, eval_zero_quad, coeff_two_quad, ← hc]

/-! ## The projective basis -/

/-- The polynomial a message [s(1), s(inf)] stands for under the claim c. -/
noncomputable def decProj (c : F) (m : F × F) : F[X] := quad (c - m.2) m.1 m.2

theorem reduce_claim_projective (c_a c_inf r c : F) :
    Basis.Projective.reduce_claim c_a c_inf r c = (decProj c (c_a, c_inf)).eval r :=
  (eval_quad _ _ _ _).symm

/-- The projective identity: s(0) + s(inf) = c, with s(1) the first value sent. -/
theorem decProj_identity (c : F) (m : F × F) :
    (decProj c m).eval 0 + (decProj c m).coeff 2 = c ∧ (decProj c m).eval 1 = m.1 := by
  simp [decProj, eval_zero_quad, eval_one_quad, coeff_two_quad]

end Plonky3Lean.Proofs.Sumcheck
