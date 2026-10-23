module

public import P3Circle.Point
public import Plonky3Lean.Spec.Circle
public import Plonky3Lean.Proofs.Circle.Util
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Algebra.Polynomial.Derivative

@[expose] public section

/-!
# p3-circle: the points and the group law

Every map on points agrees with the group law of the circle, on points of the circle.

So every point the crate builds from points of the circle lies on the circle, and the constructor's debug assertion never fires.
-/

namespace Plonky3Lean.Proofs.Circle

open Plonky3Lean.Spec.Circle p3_circle.point.mirror Finset

set_option linter.unusedSectionVars false

variable {K : Type _} [Field K] [DecidableEq K]

/-- The point of the model with the coordinates of a point of the circle. -/
def ofC (P : C K) : Point K := ⟨P.x, P.y⟩

theorem ofC_injective : Function.Injective (ofC : C K → Point K) := by
  intro P Q h
  simp only [ofC, Point.mk.injEq] at h
  exact C.ext h.1 h.2

@[simp] theorem ofC_x (P : C K) : (ofC P).x = P.x := rfl
@[simp] theorem ofC_y (P : C K) : (ofC P).y = P.y := rfl

theorem ZERO_eq : (Point.ZERO : Point K) = ofC 0 := rfl

theorem neg_ofC (P : C K) : Point.neg (ofC P) = ofC (-P) := rfl

theorem add_ofC (P Q : C K) : Point.add (ofC P) (ofC Q) = ofC (P + Q) := rfl

theorem sub_ofC (P Q : C K) : Point.sub (ofC P) (ofC Q) = ofC (P - Q) := by
  simp only [Point.sub, Point.new, ofC, C.sub_x, C.sub_y]

theorem double_ofC (P : C K) : Point.double (ofC P) = ofC (2 • P) := by
  simp only [Point.double, Point.new, ofC, two_nsmul, C.add_x, C.add_y, Point.mk.injEq]
  constructor
  · linear_combination P.eq
  · ring

theorem vnStep_x (P : C K) : Point.vnStep P.x = (2 • P).x := by
  rw [C.two_nsmul_x, Point.vnStep]; ring

theorem repeated_double_ofC (P : C K) (n : ℕ) :
    Point.repeated_double (ofC P) n = ofC (2 ^ n • P) := by
  induction n generalizing P with
  | zero => simp [Point.repeated_double]
  | succ n ih => rw [Point.repeated_double, double_ofC, ih, smul_smul, ← pow_succ]

theorem vnStep_iterate (P : C K) (m : ℕ) : Point.vnStep^[m] P.x = (2 ^ m • P).x := by
  induction m generalizing P with
  | zero => simp
  | succ m ih => rw [Function.iterate_succ_apply, vnStep_x, ih, smul_smul, ← pow_succ]

/-- v_n is the vanishing polynomial of equation (8) for log_n >= 1, and panics at log_n = 0. -/
theorem v_n_ofC (P : C K) (n : ℕ) :
    Point.v_n (ofC P) n = if 1 ≤ n then some (vn n P) else none := by
  simp only [Point.v_n, ge_iff_le, ofC_x, vnStep_iterate, vn]

theorem vnProdLoop_ofC (P : C K) (n : ℕ) (out : K) :
    Point.vnProdLoop n P.x out = out * ∏ k ∈ range n, (2 ^ (k + 1) • P).x := by
  induction n generalizing P out with
  | zero => simp [Point.vnProdLoop]
  | succ n ih =>
    rw [Point.vnProdLoop, vnStep_x, ih, prod_range_succ']
    simp only [smul_smul, ← pow_succ, zero_add, pow_one]
    ring

/-- v_n_prod is the product of v_1, ..., v_(log_n - 1). -/
theorem v_n_prod_ofC (P : C K) (n : ℕ) :
    Point.v_n_prod (ofC P) n = ∏ k ∈ range (n - 1), vn (k + 1) P := by
  unfold Point.v_n_prod
  split_ifs with h
  · rw [show n - 1 = 0 by omega, prod_range_zero]
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
    rw [show m + 2 - 2 = m by omega, show m + 2 - 1 = m + 1 by omega, ofC_x, vnProdLoop_ofC,
      prod_range_succ']
    simp [vn, mul_comm]

theorem mulLoop_ofC (R S : C K) (n : ℕ) :
    Point.mulLoop (ofC R) (ofC S) n = ofC (R + n • S) := by
  induction n using Nat.strong_induction_on generalizing R S with
  | _ n ih =>
    rw [Point.mulLoop]
    split_ifs with h0 h1
    · simp [h0]
    · rw [add_ofC, double_ofC, ih _ (by omega)]
      congr 1
      conv_rhs => rw [← Nat.mod_add_div n 2, h1]
      simp only [add_nsmul, one_nsmul, smul_smul, mul_comm]
      abel
    · rw [double_ofC, ih _ (by omega)]
      congr 1
      conv_rhs => rw [← Nat.mod_add_div n 2, show n % 2 = 0 by omega]
      simp only [zero_add, smul_smul, mul_comm]

/-- The scalar multiplication by double-and-add is n P. -/
theorem mul_ofC (P : C K) (n : ℕ) : Point.mul (ofC P) n = ofC (n • P) := by
  rw [Point.mul, ZERO_eq, mulLoop_ofC, zero_add]


/-! ## The projective line -/

/-- The inverse stereographic projection of Lemma 1, t -> ((1 - t^2) / (1 + t^2), 2 t / (1 + t^2)), off t^2 = -1. -/
def stereo (t : K) (ht : 1 + t * t ≠ 0) : C K :=
  C.mk ((1 - t * t) * (1 + t * t)⁻¹) ((t + t) * (1 + t * t)⁻¹) (by
    rw [mul_pow, mul_pow, ← add_mul, inv_pow, ← div_eq_mul_inv, div_eq_one_iff_eq (pow_ne_zero 2 ht)]
    ring)

/-- The point from the projective line panics exactly at t^2 = -1, and lies on the circle otherwise. -/
theorem from_projective_line_eq (t : K) :
    Point.from_projective_line t = if ht : 1 + t * t = 0 then none else some (ofC (stereo t ht)) := by
  unfold Point.from_projective_line inv p3_commit.domain.mirror.inv
  split_ifs <;> simp_all [Point.new, ofC, stereo]

/-- The projection to the line is y / (x + 1), and none exactly at x = -1. -/
theorem to_projective_line_ofC (P : C K) :
    Point.to_projective_line (ofC P) = if P.x + 1 = 0 then none else some (P.y / (P.x + 1)) := by
  unfold Point.to_projective_line tryInverse
  by_cases h : P.x + 1 = 0 <;> simp [h, div_eq_inv_mul]

/-- Lemma 1, one way: projecting the point of t gives back t. -/
theorem to_from_projective_line (h2 : (2 : K) ≠ 0) (t : K) (ht : 1 + t * t ≠ 0) :
    Point.to_projective_line (ofC (stereo t ht)) = some t := by
  rw [to_projective_line_ofC]
  have ht2 : 1 + t ^ 2 ≠ 0 := by rwa [sq]
  have hx : (stereo t ht).x + 1 = 2 * (1 + t * t)⁻¹ := by
    simp only [stereo, C.mk_x]; field_simp; ring
  have hne : (stereo t ht).x + 1 ≠ 0 := by rw [hx]; exact mul_ne_zero h2 (inv_ne_zero ht)
  simp only [hne, ↓reduceIte]
  rw [hx]
  simp only [stereo, C.mk_y, Option.some.injEq]
  field_simp
  ring

/-- Lemma 1, the other way: off x = -1, the point of the projection y / (x + 1) is the point itself. -/
theorem from_to_projective_line (h2 : (2 : K) ≠ 0) (P : C K) (hP : P.x + 1 ≠ 0) :
    ∃ ht, stereo (P.y / (P.x + 1)) ht = P := by
  have hy : P.y ^ 2 = (1 - P.x) * (P.x + 1) := by linear_combination P.eq
  have hden : 1 + P.y / (P.x + 1) * (P.y / (P.x + 1)) = 2 / (P.x + 1) := by
    field_simp; linear_combination P.eq
  refine ⟨by rw [hden]; exact div_ne_zero h2 hP, C.ext ?_ ?_⟩
  · simp only [stereo, C.mk_x, hden]; field_simp; linear_combination -P.eq
  · simp only [stereo, C.mk_y, hden]; field_simp; ring

/-! ## The selectors and the single-point vanishing function -/

/-- v_tilde_p(p, at) projects at - p to the line, and panics exactly when (at - p).x = -1. -/
theorem v_tilde_p_ofC (P Q : C K) :
    Point.v_tilde_p (ofC P) (ofC Q) =
      if (Q - P).x + 1 = 0 then none else some ((Q - P).y / ((Q - P).x + 1)) := by
  rw [Point.v_tilde_p, sub_ofC, to_projective_line_ofC]

theorem recip_v_tilde_p_num_den_ofC (P Q : C K) :
    Point.recip_v_tilde_p_num_den (ofC P) (ofC Q) = ((Q - P).x + 1, (Q - P).y) := by
  rw [Point.recip_v_tilde_p_num_den, sub_ofC]; rfl

/-- v_p(p, at) is the complex conjugate of the paper's v_P(at), equation (11). -/
theorem v_p_ofC (P Q : C K) :
    Point.v_p (ofC P) (ofC Q) = ((vP P Q).1, -(vP P Q).2) := by
  simp only [Point.v_p, neg_ofC, add_ofC, ofC_x, ofC_y, vP, vBlock, C.add_x, C.add_y, C.neg_x,
    C.neg_y, Prod.mk.injEq]
  constructor <;> ring


/-! ## The normalizer of the single-point selector -/

open Polynomial in
/-- The vanishing polynomial v_(m+1) as a polynomial in x: v_1 = X and v_(m+2) = 2 v_(m+1)^2 - 1. -/
noncomputable def vnPoly : ℕ → K[X]
  | 0 => X
  | m + 1 => 2 * vnPoly m ^ 2 - 1

open Polynomial in
theorem vn_eq_eval (P : C K) (m : ℕ) : vn (m + 1) P = (vnPoly m).eval P.x := by
  induction m with
  | zero => simp [vn, vnPoly]
  | succ m ih =>
    rw [vnPoly, eval_sub, eval_mul, eval_pow, ← ih]
    simp only [vn, Nat.add_sub_cancel, pow_succ, mul_comm _ 2, ← smul_smul, C.two_nsmul_x]
    simp

open Polynomial in
/-- The derivative of Remark 15: v_(m+1)' = 4^m v_1 v_2 ... v_m. -/
theorem derivative_vnPoly (m : ℕ) :
    derivative (vnPoly m : K[X]) = 4 ^ m * ∏ k ∈ range m, vnPoly k := by
  induction m with
  | zero => simp [vnPoly]
  | succ m ih =>
    rw [vnPoly, derivative_sub, derivative_mul, derivative_pow, ih, prod_range_succ]
    simp only [derivative_ofNat, derivative_one]
    rw [show (Polynomial.C ((2 : ℕ) : K) : K[X]) = 2 by rw [Nat.cast_ofNat, Polynomial.C_ofNat]]
    ring

open Polynomial in
/-- s_p_at_p is the value -2 v_n'(P_x) P_y of Remark 16, and panics at log_n = 0. -/
theorem s_p_at_p_ofC (P : C K) (m : ℕ) :
    Point.s_p_at_p (ofC P) (m + 1) = some (-2 * (derivative (vnPoly (K := K) m)).eval P.x * P.y) := by
  simp only [Point.s_p_at_p, ge_iff_le, show 1 ≤ m + 1 by omega, ↓reduceIte]
  rw [v_n_prod_ofC, derivative_vnPoly, Nat.add_sub_cancel]
  simp only [eval_mul, eval_pow, eval_prod, ofC_y, ← vn_eq_eval]
  congr 1
  rw [show 2 * (m + 1) - 1 = 2 * m + 1 by omega, pow_succ, pow_mul]
  norm_num
  ring_nf
  simp

theorem s_p_at_p_zero (p : Point K) : Point.s_p_at_p p 0 = none := rfl

end Plonky3Lean.Proofs.Circle
