module

public import Plonky3Lean.Proofs.Circle.Query
public import Plonky3Lean.Proofs.Circle.Poly

@[expose] public section

/-!
# p3-circle: the input checks accept honest openings

Take columns that are polynomials of degree below the trace size, opened at points off the LDE domain.

At every height, the verifier's reduction then reads one function of the query point: the DEEP function.

By the DEEP quotient lemma, that function has the degree of the columns.

Its lambda correction then lies in the FFT space, and its first-layer fold is what circle FRI folds.
-/

namespace Plonky3Lean.Proofs.Circle

open Plonky3Lean.Spec.Circle Plonky3Lean.Proofs.Dft Finset
open p3_dft.mirror p3_fri.mirror p3_circle.point.mirror p3_circle.deep_quotient.mirror

set_option linter.unusedSectionVars false

variable {K : Type} [Field K] [DecidableEq K] {G : Gen (K × K)}

/-! ## The DEEP term of honest values -/

/-- The real part of the quotient by v is half the numerator, off the opening point. -/
theorem cquot_fst (h2 : (2 : K) ≠ 0) (g : K) {P Q : C K} (hPQ : P ≠ Q) :
    (cquot g (Point.v_p (ofC P) (ofC Q))).1 = g / 2 := by
  have hre := mt (v_p_denom_eq_zero h2 P Q).mp hPQ
  have hv1 : (Point.v_p (ofC P) (ofC Q)).1 ≠ 0 := fun h => hre (by rw [h, add_zero])
  rw [cquot, v_p_norm]
  field_simp

/-- The imaginary part of the quotient by v is g (P - Q)_y / (2 (1 - (P - Q)_x)), off the opening point. -/
theorem cquot_snd (h2 : (2 : K) ≠ 0) (g : K) {P Q : C K} (hPQ : P ≠ Q) :
    (cquot g (Point.v_p (ofC P) (ofC Q))).2 * (2 * (1 - (P - Q).x)) = g * (P - Q).y := by
  have hre := mt (v_p_denom_eq_zero h2 P Q).mp hPQ
  have hv1 : (Point.v_p (ofC P) (ofC Q)).1 ≠ 0 := fun h => hre (by rw [h, add_zero])
  rw [cquot, v_p_norm]
  rw [v_p_eq] at hv1 ⊢
  have hx : (Q - P).x = (P - Q).x := by simp only [C.sub_x]; ring
  have hy : (Q - P).y = -(P - Q).y := by simp only [C.sub_y]; ring
  rw [hx, hy]
  have hv1' : 1 - (P - Q).x ≠ 0 := by simpa [hx] using hv1
  field_simp

/-- The DEEP term of honest values at one opening point has the degree of the columns, off that point. -/
theorem deepTerm_circlePoly (h2 : (2 : K) ≠ 0) (α : K) {D : ℕ} (Z : C K) (fs : List (C K → K))
    (hfs : ∀ f ∈ fs, IsCirclePoly D f) :
    ∃ F, IsCirclePoly D F ∧ ∀ P, P ≠ Z → deepTerm α P Z (fs.map (· P)) (fs.map (· Z)) = F P := by
  set f : ℕ → C K → K := fun j => (fs[j]?).getD fun _ => 0
  have hf : ∀ j, IsCirclePoly D (f j) := fun j => by
    rcases h : fs[j]? with _ | g
    · simpa [f, h] using IsCirclePoly.const D (0 : K)
    · simpa [f, h] using hfs g (List.mem_of_getElem? h)
  choose g hg hgeq using fun j => (hf j).deep Z
  refine ⟨fun P => ∑ j ∈ range fs.length, (α ^ j * ((f j P - f j Z) / 2) + α ^ (fs.length + j) * (g j P / 2)),
    IsCirclePoly.sum _ fun j _ => ?_, fun P hP => ?_⟩
  · refine IsCirclePoly.add (IsCirclePoly.smul _ ?_) (IsCirclePoly.smul _ ?_)
    · simpa [div_eq_mul_inv, mul_comm, ← sub_eq_add_neg] using IsCirclePoly.smul (2 : K)⁻¹
        (IsCirclePoly.add (hf j) (IsCirclePoly.const D (-f j Z)))
    · simpa [div_eq_mul_inv, mul_comm] using IsCirclePoly.smul (2 : K)⁻¹ (hg j)
  · have hne : 1 - (P - Z).x ≠ 0 := by
      have := mt (v_p_denom_eq_zero h2 P Z).mp hP
      rw [v_p_eq, show (Z - P).x = (P - Z).x by simp only [C.sub_x]; ring] at this
      intro h; exact this (by rw [h, add_zero])
    unfold deepTerm
    rw [List.length_map]
    refine sum_congr rfl fun j hj => ?_
    have hget : ∀ Q, (fs.map (· Q)).getD j 0 = f j Q := fun Q => by
      rw [List.getD_eq_getElem?_getD, List.getElem?_map]
      rcases h : fs[j]? with _ | g <;> simp [f, h]
    rw [hget, hget, cquot_fst h2 _ hP]
    congr 1
    have hs := cquot_snd h2 (f j P - f j Z) hP
    rw [← hgeq j P] at hs
    have hc : (cquot (f j P - f j Z) (Point.v_p (ofC P) (ofC Z))).2 * 2 = g j P :=
      mul_left_cancel₀ hne (by linear_combination hs)
    rw [← hc]
    field_simp

end Plonky3Lean.Proofs.Circle
