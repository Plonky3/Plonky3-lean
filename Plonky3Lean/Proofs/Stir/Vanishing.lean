module

public import Plonky3Lean.Proofs.Stir.Horner
public import Plonky3Lean.Proofs.Stir.Lists

@[expose] public section

/-!
# The vanishing polynomial of a list of roots
-/

namespace Plonky3Lean.Proofs.Stir

open Polynomial Finset Plonky3Lean.Spec.Stir p3_stir.utils.mirror

set_option linter.unusedSectionVars false

variable {K : Type _} [Field K] [DecidableEq K]

/-- One step of the loop multiplies the coefficient list by X - root. -/
theorem vanishing_step (coeffs : List K) (root : K) :
    let cs := coeffs ++ [0]
    let cs := (List.range (cs.length - 1)).reverse.foldl
      (fun cs i' => let i := i' + 1; cs.set i (cs.getD (i - 1) 0 - cs.getD i 0 * root)) cs
    let cs := cs.set 0 (-(cs.getD 0 0) * root)
    coeffPoly cs = (X - C root) * coeffPoly coeffs ∧ cs.length = coeffs.length + 1 := by
  intro cs0 cs1 cs2
  have hlen1 : cs1.length = coeffs.length + 1 := by
    simp only [cs1]; erw [length_foldl_set]; simp [cs0]
  have key := foldl_desc_set (fun _ a b => a - b * root) (0 : K) 1 one_pos coeffs.length cs0
    (by simp [cs0]; omega)
  have h0 : ∀ j, cs0.getD j 0 = coeffs.getD j 0 := fun j => by
    simp only [cs0, List.getD_eq_getElem?_getD, List.getElem?_append]
    split_ifs with h
    · rfl
    · simp [List.getElem?_singleton, List.getElem?_eq_none (by omega : coeffs.length ≤ j)]
      split_ifs <;> simp
  have k1 : ∀ j, cs1.getD j 0 = if 1 ≤ j ∧ j < 1 + coeffs.length then
      coeffs.getD (j - 1) 0 - coeffs.getD j 0 * root else coeffs.getD j 0 := fun j => by
    have k := key j
    simp only [h0] at k
    simpa [cs1, cs0] using k
  have c2 : ∀ j, cs2.getD (j + 1) 0 = cs1.getD (j + 1) 0 := fun j => by
    simp only [cs2, getD_set_eq]; simp
  have c20 : cs2.getD 0 0 = -(coeffs.getD 0 0) * root := by
    simp only [cs2, getD_set_eq, hlen1, k1]; simp
  refine ⟨Polynomial.ext fun j => ?_, by simp [cs2, hlen1]⟩
  rw [coeff_coeffPoly, sub_mul, coeff_sub, coeff_C_mul, coeff_coeffPoly]
  rcases j with _ | j
  · rw [c20]; simp; ring
  · rw [coeff_X_mul, coeff_coeffPoly, c2, k1]
    simp only [Nat.add_sub_cancel]
    split_ifs with h1
    · ring
    · simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega : coeffs.length ≤ j + 1),
        List.getElem?_eq_none (by omega : coeffs.length ≤ j)]

/-- The vanishing polynomial's coefficients of prod_{y in roots} (X - y), with one more entry than roots. -/
theorem vanishing_poly_from_roots_eq (roots : List K) :
    coeffPoly (vanishing_poly_from_roots roots) = (roots.map fun r => X - C r).prod ∧
      (vanishing_poly_from_roots roots).length = roots.length + 1 := by
  suffices ∀ (rs : List K) (acc : List K),
      coeffPoly (rs.foldl (fun coeffs root =>
        let coeffs := coeffs ++ [0]
        let coeffs := (List.range (coeffs.length - 1)).reverse.foldl
          (fun cs i' => let i := i' + 1; cs.set i (cs.getD (i - 1) 0 - cs.getD i 0 * root)) coeffs
        coeffs.set 0 (-(coeffs.getD 0 0) * root)) acc) = coeffPoly acc * (rs.map fun r => X - C r).prod ∧
      (rs.foldl (fun coeffs root =>
        let coeffs := coeffs ++ [0]
        let coeffs := (List.range (coeffs.length - 1)).reverse.foldl
          (fun cs i' => let i := i' + 1; cs.set i (cs.getD (i - 1) 0 - cs.getD i 0 * root)) coeffs
        coeffs.set 0 (-(coeffs.getD 0 0) * root)) acc).length = acc.length + rs.length by
    obtain ⟨h1, h2⟩ := this roots [1]
    refine ⟨?_, ?_⟩
    · rw [vanishing_poly_from_roots, h1]; simp [coeffPoly]
    · rw [vanishing_poly_from_roots, h2]; simp [add_comm]
  intro rs
  induction rs with
  | nil => intro acc; simp
  | cons r rs ih =>
    intro acc
    obtain ⟨hp, hl⟩ := vanishing_step acc r
    rw [List.foldl_cons]
    obtain ⟨h1, h2⟩ := ih _
    refine ⟨?_, ?_⟩
    · rw [h1, hp, List.map_cons, List.prod_cons]; ring
    · rw [h2, hl]; simp; ring

end Plonky3Lean.Proofs.Stir
