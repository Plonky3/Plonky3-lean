module

public import Plonky3Lean.Proofs.Stir.Horner

@[expose] public section

/-!
# Base-field points: Horner at a base point, and reduction modulo X^n - c
-/

namespace Plonky3Lean.Proofs.Stir

open Polynomial Finset Plonky3Lean.Spec.Stir p3_stir.mirror p3_stir.utils.mirror

set_option linter.unusedSectionVars false

variable {F EF : Type _} [Field F] [Field EF] [Algebra F EF] [DecidableEq F] [DecidableEq EF]

/-- Horner's rule at a base point is the value at its image in EF. -/
theorem eval_poly_at_base_eq (poly : List EF) (point : F) :
    eval_poly_at_base poly point = (coeffPoly poly).eval (algebraMap F EF point) := by
  rw [← eval_poly_eq]; rfl

/-- The fold of reduce_mod_x_pow_minus_c: slot i holds sum_b block_b[i] c^b. -/
theorem reduce_fold_getD (n : ℕ) (c : F) (blocks : List (List EF)) :
    let st := blocks.foldl (fun (st : List EF × F) block =>
      ((List.range n).map fun i =>
        if i < block.length then st.1.getD i 0 + block.getD i 0 * algebraMap F EF st.2
        else st.1.getD i 0, st.2 * c)) (List.replicate n 0, 1)
    st.1.length = n ∧ st.2 = c ^ blocks.length ∧ ∀ i < n,
      st.1.getD i 0 = ∑ b ∈ range blocks.length, (blocks.getD b []).getD i 0 * algebraMap F EF (c ^ b) := by
  induction blocks using List.reverseRecOn with
  | nil => simp [List.getD_eq_getElem?_getD, List.getElem?_replicate]; intro i hi; simp [hi]
  | append_singleton bs blk ih =>
    obtain ⟨h1, h2, h3⟩ := ih
    simp only [List.foldl_append, List.foldl_cons, List.foldl_nil, List.length_map, List.length_range,
      List.length_append, List.length_singleton, true_and]
    refine ⟨by rw [h2, pow_succ], fun i hi => ?_⟩
    rw [getD_map_range _ _ hi, sum_range_succ]
    have hb : ∀ b ∈ range bs.length, ((bs ++ [blk]).getD b []).getD i 0 = (bs.getD b []).getD i 0 :=
      fun b hb => by
        simp [List.getD_eq_getElem?_getD, List.getElem?_append_left (mem_range.1 hb)]
    rw [sum_congr rfl fun b hb' => by rw [hb b hb'], ← h3 i hi, h2]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _), Nat.sub_self,
      List.getElem?_singleton, ite_true, Option.getD_some]
    split_ifs with h
    · rfl
    · simp [List.getElem?_eq_none (not_lt.1 h)]

/-- Reduction modulo X^n - c: n slots whose polynomial agrees with the input at every y with y^n = c, for n > 0. -/
theorem reduce_mod_x_pow_minus_c_eq {n : ℕ} (hn : 0 < n) (poly : List EF) (c : F) :
    ∃ r, reduce_mod_x_pow_minus_c poly n c = some r ∧ r.length = n ∧
      ∀ y : EF, y ^ n = algebraMap F EF c → (coeffPoly r).eval y = (coeffPoly poly).eval y := by
  set m := (poly.length + n - 1) / n
  obtain ⟨h1, -, h3⟩ := reduce_fold_getD n c ((List.range m).map fun j => (poly.drop (j * n)).take n)
  refine ⟨_, by simp [reduce_mod_x_pow_minus_c, chunks, hn.ne']; rfl, h1, fun y hy => ?_⟩
  rw [eval_coeffPoly_of_le _ y (le_of_eq h1), eval_coeffPoly_blocks poly y (length_le_ceil_mul hn _)]
  simp only [List.length_map, List.length_range] at h3
  rw [sum_congr rfl fun i hi => by rw [h3 i (mem_range.1 hi), sum_mul]]
  rw [sum_comm]
  refine sum_congr rfl fun j hj => ?_
  rw [pow_mul', hy, ← map_pow, eval_coeffPoly_of_le _ y (N := n) (by simp), mul_sum,
    getD_map_range _ _ (mem_range.1 hj)]
  refine sum_congr rfl fun i _ => by ring

/-- Reduction modulo X^0 - c panics. -/
theorem reduce_mod_x_pow_minus_c_panics (poly : List EF) (c : F) :
    reduce_mod_x_pow_minus_c poly 0 c = none := by
  simp [reduce_mod_x_pow_minus_c, chunks]

end Plonky3Lean.Proofs.Stir
