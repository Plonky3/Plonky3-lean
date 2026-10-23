module

public import P3Stir
public import Plonky3Lean.Spec.Stir

@[expose] public section

/-!
# Horner evaluation, division by a linear factor, and sums of coefficient lists
-/

namespace Plonky3Lean.Proofs.Stir

open Polynomial Finset Plonky3Lean.Spec.Stir p3_stir.mirror p3_stir.utils.mirror

set_option linter.unusedSectionVars false

variable {K : Type _} [Field K] [DecidableEq K]

theorem eval_coeffPoly (l : List K) (x : K) :
    (coeffPoly l).eval x = ∑ i ∈ range l.length, l.getD i 0 * x ^ i := by
  simp [coeffPoly, eval_finsetSum]

@[simp] theorem coeffPoly_nil : coeffPoly ([] : List K) = 0 := by simp [coeffPoly]

theorem coeffPoly_cons (a : K) (l : List K) : coeffPoly (a :: l) = C a + X * coeffPoly l := by
  simp only [coeffPoly, List.length_cons, sum_range_succ', List.getD_cons_succ, List.getD_cons_zero,
    pow_zero, mul_one, mul_sum, pow_succ]
  rw [add_comm]; congr 1; refine sum_congr rfl fun i _ => by ring

theorem coeffPoly_append (l m : List K) :
    coeffPoly (l ++ m) = coeffPoly l + X ^ l.length * coeffPoly m := by
  induction l with
  | nil => simp
  | cons a l ih => simp [coeffPoly_cons, ih, pow_succ]; ring

theorem coeff_coeffPoly (l : List K) (n : ℕ) : (coeffPoly l).coeff n = l.getD n 0 := by
  induction l generalizing n with
  | nil => simp
  | cons a l ih =>
    rcases n with _ | n <;> simp [coeffPoly_cons, coeff_C, ih, coeff_X_mul]

theorem degree_coeffPoly_lt (l : List K) : (coeffPoly l).degree < l.length := by
  rw [coeffPoly]
  refine (degree_sum_le _ _).trans_lt ((Finset.sup_lt_iff (WithBot.bot_lt_coe _)).2 fun i hi => ?_)
  exact (degree_C_mul_X_pow_le _ _).trans_lt (by exact_mod_cast mem_range.1 hi)

theorem natDegree_coeffPoly_lt {l : List K} (hl : l ≠ []) : (coeffPoly l).natDegree < l.length := by
  have := degree_coeffPoly_lt l
  by_cases h : coeffPoly l = 0
  · simp [h]; exact List.length_pos_of_ne_nil hl
  · exact (natDegree_lt_iff_degree_lt h).2 this

/-- eval_poly is the value of the coefficient list's polynomial. -/
theorem eval_poly_eq (poly : List K) (point : K) : eval_poly poly point = (coeffPoly poly).eval point := by
  induction poly with
  | nil => simp [eval_poly]
  | cons a l ih =>
    simp only [eval_poly, List.reverse_cons, List.foldl_append, List.foldl_cons, List.foldl_nil] at ih ⊢
    rw [ih, coeffPoly_cons]; simp; ring

/-- A coefficient list read with zeros past its end: any longer range gives the same sum. -/
theorem eval_coeffPoly_of_le (l : List K) (x : K) {N : ℕ} (hN : l.length ≤ N) :
    (coeffPoly l).eval x = ∑ i ∈ range N, l.getD i 0 * x ^ i := by
  rw [eval_coeffPoly, ← sum_range_add_sum_Ico _ hN, left_eq_add]
  exact sum_eq_zero fun i hi => by
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (mem_Ico.1 hi).1]

theorem sum_range_mul_split (f : ℕ → K) (m c : ℕ) :
    ∑ n ∈ range (m * c), f n = ∑ j ∈ range m, ∑ i ∈ range c, f (j * c + i) := by
  induction m with
  | zero => simp
  | succ m ih => rw [Nat.succ_mul, sum_range_add, ih, sum_range_succ]

theorem getD_map_range {α : Type _} (f : ℕ → α) (d : α) {m j : ℕ} (hj : j < m) :
    ((List.range m).map f).getD j d = f j := by
  simp [List.getD_eq_getElem?_getD, hj]

/-- A block of c coefficients starting at k evaluates to the matching slice of the sum. -/
theorem eval_take_drop (l : List K) (x : K) (k c : ℕ) :
    (coeffPoly ((l.drop k).take c)).eval x = ∑ i ∈ range c, l.getD (k + i) 0 * x ^ i := by
  rw [eval_coeffPoly_of_le _ _ (N := c) (by simp)]
  refine sum_congr rfl fun i hi => ?_
  simp [List.getD_eq_getElem?_getD, mem_range.1 hi]

/-- A polynomial is the sum of its blocks of c coefficients, block j scaled by x^(j c). -/
theorem eval_coeffPoly_blocks (l : List K) (x : K) {c m : ℕ} (hm : l.length ≤ m * c) :
    (coeffPoly l).eval x = ∑ j ∈ range m, x ^ (j * c) * (coeffPoly ((l.drop (j * c)).take c)).eval x := by
  rw [eval_coeffPoly_of_le l x hm, sum_range_mul_split]
  refine sum_congr rfl fun j _ => ?_
  rw [eval_take_drop, mul_sum]
  refine sum_congr rfl fun i _ => ?_
  rw [pow_add]; ring

theorem length_le_ceil_mul {c : ℕ} (hc : 0 < c) (n : ℕ) : n ≤ (n + c - 1) / c * c := by
  have := Nat.lt_div_mul_add (a := n + c - 1) hc; omega

/-- eval_poly_parallel is eval_poly, for every positive chunk size. -/
theorem eval_poly_parallel_eq {c : ℕ} (hc : 0 < c) (poly : List K) (point : K) :
    eval_poly_parallel c poly point = some ((coeffPoly poly).eval point) := by
  unfold eval_poly_parallel
  split_ifs with h
  · rw [eval_poly_eq]
  · simp only [chunks, hc.ne', ite_false, Option.bind_eq_bind, Option.bind_some, Option.some.injEq,
      List.map_map, Function.comp_def]
    rw [show ∀ vs : List K, vs.reverse.foldl (fun acc v => acc * point ^ c + v) 0 =
      eval_poly vs (point ^ c) from fun _ => rfl, eval_poly_eq, eval_coeffPoly]
    set m := (poly.length + c - 1) / c
    have hm : poly.length ≤ m * c := by
      have := Nat.lt_div_mul_add (a := poly.length + c - 1) hc; simp only [m]; omega
    rw [eval_coeffPoly_of_le poly point hm, sum_range_mul_split, List.length_map, List.length_range]
    refine sum_congr rfl fun j hj => ?_
    rw [getD_map_range _ _ (mem_range.1 hj), eval_poly_eq, eval_take_drop, sum_mul]
    refine sum_congr rfl fun i _ => ?_
    rw [← pow_mul, mul_assoc, ← pow_add, mul_comm c j, add_comm i]

end Plonky3Lean.Proofs.Stir
