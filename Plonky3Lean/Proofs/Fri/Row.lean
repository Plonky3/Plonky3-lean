module

public import Plonky3Lean.Proofs.Fri.Poly
public import P3Fri.Fold
public import Plonky3Lean.Proofs.Dft.Glue

@[expose] public section

/-!
# The row fold computes the fold of the opened word

The barycentric interpolation over a two-adic coset, and the closed form at arity 2, both return the value at beta of the polynomial through the row.
-/

namespace Plonky3Lean.Proofs.Fri

set_option linter.unusedSectionVars false

open Polynomial Finset Plonky3Lean.Spec.Fri p3_fri.two_adic_pcs.mirror p3_dft.mirror

variable {K : Type _} [Field K] [DecidableEq K]

omit [DecidableEq K] in
theorem foldl_add_map {α : Type _} (f : α → K) (l : List α) (a : K) :
    l.foldl (fun acc e => acc + f e) a = a + (l.map f).sum := by
  induction l generalizing a with
  | nil => simp
  | cons x l ih => simp [ih, add_assoc]

theorem zip_ofFn {α β : Type _} {n : ℕ} (a : Fin n → α) (b : Fin n → β) :
    (List.ofFn a).zip (List.ofFn b) = List.ofFn fun i => (a i, b i) := by
  apply List.ext_getElem <;> simp

variable {s ω : K} {k : ℕ}

/-- The nodes of a coset s H of order n = 2^k are the roots of X^n - s^n. -/
theorem nodal_revCoset (hω : IsPrimitiveRoot ω (2 ^ k)) (hs : s ≠ 0) :
    Lagrange.nodal univ (revCoset s ω k) = X ^ 2 ^ k - C (s ^ 2 ^ k) := by
  refine eq_of_degree_sub_lt_of_eval_index_eq univ (revCoset_injective hω hs).injOn ?_ ?_
  · have h1 : (Lagrange.nodal univ (revCoset s ω k)).degree = ((2 ^ k : ℕ) : WithBot ℕ) := by
      rw [Lagrange.degree_nodal, card_univ, Fintype.card_fin]
    rw [card_univ, Fintype.card_fin, ← h1]
    refine degree_sub_lt_left ?_ (Lagrange.nodal_monic.ne_zero) ?_
    · rw [h1, degree_X_pow_sub_C (by positivity)]
    · rw [Lagrange.nodal_monic.leadingCoeff, (monic_X_pow_sub_C (s ^ 2 ^ k) (pow_ne_zero k two_ne_zero)).leadingCoeff]
  · intro j _
    rw [Lagrange.eval_nodal_at_node (mem_univ j)]
    simp [revCoset_pow hω.pow_eq_one]

/-- The barycentric weight of node x: x / (n s^n). -/
theorem nodalWeight_revCoset (hω : IsPrimitiveRoot ω (2 ^ k)) (hs : s ≠ 0) (h2 : (2 : K) ≠ 0)
    (j : Fin (2 ^ k)) :
    Lagrange.nodalWeight univ (revCoset s ω k) j =
      revCoset s ω k j * ((2 ^ k : ℕ) * s ^ 2 ^ k : K)⁻¹ := by
  have hx : revCoset s ω k j ≠ 0 := mul_ne_zero hs (pow_ne_zero _ (hω.ne_zero (by positivity)))
  rw [Lagrange.nodalWeight_eq_eval_derivative_nodal (mem_univ j), nodal_revCoset hω hs]
  simp only [derivative_sub, derivative_X_pow, derivative_C, sub_zero, eval_mul, eval_C, eval_pow, eval_X]
  rw [← revCoset_pow (s := s) hω.pow_eq_one j]
  have h2k : ((2 ^ k : ℕ) : K) ≠ 0 := by exact_mod_cast pow_ne_zero k h2
  obtain ⟨m, hm⟩ : ∃ m, 2 ^ k = m + 1 := ⟨2 ^ k - 1, by have := Nat.one_le_two_pow (n := k); omega⟩
  rw [hm, Nat.cast_add_one, Nat.add_sub_cancel, pow_succ]
  rw [hm, Nat.cast_add_one] at h2k
  field_simp

/-- Barycentric interpolation over a coset in bit-reversed order returns the value at z of the polynomial through the values. -/
theorem lagrange_interpolate_at_revCoset (hω : IsPrimitiveRoot ω (2 ^ k)) (hs : s ≠ 0) (h2 : (2 : K) ≠ 0)
    (y : Fin (2 ^ k) → K) (z : K) :
    lagrange_interpolate_at (List.ofFn (revCoset s ω k)) (List.ofFn y) z = some (foldValue s ω k y z) := by
  have hinj := (revCoset_injective hω hs).injOn (s := ↑(univ : Finset (Fin (2 ^ k))))
  have hget : ∀ i (hi : i < 2 ^ k), (List.ofFn (revCoset s ω k)).getD i 0 = revCoset s ω k ⟨i, hi⟩ := by
    intro i hi; simp [List.getD_eq_getElem?_getD, hi]
  unfold lagrange_interpolate_at
  simp only [List.length_ofFn, ne_eq, not_true_eq_false, ↓reduceIte, pow_ne_zero k two_ne_zero]
  cases hf : (List.range (2 ^ k)).find? (fun i => z - (List.ofFn (revCoset s ω k)).getD i 0 = 0) with
  | some i =>
    have hi : i < 2 ^ k := List.mem_range.1 (List.mem_of_find?_eq_some hf)
    have hz : z = revCoset s ω k ⟨i, hi⟩ := by
      have := List.find?_some hf; rw [hget i hi] at this; simpa [sub_eq_zero] using this
    simp only [foldValue, hz, Lagrange.eval_interpolate_at_node _ hinj (mem_univ _)]
    simp [List.getD_eq_getElem?_getD, hi]
  | none =>
    have hne : ∀ i : Fin (2 ^ k), z ≠ revCoset s ω k i := by
      intro i h
      have := List.find?_eq_none.1 hf i.val (List.mem_range.2 i.2)
      rw [hget i i.2] at this; simp [h] at this
    have h2k : ((2 ^ k : ℕ) : K) * s ^ 2 ^ k ≠ 0 :=
      mul_ne_zero (by exact_mod_cast pow_ne_zero k h2) (pow_ne_zero _ hs)
    simp only [Plonky3Lean.Proofs.Dft.log2Strict_pow, Option.bind_eq_bind, Option.bind_some]
    have hall : ∀ x ∈ List.ofFn (fun i => z - revCoset s ω k i), x ≠ 0 := by
      simp only [List.mem_ofFn]
      rintro _ ⟨i, rfl⟩
      exact sub_ne_zero.2 (hne i)
    rw [hget 0 (by positivity), revCoset_pow hω.pow_eq_one]
    simp only [inv, p3_commit.domain.mirror.inv, h2k, ↓reduceIte, Option.bind_some, batchInv,
      p3_commit.domain.mirror.batchInv, List.map_ofFn, zip_ofFn, foldl_add_map,
      zero_add, List.prod_ofFn, Function.comp_def]
    rw [ite_eq_left_of_eq_true _ _ (eq_true hall)]
    simp only [Option.bind_some, zip_ofFn, List.map_ofFn, Function.comp_def, List.sum_ofFn]
    rw [foldValue, Lagrange.eval_interpolate_not_at_node _ fun i _ => hne i, Lagrange.eval_nodal,
      mul_comm]
    congr 2
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [nodalWeight_revCoset hω hs h2]
    ring

theorem bitRev_lt' (k i : ℕ) : bitRev k i < 2 ^ k := by
  rw [Plonky3Lean.Proofs.Dft.bitRev_eq]; exact Plonky3Lean.Proofs.Matrix.bitRev_lt k i

/-- The interpolation points of a row: the coset's shifted powers, bit-reversed. -/
theorem revIndex_shiftedPowers (w s : K) (k : ℕ) :
    revIndex (2 ^ k) (shiftedPowersList w s (2 ^ k)) = List.ofFn (revCoset s w k) := by
  apply List.ext_getElem
  · simp [revIndex]
  · intro i h1 h2
    simp only [revIndex, shiftedPowersList, Nat.log_pow (by norm_num : 1 < 2), List.getElem_map,
      List.getElem_range, List.getElem_ofFn, revCoset]
    rw [List.getD_eq_getElem _ _ (by simpa using bitRev_lt' k i)]
    simp

/-- Two points s and -s: the closed form is the value at beta of the line through them. -/
theorem foldValue_two {s ω : K} (hω : IsPrimitiveRoot ω (2 ^ 1)) (hs : s ≠ 0) (h2 : (2 : K) ≠ 0)
    (lo hi β : K) :
    foldValue s ω 1 ![lo, hi] β = (lo + hi) / 2 + (lo - hi) * β * (s + s)⁻¹ := by
  have hinj := revCoset_injective hω hs
  obtain rfl : ω = -1 := by rw [pow_one] at hω; exact hω.eq_neg_one_of_two_right
  have hq : C ((lo + hi) / 2) + C ((lo - hi) * (s + s)⁻¹) * X =
      Lagrange.interpolate univ (revCoset s (-1) 1) ![lo, hi] := by
    refine Lagrange.eq_interpolate_of_eval_eq _ hinj.injOn ?_ ?_
    · rw [card_univ, Fintype.card_fin]
      refine lt_of_le_of_lt (degree_add_le _ _) (max_lt ?_ ?_)
      · exact lt_of_le_of_lt degree_C_le (by norm_num)
      · exact lt_of_le_of_lt (degree_C_mul_X_le _) (by norm_num)
    · intro j _
      have hh : (s + s)⁻¹ * s = 2⁻¹ := by rw [← two_mul, mul_inv, mul_assoc, inv_mul_cancel₀ hs, mul_one]
      have h22 : (2 : K)⁻¹ * 2 = 1 := inv_mul_cancel₀ h2
      fin_cases j
      · simp only [revCoset, bitRev, eval_add, eval_mul, eval_C, eval_X]
        norm_num
        linear_combination (lo - hi) * hh + lo * h22
      · simp only [revCoset, bitRev, eval_add, eval_mul, eval_C, eval_X]
        norm_num
        linear_combination -(lo - hi) * hh + hi * h22
  rw [foldValue, ← hq]
  simp [mul_assoc, mul_comm]

/-- The row fold returns the value at beta of the polynomial through the row on its coset. -/
theorem fold_row_eq (G : Gen K) (hV : Plonky3Lean.Proofs.Dft.GenValid G) (h2 : (2 : K) ≠ 0)
    {index h k : ℕ} (hk : 1 ≤ k) (hhk : h + k ≤ G.adicity) (evals : Fin (2 ^ k) → K) (β : K) :
    fold_row G index h k β (List.ofFn evals) =
      some (foldValue (G.gen (h + k) ^ bitRev h index) (G.gen k) k evals β) := by
  have hs : G.gen (h + k) ^ bitRev h index ≠ 0 :=
    pow_ne_zero _ ((hV _ hhk).ne_zero (by positivity))
  have hw := hV k (by omega)
  unfold fold_row
  rw [Plonky3Lean.Proofs.Dft.gen_get_of_le G hhk]
  simp only [Option.bind_eq_bind, Option.bind_some]
  rcases Nat.lt_or_ge k 2 with hk1 | hk2
  · obtain rfl : k = 1 := by omega
    have hω : G.gen 1 = -1 := by
      have := hV 1 (by omega); rw [pow_one] at this; exact this.eq_neg_one_of_two_right
    have hev : List.ofFn evals = [evals 0, evals 1] := by simp [List.ofFn_succ]
    have hss : ¬ (G.gen (h + 1) ^ bitRev h index + G.gen (h + 1) ^ bitRev h index = 0) := by
      rw [← two_mul]; exact mul_ne_zero h2 hs
    have hev' : evals = ![evals 0, evals 1] := by funext i; fin_cases i <;> rfl
    simp only [↓reduceIte, hev, inv, p3_commit.domain.mirror.inv, hss, Option.bind_some]
    rw [hev', foldValue_two hw hs h2]
    rfl
  · simp only [show k ≠ 1 by omega, ↓reduceIte, List.length_ofFn, ne_eq, not_true_eq_false,
      Plonky3Lean.Proofs.Dft.gen_get_of_le G (show k ≤ G.adicity by omega), Option.bind_some,
      revIndex_shiftedPowers]
    exact lagrange_interpolate_at_revCoset hw hs h2 evals β

/-- The row fold panics exactly when the generator table is too short or the row does not hold 2^k values. -/
theorem fold_row_eq_none (G : Gen K) (hV : Plonky3Lean.Proofs.Dft.GenValid G) (h2 : (2 : K) ≠ 0)
    {index h k : ℕ} (hk : 1 ≤ k) (β : K) (evals : List K) :
    fold_row G index h k β evals = none ↔ G.adicity < h + k ∨ evals.length ≠ 2 ^ k := by
  constructor
  · intro hn
    by_contra hc
    push Not at hc
    have := fold_row_eq G hV h2 (index := index) hk hc.1 (fun i => evals.get (i.cast hc.2.symm)) β
    rw [show List.ofFn (fun i : Fin (2 ^ k) => evals.get (i.cast hc.2.symm)) = evals from
      List.ext_getElem (by simp [hc.2]) (by simp)] at this
    rw [hn] at this
    exact absurd this (by simp)
  · rintro (ha | hl)
    · simp [fold_row, Plonky3Lean.Proofs.Dft.gen_get_of_lt G ha]
    · unfold fold_row
      cases hg : G.get (h + k) with
      | none => rfl
      | some g =>
        simp only [Option.bind_eq_bind, Option.bind_some]
        rcases Nat.lt_or_ge k 2 with hk1 | hk2
        · obtain rfl : k = 1 := by omega
          match evals, hl with
          | [], _ => rfl
          | [_], _ => rfl
          | [_, _], hl => exact absurd rfl hl
          | _ :: _ :: _ :: _, _ => rfl
        · simp [show k ≠ 1 by omega, hl]

end Plonky3Lean.Proofs.Fri
