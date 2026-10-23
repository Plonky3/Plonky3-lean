module

public import Plonky3Lean.Proofs.MultilinearUtil.Poly

@[expose] public section

/-!
# Folds: fixing the first or the last variable

Fixing the first variable at c interpolates the two halves of the table:

```text
    f~(c, r) = (1 - c) f_0~(r) + c f_1~(r),     f = f_0 ++ f_1
```

Fixing the last variable interpolates each adjacent pair the same way.
-/

namespace Plonky3Lean.Proofs.MultilinearUtil

open Plonky3Lean.Spec.MultilinearUtil p3_multilinear_util.mirror p3_multilinear_util.poly.mirror
open Finset

variable {K : Type _} [CommRing K]

/-- The extension is linear in the table, entry by entry. -/
theorem mle_zipWith (α β : K) {f g : List K} {r : List K} (hf : f.length = 2 ^ r.length)
    (hg : g.length = 2 ^ r.length) :
    mle (List.zipWith (fun a b => α * a + β * b) f g) r = α * mle f r + β * mle g r := by
  simp only [mle, mul_sum, ← sum_add_distrib]
  refine sum_congr rfl fun b hb => ?_
  simp only [mem_range] at hb
  simp only [List.getD_eq_getElem?_getD, List.getElem?_zipWith,
    List.getElem?_eq_getElem (show b < f.length by omega),
    List.getElem?_eq_getElem (show b < g.length by omega), Option.getD_some]
  ring

/-- Fixing the first variable of a table of 2^(n+1) entries at c. -/
theorem mle_fold_prefix (c : K) {f : List K} {r : List K} (hf : f.length = 2 ^ (r.length + 1)) :
    mle (List.zipWith (fun a0 a1 => a0 + (a1 - a0) * c) (f.take (f.length / 2))
      (f.drop (f.length / 2))) r = mle f (c :: r) := by
  have hh : f.length / 2 = 2 ^ r.length := by rw [hf, pow_succ]; omega
  rw [mle_cons, hh, ← mle_zipWith (1 - c) c (by simp [hf, pow_succ]) (by simp [hf, pow_succ]; omega)]
  congr 1
  exact congrArg (fun φ => List.zipWith φ _ _) (by funext a b; ring)

theorem sum_range_two_mul {M : Type _} [AddCommMonoid M] (N : ℕ) (h : ℕ → M) :
    ∑ x ∈ range (2 * N), h x = ∑ b ∈ range N, (h (2 * b) + h (2 * b + 1)) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [show 2 * (N + 1) = 2 * N + 1 + 1 by ring, sum_range_succ, sum_range_succ, ih,
      sum_range_succ]
    abel

/-- Fixing the last variable at c interpolates each adjacent pair. -/
theorem mle_snoc (c : K) (f r : List K) :
    mle f (r ++ [c]) = mle ((List.range (2 ^ r.length)).map fun b =>
      (1 - c) * f.getD (2 * b) 0 + c * f.getD (2 * b + 1) 0) r := by
  simp only [mle, List.length_append, List.length_singleton, pow_succ, Nat.mul_comm _ 2,
    sum_range_two_mul]
  refine sum_congr rfl fun b hb => ?_
  have h0 := getElem_eqTable_snoc c r b false
  have h1 := getElem_eqTable_snoc c r b true
  simp only [Nat.bit_false, Nat.bit_true, Bool.false_eq_true, ↓reduceIte] at h0 h1
  rw [h0, h1, getD_map_range _ _ (mem_range.mp hb)]
  ring

/-! ## The folds of the transcription -/

section Folds

variable {F A : Type _} [Field F] [CommRing A] [Algebra F A]

/-- fix_prefix_var_mut: the table of the restriction to x_0 = r, half as long. -/
theorem fix_prefix_var_mut_spec (evals : List A) (r : F) {n : ℕ} (h : evals.length = 2 ^ (n + 1)) :
    ∃ res, Poly.fix_prefix_var_mut evals r = some res ∧ res.length = 2 ^ n ∧
      ∀ r' : List A, r'.length = n → mle res r' = mle evals (algebraMap F A r :: r') := by
  have h1 : evals.length ≠ 1 := by rw [h, pow_succ]; have := Nat.one_le_two_pow (n := n); omega
  refine ⟨List.zipWith (fun a0 a1 => a0 + (a1 - a0) * algebraMap F A r)
    (evals.take (evals.length / 2)) (evals.drop (evals.length / 2)),
    by simp [Poly.fix_prefix_var_mut, h1], by simp [h, pow_succ]; omega, fun r' hr => ?_⟩
  rw [mle_fold_prefix _ (by rw [h, hr])]

theorem fix_prefix_var_mut_panics (evals : List A) (r : F) (h : evals.length = 1) :
    Poly.fix_prefix_var_mut evals r = none := by simp [Poly.fix_prefix_var_mut, h]

/-- sum_prefix_var_mut: the table of p(0, x) + p(1, x), half as long; a constant is left alone. -/
theorem sum_prefix_var_mut_spec (evals : List A) {n : ℕ} (h : evals.length = 2 ^ (n + 1)) :
    (Poly.sum_prefix_var_mut evals).length = 2 ^ n ∧ ∀ r' : List A, r'.length = n →
      mle (Poly.sum_prefix_var_mut evals) r' = mle evals (0 :: r') + mle evals (1 :: r') := by
  have h1 : evals.length ≠ 1 := by rw [h, pow_succ]; have := Nat.one_le_two_pow (n := n); omega
  have hh : evals.length / 2 = 2 ^ n := by rw [h, pow_succ]; omega
  refine ⟨by simp [Poly.sum_prefix_var_mut, h1, hh]; omega, fun r' hr => ?_⟩
  simp only [Poly.sum_prefix_var_mut, h1, ↓reduceIte, mle_cons, hr, hh]
  rw [show (List.zipWith (· + ·) (evals.take (2 ^ n)) (evals.drop (2 ^ n))) =
    List.zipWith (fun a b => 1 * a + 1 * b) (evals.take (2 ^ n)) (evals.drop (2 ^ n)) by simp,
    mle_zipWith 1 1 (by simp [h, hr, pow_succ]) (by simp [h, hr, pow_succ]; omega)]
  ring

/-- fix_prefix_var_mut_monomial: in the monomial basis, the coefficients of p(r, x). -/
theorem fix_prefix_var_mut_monomial_eq (evals : List A) (r : F) (h : evals.length ≠ 1) :
    Poly.fix_prefix_var_mut_monomial evals r = some (List.zipWith
      (fun a0 a1 => a0 + a1 * algebraMap F A r) (evals.take (evals.length / 2))
      (evals.drop (evals.length / 2))) := by
  simp [Poly.fix_prefix_var_mut_monomial, h]

/-- The adjacent pairs of a table, interpolated at c. -/
def pairFold {K : Type _} [CommRing K] (c : K) (f : List K) (N : ℕ) : List K :=
  (List.range N).map fun b => (1 - c) * f.getD (2 * b) 0 + c * f.getD (2 * b + 1) 0

theorem fix_suffix_var_mut_split_eq (evals : List A) (r : F) {N : ℕ}
    (h : evals.length = 2 * N) :
    Poly.fix_suffix_var_mut_split evals r = pairFold (algebraMap F A r) evals N := by
  rw [Poly.fix_suffix_var_mut_split, chunks_eq two_pos (by rw [h, Nat.mul_comm]), List.map_map,
    pairFold]
  refine List.map_congr_left fun b hb => ?_
  simp only [List.mem_range] at hb
  simp only [Function.comp, chunkAt, List.getD_eq_getElem?_getD, List.getElem?_take,
    List.getElem?_drop]
  simp only [show (0 : ℕ) < 2 by norm_num, show (1 : ℕ) < 2 by norm_num, ↓reduceIte,
    Nat.mul_comm b 2, Nat.add_zero, Nat.add_comm (2 * b) 1]
  rw [show 1 + 2 * b = 2 * b + 1 by omega]
  ring

/-- The in-place suffix fold: step i reads entries 2 i and 2 i + 1, which no earlier step wrote. -/
theorem fix_suffix_whole_loop (evals : List A) (r : F) {N : ℕ} (h : evals.length = 2 * N)
    {j : ℕ} (hj : j ≤ N) :
    let v := (List.range j).foldl (fun v i =>
      v.set i ((v.getD (2 * i + 1) 0 - v.getD (2 * i) 0) * algebraMap F A r + v.getD (2 * i) 0))
      evals
    v.length = evals.length ∧ ∀ k < evals.length, v.getD k 0 =
      if k < j then (pairFold (algebraMap F A r) evals N).getD k 0 else evals.getD k 0 := by
  induction j with
  | zero => simp
  | succ j ih =>
    obtain ⟨hl, hx⟩ := ih (by omega)
    simp only [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    generalize List.foldl _ evals (List.range j) = v at hl hx ⊢
    have r0 := hx (2 * j) (by omega)
    have r1 := hx (2 * j + 1) (by omega)
    rw [ite_of_neg (by omega)] at r0 r1
    refine ⟨by simp [hl], fun k hk => ?_⟩
    rw [r0, r1]
    by_cases hkj : k = j
    · subst hkj
      simp only [List.getD_eq_getElem?_getD, List.getElem?_set_self (show k < v.length by omega),
        Option.getD_some, show k < k + 1 by omega, ↓reduceIte, pairFold,
        List.getElem?_map, List.getElem?_range (show k < N by omega), Option.map_some]
      ring
    · have := hx k hk
      simp only [List.getD_eq_getElem?_getD, List.getElem?_set_ne (Ne.symm hkj)] at this ⊢
      rw [this]
      by_cases hk' : k < j
      · simp [hk', show k < j + 1 by omega]
      · simp [hk', show ¬ k < j + 1 by omega]

/-- fix_suffix_var_mut: whichever path the cost model takes, the table of the restriction to x_{n-1} = r. -/
theorem fix_suffix_var_mut_eq (split : Bool) (evals : List A) (r : F) {N : ℕ}
    (h : evals.length = 2 * N) (hN : 0 < N) :
    Poly.fix_suffix_var_mut split evals r = some (pairFold (algebraMap F A r) evals N) := by
  have h1 : evals.length ≠ 1 := by omega
  obtain ⟨hl, hx⟩ := fix_suffix_whole_loop evals r h (le_refl N)
  cases split <;> simp only [Poly.fix_suffix_var_mut, h1, ↓reduceIte, Option.some.injEq,
    show evals.length / 2 = N by omega, Bool.false_eq_true]
  · refine ext_getD 0 (by
      rw [Poly.fix_suffix_var_mut_whole, List.length_take, hl]; simp [pairFold]; omega)
      fun k hk => ?_
    simp only [Poly.fix_suffix_var_mut_whole, List.length_take, hl] at hk ⊢
    rw [List.getD_eq_getElem?_getD, List.getElem?_take, ite_of_pos (by omega),
      ← List.getD_eq_getElem?_getD, hx k (by omega), ite_of_pos (by omega)]
  · exact fix_suffix_var_mut_split_eq evals r h

theorem mle_pairFold (c : K) (f r : List K) :
    mle (pairFold c f (2 ^ r.length)) r = mle f (r ++ [c]) := (mle_snoc c f r).symm

end Folds

section Extension

variable {A B : Type _} [Field A] [Field B] [Algebra A B]

theorem Poly_new_pow {α : Type _} (l : List α) {n : ℕ} (h : l.length = 2 ^ n) :
    Poly.new l = some l := by
  simp [Poly.new, h, Nat.log_pow]

theorem Poly_new_panics {α : Type _} (l : List α) (h : ∀ n, l.length ≠ 2 ^ n) : Poly.new l = none := by
  simp only [Poly.new, ite_eq_right_iff, reduceCtorEq, imp_false, not_and]
  exact fun _ h' => h _ h'.symm

/-- fix_prefix_var: the table of the restriction to x_0 = r, in the larger field. -/
theorem fix_prefix_var_spec (evals : List A) (r : B) {n : ℕ} (h : evals.length = 2 ^ (n + 1)) :
    ∃ res, Poly.fix_prefix_var evals r = some res ∧ res.length = 2 ^ n ∧
      ∀ r' : List B, r'.length = n → mle res r' = mle (evals.map (algebraMap A B)) (r :: r') := by
  have h1 : ¬ evals.length ≤ 1 := by rw [h, pow_succ]; have := Nat.one_le_two_pow (n := n); omega
  have hh : evals.length / 2 = 2 ^ n := by rw [h, pow_succ]; omega
  set res := List.zipWith (fun a0 a1 => r * algebraMap A B (a1 - a0) + algebraMap A B a0)
    (evals.take (evals.length / 2)) (evals.drop (evals.length / 2)) with hres
  have hl : res.length = 2 ^ n := by simp [hres, h, pow_succ]; omega
  refine ⟨res, by simp only [Poly.fix_prefix_var, h1, ↓reduceIte]; exact Poly_new_pow _ hl, hl,
    fun r' hr => ?_⟩
  rw [← mle_fold_prefix _ (by simp [h, hr])]
  congr 1
  simp only [hres, List.length_map, ← List.map_take, ← List.map_drop, List.zipWith_map]
  exact congrArg (fun φ => List.zipWith φ _ _) (by funext a b; simp [map_sub]; ring)

theorem fix_prefix_var_panics (evals : List A) (r : B) (h : evals.length ≤ 1) :
    Poly.fix_prefix_var evals r = none := by simp [Poly.fix_prefix_var, h]

/-- fix_prefix_var_at: one entry of the prefix fold, and a panic past the residual cube. -/
theorem fix_prefix_var_at_eq (evals : List A) (r : B) {index : ℕ}
    (hi : index + evals.length / 2 < evals.length) :
    Poly.fix_prefix_var_at evals r index = some ((1 - r) * algebraMap A B (evals.getD index 0) +
      r * algebraMap A B (evals.getD (index + evals.length / 2) 0)) := by
  simp only [Poly.fix_prefix_var_at, List.getElem?_eq_getElem (show index < evals.length by omega),
    List.getElem?_eq_getElem hi, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
    Option.some.injEq, List.getD_eq_getElem?_getD, Option.getD_some, map_sub]
  ring

theorem fix_prefix_var_at_panics (evals : List A) (r : B) {index : ℕ}
    (hi : evals.length ≤ index + evals.length / 2) : Poly.fix_prefix_var_at evals r index = none := by
  simp [Poly.fix_prefix_var_at, List.getElem?_eq_none hi]

/-- fix_suffix_var: the table of the restriction to x_{n-1} = r, in the larger field. -/
theorem fix_suffix_var_eq (evals : List A) (r : B) {N : ℕ} (h : evals.length = 2 * N) (hN : 0 < N)
    (hpow : ∃ n, N = 2 ^ n) :
    Poly.fix_suffix_var evals r = some (pairFold r (evals.map (algebraMap A B)) N) := by
  obtain ⟨n, rfl⟩ := hpow
  simp only [Poly.fix_suffix_var, show evals.length ≠ 1 by omega, ↓reduceIte]
  rw [chunks_eq two_pos (by rw [h, Nat.mul_comm]), List.map_map]
  rw [Poly_new_pow _ (n := n) (by simp)]
  congr 1
  refine List.map_congr_left fun b hb => ?_
  simp only [List.mem_range] at hb
  simp only [Function.comp, chunkAt, List.getD_eq_getElem?_getD, List.getElem?_take,
    List.getElem?_drop, List.getElem?_map]
  simp only [show (0 : ℕ) < 2 by norm_num, show (1 : ℕ) < 2 by norm_num, ↓reduceIte,
    Nat.mul_comm b 2, Nat.add_zero, Nat.add_comm (2 * b) 1]
  rw [show 1 + 2 * b = 2 * b + 1 by omega]
  rcases evals[2 * b]? <;> rcases evals[2 * b + 1]? <;> simp <;> ring

theorem fix_suffix_var_panics (evals : List A) (r : B) (h : evals.length = 1) :
    Poly.fix_suffix_var evals r = none := by simp [Poly.fix_suffix_var, h]

end Extension

end Plonky3Lean.Proofs.MultilinearUtil
