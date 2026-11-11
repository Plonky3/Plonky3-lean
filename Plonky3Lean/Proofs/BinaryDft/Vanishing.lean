module

public import Plonky3Lean.Proofs.BinaryDft.Basic
public import Mathlib.Algebra.CharP.Two
public import Mathlib.Tactic.LinearCombination

@[expose] public section

/-!
# Subspace polynomials and the novel basis

W_i vanishes on the 2^i points of S_i, and W_(i+1)(x) = W_i(x) W_i(x - beta_i).

In characteristic 2 this makes W_i additive (Lin, Chung and Han, Lemma 1).

For a Cantor basis, W_j(beta_i) = beta_(i-j), so W_j(beta_j) = 1 and W_j is the j-th iterate of x^2 + x.
-/

namespace Plonky3Lean.Proofs.BinaryDft

open Finset Plonky3Lean.Spec.BinaryDft

variable {F : Type _} [Field F] (β : ℕ → F)

@[simp] theorem vanishing_zero (x : F) : vanishing β 0 x = x := by simp [vanishing]

theorem vanishing_succ (i : ℕ) (x : F) :
    vanishing β (i + 1) x = vanishing β i x * vanishing β i (x - β i) := by
  simp only [vanishing, pow_succ, mul_two, prod_range_add]
  congr 1
  refine prod_congr rfl fun m hm => ?_
  rw [add_comm, point_add_two_pow β (mem_range.mp hm)]
  ring

theorem vanishing_point {i m : ℕ} (hm : m < 2 ^ i) : vanishing β i (point β m) = 0 :=
  prod_eq_zero (mem_range.mpr hm) (sub_self _)

/-- The scaling factor of the normalisation is nonzero for an independent basis. -/
theorem vanishing_basis_ne_zero {n i : ℕ} (hβ : Independent β n) (hi : i < n) :
    vanishing β i (β i) ≠ 0 :=
  prod_ne_zero_iff.mpr fun m hm => sub_ne_zero.mpr (hβ i hi m (mem_range.mp hm)).symm

section CharTwo

variable [CharP F 2]

/-- Lin, Chung and Han, Lemma 1: W_i is additive in characteristic 2. -/
theorem vanishing_add (i : ℕ) (x y : F) :
    vanishing β i (x + y) = vanishing β i x + vanishing β i y := by
  induction i generalizing x y with
  | zero => simp
  | succ i ih =>
    have hsub : ∀ z, vanishing β i (z - β i) = vanishing β i z + vanishing β i (β i) := by
      intro z; rw [CharTwo.sub_eq_add, ih]
    simp only [vanishing_succ, hsub, ih]
    linear_combination (vanishing β i x * vanishing β i y) * CharTwo.two_eq_zero (R := F)

/-- W_i as an additive map. -/
def vanishingHom (i : ℕ) : F →+ F where
  toFun := vanishing β i
  map_zero' := by
    have := vanishing_add β i 0 0
    rw [add_zero] at this
    linear_combination -this
  map_add' := vanishing_add β i

theorem vanishing_succ' (i : ℕ) (x : F) :
    vanishing β (i + 1) x = vanishing β i x * (vanishing β i x + vanishing β i (β i)) := by
  rw [vanishing_succ, CharTwo.sub_eq_add, vanishing_add]

theorem normalized_add (i : ℕ) (x y : F) :
    normalized β i (x + y) = normalized β i x + normalized β i y := by
  simp [normalized, vanishing_add, add_div]

omit [CharP F 2] in
theorem normalized_basis {n i : ℕ} (hβ : Independent β n) (hi : i < n) :
    normalized β i (β i) = 1 :=
  div_self (vanishing_basis_ne_zero β hβ hi)

omit [CharP F 2] in
theorem normalized_point {i m : ℕ} (hm : m < 2 ^ i) : normalized β i (point β m) = 0 := by
  simp [normalized, vanishing_point β hm]

/-- W^_l is constant on a coset of S_l. -/
theorem normalized_shift_low (l : ℕ) (shift : F) {i : ℕ} (hi : i < 2 ^ l) :
    normalized β l (shift + point β i) = normalized β l shift := by
  rw [normalized_add, normalized_point β hi, add_zero]

/-- W^_l rises by one on the next coset of S_l. -/
theorem normalized_shift_high {n l : ℕ} (hβ : Independent β n) (hl : l < n) (shift : F)
    {i : ℕ} (hi : i < 2 ^ l) :
    normalized β l (shift + point β (i + 2 ^ l)) = normalized β l shift + 1 := by
  rw [point_add_two_pow β hi, normalized_add, normalized_add, normalized_point β hi,
    normalized_basis β hβ hl, zero_add]

end CharTwo

/-! ## The novel basis -/

theorem novel_succ_low (l : ℕ) {k : ℕ} (hk : k < 2 ^ l) (x : F) :
    novel β (l + 1) k x = novel β l k x := by
  rw [novel, prod_range_succ]; simp [testBit_of_lt hk le_rfl]; rfl

theorem novel_succ_high (l : ℕ) {k : ℕ} (hk : k < 2 ^ l) (x : F) :
    novel β (l + 1) (k + 2 ^ l) x = novel β l k x * normalized β l x := by
  rw [novel, prod_range_succ, novel]
  congr 1
  · refine prod_congr rfl fun j hj => ?_
    rw [add_comm, ← mul_one (2 ^ l), Nat.testBit_two_pow_mul_add 1 hk]
    simp [mem_range.mp hj]
  · rw [add_comm, ← mul_one (2 ^ l), Nat.testBit_two_pow_mul_add 1 hk]; simp

/-! ## Cantor bases -/

section Cantor

variable [CharP F 2] {β}

omit [CharP F 2] in
theorem sqAddIter_succ (j : ℕ) (x : F) :
    sqAddIter (j + 1) x = sqAddIter j x ^ 2 + sqAddIter j x :=
  Function.iterate_succ_apply' _ j x

omit [CharP F 2] in
/-- The iterate sends beta_i to beta_(i-j). -/
theorem sqAddIter_basis {n : ℕ} (hβ : IsCantor β n) {i j : ℕ} (hi : i < n) (hj : j ≤ i) :
    sqAddIter j (β i) = β (i - j) := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [sqAddIter_succ, ih (by omega)]
    have := hβ.2 (i - (j + 1)) (by omega)
    rwa [show i - (j + 1) + 1 = i - j by omega] at this

/-- For a Cantor basis, W_j is the j-th iterate of x^2 + x. -/
theorem vanishing_eq_sqAddIter {n : ℕ} (hβ : IsCantor β n) {j : ℕ} (hj : j ≤ n) (x : F) :
    vanishing β j x = sqAddIter j x := by
  induction j generalizing x with
  | zero => simp [sqAddIter]
  | succ j ih =>
    rw [vanishing_succ', ih (by omega), ih (by omega), sqAddIter_succ,
      sqAddIter_basis hβ (by omega) le_rfl, Nat.sub_self, hβ.1]
    ring

theorem vanishing_basis_cantor {n : ℕ} (hβ : IsCantor β n) {j : ℕ} (hj : j < n) :
    vanishing β j (β j) = 1 := by
  rw [vanishing_eq_sqAddIter hβ hj.le, sqAddIter_basis hβ hj le_rfl, Nat.sub_self, hβ.1]

/-- A Cantor basis is independent. -/
theorem IsCantor.independent {n : ℕ} (hβ : IsCantor β n) : Independent β n := by
  intro i hi m hm h
  have := vanishing_point β hm
  rw [h, vanishing_basis_cantor hβ hi] at this
  exact one_ne_zero this

/-- For a Cantor basis, W^_j = W_j: the normalisation divides by one. -/
theorem normalized_eq_sqAddIter {n : ℕ} (hβ : IsCantor β n) {j : ℕ} (hj : j < n) (x : F) :
    normalized β j x = sqAddIter j x := by
  rw [normalized, vanishing_basis_cantor hβ hj, div_one, vanishing_eq_sqAddIter hβ hj.le]

/-- The code's twiddle: W_j(shift) plus the domain point 2b, for blocks inside the basis. -/
theorem twiddle_cantor {n : ℕ} (hβ : IsCantor β n) (shift : F) {j b : ℕ} (hj : j < n)
    (hb : b * 2 ^ (j + 1) < 2 ^ n) :
    twiddle β shift j b = sqAddIter j shift + point β (2 * b) := by
  have hb' : b < 2 ^ (n - (j + 1)) := by
    by_contra h
    have := Nat.mul_le_mul_right (2 ^ (j + 1)) (not_lt.mp h)
    rw [← pow_add, Nat.sub_add_cancel (by omega)] at this
    omega
  rw [twiddle, normalized_eq_sqAddIter hβ hj, ← vanishing_eq_sqAddIter hβ hj.le,
    ← vanishing_eq_sqAddIter hβ hj.le, vanishing_add, mul_comm, point_mul_two_pow]
  congr 1
  change vanishingHom β j _ = _
  rw [map_point, ← pow_one 2, point_mul_two_pow]
  refine point_congr hb' fun r hr => ?_
  simp only [Function.comp, vanishingHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  rw [vanishing_eq_sqAddIter hβ hj.le, sqAddIter_basis hβ (by omega) (by omega)]
  congr 1; omega

end Cantor

end Plonky3Lean.Proofs.BinaryDft
