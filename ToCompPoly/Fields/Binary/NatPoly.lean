/-
Copyright (c) 2026 CompPoly. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Coratger
-/
import CompPoly.Fields.Binary.Common

/-!
# Natural numbers as polynomials over `GF(2)`

A natural number `n` is read as the polynomial whose coefficient of `X ^ i` is bit `i` of `n`.

- Exclusive or is addition.
- A left shift by `k` is a multiplication by `X ^ k`.
- Splitting off the low `k` bits splits off the terms of degree below `k`.

`toPoly v` of a bit vector is `natPoly v.toNat`.
-/

namespace BinaryField

open Polynomial

/-- The polynomial over `GF(2)` whose coefficient of `X ^ i` is bit `i` of `n`. -/
noncomputable def natPoly (n : ℕ) : (ZMod 2)[X] :=
  ∑ i ∈ Finset.range n, if n.testBit i then X ^ i else 0

/-- The coefficient of `X ^ i` is bit `i`. -/
theorem coeff_natPoly (n i : ℕ) :
    (natPoly n).coeff i = if n.testBit i then 1 else 0 := by
  unfold natPoly
  rw [finsetSum_coeff]
  simp_rw [apply_ite (fun p : (ZMod 2)[X] => p.coeff i), coeff_X_pow, coeff_zero]
  by_cases hi : i < n
  · rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hj
      simp [Ne.symm hj]
    · intro h
      exact absurd (Finset.mem_range.mpr hi) h
  · have hb : n.testBit i = false :=
      Nat.testBit_lt_two_pow (lt_of_lt_of_le n.lt_two_pow_self
        (Nat.pow_le_pow_right (by norm_num) (by omega)))
    rw [hb, Finset.sum_eq_zero]
    · simp
    · intro j hj
      have : i ≠ j := by
        have := Finset.mem_range.mp hj
        omega
      simp [this]

/-- Two numbers with the same polynomial are equal. -/
theorem natPoly_injective : Function.Injective natPoly := by
  intro a b h
  apply Nat.eq_of_testBit_eq
  intro i
  have := congrArg (fun p => p.coeff i) h
  simp only [coeff_natPoly] at this
  cases ha : a.testBit i <;> cases hb : b.testBit i <;> simp_all

@[simp]
theorem natPoly_zero : natPoly 0 = 0 := by
  simp [natPoly]

/-- Exclusive or is addition. -/
theorem natPoly_xor (a b : ℕ) : natPoly (a ^^^ b) = natPoly a + natPoly b := by
  ext i
  simp only [coeff_natPoly, coeff_add, Nat.testBit_xor]
  cases a.testBit i <;> cases b.testBit i <;> decide

/-- A left shift multiplies by a power of `X`. -/
theorem natPoly_shiftLeft (a k : ℕ) : natPoly (a <<< k) = X ^ k * natPoly a := by
  ext i
  simp only [coeff_natPoly, coeff_X_pow_mul', Nat.testBit_shiftLeft]
  by_cases h : k ≤ i <;> simp [h]

/-- Multiplying by a power of two multiplies by a power of `X`. -/
theorem natPoly_two_pow_mul (a k : ℕ) : natPoly (2 ^ k * a) = X ^ k * natPoly a := by
  rw [← natPoly_shiftLeft, Nat.shiftLeft_eq, Nat.mul_comm]

/-- A power of two is a power of `X`. -/
theorem natPoly_two_pow (k : ℕ) : natPoly (2 ^ k) = X ^ k := by
  ext i
  rw [coeff_natPoly, coeff_X_pow, Nat.testBit_two_pow]
  by_cases h : k = i <;> simp [h, eq_comm]

@[simp]
theorem natPoly_one : natPoly 1 = 1 := by
  simpa using natPoly_two_pow 0

theorem natPoly_two : natPoly 2 = X := by
  simpa using natPoly_two_pow 1

/-- The bits from `k` up are the quotient by `X ^ k`. -/
theorem natPoly_split (a k : ℕ) :
    natPoly a = X ^ k * natPoly (a >>> k) + natPoly (a % 2 ^ k) := by
  ext i
  simp only [coeff_natPoly, coeff_add, coeff_X_pow_mul', Nat.testBit_shiftRight,
    Nat.testBit_mod_two_pow]
  by_cases h : k ≤ i
  · simp [h, show ¬ i < k by omega, show k + (i - k) = i by omega]
  · simp [h, show i < k by omega]

/-- A number below `2 ^ k` has no coefficient from degree `k` up. -/
theorem coeff_natPoly_of_lt {a k i : ℕ} (ha : a < 2 ^ k) (hi : k ≤ i) :
    (natPoly a).coeff i = 0 := by
  rw [coeff_natPoly, Nat.testBit_lt_two_pow
    (lt_of_lt_of_le ha (Nat.pow_le_pow_right (by norm_num) hi))]
  rfl

/-- A number below `2 ^ k` is a polynomial of degree below `k`. -/
theorem degree_natPoly_lt {a k : ℕ} (ha : a < 2 ^ k) : (natPoly a).degree < k := by
  rw [degree_lt_iff_coeff_zero]
  intro i hi
  exact coeff_natPoly_of_lt ha hi

/-- A number whose polynomial has degree below `k` is below `2 ^ k`. -/
theorem lt_two_pow_of_degree_natPoly_lt {a k : ℕ} (h : (natPoly a).degree < k) :
    a < 2 ^ k := by
  apply Nat.lt_pow_two_of_testBit
  intro i hi
  have := coeff_eq_zero_of_degree_lt (lt_of_lt_of_le h (by exact_mod_cast hi))
  rw [coeff_natPoly] at this
  cases hb : a.testBit i
  · rfl
  · simp [hb] at this

/-- Placing `b` above `a` adds `X ^ k · b` when `a` fits in `k` bits. -/
theorem natPoly_or_shiftLeft {a b k : ℕ} (ha : a < 2 ^ k) :
    natPoly (a ||| b <<< k) = natPoly a + X ^ k * natPoly b := by
  ext i
  simp only [coeff_natPoly, coeff_add, coeff_X_pow_mul', Nat.testBit_or, Nat.testBit_shiftLeft]
  by_cases h : k ≤ i
  · have : a.testBit i = false :=
      Nat.testBit_lt_two_pow (lt_of_lt_of_le ha (Nat.pow_le_pow_right (by norm_num) h))
    simp [this, h]
  · simp [h]

/-- A bit vector's polynomial is that of its value. -/
theorem toPoly_eq_natPoly {w : ℕ} (v : BitVec w) : toPoly v = natPoly v.toNat := by
  ext i
  rw [toPoly_coeff, coeff_natPoly]
  by_cases h : i < w
  · simp [h, BitVec.getLsb, BitVec.testBit_toNat]
  · rw [dif_neg h, Nat.testBit_lt_two_pow
      (lt_of_lt_of_le v.isLt (Nat.pow_le_pow_right (by norm_num) (by omega)))]
    rfl

end BinaryField
