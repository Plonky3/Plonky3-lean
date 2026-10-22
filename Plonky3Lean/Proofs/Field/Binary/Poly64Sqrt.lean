import Plonky3Lean.Proofs.Field.Binary.Poly64Irreducible

/-!
# The square root in `GF(2^64)`

`poly_sqrt_64` splits `a` into its even and odd coefficients, `a = e^2 + X · o^2`.

Squaring is additive in characteristic `2`, so `e + sqrt(X) · o` squares back to `a`.

`ROOT_X` is `sqrt(X)` modulo `x^64 + x^4 + x^3 + x + 1`.
-/

open Aeneas Aeneas.Std CoreModels Polynomial
open p3_binary_field BinaryField
open Plonky3Lean.Lib Plonky3Lean.Spec.BinaryField

namespace Plonky3Lean.Proofs.Binary

/-- A 64-bit polynomial is its even part squared plus `X` times its odd part squared. -/
theorem natPoly_even_odd_64 {a : ℕ} (ha : a < 2 ^ 64) :
    natPoly a = natPoly (compactNat a) ^ 2 + X ^ 1 * natPoly (compactNat (a >>> 1)) ^ 2 := by
  have ho : a >>> 1 < 2 ^ 64 := lt_of_le_of_lt (Nat.shiftRight_le _ _) ha
  have hb : ∀ i, 64 ≤ i → a.testBit i = false := fun i hi =>
    Nat.testBit_lt_two_pow (lt_of_lt_of_le ha (Nat.pow_le_pow_right (by norm_num) hi))
  have he : ∀ j, (compactNat a).testBit j = a.testBit (2 * j) := by
    intro j
    rw [testBit_compactNat ha]
    by_cases hj : j < 32
    · simp [hj]
    · simp [hj, hb (2 * j) (by omega)]
  have hd : ∀ j, (compactNat (a >>> 1)).testBit j = a.testBit (2 * j + 1) := by
    intro j
    rw [testBit_compactNat ho, Nat.testBit_shiftRight, Nat.add_comm 1]
    by_cases hj : j < 32
    · simp [hj]
    · simp [hj, hb (2 * j + 1) (by omega)]
  rw [← ZMod.expand_card, ← ZMod.expand_card]
  ext k
  rw [coeff_add, coeff_X_pow_mul', coeff_expand (by norm_num), coeff_natPoly, coeff_natPoly]
  rcases Nat.even_or_odd' k with ⟨j, rfl | rfl⟩
  · have h1 : 2 ∣ 2 * j := ⟨j, rfl⟩
    rw [he]
    by_cases hj : 1 ≤ 2 * j
    · rw [coeff_expand (by norm_num)]
      simp [h1, show ¬ 2 ∣ 2 * j - 1 by omega, hj]
    · simp [h1, hj]
  · have h1 : ¬ 2 ∣ 2 * j + 1 := by omega
    rw [coeff_expand (by norm_num), coeff_natPoly, hd]
    simp [h1]

theorem root_x_64_val : clmul.gf64.ROOT_X.val = 0xffff_ffff_0000_000a := by
  decide +kernel

/-- `ROOT_X` squares to `X` modulo the modulus. -/
theorem root_x_64_sq :
    AdjoinRoot.mk Poly64.modulus (natPoly clmul.gf64.ROOT_X.val) ^ 2 =
      AdjoinRoot.mk Poly64.modulus X := by
  rw [root_x_64_val, sq, ← mk_mulModHalves (by norm_num) (by norm_num),
    show mulModHalves 0xffff_ffff_0000_000a 0xffff_ffff_0000_000a = 2 by decide +kernel,
    natPoly_two]

theorem two_eq_zero_quot64 : (2 : Poly64.Quot) = 0 := by
  calc (2 : Poly64.Quot) = AdjoinRoot.mk Poly64.modulus 2 := (map_ofNat _ 2).symm
    _ = AdjoinRoot.mk Poly64.modulus 0 := by rw [ZMod2Poly.two_eq_zero]
    _ = 0 := map_zero _

theorem compactNat_val (x : ℕ) : (⟨BitVec.ofNat 64 (compactNat x)⟩ : Std.U64).val = compactNat x :=
  val_ofNat_64 (lt_trans (compactNat_lt _) (by norm_num))

/-- `poly_sqrt_64` never panics and returns a square root in `GF(2)[x] / (modulus)`. -/
theorem poly_sqrt_64_toQuot (a : Std.U64) :
    clmul.gf64.poly_sqrt_64 a ⦃ r => toQuot64 r * toQuot64 r = toQuot64 a ⦄ := by
  unfold clmul.gf64.poly_sqrt_64
  have hs : a >>> 1#i32 = .ok ⟨BitVec.ofNat 64 (a.val >>> 1)⟩ := by
    rw [shiftRight_i32_eq _ _ (by decide) (by decide)]
    congr 2
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, UScalarTy.U64_numBits_eq,
      show I32.toNat 1#i32 = 1 from rfl]
    rw [Nat.mod_eq_of_lt (lt_of_le_of_lt (Nat.shiftRight_le _ _) (u64_val_lt a))]
    rfl
  simp only [compact_even_eq, hs, poly_mul_64_eq, bind_tc_ok, WP.spec_ok]
  have hx : ∀ x y : Std.U64, toQuot64 (x ^^^ y) = toQuot64 x + toQuot64 y := by
    intro x y
    rw [toQuot64_eq, toQuot64_eq, toQuot64_eq, ← map_add, ← natPoly_xor]
    rfl
  rw [hx, toQuot64_mulMod64, toQuot64_eq, toQuot64_eq, toQuot64_eq, toQuot64_eq, compactNat_val,
    compactNat_val, val_ofNat_64 (lt_of_le_of_lt (Nat.shiftRight_le _ _) (u64_val_lt a)),
    natPoly_even_odd_64 (u64_val_lt a)]
  simp only [map_add, map_mul, map_pow]
  rw [← sq, ← root_x_64_sq]
  linear_combination (AdjoinRoot.mk Poly64.modulus (natPoly (compactNat a.val)) *
    (AdjoinRoot.mk Poly64.modulus (natPoly clmul.gf64.ROOT_X.val) *
      AdjoinRoot.mk Poly64.modulus (natPoly (compactNat (a.val >>> 1))))) * two_eq_zero_quot64

end Plonky3Lean.Proofs.Binary
