import P3BinaryField
import Plonky3Lean.Lib.Scalar.Bits
import Plonky3Lean.Proofs.Field.Binary.MaskedMul
import Plonky3Lean.Spec.BinaryField

/-!
# The portable carry-less multiply

`bmul64` returns the low half of the carry-less product.

Reversing both operands reverses the product, so the same routine on the reversed operands
returns the high half.
-/

open Aeneas Aeneas.Std CoreModels Polynomial
open p3_binary_field BinaryField
open Plonky3Lean.Lib Plonky3Lean.Spec.BinaryField

namespace Plonky3Lean.Proofs.Binary

theorem u64_val_lt (x : Std.U64) : x.val < 2 ^ 64 := by
  have := x.hBounds; simpa using this

theorem u128_val_lt (x : Std.U128) : x.val < 2 ^ 128 := by
  have := x.hBounds; simpa using this

theorem poly_eq_natPoly {ty : UScalarTy} (x : UScalar ty) : poly x = natPoly x.val :=
  toPoly_eq_natPoly x.bv

/-! ## The low half -/

/-- `bmul64` never panics and returns the masked multiply. -/
theorem bmul64_eq (x y : Std.U64) :
    clmul.portable.bmul64 x y = .ok ⟨BitVec.ofNat 64 (bmulNat x.val y.val)⟩ := by
  unfold clmul.portable.bmul64 clmul.portable.NIBBLE_1 clmul.portable.NIBBLE_2
    clmul.portable.NIBBLE_3
  simp (disch := decide) only [shiftLeft_i32_eq, lift_eq, bind_tc_ok, wrapping_mul_u64_eq]
  congr 1
  apply UScalar.eq_of_val_eq
  have h0 : clmul.portable.NIBBLE_0.bv.toNat = nibbleMask 0 := by
    unfold clmul.portable.NIBBLE_0; rfl
  have h1 : (clmul.portable.NIBBLE_0.bv <<< I32.toNat 1#i32).toNat = nibbleMask 1 := by
    unfold clmul.portable.NIBBLE_0; rfl
  have h2 : (clmul.portable.NIBBLE_0.bv <<< I32.toNat 2#i32).toNat = nibbleMask 2 := by
    unfold clmul.portable.NIBBLE_0; rfl
  have h3 : (clmul.portable.NIBBLE_0.bv <<< I32.toNat 3#i32).toNat = nibbleMask 3 := by
    unfold clmul.portable.NIBBLE_0; rfl
  simp only [UScalar.val, and_bv, or_bv, xor_bv, BitVec.toNat_and, BitVec.toNat_or,
    BitVec.toNat_xor, BitVec.toNat_mul, h0, h1, h2, h3]
  simp only [UScalarTy.U64_numBits_eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (bmulNat_lt _ _)]
  rfl

/-! ## Reversal -/

theorem natDegree_natPoly_le {a k : ℕ} (ha : a < 2 ^ (k + 1)) : (natPoly a).natDegree ≤ k := by
  rw [natDegree_le_iff_coeff_eq_zero]
  intro N hN
  exact coeff_natPoly_of_lt ha (by exact_mod_cast hN)

/-- Reversing 64 bits reflects the polynomial about degree `63`. -/
theorem natPoly_reverse (v : BitVec 64) :
    natPoly v.reverse.toNat = reflect 63 (natPoly v.toNat) := by
  ext i
  rw [coeff_reflect, coeff_natPoly, coeff_natPoly, BitVec.testBit_toNat, BitVec.getLsbD_reverse,
    BitVec.getMsbD]
  by_cases hi : i ≤ 63
  · rw [revAt_le hi, BitVec.testBit_toNat, decide_eq_true (by omega), Bool.true_and]
  · rw [revAt, Function.Embedding.coeFn_mk, if_neg hi, decide_eq_false (by omega),
      Bool.false_and, BitVec.testBit_toNat, BitVec.getLsbD_of_ge _ _ (by omega)]

/-- The coefficients of a product of two polynomials of degree below `64` stop at `126`. -/
theorem coeff_mul_of_ge {a b : ℕ} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) {n : ℕ} (hn : 127 ≤ n) :
    (natPoly a * natPoly b).coeff n = 0 := by
  apply coeff_eq_zero_of_natDegree_lt
  have h1 := natDegree_natPoly_le (k := 63) ha
  have h2 := natDegree_natPoly_le (k := 63) hb
  have := natDegree_mul_le (p := natPoly a) (q := natPoly b)
  omega

/-- The value `clmul_64x64_halves` puts in its high half. -/
def highNat (a b : BitVec 64) : ℕ :=
  (BitVec.ofNat 64 (bmulNat a.reverse.toNat b.reverse.toNat)).reverse.toNat >>> 1

theorem highNat_lt (a b : BitVec 64) : highNat a b < 2 ^ 64 :=
  lt_of_le_of_lt (Nat.shiftRight_le _ _) (BitVec.isLt _)

/-- The high half holds coefficients `64` to `127` of the carry-less product. -/
theorem coeff_natPoly_highNat (a b : BitVec 64) (j : ℕ) :
    (natPoly (highNat a b)).coeff j = (natPoly a.toNat * natPoly b.toNat).coeff (64 + j) := by
  rw [coeff_natPoly, highNat, Nat.testBit_shiftRight, BitVec.testBit_toNat,
    BitVec.getLsbD_reverse, BitVec.getMsbD]
  by_cases hj : j ≤ 62
  · rw [decide_eq_true (by omega), Bool.true_and, ← BitVec.testBit_toNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (bmulNat_lt _ _), show 64 - 1 - (1 + j) = 62 - j by omega,
      ← coeff_natPoly, coeff_natPoly_bmulNat (BitVec.isLt _) (BitVec.isLt _) (by omega),
      natPoly_reverse, natPoly_reverse,
      ← reflect_mul _ _ (natDegree_natPoly_le (BitVec.isLt _))
        (natDegree_natPoly_le (BitVec.isLt _)),
      coeff_reflect, revAt_le (by omega)]
    congr 1
    omega
  · rw [decide_eq_false (by omega), Bool.false_and,
      coeff_mul_of_ge (BitVec.isLt _) (BitVec.isLt _) (by omega)]
    rfl

/-- The low and high halves together are the carry-less product. -/
theorem natPoly_halves (a b : BitVec 64) :
    natPoly (bmulNat a.toNat b.toNat) + X ^ 64 * natPoly (highNat a b) =
      natPoly a.toNat * natPoly b.toNat := by
  ext p
  rw [coeff_add, coeff_X_pow_mul']
  by_cases hp : p < 64
  · rw [coeff_natPoly_bmulNat (BitVec.isLt _) (BitVec.isLt _) hp, if_neg (by omega), add_zero]
  · rw [coeff_natPoly_of_lt (bmulNat_lt _ _) (by omega), if_pos (by omega),
      coeff_natPoly_highNat, zero_add]
    congr 1
    omega

/-! ## The extracted functions -/

/-- `clmul_64x64_halves` never panics and returns the low and high halves. -/
theorem clmul_64x64_halves_eq (a b : Std.U64) :
    clmul.portable.clmul_64x64_halves a b =
      .ok (⟨BitVec.ofNat 64 (bmulNat a.val b.val)⟩, ⟨BitVec.ofNat 64 (highNat a.bv b.bv)⟩) := by
  unfold clmul.portable.clmul_64x64_halves
  simp (disch := decide) only [bmul64_eq, reverse_bits_u64_eq, shiftRight_i32_eq, bind_tc_ok]
  congr 3
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight, UScalarTy.U64_numBits_eq, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (highNat_lt _ _)]
  rfl

/-- `clmul_64x64` never panics and returns the halves side by side. -/
theorem clmul_64x64_eq (a b : Std.U64) :
    clmul.portable.clmul_64x64 a b =
      .ok ⟨BitVec.ofNat 128 (bmulNat a.val b.val ||| highNat a.bv b.bv <<< 64)⟩ := by
  unfold clmul.portable.clmul_64x64
  rw [clmul_64x64_halves_eq]
  simp (disch := decide) only [lift_eq, shiftLeft_i32_eq, bind_tc_ok]
  show RustM.ok _ = _
  congr 1
  apply UScalar.eq_of_val_eq
  simp only [UScalar.val, or_bv, cast_bv, BitVec.toNat_or, BitVec.toNat_shiftLeft,
    BitVec.toNat_setWidth, BitVec.toNat_ofNat, UScalarTy.U64_numBits_eq, UScalarTy.U128_numBits_eq,
    Nat.mod_eq_of_lt (bmulNat_lt _ _), Nat.mod_eq_of_lt (highNat_lt _ _)]
  have hl := bmulNat_lt a.bv.toNat b.bv.toNat
  have hh := highNat_lt a.bv b.bv
  have hs : highNat a.bv b.bv <<< 64 < 2 ^ 128 := by rw [Nat.shiftLeft_eq]; omega
  have ho : bmulNat a.bv.toNat b.bv.toNat ||| highNat a.bv b.bv <<< 64 < 2 ^ 128 :=
    Nat.or_lt_two_pow (by omega) hs
  rw [show I32.toNat 64#i32 = 64 from rfl, Nat.mod_eq_of_lt (by omega : bmulNat a.bv.toNat b.bv.toNat < 2 ^ 128),
    Nat.mod_eq_of_lt (by omega : highNat a.bv b.bv < 2 ^ 128), Nat.mod_eq_of_lt hs,
    Nat.mod_eq_of_lt ho]

/-- `clmul_64x64` never panics and returns the carry-less product. -/
theorem clmul_64x64_spec (a b : Std.U64) :
    clmul.portable.clmul_64x64 a b ⦃ r => poly r = poly a * poly b ⦄ := by
  rw [clmul_64x64_eq, WP.spec_ok, poly_eq_natPoly, poly_eq_natPoly, poly_eq_natPoly]
  show natPoly _ = natPoly a.bv.toNat * natPoly b.bv.toNat
  rw [← natPoly_halves, ← natPoly_or_shiftLeft (bmulNat_lt _ _)]
  congr 1
  show (BitVec.ofNat 128 _).toNat = _
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
  · rfl
  · exact Nat.or_lt_two_pow (lt_trans (bmulNat_lt _ _) (by norm_num))
      (by rw [Nat.shiftLeft_eq]; have := highNat_lt a.bv b.bv; omega)

end Plonky3Lean.Proofs.Binary
