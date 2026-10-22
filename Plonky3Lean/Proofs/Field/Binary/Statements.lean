module

public import Plonky3Lean.Proofs.Field.Binary.Poly64Field
public import Plonky3Lean.Proofs.Field.Binary.Poly64Sqrt
public import Plonky3Lean.Proofs.Field.Binary.Poly192
public import Plonky3Lean.Proofs.Field.Binary.TowerField

@[expose] public section

/-!
# Binary fields: the statements the claims make

The proofs work with `natPoly n`, the polynomial of a natural number.

The claims speak of `poly x`, the polynomial of an integer of the model, and these lemmas
restate the results that way.
-/

open Aeneas Aeneas.Std CoreModels Polynomial
open p3_binary_field BinaryField BF128Ghash
open Plonky3Lean.Lib Plonky3Lean.Spec.BinaryField

namespace Plonky3Lean.Proofs.Binary

/-- `reduce_64` never panics and reduces modulo `x^64 + x^4 + x^3 + x + 1`. -/
theorem reduce_64_toQuot64 (p : Std.U128) :
    clmul.reduce_64 p ⦃ r => toQuot64 r = AdjoinRoot.mk BF64.basePoly (poly p) ⦄ := by
  rw [reduce_64_eq, WP.spec_ok, toQuot64_eq, val_ofNat_64 (reduce64Nat_lt _),
    mk_natPoly_reduce64Nat (u128_val_lt p), poly_eq_natPoly]

/-- `reduce_128` never panics and reduces `low + X^128 · high` in the GHASH field. -/
theorem reduce_128_toQuot_poly (low high : Std.U128) :
    clmul.reduce_128 low high ⦃ r =>
      toQuot (ghash r) = AdjoinRoot.mk ghashPoly (poly low + X ^ 128 * poly high) ⦄ := by
  rw [poly_eq_natPoly, poly_eq_natPoly]
  exact reduce_128_toQuot low high

/-- `poly_mul_128_by_64` never panics and multiplies by a 64-bit polynomial in the GHASH field. -/
theorem poly_mul_128_by_64_toQuot_poly (a : Std.U128) (b : Std.U64) :
    clmul.portable.poly_mul_128_by_64 a b ⦃ r =>
      toQuot (ghash r) = toQuot (ghash a) * AdjoinRoot.mk ghashPoly (poly b) ⦄ := by
  rw [poly_eq_natPoly]
  exact poly_mul_128_by_64_toQuot a b

/-! ## `GF(2^64)`, as CompPoly's `BF64` -/

/-- CompPoly's quotient map on `BF64`, as a ring homomorphism. -/
noncomputable def bf64ToQuot : BF64 →+* BF64.BF64Quot where
  toFun := BF64.toQuot
  map_one' := BF64.toQuot_one
  map_mul' := BF64.toQuot_mul
  map_zero' := BF64.toQuot_zero
  map_add' := BF64.toQuot_add

theorem poly_mul_64_bf64 (a b : Std.U64) :
    clmul.gf64.poly_mul_64 a b ⦃ r => bf64 r = bf64 a * bf64 b ⦄ :=
  WP.spec_mono (poly_mul_64_toQuot a b) fun _ h =>
    BF64.toQuot_injective (by rw [BF64.toQuot_mul]; exact h)

theorem poly_square_64_bf64 (a : Std.U64) :
    clmul.gf64.poly_square_64 a ⦃ r => bf64 r = bf64 a * bf64 a ⦄ :=
  WP.spec_mono (poly_square_64_toQuot a) fun _ h =>
    BF64.toQuot_injective (by rw [BF64.toQuot_mul]; exact h)

theorem poly_sqrt_64_bf64 (a : Std.U64) :
    clmul.gf64.poly_sqrt_64 a ⦃ r => bf64 r * bf64 r = bf64 a ⦄ :=
  WP.spec_mono (poly_sqrt_64_toQuot a) fun _ h =>
    BF64.toQuot_injective (by rw [BF64.toQuot_mul]; exact h)

theorem poly_inverse_64_bf64 (x : Std.U64) :
    clmul.gf64.poly_inverse_64 x ⦃ r => bf64 r = (bf64 x)⁻¹ ⦄ :=
  WP.spec_mono (poly_inverse_64_inv x) fun _ h =>
    BF64.toQuot_injective (h.trans (map_inv₀ bf64ToQuot (bf64 x)).symm)

/-! ## The GHASH field, as CompPoly's `ConcreteBF128Ghash` -/

theorem poly_square_128_ghash (a : Std.U128) :
    clmul.portable.poly_square_128 a ⦃ r => ghash r = ghash a * ghash a ⦄ :=
  WP.spec_mono (poly_square_128_toQuot a) fun _ h =>
    toQuot_injective (by rw [toQuot_mul]; exact h)

theorem poly_sqrt_128_ghash (a : Std.U128) :
    clmul.sqrt.poly_sqrt_128 a ⦃ r => ghash r * ghash r = ghash a ⦄ :=
  WP.spec_mono (poly_sqrt_128_toQuot a) fun _ h =>
    toQuot_injective (by rw [toQuot_mul]; exact h)

/-- `poly_mul_128_by_64(a, b)` is `a · b`, with `b` widened to 128 bits. -/
theorem poly_mul_128_by_64_ghash (a : Std.U128) (b : Std.U64) :
    clmul.portable.poly_mul_128_by_64 a b ⦃ r => ghash r = ghash a * ghash (UScalar.cast .U128 b) ⦄ :=
  WP.spec_mono (poly_mul_128_by_64_toQuot a b) fun _ h =>
    toQuot_injective (by
      rw [toQuot_mul, h, toQuot_eq_mk (UScalar.cast .U128 b), UScalar.cast_val_eq,
        UScalarTy.U128_numBits_eq, Nat.mod_eq_of_lt (by have := u64_val_lt b; omega)])

end Plonky3Lean.Proofs.Binary
