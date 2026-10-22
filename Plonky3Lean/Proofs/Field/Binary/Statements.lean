module

public import Plonky3Lean.Proofs.Field.Binary.Poly64Field
public import Plonky3Lean.Proofs.Field.Binary.Poly192Irreducible
public import Plonky3Lean.Proofs.Field.Binary.Tables

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
    clmul.reduce_64 p ⦃ r => toQuot64 r = AdjoinRoot.mk Poly64.modulus (poly p) ⦄ := by
  rw [reduce_64_eq, WP.spec_ok, toQuot64_eq, val_ofNat_64 (reduce64Nat_lt _),
    mk_natPoly_reduce64Nat (u128_val_lt p), poly_eq_natPoly]

/-- `reduce_128` never panics and reduces `low + X^128 · high` in the GHASH field. -/
theorem reduce_128_toQuot_poly (low high : Std.U128) :
    clmul.reduce_128 low high ⦃ r =>
      toQuot r.bv = AdjoinRoot.mk ghashPoly (poly low + X ^ 128 * poly high) ⦄ := by
  rw [poly_eq_natPoly, poly_eq_natPoly]
  exact reduce_128_toQuot low high

/-- `poly_mul_128_by_64` never panics and multiplies by a 64-bit polynomial in the GHASH field. -/
theorem poly_mul_128_by_64_toQuot_poly (a : Std.U128) (b : Std.U64) :
    clmul.portable.poly_mul_128_by_64 a b ⦃ r =>
      toQuot r.bv = toQuot a.bv * AdjoinRoot.mk ghashPoly (poly b) ⦄ := by
  rw [poly_eq_natPoly]
  exact poly_mul_128_by_64_toQuot a b

end Plonky3Lean.Proofs.Binary
