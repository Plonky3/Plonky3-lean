module

public import Plonky3Lean.Proofs.Field.Binary.Statements

@[expose] public section

/-!
# Binary fields: claims

What this repository asserts about p3-binary-field's portable integer kernels, at the Plonky3
commit pinned in `plonky3/`.

- The model is the scoped extraction in `crates/binary-field`.
- An integer stands for a polynomial over `GF(2)`: bit `i` is the coefficient of `X^i` (`poly`).
- `GF(2^128)` is CompPoly's GHASH field, `GF(2)[X] / (X^128 + X^7 + X^2 + X + 1)`, read through
  CompPoly's `toQuot`.
- `GF(2^64)` is `GF(2)[X] / (X^64 + X^4 + X^3 + X + 1)`, read through `toQuot64`.
- `GF(2^192)` is `GF(2^64)[Y] / (Y^3 + Y + 1)`, three limbs read through `toQuot192`.
- The tower's `GF(2^8)` is CompPoly's `ConcreteBTField 3`, a byte read bit for bit (`tower8`).

Both moduli staged here are claimed irreducible, so both quotients are fields.

Every claim holds for every input.

`m ⦃ r => P r ⦄` states that `m` returns a value `r`, so it does not panic, and that `P r` holds.

Not claimed:
- the tower fields above `GF(2^8)`;
- the field types themselves (`BinaryField8`, `Poly64`, `Poly192`, ...), whose trait hierarchy is
  not extracted;
- the dot products, the AES and bit-plane code, and the packed (SIMD) arithmetic;
- the hardware kernels (PCLMULQDQ, PMULL, GFNI), which the extraction target does not have.
-/

open Aeneas Aeneas.Std CoreModels Polynomial
open p3_binary_field BinaryField BF128Ghash ConcreteBinaryTower
open Plonky3Lean.Spec.BinaryField

namespace Plonky3Lean.Claims.BinaryField

/-! ## Carry-less multiplication -/

/-- `clmul_64x64` is the carry-less product of two 64-bit polynomials. -/
theorem clmul.portable.clmul_64x64.poly (a b : Std.U64) :
    clmul.portable.clmul_64x64 a b ⦃ r => poly r = poly a * poly b ⦄ :=
  Proofs.Binary.clmul_64x64_spec a b

/-! ## `GF(2^128)`, the GHASH field -/

/-- `reduce_128(low, high)` is `low + X^128 · high` in the GHASH field. -/
theorem clmul.reduce_128.toQuot (low high : Std.U128) :
    clmul.reduce_128 low high ⦃ r =>
      toQuot r.bv = AdjoinRoot.mk ghashPoly (poly low + X ^ 128 * poly high) ⦄ :=
  Proofs.Binary.reduce_128_toQuot_poly low high

/-- `poly_mul_128` is multiplication in the GHASH field. -/
theorem clmul.portable.poly_mul_128.toQuot (a b : Std.U128) :
    clmul.portable.poly_mul_128 a b ⦃ r => toQuot r.bv = toQuot a.bv * toQuot b.bv ⦄ :=
  Proofs.Binary.poly_mul_128_toQuot a b

/-- `poly_square_128` is squaring in the GHASH field. -/
theorem clmul.portable.poly_square_128.toQuot (a : Std.U128) :
    clmul.portable.poly_square_128 a ⦃ r => toQuot r.bv = toQuot a.bv * toQuot a.bv ⦄ :=
  Proofs.Binary.poly_square_128_toQuot a

/-- `poly_mul_128_by_64` is multiplication by a polynomial of degree below `64` in the GHASH field. -/
theorem clmul.portable.poly_mul_128_by_64.toQuot (a : Std.U128) (b : Std.U64) :
    clmul.portable.poly_mul_128_by_64 a b ⦃ r =>
      toQuot r.bv = toQuot a.bv * AdjoinRoot.mk ghashPoly (poly b) ⦄ :=
  Proofs.Binary.poly_mul_128_by_64_toQuot_poly a b

/-- `poly_sqrt_128` returns a square root in the GHASH field. -/
theorem clmul.sqrt.poly_sqrt_128.toQuot (a : Std.U128) :
    clmul.sqrt.poly_sqrt_128 a ⦃ r => toQuot r.bv * toQuot r.bv = toQuot a.bv ⦄ :=
  Proofs.Binary.poly_sqrt_128_toQuot a

/-! ## `GF(2^64)` -/

/-- `X^64 + X^4 + X^3 + X + 1` is irreducible over `GF(2)`, so `GF(2)[X] / (modulus)` is a field. -/
theorem Poly64.modulus.irreducible : Irreducible Poly64.modulus :=
  Proofs.Binary.modulus_irreducible

/-- `reduce_64(p)` is `p` modulo `X^64 + X^4 + X^3 + X + 1`. -/
theorem clmul.reduce_64.toQuot64 (p : Std.U128) :
    clmul.reduce_64 p ⦃ r => toQuot64 r = AdjoinRoot.mk Poly64.modulus (poly p) ⦄ :=
  Proofs.Binary.reduce_64_toQuot64 p

/-- `poly_mul_64` is multiplication in `GF(2^64)`. -/
theorem clmul.gf64.poly_mul_64.toQuot64 (a b : Std.U64) :
    clmul.gf64.poly_mul_64 a b ⦃ r => toQuot64 r = toQuot64 a * toQuot64 b ⦄ :=
  Proofs.Binary.poly_mul_64_toQuot a b

/-- `poly_square_64` is squaring in `GF(2^64)`. -/
theorem clmul.gf64.poly_square_64.toQuot64 (a : Std.U64) :
    clmul.gf64.poly_square_64 a ⦃ r => toQuot64 r = toQuot64 a * toQuot64 a ⦄ :=
  Proofs.Binary.poly_square_64_toQuot a

/-- `poly_sqrt_64` returns a square root in `GF(2^64)`. -/
theorem clmul.gf64.poly_sqrt_64.toQuot64 (a : Std.U64) :
    clmul.gf64.poly_sqrt_64 a ⦃ r => toQuot64 r * toQuot64 r = toQuot64 a ⦄ :=
  Proofs.Binary.poly_sqrt_64_toQuot a

/-- `poly_inverse_64` is inversion in `GF(2^64)`, with `0` sent to `0`. -/
theorem clmul.gf64.poly_inverse_64.toQuot64 (x : Std.U64) :
    clmul.gf64.poly_inverse_64 x ⦃ r => toQuot64 r = (toQuot64 x)⁻¹ ⦄ :=
  Proofs.Binary.poly_inverse_64_inv x

/-! ## `GF(2^192)` -/

/-- `Y^3 + Y + 1` is irreducible over `GF(2^64)`, so `GF(2^64)[Y] / (Y^3 + Y + 1)` is a field. -/
theorem Poly192.modulus.irreducible : Irreducible Poly192.modulus :=
  Proofs.Binary.poly192_irreducible

/-- `poly_mul_192` is multiplication in `GF(2^192)`. -/
theorem clmul.gf192.poly_mul_192.toQuot192 (a b : Std.Array Std.U64 3#usize) :
    clmul.gf192.poly_mul_192 a b ⦃ r => toQuot192 r = toQuot192 a * toQuot192 b ⦄ :=
  Proofs.Binary.poly_mul_192_toQuot a b

/-- `poly_square_192` is squaring in `GF(2^192)`. -/
theorem clmul.gf192.poly_square_192.toQuot192 (a : Std.Array Std.U64 3#usize) :
    clmul.gf192.poly_square_192 a ⦃ r => toQuot192 r = toQuot192 a * toQuot192 a ⦄ :=
  Proofs.Binary.poly_square_192_toQuot a

/-- `poly_mul_192_by_64` is multiplication by an element of `GF(2^64)`, embedded in `GF(2^192)`. -/
theorem clmul.gf192.poly_mul_192_by_64.toQuot192 (a : Std.Array Std.U64 3#usize) (k : Std.U64) :
    clmul.gf192.poly_mul_192_by_64 a k ⦃ r =>
      toQuot192 r = toQuot192 a * AdjoinRoot.of Poly192.modulus (toQuot64 k) ⦄ :=
  Proofs.Binary.poly_mul_192_by_64_toQuot a k

/-! ## The tower's `GF(2^8)`, through lookup tables -/

/-- `tables::mul` is multiplication in the tower's `GF(2^8)`. -/
theorem tables.mul.tower8 (a b : Std.U8) :
    tables.mul a b ⦃ r => tower8 r = tower8 a * tower8 b ⦄ :=
  Proofs.Binary.tables_mul_spec a b

/-- `tables::square` is squaring in the tower's `GF(2^8)`. -/
theorem tables.square.tower8 (a : Std.U8) :
    tables.square a ⦃ r => tower8 r = tower8 a * tower8 a ⦄ :=
  Proofs.Binary.tables_square_spec a

/-- `tables::try_inverse` is `None` for `0`, and otherwise the inverse in the tower's `GF(2^8)`. -/
theorem tables.try_inverse.tower8 (a : Std.U8) :
    tables.try_inverse a ⦃ r => (tower8 a = 0 → r = none) ∧
      (tower8 a ≠ 0 → ∃ c, r = some c ∧ tower8 c * tower8 a = 1) ⦄ :=
  Proofs.Binary.tables_try_inverse_spec a

end Plonky3Lean.Claims.BinaryField
