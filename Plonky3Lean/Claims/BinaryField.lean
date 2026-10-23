module

public import Plonky3Lean.Proofs.Field.Binary.Aes
public import Plonky3Lean.Proofs.Field.Binary.Operators
public import Plonky3Lean.Proofs.Field.Binary.TowerApi
public import Plonky3Lean.Proofs.Field.Binary.PolyField
public import Plonky3Lean.Proofs.Field.Binary.ExtensionMul
public import Plonky3Lean.Proofs.Field.Binary.CantorSpec

@[expose] public section

/-!
# Binary fields: claims

What this repository asserts about p3-binary-field's portable arithmetic, at the Plonky3 commit
pinned in `plonky3/`.

- The model is the scoped extraction in `crates/binary-field`.
- An integer stands for a polynomial over `GF(2)`: bit `i` is the coefficient of `X^i` (`poly`).
- Every field is CompPoly's, and an integer is read as one of its elements:
  - `GF(2^64)` is `BF64`, `GF(2)[X] / (X^64 + X^4 + X^3 + X + 1)`, read through `bf64`;
  - `GF(2^128)` is the GHASH field, `GF(2)[X] / (X^128 + X^7 + X^2 + X + 1)`, read through `ghash`;
  - `GF(2^192)` is `BF64.Ext3`, `BF64[Y] / (Y^3 + Y + 1)`, three limbs read through `toExt3`;
  - the block cipher's `GF(2^8)` is `AesField`, `GF(2)[X] / (X^8 + X^4 + X^3 + X + 1)`, read
    through `aes`;
  - level `k` of the binary tower, `GF(2^(2^k))`, is `ConcreteBTField k`, read through `towerOf k`
    from the low `2^k` bits.
- CompPoly proves each of these is a field.

Every claim holds for every input, unless it states a hypothesis.

`m ⦃ r => P r ⦄` states that `m` returns a value `r`, so it does not panic, and that `P r` holds.

Not claimed:
- the trait methods of the field types (`square`, `try_inverse`, `Field`, `ExtensionField`, ...),
  which the extraction cannot reach;
- the dot products, the AES and bit-plane code, the challenger and
  transcript, and the packed arithmetic;
- the hardware kernels (PCLMULQDQ, PMULL, GFNI), which the extraction target does not have; the
  carry-less paths around them are claimed with the portable carry-less multiply in their place.
-/

open Aeneas Aeneas.Std CoreModels Polynomial
open p3_binary_field BinaryField BF128Ghash ConcreteBinaryTower
open Plonky3Lean.Spec.BinaryField

namespace Plonky3Lean.Claims.P3BinaryField

/-! ## Carry-less multiplication -/

/-- `clmul_64x64` is the carry-less product of two 64-bit polynomials. -/
theorem clmul.portable.clmul_64x64.poly (a b : Std.U64) :
    clmul.portable.clmul_64x64 a b ⦃ r => poly r = poly a * poly b ⦄ :=
  Proofs.Binary.clmul_64x64_spec a b

/-! ## `GF(2^128)`, the GHASH field -/

/-- `reduce_128(low, high)` is `low + X^128 · high` in the GHASH field. -/
theorem clmul.reduce_128.toQuot (low high : Std.U128) :
    clmul.reduce_128 low high ⦃ r =>
      toQuot (ghash r) = AdjoinRoot.mk ghashPoly (poly low + X ^ 128 * poly high) ⦄ :=
  Proofs.Binary.reduce_128_toQuot_poly low high

/-- `poly_mul_128` is multiplication in the GHASH field. -/
theorem clmul.portable.poly_mul_128.ghash (a b : Std.U128) :
    clmul.portable.poly_mul_128 a b ⦃ r => ghash r = ghash a * ghash b ⦄ :=
  Proofs.Binary.poly_mul_128_spec a b

/-- `poly_square_128` is squaring in the GHASH field. -/
theorem clmul.portable.poly_square_128.ghash (a : Std.U128) :
    clmul.portable.poly_square_128 a ⦃ r => ghash r = ghash a * ghash a ⦄ :=
  Proofs.Binary.poly_square_128_ghash a

/-- `poly_mul_128_by_64` is multiplication by a 64-bit element in the GHASH field. -/
theorem clmul.portable.poly_mul_128_by_64.ghash (a : Std.U128) (b : Std.U64) :
    clmul.portable.poly_mul_128_by_64 a b ⦃ r => ghash r = ghash a * ghash (UScalar.cast .U128 b) ⦄ :=
  Proofs.Binary.poly_mul_128_by_64_ghash a b

/-- `poly_sqrt_128` returns a square root in the GHASH field. -/
theorem clmul.sqrt.poly_sqrt_128.ghash (a : Std.U128) :
    clmul.sqrt.poly_sqrt_128 a ⦃ r => ghash r * ghash r = ghash a ⦄ :=
  Proofs.Binary.poly_sqrt_128_ghash a

theorem ghash.Ghash128.Insts.CoreOpsArithAddGhash128Ghash128.add.toGhash (a b : ghash.Ghash128) :
    ghash.Ghash128.Insts.CoreOpsArithAddGhash128Ghash128.add a b ⦃ r => ghash r = ghash a + ghash b ⦄ :=
  Proofs.Binary.ghash128_add_ghash a b

theorem ghash.Ghash128.Insts.CoreOpsArithSubGhash128Ghash128.sub.toGhash (a b : ghash.Ghash128) :
    ghash.Ghash128.Insts.CoreOpsArithSubGhash128Ghash128.sub a b ⦃ r => ghash r = ghash a - ghash b ⦄ :=
  Proofs.Binary.ghash128_sub_ghash a b

theorem ghash.Ghash128.Insts.CoreOpsArithNegGhash128.neg.toGhash (a : ghash.Ghash128) :
    ghash.Ghash128.Insts.CoreOpsArithNegGhash128.neg a ⦃ r => ghash r = -ghash a ⦄ :=
  Proofs.Binary.ghash128_neg_ghash a

theorem ghash.Ghash128.Insts.CoreOpsArithMulGhash128Ghash128.mul.toGhash (a b : ghash.Ghash128) :
    ghash.Ghash128.Insts.CoreOpsArithMulGhash128Ghash128.mul a b ⦃ r => ghash r = ghash a * ghash b ⦄ :=
  Proofs.Binary.ghash128_mul_ghash a b

/-! ## `GF(2^64)` -/

/-- `reduce_64(p)` is `p` modulo `X^64 + X^4 + X^3 + X + 1`. -/
theorem clmul.reduce_64.toQuot64 (p : Std.U128) :
    clmul.reduce_64 p ⦃ r => toQuot64 r = AdjoinRoot.mk BF64.basePoly (poly p) ⦄ :=
  Proofs.Binary.reduce_64_toQuot64 p

/-- `poly_mul_64` is multiplication in `GF(2^64)`. -/
theorem clmul.gf64.poly_mul_64.bf64 (a b : Std.U64) :
    clmul.gf64.poly_mul_64 a b ⦃ r => bf64 r = bf64 a * bf64 b ⦄ :=
  Proofs.Binary.poly_mul_64_bf64 a b

/-- `poly_square_64` is squaring in `GF(2^64)`. -/
theorem clmul.gf64.poly_square_64.bf64 (a : Std.U64) :
    clmul.gf64.poly_square_64 a ⦃ r => bf64 r = bf64 a * bf64 a ⦄ :=
  Proofs.Binary.poly_square_64_bf64 a

/-- `poly_sqrt_64` returns a square root in `GF(2^64)`. -/
theorem clmul.gf64.poly_sqrt_64.bf64 (a : Std.U64) :
    clmul.gf64.poly_sqrt_64 a ⦃ r => bf64 r * bf64 r = bf64 a ⦄ :=
  Proofs.Binary.poly_sqrt_64_bf64 a

/-- `poly_inverse_64` is inversion in `GF(2^64)`, with `0` sent to `0`. -/
theorem clmul.gf64.poly_inverse_64.bf64 (x : Std.U64) :
    clmul.gf64.poly_inverse_64 x ⦃ r => bf64 r = (bf64 x)⁻¹ ⦄ :=
  Proofs.Binary.poly_inverse_64_bf64 x

theorem poly64.Poly64.Insts.CoreOpsArithAddPoly64Poly64.add.bf64 (a b : poly64.Poly64) :
    poly64.Poly64.Insts.CoreOpsArithAddPoly64Poly64.add a b ⦃ r => bf64 r = bf64 a + bf64 b ⦄ :=
  Proofs.Binary.poly64_add_bf64 a b

theorem poly64.Poly64.Insts.CoreOpsArithSubPoly64Poly64.sub.bf64 (a b : poly64.Poly64) :
    poly64.Poly64.Insts.CoreOpsArithSubPoly64Poly64.sub a b ⦃ r => bf64 r = bf64 a - bf64 b ⦄ :=
  Proofs.Binary.poly64_sub_bf64 a b

theorem poly64.Poly64.Insts.CoreOpsArithNegPoly64.neg.bf64 (a : poly64.Poly64) :
    poly64.Poly64.Insts.CoreOpsArithNegPoly64.neg a ⦃ r => bf64 r = -bf64 a ⦄ :=
  Proofs.Binary.poly64_neg_bf64 a

theorem poly64.Poly64.Insts.CoreOpsArithMulPoly64Poly64.mul.bf64 (a b : poly64.Poly64) :
    poly64.Poly64.Insts.CoreOpsArithMulPoly64Poly64.mul a b ⦃ r => bf64 r = bf64 a * bf64 b ⦄ :=
  Proofs.Binary.poly64_mul_bf64 a b

/-! ## `GF(2^192)` -/

/-- `poly_mul_192` is multiplication in `GF(2^192)`. -/
theorem clmul.gf192.poly_mul_192.toExt3 (a b : Std.Array Std.U64 3#usize) :
    clmul.gf192.poly_mul_192 a b ⦃ r => toExt3 r = toExt3 a * toExt3 b ⦄ :=
  Proofs.Binary.poly_mul_192_ext a b

/-- `poly_square_192` is squaring in `GF(2^192)`. -/
theorem clmul.gf192.poly_square_192.toExt3 (a : Std.Array Std.U64 3#usize) :
    clmul.gf192.poly_square_192 a ⦃ r => toExt3 r = toExt3 a * toExt3 a ⦄ :=
  Proofs.Binary.poly_square_192_ext a

/-- `poly_mul_192_by_64` is multiplication by an element of `GF(2^64)`, embedded in `GF(2^192)`. -/
theorem clmul.gf192.poly_mul_192_by_64.toExt3 (a : Std.Array Std.U64 3#usize) (k : Std.U64) :
    clmul.gf192.poly_mul_192_by_64 a k ⦃ r =>
      toExt3 r = toExt3 a * algebraMap BF64 BF64.Ext3 (bf64 k) ⦄ :=
  Proofs.Binary.poly_mul_192_by_64_ext a k

theorem poly192.Poly192.Insts.CoreOpsArithAddPoly192Poly192.add.toExt3 (a b : poly192.Poly192) :
    poly192.Poly192.Insts.CoreOpsArithAddPoly192Poly192.add a b ⦃ r =>
      toExt3 r = toExt3 a + toExt3 b ⦄ :=
  Proofs.Binary.poly192_add_ext a b

theorem poly192.Poly192.Insts.CoreOpsArithSubPoly192Poly192.sub.toExt3 (a b : poly192.Poly192) :
    poly192.Poly192.Insts.CoreOpsArithSubPoly192Poly192.sub a b ⦃ r =>
      toExt3 r = toExt3 a - toExt3 b ⦄ :=
  Proofs.Binary.poly192_sub_ext a b

theorem poly192.Poly192.Insts.CoreOpsArithNegPoly192.neg.toExt3 (a : poly192.Poly192) :
    poly192.Poly192.Insts.CoreOpsArithNegPoly192.neg a ⦃ r => toExt3 r = -toExt3 a ⦄ :=
  Proofs.Binary.poly192_neg_ext a

theorem poly192.Poly192.Insts.CoreOpsArithMulPoly192Poly192.mul.toExt3 (a b : poly192.Poly192) :
    poly192.Poly192.Insts.CoreOpsArithMulPoly192Poly192.mul a b ⦃ r =>
      toExt3 r = toExt3 a * toExt3 b ⦄ :=
  Proofs.Binary.poly192_mul_ext a b

/-! ## The block cipher's `GF(2^8)` -/

/-- `aes::mul_bytes` is multiplication in the block cipher's field. -/
theorem aes.mul_bytes.toAesField (a b : Std.U8) :
    aes.mul_bytes a b ⦃ r => Spec.BinaryField.aes r = Spec.BinaryField.aes a * Spec.BinaryField.aes b ⦄ :=
  Proofs.Binary.mul_bytes_aes a b

/-- `aes::invert_byte` is inversion in the block cipher's field, with `0` sent to `0`. -/
theorem aes.invert_byte.toAesField (a : Std.U8) :
    aes.invert_byte a ⦃ r => Spec.BinaryField.aes r = (Spec.BinaryField.aes a)⁻¹ ⦄ :=
  Proofs.Binary.invert_byte_aes a

/-! ## The binary tower

Each level `k` stores `GF(2^(2^k))` in an integer, and its operations act on the low `2^k` bits.
-/

/-! ### `GF(2^8)`, through lookup tables -/

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

/-! ### `GF(2)`, `Gf2` -/

theorem gf2.Gf2.Insts.CoreOpsArithAddGf2Gf2.add.towerOf (a b : gf2.Gf2) :
    gf2.Gf2.Insts.CoreOpsArithAddGf2Gf2.add a b ⦃ r => towerOf 0 r = towerOf 0 a + towerOf 0 b ⦄ :=
  WP.spec_mono (Proofs.Binary.gf2_add_spec a b) fun _ h => Proofs.Binary.towerOf_add h

theorem gf2.Gf2.Insts.CoreOpsArithSubGf2Gf2.sub.towerOf (a b : gf2.Gf2) :
    gf2.Gf2.Insts.CoreOpsArithSubGf2Gf2.sub a b ⦃ r => towerOf 0 r = towerOf 0 a - towerOf 0 b ⦄ :=
  WP.spec_mono (Proofs.Binary.gf2_sub_spec a b) fun _ h => Proofs.Binary.towerOf_sub h

theorem gf2.Gf2.Insts.CoreOpsArithMulGf2Gf2.mul.towerOf (a b : gf2.Gf2) :
    gf2.Gf2.Insts.CoreOpsArithMulGf2Gf2.mul a b ⦃ r => towerOf 0 r = towerOf 0 a * towerOf 0 b ⦄ :=
  WP.spec_mono (Proofs.Binary.gf2_mul_spec a b) fun _ h => Proofs.Binary.towerOf_mul h

theorem gf2.Gf2.Insts.CoreOpsArithNegGf2.neg.towerOf (a : gf2.Gf2) :
    gf2.Gf2.Insts.CoreOpsArithNegGf2.neg a ⦃ r => towerOf 0 r = -towerOf 0 a ⦄ :=
  WP.spec_mono (Proofs.Binary.gf2_neg_spec a) fun _ h => Proofs.Binary.towerOf_neg h

/-- `from_repr` keeps the low `2^0` bits of its argument. -/
theorem gf2.Gf2.from_repr.towerOf (r : Std.U8) :
    gf2.Gf2.from_repr r ⦃ x => x.val < 2 ^ 2 ^ 0 ∧ towerOf 0 x = towerOf 0 r ⦄ :=
  WP.spec_mono (Proofs.Binary.gf2_from_repr_spec r) fun _ h =>
    ⟨h ▸ Nat.mod_lt _ (by positivity), Proofs.Binary.towerOf_mod h⟩

/-- `mul_alpha` multiplies by the level's generator `Z 0`. -/
theorem gf2.Gf2.mul_alpha.towerOf (x : gf2.Gf2) (hx : x.val < 2 ^ 2 ^ 0) :
    gf2.Gf2.mul_alpha x ⦃ y => towerOf 0 y = towerOf 0 x * Z 0 ⦄ :=
  WP.spec_mono (Proofs.Binary.gf2_mul_alpha_spec x hx) fun _ h => Proofs.Binary.towerOf_mul_Z h

/-! ### `GF(2^2)`, `BinaryField2` -/

theorem tower.BinaryField2.Insts.CoreOpsArithAddBinaryField2BinaryField2.add.towerOf (a b : tower.BinaryField2) :
    tower.BinaryField2.Insts.CoreOpsArithAddBinaryField2BinaryField2.add a b ⦃ r => towerOf 1 r = towerOf 1 a + towerOf 1 b ⦄ :=
  WP.spec_mono (Proofs.Binary.bf2_add_spec a b) fun _ h => Proofs.Binary.towerOf_add h

theorem tower.BinaryField2.Insts.CoreOpsArithSubBinaryField2BinaryField2.sub.towerOf (a b : tower.BinaryField2) :
    tower.BinaryField2.Insts.CoreOpsArithSubBinaryField2BinaryField2.sub a b ⦃ r => towerOf 1 r = towerOf 1 a - towerOf 1 b ⦄ :=
  WP.spec_mono (Proofs.Binary.bf2_sub_spec a b) fun _ h => Proofs.Binary.towerOf_sub h

theorem tower.BinaryField2.Insts.CoreOpsArithMulBinaryField2BinaryField2.mul.towerOf (a b : tower.BinaryField2) :
    tower.BinaryField2.Insts.CoreOpsArithMulBinaryField2BinaryField2.mul a b ⦃ r => towerOf 1 r = towerOf 1 a * towerOf 1 b ⦄ :=
  WP.spec_mono (Proofs.Binary.bf2_mul_spec a b) fun _ h => Proofs.Binary.towerOf_mul h

theorem tower.BinaryField2.Insts.CoreOpsArithNegBinaryField2.neg.towerOf (a : tower.BinaryField2) :
    tower.BinaryField2.Insts.CoreOpsArithNegBinaryField2.neg a ⦃ r => towerOf 1 r = -towerOf 1 a ⦄ :=
  WP.spec_mono (Proofs.Binary.bf2_neg_spec a) fun _ h => Proofs.Binary.towerOf_neg h

/-- `from_repr` keeps the low `2^1` bits of its argument. -/
theorem tower.BinaryField2.from_repr.towerOf (r : Std.U8) :
    tower.BinaryField2.from_repr r ⦃ x => x.val < 2 ^ 2 ^ 1 ∧ towerOf 1 x = towerOf 1 r ⦄ :=
  WP.spec_mono (Proofs.Binary.bf2_from_repr_spec r) fun _ h =>
    ⟨h ▸ Nat.mod_lt _ (by positivity), Proofs.Binary.towerOf_mod h⟩

/-- `mul_alpha` multiplies by the level's generator `Z 1`. -/
theorem tower.BinaryField2.mul_alpha.towerOf (x : tower.BinaryField2) :
    tower.BinaryField2.mul_alpha x ⦃ y => towerOf 1 y = towerOf 1 x * Z 1 ⦄ :=
  WP.spec_mono (Proofs.Binary.bf2_mul_alpha_spec x) fun _ h => Proofs.Binary.towerOf_mul_Z h

/-! ### `GF(2^4)`, `BinaryField4` -/

theorem tower.BinaryField4.Insts.CoreOpsArithAddBinaryField4BinaryField4.add.towerOf (a b : tower.BinaryField4) :
    tower.BinaryField4.Insts.CoreOpsArithAddBinaryField4BinaryField4.add a b ⦃ r => towerOf 2 r = towerOf 2 a + towerOf 2 b ⦄ :=
  WP.spec_mono (Proofs.Binary.bf4_add_spec a b) fun _ h => Proofs.Binary.towerOf_add h

theorem tower.BinaryField4.Insts.CoreOpsArithSubBinaryField4BinaryField4.sub.towerOf (a b : tower.BinaryField4) :
    tower.BinaryField4.Insts.CoreOpsArithSubBinaryField4BinaryField4.sub a b ⦃ r => towerOf 2 r = towerOf 2 a - towerOf 2 b ⦄ :=
  WP.spec_mono (Proofs.Binary.bf4_sub_spec a b) fun _ h => Proofs.Binary.towerOf_sub h

theorem tower.BinaryField4.Insts.CoreOpsArithMulBinaryField4BinaryField4.mul.towerOf (a b : tower.BinaryField4) :
    tower.BinaryField4.Insts.CoreOpsArithMulBinaryField4BinaryField4.mul a b ⦃ r => towerOf 2 r = towerOf 2 a * towerOf 2 b ⦄ :=
  WP.spec_mono (Proofs.Binary.bf4_mul_spec a b) fun _ h => Proofs.Binary.towerOf_mul h

theorem tower.BinaryField4.Insts.CoreOpsArithNegBinaryField4.neg.towerOf (a : tower.BinaryField4) :
    tower.BinaryField4.Insts.CoreOpsArithNegBinaryField4.neg a ⦃ r => towerOf 2 r = -towerOf 2 a ⦄ :=
  WP.spec_mono (Proofs.Binary.bf4_neg_spec a) fun _ h => Proofs.Binary.towerOf_neg h

/-- `from_repr` keeps the low `2^2` bits of its argument. -/
theorem tower.BinaryField4.from_repr.towerOf (r : Std.U8) :
    tower.BinaryField4.from_repr r ⦃ x => x.val < 2 ^ 2 ^ 2 ∧ towerOf 2 x = towerOf 2 r ⦄ :=
  WP.spec_mono (Proofs.Binary.bf4_from_repr_spec r) fun _ h =>
    ⟨h ▸ Nat.mod_lt _ (by positivity), Proofs.Binary.towerOf_mod h⟩

/-! ### `GF(2^8)`, `BinaryField8` -/

theorem tower.BinaryField8.Insts.CoreOpsArithAddBinaryField8BinaryField8.add.towerOf (a b : tower.BinaryField8) :
    tower.BinaryField8.Insts.CoreOpsArithAddBinaryField8BinaryField8.add a b ⦃ r => towerOf 3 r = towerOf 3 a + towerOf 3 b ⦄ :=
  WP.spec_mono (Proofs.Binary.bf8_add_spec a b) fun _ h => Proofs.Binary.towerOf_add h

theorem tower.BinaryField8.Insts.CoreOpsArithSubBinaryField8BinaryField8.sub.towerOf (a b : tower.BinaryField8) :
    tower.BinaryField8.Insts.CoreOpsArithSubBinaryField8BinaryField8.sub a b ⦃ r => towerOf 3 r = towerOf 3 a - towerOf 3 b ⦄ :=
  WP.spec_mono (Proofs.Binary.bf8_sub_spec a b) fun _ h => Proofs.Binary.towerOf_sub h

theorem tower.BinaryField8.Insts.CoreOpsArithMulBinaryField8BinaryField8.mul.towerOf (a b : tower.BinaryField8) :
    tower.BinaryField8.Insts.CoreOpsArithMulBinaryField8BinaryField8.mul a b ⦃ r => towerOf 3 r = towerOf 3 a * towerOf 3 b ⦄ :=
  WP.spec_mono (Proofs.Binary.bf8_mul_spec a b) fun _ h => Proofs.Binary.towerOf_mul h

theorem tower.BinaryField8.Insts.CoreOpsArithNegBinaryField8.neg.towerOf (a : tower.BinaryField8) :
    tower.BinaryField8.Insts.CoreOpsArithNegBinaryField8.neg a ⦃ r => towerOf 3 r = -towerOf 3 a ⦄ :=
  WP.spec_mono (Proofs.Binary.bf8_neg_spec a) fun _ h => Proofs.Binary.towerOf_neg h

/-- `from_repr` keeps the low `2^3` bits of its argument. -/
theorem tower.BinaryField8.from_repr.towerOf (r : Std.U8) :
    tower.BinaryField8.from_repr r ⦃ x => x.val < 2 ^ 2 ^ 3 ∧ towerOf 3 x = towerOf 3 r ⦄ :=
  WP.spec_mono (Proofs.Binary.bf8_from_repr_spec r) fun _ h =>
    ⟨h ▸ Nat.mod_lt _ (by positivity), Proofs.Binary.towerOf_mod h⟩

/-- `mul_alpha` multiplies by the level's generator `Z 3`. -/
theorem tower.BinaryField8.mul_alpha.towerOf (x : tower.BinaryField8) :
    tower.BinaryField8.mul_alpha x ⦃ y => towerOf 3 y = towerOf 3 x * Z 3 ⦄ :=
  WP.spec_mono (Proofs.Binary.bf8_mul_alpha_spec x) fun _ h => Proofs.Binary.towerOf_mul_Z h

/-! ### `GF(2^16)`, `BinaryField16` -/

theorem tower.BinaryField16.Insts.CoreOpsArithAddBinaryField16BinaryField16.add.towerOf (a b : tower.BinaryField16) :
    tower.BinaryField16.Insts.CoreOpsArithAddBinaryField16BinaryField16.add a b ⦃ r => towerOf 4 r = towerOf 4 a + towerOf 4 b ⦄ :=
  WP.spec_mono (Proofs.Binary.bf16_add_spec a b) fun _ h => Proofs.Binary.towerOf_add h

theorem tower.BinaryField16.Insts.CoreOpsArithSubBinaryField16BinaryField16.sub.towerOf (a b : tower.BinaryField16) :
    tower.BinaryField16.Insts.CoreOpsArithSubBinaryField16BinaryField16.sub a b ⦃ r => towerOf 4 r = towerOf 4 a - towerOf 4 b ⦄ :=
  WP.spec_mono (Proofs.Binary.bf16_sub_spec a b) fun _ h => Proofs.Binary.towerOf_sub h

theorem tower.BinaryField16.Insts.CoreOpsArithMulBinaryField16BinaryField16.mul.towerOf (a b : tower.BinaryField16) :
    tower.BinaryField16.Insts.CoreOpsArithMulBinaryField16BinaryField16.mul a b ⦃ r => towerOf 4 r = towerOf 4 a * towerOf 4 b ⦄ :=
  WP.spec_mono (Proofs.Binary.bf16_mul_spec a b) fun _ h => Proofs.Binary.towerOf_mul h

theorem tower.BinaryField16.Insts.CoreOpsArithNegBinaryField16.neg.towerOf (a : tower.BinaryField16) :
    tower.BinaryField16.Insts.CoreOpsArithNegBinaryField16.neg a ⦃ r => towerOf 4 r = -towerOf 4 a ⦄ :=
  WP.spec_mono (Proofs.Binary.bf16_neg_spec a) fun _ h => Proofs.Binary.towerOf_neg h

/-- `from_repr` keeps the low `2^4` bits of its argument. -/
theorem tower.BinaryField16.from_repr.towerOf (r : Std.U16) :
    tower.BinaryField16.from_repr r ⦃ x => x.val < 2 ^ 2 ^ 4 ∧ towerOf 4 x = towerOf 4 r ⦄ :=
  WP.spec_mono (Proofs.Binary.bf16_from_repr_spec r) fun _ h =>
    ⟨h ▸ Nat.mod_lt _ (by positivity), Proofs.Binary.towerOf_mod h⟩

/-- `mul_alpha` multiplies by the level's generator `Z 4`. -/
theorem tower.BinaryField16.mul_alpha.towerOf (x : tower.BinaryField16) :
    tower.BinaryField16.mul_alpha x ⦃ y => towerOf 4 y = towerOf 4 x * Z 4 ⦄ :=
  WP.spec_mono (Proofs.Binary.bf16_mul_alpha_spec x) fun _ h => Proofs.Binary.towerOf_mul_Z h

/-! ### `GF(2^32)`, `BinaryField32` -/

theorem tower.BinaryField32.Insts.CoreOpsArithAddBinaryField32BinaryField32.add.towerOf (a b : tower.BinaryField32) :
    tower.BinaryField32.Insts.CoreOpsArithAddBinaryField32BinaryField32.add a b ⦃ r => towerOf 5 r = towerOf 5 a + towerOf 5 b ⦄ :=
  WP.spec_mono (Proofs.Binary.bf32_add_spec a b) fun _ h => Proofs.Binary.towerOf_add h

theorem tower.BinaryField32.Insts.CoreOpsArithSubBinaryField32BinaryField32.sub.towerOf (a b : tower.BinaryField32) :
    tower.BinaryField32.Insts.CoreOpsArithSubBinaryField32BinaryField32.sub a b ⦃ r => towerOf 5 r = towerOf 5 a - towerOf 5 b ⦄ :=
  WP.spec_mono (Proofs.Binary.bf32_sub_spec a b) fun _ h => Proofs.Binary.towerOf_sub h

theorem tower.BinaryField32.Insts.CoreOpsArithMulBinaryField32BinaryField32.mul.towerOf (a b : tower.BinaryField32) :
    tower.BinaryField32.Insts.CoreOpsArithMulBinaryField32BinaryField32.mul a b ⦃ r => towerOf 5 r = towerOf 5 a * towerOf 5 b ⦄ :=
  WP.spec_mono (Proofs.Binary.bf32_mul_spec a b) fun _ h => Proofs.Binary.towerOf_mul h

theorem tower.BinaryField32.Insts.CoreOpsArithNegBinaryField32.neg.towerOf (a : tower.BinaryField32) :
    tower.BinaryField32.Insts.CoreOpsArithNegBinaryField32.neg a ⦃ r => towerOf 5 r = -towerOf 5 a ⦄ :=
  WP.spec_mono (Proofs.Binary.bf32_neg_spec a) fun _ h => Proofs.Binary.towerOf_neg h

/-- `from_repr` keeps the low `2^5` bits of its argument. -/
theorem tower.BinaryField32.from_repr.towerOf (r : Std.U32) :
    tower.BinaryField32.from_repr r ⦃ x => x.val < 2 ^ 2 ^ 5 ∧ towerOf 5 x = towerOf 5 r ⦄ :=
  WP.spec_mono (Proofs.Binary.bf32_from_repr_spec r) fun _ h =>
    ⟨h ▸ Nat.mod_lt _ (by positivity), Proofs.Binary.towerOf_mod h⟩

/-- `mul_alpha` multiplies by the level's generator `Z 5`. -/
theorem tower.BinaryField32.mul_alpha.towerOf (x : tower.BinaryField32) :
    tower.BinaryField32.mul_alpha x ⦃ y => towerOf 5 y = towerOf 5 x * Z 5 ⦄ :=
  WP.spec_mono (Proofs.Binary.bf32_mul_alpha_spec x) fun _ h => Proofs.Binary.towerOf_mul_Z h

/-! ### `GF(2^64)`, `BinaryField64` -/

theorem tower.BinaryField64.Insts.CoreOpsArithAddBinaryField64BinaryField64.add.towerOf (a b : tower.BinaryField64) :
    tower.BinaryField64.Insts.CoreOpsArithAddBinaryField64BinaryField64.add a b ⦃ r => towerOf 6 r = towerOf 6 a + towerOf 6 b ⦄ :=
  WP.spec_mono (Proofs.Binary.bf64_add_spec a b) fun _ h => Proofs.Binary.towerOf_add h

theorem tower.BinaryField64.Insts.CoreOpsArithSubBinaryField64BinaryField64.sub.towerOf (a b : tower.BinaryField64) :
    tower.BinaryField64.Insts.CoreOpsArithSubBinaryField64BinaryField64.sub a b ⦃ r => towerOf 6 r = towerOf 6 a - towerOf 6 b ⦄ :=
  WP.spec_mono (Proofs.Binary.bf64_sub_spec a b) fun _ h => Proofs.Binary.towerOf_sub h

theorem tower.BinaryField64.Insts.CoreOpsArithMulBinaryField64BinaryField64.mul.towerOf (a b : tower.BinaryField64) :
    tower.BinaryField64.Insts.CoreOpsArithMulBinaryField64BinaryField64.mul a b ⦃ r => towerOf 6 r = towerOf 6 a * towerOf 6 b ⦄ :=
  WP.spec_mono (Proofs.Binary.bf64_mul_spec a b) fun _ h => Proofs.Binary.towerOf_mul h

theorem tower.BinaryField64.Insts.CoreOpsArithNegBinaryField64.neg.towerOf (a : tower.BinaryField64) :
    tower.BinaryField64.Insts.CoreOpsArithNegBinaryField64.neg a ⦃ r => towerOf 6 r = -towerOf 6 a ⦄ :=
  WP.spec_mono (Proofs.Binary.bf64_neg_spec a) fun _ h => Proofs.Binary.towerOf_neg h

/-- `from_repr` keeps the low `2^6` bits of its argument. -/
theorem tower.BinaryField64.from_repr.towerOf (r : Std.U64) :
    tower.BinaryField64.from_repr r ⦃ x => x.val < 2 ^ 2 ^ 6 ∧ towerOf 6 x = towerOf 6 r ⦄ :=
  WP.spec_mono (Proofs.Binary.bf64_from_repr_spec r) fun _ h =>
    ⟨h ▸ Nat.mod_lt _ (by positivity), Proofs.Binary.towerOf_mod h⟩

/-- `mul_alpha` multiplies by the level's generator `Z 6`. -/
theorem tower.BinaryField64.mul_alpha.towerOf (x : tower.BinaryField64) :
    tower.BinaryField64.mul_alpha x ⦃ y => towerOf 6 y = towerOf 6 x * Z 6 ⦄ :=
  WP.spec_mono (Proofs.Binary.bf64_mul_alpha_spec x) fun _ h => Proofs.Binary.towerOf_mul_Z h

/-! ### `GF(2^128)`, `BinaryField128` -/

theorem tower.BinaryField128.Insts.CoreOpsArithAddBinaryField128BinaryField128.add.towerOf (a b : tower.BinaryField128) :
    tower.BinaryField128.Insts.CoreOpsArithAddBinaryField128BinaryField128.add a b ⦃ r => towerOf 7 r = towerOf 7 a + towerOf 7 b ⦄ :=
  WP.spec_mono (Proofs.Binary.bf128_add_spec a b) fun _ h => Proofs.Binary.towerOf_add h

theorem tower.BinaryField128.Insts.CoreOpsArithSubBinaryField128BinaryField128.sub.towerOf (a b : tower.BinaryField128) :
    tower.BinaryField128.Insts.CoreOpsArithSubBinaryField128BinaryField128.sub a b ⦃ r => towerOf 7 r = towerOf 7 a - towerOf 7 b ⦄ :=
  WP.spec_mono (Proofs.Binary.bf128_sub_spec a b) fun _ h => Proofs.Binary.towerOf_sub h

theorem tower.BinaryField128.Insts.CoreOpsArithMulBinaryField128BinaryField128.mul.towerOf (a b : tower.BinaryField128) :
    tower.BinaryField128.Insts.CoreOpsArithMulBinaryField128BinaryField128.mul a b ⦃ r => towerOf 7 r = towerOf 7 a * towerOf 7 b ⦄ :=
  WP.spec_mono (Proofs.Binary.bf128_mul_spec a b) fun _ h => Proofs.Binary.towerOf_mul h

theorem tower.BinaryField128.Insts.CoreOpsArithNegBinaryField128.neg.towerOf (a : tower.BinaryField128) :
    tower.BinaryField128.Insts.CoreOpsArithNegBinaryField128.neg a ⦃ r => towerOf 7 r = -towerOf 7 a ⦄ :=
  WP.spec_mono (Proofs.Binary.bf128_neg_spec a) fun _ h => Proofs.Binary.towerOf_neg h


/-! ### Squaring at every level -/

/-- `square` is squaring in level `0` of the tower. -/
theorem gf2.Gf2.Insts.P3_fieldFieldPrimeCharacteristicRing.square.towerOf (a : gf2.Gf2) :
    gf2.Gf2.Insts.P3_fieldFieldPrimeCharacteristicRing.square a ⦃ r =>
      towerOf 0 r = towerOf 0 a * towerOf 0 a ⦄ :=
  WP.spec_mono (Proofs.Binary.gf2_square_spec a) fun _ h => Proofs.Binary.towerOf_mul h

/-- `square` is squaring in level `1` of the tower. -/
theorem tower.BinaryField2.Insts.P3_fieldFieldPrimeCharacteristicRing.square.towerOf (a : tower.BinaryField2) :
    tower.BinaryField2.Insts.P3_fieldFieldPrimeCharacteristicRing.square a ⦃ r =>
      towerOf 1 r = towerOf 1 a * towerOf 1 a ⦄ :=
  WP.spec_mono (Proofs.Binary.bf2_square_spec a) fun _ h => Proofs.Binary.towerOf_mul h

/-- `square` is squaring in level `2` of the tower. -/
theorem tower.BinaryField4.Insts.P3_fieldFieldPrimeCharacteristicRing.square.towerOf (a : tower.BinaryField4) :
    tower.BinaryField4.Insts.P3_fieldFieldPrimeCharacteristicRing.square a ⦃ r =>
      towerOf 2 r = towerOf 2 a * towerOf 2 a ⦄ :=
  WP.spec_mono (Proofs.Binary.bf4_square_spec a) fun _ h => Proofs.Binary.towerOf_mul h

/-- `square` is squaring in level `3` of the tower. -/
theorem tower.BinaryField8.Insts.P3_fieldFieldPrimeCharacteristicRing.square.towerOf (a : tower.BinaryField8) :
    tower.BinaryField8.Insts.P3_fieldFieldPrimeCharacteristicRing.square a ⦃ r =>
      towerOf 3 r = towerOf 3 a * towerOf 3 a ⦄ :=
  WP.spec_mono (Proofs.Binary.bf8_square_spec a) fun _ h => Proofs.Binary.towerOf_mul h

/-- `square` is squaring in level `4` of the tower. -/
theorem tower.BinaryField16.Insts.P3_fieldFieldPrimeCharacteristicRing.square.towerOf (a : tower.BinaryField16) :
    tower.BinaryField16.Insts.P3_fieldFieldPrimeCharacteristicRing.square a ⦃ r =>
      towerOf 4 r = towerOf 4 a * towerOf 4 a ⦄ :=
  WP.spec_mono (Proofs.Binary.bf16_square_spec a) fun _ h => Proofs.Binary.towerOf_mul h

/-- `square` is squaring in level `5` of the tower. -/
theorem tower.BinaryField32.Insts.P3_fieldFieldPrimeCharacteristicRing.square.towerOf (a : tower.BinaryField32) :
    tower.BinaryField32.Insts.P3_fieldFieldPrimeCharacteristicRing.square a ⦃ r =>
      towerOf 5 r = towerOf 5 a * towerOf 5 a ⦄ :=
  WP.spec_mono (Proofs.Binary.bf32_square_spec a) fun _ h => Proofs.Binary.towerOf_mul h

/-- `square` is squaring in level `6` of the tower. -/
theorem tower.BinaryField64.Insts.P3_fieldFieldPrimeCharacteristicRing.square.towerOf (a : tower.BinaryField64) :
    tower.BinaryField64.Insts.P3_fieldFieldPrimeCharacteristicRing.square a ⦃ r =>
      towerOf 6 r = towerOf 6 a * towerOf 6 a ⦄ :=
  WP.spec_mono (Proofs.Binary.bf64_square_spec a) fun _ h => Proofs.Binary.towerOf_mul h

/-- `square` is squaring in level `7` of the tower. -/
theorem tower.BinaryField128.Insts.P3_fieldFieldPrimeCharacteristicRing.square.towerOf (a : tower.BinaryField128) :
    tower.BinaryField128.Insts.P3_fieldFieldPrimeCharacteristicRing.square a ⦃ r =>
      towerOf 7 r = towerOf 7 a * towerOf 7 a ⦄ :=
  WP.spec_mono (Proofs.Binary.bf128_square_spec a) fun _ h => Proofs.Binary.towerOf_mul h
/-! ### Inversion at every level

`GF(2)`, `GF(2^2)` and `GF(2^4)` are stored in a `u8`, and the claims there assume the value is
canonical: it fits in `2^k` bits. Every constructor, deserializer and operation of the crate keeps
it so. Every result below is canonical too. -/

/-- `try_inverse` is inversion in level `0` of the tower: `None` exactly for zero. -/
theorem gf2.Gf2.Insts.P3_fieldFieldField.try_inverse.towerOf (a : gf2.Gf2) (hA : a.val < 2 ^ 2 ^ 0) :
    gf2.Gf2.Insts.P3_fieldFieldField.try_inverse a ⦃ r =>
      (towerOf 0 a = 0 → r = .None) ∧
        (towerOf 0 a ≠ 0 → ∃ c, r = .Some c ∧ c.val < 2 ^ 2 ^ 0 ∧
          towerOf 0 c = (towerOf 0 a)⁻¹) ⦄ :=
  Proofs.Binary.gf2_try_inverse_spec a hA

/-- `try_inverse` is inversion in level `1` of the tower: `None` exactly for zero. -/
theorem tower.BinaryField2.Insts.P3_fieldFieldField.try_inverse.towerOf (a : tower.BinaryField2) (hA : a.val < 2 ^ 2 ^ 1) :
    tower.BinaryField2.Insts.P3_fieldFieldField.try_inverse a ⦃ r =>
      (towerOf 1 a = 0 → r = .None) ∧
        (towerOf 1 a ≠ 0 → ∃ c, r = .Some c ∧ c.val < 2 ^ 2 ^ 1 ∧
          towerOf 1 c = (towerOf 1 a)⁻¹) ⦄ :=
  Proofs.Binary.bf2_try_inverse_spec a hA

/-- `try_inverse` is inversion in level `2` of the tower: `None` exactly for zero. -/
theorem tower.BinaryField4.Insts.P3_fieldFieldField.try_inverse.towerOf (a : tower.BinaryField4) (hA : a.val < 2 ^ 2 ^ 2) :
    tower.BinaryField4.Insts.P3_fieldFieldField.try_inverse a ⦃ r =>
      (towerOf 2 a = 0 → r = .None) ∧
        (towerOf 2 a ≠ 0 → ∃ c, r = .Some c ∧ c.val < 2 ^ 2 ^ 2 ∧
          towerOf 2 c = (towerOf 2 a)⁻¹) ⦄ :=
  Proofs.Binary.bf4_try_inverse_spec a hA

/-- `try_inverse` is inversion in level `3` of the tower: `None` exactly for zero. -/
theorem tower.BinaryField8.Insts.P3_fieldFieldField.try_inverse.towerOf (a : tower.BinaryField8) :
    tower.BinaryField8.Insts.P3_fieldFieldField.try_inverse a ⦃ r =>
      (towerOf 3 a = 0 → r = .None) ∧
        (towerOf 3 a ≠ 0 → ∃ c, r = .Some c ∧ c.val < 2 ^ 2 ^ 3 ∧
          towerOf 3 c = (towerOf 3 a)⁻¹) ⦄ :=
  Proofs.Binary.bf8_try_inverse_spec a

/-- `try_inverse` is inversion in level `4` of the tower: `None` exactly for zero. -/
theorem tower.BinaryField16.Insts.P3_fieldFieldField.try_inverse.towerOf (a : tower.BinaryField16) :
    tower.BinaryField16.Insts.P3_fieldFieldField.try_inverse a ⦃ r =>
      (towerOf 4 a = 0 → r = .None) ∧
        (towerOf 4 a ≠ 0 → ∃ c, r = .Some c ∧ c.val < 2 ^ 2 ^ 4 ∧
          towerOf 4 c = (towerOf 4 a)⁻¹) ⦄ :=
  Proofs.Binary.bf16_try_inverse_spec a

/-- `try_inverse` is inversion in level `5` of the tower: `None` exactly for zero. -/
theorem tower.BinaryField32.Insts.P3_fieldFieldField.try_inverse.towerOf (a : tower.BinaryField32) :
    tower.BinaryField32.Insts.P3_fieldFieldField.try_inverse a ⦃ r =>
      (towerOf 5 a = 0 → r = .None) ∧
        (towerOf 5 a ≠ 0 → ∃ c, r = .Some c ∧ c.val < 2 ^ 2 ^ 5 ∧
          towerOf 5 c = (towerOf 5 a)⁻¹) ⦄ :=
  Proofs.Binary.bf32_try_inverse_spec a

/-- `try_inverse` is inversion in level `6` of the tower: `None` exactly for zero. -/
theorem tower.BinaryField64.Insts.P3_fieldFieldField.try_inverse.towerOf (a : tower.BinaryField64) :
    tower.BinaryField64.Insts.P3_fieldFieldField.try_inverse a ⦃ r =>
      (towerOf 6 a = 0 → r = .None) ∧
        (towerOf 6 a ≠ 0 → ∃ c, r = .Some c ∧ c.val < 2 ^ 2 ^ 6 ∧
          towerOf 6 c = (towerOf 6 a)⁻¹) ⦄ :=
  Proofs.Binary.bf64_try_inverse_spec a

/-- `try_inverse` is inversion in level `7` of the tower: `None` exactly for zero. -/
theorem tower.BinaryField128.Insts.P3_fieldFieldField.try_inverse.towerOf (a : tower.BinaryField128) :
    tower.BinaryField128.Insts.P3_fieldFieldField.try_inverse a ⦃ r =>
      (towerOf 7 a = 0 → r = .None) ∧
        (towerOf 7 a ≠ 0 → ∃ c, r = .Some c ∧ c.val < 2 ^ 2 ^ 7 ∧
          towerOf 7 c = (towerOf 7 a)⁻¹) ⦄ :=
  Proofs.Binary.bf128_try_inverse_spec a

/-! ### Square roots at every level

Every element has a square root. Below `GF(2^16)`, `try_sqrt` computes it as `a^(2^(BITS - 1))`
with `exp_power_of_2`. -/

/-- `try_sqrt` returns a square root in level `0` of the tower. -/
theorem gf2.Gf2.Insts.P3_fieldFieldField.try_sqrt.towerOf (a : gf2.Gf2) (hA : a.val < 2 ^ 2 ^ 0) :
    gf2.Gf2.Insts.P3_fieldFieldField.try_sqrt a ⦃ r =>
      ∃ c, r = .Some c ∧ c.val < 2 ^ 2 ^ 0 ∧ towerOf 0 c * towerOf 0 c = towerOf 0 a ⦄ :=
  Proofs.Binary.gf2_try_sqrt_spec a hA

/-- `try_sqrt` returns a square root in level `1` of the tower. -/
theorem tower.BinaryField2.Insts.P3_fieldFieldField.try_sqrt.towerOf (a : tower.BinaryField2) (hA : a.val < 2 ^ 2 ^ 1) :
    tower.BinaryField2.Insts.P3_fieldFieldField.try_sqrt a ⦃ r =>
      ∃ c, r = .Some c ∧ c.val < 2 ^ 2 ^ 1 ∧ towerOf 1 c * towerOf 1 c = towerOf 1 a ⦄ :=
  Proofs.Binary.bf2_try_sqrt_spec a hA

/-- `try_sqrt` returns a square root in level `2` of the tower. -/
theorem tower.BinaryField4.Insts.P3_fieldFieldField.try_sqrt.towerOf (a : tower.BinaryField4) (hA : a.val < 2 ^ 2 ^ 2) :
    tower.BinaryField4.Insts.P3_fieldFieldField.try_sqrt a ⦃ r =>
      ∃ c, r = .Some c ∧ c.val < 2 ^ 2 ^ 2 ∧ towerOf 2 c * towerOf 2 c = towerOf 2 a ⦄ :=
  Proofs.Binary.bf4_try_sqrt_spec a hA

/-- `try_sqrt` returns a square root in level `3` of the tower. -/
theorem tower.BinaryField8.Insts.P3_fieldFieldField.try_sqrt.towerOf (a : tower.BinaryField8) :
    tower.BinaryField8.Insts.P3_fieldFieldField.try_sqrt a ⦃ r =>
      ∃ c, r = .Some c ∧ c.val < 2 ^ 2 ^ 3 ∧ towerOf 3 c * towerOf 3 c = towerOf 3 a ⦄ :=
  Proofs.Binary.bf8_try_sqrt_spec a

/-- `try_sqrt` returns a square root in level `4` of the tower. -/
theorem tower.BinaryField16.Insts.P3_fieldFieldField.try_sqrt.towerOf (a : tower.BinaryField16) :
    tower.BinaryField16.Insts.P3_fieldFieldField.try_sqrt a ⦃ r =>
      ∃ c, r = .Some c ∧ c.val < 2 ^ 2 ^ 4 ∧ towerOf 4 c * towerOf 4 c = towerOf 4 a ⦄ :=
  Proofs.Binary.bf16_try_sqrt_spec a

/-- `try_sqrt` returns a square root in level `5` of the tower. -/
theorem tower.BinaryField32.Insts.P3_fieldFieldField.try_sqrt.towerOf (a : tower.BinaryField32) :
    tower.BinaryField32.Insts.P3_fieldFieldField.try_sqrt a ⦃ r =>
      ∃ c, r = .Some c ∧ c.val < 2 ^ 2 ^ 5 ∧ towerOf 5 c * towerOf 5 c = towerOf 5 a ⦄ :=
  Proofs.Binary.bf32_try_sqrt_spec a

/-- `try_sqrt` returns a square root in level `6` of the tower. -/
theorem tower.BinaryField64.Insts.P3_fieldFieldField.try_sqrt.towerOf (a : tower.BinaryField64) :
    tower.BinaryField64.Insts.P3_fieldFieldField.try_sqrt a ⦃ r =>
      ∃ c, r = .Some c ∧ c.val < 2 ^ 2 ^ 6 ∧ towerOf 6 c * towerOf 6 c = towerOf 6 a ⦄ :=
  Proofs.Binary.bf64_try_sqrt_spec a

/-- `try_sqrt` returns a square root in level `7` of the tower. -/
theorem tower.BinaryField128.Insts.P3_fieldFieldField.try_sqrt.towerOf (a : tower.BinaryField128) :
    tower.BinaryField128.Insts.P3_fieldFieldField.try_sqrt a ⦃ r =>
      ∃ c, r = .Some c ∧ c.val < 2 ^ 2 ^ 7 ∧ towerOf 7 c * towerOf 7 c = towerOf 7 a ⦄ :=
  Proofs.Binary.bf128_try_sqrt_spec a

/-! ### Powers `x^(2^n)` below `GF(2^16)` -/

/-- `exp_power_of_2 a n` is `a^(2^n)` in level `1` of the tower. -/
theorem tower.BinaryField2.Insts.P3_fieldFieldPrimeCharacteristicRing.exp_power_of_2.towerOf (a : tower.BinaryField2) (hA : a.val < 2 ^ 2 ^ 1) (n : Std.Usize) :
    tower.BinaryField2.Insts.P3_fieldFieldPrimeCharacteristicRing.exp_power_of_2 a n ⦃ r =>
      r.val < 2 ^ 2 ^ 1 ∧ towerOf 1 r = towerOf 1 a ^ 2 ^ n.val ⦄ :=
  Proofs.Binary.bf2_exp_power_of_2_spec a hA n

/-- `exp_power_of_2 a n` is `a^(2^n)` in level `2` of the tower. -/
theorem tower.BinaryField4.Insts.P3_fieldFieldPrimeCharacteristicRing.exp_power_of_2.towerOf (a : tower.BinaryField4) (hA : a.val < 2 ^ 2 ^ 2) (n : Std.Usize) :
    tower.BinaryField4.Insts.P3_fieldFieldPrimeCharacteristicRing.exp_power_of_2 a n ⦃ r =>
      r.val < 2 ^ 2 ^ 2 ∧ towerOf 2 r = towerOf 2 a ^ 2 ^ n.val ⦄ :=
  Proofs.Binary.bf4_exp_power_of_2_spec a hA n

/-- `exp_power_of_2 a n` is `a^(2^n)` in level `3` of the tower. -/
theorem tower.BinaryField8.Insts.P3_fieldFieldPrimeCharacteristicRing.exp_power_of_2.towerOf (a : tower.BinaryField8) (n : Std.Usize) :
    tower.BinaryField8.Insts.P3_fieldFieldPrimeCharacteristicRing.exp_power_of_2 a n ⦃ r =>
      r.val < 2 ^ 2 ^ 3 ∧ towerOf 3 r = towerOf 3 a ^ 2 ^ n.val ⦄ :=
  Proofs.Binary.bf8_exp_power_of_2_spec a n

/-! ### The rest of the field API -/

/-- The value `inverse` returns. -/
theorem field_defaults.BinaryField16.inverse.towerOf (a : tower.BinaryField16) (ha : Spec.BinaryField.towerOf 4 a ≠ 0) :
    field_defaults.BinaryField16.inverse a ⦃ c =>
      c.val < 2 ^ 2 ^ 4 ∧ towerOf 4 c = (towerOf 4 a)⁻¹ ⦄ :=
  Proofs.Binary.bf16_inverse_spec a ha

/-- `inverse` panics. -/
theorem field_defaults.BinaryField16.inverse.panics (a : tower.BinaryField16) (ha : Spec.BinaryField.towerOf 4 a = 0) :
    field_defaults.BinaryField16.inverse a = .fail .panic :=
  Proofs.Binary.bf16_inverse_zero a ha

/-- The value `div` returns. -/
theorem tower.BinaryField16.Insts.CoreOpsArithDivBinaryField16BinaryField16.div.towerOf (a b : tower.BinaryField16) (hb : Spec.BinaryField.towerOf 4 b ≠ 0) :
    tower.BinaryField16.Insts.CoreOpsArithDivBinaryField16BinaryField16.div a b ⦃ r =>
      r.val < 2 ^ 2 ^ 4 ∧ towerOf 4 r = towerOf 4 a / towerOf 4 b ⦄ :=
  Proofs.Binary.bf16_div_spec a b hb

/-- `div` panics. -/
theorem tower.BinaryField16.Insts.CoreOpsArithDivBinaryField16BinaryField16.div.panics (a b : tower.BinaryField16) (hb : Spec.BinaryField.towerOf 4 b = 0) :
    tower.BinaryField16.Insts.CoreOpsArithDivBinaryField16BinaryField16.div a b = .fail .panic :=
  Proofs.Binary.bf16_div_zero a b hb

/-- The value `mul_assign` returns. -/
theorem tower.BinaryField16.Insts.CoreOpsArithMulAssign.mul_assign.towerOf (a b : tower.BinaryField16) :
    tower.BinaryField16.Insts.CoreOpsArithMulAssign.mul_assign
      (core.convert.Into.Blanket (core.convert.From.Blanket tower.BinaryField16)) a b ⦃ r =>
      towerOf 4 r = towerOf 4 a * towerOf 4 b ⦄ :=
  Proofs.Binary.bf16_mul_assign_spec a b

/-- The value `add_assign` returns. -/
theorem tower.BinaryField16.Insts.CoreOpsArithAddAssign.add_assign.towerOf (a b : tower.BinaryField16) :
    tower.BinaryField16.Insts.CoreOpsArithAddAssign.add_assign
      (core.convert.Into.Blanket (core.convert.From.Blanket tower.BinaryField16)) a b ⦃ r =>
      towerOf 4 r = towerOf 4 a + towerOf 4 b ⦄ :=
  Proofs.Binary.bf16_add_assign_spec a b

/-- The value `sub_assign` returns. -/
theorem tower.BinaryField16.Insts.CoreOpsArithSubAssign.sub_assign.towerOf (a b : tower.BinaryField16) :
    tower.BinaryField16.Insts.CoreOpsArithSubAssign.sub_assign
      (core.convert.Into.Blanket (core.convert.From.Blanket tower.BinaryField16)) a b ⦃ r =>
      towerOf 4 r = towerOf 4 a - towerOf 4 b ⦄ :=
  Proofs.Binary.bf16_sub_assign_spec a b

/-- The value `div_assign` returns. -/
theorem tower.BinaryField16.Insts.CoreOpsArithDivAssignBinaryField16.div_assign.towerOf (a b : tower.BinaryField16) (hb : Spec.BinaryField.towerOf 4 b ≠ 0) :
    tower.BinaryField16.Insts.CoreOpsArithDivAssignBinaryField16.div_assign a b ⦃ r =>
      towerOf 4 r = towerOf 4 a / towerOf 4 b ⦄ :=
  Proofs.Binary.bf16_div_assign_spec a b hb

/-- The value `eq` returns. -/
theorem tower.BinaryField16.Insts.CoreCmpPartialEqBinaryField16.eq.towerOf (a b : tower.BinaryField16) :
    tower.BinaryField16.Insts.CoreCmpPartialEqBinaryField16.eq a b ⦃ r =>
      (r = true ↔ towerOf 4 a = towerOf 4 b) ⦄ :=
  Proofs.Binary.bf16_eq_spec a b

/-- The value `bool_check` returns. -/
theorem tower.BinaryField16.Insts.P3_fieldFieldPrimeCharacteristicRing.bool_check.towerOf (a : tower.BinaryField16) :
    tower.BinaryField16.Insts.P3_fieldFieldPrimeCharacteristicRing.bool_check a ⦃ r =>
      towerOf 4 r = towerOf 4 a * towerOf 4 a + towerOf 4 a ⦄ :=
  Proofs.Binary.bf16_bool_check_spec a

/-- The value `bits` returns. -/
theorem tower.BinaryField16.Insts.P3_fieldFieldField.bits.val :
    tower.BinaryField16.Insts.P3_fieldFieldField.bits ⦃ r => r.val = 2 ^ 4 ⦄ :=
  Proofs.Binary.bf16_bits_spec

/-- The value `from_bool` returns. -/
theorem tower.BinaryField16.Insts.P3_fieldFieldPrimeCharacteristicRing.from_bool.val (b : Bool) :
    tower.BinaryField16.Insts.P3_fieldFieldPrimeCharacteristicRing.from_bool b ⦃ r =>
      r.val = b.toNat ⦄ :=
  Proofs.Binary.bf16_from_bool_spec b

/-- The value `interpolation_node` returns. -/
theorem tower.BinaryField16.Insts.P3_fieldFieldField.interpolation_node.val (i : Std.Usize) (hi : i.val < 2 ^ 2 ^ 4) :
    tower.BinaryField16.Insts.P3_fieldFieldField.interpolation_node i ⦃ r => r.val = i.val ⦄ :=
  Proofs.Binary.bf16_interpolation_node_spec i hi

/-- `interpolation_node` panics. -/
theorem tower.BinaryField16.Insts.P3_fieldFieldField.interpolation_node.panics (i : Std.Usize) (hi : 2 ^ 2 ^ 4 ≤ i.val) :
    tower.BinaryField16.Insts.P3_fieldFieldField.interpolation_node i = .fail .panic :=
  Proofs.Binary.bf16_interpolation_node_fail i hi

/-- The value `inverse` returns. -/
theorem field_defaults.Gf2.inverse.towerOf (a : gf2.Gf2) (hA : a.val < 2 ^ 2 ^ 0) (ha : Spec.BinaryField.towerOf 0 a ≠ 0) :
    field_defaults.Gf2.inverse a ⦃ c =>
      c.val < 2 ^ 2 ^ 0 ∧ towerOf 0 c = (towerOf 0 a)⁻¹ ⦄ :=
  Proofs.Binary.gf2_inverse_spec a hA ha

/-- `inverse` panics. -/
theorem field_defaults.Gf2.inverse.panics (a : gf2.Gf2) (hA : a.val < 2 ^ 2 ^ 0) (ha : Spec.BinaryField.towerOf 0 a = 0) :
    field_defaults.Gf2.inverse a = .fail .panic :=
  Proofs.Binary.gf2_inverse_zero a hA ha

/-- The value `div` returns. -/
theorem gf2.Gf2.Insts.CoreOpsArithDivGf2Gf2.div.towerOf (a b : gf2.Gf2) (hA : a.val < 2 ^ 2 ^ 0) (hB : b.val < 2 ^ 2 ^ 0) (hb : Spec.BinaryField.towerOf 0 b ≠ 0) :
    gf2.Gf2.Insts.CoreOpsArithDivGf2Gf2.div a b ⦃ r =>
      r.val < 2 ^ 2 ^ 0 ∧ towerOf 0 r = towerOf 0 a / towerOf 0 b ⦄ :=
  Proofs.Binary.gf2_div_spec a b hA hB hb

/-- `div` panics. -/
theorem gf2.Gf2.Insts.CoreOpsArithDivGf2Gf2.div.panics (a b : gf2.Gf2) (hB : b.val < 2 ^ 2 ^ 0) (hb : Spec.BinaryField.towerOf 0 b = 0) :
    gf2.Gf2.Insts.CoreOpsArithDivGf2Gf2.div a b = .fail .panic :=
  Proofs.Binary.gf2_div_zero a b hB hb

/-- The value `mul_assign` returns. -/
theorem gf2.Gf2.Insts.CoreOpsArithMulAssign.mul_assign.towerOf (a b : gf2.Gf2) :
    gf2.Gf2.Insts.CoreOpsArithMulAssign.mul_assign
      (core.convert.Into.Blanket (core.convert.From.Blanket gf2.Gf2)) a b ⦃ r =>
      towerOf 0 r = towerOf 0 a * towerOf 0 b ⦄ :=
  Proofs.Binary.gf2_mul_assign_spec a b

/-- The value `add_assign` returns. -/
theorem gf2.Gf2.Insts.CoreOpsArithAddAssign.add_assign.towerOf (a b : gf2.Gf2) :
    gf2.Gf2.Insts.CoreOpsArithAddAssign.add_assign
      (core.convert.Into.Blanket (core.convert.From.Blanket gf2.Gf2)) a b ⦃ r =>
      towerOf 0 r = towerOf 0 a + towerOf 0 b ⦄ :=
  Proofs.Binary.gf2_add_assign_spec a b

/-- The value `sub_assign` returns. -/
theorem gf2.Gf2.Insts.CoreOpsArithSubAssign.sub_assign.towerOf (a b : gf2.Gf2) :
    gf2.Gf2.Insts.CoreOpsArithSubAssign.sub_assign
      (core.convert.Into.Blanket (core.convert.From.Blanket gf2.Gf2)) a b ⦃ r =>
      towerOf 0 r = towerOf 0 a - towerOf 0 b ⦄ :=
  Proofs.Binary.gf2_sub_assign_spec a b

/-- The value `div_assign` returns. -/
theorem gf2.Gf2.Insts.CoreOpsArithDivAssignGf2.div_assign.towerOf (a b : gf2.Gf2) (hB : b.val < 2 ^ 2 ^ 0) (hb : Spec.BinaryField.towerOf 0 b ≠ 0) :
    gf2.Gf2.Insts.CoreOpsArithDivAssignGf2.div_assign a b ⦃ r =>
      towerOf 0 r = towerOf 0 a / towerOf 0 b ⦄ :=
  Proofs.Binary.gf2_div_assign_spec a b hB hb

/-- The value `eq` returns. -/
theorem gf2.Gf2.Insts.CoreCmpPartialEqGf2.eq.towerOf (a b : gf2.Gf2) (hA : a.val < 2 ^ 2 ^ 0) (hB : b.val < 2 ^ 2 ^ 0) :
    gf2.Gf2.Insts.CoreCmpPartialEqGf2.eq a b ⦃ r =>
      (r = true ↔ towerOf 0 a = towerOf 0 b) ⦄ :=
  Proofs.Binary.gf2_eq_spec a b hA hB

/-- The value `bits` returns. -/
theorem gf2.Gf2.Insts.P3_fieldFieldField.bits.val :
    gf2.Gf2.Insts.P3_fieldFieldField.bits ⦃ r => r.val = 2 ^ 0 ⦄ :=
  Proofs.Binary.gf2_bits_spec

/-- The value `from_bool` returns. -/
theorem gf2.Gf2.Insts.P3_fieldFieldPrimeCharacteristicRing.from_bool.val (b : Bool) :
    gf2.Gf2.Insts.P3_fieldFieldPrimeCharacteristicRing.from_bool b ⦃ r => r.val = b.toNat ⦄ :=
  Proofs.Binary.gf2_from_bool_spec b

/-- The value `new` returns. -/
theorem gf2.Gf2.new.val (bit : Std.U8) :
    gf2.Gf2.new bit ⦃ r => r.val = bit.val % 2 ⦄ :=
  Proofs.Binary.gf2_new_spec bit

/-- The value `interpolation_node` returns. -/
theorem gf2.Gf2.Insts.P3_fieldFieldField.interpolation_node.val (i : Std.Usize) (hi : i.val < 2) :
    gf2.Gf2.Insts.P3_fieldFieldField.interpolation_node i ⦃ r => r.val = i.val ⦄ :=
  Proofs.Binary.gf2_interpolation_node_spec i hi

/-- `interpolation_node` panics. -/
theorem gf2.Gf2.Insts.P3_fieldFieldField.interpolation_node.panics (i : Std.Usize) (hi : 2 ≤ i.val) :
    gf2.Gf2.Insts.P3_fieldFieldField.interpolation_node i = .fail .panic :=
  Proofs.Binary.gf2_interpolation_node_fail i hi

/-- `halve` panics. -/
theorem gf2.Gf2.Insts.P3_fieldFieldPrimeCharacteristicRing.halve.panics (a : gf2.Gf2) :
    gf2.Gf2.Insts.P3_fieldFieldPrimeCharacteristicRing.halve a = .fail .panic :=
  Proofs.Binary.gf2_halve_fail a

/-- `div_2exp_u64` panics. -/
theorem gf2.Gf2.Insts.P3_fieldFieldPrimeCharacteristicRing.div_2exp_u64.panics (a : gf2.Gf2) (e : Std.U64) :
    gf2.Gf2.Insts.P3_fieldFieldPrimeCharacteristicRing.div_2exp_u64 a e = .fail .panic :=
  Proofs.Binary.gf2_div_2exp_u64_fail a e

/-- The value `double` returns. -/
theorem gf2.Gf2.Insts.P3_fieldFieldPrimeCharacteristicRing.double.towerOf (a : gf2.Gf2) :
    gf2.Gf2.Insts.P3_fieldFieldPrimeCharacteristicRing.double a ⦃ r =>
      towerOf 0 r = towerOf 0 a + towerOf 0 a ⦄ :=
  Proofs.Binary.gf2_double_spec a

/-- The value `mul_2exp_u64` returns. -/
theorem gf2.Gf2.Insts.P3_fieldFieldPrimeCharacteristicRing.mul_2exp_u64.towerOf (a : gf2.Gf2) (e : Std.U64) :
    gf2.Gf2.Insts.P3_fieldFieldPrimeCharacteristicRing.mul_2exp_u64 a e ⦃ r =>
      towerOf 0 r = towerOf 0 a * 2 ^ e.val ⦄ :=
  Proofs.Binary.gf2_mul_2exp_u64_spec a e

/-- The value `xor` returns. -/
theorem gf2.Gf2.Insts.P3_fieldFieldPrimeCharacteristicRing.xor.towerOf (a b : gf2.Gf2) :
    gf2.Gf2.Insts.P3_fieldFieldPrimeCharacteristicRing.xor a b ⦃ r =>
      towerOf 0 r = towerOf 0 a + towerOf 0 b ⦄ :=
  Proofs.Binary.gf2_xor_spec a b

/-- The value `from_int` returns. -/
theorem gf2.Gf2.Insts.P3_fieldIntegersQuotientMapU8.from_int.val (n : Std.U8) :
    gf2.Gf2.Insts.P3_fieldIntegersQuotientMapU8.from_int n ⦃ r => r.val = n.val % 2 ⦄ :=
  Proofs.Binary.gf2_from_int_u8_spec n

/-- The value `from_int` returns. -/
theorem gf2.Gf2.Insts.P3_fieldIntegersQuotientMapI8.from_int.val (n : Std.I8) :
    gf2.Gf2.Insts.P3_fieldIntegersQuotientMapI8.from_int n ⦃ r => (r.val : ℤ) = n.val % 2 ⦄ :=
  Proofs.Binary.gf2_from_int_i8_spec n

/-- The value `as_canonical_u64` returns. -/
theorem gf2.Gf2.Insts.P3_fieldFieldPrimeField64.as_canonical_u64.val (a : gf2.Gf2) :
    gf2.Gf2.Insts.P3_fieldFieldPrimeField64.as_canonical_u64 a ⦃ r => r.val = a.val ⦄ :=
  Proofs.Binary.gf2_as_canonical_u64_spec a

/-- The value `as_canonical_u32` returns. -/
theorem gf2.Gf2.Insts.P3_fieldFieldPrimeField32.as_canonical_u32.val (a : gf2.Gf2) :
    gf2.Gf2.Insts.P3_fieldFieldPrimeField32.as_canonical_u32 a ⦃ r => r.val = a.val ⦄ :=
  Proofs.Binary.gf2_as_canonical_u32_spec a

/-- The value `from_canonical_checked` returns. -/
theorem gf2.Gf2.Insts.P3_fieldIntegersQuotientMapU8.from_canonical_checked.val (n : Std.U8) :
    gf2.Gf2.Insts.P3_fieldIntegersQuotientMapU8.from_canonical_checked n ⦃ r =>
      (n.val < 2 → ∃ c, r = .Some c ∧ c.val = n.val) ∧ (2 ≤ n.val → r = .None) ⦄ :=
  Proofs.Binary.gf2_from_canonical_checked_u8_spec n

/-- The value `from_canonical_checked` returns. -/
theorem gf2.Gf2.Insts.P3_fieldIntegersQuotientMapI8.from_canonical_checked.val (n : Std.I8) :
    gf2.Gf2.Insts.P3_fieldIntegersQuotientMapI8.from_canonical_checked n ⦃ r =>
      ((0 ≤ n.val ∧ n.val < 2) → ∃ c, r = .Some c ∧ (c.val : ℤ) = n.val) ∧
        (¬ (0 ≤ n.val ∧ n.val < 2) → r = .None) ⦄ :=
  Proofs.Binary.gf2_from_canonical_checked_i8_spec n

/-- The value `inverse` returns. -/
theorem field_defaults.BinaryField2.inverse.towerOf (a : tower.BinaryField2) (hA : a.val < 2 ^ 2 ^ 1) (ha : Spec.BinaryField.towerOf 1 a ≠ 0) :
    field_defaults.BinaryField2.inverse a ⦃ c =>
      c.val < 2 ^ 2 ^ 1 ∧ towerOf 1 c = (towerOf 1 a)⁻¹ ⦄ :=
  Proofs.Binary.bf2_inverse_spec a hA ha

/-- `inverse` panics. -/
theorem field_defaults.BinaryField2.inverse.panics (a : tower.BinaryField2) (hA : a.val < 2 ^ 2 ^ 1) (ha : Spec.BinaryField.towerOf 1 a = 0) :
    field_defaults.BinaryField2.inverse a = .fail .panic :=
  Proofs.Binary.bf2_inverse_zero a hA ha

/-- The value `div` returns. -/
theorem tower.BinaryField2.Insts.CoreOpsArithDivBinaryField2BinaryField2.div.towerOf (a b : tower.BinaryField2) (hA : a.val < 2 ^ 2 ^ 1) (hB : b.val < 2 ^ 2 ^ 1) (hb : Spec.BinaryField.towerOf 1 b ≠ 0) :
    tower.BinaryField2.Insts.CoreOpsArithDivBinaryField2BinaryField2.div a b ⦃ r =>
      r.val < 2 ^ 2 ^ 1 ∧ towerOf 1 r = towerOf 1 a / towerOf 1 b ⦄ :=
  Proofs.Binary.bf2_div_spec a b hA hB hb

/-- `div` panics. -/
theorem tower.BinaryField2.Insts.CoreOpsArithDivBinaryField2BinaryField2.div.panics (a b : tower.BinaryField2) (hB : b.val < 2 ^ 2 ^ 1) (hb : Spec.BinaryField.towerOf 1 b = 0) :
    tower.BinaryField2.Insts.CoreOpsArithDivBinaryField2BinaryField2.div a b = .fail .panic :=
  Proofs.Binary.bf2_div_zero a b hB hb

/-- The value `mul_assign` returns. -/
theorem tower.BinaryField2.Insts.CoreOpsArithMulAssign.mul_assign.towerOf (a b : tower.BinaryField2) :
    tower.BinaryField2.Insts.CoreOpsArithMulAssign.mul_assign
      (core.convert.Into.Blanket (core.convert.From.Blanket tower.BinaryField2)) a b ⦃ r =>
      towerOf 1 r = towerOf 1 a * towerOf 1 b ⦄ :=
  Proofs.Binary.bf2_mul_assign_spec a b

/-- The value `add_assign` returns. -/
theorem tower.BinaryField2.Insts.CoreOpsArithAddAssign.add_assign.towerOf (a b : tower.BinaryField2) :
    tower.BinaryField2.Insts.CoreOpsArithAddAssign.add_assign
      (core.convert.Into.Blanket (core.convert.From.Blanket tower.BinaryField2)) a b ⦃ r =>
      towerOf 1 r = towerOf 1 a + towerOf 1 b ⦄ :=
  Proofs.Binary.bf2_add_assign_spec a b

/-- The value `sub_assign` returns. -/
theorem tower.BinaryField2.Insts.CoreOpsArithSubAssign.sub_assign.towerOf (a b : tower.BinaryField2) :
    tower.BinaryField2.Insts.CoreOpsArithSubAssign.sub_assign
      (core.convert.Into.Blanket (core.convert.From.Blanket tower.BinaryField2)) a b ⦃ r =>
      towerOf 1 r = towerOf 1 a - towerOf 1 b ⦄ :=
  Proofs.Binary.bf2_sub_assign_spec a b

/-- The value `div_assign` returns. -/
theorem tower.BinaryField2.Insts.CoreOpsArithDivAssignBinaryField2.div_assign.towerOf (a b : tower.BinaryField2) (hB : b.val < 2 ^ 2 ^ 1) (hb : Spec.BinaryField.towerOf 1 b ≠ 0) :
    tower.BinaryField2.Insts.CoreOpsArithDivAssignBinaryField2.div_assign a b ⦃ r =>
      towerOf 1 r = towerOf 1 a / towerOf 1 b ⦄ :=
  Proofs.Binary.bf2_div_assign_spec a b hB hb

/-- The value `eq` returns. -/
theorem tower.BinaryField2.Insts.CoreCmpPartialEqBinaryField2.eq.towerOf (a b : tower.BinaryField2) (hA : a.val < 2 ^ 2 ^ 1) (hB : b.val < 2 ^ 2 ^ 1) :
    tower.BinaryField2.Insts.CoreCmpPartialEqBinaryField2.eq a b ⦃ r =>
      (r = true ↔ towerOf 1 a = towerOf 1 b) ⦄ :=
  Proofs.Binary.bf2_eq_spec a b hA hB

/-- The value `bool_check` returns. -/
theorem tower.BinaryField2.Insts.P3_fieldFieldPrimeCharacteristicRing.bool_check.towerOf (a : tower.BinaryField2) :
    tower.BinaryField2.Insts.P3_fieldFieldPrimeCharacteristicRing.bool_check a ⦃ r =>
      towerOf 1 r = towerOf 1 a * towerOf 1 a + towerOf 1 a ⦄ :=
  Proofs.Binary.bf2_bool_check_spec a

/-- The value `bits` returns. -/
theorem tower.BinaryField2.Insts.P3_fieldFieldField.bits.val :
    tower.BinaryField2.Insts.P3_fieldFieldField.bits ⦃ r => r.val = 2 ^ 1 ⦄ :=
  Proofs.Binary.bf2_bits_spec

/-- The value `from_bool` returns. -/
theorem tower.BinaryField2.Insts.P3_fieldFieldPrimeCharacteristicRing.from_bool.val (b : Bool) :
    tower.BinaryField2.Insts.P3_fieldFieldPrimeCharacteristicRing.from_bool b ⦃ r =>
      r.val = b.toNat ⦄ :=
  Proofs.Binary.bf2_from_bool_spec b

/-- The value `interpolation_node` returns. -/
theorem tower.BinaryField2.Insts.P3_fieldFieldField.interpolation_node.val (i : Std.Usize) (hi : i.val < 2 ^ 2 ^ 1) :
    tower.BinaryField2.Insts.P3_fieldFieldField.interpolation_node i ⦃ r => r.val = i.val ⦄ :=
  Proofs.Binary.bf2_interpolation_node_spec i hi

/-- `interpolation_node` panics. -/
theorem tower.BinaryField2.Insts.P3_fieldFieldField.interpolation_node.panics (i : Std.Usize) (hi : 2 ^ 2 ^ 1 ≤ i.val) :
    tower.BinaryField2.Insts.P3_fieldFieldField.interpolation_node i = .fail .panic :=
  Proofs.Binary.bf2_interpolation_node_fail i hi

/-- The value `inverse` returns. -/
theorem field_defaults.BinaryField4.inverse.towerOf (a : tower.BinaryField4) (hA : a.val < 2 ^ 2 ^ 2) (ha : Spec.BinaryField.towerOf 2 a ≠ 0) :
    field_defaults.BinaryField4.inverse a ⦃ c =>
      c.val < 2 ^ 2 ^ 2 ∧ towerOf 2 c = (towerOf 2 a)⁻¹ ⦄ :=
  Proofs.Binary.bf4_inverse_spec a hA ha

/-- `inverse` panics. -/
theorem field_defaults.BinaryField4.inverse.panics (a : tower.BinaryField4) (hA : a.val < 2 ^ 2 ^ 2) (ha : Spec.BinaryField.towerOf 2 a = 0) :
    field_defaults.BinaryField4.inverse a = .fail .panic :=
  Proofs.Binary.bf4_inverse_zero a hA ha

/-- The value `div` returns. -/
theorem tower.BinaryField4.Insts.CoreOpsArithDivBinaryField4BinaryField4.div.towerOf (a b : tower.BinaryField4) (hA : a.val < 2 ^ 2 ^ 2) (hB : b.val < 2 ^ 2 ^ 2) (hb : Spec.BinaryField.towerOf 2 b ≠ 0) :
    tower.BinaryField4.Insts.CoreOpsArithDivBinaryField4BinaryField4.div a b ⦃ r =>
      r.val < 2 ^ 2 ^ 2 ∧ towerOf 2 r = towerOf 2 a / towerOf 2 b ⦄ :=
  Proofs.Binary.bf4_div_spec a b hA hB hb

/-- `div` panics. -/
theorem tower.BinaryField4.Insts.CoreOpsArithDivBinaryField4BinaryField4.div.panics (a b : tower.BinaryField4) (hB : b.val < 2 ^ 2 ^ 2) (hb : Spec.BinaryField.towerOf 2 b = 0) :
    tower.BinaryField4.Insts.CoreOpsArithDivBinaryField4BinaryField4.div a b = .fail .panic :=
  Proofs.Binary.bf4_div_zero a b hB hb

/-- The value `mul_assign` returns. -/
theorem tower.BinaryField4.Insts.CoreOpsArithMulAssign.mul_assign.towerOf (a b : tower.BinaryField4) :
    tower.BinaryField4.Insts.CoreOpsArithMulAssign.mul_assign
      (core.convert.Into.Blanket (core.convert.From.Blanket tower.BinaryField4)) a b ⦃ r =>
      towerOf 2 r = towerOf 2 a * towerOf 2 b ⦄ :=
  Proofs.Binary.bf4_mul_assign_spec a b

/-- The value `add_assign` returns. -/
theorem tower.BinaryField4.Insts.CoreOpsArithAddAssign.add_assign.towerOf (a b : tower.BinaryField4) :
    tower.BinaryField4.Insts.CoreOpsArithAddAssign.add_assign
      (core.convert.Into.Blanket (core.convert.From.Blanket tower.BinaryField4)) a b ⦃ r =>
      towerOf 2 r = towerOf 2 a + towerOf 2 b ⦄ :=
  Proofs.Binary.bf4_add_assign_spec a b

/-- The value `sub_assign` returns. -/
theorem tower.BinaryField4.Insts.CoreOpsArithSubAssign.sub_assign.towerOf (a b : tower.BinaryField4) :
    tower.BinaryField4.Insts.CoreOpsArithSubAssign.sub_assign
      (core.convert.Into.Blanket (core.convert.From.Blanket tower.BinaryField4)) a b ⦃ r =>
      towerOf 2 r = towerOf 2 a - towerOf 2 b ⦄ :=
  Proofs.Binary.bf4_sub_assign_spec a b

/-- The value `div_assign` returns. -/
theorem tower.BinaryField4.Insts.CoreOpsArithDivAssignBinaryField4.div_assign.towerOf (a b : tower.BinaryField4) (hB : b.val < 2 ^ 2 ^ 2) (hb : Spec.BinaryField.towerOf 2 b ≠ 0) :
    tower.BinaryField4.Insts.CoreOpsArithDivAssignBinaryField4.div_assign a b ⦃ r =>
      towerOf 2 r = towerOf 2 a / towerOf 2 b ⦄ :=
  Proofs.Binary.bf4_div_assign_spec a b hB hb

/-- The value `eq` returns. -/
theorem tower.BinaryField4.Insts.CoreCmpPartialEqBinaryField4.eq.towerOf (a b : tower.BinaryField4) (hA : a.val < 2 ^ 2 ^ 2) (hB : b.val < 2 ^ 2 ^ 2) :
    tower.BinaryField4.Insts.CoreCmpPartialEqBinaryField4.eq a b ⦃ r =>
      (r = true ↔ towerOf 2 a = towerOf 2 b) ⦄ :=
  Proofs.Binary.bf4_eq_spec a b hA hB

/-- The value `bool_check` returns. -/
theorem tower.BinaryField4.Insts.P3_fieldFieldPrimeCharacteristicRing.bool_check.towerOf (a : tower.BinaryField4) :
    tower.BinaryField4.Insts.P3_fieldFieldPrimeCharacteristicRing.bool_check a ⦃ r =>
      towerOf 2 r = towerOf 2 a * towerOf 2 a + towerOf 2 a ⦄ :=
  Proofs.Binary.bf4_bool_check_spec a

/-- The value `bits` returns. -/
theorem tower.BinaryField4.Insts.P3_fieldFieldField.bits.val :
    tower.BinaryField4.Insts.P3_fieldFieldField.bits ⦃ r => r.val = 2 ^ 2 ⦄ :=
  Proofs.Binary.bf4_bits_spec

/-- The value `from_bool` returns. -/
theorem tower.BinaryField4.Insts.P3_fieldFieldPrimeCharacteristicRing.from_bool.val (b : Bool) :
    tower.BinaryField4.Insts.P3_fieldFieldPrimeCharacteristicRing.from_bool b ⦃ r =>
      r.val = b.toNat ⦄ :=
  Proofs.Binary.bf4_from_bool_spec b

/-- The value `interpolation_node` returns. -/
theorem tower.BinaryField4.Insts.P3_fieldFieldField.interpolation_node.val (i : Std.Usize) (hi : i.val < 2 ^ 2 ^ 2) :
    tower.BinaryField4.Insts.P3_fieldFieldField.interpolation_node i ⦃ r => r.val = i.val ⦄ :=
  Proofs.Binary.bf4_interpolation_node_spec i hi

/-- `interpolation_node` panics. -/
theorem tower.BinaryField4.Insts.P3_fieldFieldField.interpolation_node.panics (i : Std.Usize) (hi : 2 ^ 2 ^ 2 ≤ i.val) :
    tower.BinaryField4.Insts.P3_fieldFieldField.interpolation_node i = .fail .panic :=
  Proofs.Binary.bf4_interpolation_node_fail i hi

/-- The value `inverse` returns. -/
theorem field_defaults.BinaryField8.inverse.towerOf (a : tower.BinaryField8) (ha : Spec.BinaryField.towerOf 3 a ≠ 0) :
    field_defaults.BinaryField8.inverse a ⦃ c =>
      c.val < 2 ^ 2 ^ 3 ∧ towerOf 3 c = (towerOf 3 a)⁻¹ ⦄ :=
  Proofs.Binary.bf8_inverse_spec a ha

/-- `inverse` panics. -/
theorem field_defaults.BinaryField8.inverse.panics (a : tower.BinaryField8) (ha : Spec.BinaryField.towerOf 3 a = 0) :
    field_defaults.BinaryField8.inverse a = .fail .panic :=
  Proofs.Binary.bf8_inverse_zero a ha

/-- The value `div` returns. -/
theorem tower.BinaryField8.Insts.CoreOpsArithDivBinaryField8BinaryField8.div.towerOf (a b : tower.BinaryField8) (hb : Spec.BinaryField.towerOf 3 b ≠ 0) :
    tower.BinaryField8.Insts.CoreOpsArithDivBinaryField8BinaryField8.div a b ⦃ r =>
      r.val < 2 ^ 2 ^ 3 ∧ towerOf 3 r = towerOf 3 a / towerOf 3 b ⦄ :=
  Proofs.Binary.bf8_div_spec a b hb

/-- `div` panics. -/
theorem tower.BinaryField8.Insts.CoreOpsArithDivBinaryField8BinaryField8.div.panics (a b : tower.BinaryField8) (hb : Spec.BinaryField.towerOf 3 b = 0) :
    tower.BinaryField8.Insts.CoreOpsArithDivBinaryField8BinaryField8.div a b = .fail .panic :=
  Proofs.Binary.bf8_div_zero a b hb

/-- The value `mul_assign` returns. -/
theorem tower.BinaryField8.Insts.CoreOpsArithMulAssign.mul_assign.towerOf (a b : tower.BinaryField8) :
    tower.BinaryField8.Insts.CoreOpsArithMulAssign.mul_assign
      (core.convert.Into.Blanket (core.convert.From.Blanket tower.BinaryField8)) a b ⦃ r =>
      towerOf 3 r = towerOf 3 a * towerOf 3 b ⦄ :=
  Proofs.Binary.bf8_mul_assign_spec a b

/-- The value `add_assign` returns. -/
theorem tower.BinaryField8.Insts.CoreOpsArithAddAssign.add_assign.towerOf (a b : tower.BinaryField8) :
    tower.BinaryField8.Insts.CoreOpsArithAddAssign.add_assign
      (core.convert.Into.Blanket (core.convert.From.Blanket tower.BinaryField8)) a b ⦃ r =>
      towerOf 3 r = towerOf 3 a + towerOf 3 b ⦄ :=
  Proofs.Binary.bf8_add_assign_spec a b

/-- The value `sub_assign` returns. -/
theorem tower.BinaryField8.Insts.CoreOpsArithSubAssign.sub_assign.towerOf (a b : tower.BinaryField8) :
    tower.BinaryField8.Insts.CoreOpsArithSubAssign.sub_assign
      (core.convert.Into.Blanket (core.convert.From.Blanket tower.BinaryField8)) a b ⦃ r =>
      towerOf 3 r = towerOf 3 a - towerOf 3 b ⦄ :=
  Proofs.Binary.bf8_sub_assign_spec a b

/-- The value `div_assign` returns. -/
theorem tower.BinaryField8.Insts.CoreOpsArithDivAssignBinaryField8.div_assign.towerOf (a b : tower.BinaryField8) (hb : Spec.BinaryField.towerOf 3 b ≠ 0) :
    tower.BinaryField8.Insts.CoreOpsArithDivAssignBinaryField8.div_assign a b ⦃ r =>
      towerOf 3 r = towerOf 3 a / towerOf 3 b ⦄ :=
  Proofs.Binary.bf8_div_assign_spec a b hb

/-- The value `eq` returns. -/
theorem tower.BinaryField8.Insts.CoreCmpPartialEqBinaryField8.eq.towerOf (a b : tower.BinaryField8) :
    tower.BinaryField8.Insts.CoreCmpPartialEqBinaryField8.eq a b ⦃ r =>
      (r = true ↔ towerOf 3 a = towerOf 3 b) ⦄ :=
  Proofs.Binary.bf8_eq_spec a b

/-- The value `bool_check` returns. -/
theorem tower.BinaryField8.Insts.P3_fieldFieldPrimeCharacteristicRing.bool_check.towerOf (a : tower.BinaryField8) :
    tower.BinaryField8.Insts.P3_fieldFieldPrimeCharacteristicRing.bool_check a ⦃ r =>
      towerOf 3 r = towerOf 3 a * towerOf 3 a + towerOf 3 a ⦄ :=
  Proofs.Binary.bf8_bool_check_spec a

/-- The value `bits` returns. -/
theorem tower.BinaryField8.Insts.P3_fieldFieldField.bits.val :
    tower.BinaryField8.Insts.P3_fieldFieldField.bits ⦃ r => r.val = 2 ^ 3 ⦄ :=
  Proofs.Binary.bf8_bits_spec

/-- The value `from_bool` returns. -/
theorem tower.BinaryField8.Insts.P3_fieldFieldPrimeCharacteristicRing.from_bool.val (b : Bool) :
    tower.BinaryField8.Insts.P3_fieldFieldPrimeCharacteristicRing.from_bool b ⦃ r =>
      r.val = b.toNat ⦄ :=
  Proofs.Binary.bf8_from_bool_spec b

/-- The value `interpolation_node` returns. -/
theorem tower.BinaryField8.Insts.P3_fieldFieldField.interpolation_node.val (i : Std.Usize) (hi : i.val < 2 ^ 2 ^ 3) :
    tower.BinaryField8.Insts.P3_fieldFieldField.interpolation_node i ⦃ r => r.val = i.val ⦄ :=
  Proofs.Binary.bf8_interpolation_node_spec i hi

/-- `interpolation_node` panics. -/
theorem tower.BinaryField8.Insts.P3_fieldFieldField.interpolation_node.panics (i : Std.Usize) (hi : 2 ^ 2 ^ 3 ≤ i.val) :
    tower.BinaryField8.Insts.P3_fieldFieldField.interpolation_node i = .fail .panic :=
  Proofs.Binary.bf8_interpolation_node_fail i hi

/-- The value `inverse` returns. -/
theorem field_defaults.BinaryField32.inverse.towerOf (a : tower.BinaryField32) (ha : Spec.BinaryField.towerOf 5 a ≠ 0) :
    field_defaults.BinaryField32.inverse a ⦃ c =>
      c.val < 2 ^ 2 ^ 5 ∧ towerOf 5 c = (towerOf 5 a)⁻¹ ⦄ :=
  Proofs.Binary.bf32_inverse_spec a ha

/-- `inverse` panics. -/
theorem field_defaults.BinaryField32.inverse.panics (a : tower.BinaryField32) (ha : Spec.BinaryField.towerOf 5 a = 0) :
    field_defaults.BinaryField32.inverse a = .fail .panic :=
  Proofs.Binary.bf32_inverse_zero a ha

/-- The value `div` returns. -/
theorem tower.BinaryField32.Insts.CoreOpsArithDivBinaryField32BinaryField32.div.towerOf (a b : tower.BinaryField32) (hb : Spec.BinaryField.towerOf 5 b ≠ 0) :
    tower.BinaryField32.Insts.CoreOpsArithDivBinaryField32BinaryField32.div a b ⦃ r =>
      r.val < 2 ^ 2 ^ 5 ∧ towerOf 5 r = towerOf 5 a / towerOf 5 b ⦄ :=
  Proofs.Binary.bf32_div_spec a b hb

/-- `div` panics. -/
theorem tower.BinaryField32.Insts.CoreOpsArithDivBinaryField32BinaryField32.div.panics (a b : tower.BinaryField32) (hb : Spec.BinaryField.towerOf 5 b = 0) :
    tower.BinaryField32.Insts.CoreOpsArithDivBinaryField32BinaryField32.div a b = .fail .panic :=
  Proofs.Binary.bf32_div_zero a b hb

/-- The value `mul_assign` returns. -/
theorem tower.BinaryField32.Insts.CoreOpsArithMulAssign.mul_assign.towerOf (a b : tower.BinaryField32) :
    tower.BinaryField32.Insts.CoreOpsArithMulAssign.mul_assign
      (core.convert.Into.Blanket (core.convert.From.Blanket tower.BinaryField32)) a b ⦃ r =>
      towerOf 5 r = towerOf 5 a * towerOf 5 b ⦄ :=
  Proofs.Binary.bf32_mul_assign_spec a b

/-- The value `add_assign` returns. -/
theorem tower.BinaryField32.Insts.CoreOpsArithAddAssign.add_assign.towerOf (a b : tower.BinaryField32) :
    tower.BinaryField32.Insts.CoreOpsArithAddAssign.add_assign
      (core.convert.Into.Blanket (core.convert.From.Blanket tower.BinaryField32)) a b ⦃ r =>
      towerOf 5 r = towerOf 5 a + towerOf 5 b ⦄ :=
  Proofs.Binary.bf32_add_assign_spec a b

/-- The value `sub_assign` returns. -/
theorem tower.BinaryField32.Insts.CoreOpsArithSubAssign.sub_assign.towerOf (a b : tower.BinaryField32) :
    tower.BinaryField32.Insts.CoreOpsArithSubAssign.sub_assign
      (core.convert.Into.Blanket (core.convert.From.Blanket tower.BinaryField32)) a b ⦃ r =>
      towerOf 5 r = towerOf 5 a - towerOf 5 b ⦄ :=
  Proofs.Binary.bf32_sub_assign_spec a b

/-- The value `div_assign` returns. -/
theorem tower.BinaryField32.Insts.CoreOpsArithDivAssignBinaryField32.div_assign.towerOf (a b : tower.BinaryField32) (hb : Spec.BinaryField.towerOf 5 b ≠ 0) :
    tower.BinaryField32.Insts.CoreOpsArithDivAssignBinaryField32.div_assign a b ⦃ r =>
      towerOf 5 r = towerOf 5 a / towerOf 5 b ⦄ :=
  Proofs.Binary.bf32_div_assign_spec a b hb

/-- The value `eq` returns. -/
theorem tower.BinaryField32.Insts.CoreCmpPartialEqBinaryField32.eq.towerOf (a b : tower.BinaryField32) :
    tower.BinaryField32.Insts.CoreCmpPartialEqBinaryField32.eq a b ⦃ r =>
      (r = true ↔ towerOf 5 a = towerOf 5 b) ⦄ :=
  Proofs.Binary.bf32_eq_spec a b

/-- The value `bool_check` returns. -/
theorem tower.BinaryField32.Insts.P3_fieldFieldPrimeCharacteristicRing.bool_check.towerOf (a : tower.BinaryField32) :
    tower.BinaryField32.Insts.P3_fieldFieldPrimeCharacteristicRing.bool_check a ⦃ r =>
      towerOf 5 r = towerOf 5 a * towerOf 5 a + towerOf 5 a ⦄ :=
  Proofs.Binary.bf32_bool_check_spec a

/-- The value `bits` returns. -/
theorem tower.BinaryField32.Insts.P3_fieldFieldField.bits.val :
    tower.BinaryField32.Insts.P3_fieldFieldField.bits ⦃ r => r.val = 2 ^ 5 ⦄ :=
  Proofs.Binary.bf32_bits_spec

/-- The value `from_bool` returns. -/
theorem tower.BinaryField32.Insts.P3_fieldFieldPrimeCharacteristicRing.from_bool.val (b : Bool) :
    tower.BinaryField32.Insts.P3_fieldFieldPrimeCharacteristicRing.from_bool b ⦃ r =>
      r.val = b.toNat ⦄ :=
  Proofs.Binary.bf32_from_bool_spec b

/-- The value `inverse` returns. -/
theorem field_defaults.BinaryField64.inverse.towerOf (a : tower.BinaryField64) (ha : Spec.BinaryField.towerOf 6 a ≠ 0) :
    field_defaults.BinaryField64.inverse a ⦃ c =>
      c.val < 2 ^ 2 ^ 6 ∧ towerOf 6 c = (towerOf 6 a)⁻¹ ⦄ :=
  Proofs.Binary.bf64_inverse_spec a ha

/-- `inverse` panics. -/
theorem field_defaults.BinaryField64.inverse.panics (a : tower.BinaryField64) (ha : Spec.BinaryField.towerOf 6 a = 0) :
    field_defaults.BinaryField64.inverse a = .fail .panic :=
  Proofs.Binary.bf64_inverse_zero a ha

/-- The value `div` returns. -/
theorem tower.BinaryField64.Insts.CoreOpsArithDivBinaryField64BinaryField64.div.towerOf (a b : tower.BinaryField64) (hb : Spec.BinaryField.towerOf 6 b ≠ 0) :
    tower.BinaryField64.Insts.CoreOpsArithDivBinaryField64BinaryField64.div a b ⦃ r =>
      r.val < 2 ^ 2 ^ 6 ∧ towerOf 6 r = towerOf 6 a / towerOf 6 b ⦄ :=
  Proofs.Binary.bf64_div_spec a b hb

/-- `div` panics. -/
theorem tower.BinaryField64.Insts.CoreOpsArithDivBinaryField64BinaryField64.div.panics (a b : tower.BinaryField64) (hb : Spec.BinaryField.towerOf 6 b = 0) :
    tower.BinaryField64.Insts.CoreOpsArithDivBinaryField64BinaryField64.div a b = .fail .panic :=
  Proofs.Binary.bf64_div_zero a b hb

/-- The value `mul_assign` returns. -/
theorem tower.BinaryField64.Insts.CoreOpsArithMulAssign.mul_assign.towerOf (a b : tower.BinaryField64) :
    tower.BinaryField64.Insts.CoreOpsArithMulAssign.mul_assign
      (core.convert.Into.Blanket (core.convert.From.Blanket tower.BinaryField64)) a b ⦃ r =>
      towerOf 6 r = towerOf 6 a * towerOf 6 b ⦄ :=
  Proofs.Binary.bf64_mul_assign_spec a b

/-- The value `add_assign` returns. -/
theorem tower.BinaryField64.Insts.CoreOpsArithAddAssign.add_assign.towerOf (a b : tower.BinaryField64) :
    tower.BinaryField64.Insts.CoreOpsArithAddAssign.add_assign
      (core.convert.Into.Blanket (core.convert.From.Blanket tower.BinaryField64)) a b ⦃ r =>
      towerOf 6 r = towerOf 6 a + towerOf 6 b ⦄ :=
  Proofs.Binary.bf64_add_assign_spec a b

/-- The value `sub_assign` returns. -/
theorem tower.BinaryField64.Insts.CoreOpsArithSubAssign.sub_assign.towerOf (a b : tower.BinaryField64) :
    tower.BinaryField64.Insts.CoreOpsArithSubAssign.sub_assign
      (core.convert.Into.Blanket (core.convert.From.Blanket tower.BinaryField64)) a b ⦃ r =>
      towerOf 6 r = towerOf 6 a - towerOf 6 b ⦄ :=
  Proofs.Binary.bf64_sub_assign_spec a b

/-- The value `div_assign` returns. -/
theorem tower.BinaryField64.Insts.CoreOpsArithDivAssignBinaryField64.div_assign.towerOf (a b : tower.BinaryField64) (hb : Spec.BinaryField.towerOf 6 b ≠ 0) :
    tower.BinaryField64.Insts.CoreOpsArithDivAssignBinaryField64.div_assign a b ⦃ r =>
      towerOf 6 r = towerOf 6 a / towerOf 6 b ⦄ :=
  Proofs.Binary.bf64_div_assign_spec a b hb

/-- The value `eq` returns. -/
theorem tower.BinaryField64.Insts.CoreCmpPartialEqBinaryField64.eq.towerOf (a b : tower.BinaryField64) :
    tower.BinaryField64.Insts.CoreCmpPartialEqBinaryField64.eq a b ⦃ r =>
      (r = true ↔ towerOf 6 a = towerOf 6 b) ⦄ :=
  Proofs.Binary.bf64_eq_spec a b

/-- The value `bool_check` returns. -/
theorem tower.BinaryField64.Insts.P3_fieldFieldPrimeCharacteristicRing.bool_check.towerOf (a : tower.BinaryField64) :
    tower.BinaryField64.Insts.P3_fieldFieldPrimeCharacteristicRing.bool_check a ⦃ r =>
      towerOf 6 r = towerOf 6 a * towerOf 6 a + towerOf 6 a ⦄ :=
  Proofs.Binary.bf64_bool_check_spec a

/-- The value `bits` returns. -/
theorem tower.BinaryField64.Insts.P3_fieldFieldField.bits.val :
    tower.BinaryField64.Insts.P3_fieldFieldField.bits ⦃ r => r.val = 2 ^ 6 ⦄ :=
  Proofs.Binary.bf64_bits_spec

/-- The value `from_bool` returns. -/
theorem tower.BinaryField64.Insts.P3_fieldFieldPrimeCharacteristicRing.from_bool.val (b : Bool) :
    tower.BinaryField64.Insts.P3_fieldFieldPrimeCharacteristicRing.from_bool b ⦃ r =>
      r.val = b.toNat ⦄ :=
  Proofs.Binary.bf64_from_bool_spec b

/-- The value `inverse` returns. -/
theorem field_defaults.BinaryField128.inverse.towerOf (a : tower.BinaryField128) (ha : Spec.BinaryField.towerOf 7 a ≠ 0) :
    field_defaults.BinaryField128.inverse a ⦃ c =>
      c.val < 2 ^ 2 ^ 7 ∧ towerOf 7 c = (towerOf 7 a)⁻¹ ⦄ :=
  Proofs.Binary.bf128_inverse_spec a ha

/-- `inverse` panics. -/
theorem field_defaults.BinaryField128.inverse.panics (a : tower.BinaryField128) (ha : Spec.BinaryField.towerOf 7 a = 0) :
    field_defaults.BinaryField128.inverse a = .fail .panic :=
  Proofs.Binary.bf128_inverse_zero a ha

/-- The value `div` returns. -/
theorem tower.BinaryField128.Insts.CoreOpsArithDivBinaryField128BinaryField128.div.towerOf (a b : tower.BinaryField128) (hb : Spec.BinaryField.towerOf 7 b ≠ 0) :
    tower.BinaryField128.Insts.CoreOpsArithDivBinaryField128BinaryField128.div a b ⦃ r =>
      r.val < 2 ^ 2 ^ 7 ∧ towerOf 7 r = towerOf 7 a / towerOf 7 b ⦄ :=
  Proofs.Binary.bf128_div_spec a b hb

/-- `div` panics. -/
theorem tower.BinaryField128.Insts.CoreOpsArithDivBinaryField128BinaryField128.div.panics (a b : tower.BinaryField128) (hb : Spec.BinaryField.towerOf 7 b = 0) :
    tower.BinaryField128.Insts.CoreOpsArithDivBinaryField128BinaryField128.div a b = .fail .panic :=
  Proofs.Binary.bf128_div_zero a b hb

/-- The value `mul_assign` returns. -/
theorem tower.BinaryField128.Insts.CoreOpsArithMulAssign.mul_assign.towerOf (a b : tower.BinaryField128) :
    tower.BinaryField128.Insts.CoreOpsArithMulAssign.mul_assign
      (core.convert.Into.Blanket (core.convert.From.Blanket tower.BinaryField128)) a b ⦃ r =>
      towerOf 7 r = towerOf 7 a * towerOf 7 b ⦄ :=
  Proofs.Binary.bf128_mul_assign_spec a b

/-- The value `add_assign` returns. -/
theorem tower.BinaryField128.Insts.CoreOpsArithAddAssign.add_assign.towerOf (a b : tower.BinaryField128) :
    tower.BinaryField128.Insts.CoreOpsArithAddAssign.add_assign
      (core.convert.Into.Blanket (core.convert.From.Blanket tower.BinaryField128)) a b ⦃ r =>
      towerOf 7 r = towerOf 7 a + towerOf 7 b ⦄ :=
  Proofs.Binary.bf128_add_assign_spec a b

/-- The value `sub_assign` returns. -/
theorem tower.BinaryField128.Insts.CoreOpsArithSubAssign.sub_assign.towerOf (a b : tower.BinaryField128) :
    tower.BinaryField128.Insts.CoreOpsArithSubAssign.sub_assign
      (core.convert.Into.Blanket (core.convert.From.Blanket tower.BinaryField128)) a b ⦃ r =>
      towerOf 7 r = towerOf 7 a - towerOf 7 b ⦄ :=
  Proofs.Binary.bf128_sub_assign_spec a b

/-- The value `div_assign` returns. -/
theorem tower.BinaryField128.Insts.CoreOpsArithDivAssignBinaryField128.div_assign.towerOf (a b : tower.BinaryField128) (hb : Spec.BinaryField.towerOf 7 b ≠ 0) :
    tower.BinaryField128.Insts.CoreOpsArithDivAssignBinaryField128.div_assign a b ⦃ r =>
      towerOf 7 r = towerOf 7 a / towerOf 7 b ⦄ :=
  Proofs.Binary.bf128_div_assign_spec a b hb

/-- The value `eq` returns. -/
theorem tower.BinaryField128.Insts.CoreCmpPartialEqBinaryField128.eq.towerOf (a b : tower.BinaryField128) :
    tower.BinaryField128.Insts.CoreCmpPartialEqBinaryField128.eq a b ⦃ r =>
      (r = true ↔ towerOf 7 a = towerOf 7 b) ⦄ :=
  Proofs.Binary.bf128_eq_spec a b

/-- The value `bool_check` returns. -/
theorem tower.BinaryField128.Insts.P3_fieldFieldPrimeCharacteristicRing.bool_check.towerOf (a : tower.BinaryField128) :
    tower.BinaryField128.Insts.P3_fieldFieldPrimeCharacteristicRing.bool_check a ⦃ r =>
      towerOf 7 r = towerOf 7 a * towerOf 7 a + towerOf 7 a ⦄ :=
  Proofs.Binary.bf128_bool_check_spec a

/-- The value `bits` returns. -/
theorem tower.BinaryField128.Insts.P3_fieldFieldField.bits.val :
    tower.BinaryField128.Insts.P3_fieldFieldField.bits ⦃ r => r.val = 2 ^ 7 ⦄ :=
  Proofs.Binary.bf128_bits_spec

/-- The value `from_bool` returns. -/
theorem tower.BinaryField128.Insts.P3_fieldFieldPrimeCharacteristicRing.from_bool.val (b : Bool) :
    tower.BinaryField128.Insts.P3_fieldFieldPrimeCharacteristicRing.from_bool b ⦃ r =>
      r.val = b.toNat ⦄ :=
  Proofs.Binary.bf128_from_bool_spec b

/-- The value `interpolation_node` returns. -/
theorem tower.BinaryField64.Insts.P3_fieldFieldField.interpolation_node.val (i : Std.Usize) :
    tower.BinaryField64.Insts.P3_fieldFieldField.interpolation_node i ⦃ r => r.val = i.val ⦄ :=
  Proofs.Binary.bf64_interpolation_node_spec i

/-- The value `interpolation_node` returns. -/
theorem tower.BinaryField128.Insts.P3_fieldFieldField.interpolation_node.val (i : Std.Usize) :
    tower.BinaryField128.Insts.P3_fieldFieldField.interpolation_node i ⦃ r => r.val = i.val ⦄ :=
  Proofs.Binary.bf128_interpolation_node_spec i

/-- The value `interpolation_node` returns. -/
theorem tower.BinaryField32.Insts.P3_fieldFieldField.interpolation_node.val (i : Std.Usize) (hi : i.val < 2 ^ 2 ^ 5) :
    tower.BinaryField32.Insts.P3_fieldFieldField.interpolation_node i ⦃ r => r.val = i.val ⦄ :=
  Proofs.Binary.bf32_interpolation_node_spec i hi

/-- `interpolation_node` panics. -/
theorem tower.BinaryField32.Insts.P3_fieldFieldField.interpolation_node.panics (i : Std.Usize) (hi : 2 ^ 2 ^ 5 ≤ i.val) :
    tower.BinaryField32.Insts.P3_fieldFieldField.interpolation_node i = .fail .panic :=
  Proofs.Binary.bf32_interpolation_node_fail i hi

/-! ### Poly64, Poly192 and Ghash128 -/

/-- The value `square` returns. -/
theorem poly64.Poly64.Insts.P3_fieldFieldPrimeCharacteristicRing.square.bf64 (a : poly64.Poly64) :
    poly64.Poly64.Insts.P3_fieldFieldPrimeCharacteristicRing.square a ⦃ r =>
      bf64 r = bf64 a * bf64 a ⦄ :=
  Proofs.Binary.poly64_square_bf64 a

/-- The value `invert_or_zero` returns. -/
theorem poly64.Poly64.invert_or_zero.bf64 (a : poly64.Poly64) :
    poly64.Poly64.invert_or_zero a ⦃ r => bf64 r = (bf64 a)⁻¹ ⦄ :=
  Proofs.Binary.poly64_invert_or_zero_bf64 a

/-- The value `is_zero` returns. -/
theorem field_defaults.Poly64.is_zero.bf64 (a : poly64.Poly64) :
    field_defaults.Poly64.is_zero a ⦃ b => (b = true ↔ bf64 a = 0) ⦄ :=
  Proofs.Binary.poly64_is_zero_spec a

/-- The value `try_inverse` returns. -/
theorem poly64.Poly64.Insts.P3_fieldFieldField.try_inverse.bf64 (a : poly64.Poly64) :
    poly64.Poly64.Insts.P3_fieldFieldField.try_inverse a ⦃ r =>
      (bf64 a = 0 → r = .None) ∧ (bf64 a ≠ 0 → ∃ c, r = .Some c ∧ bf64 c = (bf64 a)⁻¹) ⦄ :=
  Proofs.Binary.poly64_try_inverse_spec a

/-- The value `mul` returns. -/
theorem poly192.Poly192.Insts.CoreOpsArithMulPoly64Poly192.mul.toExt3 (a : poly192.Poly192) (k : poly64.Poly64) :
    poly192.Poly192.Insts.CoreOpsArithMulPoly64Poly192.mul a k ⦃ r =>
      toExt3 r = toExt3 a * algebraMap BF64 BF64.Ext3 (bf64 k) ⦄ :=
  Proofs.Binary.poly192_mul_poly64_ext a k

/-- The value `try_inverse` returns. -/
theorem poly192.Poly192.Insts.P3_fieldFieldField.try_inverse.toExt3 (a : poly192.Poly192) :
    poly192.Poly192.Insts.P3_fieldFieldField.try_inverse a ⦃ r =>
      (toExt3 a = 0 → r = .None) ∧ (toExt3 a ≠ 0 → ∃ c, r = .Some c ∧ toExt3 c = (toExt3 a)⁻¹) ⦄ :=
  Proofs.Binary.poly192_try_inverse_spec a

/-- The value `try_sqrt` returns. -/
theorem poly64.Poly64.Insts.P3_fieldFieldField.try_sqrt.bf64 (a : poly64.Poly64) :
    poly64.Poly64.Insts.P3_fieldFieldField.try_sqrt a ⦃ r =>
      ∃ c, r = .Some c ∧ bf64 c * bf64 c = bf64 a ⦄ :=
  Proofs.Binary.poly64_try_sqrt_bf64 a

/-- The value `try_sqrt` returns. -/
theorem poly192.Poly192.Insts.P3_fieldFieldField.try_sqrt.toExt3 (a : poly192.Poly192) :
    poly192.Poly192.Insts.P3_fieldFieldField.try_sqrt a ⦃ r =>
      ∃ c, r = .Some c ∧ toExt3 c * toExt3 c = toExt3 a ⦄ :=
  Proofs.Binary.poly192_try_sqrt_spec a

/-- The value `inverse` returns. -/
theorem field_defaults.Poly64.inverse.bf64 (a : poly64.Poly64) (ha : Spec.BinaryField.bf64 a ≠ 0) :
    field_defaults.Poly64.inverse a ⦃ c => bf64 c = (bf64 a)⁻¹ ⦄ :=
  Proofs.Binary.poly64_inverse_bf64 a ha

/-- `inverse` panics. -/
theorem field_defaults.Poly64.inverse.panics (a : poly64.Poly64) (ha : Spec.BinaryField.bf64 a = 0) :
    field_defaults.Poly64.inverse a = .fail .panic :=
  Proofs.Binary.poly64_inverse_zero a ha

/-- The value `div` returns. -/
theorem poly64.Poly64.Insts.CoreOpsArithDivPoly64Poly64.div.bf64 (a b : poly64.Poly64) (hb : Spec.BinaryField.bf64 b ≠ 0) :
    poly64.Poly64.Insts.CoreOpsArithDivPoly64Poly64.div a b ⦃ r => bf64 r = bf64 a / bf64 b ⦄ :=
  Proofs.Binary.poly64_div_bf64 a b hb

/-- `div` panics. -/
theorem poly64.Poly64.Insts.CoreOpsArithDivPoly64Poly64.div.panics (a b : poly64.Poly64) (hb : Spec.BinaryField.bf64 b = 0) :
    poly64.Poly64.Insts.CoreOpsArithDivPoly64Poly64.div a b = .fail .panic :=
  Proofs.Binary.poly64_div_zero a b hb

/-- The value `mul_assign` returns. -/
theorem poly64.Poly64.Insts.CoreOpsArithMulAssign.mul_assign.bf64 (a b : poly64.Poly64) :
    poly64.Poly64.Insts.CoreOpsArithMulAssign.mul_assign
      (core.convert.Into.Blanket (core.convert.From.Blanket poly64.Poly64)) a b ⦃ r =>
      bf64 r = bf64 a * bf64 b ⦄ :=
  Proofs.Binary.poly64_mul_assign_bf64 a b

/-- The value `add_assign` returns. -/
theorem poly64.Poly64.Insts.CoreOpsArithAddAssign.add_assign.bf64 (a b : poly64.Poly64) :
    poly64.Poly64.Insts.CoreOpsArithAddAssign.add_assign
      (core.convert.Into.Blanket (core.convert.From.Blanket poly64.Poly64)) a b ⦃ r =>
      bf64 r = bf64 a + bf64 b ⦄ :=
  Proofs.Binary.poly64_add_assign_bf64 a b

/-- The value `sub_assign` returns. -/
theorem poly64.Poly64.Insts.CoreOpsArithSubAssign.sub_assign.bf64 (a b : poly64.Poly64) :
    poly64.Poly64.Insts.CoreOpsArithSubAssign.sub_assign
      (core.convert.Into.Blanket (core.convert.From.Blanket poly64.Poly64)) a b ⦃ r =>
      bf64 r = bf64 a - bf64 b ⦄ :=
  Proofs.Binary.poly64_sub_assign_bf64 a b

/-- The value `div_assign` returns. -/
theorem poly64.Poly64.Insts.CoreOpsArithDivAssignPoly64.div_assign.bf64 (a b : poly64.Poly64) (hb : Spec.BinaryField.bf64 b ≠ 0) :
    poly64.Poly64.Insts.CoreOpsArithDivAssignPoly64.div_assign a b ⦃ r =>
      bf64 r = bf64 a / bf64 b ⦄ :=
  Proofs.Binary.poly64_div_assign_bf64 a b hb

/-- The value `eq` returns. -/
theorem poly64.Poly64.Insts.CoreCmpPartialEqPoly64.eq.bf64 (a b : poly64.Poly64) :
    poly64.Poly64.Insts.CoreCmpPartialEqPoly64.eq a b ⦃ r => (r = true ↔ bf64 a = bf64 b) ⦄ :=
  Proofs.Binary.poly64_eq_spec a b

/-- The value `from_bool` returns. -/
theorem poly64.Poly64.Insts.P3_fieldFieldPrimeCharacteristicRing.from_bool.val (b : Bool) :
    poly64.Poly64.Insts.P3_fieldFieldPrimeCharacteristicRing.from_bool b ⦃ r => r.val = b.toNat ⦄ :=
  Proofs.Binary.poly64_from_bool_spec b

/-- The value `interpolation_node` returns. -/
theorem poly64.Poly64.Insts.P3_fieldFieldField.interpolation_node.val (i : Std.Usize) :
    poly64.Poly64.Insts.P3_fieldFieldField.interpolation_node i ⦃ r => r.val = i.val ⦄ :=
  Proofs.Binary.poly64_interpolation_node_spec i

/-- The value `square` returns. -/
theorem poly192.Poly192.Insts.P3_fieldFieldPrimeCharacteristicRing.square.toExt3 (a : poly192.Poly192) :
    poly192.Poly192.Insts.P3_fieldFieldPrimeCharacteristicRing.square a ⦃ r =>
      toExt3 r = toExt3 a * toExt3 a ⦄ :=
  Proofs.Binary.poly192_square_ext a

/-- The value `square` returns. -/
theorem ghash.Ghash128.Insts.P3_fieldFieldPrimeCharacteristicRing.square.toGhash (a : ghash.Ghash128) :
    ghash.Ghash128.Insts.P3_fieldFieldPrimeCharacteristicRing.square a ⦃ r =>
      ghash r = ghash a * ghash a ⦄ :=
  Proofs.Binary.ghash128_square_ghash a

/-- The value `try_sqrt` returns. -/
theorem ghash.Ghash128.Insts.P3_fieldFieldField.try_sqrt.toGhash (a : ghash.Ghash128) :
    ghash.Ghash128.Insts.P3_fieldFieldField.try_sqrt a ⦃ r =>
      ∃ c, r = .Some c ∧ ghash c * ghash c = ghash a ⦄ :=
  Proofs.Binary.ghash128_try_sqrt_ghash a

/-- The value `mul_assign` returns. -/
theorem ghash.Ghash128.Insts.CoreOpsArithMulAssign.mul_assign.toGhash (a b : ghash.Ghash128) :
    ghash.Ghash128.Insts.CoreOpsArithMulAssign.mul_assign
      (core.convert.Into.Blanket (core.convert.From.Blanket ghash.Ghash128)) a b ⦃ r =>
      ghash r = ghash a * ghash b ⦄ :=
  Proofs.Binary.ghash128_mul_assign_ghash a b

/-- The value `add_assign` returns. -/
theorem ghash.Ghash128.Insts.CoreOpsArithAddAssign.add_assign.toGhash (a b : ghash.Ghash128) :
    ghash.Ghash128.Insts.CoreOpsArithAddAssign.add_assign
      (core.convert.Into.Blanket (core.convert.From.Blanket ghash.Ghash128)) a b ⦃ r =>
      ghash r = ghash a + ghash b ⦄ :=
  Proofs.Binary.ghash128_add_assign_ghash a b

/-- The value `sub_assign` returns. -/
theorem ghash.Ghash128.Insts.CoreOpsArithSubAssign.sub_assign.toGhash (a b : ghash.Ghash128) :
    ghash.Ghash128.Insts.CoreOpsArithSubAssign.sub_assign
      (core.convert.Into.Blanket (core.convert.From.Blanket ghash.Ghash128)) a b ⦃ r =>
      ghash r = ghash a - ghash b ⦄ :=
  Proofs.Binary.ghash128_sub_assign_ghash a b

/-- The value `interpolation_node` returns. -/
theorem ghash.Ghash128.Insts.P3_fieldFieldField.interpolation_node.val (i : Std.Usize) :
    ghash.Ghash128.Insts.P3_fieldFieldField.interpolation_node i ⦃ r => r.val = i.val ⦄ :=
  Proofs.Binary.ghash128_interpolation_node_spec i

/-- The value `inverse` returns. -/
theorem field_defaults.Poly192.inverse.toExt3 (a : poly192.Poly192) (ha : Spec.BinaryField.toExt3 a ≠ 0) :
    field_defaults.Poly192.inverse a ⦃ c => toExt3 c = (toExt3 a)⁻¹ ⦄ :=
  Proofs.Binary.poly192_inverse_ext a ha

/-- The value `div` returns. -/
theorem poly192.Poly192.Insts.CoreOpsArithDivPoly192Poly192.div.toExt3 (a b : poly192.Poly192) (hb : Spec.BinaryField.toExt3 b ≠ 0) :
    poly192.Poly192.Insts.CoreOpsArithDivPoly192Poly192.div a b ⦃ r =>
      toExt3 r = toExt3 a / toExt3 b ⦄ :=
  Proofs.Binary.poly192_div_ext a b hb

/-- The value `mul_assign` returns. -/
theorem poly192.Poly192.Insts.CoreOpsArithMulAssign.mul_assign.toExt3 (a b : poly192.Poly192) :
    poly192.Poly192.Insts.CoreOpsArithMulAssign.mul_assign
      (core.convert.Into.Blanket (core.convert.From.Blanket poly192.Poly192)) a b ⦃ r =>
      toExt3 r = toExt3 a * toExt3 b ⦄ :=
  Proofs.Binary.poly192_mul_assign_ext a b

/-- The value `add_assign` returns. -/
theorem poly192.Poly192.Insts.CoreOpsArithAddAssign.add_assign.toExt3 (a b : poly192.Poly192) :
    poly192.Poly192.Insts.CoreOpsArithAddAssign.add_assign
      (core.convert.Into.Blanket (core.convert.From.Blanket poly192.Poly192)) a b ⦃ r =>
      toExt3 r = toExt3 a + toExt3 b ⦄ :=
  Proofs.Binary.poly192_add_assign_ext a b

/-- The value `sub_assign` returns. -/
theorem poly192.Poly192.Insts.CoreOpsArithSubAssign.sub_assign.toExt3 (a b : poly192.Poly192) :
    poly192.Poly192.Insts.CoreOpsArithSubAssign.sub_assign
      (core.convert.Into.Blanket (core.convert.From.Blanket poly192.Poly192)) a b ⦃ r =>
      toExt3 r = toExt3 a - toExt3 b ⦄ :=
  Proofs.Binary.poly192_sub_assign_ext a b

/-- The value `div_assign` returns. -/
theorem poly192.Poly192.Insts.CoreOpsArithDivAssignPoly192.div_assign.toExt3 (a b : poly192.Poly192) (hb : Spec.BinaryField.toExt3 b ≠ 0) :
    poly192.Poly192.Insts.CoreOpsArithDivAssignPoly192.div_assign a b ⦃ r =>
      toExt3 r = toExt3 a / toExt3 b ⦄ :=
  Proofs.Binary.poly192_div_assign_ext a b hb

/-! ### Powers `x^(2^n)` from `GF(2^16)` up

`exp_power_of_2` applies `linear.rs`'s Frobenius tables. -/

/-- `exp_power_of_2 a n` is `a^(2^n)` in level `4` of the tower. -/
theorem tower.BinaryField16.Insts.P3_fieldFieldPrimeCharacteristicRing.exp_power_of_2.towerOf (a : tower.BinaryField16) (n : Std.Usize) :
    tower.BinaryField16.Insts.P3_fieldFieldPrimeCharacteristicRing.exp_power_of_2 a n ⦃ r =>
      r.val < 2 ^ 2 ^ 4 ∧ towerOf 4 r = towerOf 4 a ^ 2 ^ n.val ⦄ :=
  Proofs.Binary.bf16_exp_power_of_2_spec a n

/-- `exp_power_of_2 a n` is `a^(2^n)` in level `5` of the tower. -/
theorem tower.BinaryField32.Insts.P3_fieldFieldPrimeCharacteristicRing.exp_power_of_2.towerOf (a : tower.BinaryField32) (n : Std.Usize) :
    tower.BinaryField32.Insts.P3_fieldFieldPrimeCharacteristicRing.exp_power_of_2 a n ⦃ r =>
      r.val < 2 ^ 2 ^ 5 ∧ towerOf 5 r = towerOf 5 a ^ 2 ^ n.val ⦄ :=
  Proofs.Binary.bf32_exp_power_of_2_spec a n

/-- `exp_power_of_2 a n` is `a^(2^n)` in level `6` of the tower. -/
theorem tower.BinaryField64.Insts.P3_fieldFieldPrimeCharacteristicRing.exp_power_of_2.towerOf (a : tower.BinaryField64) (n : Std.Usize) :
    tower.BinaryField64.Insts.P3_fieldFieldPrimeCharacteristicRing.exp_power_of_2 a n ⦃ r =>
      r.val < 2 ^ 2 ^ 6 ∧ towerOf 6 r = towerOf 6 a ^ 2 ^ n.val ⦄ :=
  Proofs.Binary.bf64_exp_power_of_2_spec a n

/-- `exp_power_of_2 a n` is `a^(2^n)` in level `7` of the tower. -/
theorem tower.BinaryField128.Insts.P3_fieldFieldPrimeCharacteristicRing.exp_power_of_2.towerOf (a : tower.BinaryField128) (n : Std.Usize) :
    tower.BinaryField128.Insts.P3_fieldFieldPrimeCharacteristicRing.exp_power_of_2 a n ⦃ r =>
      r.val < 2 ^ 2 ^ 7 ∧ towerOf 7 r = towerOf 7 a ^ 2 ^ n.val ⦄ :=
  Proofs.Binary.bf128_exp_power_of_2_spec a n

/-! ### The tower as an extension of its lower levels -/

/-- The value `frobenius` returns. -/
theorem tower.BinaryField16.Insts.P3_fieldExtensionHasFrobeniusBinaryField8.frobenius.towerOf (a : tower.BinaryField16) :
    tower.BinaryField16.Insts.P3_fieldExtensionHasFrobeniusBinaryField8.frobenius a ⦃ r =>
      r.val < 2 ^ 2 ^ 4 ∧ towerOf 4 r = towerOf 4 a ^ 2 ^ 2 ^ 3 ⦄ :=
  Proofs.Binary.bf16_bf8_frobenius_spec a

/-- The value `from` returns. -/
theorem tower.BinaryField16.Insts.CoreConvertFromBinaryField8.from.towerOf (x : tower.BinaryField8) :
    tower.BinaryField16.Insts.CoreConvertFromBinaryField8.from x ⦃ r =>
      towerOf 4 r = ConcreteBinaryTower.concreteTowerAlgebraMap 3 4 (by omega) (towerOf 3 x) ⦄ :=
  Proofs.Binary.bf16_bf8_from_spec x

/-- The value `is_in_basefield` returns. -/
theorem tower.BinaryField16.Insts.P3_fieldFieldExtensionFieldBinaryField8.is_in_basefield.towerOf (a : tower.BinaryField16) :
    tower.BinaryField16.Insts.P3_fieldFieldExtensionFieldBinaryField8.is_in_basefield a ⦃ b =>
      (b = true ↔ ∃ y, towerOf 4 a = ConcreteBinaryTower.concreteTowerAlgebraMap 3 4 (by omega) y) ⦄ :=
  Proofs.Binary.bf16_bf8_is_in_basefield_spec a

/-- The value `as_base` returns. -/
theorem tower.BinaryField16.Insts.P3_fieldFieldExtensionFieldBinaryField8.as_base.towerOf (a : tower.BinaryField16) :
    tower.BinaryField16.Insts.P3_fieldFieldExtensionFieldBinaryField8.as_base a ⦃ r =>
      ((∃ y, towerOf 4 a = ConcreteBinaryTower.concreteTowerAlgebraMap 3 4 (by omega) y) →
        ∃ c, r = .Some c ∧ ConcreteBinaryTower.concreteTowerAlgebraMap 3 4 (by omega) (towerOf 3 c) = towerOf 4 a) ∧
      ((¬∃ y, towerOf 4 a = ConcreteBinaryTower.concreteTowerAlgebraMap 3 4 (by omega) y) → r = .None) ⦄ :=
  Proofs.Binary.bf16_bf8_as_base_spec a

/-- The value `repeated_frobenius` returns. -/
theorem tower.BinaryField16.Insts.P3_fieldExtensionHasFrobeniusBinaryField8.repeated_frobenius.towerOf (a : tower.BinaryField16) (count : Std.Usize) :
    tower.BinaryField16.Insts.P3_fieldExtensionHasFrobeniusBinaryField8.repeated_frobenius a count
      ⦃ r => r.val < 2 ^ 2 ^ 4 ∧ towerOf 4 r = towerOf 4 a ^ 2 ^ (2 ^ 3 * count.val) ⦄ :=
  Proofs.Binary.bf16_bf8_repeated_frobenius_spec a count

/-- The value `from` returns. -/
theorem tower.BinaryField32.Insts.CoreConvertFromBinaryField8.from.towerOf (x : tower.BinaryField8) :
    tower.BinaryField32.Insts.CoreConvertFromBinaryField8.from x ⦃ r =>
      towerOf 5 r = ConcreteBinaryTower.concreteTowerAlgebraMap 3 5 (by omega) (towerOf 3 x) ⦄ :=
  Proofs.Binary.bf32_bf8_from_spec x

/-- The value `is_in_basefield` returns. -/
theorem tower.BinaryField32.Insts.P3_fieldFieldExtensionFieldBinaryField8.is_in_basefield.towerOf (a : tower.BinaryField32) :
    tower.BinaryField32.Insts.P3_fieldFieldExtensionFieldBinaryField8.is_in_basefield a ⦃ b =>
      (b = true ↔ ∃ y, towerOf 5 a = ConcreteBinaryTower.concreteTowerAlgebraMap 3 5 (by omega) y) ⦄ :=
  Proofs.Binary.bf32_bf8_is_in_basefield_spec a

/-- The value `as_base` returns. -/
theorem tower.BinaryField32.Insts.P3_fieldFieldExtensionFieldBinaryField8.as_base.towerOf (a : tower.BinaryField32) :
    tower.BinaryField32.Insts.P3_fieldFieldExtensionFieldBinaryField8.as_base a ⦃ r =>
      ((∃ y, towerOf 5 a = ConcreteBinaryTower.concreteTowerAlgebraMap 3 5 (by omega) y) →
        ∃ c, r = .Some c ∧ ConcreteBinaryTower.concreteTowerAlgebraMap 3 5 (by omega) (towerOf 3 c) = towerOf 5 a) ∧
      ((¬∃ y, towerOf 5 a = ConcreteBinaryTower.concreteTowerAlgebraMap 3 5 (by omega) y) → r = .None) ⦄ :=
  Proofs.Binary.bf32_bf8_as_base_spec a

/-- The value `frobenius` returns. -/
theorem tower.BinaryField32.Insts.P3_fieldExtensionHasFrobeniusBinaryField8.frobenius.towerOf (a : tower.BinaryField32) :
    tower.BinaryField32.Insts.P3_fieldExtensionHasFrobeniusBinaryField8.frobenius a ⦃ r =>
      r.val < 2 ^ 2 ^ 5 ∧ towerOf 5 r = towerOf 5 a ^ 2 ^ 2 ^ 3 ⦄ :=
  Proofs.Binary.bf32_bf8_frobenius_spec a

/-- The value `repeated_frobenius` returns. -/
theorem tower.BinaryField32.Insts.P3_fieldExtensionHasFrobeniusBinaryField8.repeated_frobenius.towerOf (a : tower.BinaryField32) (count : Std.Usize) :
    tower.BinaryField32.Insts.P3_fieldExtensionHasFrobeniusBinaryField8.repeated_frobenius a count
      ⦃ r => r.val < 2 ^ 2 ^ 5 ∧ towerOf 5 r = towerOf 5 a ^ 2 ^ (2 ^ 3 * count.val) ⦄ :=
  Proofs.Binary.bf32_bf8_repeated_frobenius_spec a count

/-- The value `from` returns. -/
theorem tower.BinaryField32.Insts.CoreConvertFromBinaryField16.from.towerOf (x : tower.BinaryField16) :
    tower.BinaryField32.Insts.CoreConvertFromBinaryField16.from x ⦃ r =>
      towerOf 5 r = ConcreteBinaryTower.concreteTowerAlgebraMap 4 5 (by omega) (towerOf 4 x) ⦄ :=
  Proofs.Binary.bf32_bf16_from_spec x

/-- The value `is_in_basefield` returns. -/
theorem tower.BinaryField32.Insts.P3_fieldFieldExtensionFieldBinaryField16.is_in_basefield.towerOf (a : tower.BinaryField32) :
    tower.BinaryField32.Insts.P3_fieldFieldExtensionFieldBinaryField16.is_in_basefield a ⦃ b =>
      (b = true ↔ ∃ y, towerOf 5 a = ConcreteBinaryTower.concreteTowerAlgebraMap 4 5 (by omega) y) ⦄ :=
  Proofs.Binary.bf32_bf16_is_in_basefield_spec a

/-- The value `as_base` returns. -/
theorem tower.BinaryField32.Insts.P3_fieldFieldExtensionFieldBinaryField16.as_base.towerOf (a : tower.BinaryField32) :
    tower.BinaryField32.Insts.P3_fieldFieldExtensionFieldBinaryField16.as_base a ⦃ r =>
      ((∃ y, towerOf 5 a = ConcreteBinaryTower.concreteTowerAlgebraMap 4 5 (by omega) y) →
        ∃ c, r = .Some c ∧ ConcreteBinaryTower.concreteTowerAlgebraMap 4 5 (by omega) (towerOf 4 c) = towerOf 5 a) ∧
      ((¬∃ y, towerOf 5 a = ConcreteBinaryTower.concreteTowerAlgebraMap 4 5 (by omega) y) → r = .None) ⦄ :=
  Proofs.Binary.bf32_bf16_as_base_spec a

/-- The value `frobenius` returns. -/
theorem tower.BinaryField32.Insts.P3_fieldExtensionHasFrobeniusBinaryField16.frobenius.towerOf (a : tower.BinaryField32) :
    tower.BinaryField32.Insts.P3_fieldExtensionHasFrobeniusBinaryField16.frobenius a ⦃ r =>
      r.val < 2 ^ 2 ^ 5 ∧ towerOf 5 r = towerOf 5 a ^ 2 ^ 2 ^ 4 ⦄ :=
  Proofs.Binary.bf32_bf16_frobenius_spec a

/-- The value `repeated_frobenius` returns. -/
theorem tower.BinaryField32.Insts.P3_fieldExtensionHasFrobeniusBinaryField16.repeated_frobenius.towerOf (a : tower.BinaryField32) (count : Std.Usize) :
    tower.BinaryField32.Insts.P3_fieldExtensionHasFrobeniusBinaryField16.repeated_frobenius a count
      ⦃ r => r.val < 2 ^ 2 ^ 5 ∧ towerOf 5 r = towerOf 5 a ^ 2 ^ (2 ^ 4 * count.val) ⦄ :=
  Proofs.Binary.bf32_bf16_repeated_frobenius_spec a count

/-- The value `from` returns. -/
theorem tower.BinaryField64.Insts.CoreConvertFromBinaryField32.from.towerOf (x : tower.BinaryField32) :
    tower.BinaryField64.Insts.CoreConvertFromBinaryField32.from x ⦃ r =>
      towerOf 6 r = ConcreteBinaryTower.concreteTowerAlgebraMap 5 6 (by omega) (towerOf 5 x) ⦄ :=
  Proofs.Binary.bf64_bf32_from_spec x

/-- The value `is_in_basefield` returns. -/
theorem tower.BinaryField64.Insts.P3_fieldFieldExtensionFieldBinaryField32.is_in_basefield.towerOf (a : tower.BinaryField64) :
    tower.BinaryField64.Insts.P3_fieldFieldExtensionFieldBinaryField32.is_in_basefield a ⦃ b =>
      (b = true ↔ ∃ y, towerOf 6 a = ConcreteBinaryTower.concreteTowerAlgebraMap 5 6 (by omega) y) ⦄ :=
  Proofs.Binary.bf64_bf32_is_in_basefield_spec a

/-- The value `as_base` returns. -/
theorem tower.BinaryField64.Insts.P3_fieldFieldExtensionFieldBinaryField32.as_base.towerOf (a : tower.BinaryField64) :
    tower.BinaryField64.Insts.P3_fieldFieldExtensionFieldBinaryField32.as_base a ⦃ r =>
      ((∃ y, towerOf 6 a = ConcreteBinaryTower.concreteTowerAlgebraMap 5 6 (by omega) y) →
        ∃ c, r = .Some c ∧ ConcreteBinaryTower.concreteTowerAlgebraMap 5 6 (by omega) (towerOf 5 c) = towerOf 6 a) ∧
      ((¬∃ y, towerOf 6 a = ConcreteBinaryTower.concreteTowerAlgebraMap 5 6 (by omega) y) → r = .None) ⦄ :=
  Proofs.Binary.bf64_bf32_as_base_spec a

/-- The value `frobenius` returns. -/
theorem tower.BinaryField64.Insts.P3_fieldExtensionHasFrobeniusBinaryField32.frobenius.towerOf (a : tower.BinaryField64) :
    tower.BinaryField64.Insts.P3_fieldExtensionHasFrobeniusBinaryField32.frobenius a ⦃ r =>
      r.val < 2 ^ 2 ^ 6 ∧ towerOf 6 r = towerOf 6 a ^ 2 ^ 2 ^ 5 ⦄ :=
  Proofs.Binary.bf64_bf32_frobenius_spec a

/-- The value `repeated_frobenius` returns. -/
theorem tower.BinaryField64.Insts.P3_fieldExtensionHasFrobeniusBinaryField32.repeated_frobenius.towerOf (a : tower.BinaryField64) (count : Std.Usize) :
    tower.BinaryField64.Insts.P3_fieldExtensionHasFrobeniusBinaryField32.repeated_frobenius a count
      ⦃ r => r.val < 2 ^ 2 ^ 6 ∧ towerOf 6 r = towerOf 6 a ^ 2 ^ (2 ^ 5 * count.val) ⦄ :=
  Proofs.Binary.bf64_bf32_repeated_frobenius_spec a count

/-- The value `from` returns. -/
theorem tower.BinaryField128.Insts.CoreConvertFromBinaryField64.from.towerOf (x : tower.BinaryField64) :
    tower.BinaryField128.Insts.CoreConvertFromBinaryField64.from x ⦃ r =>
      towerOf 7 r = ConcreteBinaryTower.concreteTowerAlgebraMap 6 7 (by omega) (towerOf 6 x) ⦄ :=
  Proofs.Binary.bf128_bf64_from_spec x

/-- The value `is_in_basefield` returns. -/
theorem tower.BinaryField128.Insts.P3_fieldFieldExtensionFieldBinaryField64.is_in_basefield.towerOf (a : tower.BinaryField128) :
    tower.BinaryField128.Insts.P3_fieldFieldExtensionFieldBinaryField64.is_in_basefield a ⦃ b =>
      (b = true ↔ ∃ y, towerOf 7 a = ConcreteBinaryTower.concreteTowerAlgebraMap 6 7 (by omega) y) ⦄ :=
  Proofs.Binary.bf128_bf64_is_in_basefield_spec a

/-- The value `as_base` returns. -/
theorem tower.BinaryField128.Insts.P3_fieldFieldExtensionFieldBinaryField64.as_base.towerOf (a : tower.BinaryField128) :
    tower.BinaryField128.Insts.P3_fieldFieldExtensionFieldBinaryField64.as_base a ⦃ r =>
      ((∃ y, towerOf 7 a = ConcreteBinaryTower.concreteTowerAlgebraMap 6 7 (by omega) y) →
        ∃ c, r = .Some c ∧ ConcreteBinaryTower.concreteTowerAlgebraMap 6 7 (by omega) (towerOf 6 c) = towerOf 7 a) ∧
      ((¬∃ y, towerOf 7 a = ConcreteBinaryTower.concreteTowerAlgebraMap 6 7 (by omega) y) → r = .None) ⦄ :=
  Proofs.Binary.bf128_bf64_as_base_spec a

/-- The value `frobenius` returns. -/
theorem tower.BinaryField128.Insts.P3_fieldExtensionHasFrobeniusBinaryField64.frobenius.towerOf (a : tower.BinaryField128) :
    tower.BinaryField128.Insts.P3_fieldExtensionHasFrobeniusBinaryField64.frobenius a ⦃ r =>
      r.val < 2 ^ 2 ^ 7 ∧ towerOf 7 r = towerOf 7 a ^ 2 ^ 2 ^ 6 ⦄ :=
  Proofs.Binary.bf128_bf64_frobenius_spec a

/-- The value `repeated_frobenius` returns. -/
theorem tower.BinaryField128.Insts.P3_fieldExtensionHasFrobeniusBinaryField64.repeated_frobenius.towerOf (a : tower.BinaryField128) (count : Std.Usize) :
    tower.BinaryField128.Insts.P3_fieldExtensionHasFrobeniusBinaryField64.repeated_frobenius a count
      ⦃ r => r.val < 2 ^ 2 ^ 7 ∧ towerOf 7 r = towerOf 7 a ^ 2 ^ (2 ^ 6 * count.val) ⦄ :=
  Proofs.Binary.bf128_bf64_repeated_frobenius_spec a count

/-- The value `from` returns. -/
theorem tower.BinaryField64.Insts.CoreConvertFromBinaryField8.from.towerOf (x : tower.BinaryField8) :
    tower.BinaryField64.Insts.CoreConvertFromBinaryField8.from x ⦃ r =>
      towerOf 6 r = ConcreteBinaryTower.concreteTowerAlgebraMap 3 6 (by omega) (towerOf 3 x) ⦄ :=
  Proofs.Binary.bf64_bf8_from_spec x

/-- The value `is_in_basefield` returns. -/
theorem tower.BinaryField64.Insts.P3_fieldFieldExtensionFieldBinaryField8.is_in_basefield.towerOf (a : tower.BinaryField64) :
    tower.BinaryField64.Insts.P3_fieldFieldExtensionFieldBinaryField8.is_in_basefield a ⦃ b =>
      (b = true ↔ ∃ y, towerOf 6 a = ConcreteBinaryTower.concreteTowerAlgebraMap 3 6 (by omega) y) ⦄ :=
  Proofs.Binary.bf64_bf8_is_in_basefield_spec a

/-- The value `as_base` returns. -/
theorem tower.BinaryField64.Insts.P3_fieldFieldExtensionFieldBinaryField8.as_base.towerOf (a : tower.BinaryField64) :
    tower.BinaryField64.Insts.P3_fieldFieldExtensionFieldBinaryField8.as_base a ⦃ r =>
      ((∃ y, towerOf 6 a = ConcreteBinaryTower.concreteTowerAlgebraMap 3 6 (by omega) y) →
        ∃ c, r = .Some c ∧ ConcreteBinaryTower.concreteTowerAlgebraMap 3 6 (by omega) (towerOf 3 c) = towerOf 6 a) ∧
      ((¬∃ y, towerOf 6 a = ConcreteBinaryTower.concreteTowerAlgebraMap 3 6 (by omega) y) → r = .None) ⦄ :=
  Proofs.Binary.bf64_bf8_as_base_spec a

/-- The value `frobenius` returns. -/
theorem tower.BinaryField64.Insts.P3_fieldExtensionHasFrobeniusBinaryField8.frobenius.towerOf (a : tower.BinaryField64) :
    tower.BinaryField64.Insts.P3_fieldExtensionHasFrobeniusBinaryField8.frobenius a ⦃ r =>
      r.val < 2 ^ 2 ^ 6 ∧ towerOf 6 r = towerOf 6 a ^ 2 ^ 2 ^ 3 ⦄ :=
  Proofs.Binary.bf64_bf8_frobenius_spec a

/-- The value `repeated_frobenius` returns. -/
theorem tower.BinaryField64.Insts.P3_fieldExtensionHasFrobeniusBinaryField8.repeated_frobenius.towerOf (a : tower.BinaryField64) (count : Std.Usize) :
    tower.BinaryField64.Insts.P3_fieldExtensionHasFrobeniusBinaryField8.repeated_frobenius a count
      ⦃ r => r.val < 2 ^ 2 ^ 6 ∧ towerOf 6 r = towerOf 6 a ^ 2 ^ (2 ^ 3 * count.val) ⦄ :=
  Proofs.Binary.bf64_bf8_repeated_frobenius_spec a count

/-- The value `from` returns. -/
theorem tower.BinaryField128.Insts.CoreConvertFromBinaryField8.from.towerOf (x : tower.BinaryField8) :
    tower.BinaryField128.Insts.CoreConvertFromBinaryField8.from x ⦃ r =>
      towerOf 7 r = ConcreteBinaryTower.concreteTowerAlgebraMap 3 7 (by omega) (towerOf 3 x) ⦄ :=
  Proofs.Binary.bf128_bf8_from_spec x

/-- The value `is_in_basefield` returns. -/
theorem tower.BinaryField128.Insts.P3_fieldFieldExtensionFieldBinaryField8.is_in_basefield.towerOf (a : tower.BinaryField128) :
    tower.BinaryField128.Insts.P3_fieldFieldExtensionFieldBinaryField8.is_in_basefield a ⦃ b =>
      (b = true ↔ ∃ y, towerOf 7 a = ConcreteBinaryTower.concreteTowerAlgebraMap 3 7 (by omega) y) ⦄ :=
  Proofs.Binary.bf128_bf8_is_in_basefield_spec a

/-- The value `as_base` returns. -/
theorem tower.BinaryField128.Insts.P3_fieldFieldExtensionFieldBinaryField8.as_base.towerOf (a : tower.BinaryField128) :
    tower.BinaryField128.Insts.P3_fieldFieldExtensionFieldBinaryField8.as_base a ⦃ r =>
      ((∃ y, towerOf 7 a = ConcreteBinaryTower.concreteTowerAlgebraMap 3 7 (by omega) y) →
        ∃ c, r = .Some c ∧ ConcreteBinaryTower.concreteTowerAlgebraMap 3 7 (by omega) (towerOf 3 c) = towerOf 7 a) ∧
      ((¬∃ y, towerOf 7 a = ConcreteBinaryTower.concreteTowerAlgebraMap 3 7 (by omega) y) → r = .None) ⦄ :=
  Proofs.Binary.bf128_bf8_as_base_spec a

/-- The value `frobenius` returns. -/
theorem tower.BinaryField128.Insts.P3_fieldExtensionHasFrobeniusBinaryField8.frobenius.towerOf (a : tower.BinaryField128) :
    tower.BinaryField128.Insts.P3_fieldExtensionHasFrobeniusBinaryField8.frobenius a ⦃ r =>
      r.val < 2 ^ 2 ^ 7 ∧ towerOf 7 r = towerOf 7 a ^ 2 ^ 2 ^ 3 ⦄ :=
  Proofs.Binary.bf128_bf8_frobenius_spec a

/-- The value `repeated_frobenius` returns. -/
theorem tower.BinaryField128.Insts.P3_fieldExtensionHasFrobeniusBinaryField8.repeated_frobenius.towerOf (a : tower.BinaryField128) (count : Std.Usize) :
    tower.BinaryField128.Insts.P3_fieldExtensionHasFrobeniusBinaryField8.repeated_frobenius a count
      ⦃ r => r.val < 2 ^ 2 ^ 7 ∧ towerOf 7 r = towerOf 7 a ^ 2 ^ (2 ^ 3 * count.val) ⦄ :=
  Proofs.Binary.bf128_bf8_repeated_frobenius_spec a count

/-- The value `from` returns. -/
theorem tower.BinaryField64.Insts.CoreConvertFromBinaryField16.from.towerOf (x : tower.BinaryField16) :
    tower.BinaryField64.Insts.CoreConvertFromBinaryField16.from x ⦃ r =>
      towerOf 6 r = ConcreteBinaryTower.concreteTowerAlgebraMap 4 6 (by omega) (towerOf 4 x) ⦄ :=
  Proofs.Binary.bf64_bf16_from_spec x

/-- The value `is_in_basefield` returns. -/
theorem tower.BinaryField64.Insts.P3_fieldFieldExtensionFieldBinaryField16.is_in_basefield.towerOf (a : tower.BinaryField64) :
    tower.BinaryField64.Insts.P3_fieldFieldExtensionFieldBinaryField16.is_in_basefield a ⦃ b =>
      (b = true ↔ ∃ y, towerOf 6 a = ConcreteBinaryTower.concreteTowerAlgebraMap 4 6 (by omega) y) ⦄ :=
  Proofs.Binary.bf64_bf16_is_in_basefield_spec a

/-- The value `as_base` returns. -/
theorem tower.BinaryField64.Insts.P3_fieldFieldExtensionFieldBinaryField16.as_base.towerOf (a : tower.BinaryField64) :
    tower.BinaryField64.Insts.P3_fieldFieldExtensionFieldBinaryField16.as_base a ⦃ r =>
      ((∃ y, towerOf 6 a = ConcreteBinaryTower.concreteTowerAlgebraMap 4 6 (by omega) y) →
        ∃ c, r = .Some c ∧ ConcreteBinaryTower.concreteTowerAlgebraMap 4 6 (by omega) (towerOf 4 c) = towerOf 6 a) ∧
      ((¬∃ y, towerOf 6 a = ConcreteBinaryTower.concreteTowerAlgebraMap 4 6 (by omega) y) → r = .None) ⦄ :=
  Proofs.Binary.bf64_bf16_as_base_spec a

/-- The value `frobenius` returns. -/
theorem tower.BinaryField64.Insts.P3_fieldExtensionHasFrobeniusBinaryField16.frobenius.towerOf (a : tower.BinaryField64) :
    tower.BinaryField64.Insts.P3_fieldExtensionHasFrobeniusBinaryField16.frobenius a ⦃ r =>
      r.val < 2 ^ 2 ^ 6 ∧ towerOf 6 r = towerOf 6 a ^ 2 ^ 2 ^ 4 ⦄ :=
  Proofs.Binary.bf64_bf16_frobenius_spec a

/-- The value `repeated_frobenius` returns. -/
theorem tower.BinaryField64.Insts.P3_fieldExtensionHasFrobeniusBinaryField16.repeated_frobenius.towerOf (a : tower.BinaryField64) (count : Std.Usize) :
    tower.BinaryField64.Insts.P3_fieldExtensionHasFrobeniusBinaryField16.repeated_frobenius a count
      ⦃ r => r.val < 2 ^ 2 ^ 6 ∧ towerOf 6 r = towerOf 6 a ^ 2 ^ (2 ^ 4 * count.val) ⦄ :=
  Proofs.Binary.bf64_bf16_repeated_frobenius_spec a count

/-- The value `from` returns. -/
theorem tower.BinaryField128.Insts.CoreConvertFromBinaryField16.from.towerOf (x : tower.BinaryField16) :
    tower.BinaryField128.Insts.CoreConvertFromBinaryField16.from x ⦃ r =>
      towerOf 7 r = ConcreteBinaryTower.concreteTowerAlgebraMap 4 7 (by omega) (towerOf 4 x) ⦄ :=
  Proofs.Binary.bf128_bf16_from_spec x

/-- The value `is_in_basefield` returns. -/
theorem tower.BinaryField128.Insts.P3_fieldFieldExtensionFieldBinaryField16.is_in_basefield.towerOf (a : tower.BinaryField128) :
    tower.BinaryField128.Insts.P3_fieldFieldExtensionFieldBinaryField16.is_in_basefield a ⦃ b =>
      (b = true ↔ ∃ y, towerOf 7 a = ConcreteBinaryTower.concreteTowerAlgebraMap 4 7 (by omega) y) ⦄ :=
  Proofs.Binary.bf128_bf16_is_in_basefield_spec a

/-- The value `as_base` returns. -/
theorem tower.BinaryField128.Insts.P3_fieldFieldExtensionFieldBinaryField16.as_base.towerOf (a : tower.BinaryField128) :
    tower.BinaryField128.Insts.P3_fieldFieldExtensionFieldBinaryField16.as_base a ⦃ r =>
      ((∃ y, towerOf 7 a = ConcreteBinaryTower.concreteTowerAlgebraMap 4 7 (by omega) y) →
        ∃ c, r = .Some c ∧ ConcreteBinaryTower.concreteTowerAlgebraMap 4 7 (by omega) (towerOf 4 c) = towerOf 7 a) ∧
      ((¬∃ y, towerOf 7 a = ConcreteBinaryTower.concreteTowerAlgebraMap 4 7 (by omega) y) → r = .None) ⦄ :=
  Proofs.Binary.bf128_bf16_as_base_spec a

/-- The value `frobenius` returns. -/
theorem tower.BinaryField128.Insts.P3_fieldExtensionHasFrobeniusBinaryField16.frobenius.towerOf (a : tower.BinaryField128) :
    tower.BinaryField128.Insts.P3_fieldExtensionHasFrobeniusBinaryField16.frobenius a ⦃ r =>
      r.val < 2 ^ 2 ^ 7 ∧ towerOf 7 r = towerOf 7 a ^ 2 ^ 2 ^ 4 ⦄ :=
  Proofs.Binary.bf128_bf16_frobenius_spec a

/-- The value `repeated_frobenius` returns. -/
theorem tower.BinaryField128.Insts.P3_fieldExtensionHasFrobeniusBinaryField16.repeated_frobenius.towerOf (a : tower.BinaryField128) (count : Std.Usize) :
    tower.BinaryField128.Insts.P3_fieldExtensionHasFrobeniusBinaryField16.repeated_frobenius a count
      ⦃ r => r.val < 2 ^ 2 ^ 7 ∧ towerOf 7 r = towerOf 7 a ^ 2 ^ (2 ^ 4 * count.val) ⦄ :=
  Proofs.Binary.bf128_bf16_repeated_frobenius_spec a count

/-- The value `from` returns. -/
theorem tower.BinaryField128.Insts.CoreConvertFromBinaryField32.from.towerOf (x : tower.BinaryField32) :
    tower.BinaryField128.Insts.CoreConvertFromBinaryField32.from x ⦃ r =>
      towerOf 7 r = ConcreteBinaryTower.concreteTowerAlgebraMap 5 7 (by omega) (towerOf 5 x) ⦄ :=
  Proofs.Binary.bf128_bf32_from_spec x

/-- The value `is_in_basefield` returns. -/
theorem tower.BinaryField128.Insts.P3_fieldFieldExtensionFieldBinaryField32.is_in_basefield.towerOf (a : tower.BinaryField128) :
    tower.BinaryField128.Insts.P3_fieldFieldExtensionFieldBinaryField32.is_in_basefield a ⦃ b =>
      (b = true ↔ ∃ y, towerOf 7 a = ConcreteBinaryTower.concreteTowerAlgebraMap 5 7 (by omega) y) ⦄ :=
  Proofs.Binary.bf128_bf32_is_in_basefield_spec a

/-- The value `as_base` returns. -/
theorem tower.BinaryField128.Insts.P3_fieldFieldExtensionFieldBinaryField32.as_base.towerOf (a : tower.BinaryField128) :
    tower.BinaryField128.Insts.P3_fieldFieldExtensionFieldBinaryField32.as_base a ⦃ r =>
      ((∃ y, towerOf 7 a = ConcreteBinaryTower.concreteTowerAlgebraMap 5 7 (by omega) y) →
        ∃ c, r = .Some c ∧ ConcreteBinaryTower.concreteTowerAlgebraMap 5 7 (by omega) (towerOf 5 c) = towerOf 7 a) ∧
      ((¬∃ y, towerOf 7 a = ConcreteBinaryTower.concreteTowerAlgebraMap 5 7 (by omega) y) → r = .None) ⦄ :=
  Proofs.Binary.bf128_bf32_as_base_spec a

/-- The value `frobenius` returns. -/
theorem tower.BinaryField128.Insts.P3_fieldExtensionHasFrobeniusBinaryField32.frobenius.towerOf (a : tower.BinaryField128) :
    tower.BinaryField128.Insts.P3_fieldExtensionHasFrobeniusBinaryField32.frobenius a ⦃ r =>
      r.val < 2 ^ 2 ^ 7 ∧ towerOf 7 r = towerOf 7 a ^ 2 ^ 2 ^ 5 ⦄ :=
  Proofs.Binary.bf128_bf32_frobenius_spec a

/-- The value `repeated_frobenius` returns. -/
theorem tower.BinaryField128.Insts.P3_fieldExtensionHasFrobeniusBinaryField32.repeated_frobenius.towerOf (a : tower.BinaryField128) (count : Std.Usize) :
    tower.BinaryField128.Insts.P3_fieldExtensionHasFrobeniusBinaryField32.repeated_frobenius a count
      ⦃ r => r.val < 2 ^ 2 ^ 7 ∧ towerOf 7 r = towerOf 7 a ^ 2 ^ (2 ^ 5 * count.val) ⦄ :=
  Proofs.Binary.bf128_bf32_repeated_frobenius_spec a count

/-! ### Products with a lower level

A level is a vector space over each lower level, its coefficients stored as consecutive chunks.
Multiplying by a lower-level element is multiplying by its embedding. -/

/-- `GF(2^16)` times `GF(2^8)` is the product with the embedding. -/
theorem tower.BinaryField16.Insts.CoreOpsArithMulBinaryField8BinaryField16.mul.towerOf (a : tower.BinaryField16) (b : tower.BinaryField8) :
    tower.BinaryField16.Insts.CoreOpsArithMulBinaryField8BinaryField16.mul a b ⦃ r =>
      towerOf 4 r =
        towerOf 4 a * ConcreteBinaryTower.concreteTowerAlgebraMap 3 4 (by omega) (towerOf 3 b) ⦄ :=
  Proofs.Binary.bf16_bf8_mul_spec a b

/-- `GF(2^8)` times `GF(2^16)` is the product with the embedding. -/
theorem tower.BinaryField8.Insts.CoreOpsArithMulBinaryField16BinaryField16.mul.towerOf (a : tower.BinaryField8) (b : tower.BinaryField16) :
    tower.BinaryField8.Insts.CoreOpsArithMulBinaryField16BinaryField16.mul a b ⦃ r =>
      towerOf 4 r =
        ConcreteBinaryTower.concreteTowerAlgebraMap 3 4 (by omega) (towerOf 3 a) * towerOf 4 b ⦄ :=
  Proofs.Binary.bf8_bf16_mul_spec a b

/-- `GF(2^32)` times `GF(2^8)` is the product with the embedding. -/
theorem tower.BinaryField32.Insts.CoreOpsArithMulBinaryField8BinaryField32.mul.towerOf (a : tower.BinaryField32) (b : tower.BinaryField8) :
    tower.BinaryField32.Insts.CoreOpsArithMulBinaryField8BinaryField32.mul a b ⦃ r =>
      towerOf 5 r =
        towerOf 5 a * ConcreteBinaryTower.concreteTowerAlgebraMap 3 5 (by omega) (towerOf 3 b) ⦄ :=
  Proofs.Binary.bf32_bf8_mul_spec a b

/-- `GF(2^8)` times `GF(2^32)` is the product with the embedding. -/
theorem tower.BinaryField8.Insts.CoreOpsArithMulBinaryField32BinaryField32.mul.towerOf (a : tower.BinaryField8) (b : tower.BinaryField32) :
    tower.BinaryField8.Insts.CoreOpsArithMulBinaryField32BinaryField32.mul a b ⦃ r =>
      towerOf 5 r =
        ConcreteBinaryTower.concreteTowerAlgebraMap 3 5 (by omega) (towerOf 3 a) * towerOf 5 b ⦄ :=
  Proofs.Binary.bf8_bf32_mul_spec a b

/-- `GF(2^64)` times `GF(2^8)` is the product with the embedding. -/
theorem tower.BinaryField64.Insts.CoreOpsArithMulBinaryField8BinaryField64.mul.towerOf (a : tower.BinaryField64) (b : tower.BinaryField8) :
    tower.BinaryField64.Insts.CoreOpsArithMulBinaryField8BinaryField64.mul a b ⦃ r =>
      towerOf 6 r =
        towerOf 6 a * ConcreteBinaryTower.concreteTowerAlgebraMap 3 6 (by omega) (towerOf 3 b) ⦄ :=
  Proofs.Binary.bf64_bf8_mul_spec a b

/-- `GF(2^8)` times `GF(2^64)` is the product with the embedding. -/
theorem tower.BinaryField8.Insts.CoreOpsArithMulBinaryField64BinaryField64.mul.towerOf (a : tower.BinaryField8) (b : tower.BinaryField64) :
    tower.BinaryField8.Insts.CoreOpsArithMulBinaryField64BinaryField64.mul a b ⦃ r =>
      towerOf 6 r =
        ConcreteBinaryTower.concreteTowerAlgebraMap 3 6 (by omega) (towerOf 3 a) * towerOf 6 b ⦄ :=
  Proofs.Binary.bf8_bf64_mul_spec a b

/-- `GF(2^128)` times `GF(2^8)` is the product with the embedding. -/
theorem tower.BinaryField128.Insts.CoreOpsArithMulBinaryField8BinaryField128.mul.towerOf (a : tower.BinaryField128) (b : tower.BinaryField8) :
    tower.BinaryField128.Insts.CoreOpsArithMulBinaryField8BinaryField128.mul a b ⦃ r =>
      towerOf 7 r =
        towerOf 7 a * ConcreteBinaryTower.concreteTowerAlgebraMap 3 7 (by omega) (towerOf 3 b) ⦄ :=
  Proofs.Binary.bf128_bf8_mul_spec a b

/-- `GF(2^8)` times `GF(2^128)` is the product with the embedding. -/
theorem tower.BinaryField8.Insts.CoreOpsArithMulBinaryField128BinaryField128.mul.towerOf (a : tower.BinaryField8) (b : tower.BinaryField128) :
    tower.BinaryField8.Insts.CoreOpsArithMulBinaryField128BinaryField128.mul a b ⦃ r =>
      towerOf 7 r =
        ConcreteBinaryTower.concreteTowerAlgebraMap 3 7 (by omega) (towerOf 3 a) * towerOf 7 b ⦄ :=
  Proofs.Binary.bf8_bf128_mul_spec a b

/-- `GF(2^32)` times `GF(2^16)` is the product with the embedding. -/
theorem tower.BinaryField32.Insts.CoreOpsArithMulBinaryField16BinaryField32.mul.towerOf (a : tower.BinaryField32) (b : tower.BinaryField16) :
    tower.BinaryField32.Insts.CoreOpsArithMulBinaryField16BinaryField32.mul a b ⦃ r =>
      towerOf 5 r =
        towerOf 5 a * ConcreteBinaryTower.concreteTowerAlgebraMap 4 5 (by omega) (towerOf 4 b) ⦄ :=
  Proofs.Binary.bf32_bf16_mul_spec a b

/-- `GF(2^16)` times `GF(2^32)` is the product with the embedding. -/
theorem tower.BinaryField16.Insts.CoreOpsArithMulBinaryField32BinaryField32.mul.towerOf (a : tower.BinaryField16) (b : tower.BinaryField32) :
    tower.BinaryField16.Insts.CoreOpsArithMulBinaryField32BinaryField32.mul a b ⦃ r =>
      towerOf 5 r =
        ConcreteBinaryTower.concreteTowerAlgebraMap 4 5 (by omega) (towerOf 4 a) * towerOf 5 b ⦄ :=
  Proofs.Binary.bf16_bf32_mul_spec a b

/-- `GF(2^64)` times `GF(2^16)` is the product with the embedding. -/
theorem tower.BinaryField64.Insts.CoreOpsArithMulBinaryField16BinaryField64.mul.towerOf (a : tower.BinaryField64) (b : tower.BinaryField16) :
    tower.BinaryField64.Insts.CoreOpsArithMulBinaryField16BinaryField64.mul a b ⦃ r =>
      towerOf 6 r =
        towerOf 6 a * ConcreteBinaryTower.concreteTowerAlgebraMap 4 6 (by omega) (towerOf 4 b) ⦄ :=
  Proofs.Binary.bf64_bf16_mul_spec a b

/-- `GF(2^16)` times `GF(2^64)` is the product with the embedding. -/
theorem tower.BinaryField16.Insts.CoreOpsArithMulBinaryField64BinaryField64.mul.towerOf (a : tower.BinaryField16) (b : tower.BinaryField64) :
    tower.BinaryField16.Insts.CoreOpsArithMulBinaryField64BinaryField64.mul a b ⦃ r =>
      towerOf 6 r =
        ConcreteBinaryTower.concreteTowerAlgebraMap 4 6 (by omega) (towerOf 4 a) * towerOf 6 b ⦄ :=
  Proofs.Binary.bf16_bf64_mul_spec a b

/-- `GF(2^128)` times `GF(2^16)` is the product with the embedding. -/
theorem tower.BinaryField128.Insts.CoreOpsArithMulBinaryField16BinaryField128.mul.towerOf (a : tower.BinaryField128) (b : tower.BinaryField16) :
    tower.BinaryField128.Insts.CoreOpsArithMulBinaryField16BinaryField128.mul a b ⦃ r =>
      towerOf 7 r =
        towerOf 7 a * ConcreteBinaryTower.concreteTowerAlgebraMap 4 7 (by omega) (towerOf 4 b) ⦄ :=
  Proofs.Binary.bf128_bf16_mul_spec a b

/-- `GF(2^16)` times `GF(2^128)` is the product with the embedding. -/
theorem tower.BinaryField16.Insts.CoreOpsArithMulBinaryField128BinaryField128.mul.towerOf (a : tower.BinaryField16) (b : tower.BinaryField128) :
    tower.BinaryField16.Insts.CoreOpsArithMulBinaryField128BinaryField128.mul a b ⦃ r =>
      towerOf 7 r =
        ConcreteBinaryTower.concreteTowerAlgebraMap 4 7 (by omega) (towerOf 4 a) * towerOf 7 b ⦄ :=
  Proofs.Binary.bf16_bf128_mul_spec a b

/-- `GF(2^64)` times `GF(2^32)` is the product with the embedding. -/
theorem tower.BinaryField64.Insts.CoreOpsArithMulBinaryField32BinaryField64.mul.towerOf (a : tower.BinaryField64) (b : tower.BinaryField32) :
    tower.BinaryField64.Insts.CoreOpsArithMulBinaryField32BinaryField64.mul a b ⦃ r =>
      towerOf 6 r =
        towerOf 6 a * ConcreteBinaryTower.concreteTowerAlgebraMap 5 6 (by omega) (towerOf 5 b) ⦄ :=
  Proofs.Binary.bf64_bf32_mul_spec a b

/-- `GF(2^32)` times `GF(2^64)` is the product with the embedding. -/
theorem tower.BinaryField32.Insts.CoreOpsArithMulBinaryField64BinaryField64.mul.towerOf (a : tower.BinaryField32) (b : tower.BinaryField64) :
    tower.BinaryField32.Insts.CoreOpsArithMulBinaryField64BinaryField64.mul a b ⦃ r =>
      towerOf 6 r =
        ConcreteBinaryTower.concreteTowerAlgebraMap 5 6 (by omega) (towerOf 5 a) * towerOf 6 b ⦄ :=
  Proofs.Binary.bf32_bf64_mul_spec a b

/-- `GF(2^128)` times `GF(2^32)` is the product with the embedding. -/
theorem tower.BinaryField128.Insts.CoreOpsArithMulBinaryField32BinaryField128.mul.towerOf (a : tower.BinaryField128) (b : tower.BinaryField32) :
    tower.BinaryField128.Insts.CoreOpsArithMulBinaryField32BinaryField128.mul a b ⦃ r =>
      towerOf 7 r =
        towerOf 7 a * ConcreteBinaryTower.concreteTowerAlgebraMap 5 7 (by omega) (towerOf 5 b) ⦄ :=
  Proofs.Binary.bf128_bf32_mul_spec a b

/-- `GF(2^32)` times `GF(2^128)` is the product with the embedding. -/
theorem tower.BinaryField32.Insts.CoreOpsArithMulBinaryField128BinaryField128.mul.towerOf (a : tower.BinaryField32) (b : tower.BinaryField128) :
    tower.BinaryField32.Insts.CoreOpsArithMulBinaryField128BinaryField128.mul a b ⦃ r =>
      towerOf 7 r =
        ConcreteBinaryTower.concreteTowerAlgebraMap 5 7 (by omega) (towerOf 5 a) * towerOf 7 b ⦄ :=
  Proofs.Binary.bf32_bf128_mul_spec a b

/-- `GF(2^128)` times `GF(2^64)` is the product with the embedding. -/
theorem tower.BinaryField128.Insts.CoreOpsArithMulBinaryField64BinaryField128.mul.towerOf (a : tower.BinaryField128) (b : tower.BinaryField64) :
    tower.BinaryField128.Insts.CoreOpsArithMulBinaryField64BinaryField128.mul a b ⦃ r =>
      towerOf 7 r =
        towerOf 7 a * ConcreteBinaryTower.concreteTowerAlgebraMap 6 7 (by omega) (towerOf 6 b) ⦄ :=
  Proofs.Binary.bf128_bf64_mul_spec a b

/-- `GF(2^64)` times `GF(2^128)` is the product with the embedding. -/
theorem tower.BinaryField64.Insts.CoreOpsArithMulBinaryField128BinaryField128.mul.towerOf (a : tower.BinaryField64) (b : tower.BinaryField128) :
    tower.BinaryField64.Insts.CoreOpsArithMulBinaryField128BinaryField128.mul a b ⦃ r =>
      towerOf 7 r =
        ConcreteBinaryTower.concreteTowerAlgebraMap 6 7 (by omega) (towerOf 6 a) * towerOf 7 b ⦄ :=
  Proofs.Binary.bf64_bf128_mul_spec a b

/-! ## The basis change between the tower and the polynomial bases -/

/-- `tower_to_poly_128` is the field isomorphism `N` of the tower's `GF(2^128)` onto the polynomial basis. -/
theorem clmul.basis.tower_to_poly_128.iso (v : Std.U128) :
    clmul.basis.tower_to_poly_128 v ⦃ r =>
      AdjoinRoot.mk (Proofs.Binary.modPoly 128 135) (poly r) = Proofs.Binary.N128 (Spec.BinaryField.towerOf 7 v) ⦄ :=
  by simpa only [Proofs.Binary.poly_eq_natPoly, Proofs.Binary.N128_apply, Proofs.Binary.N64_apply] using Proofs.Binary.tower_to_poly_128_spec v

/-- `poly_to_tower_128` is the inverse of `N`. -/
theorem clmul.basis.poly_to_tower_128.iso (v : Std.U128) :
    clmul.basis.poly_to_tower_128 v ⦃ r =>
      Proofs.Binary.N128 (Spec.BinaryField.towerOf 7 r) = AdjoinRoot.mk (Proofs.Binary.modPoly 128 135) (poly v) ⦄ :=
  by simpa only [Proofs.Binary.poly_eq_natPoly, Proofs.Binary.N128_apply, Proofs.Binary.N64_apply] using Proofs.Binary.poly_to_tower_128_spec v

/-- `tower_to_poly_64` is the field isomorphism `N` of the tower's `GF(2^64)` onto the polynomial basis. -/
theorem clmul.basis.tower_to_poly_64.iso (v : Std.U64) :
    clmul.basis.tower_to_poly_64 v ⦃ r =>
      AdjoinRoot.mk (Proofs.Binary.modPoly 64 27) (poly r) = Proofs.Binary.N64 (Spec.BinaryField.towerOf 6 v) ⦄ :=
  by simpa only [Proofs.Binary.poly_eq_natPoly, Proofs.Binary.N128_apply, Proofs.Binary.N64_apply] using Proofs.Binary.tower_to_poly_64_spec v

/-- `poly_to_tower_64` is the inverse of `N`. -/
theorem clmul.basis.poly_to_tower_64.iso (v : Std.U64) :
    clmul.basis.poly_to_tower_64 v ⦃ r =>
      Proofs.Binary.N64 (Spec.BinaryField.towerOf 6 r) = AdjoinRoot.mk (Proofs.Binary.modPoly 64 27) (poly v) ⦄ :=
  by simpa only [Proofs.Binary.poly_eq_natPoly, Proofs.Binary.N128_apply, Proofs.Binary.N64_apply] using Proofs.Binary.poly_to_tower_64_spec v

/-- `tower_to_poly_32` is the field isomorphism `N` of the tower's `GF(2^32)` onto the polynomial basis. -/
theorem clmul.basis.tower_to_poly_32.iso (v : Std.U32) :
    clmul.basis.tower_to_poly_32 v ⦃ r =>
      AdjoinRoot.mk (Proofs.Binary.modPoly 32 141) (poly r) = Proofs.Binary.towerMap Proofs.Binary.xi32 5 (Spec.BinaryField.towerOf 5 v) ⦄ :=
  by simpa only [Proofs.Binary.poly_eq_natPoly, Proofs.Binary.N128_apply, Proofs.Binary.N64_apply] using Proofs.Binary.tower_to_poly_32_spec v

/-- `poly_to_tower_32` is the inverse of `N`. -/
theorem clmul.basis.poly_to_tower_32.iso (v : Std.U32) :
    clmul.basis.poly_to_tower_32 v ⦃ r =>
      Proofs.Binary.towerMap Proofs.Binary.xi32 5 (Spec.BinaryField.towerOf 5 r) = AdjoinRoot.mk (Proofs.Binary.modPoly 32 141) (poly v) ⦄ :=
  by simpa only [Proofs.Binary.poly_eq_natPoly, Proofs.Binary.N128_apply, Proofs.Binary.N64_apply] using Proofs.Binary.poly_to_tower_32_spec v

/-- `N` at 128 bits is injective. -/
theorem Proofs.Binary.N128.injective' :
    Function.Injective Proofs.Binary.N128 :=
  Proofs.Binary.N128_injective

/-- `tower_image_128` is `N` at 128 bits. -/
theorem clmul.basis.tower_image_128.iso (v : Std.U128) :
    clmul.basis.tower_image_128 v ⦃ r =>
      AdjoinRoot.mk (Proofs.Binary.modPoly 128 135) (poly r) = Proofs.Binary.N128 (Spec.BinaryField.towerOf 7 v) ⦄ :=
  by simpa only [Proofs.Binary.poly_eq_natPoly, Proofs.Binary.N128_apply, Proofs.Binary.N64_apply] using Proofs.Binary.tower_image_128_spec v

/-- `tower_image_64` is `N` at 64 bits. -/
theorem clmul.basis.tower_image_64.iso (v : Std.U64) :
    clmul.basis.tower_image_64 v ⦃ r =>
      AdjoinRoot.mk (Proofs.Binary.modPoly 64 27) (poly r) = Proofs.Binary.N64 (Spec.BinaryField.towerOf 6 v) ⦄ :=
  by simpa only [Proofs.Binary.poly_eq_natPoly, Proofs.Binary.N128_apply, Proofs.Binary.N64_apply] using Proofs.Binary.tower_image_64_spec v

/-! ## GHASH through the tower -/

/-- `From<BinaryField128> for Ghash128` is the field embedding `towerToGhash`. -/
theorem ghash.Ghash128.Insts.CoreConvertFromBinaryField128.from.toGhash (t : tower.BinaryField128) :
    ghash.Ghash128.Insts.CoreConvertFromBinaryField128.from t ⦃ x =>
      toQuot (ghash x) = Proofs.Binary.towerToGhash (Spec.BinaryField.towerOf 7 t) ⦄ :=
  Proofs.Binary.ghash128_from_bf128_toQuot t

/-- `From<Ghash128> for BinaryField128` is the inverse of `towerToGhash`. -/
theorem tower.BinaryField128.Insts.CoreConvertFromGhash128.from.toGhash (x : ghash.Ghash128) :
    tower.BinaryField128.Insts.CoreConvertFromGhash128.from x ⦃ t =>
      Proofs.Binary.towerToGhash (Spec.BinaryField.towerOf 7 t) = toQuot (ghash x) ⦄ :=
  Proofs.Binary.bf128_from_ghash_toQuot x

/-- `towerToGhash` is injective. -/
theorem Proofs.Binary.towerToGhash.injective' :
    Function.Injective Proofs.Binary.towerToGhash :=
  Proofs.Binary.towerToGhash_injective

/-- `invert_or_zero` is the inverse in the GHASH field, with `0⁻¹ = 0`. -/
theorem ghash.Ghash128.invert_or_zero.toGhash (a : ghash.Ghash128) :
    ghash.Ghash128.invert_or_zero a ⦃ r => ghash r = (ghash a)⁻¹ ⦄ :=
  Proofs.Binary.ghash128_invert_or_zero_ghash a

/-- The value `try_inverse` returns. -/
theorem ghash.Ghash128.Insts.P3_fieldFieldField.try_inverse.toGhash (a : ghash.Ghash128) :
    ghash.Ghash128.Insts.P3_fieldFieldField.try_inverse a ⦃ r =>
      (ghash a = 0 → r = .None) ∧ (ghash a ≠ 0 → ∃ c, r = .Some c ∧ ghash c = (ghash a)⁻¹) ⦄ :=
  Proofs.Binary.ghash128_try_inverse_spec a

/-- `inverse` of a nonzero element. -/
theorem field_defaults.Ghash128.inverse.toGhash (a : ghash.Ghash128) (ha : ghash a ≠ 0) :
    field_defaults.Ghash128.inverse a ⦃ c => ghash c = (ghash a)⁻¹ ⦄ :=
  Proofs.Binary.ghash128_inverse_ghash a ha

/-- `inverse` panics. -/
theorem field_defaults.Ghash128.inverse.panics (a : ghash.Ghash128) (ha : ghash a = 0) :
    field_defaults.Ghash128.inverse a = .fail .panic :=
  Proofs.Binary.ghash128_inverse_zero a ha

/-- `div` by a nonzero element. -/
theorem ghash.Ghash128.Insts.CoreOpsArithDivGhash128Ghash128.div.toGhash (a b : ghash.Ghash128) (hb : ghash b ≠ 0) :
    ghash.Ghash128.Insts.CoreOpsArithDivGhash128Ghash128.div a b ⦃ r => ghash r = ghash a / ghash b ⦄ :=
  Proofs.Binary.ghash128_div_ghash a b hb

/-- `div` panics. -/
theorem ghash.Ghash128.Insts.CoreOpsArithDivGhash128Ghash128.div.panics (a b : ghash.Ghash128) (hb : ghash b = 0) :
    ghash.Ghash128.Insts.CoreOpsArithDivGhash128Ghash128.div a b = .fail .panic :=
  Proofs.Binary.ghash128_div_zero a b hb

/-- `div_assign` by a nonzero element. -/
theorem ghash.Ghash128.Insts.CoreOpsArithDivAssignGhash128.div_assign.toGhash (a b : ghash.Ghash128) (hb : ghash b ≠ 0) :
    ghash.Ghash128.Insts.CoreOpsArithDivAssignGhash128.div_assign a b ⦃ r => ghash r = ghash a / ghash b ⦄ :=
  Proofs.Binary.ghash128_div_assign_ghash a b hb

/-- `div_assign` panics. -/
theorem ghash.Ghash128.Insts.CoreOpsArithDivAssignGhash128.div_assign.panics (a b : ghash.Ghash128) (hb : ghash b = 0) :
    ghash.Ghash128.Insts.CoreOpsArithDivAssignGhash128.div_assign a b = .fail .panic :=
  Proofs.Binary.ghash128_div_assign_zero a b hb

/-- `add` of a GHASH element and a tower element goes through `towerToGhash`. -/
theorem ghash.Ghash128.Insts.CoreOpsArithAddBinaryField128Ghash128.add.toGhash (a : ghash.Ghash128) (b : tower.BinaryField128) :
    ghash.Ghash128.Insts.CoreOpsArithAddBinaryField128Ghash128.add a b ⦃ r =>
      toQuot (ghash r) = toQuot (ghash a) + Proofs.Binary.towerToGhash (Spec.BinaryField.towerOf 7 b) ⦄ :=
  Proofs.Binary.ghash128_add_bf128 a b

/-- `sub` of a GHASH element and a tower element goes through `towerToGhash`. -/
theorem ghash.Ghash128.Insts.CoreOpsArithSubBinaryField128Ghash128.sub.toGhash (a : ghash.Ghash128) (b : tower.BinaryField128) :
    ghash.Ghash128.Insts.CoreOpsArithSubBinaryField128Ghash128.sub a b ⦃ r =>
      toQuot (ghash r) = toQuot (ghash a) - Proofs.Binary.towerToGhash (Spec.BinaryField.towerOf 7 b) ⦄ :=
  Proofs.Binary.ghash128_sub_bf128 a b

/-- `mul` of a GHASH element and a tower element goes through `towerToGhash`. -/
theorem ghash.Ghash128.Insts.CoreOpsArithMulBinaryField128Ghash128.mul.toGhash (a : ghash.Ghash128) (b : tower.BinaryField128) :
    ghash.Ghash128.Insts.CoreOpsArithMulBinaryField128Ghash128.mul a b ⦃ r =>
      toQuot (ghash r) = toQuot (ghash a) * Proofs.Binary.towerToGhash (Spec.BinaryField.towerOf 7 b) ⦄ :=
  Proofs.Binary.ghash128_mul_bf128 a b

/-! ## The carry-less multiplication paths -/

/-- `clmul_128x128` is the carry-less product of two 128-bit polynomials, as low and high halves. -/
theorem clmul.clmul_128x128.poly (a b : Std.U128) :
    clmul.clmul_128x128 a b ⦃ p => poly p.1 + X ^ 128 * poly p.2 = poly a * poly b ⦄ :=
  by simpa only [Proofs.Binary.poly_eq_natPoly, Proofs.Binary.N128_apply, Proofs.Binary.N64_apply] using Proofs.Binary.clmul_128x128_spec a b

/-- The carry-less `mul_128` is the tower product. -/
theorem clmul.mul_128.towerOf (a b : Std.U128) :
    clmul.mul_128 a b ⦃ r => Spec.BinaryField.towerOf 7 r = Spec.BinaryField.towerOf 7 a * Spec.BinaryField.towerOf 7 b ⦄ :=
  Proofs.Binary.mul_128_spec a b

/-- The carry-less `mul_64` is the tower product. -/
theorem clmul.mul_64.towerOf (a b : Std.U64) :
    clmul.mul_64 a b ⦃ r => Spec.BinaryField.towerOf 6 r = Spec.BinaryField.towerOf 6 a * Spec.BinaryField.towerOf 6 b ⦄ :=
  Proofs.Binary.mul_64_spec a b

/-- Both products of `mul_pair_64` are tower products by the scalar. -/
theorem clmul.mul_pair_64.towerOf (a b s : Std.U64) :
    clmul.mul_pair_64 a b s ⦃ p =>
      Spec.BinaryField.towerOf 6 p.1 = Spec.BinaryField.towerOf 6 a * Spec.BinaryField.towerOf 6 s ∧ Spec.BinaryField.towerOf 6 p.2 = Spec.BinaryField.towerOf 6 b * Spec.BinaryField.towerOf 6 s ⦄ :=
  Proofs.Binary.mul_pair_64_spec a b s

/-- The table `square_64` is the tower square. -/
theorem clmul.square_64.towerOf (v : Std.U64) :
    clmul.square_64 v ⦃ r => Spec.BinaryField.towerOf 6 r = Spec.BinaryField.towerOf 6 v ^ 2 ⦄ :=
  Proofs.Binary.clmul_square_64_spec v

/-- The table `square_128` is the tower square. -/
theorem clmul.square_128.towerOf (v : Std.U128) :
    clmul.square_128 v ⦃ r => Spec.BinaryField.towerOf 7 r = Spec.BinaryField.towerOf 7 v ^ 2 ⦄ :=
  Proofs.Binary.clmul_square_128_spec v

/-- `table_square` is the tower square. -/
theorem tower.BinaryField64.table_square.towerOf (a : tower.BinaryField64) :
    tower.BinaryField64.table_square a ⦃ r => Spec.BinaryField.towerOf 6 r = Spec.BinaryField.towerOf 6 a ^ 2 ⦄ :=
  Proofs.Binary.bf64_table_square_spec a

/-- `table_square` is the tower square. -/
theorem tower.BinaryField128.table_square.towerOf (a : tower.BinaryField128) :
    tower.BinaryField128.table_square a ⦃ r => Spec.BinaryField.towerOf 7 r = Spec.BinaryField.towerOf 7 a ^ 2 ⦄ :=
  Proofs.Binary.bf128_table_square_spec a

/-! ## `Poly64` and the tower -/

/-- `From<BinaryField64> for Poly64` is the field embedding `towerToBF64`. -/
theorem poly64.Poly64.Insts.CoreConvertFromBinaryField64.from.toQuot64 (t : tower.BinaryField64) :
    poly64.Poly64.Insts.CoreConvertFromBinaryField64.from t ⦃ p =>
      toQuot64 p = Proofs.Binary.towerToBF64 (Spec.BinaryField.towerOf 6 t) ⦄ :=
  Proofs.Binary.poly64_from_bf64_spec t

/-- `From<Poly64> for BinaryField64` is the inverse of `towerToBF64`. -/
theorem tower.BinaryField64.Insts.CoreConvertFromPoly64.from.toQuot64 (p : poly64.Poly64) :
    tower.BinaryField64.Insts.CoreConvertFromPoly64.from p ⦃ t =>
      Proofs.Binary.towerToBF64 (Spec.BinaryField.towerOf 6 t) = toQuot64 p ⦄ :=
  Proofs.Binary.bf64_from_poly64_spec p

/-- `towerToBF64` is injective. -/
theorem Proofs.Binary.towerToBF64.injective' :
    Function.Injective Proofs.Binary.towerToBF64 :=
  Proofs.Binary.towerToBF64_injective

/-! ## The Cantor basis -/

/-- Vector `0` of the Cantor basis is `1`. -/
theorem Proofs.Binary.cantorTower.zero' (k : ℕ) :
    Proofs.Binary.cantorTower k 0 = 1 :=
  Proofs.Binary.cantorTower_zero k

/-- `v_i^2 + v_i = v_(i-1)`. -/
theorem Proofs.Binary.cantorTower.succ' {k : ℕ} (hk : k ≤ 7) {i : ℕ} (hi : i + 1 < 2 ^ k) :
    Proofs.Binary.cantorTower k (i + 1) ^ 2 + Proofs.Binary.cantorTower k (i + 1) = Proofs.Binary.cantorTower k i :=
  Proofs.Binary.cantorTower_succ hk hi

/-- Each root is the one whose lowest bit is clear. -/
theorem Proofs.Binary.cantorV.even' (i : ℕ) (h1 : 1 ≤ i) (h2 : i < 128) :
    Proofs.Binary.cantorV i % 2 = 0 :=
  Proofs.Binary.cantorV_even i h1 h2

/-- The first `2^k` vectors span level `k`. -/
theorem Proofs.Binary.cantorTower.span' {k : ℕ} (hk : k ≤ 7) (x : ConcreteBTField k) :
    ∃ w < 2 ^ 2 ^ k, x = ∑ i ∈ Finset.range (2 ^ k), if w.testBit i then Proofs.Binary.cantorTower k i else 0 :=
  Proofs.Binary.cantor_basis_span hk x

/-- The first `2^k` vectors are independent. -/
theorem Proofs.Binary.cantorTower.indep' {k : ℕ} (hk : k ≤ 7) {w : ℕ} (hw : w < 2 ^ 2 ^ k)
    (h : (∑ i ∈ Finset.range (2 ^ k), if w.testBit i then Proofs.Binary.cantorTower k i else 0) = 0) :
    w = 0 :=
  Proofs.Binary.cantor_basis_indep hk hw h

/-- `cantor_basis i` is vector `i` of the Cantor basis. -/
theorem gf2.Gf2.Insts.P3_binary_fieldTowerTowerLevelU8.cantor_basis.towerOf (i : Std.Usize) (hi : i.val < 1) :
    gf2.Gf2.Insts.P3_binary_fieldTowerTowerLevelU8.cantor_basis i ⦃ r => Spec.BinaryField.towerOf 0 r = Proofs.Binary.cantorTower 0 i.val ⦄ :=
  Proofs.Binary.gf2_cantor_basis_spec i hi

/-- `cantor_basis` panics past the level's width. -/
theorem gf2.Gf2.Insts.P3_binary_fieldTowerTowerLevelU8.cantor_basis.panics (i : Std.Usize) (hi : 1 ≤ i.val) :
    gf2.Gf2.Insts.P3_binary_fieldTowerTowerLevelU8.cantor_basis i = .fail .panic :=
  Proofs.Binary.gf2_cantor_basis_panic i hi

/-- `cantor_basis i` is vector `i` of the Cantor basis. -/
theorem tower.BinaryField2.Insts.P3_binary_fieldTowerTowerLevelU8.cantor_basis.towerOf (i : Std.Usize) (hi : i.val < 2) :
    tower.BinaryField2.Insts.P3_binary_fieldTowerTowerLevelU8.cantor_basis i ⦃ r => Spec.BinaryField.towerOf 1 r = Proofs.Binary.cantorTower 1 i.val ⦄ :=
  Proofs.Binary.bf2_cantor_basis_spec i hi

/-- `cantor_basis` panics past the level's width. -/
theorem tower.BinaryField2.Insts.P3_binary_fieldTowerTowerLevelU8.cantor_basis.panics (i : Std.Usize) (hi : 2 ≤ i.val) :
    tower.BinaryField2.Insts.P3_binary_fieldTowerTowerLevelU8.cantor_basis i = .fail .panic :=
  Proofs.Binary.bf2_cantor_basis_panic i hi

/-- `cantor_basis i` is vector `i` of the Cantor basis. -/
theorem tower.BinaryField4.Insts.P3_binary_fieldTowerTowerLevelU8.cantor_basis.towerOf (i : Std.Usize) (hi : i.val < 4) :
    tower.BinaryField4.Insts.P3_binary_fieldTowerTowerLevelU8.cantor_basis i ⦃ r => Spec.BinaryField.towerOf 2 r = Proofs.Binary.cantorTower 2 i.val ⦄ :=
  Proofs.Binary.bf4_cantor_basis_spec i hi

/-- `cantor_basis` panics past the level's width. -/
theorem tower.BinaryField4.Insts.P3_binary_fieldTowerTowerLevelU8.cantor_basis.panics (i : Std.Usize) (hi : 4 ≤ i.val) :
    tower.BinaryField4.Insts.P3_binary_fieldTowerTowerLevelU8.cantor_basis i = .fail .panic :=
  Proofs.Binary.bf4_cantor_basis_panic i hi

/-- `cantor_basis i` is vector `i` of the Cantor basis. -/
theorem tower.BinaryField8.Insts.P3_binary_fieldTowerTowerLevelU8.cantor_basis.towerOf (i : Std.Usize) (hi : i.val < 8) :
    tower.BinaryField8.Insts.P3_binary_fieldTowerTowerLevelU8.cantor_basis i ⦃ r => Spec.BinaryField.towerOf 3 r = Proofs.Binary.cantorTower 3 i.val ⦄ :=
  Proofs.Binary.bf8_cantor_basis_spec i hi

/-- `cantor_basis` panics past the level's width. -/
theorem tower.BinaryField8.Insts.P3_binary_fieldTowerTowerLevelU8.cantor_basis.panics (i : Std.Usize) (hi : 8 ≤ i.val) :
    tower.BinaryField8.Insts.P3_binary_fieldTowerTowerLevelU8.cantor_basis i = .fail .panic :=
  Proofs.Binary.bf8_cantor_basis_panic i hi

/-- `cantor_basis i` is vector `i` of the Cantor basis. -/
theorem tower.BinaryField16.Insts.P3_binary_fieldTowerTowerLevelU16.cantor_basis.towerOf (i : Std.Usize) (hi : i.val < 16) :
    tower.BinaryField16.Insts.P3_binary_fieldTowerTowerLevelU16.cantor_basis i ⦃ r => Spec.BinaryField.towerOf 4 r = Proofs.Binary.cantorTower 4 i.val ⦄ :=
  Proofs.Binary.bf16_cantor_basis_spec i hi

/-- `cantor_basis` panics past the level's width. -/
theorem tower.BinaryField16.Insts.P3_binary_fieldTowerTowerLevelU16.cantor_basis.panics (i : Std.Usize) (hi : 16 ≤ i.val) :
    tower.BinaryField16.Insts.P3_binary_fieldTowerTowerLevelU16.cantor_basis i = .fail .panic :=
  Proofs.Binary.bf16_cantor_basis_panic i hi

/-- `cantor_basis i` is vector `i` of the Cantor basis. -/
theorem tower.BinaryField32.Insts.P3_binary_fieldTowerTowerLevelU32.cantor_basis.towerOf (i : Std.Usize) (hi : i.val < 32) :
    tower.BinaryField32.Insts.P3_binary_fieldTowerTowerLevelU32.cantor_basis i ⦃ r => Spec.BinaryField.towerOf 5 r = Proofs.Binary.cantorTower 5 i.val ⦄ :=
  Proofs.Binary.bf32_cantor_basis_spec i hi

/-- `cantor_basis` panics past the level's width. -/
theorem tower.BinaryField32.Insts.P3_binary_fieldTowerTowerLevelU32.cantor_basis.panics (i : Std.Usize) (hi : 32 ≤ i.val) :
    tower.BinaryField32.Insts.P3_binary_fieldTowerTowerLevelU32.cantor_basis i = .fail .panic :=
  Proofs.Binary.bf32_cantor_basis_panic i hi

/-- `cantor_basis i` is vector `i` of the Cantor basis. -/
theorem tower.BinaryField64.Insts.P3_binary_fieldTowerTowerLevelU64.cantor_basis.towerOf (i : Std.Usize) (hi : i.val < 64) :
    tower.BinaryField64.Insts.P3_binary_fieldTowerTowerLevelU64.cantor_basis i ⦃ r => Spec.BinaryField.towerOf 6 r = Proofs.Binary.cantorTower 6 i.val ⦄ :=
  Proofs.Binary.bf64_cantor_basis_spec i hi

/-- `cantor_basis` panics past the level's width. -/
theorem tower.BinaryField64.Insts.P3_binary_fieldTowerTowerLevelU64.cantor_basis.panics (i : Std.Usize) (hi : 64 ≤ i.val) :
    tower.BinaryField64.Insts.P3_binary_fieldTowerTowerLevelU64.cantor_basis i = .fail .panic :=
  Proofs.Binary.bf64_cantor_basis_panic i hi

/-- `cantor_basis i` is vector `i` of the Cantor basis. -/
theorem tower.BinaryField128.Insts.P3_binary_fieldTowerTowerLevelU128.cantor_basis.towerOf (i : Std.Usize) (hi : i.val < 128) :
    tower.BinaryField128.Insts.P3_binary_fieldTowerTowerLevelU128.cantor_basis i ⦃ r => Spec.BinaryField.towerOf 7 r = Proofs.Binary.cantorTower 7 i.val ⦄ :=
  Proofs.Binary.bf128_cantor_basis_spec i hi

/-- `cantor_basis` panics past the level's width. -/
theorem tower.BinaryField128.Insts.P3_binary_fieldTowerTowerLevelU128.cantor_basis.panics (i : Std.Usize) (hi : 128 ≤ i.val) :
    tower.BinaryField128.Insts.P3_binary_fieldTowerTowerLevelU128.cantor_basis i = .fail .panic :=
  Proofs.Binary.bf128_cantor_basis_panic i hi

/-- `Ghash128::cantor_basis i` is vector `i` of the Cantor basis, through `towerToGhash`. -/
theorem ghash.Ghash128.Insts.P3_binary_fieldTowerTowerLevelU128.cantor_basis.toGhash (i : Std.Usize) (hi : i.val < 128) :
    ghash.Ghash128.Insts.P3_binary_fieldTowerTowerLevelU128.cantor_basis i ⦃ r =>
      toQuot (ghash r) = Proofs.Binary.towerToGhash (Proofs.Binary.cantorTower 7 i.val) ⦄ :=
  Proofs.Binary.ghash128_cantor_basis_spec i hi

/-- `cantor_basis` panics past 128. -/
theorem ghash.Ghash128.Insts.P3_binary_fieldTowerTowerLevelU128.cantor_basis.panics (i : Std.Usize) (hi : 128 ≤ i.val) :
    ghash.Ghash128.Insts.P3_binary_fieldTowerTowerLevelU128.cantor_basis i = .fail .panic :=
  Proofs.Binary.ghash128_cantor_basis_panic i hi

/-- `Poly64::cantor_basis i` is vector `i` of the Cantor basis, through `towerToBF64`. -/
theorem poly64.Poly64.Insts.P3_binary_fieldTowerTowerLevelU64.cantor_basis.toQuot64 (i : Std.Usize) (hi : i.val < 64) :
    poly64.Poly64.Insts.P3_binary_fieldTowerTowerLevelU64.cantor_basis i ⦃ r =>
      toQuot64 r = Proofs.Binary.towerToBF64 (Proofs.Binary.cantorTower 6 i.val) ⦄ :=
  Proofs.Binary.poly64_cantor_basis_spec i hi

/-- `cantor_basis` panics past 64. -/
theorem poly64.Poly64.Insts.P3_binary_fieldTowerTowerLevelU64.cantor_basis.panics (i : Std.Usize) (hi : 64 ≤ i.val) :
    poly64.Poly64.Insts.P3_binary_fieldTowerTowerLevelU64.cantor_basis i = .fail .panic :=
  Proofs.Binary.poly64_cantor_basis_panic i hi

end Plonky3Lean.Claims.P3BinaryField
