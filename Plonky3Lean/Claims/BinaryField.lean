module

public import Plonky3Lean.Proofs.Field.Binary.Operators

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
  - level `k` of the binary tower, `GF(2^(2^k))`, is `ConcreteBTField k`, read through `towerOf k`
    from the low `2^k` bits.
- CompPoly proves each of these is a field.

Every claim holds for every input, unless it states a hypothesis.

`m ⦃ r => P r ⦄` states that `m` returns a value `r`, so it does not panic, and that `P r` holds.

Not claimed:
- the trait methods of the field types (`square`, `try_inverse`, `Field`, `ExtensionField`, ...),
  which the extraction cannot reach;
- the basis conversions, the dot products, the AES and bit-plane code, the challenger and
  transcript, and the packed arithmetic;
- the hardware kernels (PCLMULQDQ, PMULL, GFNI), which the extraction target does not have.
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


end Plonky3Lean.Claims.P3BinaryField
