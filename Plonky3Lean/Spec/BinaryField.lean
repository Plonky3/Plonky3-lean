module

public import Aeneas
public import CompPoly.Fields.Binary.Common
public import CompPoly.Fields.Binary.BF64.Ext3
public import CompPoly.Fields.Binary.Tower.Impl
public import CompPoly.Fields.Binary.BF128Ghash.Impl

@[expose] public section

/-!
# Binary fields: what the model's integers mean

An integer of the model stands for a polynomial over `GF(2)`.

- Bit `i` is the coefficient of `X ^ i`.
- This is CompPoly's `toPoly`, applied to the integer's bit vector.

A carry-less product is then a product of polynomials, and a reduction is a remainder.

Every field below is CompPoly's:

- A 64-bit integer stands for an element of `BF64`, `GF(2)[X] / (X^64 + X^4 + X^3 + X + 1)`.
- Three 64-bit limbs `[a_0, a_1, a_2]` stand for `a_0 + a_1 Y + a_2 Y^2` in `BF64.Ext3`,
  `BF64[Y] / (Y^3 + Y + 1)`.
- A 128-bit integer stands for an element of the GHASH field, through `toQuot`.
- An integer stands for an element of the tower's level `k`, `ConcreteBTField k`, through its
  low `2^k` bits.
-/

open Aeneas Aeneas.Std Polynomial

namespace Plonky3Lean.Spec.BinaryField

/-- The polynomial over `GF(2)` an unsigned integer stands for: bit `i` is the coefficient of
`X ^ i`. -/
noncomputable def poly {ty : UScalarTy} (x : UScalar ty) : (ZMod 2)[X] :=
  _root_.BinaryField.toPoly x.bv

/-- The element of CompPoly's GHASH field a 128-bit integer stands for. -/
def ghash (x : Std.U128) : BF128Ghash.ConcreteBF128Ghash := BF128Ghash.ofBitVec x.bv

/-- The element of CompPoly's `BF64` a 64-bit integer stands for. -/
def bf64 (x : Std.U64) : BF64 := BF64.ofBitVec x.bv

/-- The element of `GF(2)[X] / (X^64 + X^4 + X^3 + X + 1)` a 64-bit integer stands for:
CompPoly's quotient image of `bf64 x`. -/
noncomputable def toQuot64 (x : Std.U64) : BF64.BF64Quot := BF64.toQuot (bf64 x)

/-- The element `a_0 + a_1 Y + a_2 Y^2` of CompPoly's `BF64.Ext3` three 64-bit limbs stand
for. -/
def toExt3 (a : Std.Array Std.U64 3#usize) : BF64.Ext3 :=
  CompPoly.Extension.Ext.ofVector
    #v[bf64 (a.val.getD 0 0#u64), bf64 (a.val.getD 1 0#u64), bf64 (a.val.getD 2 0#u64)]

/-- The element of the tower's level `k`, CompPoly's `ConcreteBTField k`, an integer stands for:
the element whose bits are the integer's low `2^k` bits. -/
def towerOf (k : ℕ) {ty : UScalarTy} (x : UScalar ty) : ConcreteBinaryTower.ConcreteBTField k :=
  ConcreteBinaryTower.fromNat x.val

/-- The element of the tower's `GF(2^8)` an 8-bit integer stands for. -/
def tower8 (x : Std.U8) : ConcreteBinaryTower.ConcreteBTField 3 := towerOf 3 x

end Plonky3Lean.Spec.BinaryField
