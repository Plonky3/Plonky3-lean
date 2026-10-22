module

public import Aeneas
public import CompPoly.Fields.Binary.Common
public import ToCompPoly.Fields.Binary.Poly192.Basic
public import CompPoly.Fields.Binary.Tower.Impl

@[expose] public section

/-!
# Binary fields: what the model's integers mean

An integer of the model stands for a polynomial over `GF(2)`.

- Bit `i` is the coefficient of `X ^ i`.
- This is CompPoly's `toPoly`, applied to the integer's bit vector.

A carry-less product is then a product of polynomials, and a reduction is a remainder.

- A 64-bit integer stands for an element of `GF(2)[X] / (X^64 + X^4 + X^3 + X + 1)`.
- Three 64-bit limbs `[a_0, a_1, a_2]` stand for `a_0 + a_1 Y + a_2 Y^2` in
  `GF(2^64)[Y] / (Y^3 + Y + 1)`.
- A 128-bit integer stands for an element of the GHASH field, through CompPoly's `toQuot`.
- An 8-bit integer stands for an element of CompPoly's tower field `GF(2^8)`, bit for bit.
-/

open Aeneas Aeneas.Std Polynomial

namespace Plonky3Lean.Spec.BinaryField

/-- The polynomial over `GF(2)` an unsigned integer stands for: bit `i` is the coefficient of
`X ^ i`. -/
noncomputable def poly {ty : UScalarTy} (x : UScalar ty) : (ZMod 2)[X] :=
  _root_.BinaryField.toPoly x.bv

/-- The element of `GF(2)[X] / (X^64 + X^4 + X^3 + X + 1)` a 64-bit integer stands for. -/
noncomputable def toQuot64 (x : Std.U64) : Poly64.Quot := AdjoinRoot.mk Poly64.modulus (poly x)

/-- The element `a_0 + a_1 Y + a_2 Y^2` of `GF(2^64)[Y] / (Y^3 + Y + 1)` three 64-bit limbs
stand for. -/
noncomputable def toQuot192 (a : Std.Array Std.U64 3#usize) : Poly192.Quot :=
  Poly192.ofCoeffs (toQuot64 (a.val.getD 0 0#u64)) (toQuot64 (a.val.getD 1 0#u64))
    (toQuot64 (a.val.getD 2 0#u64))

/-- The element of the tower's `GF(2^8)`, CompPoly's `ConcreteBTField 3`, an 8-bit integer stands
for: its bits are the element's bits. -/
def tower8 (x : Std.U8) : ConcreteBinaryTower.ConcreteBTField 3 := x.bv

end Plonky3Lean.Spec.BinaryField
