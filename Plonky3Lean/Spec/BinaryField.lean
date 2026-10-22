import Aeneas
import CompPoly.Fields.Binary.Common

/-!
# Binary fields: what the model's integers mean

An integer of the model stands for a polynomial over `GF(2)`.

- Bit `i` is the coefficient of `X ^ i`.
- This is CompPoly's `toPoly`, applied to the integer's bit vector.

A carry-less product is then a product of polynomials, and a reduction is a remainder.
-/

open Aeneas Aeneas.Std Polynomial

namespace Plonky3Lean.Spec.BinaryField

/-- The polynomial over `GF(2)` an unsigned integer stands for: bit `i` is the coefficient of
`X ^ i`. -/
noncomputable def poly {ty : UScalarTy} (x : UScalar ty) : (ZMod 2)[X] :=
  _root_.BinaryField.toPoly x.bv

end Plonky3Lean.Spec.BinaryField
