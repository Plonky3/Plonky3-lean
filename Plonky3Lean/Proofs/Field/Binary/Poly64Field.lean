module

public import Plonky3Lean.Proofs.Field.Binary.Poly64Halves

@[expose] public section

/-!
# `poly_inverse_64` inverts in `GF(2^64)`

- CompPoly's `BF64.BF64Quot` is a field with `2^64` elements, so `x^(2^64) = x`.
- `x^(2^64 - 2)`, which `poly_inverse_64` computes, is then `x⁻¹`, and `0` for `x = 0`.
-/

open Aeneas Aeneas.Std CoreModels Polynomial
open p3_binary_field BinaryField
open Plonky3Lean.Lib Plonky3Lean.Spec.BinaryField

namespace Plonky3Lean.Proofs.Binary

/-- Every element of `GF(2^64)` is fixed by `x ↦ x^(2^64)`: the field has `2^64` elements. -/
theorem pow_two_pow_64 (x : BF64.BF64Quot) : x ^ 2 ^ 64 = x := by
  rw [← BF64.card_bf64Quot]
  exact FiniteField.pow_card x

/-- `x^(2^64 - 2)` is the inverse in `GF(2^64)`, and `0` at `0`. -/
theorem pow_two_pow_64_sub_two (x : BF64.BF64Quot) : x ^ (2 ^ 64 - 2) = x⁻¹ := by
  by_cases hx : x = 0
  · rw [hx, inv_zero, zero_pow (by norm_num)]
  · have h := pow_two_pow_64 x
    rw [show (2 : ℕ) ^ 64 = (2 ^ 64 - 2) + 1 + 1 by norm_num, pow_succ, pow_succ] at h
    have h1 : x ^ (2 ^ 64 - 2) * x = 1 := by
      have := congrArg (· * x⁻¹) h
      simpa [mul_assoc, mul_inv_cancel₀ hx] using this
    exact eq_inv_of_mul_eq_one_left h1

/-- `poly_inverse_64` never panics and returns the inverse in `GF(2^64)`, and `0` at `0`. -/
theorem poly_inverse_64_inv (x : Std.U64) :
    clmul.gf64.poly_inverse_64 x ⦃ r => toQuot64 r = (toQuot64 x)⁻¹ ⦄ := by
  apply WP.spec_mono (poly_inverse_64_toQuot x)
  intro r hr
  rw [hr, pow_two_pow_64_sub_two]

end Plonky3Lean.Proofs.Binary
