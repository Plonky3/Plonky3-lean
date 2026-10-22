import Plonky3Lean.Proofs.Field.Binary.Poly64Irreducible

/-!
# `GF(2^64)` is a field, and `poly_inverse_64` inverts in it

- The modulus is irreducible, so the quotient is a field.
- Every element satisfies `x^(2^64) = x`, since `X` does.
- `x^(2^64 - 2)`, which `poly_inverse_64` computes, is then `x⁻¹`, and `0` for `x = 0`.
-/

open Aeneas Aeneas.Std CoreModels Polynomial
open p3_binary_field BinaryField
open Plonky3Lean.Lib Plonky3Lean.Spec.BinaryField

namespace Plonky3Lean.Proofs.Binary

/-- Over `GF(2)`, raising to `2^k` is expanding by `2^k`. -/
theorem pow_two_pow_eq_expand (p : (ZMod 2)[X]) (k : ℕ) : p ^ 2 ^ k = expand (ZMod 2) (2 ^ k) p := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, pow_mul, ih, ← ZMod.expand_card, expand_expand, mul_comm]

/-- If `X^(2^k) = X` in `GF(2)[X] / (P)`, then every element is fixed by `x ↦ x^(2^k)`. -/
theorem pow_two_pow_eq_self_of_X {P : (ZMod 2)[X]} {k : ℕ}
    (hX : AdjoinRoot.mk P X ^ 2 ^ k = AdjoinRoot.mk P X) (x : AdjoinRoot P) : x ^ 2 ^ k = x := by
  rw [AdjoinRoot.mk_X] at hX
  induction x using AdjoinRoot.induction_on with
  | ih p =>
    rw [← map_pow, pow_two_pow_eq_expand, coe_expand, ← AdjoinRoot.aeval_eq,
      ← AdjoinRoot.aeval_eq, aeval_def, aeval_def,
      show eval₂ C (X ^ 2 ^ k) p = p.comp (X ^ 2 ^ k) from rfl, eval₂_comp, eval₂_X_pow, hX]

instance : Fact (Irreducible Poly64.modulus) := ⟨modulus_irreducible⟩

/-- Every element of `GF(2^64)` is fixed by `x ↦ x^(2^64)`. -/
theorem pow_two_pow_64 (x : Poly64.Quot) : x ^ 2 ^ 64 = x := by
  refine pow_two_pow_eq_self_of_X ?_ x
  rw [← (frobX_spec 64 le_rfl).2, show frobX 64 = 2 by decide +kernel, natPoly_two]

/-- `x^(2^64 - 2)` is the inverse in `GF(2^64)`, and `0` at `0`. -/
theorem pow_two_pow_64_sub_two (x : Poly64.Quot) : x ^ (2 ^ 64 - 2) = x⁻¹ := by
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
