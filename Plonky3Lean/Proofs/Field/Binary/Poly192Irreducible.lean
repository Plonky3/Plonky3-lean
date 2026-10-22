import Mathlib.Algebra.Polynomial.SpecificDegree
import Plonky3Lean.Proofs.Field.Binary.Poly192
import Plonky3Lean.Proofs.Field.Binary.Poly64Field

/-!
# `Y^3 + Y + 1` is irreducible over `GF(2^64)`

A cubic is irreducible over a field when it has no root.

- Every element of `GF(2^64)` satisfies `x^(2^64) = x`, since `X` does.
- A root `r` satisfies `r^7 = 1`, and `2^64 ≡ 2 (mod 7)`, so `r = r^(2^64) = r^2`.
- Then `r = 1`, which is not a root.
-/

open Polynomial BinaryField

namespace Plonky3Lean.Proofs.Binary

theorem natDegree_poly192 : Poly192.modulus.natDegree = 3 := by
  unfold Poly192.modulus
  compute_degree!

theorem monic_poly192 : Poly192.modulus.Monic := by
  unfold Poly192.modulus
  monicity!

/-- `Y^3 + Y + 1` has no root in `GF(2^64)`. -/
theorem not_isRoot_poly192 (r : Poly64.Quot) : ¬ Poly192.modulus.IsRoot r := by
  intro h
  have h2 := two_eq_zero_quot64
  have hr : r ^ 3 + r + 1 = 0 := by
    simpa [Poly192.modulus] using h
  have h3 : r ^ 3 = r + 1 := by linear_combination hr - (r + 1) * h2
  have h7 : r ^ 7 = 1 := by
    have : r ^ 7 = (r ^ 3) ^ 2 * r := by ring
    rw [this, h3]
    linear_combination h3 + (r ^ 2 + r) * h2
  have hsq : r ^ 2 = r := by
    have e : (2 : ℕ) ^ 64 = 7 * 2635249153387078802 + 2 := by norm_num
    have := pow_two_pow_64 r
    rwa [e, pow_add, pow_mul, h7, one_pow, one_mul] at this
  have hr0 : r ≠ 0 := by
    rintro rfl
    simp at hr
  have h1 : r = 1 := by
    have : r * (r - 1) = 0 := by linear_combination hsq
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h hr0
    · exact sub_eq_zero.mp h
  rw [h1] at hr
  have : (1 : Poly64.Quot) = 0 := by linear_combination hr - h2
  exact one_ne_zero this

/-- `Y^3 + Y + 1` is irreducible over `GF(2^64)`. -/
theorem poly192_irreducible : Irreducible Poly192.modulus := by
  rw [Monic.irreducible_iff_roots_eq_zero_of_degree_le_three monic_poly192
    (by rw [natDegree_poly192]; norm_num) (by rw [natDegree_poly192])]
  exact Multiset.eq_zero_iff_forall_notMem.mpr fun r hr =>
    not_isRoot_poly192 r ((mem_roots monic_poly192.ne_zero).mp hr)

end Plonky3Lean.Proofs.Binary
