/-
Copyright (c) 2026 CompPoly. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Derek Sorensen
-/
import CompPoly.Fields.BabyBear
import Mathlib.FieldTheory.Finite.Basic
import ToCompPoly.Data.Nat.PowMod

/-!
  # BabyBear: a multiplicative generator and seventh roots

  Additions to `CompPoly.Fields.BabyBear`:
  - `generator = 31` generates the multiplicative group;
  - `x ↦ x ^ 1725656503` inverts `x ↦ x ^ 7`, since `7 · 1725656503 ≡ 1 (mod p - 1)`.

  Both are kernel-checked, without `native_decide`.
-/

namespace BabyBear

/-- A nonzero power of a natural number in the field, checked through `Nat.powMod`. -/
theorem natCast_pow_ne_one {e : ℕ} (b : ℕ) (he : e < 2 ^ 64)
    (h : (Nat.powMod b e fieldSize : Field) ≠ 1) :
    (b : Field) ^ e ≠ 1 := by
  rwa [ZMod.natCast_pow_eq_powMod b e he]

/-- The primes dividing `p - 1 = 2 ^ 27 · 3 · 5`. -/
theorem prime_dvd_fieldSize_sub_one {q : ℕ} (hq : q.Prime) (h : q ∣ fieldSize - 1) :
    q = 2 ∨ q = 3 ∨ q = 5 := by
  rw [show fieldSize - 1 = 2 ^ 27 * 3 * 5 by decide] at h
  rcases (Nat.Prime.dvd_mul hq).mp h with h | h
  · rcases (Nat.Prime.dvd_mul hq).mp h with h | h
    · exact .inl ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp (hq.dvd_of_dvd_pow h))
    · exact .inr (.inl ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp h))
  · exact .inr (.inr ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_five).mp h))

/-- A generator of the multiplicative group of the BabyBear field. -/
@[reducible]
def generator : Field := 31

/-- `generator` has order `p - 1`. -/
theorem orderOf_generator : orderOf generator = fieldSize - 1 := by
  show orderOf (31 : Field) = fieldSize - 1
  apply orderOf_eq_of_pow_and_pow_div_prime (by decide)
  · exact ZMod.pow_card_sub_one_eq_one (by decide)
  · intro q hq hdvd
    rcases prime_dvd_fieldSize_sub_one hq hdvd with rfl | rfl | rfl <;>
    · exact_mod_cast natCast_pow_ne_one 31 (by unfold fieldSize; norm_num) (by decide)

/-- `x ↦ x ^ 1725656503` is the inverse of `x ↦ x ^ 7`: `7 · 1725656503 ≡ 1 (mod p - 1)`. -/
theorem pow_1725656503_pow_seven (x : Field) : (x ^ 1725656503) ^ 7 = x := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · rw [← pow_mul, show 1725656503 * 7 = 6 * (fieldSize - 1) + 1 by decide,
      pow_succ, pow_mul', ZMod.pow_card_sub_one_eq_one hx, one_pow, one_mul]

end BabyBear
