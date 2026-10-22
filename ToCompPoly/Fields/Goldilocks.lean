/-
Copyright (c) 2026 CompPoly. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Coratger
-/
import CompPoly.Fields.Goldilocks
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic.NormNum.Prime
import ToCompPoly.Data.Nat.PowMod

/-!
  # Goldilocks: two-adicity, a generator and a primitive `2^32`-th root of unity

  Additions to `CompPoly.Fields.Goldilocks`:
  - `p - 1 = 2^32 (2^32 - 1)`, so the two-adicity is `32`;
  - `generator = 7` generates the multiplicative group;
  - `twoAdicGenerator = 7^((p - 1) / 2^32)` has order `2^32`;
  - `x ↦ x ^ 10540996611094048183` inverts `x ↦ x ^ 7`.

  All are kernel-checked, without `native_decide`.
-/

namespace Goldilocks

instance : Fact (Nat.Prime fieldSize) := ⟨is_prime⟩

/-- The largest `k` with `2^k` dividing `p - 1`. -/
@[reducible]
def twoAdicity : ℕ := 32

/-- `p - 1 = 2^32 (2^32 - 1)`. -/
theorem fieldSize_sub_one_factorization : fieldSize - 1 = 2 ^ twoAdicity * (2 ^ 32 - 1) := by
  decide

/-- `2^33` does not divide `p - 1`. -/
theorem twoAdicity_maximal : ¬ 2 ^ (twoAdicity + 1) ∣ fieldSize - 1 := by
  decide

/-- A power of a natural number in the field is not `1`, checked through `Nat.powMod`. -/
theorem natCast_pow_ne_one {e : ℕ} (b : ℕ) (he : e < 2 ^ 64)
    (h : (Nat.powMod b e fieldSize : Field) ≠ 1) :
    (b : Field) ^ e ≠ 1 := by
  rwa [ZMod.natCast_pow_eq_powMod b e he]

/-- The primes dividing `p - 1 = 2^32 · 3 · 5 · 17 · 257 · 65537`. -/
theorem prime_dvd_fieldSize_sub_one {q : ℕ} (hq : q.Prime) (h : q ∣ fieldSize - 1) :
    q = 2 ∨ q = 3 ∨ q = 5 ∨ q = 17 ∨ q = 257 ∨ q = 65537 := by
  have p257 : Nat.Prime 257 := by norm_num
  have p65537 : Nat.Prime 65537 := by norm_num
  have p17 : Nat.Prime 17 := by norm_num
  rw [show fieldSize - 1 = 2 ^ 32 * 3 * 5 * 17 * 257 * 65537 by decide] at h
  have e : ∀ r : ℕ, r.Prime → q ∣ r → q = r := fun r hr hd =>
    (Nat.prime_dvd_prime_iff_eq hq hr).mp hd
  rcases (Nat.Prime.dvd_mul hq).mp h with h | h
  · rcases (Nat.Prime.dvd_mul hq).mp h with h | h
    · rcases (Nat.Prime.dvd_mul hq).mp h with h | h
      · rcases (Nat.Prime.dvd_mul hq).mp h with h | h
        · rcases (Nat.Prime.dvd_mul hq).mp h with h | h
          · exact .inl (e 2 Nat.prime_two (hq.dvd_of_dvd_pow h))
          · exact .inr (.inl (e 3 Nat.prime_three h))
        · exact .inr (.inr (.inl (e 5 Nat.prime_five h)))
      · exact .inr (.inr (.inr (.inl (e 17 p17 h))))
    · exact .inr (.inr (.inr (.inr (.inl (e 257 p257 h)))))
  · exact .inr (.inr (.inr (.inr (.inr (e 65537 p65537 h)))))

/-- A generator of the multiplicative group. -/
@[reducible]
def generator : Field := 7

/-- `generator` has order `p - 1`. -/
theorem orderOf_generator : orderOf generator = fieldSize - 1 := by
  show orderOf (7 : Field) = fieldSize - 1
  apply orderOf_eq_of_pow_and_pow_div_prime (by decide)
  · exact ZMod.pow_card_sub_one_eq_one (by decide)
  · intro q hq hdvd
    rcases prime_dvd_fieldSize_sub_one hq hdvd with rfl | rfl | rfl | rfl | rfl | rfl <;>
    · exact_mod_cast natCast_pow_ne_one 7 (by unfold fieldSize; norm_num) (by decide)

/-- A primitive `2^32`-th root of unity: `7^((p - 1) / 2^32)`. -/
@[reducible]
def twoAdicGenerator : Field := 0x185629dcda58878c

/-- `twoAdicGenerator` is `generator ^ ((p - 1) / 2^32)`. -/
theorem twoAdicGenerator_eq : twoAdicGenerator = generator ^ ((fieldSize - 1) / 2 ^ 32) := by
  show ((0x185629dcda58878c : ℕ) : Field) = ((7 : ℕ) : Field) ^ ((fieldSize - 1) / 2 ^ 32)
  rw [ZMod.natCast_pow_eq_powMod 7 _ (by unfold fieldSize; norm_num)]
  decide

/-- `twoAdicGenerator` has order `2^32`. -/
theorem orderOf_twoAdicGenerator : orderOf twoAdicGenerator = 2 ^ twoAdicity := by
  rw [twoAdicGenerator_eq, orderOf_pow_of_dvd (by decide), orderOf_generator,
    fieldSize_sub_one_factorization]
  · decide
  · rw [orderOf_generator, fieldSize_sub_one_factorization]
    exact Dvd.intro_left _ rfl

/-- `x ↦ x ^ 10540996611094048183` inverts `x ↦ x ^ 7`: `7 · 10540996611094048183 ≡ 1 (mod p - 1)`. -/
theorem pow_10540996611094048183_pow_seven (x : Field) : (x ^ 10540996611094048183) ^ 7 = x := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · rw [← pow_mul, show 10540996611094048183 * 7 = 4 * (fieldSize - 1) + 1 by decide,
      pow_succ, pow_mul', ZMod.pow_card_sub_one_eq_one hx, one_pow, one_mul]

end Goldilocks
