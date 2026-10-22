/-
Copyright (c) 2026 CompPoly. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Coratger
-/
import CompPoly.Fields.Mersenne
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic.NormNum.Prime
import ToCompPoly.Data.Nat.PowMod

/-!
  # Mersenne31: the field, a multiplicative generator, fifth roots, non-residues

  Additions to `CompPoly.Fields.Mersenne`:
  - the `Field` instance on `Mersenne31.Field`;
  - `generator = 7` generates the multiplicative group;
  - `x ↦ x ^ 1717986917` inverts `x ↦ x ^ 5`, since `5 · 1717986917 ≡ 1 (mod p - 1)`;
  - `-1` and `5` are not squares, and `5` is not a cube.

  Everything is kernel-checked, without `native_decide`.
-/

namespace Mersenne31

instance : Fact (Nat.Prime fieldSize) := ⟨is_prime⟩

instance : _root_.Field Field := ZMod.instField fieldSize

/-- A power of a natural number in the field, checked through `Nat.powMod`. -/
theorem natCast_pow_eq {e : ℕ} (b c : ℕ) (he : e < 2 ^ 64) (h : Nat.powMod b e fieldSize = c) :
    (b : Field) ^ e = c := by
  rw [ZMod.natCast_pow_eq_powMod b e he, h]

/-- A nonzero power of a natural number in the field, checked through `Nat.powMod`. -/
theorem natCast_pow_ne_one {e : ℕ} (b : ℕ) (he : e < 2 ^ 64)
    (h : (Nat.powMod b e fieldSize : Field) ≠ 1) :
    (b : Field) ^ e ≠ 1 := by
  rwa [ZMod.natCast_pow_eq_powMod b e he]

/-- The primes dividing `p - 1 = 2 · 3^2 · 7 · 11 · 31 · 151 · 331`. -/
theorem prime_dvd_fieldSize_sub_one {q : ℕ} (hq : q.Prime) (h : q ∣ fieldSize - 1) :
    q = 2 ∨ q = 3 ∨ q = 7 ∨ q = 11 ∨ q = 31 ∨ q = 151 ∨ q = 331 := by
  rw [show fieldSize - 1 = 2 * 3 ^ 2 * 7 * 11 * 31 * 151 * 331 by decide] at h
  have hp : ∀ r : ℕ, r.Prime → q ∣ r → q = r := fun r hr hd =>
    (Nat.prime_dvd_prime_iff_eq hq hr).mp hd
  rcases (Nat.Prime.dvd_mul hq).mp h with h | h
  · rcases (Nat.Prime.dvd_mul hq).mp h with h | h
    · rcases (Nat.Prime.dvd_mul hq).mp h with h | h
      · rcases (Nat.Prime.dvd_mul hq).mp h with h | h
        · rcases (Nat.Prime.dvd_mul hq).mp h with h | h
          · rcases (Nat.Prime.dvd_mul hq).mp h with h | h
            · exact .inl (hp 2 Nat.prime_two h)
            · exact .inr (.inl (hp 3 Nat.prime_three (hq.dvd_of_dvd_pow h)))
          · exact .inr (.inr (.inl (hp 7 (by norm_num) h)))
        · exact .inr (.inr (.inr (.inl (hp 11 (by norm_num) h))))
      · exact .inr (.inr (.inr (.inr (.inl (hp 31 (by norm_num) h)))))
    · exact .inr (.inr (.inr (.inr (.inr (.inl (hp 151 (by norm_num) h))))))
  · exact .inr (.inr (.inr (.inr (.inr (.inr (hp 331 (by norm_num) h))))))

/-- An element of order `p - 1` generates the multiplicative group: it suffices to check
`x ^ ((p - 1) / q) ≠ 1` for the seven primes `q` dividing `p - 1`. -/
theorem orderOf_eq_of_powMod (b : ℕ) (hb : (b : Field) ≠ 0)
    (h : ∀ q ∈ [2, 3, 7, 11, 31, 151, 331],
      (Nat.powMod b ((fieldSize - 1) / q) fieldSize : Field) ≠ 1) :
    orderOf (b : Field) = fieldSize - 1 := by
  apply orderOf_eq_of_pow_and_pow_div_prime (by decide)
  · exact ZMod.pow_card_sub_one_eq_one hb
  · intro q hq hdvd
    have he : (fieldSize - 1) / q < 2 ^ 64 :=
      lt_of_le_of_lt (Nat.div_le_self _ _) (by decide)
    refine natCast_pow_ne_one b he (h q ?_)
    rcases prime_dvd_fieldSize_sub_one hq hdvd with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp

/-- A generator of the multiplicative group of the Mersenne31 field. -/
@[reducible]
def generator : Field := 7

/-- `generator` has order `p - 1`. -/
theorem orderOf_generator : orderOf generator = fieldSize - 1 := by
  show orderOf ((7 : ℕ) : Field) = fieldSize - 1
  refine orderOf_eq_of_powMod 7 (by decide) ?_
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-- `x ↦ x ^ 1717986917` is the inverse of `x ↦ x ^ 5`: `5 · 1717986917 ≡ 1 (mod p - 1)`. -/
theorem pow_1717986917_pow_five (x : Field) : (x ^ 1717986917) ^ 5 = x := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · rw [← pow_mul, show 1717986917 * 5 = 4 * (fieldSize - 1) + 1 by unfold fieldSize; norm_num,
      pow_succ, pow_mul', ZMod.pow_card_sub_one_eq_one hx, one_pow, one_mul]

/-- If `b ^ n = a` for a nonzero `a`, then `a ^ ((p - 1) / n) = 1`. -/
theorem pow_div_eq_one_of_pow_eq {n : ℕ} (hn : n ∣ fieldSize - 1) {a b : Field} (ha : a ≠ 0)
    (h : b ^ n = a) : a ^ ((fieldSize - 1) / n) = 1 := by
  have hb : b ≠ 0 := by rintro rfl; exact ha (by rw [← h, zero_pow]; rintro rfl; simp at hn)
  rw [← h, ← pow_mul, Nat.mul_div_cancel' hn, ZMod.pow_card_sub_one_eq_one hb]

/-- `-1` is not a square, since `p ≡ 3 (mod 4)`. -/
theorem neg_one_ne_sq (b : Field) : b ^ 2 ≠ -1 := by
  intro h
  have := pow_div_eq_one_of_pow_eq (n := 2) (by decide) (by decide) h
  rw [Odd.neg_one_pow (by decide)] at this
  revert this; decide

/-- `5` is not a square. -/
theorem five_ne_sq (b : Field) : b ^ 2 ≠ 5 := by
  intro h
  have := pow_div_eq_one_of_pow_eq (n := 2) (by decide) (by decide) h
  rw [show (5 : Field) = ((5 : ℕ) : Field) by norm_num,
    natCast_pow_eq 5 2147483646 (by decide) (by decide)] at this
  revert this; decide

/-- `5` is not a cube. -/
theorem five_ne_cube (b : Field) : b ^ 3 ≠ 5 := by
  intro h
  have := pow_div_eq_one_of_pow_eq (n := 3) (by decide) (by decide) h
  rw [show (5 : Field) = ((5 : ℕ) : Field) by norm_num,
    natCast_pow_eq 5 1513477735 (by decide) (by decide)] at this
  revert this; decide

end Mersenne31
