/-
Copyright (c) 2026 CompPoly. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Coratger
-/
module

public import CompPoly.Fields.KoalaBear
public import Mathlib.FieldTheory.Finite.Basic
public import ToCompPoly.Data.Nat.PowMod

/-!
  # KoalaBear: cube roots

  Additions to `CompPoly.Fields.KoalaBear`:
  - `x ↦ x ^ 1420470955` inverts `x ↦ x ^ 3`, since `3 · 1420470955 ≡ 1 (mod p - 1)`;
  - `natCast_pow_ne_one`, a kernel-checkable test that a power of a numeral is not `1`.

  Both are kernel-checked, without `native_decide`.
-/

@[expose] public section

namespace KoalaBear

/-- A nonzero power of a natural number in the field, checked through `Nat.powMod`. -/
theorem natCast_pow_ne_one {e : ℕ} (b : ℕ)
    (h : (Nat.powMod b e fieldSize : Field) ≠ 1) :
    (b : Field) ^ e ≠ 1 := by
  rwa [ZMod.natCast_pow_eq_powMod b e]

/-- `x ↦ x ^ 1420470955` is the inverse of `x ↦ x ^ 3`: `3 · 1420470955 ≡ 1 (mod p - 1)`. -/
theorem pow_1420470955_pow_three (x : Field) : (x ^ 1420470955) ^ 3 = x := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · rw [← pow_mul, show 1420470955 * 3 = 2 * (fieldSize - 1) + 1 by decide,
      pow_succ, pow_mul', ZMod.pow_card_sub_one_eq_one hx, one_pow, one_mul]

end KoalaBear
