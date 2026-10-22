/-
Copyright (c) 2026 CompPoly. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Derek Sorensen
-/
module

public import Mathlib.Data.ZMod.Basic
/-!
# Powers in `ZMod m` through core's `Nat.powMod`

Facts about concrete field elements, such as `31 ^ ((p - 1) / 2) ≠ 1` in `ZMod p`, need
`a ^ e` evaluated for large exponents. Core's `Nat.powMod` reduces in `O(log e)` steps
under `decide`; `ZMod.natCast_pow_eq_powMod` moves a power in `ZMod m` onto it.
-/

@[expose] public section

/-- A power of a natural number in `ZMod m`, as core's `Nat.powMod`. -/
theorem ZMod.natCast_pow_eq_powMod {m : ℕ} (b e : ℕ) :
    (b : ZMod m) ^ e = (Nat.powMod b e m : ZMod m) := by
  rw [Nat.powMod_def, ZMod.natCast_mod]; push_cast; rfl
