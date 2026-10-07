import Mathlib.Data.ZMod.Basic

/-!
# Modular exponentiation the kernel can evaluate

Claims about field constants need facts like `31 ^ ((p - 1) / 2) ≠ 1 (mod p)`.
`decide` cannot evaluate `a ^ e` in `ZMod p` for exponents near `2^31`, and
`native_decide` would add `Lean.ofReduceBool` to the claim's axioms, which
`claims.toml` does not allow. `powMod` is square-and-multiply, structurally
recursive on a bit budget, so the kernel evaluates it in about `log₂ e` steps;
`zmod_pow_eq_powMod` moves a power in `ZMod m` onto it.
-/

namespace Plonky3Lean.Lib

/-- `powModAux fuel b e m = b ^ e % m` once `e < 2 ^ fuel`. -/
def powModAux : ℕ → ℕ → ℕ → ℕ → ℕ
  | 0, _, _, m => 1 % m
  | fuel + 1, b, e, m =>
    if e = 0 then 1 % m
    else
      let h := powModAux fuel (b * b % m) (e / 2) m
      if e % 2 = 1 then b * h % m else h

/-- `b ^ e % m`, for `e < 2 ^ 64`. -/
def powMod (b e m : ℕ) : ℕ := powModAux 64 b e m

theorem powModAux_eq (fuel b e m : ℕ) (he : e < 2 ^ fuel) :
    powModAux fuel b e m = b ^ e % m := by
  induction fuel generalizing b e with
  | zero =>
    have : e = 0 := by simpa using he
    subst this; simp [powModAux]
  | succ fuel ih =>
    unfold powModAux
    by_cases h0 : e = 0
    · subst h0; simp
    · rw [if_neg h0]
      have he2 : e / 2 < 2 ^ fuel := by
        rw [pow_succ] at he; omega
      rw [ih _ _ he2]
      have hsq : (b * b % m) ^ (e / 2) % m = b ^ (2 * (e / 2)) % m := by
        rw [pow_mul, sq, Nat.pow_mod (b * b)]
      rw [hsq]
      rcases Nat.mod_two_eq_zero_or_one e with h | h
      · rw [if_neg (by omega)]
        congr 2; omega
      · rw [if_pos h, Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, ← pow_succ']
        congr 2; omega

theorem powMod_eq (b e m : ℕ) (he : e < 2 ^ 64) : powMod b e m = b ^ e % m :=
  powModAux_eq 64 b e m he

/-- A power in `ZMod m`, as `powMod`. -/
theorem zmod_pow_eq_powMod {m : ℕ} (b e : ℕ) (he : e < 2 ^ 64) :
    (b : ZMod m) ^ e = (powMod b e m : ZMod m) := by
  rw [powMod_eq b e m he, ZMod.natCast_mod]; push_cast; rfl

end Plonky3Lean.Lib
