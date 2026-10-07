import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic.Positivity

/-!
# Orders of elements
-/

namespace Plonky3Lean.Lib

/-- If `x ^ 2` has order `2 ^ (k + 1)`, then `x` has order `2 ^ (k + 2)`: a square
root of a primitive `2 ^ (k + 1)`-th root of unity is a primitive
`2 ^ (k + 2)`-th one. -/
theorem orderOf_eq_two_pow_succ_of_sq {M : Type*} [Monoid M] {x y : M} {k : ℕ}
    (hxy : x ^ 2 = y) (hy : orderOf y = 2 ^ (k + 1)) : orderOf x = 2 ^ (k + 2) := by
  apply orderOf_eq_prime_pow (p := 2)
  · intro h
    have : y ^ 2 ^ k = 1 := by rw [← hxy, ← pow_mul, ← pow_succ']; exact h
    have hd := orderOf_dvd_of_pow_eq_one this
    rw [hy] at hd
    exact absurd (Nat.le_of_dvd (by positivity) hd) (by
      rw [not_le]; exact Nat.pow_lt_pow_right (by norm_num) (by omega))
  · rw [pow_succ', pow_mul, hxy, ← hy, pow_orderOf_eq_one]

end Plonky3Lean.Lib
