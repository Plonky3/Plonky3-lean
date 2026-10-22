module

public import CompPoly.Fields.Binary.Tower.Concrete.CoordinateArithmetic
public import Mathlib.FieldTheory.Finite.Basic

@[expose] public section

/-!
# The Frobenius of a quadratic step is conjugation

Level `k + 1` of the tower is level `k` with a root `X` of `t^2 + Z t + 1` adjoined. With
`q = 2^(2^k)` elements at level `k`, `x ↦ x^q` fixes level `k` and sends `X` to the other root
`X + Z`. It is CompPoly's `conjugate`:

`(lo + hi X)^q = (lo + hi Z) + hi X`.

`exp_power_of_2` applies it to raise to the power `2^(2^k)` without squaring `2^k` times.

The proof: `X^q` is a root of `t^2 + Z t + 1 = (t + X) (t + X + Z)`. If it were `X`, every
element would be a root of `t^q - t`, which has `q < q^2` roots.
-/

open ConcreteBinaryTower ConcreteBinaryTower.Coordinates

namespace Plonky3Lean.Proofs.Binary

/-- The embedding of level `k` into level `k + 1`. -/
abbrev embed (k : ℕ) := concreteTowerAlgebraMap k (k + 1) (Nat.le_succ k)

theorem card_level (k : ℕ) : Fintype.card (ConcreteBTField k) = 2 ^ 2 ^ k :=
  (getBTFResult k).fieldFintypeCard

theorem pow_card_level {k : ℕ} (a : ConcreteBTField k) : a ^ 2 ^ 2 ^ k = a := by
  rw [← card_level]
  exact FiniteField.pow_card a

theorem pow_two_pow_add {k : ℕ} (n : ℕ) (x y : ConcreteBTField k) :
    (x + y) ^ 2 ^ n = x ^ 2 ^ n + y ^ 2 ^ n :=
  add_pow_char_pow x y 2 n

/-- `X`, the generator of level `k + 1`, has coordinates `(0, 1)`. -/
theorem Z_succ_eq_joinSucc (k : ℕ) : Z (k + 1) = joinSucc k 0 1 := by
  rw [joinSucc_eq_map_mul_add, map_one, map_zero, one_mul, add_zero]

/-- `X^2 = Z X + 1`. -/
theorem Z_succ_mul_self (k : ℕ) : Z (k + 1) * Z (k + 1) = embed k (Z k) * Z (k + 1) + 1 := by
  have h := joinSucc_mul_joinSucc k 0 1 0 1
  simp only [mul_zero, mul_one, zero_add, one_mul] at h
  rw [Z_succ_eq_joinSucc, h, joinSucc_eq_map_mul_add, map_one, ← Z_succ_eq_joinSucc]

/-- Every element of level `k + 1` is `hi X + lo`, with `lo` and `hi` from level `k`. -/
theorem eq_embed_mul_add (k : ℕ) (x : ConcreteBTField (k + 1)) :
    x = embed k (high k x) * Z (k + 1) + embed k (low k x) := by
  conv_lhs => rw [← joinSucc_low_high k x]
  exact joinSucc_eq_map_mul_add k _ _

theorem pow_card_eq_conjugate (k : ℕ) (x : ConcreteBTField (k + 1)) :
    x ^ 2 ^ 2 ^ k = conjugate k x := by
  have hfix : ∀ a : ConcreteBTField k, embed k a ^ 2 ^ 2 ^ k = embed k a := fun a => by
    rw [← map_pow, pow_card_level]
  have hpow : ∀ w : ConcreteBTField (k + 1), w ^ 2 ^ 2 ^ k =
      embed k (high k w) * Z (k + 1) ^ 2 ^ 2 ^ k + embed k (low k w) := fun w => by
    conv_lhs => rw [eq_embed_mul_add k w]
    rw [pow_two_pow_add, mul_pow, hfix, hfix]
  set X := Z (k + 1)
  set z := embed k (Z k)
  set Y := X ^ 2 ^ 2 ^ k
  have hX : X * X = z * X + 1 := Z_succ_mul_self k
  have hz : z ^ 2 ^ 2 ^ k = z := hfix _
  have hY : Y * Y = z * Y + 1 := by
    have h := congrArg (· ^ 2 ^ 2 ^ k) hX
    simp only [mul_pow, pow_two_pow_add, one_pow, hz] at h
    exact h
  have h2 : (2 : ConcreteBTField (k + 1)) = 0 := CharTwo.two_eq_zero
  have hfac : (Y + X) * (Y + X + z) = 0 := by
    linear_combination hY + hX + (X * Y + z * Y + z * X + 1) * h2
  rcases mul_eq_zero.mp hfac with h | h
  · -- `X^q = X` would make every element a root of `t^q - t`.
    exfalso
    have hYX : Y = X := by linear_combination h - X * h2
    have hall : ∀ w : ConcreteBTField (k + 1), w ^ 2 ^ 2 ^ k = w := fun w => by
      rw [hpow, hYX, ← eq_embed_mul_add]
    have hq : 1 < 2 ^ 2 ^ k := Nat.one_lt_two_pow (by positivity)
    have hp0 := FiniteField.X_pow_card_sub_X_ne_zero (ConcreteBTField (k + 1)) hq
    have hroots : (Finset.univ : Finset (ConcreteBTField (k + 1))).val ≤
        (Polynomial.X ^ 2 ^ 2 ^ k - Polynomial.X : Polynomial (ConcreteBTField (k + 1))).roots :=
      (Multiset.le_iff_subset Finset.univ.nodup).mpr fun w _ =>
        (Polynomial.mem_roots hp0).mpr (by simp only [Polynomial.IsRoot, Polynomial.eval_sub,
          Polynomial.eval_pow, Polynomial.eval_X, hall w, sub_self])
    have hle := (Multiset.card_le_card hroots).trans (Polynomial.card_roots' _)
    rw [FiniteField.X_pow_card_sub_X_natDegree_eq _ hq, Finset.card_val, Finset.card_univ,
      card_level] at hle
    exact absurd hle (not_le.mpr (Nat.pow_lt_pow_right (by norm_num)
      (Nat.pow_lt_pow_right (by norm_num) (by omega))))
  · have hYX : Y = X + z := by linear_combination h - (X + z) * h2
    rw [hpow, hYX, conjugate_eq_joinSucc, joinSucc_eq_map_mul_add,
      map_add, map_mul]
    ring

end Plonky3Lean.Proofs.Binary
