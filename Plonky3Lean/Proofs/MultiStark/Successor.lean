module

public import Plonky3Lean.Proofs.MultiStark.Ext

@[expose] public section

/-!
# The next row on the hypercube

The successor repeats the last row instead of wrapping around to row 0:

```text
    rows      0   1   2   ...   2^n - 2   2^n - 1
    succ      1   2   3   ...   2^n - 1   2^n - 1
```

A transition constraint is gated by the transition selector, which is zero on the last row.

So a gated constraint asserts exactly the 2^n - 1 transitions b -> b + 1.

A wrapping successor gives the same assertion.

An ungated constraint that reads the next row differs.

On the last row it reads the last row twice.

The opening of the next row at the bound point is the extension of the shifted table.

It is weighted by the successor table.
-/

namespace Plonky3Lean.Proofs.MultiStark

open Plonky3Lean.Spec.MultiStark Plonky3Lean.Spec.MultilinearUtil Plonky3Lean.Proofs.MultilinearUtil
  Finset

variable {K : Type _} [Field K]

theorem succRepeat_of_lt {n b : ℕ} (h : b + 1 < 2 ^ n) : succRepeat n b = b + 1 := by
  simp [succRepeat, h]

/-- The last row's successor is itself. -/
theorem succRepeat_last (n : ℕ) : succRepeat n (2 ^ n - 1) = 2 ^ n - 1 := by
  have := Nat.one_le_two_pow (n := n)
  simp [succRepeat, show ¬ 2 ^ n - 1 + 1 < 2 ^ n by omega]

theorem succRepeat_lt {n b : ℕ} (h : b < 2 ^ n) : succRepeat n b < 2 ^ n := by
  unfold succRepeat; split <;> omega

/-- **Gated transitions.**

Take a constraint gated by the transition selector.

It holds on every row exactly when it holds on every transition b -> b + 1. -/
theorem transition_gated_iff (n : ℕ) (Q : ℕ → ℕ → K) :
    (∀ b < 2 ^ n, transitionRow n b * Q b (succRepeat n b) = 0) ↔
      ∀ b, b + 1 < 2 ^ n → Q b (b + 1) = 0 := by
  refine ⟨fun h b hb => ?_, fun h b _ => ?_⟩
  · simpa [transitionRow, hb, succRepeat_of_lt hb] using h b (by omega)
  · by_cases hb : b + 1 < 2 ^ n
    · simp [transitionRow, hb, succRepeat_of_lt hb, h b hb]
    · simp [transitionRow, hb]

/-- **Ungated next-row reads.**

An ungated constraint holds on every row exactly when it holds on:

- every transition
- the last row paired with itself, not with row 0. -/
theorem ungated_iff (n : ℕ) (Q : ℕ → ℕ → K) :
    (∀ b < 2 ^ n, Q b (succRepeat n b) = 0) ↔
      (∀ b, b + 1 < 2 ^ n → Q b (b + 1) = 0) ∧ Q (2 ^ n - 1) (2 ^ n - 1) = 0 := by
  have h1 := Nat.one_le_two_pow (n := n)
  refine ⟨fun h => ⟨fun b hb => ?_, ?_⟩, fun ⟨h, hl⟩ b hb => ?_⟩
  · simpa [succRepeat_of_lt hb] using h b (by omega)
  · simpa [succRepeat_last] using h (2 ^ n - 1) (by omega)
  · by_cases hb' : b + 1 < 2 ^ n
    · rw [succRepeat_of_lt hb']; exact h b hb'
    · obtain rfl : b = 2 ^ n - 1 := by omega
      rw [succRepeat_last]; exact hl

/-- **The next-row opening.**

The extension of the shifted table is the successor table's weighting of the table. -/
theorem rowExt_succRepeat (f : ℕ → K) (r : List K) :
    rowExt (fun b => f (succRepeat r.length b)) r =
      ∑ y ∈ range (2 ^ r.length), (nextTable r).getD y 0 * f y := by
  have hget : ∀ y ∈ range (2 ^ r.length), (nextTable r).getD y 0 =
      ∑ x ∈ range (2 ^ r.length), if succRepeat r.length x = y then eq (vertex r.length x) r else 0 :=
    fun y hy => by simp [nextTable, List.getD_eq_getElem?_getD, mem_range.mp hy]
  rw [sum_congr rfl fun y hy => by rw [hget y hy], rowExt]
  simp only [sum_mul, ite_mul, zero_mul]
  rw [sum_comm]
  exact sum_congr rfl fun x hx => by
    rw [sum_ite_eq (range _) (succRepeat r.length x)]
    simp [succRepeat_lt (mem_range.mp hx)]

end Plonky3Lean.Proofs.MultiStark
