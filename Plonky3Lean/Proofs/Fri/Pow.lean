module

public import Mathlib.Data.Nat.Factorization.Basic

@[expose] public section

/-!
# The grinding check's acceptance count

The grinding check samples one canonical field value v below p and accepts when its low b bits are zero.

Over a uniform v the acceptance probability is the count of such values over p:

```text
    #{v < p : 2^b | v} = (p - 1) / 2^b + 1
```

That is at least 2^(-b), with equality only when 2^b divides p.

For BabyBear and every b from 27 to 30 the count is 2^(31 - b), so the probability is 2^31 / (2^b p).

Since 15 * 2^31 < 16 p, a b-bit grind there buys between b - log_2(16/15) and b bits.
-/

namespace Plonky3Lean.Proofs.Fri

open Finset

/-- The values below p whose low b bits are zero number (p - 1) / 2^b + 1. -/
theorem pow_accepting_card (p b : ℕ) (hp : 0 < p) :
    ((range p).filter fun v => v % 2 ^ b = 0).card = (p - 1) / 2 ^ b + 1 := by
  have hsplit : (range p).filter (fun v => v % 2 ^ b = 0) =
      insert 0 ((range (p - 1).succ).filter fun k => k ≠ 0 ∧ 2 ^ b ∣ k) := by
    ext v
    simp only [mem_filter, mem_range, mem_insert, Nat.succ_eq_add_one, Nat.sub_add_cancel hp,
      Nat.dvd_iff_mod_eq_zero]
    constructor
    · rintro ⟨h1, h2⟩
      rcases Nat.eq_zero_or_pos v with rfl | hv
      · exact .inl rfl
      · exact .inr ⟨h1, by omega, h2⟩
    · rintro (rfl | ⟨h1, -, h2⟩)
      · exact ⟨hp, Nat.zero_mod _⟩
      · exact ⟨h1, h2⟩
  rw [hsplit, card_insert_of_notMem (by simp), Nat.card_multiples']

/-- For BabyBear, every difficulty b from 27 to 30 accepts exactly 2^(31 - b) values.

The acceptance probability 2^31 / (2^b p) then lies strictly between 2^(-b) and (16/15) 2^(-b). -/
theorem pow_babyBear_count :
    (∀ b ∈ [27, 28, 29, 30], ((2013265921 - 1) / 2 ^ b + 1) * 2 ^ b = 2 ^ 31) ∧
      2013265921 < 2 ^ 31 ∧ 15 * 2 ^ 31 < 16 * 2013265921 := by
  decide

end Plonky3Lean.Proofs.Fri
