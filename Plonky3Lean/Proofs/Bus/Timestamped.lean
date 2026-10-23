module

public import P3Bus
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Algebra.Order.BigOperators.Group.List
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.FieldSimp

@[expose] public section

/-!
# The timestamped memory's clock

The clock ticks by a generator g, and each access proves `now = prev g^d` with `1 <= d <= 2^32`:

```text
    prev lo = now hi,   lo = g^(j + 1),   hi = g^(-2^16 m),   j, m < 2^16
    d = (j + 1) + 2^16 m
```

A forged cycle of n accesses would climb by a sum of gaps that the order of g divides.

That sum is between 1 and n 2^32, so it cannot be a multiple of an order above n 2^32, which is what the access bound checks.
-/

namespace Plonky3Lean.Proofs.Bus

open p3_bus.timestamped.mirror

set_option linter.unusedSectionVars false

variable {C : Type _} [Field C]

/-- **The gap factors.** A gap from 1 to 2^32 splits into digits j, m below 2^16 with d = (j + 1) + 2^16 m, and its factors are the table entries of row j and row m. -/
theorem gap_factors_spec (g : C) {d : ℕ} (h1 : 1 ≤ d) (h2 : d ≤ 2 ^ 32) :
    ∃ j < 2 ^ 16, ∃ m < 2 ^ 16, d = j + 1 + 2 ^ 16 * m ∧
      gap_factors g d = some (ClockRangeAir.low g j, ClockRangeAir.high g m) := by
  refine ⟨(d - 1) % 2 ^ 16, Nat.mod_lt _ (by norm_num), (d - 1) / 2 ^ 16, by omega, by omega, ?_⟩
  unfold gap_factors
  rw [ite_eq_right (by unfold CLOCK_GAP_BITS CLOCK_RANGE_BITS; omega)]
  rfl

/-- A gap outside 1 to 2^32 has no factors. -/
theorem gap_factors_none (g : C) {d : ℕ} (h : d = 0 ∨ 2 ^ 32 < d) : gap_factors g d = none := by
  unfold gap_factors
  rw [ite_eq_left (by unfold CLOCK_GAP_BITS CLOCK_RANGE_BITS; omega)]

/-- **The gap check.** With the table entries of rows j and m and a nonzero tick, prev lo = now hi exactly when now = prev g^d for d = (j + 1) + 2^16 m. -/
theorem gap_sound {g : C} (hg : g ≠ 0) (j m : ℕ) (prev now : C) :
    prev * ClockRangeAir.low g j = now * ClockRangeAir.high g m ↔
      now = prev * g ^ (j + 1 + 2 ^ 16 * m) := by
  unfold ClockRangeAir.low ClockRangeAir.high high_step CLOCK_RANGE_BITS
  have hgm : g ^ (2 ^ 16 * m) ≠ 0 := pow_ne_zero _ hg
  rw [inv_pow, ← pow_mul, pow_add g (j + 1)]
  constructor
  · intro h
    have := congrArg (· * g ^ (2 ^ 16 * m)) h
    simp only [mul_assoc, inv_mul_cancel₀ hgm, mul_one] at this
    rw [← this]
  · intro h
    rw [h, mul_assoc, mul_assoc, mul_inv_cancel₀ hgm, mul_one]

/-- The gap of rows j and m lies between 1 and 2^32. -/
theorem gap_range {j m : ℕ} (hj : j < 2 ^ 16) (hm : m < 2 ^ 16) :
    1 ≤ j + 1 + 2 ^ 16 * m ∧ j + 1 + 2 ^ 16 * m ≤ 2 ^ 32 := by omega

/-- **No forged cycle.** A nonempty list of gaps from 1 to 2^32, fewer than the order of g over 2^32, does not climb back to the start. -/
theorem no_cycle {G : Type _} [Monoid G] {g : G} (ds : List ℕ) (hd : ∀ d ∈ ds, 1 ≤ d ∧ d ≤ 2 ^ 32)
    (hne : ds ≠ []) (hord : ds.length * 2 ^ 32 < orderOf g) : g ^ ds.sum ≠ 1 := by
  intro h
  have hpos : 0 < ds.sum := by
    obtain ⟨d, hd'⟩ := List.exists_mem_of_ne_nil ds hne
    exact lt_of_lt_of_le (hd d hd').1 (List.le_sum_of_mem hd')
  have hle : ds.sum ≤ ds.length * 2 ^ 32 := by
    simpa using List.sum_le_length_nsmul ds (2 ^ 32) fun d h => (hd d h).2
  have := Nat.le_of_dvd hpos (orderOf_dvd_of_pow_eq_one h)
  omega

/-- The access bound accepts n pulls exactly when n 2^32 is below the orbit |C| - 1. -/
theorem check_accesses_ok (order pulls : ℕ) :
    check_accesses order pulls = .ok () ↔ pulls * 2 ^ 32 < order - 1 := by
  unfold check_accesses clock_orbit CLOCK_GAP_BITS CLOCK_RANGE_BITS
  by_cases h : pulls * 2 ^ (2 * 16) ≥ order - 1
  · rw [ite_eq_left h]; exact ⟨fun hh => (by cases hh), fun hh => (by omega)⟩
  · rw [ite_eq_right h]; exact ⟨fun _ => (by omega), fun _ => rfl⟩

/-- The orbit check accepts a clock field exactly when its orbit exceeds 2^32. -/
theorem check_orbit_ok (order : ℕ) : check_orbit order = .ok () ↔ 2 ^ 32 < order - 1 := by
  unfold check_orbit clock_orbit CLOCK_GAP_BITS CLOCK_RANGE_BITS
  dsimp only
  by_cases h : order - 1 ≤ 2 ^ (2 * 16)
  · rw [ite_eq_left h]; exact ⟨fun hh => (by cases hh), fun hh => (by omega)⟩
  · rw [ite_eq_right h]; exact ⟨fun _ => (by omega), fun _ => rfl⟩

end Plonky3Lean.Proofs.Bus
