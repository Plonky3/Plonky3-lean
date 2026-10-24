module

public import P3Challenger
public import Plonky3Lean.Proofs.Challenger.Bits

@[expose] public section

/-!
# The reductions at BabyBear, KoalaBear, Goldilocks and Mersenne31

Each field declares sampling constants.

They are checked here against the arithmetic they encode.

The multi-field challenger is checked at every pair of these fields.
-/

namespace Plonky3Lean.Proofs.Challenger.Fields

open p3_challenger.mirror

/-- The BabyBear prime, 15 * 2^27 + 1. -/
abbrev pBB : ℕ := 2013265921
/-- The KoalaBear prime, 127 * 2^24 + 1. -/
abbrev pKB : ℕ := 2130706433
/-- The Goldilocks prime, 2^64 - 2^32 + 1. -/
abbrev pGL : ℕ := 18446744069414584321
/-- The Mersenne31 prime, 2^31 - 1. -/
abbrev pM31 : ℕ := 2147483647

/-- The rejection bound for k bits, as each field computes it.

It is the prime with its low k bits masked off, in 64-bit arithmetic. -/
def samplingM (p k : ℕ) : ℕ := if k = 0 then p else p &&& (2 ^ 64 - 2 ^ k)

/-- The mask clears the low k bits.

The result is m_k = floor(p / 2^k) 2^k, the largest multiple of 2^k up to p. -/
theorem samplingM_eq_BB : ∀ k < 64, 0 < k → samplingM pBB k = pBB / 2 ^ k * 2 ^ k := by decide +kernel
theorem samplingM_eq_KB : ∀ k < 64, 0 < k → samplingM pKB k = pKB / 2 ^ k * 2 ^ k := by decide +kernel
theorem samplingM_eq_GL : ∀ k < 64, 0 < k → samplingM pGL k = pGL / 2 ^ k * 2 ^ k := by decide +kernel
theorem samplingM_eq_M31 : ∀ k < 64, 0 < k → samplingM pM31 k = pM31 / 2 ^ k * 2 ^ k := by decide +kernel

/-- Consider each field's largest single-sample bit count.

There, one canonical value in p is rejected for BabyBear (27), KoalaBear (24) and Goldilocks (32).

For Mersenne31 (16) the rejected values number 2^16 - 1.

That is a chance of about 3 * 10^-5, as its comment says. -/
theorem rejected_at_max :
    pBB % 2 ^ 27 = 1 ∧ pKB % 2 ^ 24 = 1 ∧ pGL % 2 ^ 32 = 1 ∧ pM31 % 2 ^ 16 = 2 ^ 16 - 1 := by
  decide +kernel

/-- Take a bit count the samplers accept, with 2^bits < p, above the largest single-sample count.

It splits into two halves that do not exceed it. -/
theorem halves_fit :
    (∀ b < 64, 2 ^ b < pBB → 27 < b → b - b / 2 ≤ 27) ∧
    (∀ b < 64, 2 ^ b < pKB → 24 < b → b - b / 2 ≤ 24) ∧
    (∀ b < 64, 2 ^ b < pGL → 32 < b → b - b / 2 ≤ 32) ∧
    (∀ b < 64, 2 ^ b < pM31 → 16 < b → b - b / 2 ≤ 16) := by
  decide +kernel

/-! ## The multi-field challenger -/

/-- Goldilocks holds one near-uniform limb of each 31-bit field per squeezed cell. -/
theorem squeeze_limbs_goldilocks :
    squeeze_field_order_num_limbs pBB pGL = 1 ∧ squeeze_field_order_num_limbs pKB pGL = 1 ∧
      squeeze_field_order_num_limbs pM31 pGL = 1 := by
  decide +kernel

/-- A 31-bit sponge field holds no limb of a smaller 31-bit field: its order is below the square. -/
theorem squeeze_limbs_31 :
    squeeze_field_order_num_limbs pBB pKB = 0 ∧ squeeze_field_order_num_limbs pBB pM31 = 0 ∧
      squeeze_field_order_num_limbs pKB pM31 = 0 := by
  decide +kernel

/-- The constructor accepts BabyBear sampled from a KoalaBear sponge, at rate 4. -/
theorem new_accepts_babybear_in_koalabear :
    MultiField32Challenger.new pBB pKB 4 = .ok () := by
  have h1 : ¬ pBB ≥ pKB := by decide
  have h2 : ¬ max_absorb_injective_limbs pBB pKB * 4 > 255 := by decide +kernel
  simp only [MultiField32Challenger.new, h1, h2, ↓reduceIte]

/-- With no limb per cell, a refill is empty whatever the rate cells hold. -/
theorem refill_zero (p : ℕ) (outputs : List ℕ) : refill p 0 outputs = [] := by
  simp [refill, split_pf_to_field_order_limbs]

/-- With no limb per cell, every sample from an empty queue panics. -/
theorem sample_panics_without_limbs (p : ℕ) (rate : List ℕ) : sampleFromQueue p 0 [] rate = none := by
  simp [sampleFromQueue, refill_zero]

end Plonky3Lean.Proofs.Challenger.Fields
