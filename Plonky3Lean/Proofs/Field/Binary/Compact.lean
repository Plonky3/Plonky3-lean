import Mathlib.FieldTheory.Finite.Basic
import Plonky3Lean.Proofs.Field.Binary.Clmul

/-!
# Gathering the even bits

`compact_even` moves bit `2 i` of a 64-bit word to bit `i`.

Each round doubles the width of the gathered chunks, pulling every second chunk down next to its
neighbour.
-/

open Aeneas Aeneas.Std CoreModels Polynomial
open p3_binary_field BinaryField
open Plonky3Lean.Lib

namespace Plonky3Lean.Proofs.Binary

/-- One round of the gather: chunks of `c` bits at stride `2 c` merge into chunks of `2 c`. -/
theorem compact_round (c : ℕ) (hc : c = 1 ∨ c = 2 ∨ c = 4 ∨ c = 8 ∨ c = 16) {x v M : ℕ}
    (hv : v < 2 ^ 64)
    (hx : ∀ k, x.testBit k =
      (decide (k % (2 * c) < c) && v.testBit (2 * (c * (k / (2 * c)) + k % (2 * c)))))
    (hM : ∀ k, M.testBit k = (decide (k < 64) && decide (k % (4 * c) < 2 * c))) :
    ∀ k, ((x ||| x >>> c) &&& M).testBit k =
      (decide (k % (4 * c) < 2 * c) && v.testBit (2 * (2 * c * (k / (4 * c)) + k % (4 * c)))) := by
  intro k
  rw [Nat.testBit_and, Nat.testBit_or, Nat.testBit_shiftRight, hM k, hx k, hx (c + k)]
  have hbig : ∀ i, 64 ≤ i → v.testBit i = false := fun i hi =>
    Nat.testBit_lt_two_pow (lt_of_lt_of_le hv (Nat.pow_le_pow_right (by norm_num) hi))
  by_cases h1 : k % (4 * c) < 2 * c
  · by_cases h2 : k % (2 * c) < c
    · have e1 : 2 * (c * (k / (2 * c)) + k % (2 * c)) =
          2 * (2 * c * (k / (4 * c)) + k % (4 * c)) := by
        rcases hc with rfl|rfl|rfl|rfl|rfl <;> omega
      have e2 : ¬ (c + k) % (2 * c) < c := by rcases hc with rfl|rfl|rfl|rfl|rfl <;> omega
      by_cases h3 : k < 64
      · simp [h1, h2, e1, e2, h3]
      · have := hbig (2 * (2 * c * (k / (4 * c)) + k % (4 * c)))
          (by rcases hc with rfl|rfl|rfl|rfl|rfl <;> omega)
        simp [h3, this]
    · have e2 : (c + k) % (2 * c) < c := by rcases hc with rfl|rfl|rfl|rfl|rfl <;> omega
      have e1 : 2 * (c * ((c + k) / (2 * c)) + (c + k) % (2 * c)) =
          2 * (2 * c * (k / (4 * c)) + k % (4 * c)) := by
        rcases hc with rfl|rfl|rfl|rfl|rfl <;> omega
      by_cases h3 : k < 64
      · simp [h1, h2, e1, e2, h3]
      · have := hbig (2 * (2 * c * (k / (4 * c)) + k % (4 * c)))
          (by rcases hc with rfl|rfl|rfl|rfl|rfl <;> omega)
        simp [h3, this]
  · simp [h1]

/-- The value `compact_even` computes, on natural numbers. -/
def compactNat (v : ℕ) : ℕ :=
  let x := v &&& 0x5555_5555_5555_5555
  let x := (x ||| x >>> 1) &&& 0x3333_3333_3333_3333
  let x := (x ||| x >>> 2) &&& 0x0f0f_0f0f_0f0f_0f0f
  let x := (x ||| x >>> 4) &&& 0x00ff_00ff_00ff_00ff
  let x := (x ||| x >>> 8) &&& 0x0000_ffff_0000_ffff
  (x ||| x >>> 16) &&& 0xffff_ffff

/-- Bit `i` of the gather is bit `2 i`, for `i < 32`, and the upper half is clear. -/
theorem testBit_compactNat {v : ℕ} (hv : v < 2 ^ 64) (k : ℕ) :
    (compactNat v).testBit k = (decide (k < 32) && v.testBit (2 * k)) := by
  have hbig : ∀ i, 64 ≤ i → v.testBit i = false := fun i hi =>
    Nat.testBit_lt_two_pow (lt_of_lt_of_le hv (Nat.pow_le_pow_right (by norm_num) hi))
  have hmask : ∀ (M : ℕ) (c : ℕ), M < 2 ^ 64 →
      (∀ k < 64, M.testBit k = decide (k % (4 * c) < 2 * c)) →
      ∀ k, M.testBit k = (decide (k < 64) && decide (k % (4 * c) < 2 * c)) := by
    intro M c hM h k
    by_cases hk : k < 64
    · simp [hk, h k hk]
    · rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le hM (Nat.pow_le_pow_right (by norm_num)
        (by omega)))]
      simp [hk]
  have h0 : ∀ k, (v &&& 0x5555_5555_5555_5555).testBit k =
      (decide (k % (2 * 1) < 1) && v.testBit (2 * (1 * (k / (2 * 1)) + k % (2 * 1)))) := by
    intro k
    rw [Nat.testBit_and]
    by_cases hk : k < 64
    · have : (0x5555_5555_5555_5555 : ℕ).testBit k = decide (k % 2 = 0) := by
        revert k; decide
      rw [this]
      by_cases h2 : k % 2 = 0
      · simp [h2, show 2 * (k / 2) = k by omega]
      · simp [h2, show ¬ k % 2 < 1 by omega]
    · rw [hbig k (by omega), hbig _ (by omega)]
      simp
  have h1 := compact_round 1 (by omega) hv h0 (M := 0x3333_3333_3333_3333)
    (hmask _ _ (by norm_num) (by decide))
  have h2 := compact_round 2 (v := v) (by omega) hv (fun k => (h1 k).trans (by norm_num))
    (M := 0x0f0f_0f0f_0f0f_0f0f) (hmask _ _ (by norm_num) (by decide))
  have h3 := compact_round 4 (v := v) (by omega) hv (fun k => (h2 k).trans (by norm_num))
    (M := 0x00ff_00ff_00ff_00ff) (hmask _ _ (by norm_num) (by decide))
  have h4 := compact_round 8 (v := v) (by omega) hv (fun k => (h3 k).trans (by norm_num))
    (M := 0x0000_ffff_0000_ffff) (hmask _ _ (by norm_num) (by decide))
  have h5 := compact_round 16 (v := v) (by omega) hv (fun k => (h4 k).trans (by norm_num))
    (M := 0xffff_ffff) (hmask _ _ (by norm_num) (by decide))
  refine (h5 k).trans ?_
  by_cases hk : k < 32
  · simp [hk, show k % (4 * 16) = k by omega, show k / (4 * 16) = 0 by omega]
  · by_cases h : k % (4 * 16) < 2 * 16
    · rw [hbig _ (by omega), hbig _ (by omega)]
      simp
    · simp [h, hk]

theorem compactNat_lt (v : ℕ) : compactNat v < 2 ^ 32 := by
  unfold compactNat
  exact lt_of_le_of_lt Nat.and_le_right (by norm_num)

/-- `compact_even` never panics and returns the gather. -/
theorem compact_even_eq (x : Std.U64) :
    clmul.sqrt.compact_even x = .ok ⟨BitVec.ofNat 64 (compactNat x.val)⟩ := by
  unfold clmul.sqrt.compact_even
  simp (disch := decide) only [shiftRight_i32_eq, lift_eq, bind_tc_ok]
  congr 1
  apply UScalar.eq_of_val_eq
  simp only [UScalar.val, and_bv, or_bv, BitVec.toNat_and, BitVec.toNat_or,
    BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, UScalarTy.U64_numBits_eq,
    Nat.mod_eq_of_lt (lt_trans (compactNat_lt _) (by norm_num : 2 ^ 32 < 2 ^ 64))]
  rfl

end Plonky3Lean.Proofs.Binary
