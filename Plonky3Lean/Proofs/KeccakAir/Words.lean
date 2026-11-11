module

public import Plonky3Lean.Proofs.KeccakAir.Bits
public import Plonky3Lean.Proofs.KeccakAir.Cells
public import Plonky3Lean.Proofs.Hash.Keccak.Lanes

@[expose] public section

/-!
# Words as cells

The generator writes a word as its 64 bits, or as its four 16-bit limbs.

Bit i of a word is its bit i, and limb l is the bit sum of its bits 16 l to 16 l + 15.

The round constants the generator xors in have, bit for bit, the bits the AIR reads from its table.
-/

set_option linter.unusedSectionVars false

namespace Plonky3Lean.Proofs.KeccakAir

open p3_keccak_air.mirror

variable {F : Type} [Field F]

theorem bitsum_testBit (g : ℕ → Bool) (k j : ℕ) : (bitsum g k).testBit j = (decide (j < k) && g j) := by
  induction k generalizing g j with
  | zero => simp [bitsum]
  | succ k ih =>
    simp only [bitsum]
    rcases j with _ | j
    · cases g 0 <;> simp
    · rw [show (g 0).toNat + 2 * bitsum (fun j => g (j + 1)) k =
          2 * bitsum (fun j => g (j + 1)) k + (g 0).toNat by omega, Nat.testBit_succ,
        show (2 * bitsum (fun j => g (j + 1)) k + (g 0).toNat) / 2 =
          bitsum (fun j => g (j + 1)) k by
          cases g 0 <;> simp only [Bool.toNat_false, Bool.toNat_true] <;> omega, ih]
      simp

/-- Limb l of a word is the bit sum of its bits 16 l to 16 l + 15. -/
theorem shift_mod_eq_bitsum (w : Word) (l : ℕ) :
    (w >>> (16 * l)).toNat % 2 ^ 16 = bitsum (fun j => w.getLsbD (l * 16 + j)) 16 := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [bitsum_testBit, Nat.testBit_mod_two_pow, ← BitVec.getLsbD, BitVec.getLsbD_ushiftRight]
  by_cases hj : j < 16
  · simp [hj, Nat.mul_comm, Nat.add_comm]
  · simp [hj]

theorem u64_limbs_eq (w : Word) (l : ℕ) :
    (u64_to_16_bit_limbs w l : F) = ((bitsum (fun j => w.getLsbD (l * 16 + j)) 16 : ℕ) : F) := by
  rw [u64_to_16_bit_limbs, shift_mod_eq_bitsum]

theorem u64_bits_eq (w : Word) {i : ℕ} (hi : i < 64) : (u64_to_bits_le w i : F) = bitF (w.getLsbD i) := by
  unfold u64_to_bits_le
  have : (w &&& 1#64 <<< i ≠ 0) ↔ w.getLsbD i = true := by
    constructor
    · intro h
      by_contra hb
      apply h
      apply BitVec.eq_of_getLsbD_eq
      intro k hk
      simp only [BitVec.getLsbD_and, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_one]
      by_cases hki : k = i
      · subst hki; simp_all
      · simp; omega
    · intro h h0
      have := congrArg (fun v => v.getLsbD i) h0
      rw [BitVec.getLsbD_eq_getElem hi] at h
      simp [hi] at this
      simp_all
  by_cases hb : w.getLsbD i <;> simp_all [bitF]

/-- The round constants and the table of their bits agree, bit for bit. -/
theorem rc_getLsbD : ∀ k < 24, ∀ z < 64,
    (BitVec.ofNat 64 (RC.getD k 0)).getLsbD z = decide (rcBit k z ≠ 0) := by
  decide +kernel

end Plonky3Lean.Proofs.KeccakAir
