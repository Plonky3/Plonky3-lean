module

public import Plonky3Lean.Proofs.Sha256Air.Bits

@[expose] public section

/-!
# The words of a row

On a row that meets its constraints, every bit column is a bit.

So each group of 32 bit columns holds a word: a schedule word, a chain entry, or an output word.

This file reads those words and turns each addition check into an addition of words modulo `2^32`.
-/

set_option linter.unusedSectionVars false

namespace Plonky3Lean.Proofs.Sha256Air

open p3_sha256_air.mirror Plonky3Lean.Spec.Sha256
open Plonky3Lean.Proofs.KeccakAir (bitF bitsum bitsum_lt bitsum_testBit eq_bitF)

variable {F : Type} [Field F] [DecidableEq F]

/-- The word whose bit b is whether cell b is 1. -/
def wordOf (g : ℕ → F) : BitVec 32 := BitVec.ofNat 32 (bitsum (fun j => decide (g j = 1)) 32)

theorem holds_wordOf {g : ℕ → F} (h : ∀ b < 32, g b * (g b - 1) = 0) : Holds g (wordOf g) := by
  intro b hb
  rw [eq_bitF (h b hb)]
  congr 1
  rw [wordOf, BitVec.getLsbD, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (bitsum_lt _ _), bitsum_testBit]
  simp [hb]

/-- A word's limbs make a pair of integers. -/
theorem pw_of_holds {x : ℕ → F} {w : BitVec 32} (h0 : x 0 = (lo w : F)) (h1 : x 1 = (hi w : F)) :
    PW x (lo w) w.toNat := by
  have := PW.of_limbs h0 h1
  rwa [show ((lo w : ℕ) : ℤ) + (hi w : ℕ) * 65536 = w.toNat by simp only [lo, hi]; push_cast; omega] at this

theorem pw_pack {g : ℕ → F} {w : BitVec 32} (h : Holds g w) : PW (packF g) (lo w) w.toNat :=
  pw_of_holds (packF_eq h 0 (by norm_num)) (packF_eq h 1 (by norm_num))

theorem lo_lt (w : BitVec 32) : lo w < 65536 := Nat.mod_lt _ (by norm_num)

theorem lo_le_toNat (w : BitVec 32) : lo w ≤ w.toNat := Nat.mod_le _ _

theorem hi_lt (w : BitVec 32) : hi w < 65536 := by
  have := w.isLt; simp only [hi]; omega

/-- A word of bits that an addition pins: its value is Z. -/
theorem toNat_of_pin (hp : 7 * 65536 < ringChar F) {g : ℕ → F} {w : BitVec 32} (h : Holds g w)
    {L Z : ℤ} (hpw : PW (packF g) L Z) (hL : -6 * 65536 ≤ L ∧ L < 7 * 65536)
    (hZ : -6 * 4294967296 ≤ Z ∧ Z < 7 * 4294967296) : (w.toNat : ℤ) = Z := by
  rw [← hpw.pin hp (packF_eq h 0 (by norm_num)) (packF_eq h 1 (by norm_num)) (lo_lt w) (hi_lt w) hL hZ]
  simp only [lo, hi]; push_cast; omega

end Plonky3Lean.Proofs.Sha256Air
