module

public import Plonky3Lean.Proofs.Sha256Air.Bits

@[expose] public section

/-!
# Ripple-carry addition in characteristic 2

In characteristic 2, a sum of bits is their xor, and `(x + z) (y + z) + z` is their majority.

So the carry constraints of an addition are those of a ripple-carry adder:

```text
    carry into bit 0      = 0
    carry into bit i + 1  = majority(x_i, y_i, carry into bit i)
    sum bit i             = x_i + y_i + carry into bit i
```

On bits, they force the sum to be `x + y` modulo `2^32`, bit by bit.
-/

set_option linter.unusedSectionVars false

namespace Plonky3Lean.Proofs.Sha256Air.Binary

open p3_air.builder.mirror p3_sha256_air.mirror p3_sha256_air.mirror.binary
open Plonky3Lean.Proofs.KeccakAir (fieldOps bitF)
open Plonky3Lean.Proofs.Sha256Air (Holds)

variable {F : Type} [Field F] (h2 : (2 : F) = 0)
include h2

theorem neg_eq_self (x : F) : -x = x := by
  have : x + x = 0 := by rw [← two_mul, h2, zero_mul]
  linear_combination (-1 : F) * this

theorem eq_of_add_eq_zero {x y : F} (h : x + y = 0) : x = y := by
  rw [← neg_eq_self h2 y]; exact eq_neg_of_add_eq_zero_left h

theorem add_bitF (a b : Bool) : (bitF a : F) + bitF b = bitF (a ^^ b) := by
  cases a <;> cases b <;> simp [bitF]
  rw [one_add_one_eq_two, h2]

omit h2 in
theorem mul_bitF (a b : Bool) : (bitF a : F) * bitF b = bitF (a && b) := by
  cases a <;> cases b <;> simp [bitF]

theorem maj_bitF (a b c : Bool) :
    maj fieldOps (bitF a : F) (bitF b) (bitF c) = bitF (Bool.atLeastTwo a b c) := by
  have h11 : (1 : F) + 1 = 0 := by rw [one_add_one_eq_two, h2]
  cases a <;> cases b <;> cases c <;> simp [maj, fieldOps, bitF, h11]

/-- One stored-carry addition: the carries are bits and the next partial sum holds `P + W`. -/
theorem step_holds {p w c : ℕ → F} {P W : BitVec 32} (hp : Holds p P) (hw : Holds w W)
    (h0 : p 0 * w 0 + c 0 = 0)
    (hi : ∀ i ∈ List.range' 1 30, maj fieldOps (p i) (w i) (c (i - 1)) + c i = 0) :
    Holds (fun i => if i = 0 then p 0 + w 0 else p i + w i + c (i - 1)) (P + W) := by
  have hc : ∀ i < 31, c i = bitF (BitVec.carry (i + 1) P W false) := by
    intro i
    induction i with
    | zero =>
      intro _
      rw [← eq_of_add_eq_zero h2 h0, hp 0 (by omega), hw 0 (by omega), mul_bitF, BitVec.carry_succ]
      simp
    | succ i ih =>
      intro hi'
      have e := hi (i + 1) (List.mem_range'_1.mpr ⟨by omega, by omega⟩)
      rw [show i + 1 - 1 = i by omega, ih (by omega), hp _ (by omega), hw _ (by omega), maj_bitF h2] at e
      rw [← eq_of_add_eq_zero h2 e, BitVec.carry_succ (i + 1)]
  intro b hb
  rw [BitVec.getLsbD_add hb]
  rcases b with _ | b
  · simp only [↓reduceIte, hp 0 (by omega), hw 0 (by omega), add_bitF h2, BitVec.carry_zero,
      Bool.xor_false]
  · simp only [Nat.add_one_ne_zero, ↓reduceIte, hp _ hb, hw _ hb, Nat.add_sub_cancel,
      hc b (by omega), add_bitF h2, Bool.xor_assoc]

/-- The last addition: carries read off the sum force the sum to hold `P + L`. -/
theorem final_holds {p l s : ℕ → F} {P L : BitVec 32} (hp : Holds p P) (hl : Holds l L)
    (h0 : s 0 + p 0 + l 0 = 0)
    (hi : ∀ i ∈ List.range 31, maj fieldOps (p i) (l i) (s i + p i + l i) +
      (s (i + 1) + p (i + 1) + l (i + 1)) = 0) :
    Holds s (P + L) := by
  have hc : ∀ i < 32, s i + p i + l i = bitF (BitVec.carry i P L false) := by
    intro i
    induction i with
    | zero => intro _; rw [h0]; simp [bitF]
    | succ i ih =>
      intro hi'
      have e := hi i (by simp; omega)
      rw [ih (by omega), hp i (by omega), hl i (by omega), maj_bitF h2] at e
      rw [← eq_of_add_eq_zero h2 e, BitVec.carry_succ]
  intro b hb
  have e := hc b hb
  rw [hp b hb, hl b hb] at e
  have : s b = bitF (BitVec.carry b P L false) + bitF (P.getLsbD b) + bitF (L.getLsbD b) := by
    rw [← e]; linear_combination (neg_eq_self h2 (bitF (P.getLsbD b) + bitF (L.getLsbD b) : F))
  rw [this, add_bitF h2, add_bitF h2, BitVec.getLsbD_add hb]
  cases P.getLsbD b <;> cases L.getLsbD b <;> cases BitVec.carry b P L false <;> rfl

end Plonky3Lean.Proofs.Sha256Air.Binary
