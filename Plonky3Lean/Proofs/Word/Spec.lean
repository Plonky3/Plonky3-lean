module

public import P3Word

@[expose] public section

/-!
# Fixed-width words as bit vectors

This is the reference model the extracted word relations are compared against.

A word of `n` bits is a bit vector of width `n`.

Shifts follow the Rust reference, "Arithmetic and logical binary operators":

- a logical shift fills with zeros;
- an arithmetic right shift copies the sign bit;
- a rotation moves the bits leaving one end back in at the other.

A lane operation applies a 32-bit movement to each half of a 64-bit word on its own.

```text
    64-bit word:   [ high half : 32 bits | low half : 32 bits ]
    lane move:     [   f(high half)      |   f(low half)      ]
```
-/

open p3_word

namespace Plonky3Lean.Proofs.Word

/-- Whether a movement acts on the two 32-bit lanes. -/
def isLane : shift.ShiftKind → Bool
  | .Lane32LogicalLeft | .Lane32LogicalRight | .Lane32ArithmeticRight
  | .Lane32RotateRight => true
  | _ => false

/-- Whether a movement is a rotation. -/
def isRotate : shift.ShiftKind → Bool
  | .RotateRight | .Lane32RotateRight => true
  | _ => false

/-- The movement a kind performs, on one word or one lane of `n` bits. -/
def base {n : Nat} : shift.ShiftKind → Nat → BitVec n → BitVec n
  | .LogicalLeft, a, x | .Lane32LogicalLeft, a, x => x <<< a
  | .LogicalRight, a, x | .Lane32LogicalRight, a, x => x >>> a
  | .ArithmeticRight, a, x | .Lane32ArithmeticRight, a, x => x.sshiftRight a
  | .RotateRight, a, x | .Lane32RotateRight, a, x => x.rotateRight a

/-- A 32-bit map applied to each half of a 64-bit word. -/
def lanes (f : BitVec 32 → BitVec 32) (x : BitVec 64) : BitVec 64 :=
  f (x.extractLsb' 32 32) ++ f (x.extractLsb' 0 32)

/-- The meaning of a movement on a 32-bit word. -/
def sem32 (k : shift.ShiftKind) (a : Nat) (x : BitVec 32) : BitVec 32 := base k a x

/-- The meaning of a movement on a 64-bit word. -/
def sem64 (k : shift.ShiftKind) (a : Nat) (x : BitVec 64) : BitVec 64 :=
  if isLane k then lanes (fun y => base k a y) x else base k a x

/-- The width a movement shifts within: 32 for a lane, the word width otherwise. -/
def opWidth (n : Nat) (k : shift.ShiftKind) : Nat := if isLane k then 32 else n

/-- When applying a movement to a 32-bit word panics.

- A lane movement has no lanes to act on.
- A shift by the word width or more overflows.

A rotation reduces its distance modulo the width, so it never overflows. -/
def panics32 (k : shift.ShiftKind) (a : Nat) : Prop :=
  isLane k ∨ (isRotate k = false ∧ 32 ≤ a)

/-- When applying a movement to a 64-bit word panics: a shift by its width or more. -/
def panics64 (k : shift.ShiftKind) (a : Nat) : Prop :=
  isRotate k = false ∧ opWidth 64 k ≤ a

instance (k a) : Decidable (panics32 k a) := by unfold panics32; infer_instance
instance (k a) : Decidable (panics64 k a) := by unfold panics64; infer_instance

end Plonky3Lean.Proofs.Word
