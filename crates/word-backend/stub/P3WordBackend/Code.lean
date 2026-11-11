/-
Transcriptions of keys/code.rs: the compact codes of shifts and of relation keys.

A code is a natural number below its Rust width.

A cast to a narrower integer keeps the low bits, as in Rust.

A failed expectation panics.
-/
module

public import P3Word

@[expose] public section

namespace p3_word_backend.keys.code.mirror

open Aeneas Aeneas.Std p3_word

/-- Bits of one shift code. -/
def SHIFT_BITS : ℕ := 9

/-- Bits of a sequence of two shift codes. -/
def SEQUENCE_BITS : ℕ := 2 * SHIFT_BITS

/-- The mask keeping a sequence below the family tag. -/
def SEQUENCE_MASK : ℕ := 2 ^ SEQUENCE_BITS - 1

/-- The code of one shift: its kind in three bits above its six-bit amount. -/
def ShiftCode.new {W : Type} (s : shift.Shift W) : RustM ℕ := do
  let kind ← shift.ShiftKind.code s.kind
  .ok ((kind.val <<< 6) ||| s.amount.val)

/-- The shift a code names.

The code is first cut to its nine bits.

Both the kind lookup and the constructor are expected to succeed, and panic otherwise. -/
def ShiftCode.shift {W : Type} (inst : word.Word W) (c : ℕ) : RustM (shift.Shift W) := do
  let code := c &&& (2 ^ SHIFT_BITS - 1)
  let k ← shift.ShiftKind.from_code ⟨BitVec.ofNat _ (code >>> 6)⟩
  match k with
  | .None => .fail .panic
  | .Some kind =>
    let r ← shift.Shift.new inst kind ⟨BitVec.ofNat _ (code &&& 0x3f)⟩
    match r with
    | .Ok s => .ok s
    | .Err _ => .fail .panic

/-- The code of one relation key: the family tag above the outer and the inner shift codes. -/
def KeyCode.new {W : Type} (operation : system.ConstraintKind)
    (shifts : Array (shift.Shift W) 2#usize) : RustM ℕ := do
  let op ← system.ConstraintKind.code operation
  let s1 ← Array.index_usize shifts 1#usize
  let outer ← ShiftCode.new s1
  let s0 ← Array.index_usize shifts 0#usize
  let inner ← ShiftCode.new s0
  .ok ((op.val <<< SEQUENCE_BITS) ||| (outer <<< SHIFT_BITS) ||| inner)

/-- The relation family of a key code.

The tag above the sequence is cast to a byte, which keeps its low eight bits. -/
def KeyCode.operation (c : ℕ) : RustM system.ConstraintKind := do
  let k ← system.ConstraintKind.from_code ⟨BitVec.ofNat _ (c >>> SEQUENCE_BITS)⟩
  match k with
  | .None => .fail .panic
  | .Some kind => .ok kind

/-- The shift sequence of a key code. -/
def KeyCode.sequence (c : ℕ) : ℕ := c &&& SEQUENCE_MASK

/-- The code of a shift sequence, independent of any family. -/
def ShiftSequenceCode.new {W : Type} (shifts : Array (shift.Shift W) 2#usize) : RustM ℕ := do
  let c ← KeyCode.new .Zero shifts
  .ok (KeyCode.sequence c)

/-- The inner and the outer shift of a sequence code.

Each slot is cast to 16 bits before it is decoded. -/
def ShiftSequenceCode.shifts {W : Type} (inst : word.Word W) (c : ℕ) :
    RustM (Array (shift.Shift W) 2#usize) := do
  let inner ← ShiftCode.shift inst (c % 2 ^ 16)
  let outer ← ShiftCode.shift inst ((c >>> SHIFT_BITS) % 2 ^ 16)
  .ok (Array.make 2#usize [inner, outer])

end p3_word_backend.keys.code.mirror
