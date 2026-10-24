/-
Transcriptions of the declaration surface.

It covers the direction, the channel name, the boundary, the activation, and the declaring builder.

These do not extract: the builder trait carries associated types bounded by the field traits, which aeneas rejects.

Each definition transcribes one Rust item, named in the crate's mirror entries.

What a transcription abstracts:

- a builder is the p3-air builder record, extended by the recorder's one method
- a channel name is a string, and its bytes are its UTF-8 bytes
- a panic is none.

Loops, branches and the order of operations are kept.
-/
module

public import P3Air

@[expose] public section

namespace p3_bus.mirror

open p3_air.builder.mirror

/-- The side of a multiset equality to which an entry belongs. -/
inductive BusDirection where
  | Push
  | Pull
  deriving DecidableEq, Repr

/-- Position of a direction in push-then-pull arrays. -/
def BusDirection.index : BusDirection → ℕ
  | .Push => 0
  | .Pull => 1

/-- Both sides in push-then-pull order. -/
def BusDirection.ALL : List BusDirection := [.Push, .Pull]

/-- Why a channel name leaves the alphabet. -/
inductive BusNameError where
  | Empty
  | TooLong (len max : ℕ)
  | Leading (byte : UInt8)
  | Byte (index : ℕ) (byte : UInt8)
  deriving DecidableEq, Repr

/-- The longest name the alphabet admits. -/
def BusName.MAX_LEN : ℕ := 64

def isAsciiAlphabetic (b : UInt8) : Bool := (65 ≤ b && b ≤ 90) || (97 ≤ b && b ≤ 122)

def isAsciiAlphanumeric (b : UInt8) : Bool := isAsciiAlphabetic b || (48 ≤ b && b ≤ 57)

/-- A valid channel name has one to 64 bytes.

It starts with an ASCII letter, followed by letters, digits, `_`, `.` or `-`.

The index loop returns at the first byte outside the alphabet. -/
def BusName.try_new (nm : String) : Except BusNameError String :=
  let bytes := nm.toUTF8.toList
  match bytes with
  | [] => .error .Empty
  | b0 :: _ =>
    if bytes.length > BusName.MAX_LEN then .error (.TooLong bytes.length BusName.MAX_LEN)
    else if !isAsciiAlphabetic b0 then .error (.Leading b0)
    else
      match (List.range bytes.length).drop 1 |>.find? fun i =>
          let b := bytes.getD i 0
          !(isAsciiAlphanumeric b || b == 95 || b == 46 || b == 45) with
      | some i => .error (.Byte i (bytes.getD i 0))
      | none => .ok nm

/-- End of a table at which a boundary declaration contributes. -/
inductive BusBoundary where
  | First
  | Last
  deriving DecidableEq, Repr

/-- Whether a boundary holds a row: row zero, or the last row of a table of this height. -/
def BusBoundary.contains_row : BusBoundary → ℕ → ℕ → Bool
  | .First, row, _ => row == 0
  | .Last, row, height => row + 1 == height

/-- Row activation of one declaration. -/
inductive BusActivation (E : Type _) where
  | Always
  | Boundary (boundary : BusBoundary)
  | Boolean (selector : E)

/-- The declaring builder: the p3-air builder and the recorder's one method. -/
structure BusBuilder (F E S : Type _) extends AirBuilder F E S where
  record : S → String → BusDirection → List E → BusActivation E → S

/-- Declare one bus interaction.

A Boolean activation is asserted Boolean, then the declaration is recorded. -/
def BusBuilder.push_bus_interaction {F E S : Type _} [Zero F] [One F] (B : BusBuilder F E S)
    (s : S) (bus : String) (direction : BusDirection) (fields : List E)
    (activation : BusActivation E) : S :=
  let s := match activation with
    | .Boolean selector => B.assert_zero s (B.bool_check selector)
    | _ => s
  B.record s bus direction fields activation

end p3_bus.mirror
