/-
Transcriptions of the opening claims of p3-multi-stark.

These do not extract: they are generic over the field traits, which aeneas rejects.

Each definition transcribes one Rust item, named in the crate's mirror entries.

A vector is a list, and a panic is none.
-/
module

public import Mathlib.Algebra.Field.Basic
public import Mathlib.Data.List.Basic

@[expose] public section

namespace p3_multi_stark.opening.mirror

variable {K : Type _} [Field K]

/-- TableOpening: one table's current-row values, the columns read on the next row, and their successor values. -/
structure TableOpening (K : Type _) where
  local_values : List K
  next_columns : List ℕ
  next_values : List K

/-- TableOpening::empty. -/
def TableOpening.empty : TableOpening K := ⟨[], [], []⟩

/-- One step of OpeningClaims::next_row: write the value into its column, which panics past the width. -/
def scatterStep (row : Option (List K)) (cv : ℕ × K) : Option (List K) := do
  let row ← row
  if cv.1 < row.length then some (row.set cv.1 cv.2) else none

/-- OpeningClaims::new then OpeningClaims::next_row: pair each column with its value, which asserts equal lengths, then scatter them into a zero row of the width. -/
def next_row (next_columns : List ℕ) (next_values : List K) (width : ℕ) : Option (List K) :=
  if next_columns.length = next_values.length then
    (next_columns.zip next_values).foldl scatterStep (some (List.replicate width 0))
  else none

end p3_multi_stark.opening.mirror
