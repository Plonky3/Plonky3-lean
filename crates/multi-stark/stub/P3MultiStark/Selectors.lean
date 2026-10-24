/-
Transcriptions of the boundary selectors of p3-multi-stark.

These do not extract.
They are generic over the field traits, which aeneas rejects.

Each definition transcribes one Rust item, named in the crate's mirror entries.

A point is the list of its coordinates, and a field element is an element of a field K.

The packed forms are left out.
They compute the same values one lane at a time.
-/
module

public import Mathlib.Algebra.Field.Basic

@[expose] public section

namespace p3_multi_stark.selectors.mirror

variable {K : Type _} [Field K]

/-- BoundaryEvals: the first-row, last-row and transition selectors at one point. -/
structure BoundaryEvals (K : Type _) where
  first : K
  last : K
  transition : K

/-- One step of BoundaryEvals::at: multiply the running products by 1 - r and by r. -/
def atStep (acc : K × K) (r : K) : K × K := (acc.1 * (1 - r), acc.2 * r)

/-- BoundaryEvals::at: the two running products over the coordinates.

The transition is one minus the last-row product. -/
def BoundaryEvals.at (rs : List K) : BoundaryEvals K :=
  let acc := rs.foldl atStep (1, 1)
  ⟨acc.1, acc.2, 1 - acc.2⟩

/-- BoundaryEvals::apply: fold one more bound coordinate into the running prefix. -/
def BoundaryEvals.apply (b : BoundaryEvals K) (r : K) : BoundaryEvals K :=
  ⟨b.first * (1 - r), b.last * r, 1 - b.last * r⟩

/-- BoundaryEvals::from_row: the three indicators of one row of the residual cube. -/
def BoundaryEvals.from_row (row height : ℕ) : BoundaryEvals K :=
  ⟨if row = 0 then 1 else 0, if row + 1 = height then 1 else 0, if row + 1 < height then 1 else 0⟩

/-- BoundaryEvals::from_row_with_prefix: the residual indicators combined with the bound prefix. -/
def BoundaryEvals.from_row_with_prefix (row height : ℕ) (pre : BoundaryEvals K) :
    BoundaryEvals K :=
  let s : BoundaryEvals K := BoundaryEvals.from_row row height
  ⟨pre.first * s.first, pre.last * s.last, s.transition + s.last * pre.transition⟩

end p3_multi_stark.selectors.mirror
