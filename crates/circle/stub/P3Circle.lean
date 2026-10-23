/-
The Lean model of p3-circle.

Nothing is extracted: the crate is generic over the field traits, the matrix commitment scheme and the challenger, which aeneas rejects.

Each item is transcribed over a field, one definition per Rust item.
-/
module

public import P3Circle.Point
public import P3Circle.Domain
public import P3Circle.Ordering
public import P3Circle.Cfft
public import P3Circle.Folding

@[expose] public section
