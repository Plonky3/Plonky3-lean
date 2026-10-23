/-
The Lean model of p3-whir.

Nothing is extracted: the crate is generic over the field, challenger and Merkle traits, which aeneas rejects.

The verifier is transcribed over a field, one definition per Rust item.
-/
module

public import P3Whir.Model
public import P3Whir.Query
public import P3Whir.Verifier

@[expose] public section
