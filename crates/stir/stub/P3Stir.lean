/-
The Lean model of p3-stir.

Nothing is extracted: the crate is generic over the field traits, the MMCS and the challenger, which aeneas rejects.

Each item is transcribed over a field, one definition per Rust item.
-/
module

public import P3Stir.Model
public import P3Stir.Utils
public import P3Stir.Verifier

@[expose] public section
