/-
The Lean model of p3-dft.

Nothing is extracted: every backend is generic over the field traits, which aeneas rejects.

The transforms are transcribed over a field, one definition per Rust item.
-/
module

public import P3Dft.Model
public import P3Dft.Butterflies
public import P3Dft.Transforms
public import P3Dft.Parallel

@[expose] public section
