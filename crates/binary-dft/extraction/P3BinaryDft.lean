/-
The Lean model of p3-binary-dft.

Nothing is extracted: every transform is generic over the tower-level trait, which aeneas rejects.

The transforms are transcribed over a field, one definition per Rust item.
-/
module

public import P3BinaryDft.Model
public import P3BinaryDft.Domain
public import P3BinaryDft.Naive
public import P3BinaryDft.Butterfly
public import P3BinaryDft.Lch
public import P3BinaryDft.Traits
public import P3BinaryDft.Encoder

@[expose] public section
