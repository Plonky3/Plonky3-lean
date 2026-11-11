/-
The Lean model of p3-binary-dft.

`P3BinaryDft/Extraction/` is hax's scoped extraction, rooted at `start_from` in crate.toml.

It holds the domain, the twiddle state and the Lin-Chung-Han transform, generic over the butterfly trait.

`P3BinaryDft/Encodable.lean` declares the encodable-level trait for code generic over it.

`P3BinaryDft/Assumptions/` declares the element size and the staged group, which are opaque.

`P3BinaryDft/Mirror/` transcribes the transforms over a field, as the specifications of the extracted ones.

Each transcription has a `[[mirror]]` entry in crate.toml.
-/
module

public import P3BinaryDft.Extraction
public import P3BinaryDft.Encodable
public import P3BinaryDft.Mirror.Model
public import P3BinaryDft.Mirror.Domain
public import P3BinaryDft.Mirror.Naive
public import P3BinaryDft.Mirror.Butterfly
public import P3BinaryDft.Mirror.Lch
public import P3BinaryDft.Mirror.Traits
public import P3BinaryDft.Mirror.Encoder

@[expose] public section
