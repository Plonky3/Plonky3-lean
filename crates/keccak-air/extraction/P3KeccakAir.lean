/-
The Lean model of p3-keccak-air.

The tables and the characteristic-2 round on words are hax's scoped extraction in `P3KeccakAir/Extraction/`, rooted at `start_from` in crate.toml.

The AIR evaluations and the trace generators are generic over the builder and the field traits, which aeneas rejects.

They are transcribed by hand in `P3KeccakAir/Assumptions/Mirror/`.
-/
module

public import P3KeccakAir.Extraction
public import P3KeccakAir.Assumptions.Mirror.Constants

@[expose] public section
