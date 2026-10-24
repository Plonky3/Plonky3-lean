/-
The Lean model of p3-blake3-air.

The constants, the message permutation, the generator's half quarter-round and the characteristic-2 G step on words are hax's scoped extraction in `P3Blake3Air/Extraction/`, rooted at `start_from` in crate.toml.

The AIR evaluations and the trace generators are generic over the builder and the field traits, which aeneas rejects.

They are transcribed by hand in `P3Blake3Air/Assumptions/Mirror/`.
-/
module

public import P3Blake3Air.Extraction
public import P3Blake3Air.Assumptions.Mirror.Binary

@[expose] public section
