/-
The Lean model of p3-blake2s-air.

The constants, the G step on words and the bit-sliced helpers of the packed generator are hax's scoped extraction in `P3Blake2sAir/Extraction/`, rooted at `start_from` in crate.toml.

The AIR evaluation and the trace generator are generic over the builder and the field traits, which aeneas rejects.

They are transcribed by hand in `P3Blake2sAir/Assumptions/Mirror/`.
-/
module

public import P3Blake2sAir.Extraction
public import P3Blake2sAir.Assumptions.Mirror.Generation

@[expose] public section
