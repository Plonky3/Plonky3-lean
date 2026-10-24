/-
The Lean model of p3-sha256-air.

The constants, the limb split and the sigma functions of the characteristic-2 generator are hax's scoped extraction in `P3Sha256Air/Extraction/`, rooted at `start_from` in crate.toml.

The AIR evaluations and the trace generators are generic over the builder and the field traits, which aeneas rejects.

They are transcribed by hand in `P3Sha256Air/Assumptions/Mirror/`.
-/
module

public import P3Sha256Air.Extraction
public import P3Sha256Air.Assumptions.Mirror.Binary

@[expose] public section
