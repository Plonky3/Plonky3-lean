/-
The Lean model of p3-air.

The integer helpers are hax's scoped extraction in `P3Air/Extraction/`, rooted at `start_from` in crate.toml.

The builders, the symbolic expressions and the constraint checker are generic over the field traits, which aeneas rejects.

They are transcribed by hand in `P3Air/Assumptions/Mirror/`.
-/
module

public import P3Air.Extraction
public import P3Air.Assumptions.Mirror.Air

@[expose] public section
