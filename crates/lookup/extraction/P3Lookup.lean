/-
The Lean model of p3-lookup.

The signed-count record, the indexed column check and the gadget's constructor are hax's scoped extraction in `P3Lookup/Extraction/`, rooted at `start_from` in crate.toml.

Everything else is generic over the field traits or over the builder, which aeneas rejects.

It is transcribed by hand in `P3Lookup/Assumptions/Mirror/`.
-/
module

public import P3Lookup.Extraction
public import P3Lookup.Assumptions.Mirror.Api

@[expose] public section
