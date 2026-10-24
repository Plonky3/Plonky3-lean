/-
The Lean model of p3-batch-stark.

The integer helpers are hax's scoped extraction in `P3BatchStark/Extraction/`, rooted at `start_from` in crate.toml.

The transcript, the challenge layout, the verifier, the check at zeta and the debug checker are generic over the configuration, the field traits and the AIR, which aeneas rejects.

They are transcribed by hand in `P3BatchStark/Assumptions/Mirror/`.
-/
module

public import P3BatchStark.Extraction
public import P3BatchStark.Assumptions.Mirror.Transcript
public import P3BatchStark.Assumptions.Mirror.Verifier
public import P3BatchStark.Assumptions.Mirror.Check
public import P3BatchStark.Assumptions.Mirror.Constraints

@[expose] public section
