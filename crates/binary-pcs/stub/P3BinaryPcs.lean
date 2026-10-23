/-
The Lean model of p3-binary-pcs.

Nothing is extracted: the crate is generic over the tower-level, challenger and Merkle traits, which aeneas rejects.

The schedule, the transcript shape, the fold and the verifier are transcribed over fields, one definition per Rust item.
-/
module

public import P3BinaryPcs.Model
public import P3BinaryPcs.Params
public import P3BinaryPcs.Transcript
public import P3BinaryPcs.Fold
public import P3BinaryPcs.Verifier

@[expose] public section
