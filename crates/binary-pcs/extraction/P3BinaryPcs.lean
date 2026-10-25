/-
The Lean model of p3-binary-pcs.

`P3BinaryPcs/Extraction/` is hax's scoped extraction, rooted at `start_from` in crate.toml.

It holds the fold of a pair, the schedule's constructor and folding change, the batch count and the transcript shape.

`P3BinaryPcs/Mirror/` transcribes the crate over fields, one definition per Rust item.

Each transcription has a `[[mirror]]` entry in crate.toml.
-/
module

public import P3BinaryPcs.Extraction
public import P3BinaryPcs.Mirror.Model
public import P3BinaryPcs.Mirror.Params
public import P3BinaryPcs.Mirror.Transcript
public import P3BinaryPcs.Mirror.Fold
public import P3BinaryPcs.Mirror.Verifier

@[expose] public section
