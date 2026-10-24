/-
The Lean model of p3-sumcheck.

`P3Sumcheck/Extraction/` is hax's scoped extraction, rooted at `start_from` in crate.toml.

It holds the round arithmetic: interpolation through 0, 1 and infinity, and the claim reduction.

`P3Sumcheck/Mirror/` transcribes the rest of the verifier core over a field.

Each transcription has a `[[mirror]]` entry in crate.toml.
-/
module

public import P3Sumcheck.Extraction
public import P3Sumcheck.Mirror.Model
public import P3Sumcheck.Mirror.Lagrange
public import P3Sumcheck.Mirror.Data
public import P3Sumcheck.Mirror.GenericDegree
public import P3Sumcheck.Mirror.Strategy
public import P3Sumcheck.Mirror.Constraints

@[expose] public section
