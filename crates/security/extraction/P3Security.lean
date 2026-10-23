/-
The Lean model of p3-security's integer arithmetic.

It is hax's scoped extraction in `P3Security/Extraction/`, rooted at `start_from` in crate.toml.

The floating-point arithmetic does not extract, because aeneas has no floating-point operations.

The real-valued bounds are transcribed by hand in `Plonky3Lean/Proofs/Security/`.
-/
module

public import P3Security.Extraction

@[expose] public section
