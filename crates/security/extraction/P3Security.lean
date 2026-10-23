/-
The Lean model of p3-security's integer arithmetic: hax's scoped extraction, in
`P3Security/Extraction/`, rooted at `start_from` in crate.toml. Its `f64`
arithmetic does not extract (aeneas has no floating-point binops); the
real-valued bounds are transcribed in `Plonky3Lean/Proofs/Security/`.
-/
module

public import P3Security.Extraction

@[expose] public section
