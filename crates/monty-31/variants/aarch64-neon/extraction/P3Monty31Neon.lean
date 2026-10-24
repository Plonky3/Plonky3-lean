/-
The Lean model of `PackedMontyField31Neon`'s arithmetic: hax's extraction of
p3-monty-31 for AArch64 (crates/monty-31/crate.toml, `[[variant]]`), in
`P3Monty31Neon/Extraction/`, rooted at the `Add`, `Sub`, `Neg` and `Mul` impls
and `halve_neon`. Its namespace is `p3_monty_31_neon`; `MontyField31` and its
functions are P3Monty31's, by the bindings in `P3Monty31Neon/Assumptions/`.
-/
module

public import P3Monty31Neon.Extraction

@[expose] public section
