/-
The Lean model of `PackedMontyField31AVX2`'s arithmetic: hax's extraction of
p3-monty-31 for x86_64 with AVX2 (crates/monty-31/crate.toml, `[[variant]]`), in
`P3Monty31Avx2/Extraction/`, rooted at the `Add`, `Sub`, `Neg` and `Mul` impls
and `halve_avx2`. Its namespace is `p3_monty_31_avx2`; `MontyField31` and its
functions are P3Monty31's, by the bindings in `P3Monty31Avx2/Assumptions/`.
-/
module

public import P3Monty31Avx2.Extraction

@[expose] public section
