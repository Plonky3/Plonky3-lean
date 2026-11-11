/-
The Lean model of `PackedMontyField31AVX512`'s arithmetic: hax's extraction of
p3-monty-31 for x86_64 with AVX-512F (crates/monty-31/crate.toml, `[[variant]]`), in
`P3Monty31Avx512/Extraction/`, rooted at the `Add`, `Sub`, `Neg` and `Mul` impls
and `halve_avx512`. Its namespace is `p3_monty_31_avx512`; `MontyField31` and its
functions are P3Monty31's, by the bindings in `P3Monty31Avx512/Assumptions/`.
-/
module

public import P3Monty31Avx512.Extraction

@[expose] public section
