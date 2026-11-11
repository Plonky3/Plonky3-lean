/-
The Lean model of BabyBear's AVX-512 parameters: hax's extraction of p3-baby-bear
for x86_64 with AVX-512F (crates/baby-bear/crate.toml, `[[variant]]`), in
`P3BabyBearAvx512/Extraction/`, rooted at the `MontyParametersAVX512` and
`PackedMontyParameters` impls for `BabyBearParameters`. Its namespace is
`p3_baby_bear_avx512`; the traits are P3Monty31Avx512's, and `BabyBearParameters`
and its `MontyParameters` constants are P3BabyBear's, by the bindings in
`P3BabyBearAvx512/Assumptions/`.
-/
module

public import P3BabyBearAvx512.Extraction

@[expose] public section
