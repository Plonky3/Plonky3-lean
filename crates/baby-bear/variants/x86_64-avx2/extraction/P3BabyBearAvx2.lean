/-
The Lean model of BabyBear's AVX2 parameters: hax's extraction of p3-baby-bear
for x86_64 with AVX2 (crates/baby-bear/crate.toml, `[[variant]]`), in
`P3BabyBearAvx2/Extraction/`, rooted at the `MontyParametersAVX2` and
`PackedMontyParameters` impls for `BabyBearParameters`. Its namespace is
`p3_baby_bear_avx2`; the traits are P3Monty31Avx2's, and `BabyBearParameters`
and its `MontyParameters` constants are P3BabyBear's, by the bindings in
`P3BabyBearAvx2/Assumptions/`.
-/
module

public import P3BabyBearAvx2.Extraction

@[expose] public section
