/-
The Lean model of BabyBear's NEON parameters: hax's extraction of p3-baby-bear
for AArch64 (crates/baby-bear/crate.toml, `[[variant]]`), in
`P3BabyBearNeon/Extraction/`, rooted at the `MontyParametersNeon` and
`PackedMontyParameters` impls for `BabyBearParameters`. Its namespace is
`p3_baby_bear_neon`; the traits are P3Monty31Neon's, and `BabyBearParameters`
and its `MontyParameters` constants are P3BabyBear's, by the bindings in
`P3BabyBearNeon/Assumptions/`.
-/
module

public import P3BabyBearNeon.Extraction

@[expose] public section
