# Extractor issues

Bugs and limitations in hax, charon and aeneas found while extracting Plonky3,
with how each is worked around here. They are the reason for most patches and
stubs, and each one is worth reporting upstream. Found with hax 0.4.1 (charon
`nightly-2026.09.02`, aeneas `build-183e4f0`) on p3-baby-bear, in
[Plonky3/Plonky3#2154](https://github.com/Plonky3/Plonky3/pull/2154). hax 0.4.2
keeps the same charon and aeneas and produces byte-identical output, so every
one of them is still present.

1. **hax does not pass `--target` to charon** (`into lean`). Charon also ignores
   `CARGO_BUILD_TARGET`, since it always passes its own `--target <host>`. The
   only way through is charon's `--targets`, which leads to 2.
2. **charon `--targets` drops hax's default-method roots.** Multi-target mode
   forces `--translate-all-methods`, then filters unused methods after the
   merge, which removes `clone_from` and `ne` (11 to 2 in the LLBC).
   Post-patch `010-restore-dropped-default-methods` of `baby-bear` and
   `monty-31`.
3. **aeneas's defining and using runs disagree on default-constant shapes.**
   `N.default (Self : Type) : Usize` in p3-monty-31's run is called as
   `N.default <inst> : RustM Usize` from p3-baby-bear's. Post-patch
   `baby-bear/020-trait-default-constant-shape`.
4. **aeneas silently drops `MontyField31::new_array` and `new_2d_array`.** They
   are in the LLBC with bodies, and no diagnostic is printed. Transcribed by
   hand in `crates/monty-31/extraction/P3Monty31/Assumptions/Mirror.lean`.
5. **aeneas's `__N` names for anonymous consts** trip mathlib's `nameCheck`
   linter. Post-patch `baby-bear/030-name-anonymous-const-assertions`.
6. **The seeded `Debug::fmt` signatures do not match `CoreModels`**: aeneas
   adds a `&mut Formatter` back-function that `core.fmt.Debug` lacks. Fixed in
   the hand-written `crates/baby-bear/extraction/P3BabyBear/Assumptions/FunsExternal.lean`.
7. **charon reports 2 `Type error after transformations` in the scoped
   p3-monty-31 run.** Both are in `core`'s own slice-iterator macros
   (`library/core/src/slice/iter/macros.rs:153`), which charon translates as a
   dependency, not in any Plonky3 item. aeneas exits 0, and nothing generated
   refers to them.
8. **charon splits option values on `,`**, so an impl pattern with two generic
   arguments cannot be written. The patterns omit the generics.
9. **Neither p3-monty-31 nor p3-mds extracts as a whole crate.** Whole-crate
   runs of both (with the pre-patches) fail in aeneas: each reaches p3-field's
   `PrimeCharacteristicRing`/`Algebra`/`Field`/`PrimeField`/`PackedField`
   group, which is mutually recursive through associated types ("mixed
   mutually recursive definitions"). `--opaque p3_field` does not help, because
   it hides bodies, not trait declarations. p3-mds also hits 28 unsupported
   lifetime constraints of its own. Hence the `scoped` state of both crates,
   and the `field` stub.
10. **charon and aeneas cannot lift `-> impl Trait` in trait methods**
    ([charon#1266](https://github.com/AeneasVerif/charon/issues/1266)). rustc
    desugars each into a hidden generic associated type, and p3-field has many.
    Pre-patches `baby-bear/020`, `030` and `040` hide them behind
    `cfg(hax_backend_lean)`.
11. **A scoped extraction of p3-poseidon1 fails** with an aeneas internal error
    in `core::iter`, and one of p3-poseidon2 fails on the body of
    `Poseidon2::new`. Both crates are stubs.
