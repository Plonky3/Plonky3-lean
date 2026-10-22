# Extractor issues

Bugs and limitations in hax, charon and aeneas met while extracting Plonky3 with
the toolchain `toolchain.toml` pins, with how each is worked around here. They
are the reason for most patches and stubs, and each one is worth reporting
upstream. Patch headers cite them by number, so an item that no longer applies
keeps its number and says so.

1. **hax does not pass `--target` to charon** (`into lean`). Charon also ignores
   `CARGO_BUILD_TARGET`, since it always passes its own `--target <host>`. The
   only way through is charon's `--targets`, which leads to 2.
2. **charon `--targets` drops hax's default-method roots.** Multi-target mode
   forces `--translate-all-methods`, then filters unused methods after the
   merge, which removes the `clone_from` and `ne` roots hax adds.
   Post-patch `010-restore-dropped-default-methods` of `baby-bear`,
   `goldilocks`, `koala-bear`, `mersenne-31` and `monty-31`.
3. **aeneas's defining and using runs disagree on default-constant shapes.**
   `N.default (Self : Type) : Usize` in p3-monty-31's run is called as
   `N.default <inst> : RustM Usize` from p3-baby-bear's. Post-patch
   `020-trait-default-constant-shape` of `baby-bear` and `koala-bear`.
4. **charon translates some items that aeneas does not emit.** aeneas emits only
   what charon lists in `ordered_decls`: the `--start-from` roots and everything
   they reach. charon also translates the other members of an impl it enters,
   with bodies, without listing them. Each crate's `extraction/gaps.toml` lists
   these items and `STATUS.md` shows them; for p3-monty-31 they are the
   MontyField31 impl members no root reaches (`try_inverse`, the `QuotientMap`
   conversions, `Sum`, `dot_product`, …). No diagnostic is printed.
   `PrimeCharacteristicRing::halve` is not translated at all: the trait
   provides a default body that MontyField31 overrides, and charon skips a
   provided method that nothing uses, even when it is a `--start-from` root (the
   pattern matches; no diagnostic). `--translate-all-methods` makes charon
   translate and list it, but also pulls in p3-field's trait hierarchy, which
   aeneas rejects (9). It is transcribed in
   `crates/monty-31/extraction/P3Monty31/Assumptions/Mirror.lean`.
   For p3-mersenne-31, pre-patch `010-extraction-roots` roots the run at a
   `cfg(hax_backend_lean)` module of one-line free functions, one per needed
   method. Each method is then reachable from a free function, so charon
   lists it and aeneas emits its own body, `halve` and the trait-impl
   `from_int`s included.
5. **aeneas's `__N` names for anonymous consts** trip mathlib's `nameCheck`
   linter. Post-patch `030-name-anonymous-const-assertions` of `baby-bear` and
   `koala-bear`.
6. **The seeded `Debug::fmt` signatures do not match `CoreModels`**: aeneas
   adds a `&mut Formatter` back-function that `core.fmt.Debug` lacks. Fixed in
   the hand-written `crates/baby-bear/extraction/P3BabyBear/Assumptions/FunsExternal.lean`.
7. **No longer applies:** the pinned charon reports no `Type error after
   transformations` for the scoped p3-monty-31 run. The count and sites, if any
   appear, are in `crates/monty-31/extraction/gaps.toml`.
8. **charon splits option values on `,`**, so an impl pattern with two generic
   arguments cannot be written. The patterns omit the generics.
9. **Neither p3-monty-31 nor p3-mds extracts as a whole crate.** Whole-crate
   runs of both (with the pre-patches) fail in aeneas: each reaches p3-field's
   `PrimeCharacteristicRing`/`Algebra`/`Field`/`PrimeField`/`PackedField`
   group, which is mutually recursive through associated types ("mixed
   mutually recursive definitions"). `--opaque p3_field` does not help, because
   it hides bodies, not trait declarations. p3-mds also hits 28 unsupported
   lifetime constraints of its own. Hence the `scoped` state of both crates,
   and the `field` stub. In p3-binary-field the group is reached through any
   tower arithmetic, since `TowerLevel: Field` and each level calls the level
   below through `TowerLevel` methods; pre-patch `binary-field/040` gives the
   arithmetic inherent copies of those methods. A trait method of the group
   (`square`, `try_inverse`, …) still cannot be a root.
10. **charon and aeneas cannot lift `-> impl Trait` in trait methods**
    ([charon#1266](https://github.com/AeneasVerif/charon/issues/1266)). rustc
    desugars each into a hidden generic associated type, and p3-field has many.
    Pre-patches `baby-bear/020`, `030` and `040` hide them behind
    `cfg(hax_backend_lean)`.
11. **A scoped extraction of p3-poseidon1 fails** with an aeneas internal error
    in `core::iter`, and one of p3-poseidon2 fails on the body of
    `Poseidon2::new`. Both crates are stubs.
12. **aeneas does not support dereferencing a raw pointer** ("Aeneas does not
    yet support dereferencing raw pointers"). p3-binary-field's `Poly192::limbs`
    reborrows `[Poly64; 3]` as `&[u64; 3]` through one; pre-patch
    `binary-field/050` gives the products a copy instead.
13. **`@[global_simps, irreducible]` on a long array literal reaches the maximum
    recursion depth**: registering the simp lemma of an irreducible constant
    unfolds it, which fails on p3-binary-field's 511-entry `tables::EXP` (either
    attribute alone elaborates). Post-patch `binary-field/010` keeps only
    `irreducible` there.
14. **The models lack `transmute`, `slice::from_ref`, `as_chunks_mut` and a zip
    over `IterMut`.** aeneas emits calls to them, which do not elaborate.
    p3-sha256's `Sha256Compress::compress` uses all four; pre-patch
    `sha256/010` gives the extracted variant the same body with a copied block
    and indexed writes.
15. **aeneas runs out of memory on sha2's unrolled SHA-256 backend**, the one a
    default build for the extraction target compiles: 64 inlined rounds exceed
    20 GB. Its round constants are also read through raw pointers. The sha2
    run selects the compact backend with sha2's own cfg
    (`crates/sha2/crate.toml`), so the model is that backend.
