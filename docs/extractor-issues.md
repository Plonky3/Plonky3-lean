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
   these items and `STATUS.md` shows them. No diagnostic is printed.
   charon also skips a provided-method override that nothing uses, even when it
   is a `--start-from` root (the pattern matches; no diagnostic), and a pattern
   cannot name one of several impls of a generic trait (`QuotientMap<u32>`,
   `QuotientMap<i32>`, …). `--translate-all-methods` makes charon translate and
   list such methods, but also pulls in p3-field's trait hierarchy, which aeneas
   rejects (9).
   For p3-mersenne-31 and p3-monty-31, pre-patch `010-extraction-roots` roots the
   run at a `cfg(hax_backend_lean)` module of one-line free functions, one per
   needed method. Each method is then reachable from a free function, so charon
   lists it and aeneas emits its own body, `halve` and the trait-impl
   `from_int`s included. For p3-monty-31 the rest are the MontyField31 impl
   members that no wrapper can reach (`try_inverse`, `mul_2exp_u64`,
   `div_2exp_u64`, `Sum`, `dot_product`, …), listed in its `gaps.toml`.
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
   and the `field` stub.
   What reaches the group is a trait dictionary, not a trait method: a method a
   concrete type implements, called on that type, extracts on its own (p3-binary-
   field's `square`, `try_inverse`, … are roots of pre-patch `binary-field/070`).
   A dictionary is needed by a call to a default method of the group
   (`is_zero`, `inverse`, …), by `TowerLevel` methods, which name the group
   through `TowerLevel: Field`, and by a field's `Div`, whose `inverse` makes it
   mutually recursive with the `Field` impl. In p3-binary-field, pre-patches
   `binary-field/040` and `060` give each such call an inherent copy to resolve
   to. Code generic over `F: Field` still needs the dictionary.
10. **charon and aeneas cannot lift `-> impl Trait` in trait methods**
    ([charon#1266](https://github.com/AeneasVerif/charon/issues/1266)). rustc
    desugars each into a hidden generic associated type, and p3-field has many.
    Pre-patches `baby-bear/020`, `030` and `040` hide them behind
    `cfg(hax_backend_lean)`.

    The matrix trait of p3-matrix returns opaque iterators from every row method.

    Charon translates those, but aeneas stops on the trait declaration ("Unimplemented").

    The associated types they desugar to are generic over a lifetime.

    Pre-patch `matrix/020` hides the row methods from p3-matrix's own run, behind a cfg only that run sets.
11. **A scoped extraction of p3-poseidon1 fails** with an aeneas internal error
    in `core::iter`, and one of p3-poseidon2 fails on the body of
    `Poseidon2::new`. Both crates are stubs.
12. **aeneas does not support dereferencing a raw pointer** ("Aeneas does not
    yet support dereferencing raw pointers"). p3-binary-field's `Poly192::limbs`
    reborrows `[Poly64; 3]` as `&[u64; 3]` through one; pre-patch
    `binary-field/050` gives the products and `square` a copy instead. A closure
    that returns references into the coordinates, as in `Poly192`'s dot
    products, fails aeneas's borrow checker instead ("Can't end abstraction").
13. **`@[global_simps, irreducible]` on a long array literal reaches the maximum
    recursion depth**: registering the simp lemma of an irreducible constant
    unfolds it, which fails on p3-binary-field's 511-entry `tables::EXP` (either
    attribute alone elaborates). Post-patch `binary-field/010` keeps only
    `irreducible` there.
14. **The models lack `transmute`, `slice::from_ref`, `as_chunks_mut` and the
    mutable slice iterator `IterMut`** (so `iter_mut().zip(..)` and
    `iter_mut().enumerate()`). aeneas emits calls to them, which do not
    elaborate. Pre-patch `sha256/010` gives `Sha256Compress::compress` the same
    body with a copied block and indexed writes, and pre-patch `blake2s/010`
    gives the scalar `hash_many` indexed writes.
15. **aeneas runs out of memory on sha2's unrolled SHA-256 backend**, the one a
    default build for the extraction target compiles: 64 inlined rounds exceed
    20 GB. Its round constants are also read through raw pointers (12). The sha2
    run selects the compact backend with sha2's own cfg
    (`crates/sha2/crate.toml`), so the model is that backend.
16. **aeneas rejects hybrid-array's `Array` and `ArraySize`**, a type and a
    trait mutually recursive through an associated type ("mixed mutually
    recursive definitions"), as for 9. Every RustCrypto `Digest` (sha2's
    `Sha256`, blake2's `Blake2s`) stores its buffer in one, so the incremental
    hashers do not extract. charon's `--monomorphize` would remove the trait,
    but hax's lean backend passes `--no-gen-tuple-structs`, which charon
    refuses alongside it. p3-blake2s assumes `Blake2s256::hash`; p3-sha256's
    `hash_iter` and `hash_iter_slices` are not extracted.
17. **aeneas rejects a loop that runs while a struct holding a shared slice is
    borrowed** ("Joining region abstractions containing shared loans whose shared
    value contains borrows"), **and a trait method that recurses with a generic
    function through its default implementation** ("mixed mutually recursive
    definitions"). p3-blake3's batch driver loads blocks in loops over
    `&Lanes`, whose `batch` field is a `&[u8]`, and its `Backend` trait forwards
    `hash_group`, `subtree`, `leaf` and `parent` to generic functions that call
    back into it. Pre-patch `blake3/020` gives the extracted variant a copy of
    the driver whose loops take the slice as an argument and whose tree calls
    the generic functions directly, on the one-lane backend.
18. **aeneas rejects a borrow-carrying value joined across `match` arms or reassigned in a loop.**

    The errors are "Found a case of unsupported nested borrows" and "Unreachable", as for 17.

    p3-security's budget `SecurityTerm` holds a `&'static str` label.

    `security_report` builds one term in a `match`.

    `SecurityReport::binding_term` keeps a running term in a loop.

    Pre-patch `security/010` moves the `match` into its own function.

    Pre-patch `security/020` runs the loop over the plain `u64` bit counts.

19. **aeneas has no floating-point arithmetic.**

    An `f64` operation fails with "Invalid inputs for binop".

    Every `f64` function of p3-security comes out without a body, so none is rooted.

    These are `proximity::compute_upper_m`, `ErrorBits`, and the FRI, DEEP, LogUp and WHIR bounds.

    Their readings over the reals are transcribed in `Plonky3Lean/Proofs/Security/`.

    The rounding of `f64` itself is checked by Rust tests, not modelled.

20. **aeneas binds the type parameters of a recursive impl in a polymorphic universe.**

    The trait defaults the impl passes itself to live in the lowest universe.

    A default whose body builds a closure or a view lives there, so the impl fails to elaborate.

    Post-patch `matrix/010` puts the parameters in the lowest universe.
21. **aeneas resolves a recursive impl only through functions marked as trait defaults.**

    A default may pass the impl to a closure's call instance, or to another function.

    Two matrix defaults do, so every matrix impl is left unresolved.

    Post-patch `matrix/020` marks those three definitions.
22. **The saturating operations of aeneas have no exposed body.**

    They are declared without exposing their definitions, so an importing module sees only their signatures.

    No proof can then say what they return.

    `HaxExt.lean` models word subtraction clamped at 0 again, exposed, and post-patch `matrix/030` calls that model.
