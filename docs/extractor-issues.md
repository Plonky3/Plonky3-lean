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
   merge, which removes the `clone_from` and `ne` roots hax adds. Every derived
   `Clone` and `PartialEq` then comes out without those fields, and `lake build`
   fails with "Fields missing: `clone_from`" (and `ne`). Post-patch
   `010-restore-dropped-default-methods` of `baby-bear`, `goldilocks`,
   `koala-bear`, `mersenne-31` and `monty-31`.
3. **aeneas's defining and using runs disagree on default-constant shapes.**
   `N.default (Self : Type) : Usize` in p3-monty-31's run is called as
   `N.default <inst> : RustM Usize` from p3-baby-bear's, and `lake build`
   fails with application type mismatches. Post-patch
   `020-trait-default-constant-shape` of `baby-bear` and `koala-bear`.
4. **charon translates some items that aeneas does not emit.** aeneas emits only
   what charon lists in `ordered_decls`: the `--start-from` roots and everything
   they reach. charon also translates the other members of an impl it enters,
   with bodies, without listing them. Each crate's `extraction/gaps.toml` lists
   these items and `STATUS.md` shows them. No diagnostic is printed.
   charon also skips a provided-method override that nothing uses, even when it
   is a `--start-from` root (the pattern matches; no diagnostic), and a pattern
   cannot name one of several impls of a generic trait (`QuotientMap<u32>`,
   `QuotientMap<i32>`, …; see 200). `--translate-all-methods` makes charon translate and
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
   linter: nine warnings in each of p3-baby-bear's and p3-koala-bear's
   Poseidon tables. Post-patch `030-name-anonymous-const-assertions` of
   `baby-bear` and `koala-bear`.
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
    aeneas stops on those reachable from p3-baby-bear's roots ("Can not
    extract trait associated types with parameters", or a mixed recursion
    group): `RawDataSerializable`'s, reached through `Field`'s supertraits,
    `PackedValue::unpack_iter` and `Field::prepare_bit_plane_expansion`.
    `PackedFieldExtension`'s do not change the output, but charon warns on
    each. Pre-patches `baby-bear/020`, `030` and `040` hide them all behind
    `cfg(hax_backend_lean)`; `tools/extract/patch-necessity.py` shows each
    patch is needed.

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

23. **aeneas rejects a `return` or a `continue` that leaves a nested loop.**

    The errors are "Returns inside of nested loops are not supported yet" and "Continue to outer loops are not supported yet".

    p3-symmetric's two sponges absorb a block in an inner loop.

    The padding-free sponge leaves both loops with `break 'outer` when the input runs dry.

    The 10-padded sponge returns from inside the inner loop.

    Pre-patches `symmetric/020` and `030` give each one a body with a single loop over the input.

24. **aeneas names two `Clone` witnesses of a trait alike.**

    A trait such as `Permutation<T: Clone>: Clone` needs a `Clone` witness for `Self` and one for `T`.

    aeneas calls both `corecloneCloneInst`, and Lean rejects the structure.

    Post-patch `symmetric/010` renames the witness for the type parameter.

25. **CoreModels' `flatten` needs iterator items.**

    Rust's `Iterator::flatten` takes items that are `IntoIterator`, such as arrays.

    The model of `flatten` asks for an `Iterator` witness of the item type.

    aeneas passes the `IntoIterator` witness of an array, and the call does not elaborate.

    Pre-patch `symmetric/040` gives `CompressionFunctionFromHasher::compress` a body that collects the same items into a vector.

26. **aeneas passes `Vec`'s allocator to a CoreModels witness that has none.**

    The `IntoIterator` witness of `Vec<T>` is generated as applied to `T` and `alloc.alloc.Global`.

    CoreModels declares it over `T` only, so the call does not elaborate.

    Post-patch `symmetric/020` drops the allocator.

30. **aeneas stops on the signatures of the iterator adapters it reaches.**

    The internal error points at the declaration of `core::iter::Iterator`.

    It shows up as soon as a translated body calls an adapter such as `filter`, `any`, `max`, `flatten` or the `itertools` ones.

    p3-merkle-tree's verifier sorts and walks the matrices with `sorted_by_key`, `peekable` and `peeking_take_while`.

    Pre-patch `merkle-tree/010` gives the single-index and the hiding verifiers bodies with indexed loops.

    The provided body of `CryptographicHasher::hash_iter_slices` flattens its slices.

    `crates/symmetric/crate.toml` makes that body opaque, and no claim reads it.

31. **aeneas rejects a loop that pushes shared slices into a vector.**

    The error is "Found an already registered mapping", at the loop.

    A vector of row slices, built one matrix at a time, is how a verifier would hand rows of several matrices to one hash.

    Pre-patch `merkle-tree/010` hands them over through a small iterator over a range of positions instead.

60. **aeneas gives a closure that captures `&mut self` a back function that CoreModels cannot take.**

    The closure's `call_mut` returns its output, its new state and a back function.

    CoreModels' `FnMut::call_mut` returns the output and the new state, and `FnOnce::call_once` the output alone.

    CoreModels' `map` and `array::from_fn` also drop the closure's final state, so the captured challenger would not advance.

    p3-challenger samples through such closures: the duplex challenger's `sample`, and the provided `sample_array` and `sample_vec`.

    The sampling methods of the duplex and serializing challengers are transcribed instead.

    Post-patch `challenger/010` gives the provided `sample_vec`, which the run emits but no model calls, the pair shape and a loop.
61. **aeneas garbles a method with a `const` generic `bool` that picks a trait dictionary.**

    `sample_uniform_bits::<RESAMPLE>` passes one of two strategy dictionaries to a generic helper.

    aeneas emits the method under the helper's name, with every trait parameter twice and `RESAMPLE` unbound.

    It also leaves out the two strategy instances, and their types land in different universes, as for 20.

    The uniform bit sampling of the duplex challenger is transcribed instead.
62. **A sponge field generic over `PrimeField` pulls in p3-field's `BigUint` and `Packable` surface.**

    The multi-field challenger compares `F::order()` and `PF::order()`, which are `num-bigint` values with no model.

    Its packing helpers in p3-field loop over `BigUint` digits.

    Once `PrimeField::PrimeSubfield` is reached, aeneas also renames the members of `Field` for the whole run, so the other roots stop elaborating against the field stub.

    The multi-field challenger is transcribed instead.

90. **hax's lean backend does not pass cargo arguments on to charon.**

    `cargo hax -C --features <f> ; into lean` builds the crate without the features.

    tiny-keccak compiles its permutation only with one of its hash features, and its build script fails without one.

    `extract.sh` copies a crate from outside the workspace before extracting it.

    For such a crate, `tools/extract/default-features.py` writes the `features` of its crate.toml as the copy's default features.

    A workspace crate cannot have features yet, and `extract.sh` refuses one that lists them.

91. **aeneas rejects an array of borrowed slices read in a loop.**

    The errors are "Nested borrows are not supported yet" and "Could not match the contexts".

    p3-keccak's batched hash names each lane's message by a `&[u8]` in a `[&[u8]; VECTOR_LEN]`, and gathers words from them in loops.

    Pre-patch `keccak/020` names each message by its start in the input instead.

150. **CoreModels has no `String::from(&str)`.**

    p3-lookup's indexed column check copies the table name into its error.

    The generated code calls `alloc.string.String.Insts.CoreConvertFromShared0Str.from`, which CoreModels does not define.

    `HaxExt.lean` models it as decoding the bytes, which a `&str` guarantees are UTF-8.
151. **aeneas rejects p3-lookup's indexed declaration check**, which returns an error from inside two loops in turn, as in 23.

    The check is transcribed instead, and the column check it calls is extracted.

180. **p3-multilinear-util and p3-sumcheck did not compile in the extraction variant.**

    Under `cfg(hax_backend_lean)`, pre-patch `baby-bear/030` moves `to_ext_iter` onto an extension trait.

    Pre-patch `baby-bear/020` drops `Field`'s `RawDataSerializable` supertrait, which p3-sumcheck's bit ring switch reads through `TowerLevel`.

    Pre-patches `multilinear-util/010`, `sumcheck/010` and `sumcheck/020` import the trait and state the bound, so both crates now compile there.

    aeneas rejected the signature of `PackedFieldExtension::packed_ext_powers` ("Internal error" in `translate_fun_sigs`), a required method that the packing bound of `ExtensionField` reaches.

    Pre-patch `baby-bear/050` hides it and its 8 impls under the cfg, so code generic over `ExtensionField` now extracts.

    p3-multilinear-util's equality polynomial is the first such item.

    The quadratic verifier's round loop still does not extract.

    Rooted, it stops aeneas on five errors, all from the transcript that holds a mutable borrow of the challenger:

    - the transcript's constructor builds its state in a closure over that borrow ("Can't end abstraction ... non-endable");
    - a round reads the state through `Option::expect` on the borrowed option (an internal error in core's option.rs, line 968);
    - closing the transcript consumes the state ("Unimplemented");
    - the shape's pattern builds nested borrows ("Nested borrows are not supported yet");
    - the loop that carries the transcript has no fixed point ("Could not compute a loop fixed point in 2 iterations").

    A pre-patch would have to rewrite the transcript, so the loop stays transcribed.

    Two dependents failed in that variant, and now compile:

    - p3-multi-stark needed the same import as p3-sumcheck, and the same bound at 15 sites (pre-patches `multi-stark/010` and `020`);
    - rustc panicked on p3-binary-pcs ("escaping bound vars") while reporting the same unmet bound on a serde derive, at 13 sites (pre-patch `binary-pcs/010`).

    p3-binary-pcs now extracts, generic over the tower-level trait:

    - p3-binary-dft is scoped at its domain points and subspace polynomials;
    - P3BinaryField and P3BinaryDft declare the tower-level and encodable-level traits by hand, as aeneas would emit them;
    - `P3Security/Mirror/Queries.lean` assumes the floating-point query count as an opaque function (19);
    - post-patches `security/020` and `binary-pcs/010` expose the saturating operations (22).

    p3-bus's name check, RAM validation and RAM layout do not extract either; pre-patch `bus/010` says why for each.

240. **aeneas has no function types.**

    p3-word marks a shift's word width with `PhantomData<fn() -> W>`.

    aeneas stops on the field with "Arrow types are not supported yet".

    It then drops the shift type and every item that names it.

    Pre-patch `word/010` gives the extracted variant `PhantomData<W>`, which is zero-sized as well.

241. **aeneas drops six bodies of p3-word.**

    The system constructor bounds its three family sizes in a loop over an array, with an early return.

    The address validation and the scalar verifier return early from three loops in a row.

    The composition layout returns early from a loop nested in its loop over the calls.

    The lowering readdresses every operand through a closure, and the resolver fails with "Could not match the contexts".

    The errors are "Early returns inside of loops are not supported yet", "Returns inside of nested loops are not supported yet" and "Breaks to outer loops are not supported yet".

    Pre-patches `word/020` and `word/030` give each one an equivalent body, with one loop per function.

242. **aeneas expects a back function from `from_residual` in a function returning `&mut`.**

    The mutable accessors of p3-word's composition return a slice borrowed from their input, or an error.

    On the error path, aeneas destructures CoreModels' `from_residual` as a pair, while it returns the result alone.

    Post-patch `word/020` binds the result directly.

243. **aeneas leaves the state of a closure with several captures semireducible.**

    A closure that captures one value gets a reducible state type.

    A closure that captures two gets a pair, defined without the attribute.

    Its call site passes a pair literal, so the term is not type-correct at reducible transparency, and `simp` rejects every goal that contains it.

    Post-patch `word/030` marks the three such states of p3-word reducible.

244. **aeneas stops on three binary-field items.**

    p3-binary-dft's domain steps accumulate into a captured variable, and their closure gets a back function, as in 60.

    The generated `call_once` then does not elaborate against CoreModels' `FnOnce`.

    Pre-patch `binary-dft/010` gives the domain steps a plain loop, so they are extracted now.

    p3-binary-pcs's coset fold rewrites its scratch buffer in place across layers, and aeneas reports an internal error on that loop.

    The verifier's query-coset fold matches its challenges against a one-element slice pattern, and aeneas reports an inconsistent projection.

    The two folds stay transcribed, and their callers' claims read the transcriptions.

200. **charon's `--start-from` does not accept trait generics.** A pattern such
    as `{impl p3_field::integers::QuotientMap<u32> for …}::from_int` fails with
    "`--start-from` does not support trait generics", and charon exits 101.
    Methods of generic trait impls (`QuotientMap<w>`,
    `HasTwoAdicBinomialExtension<2>`, `BinomiallyExtendable<3>`) are reached
    instead through the `010-extraction-roots` pre-patches of p3-mersenne-31 and
    p3-monty-31.

210. **The `core::arch` intrinsics have no Rust bodies.** Each is a
     `#[target_feature]` wrapper around an LLVM builtin, and the models have no
     definitions for them, so a SIMD backend extracts to calls of undefined
     functions over opaque vector types. Pre-patch `monty-31/020` imports
     `p3_arch_shims::x86_64` (`arch/`) in place of `core::arch::x86_64` under the
     cfg, in every file on BabyBear's AVX2 path: models with the same names and
     signatures, over lane arrays, each transcribing Intel's pseudocode and
     tested against the hardware. Pre-patch `monty-31/030` does the same for
     BabyBear's NEON path, with `p3_arch_shims::aarch64` and Arm's pseudocode.
211. **`--exclude` on a type that an extracted type refers to makes aeneas fail**
     with "Internal error". `--opaque` on the same item works: the type becomes
     an external declaration. The AVX2 variants make the scalar modules opaque
     (`opaque` in a `[[variant]]` table) rather than excluding them.
212. **A run re-declares the traits of an `--opaque` module.** The opaque
     module's types and functions become externals, but its trait declarations
     are emitted again, so a second run of the same crate cannot share the first
     run's namespace. On x86_64 the re-declared `PackedMontyParameters` also
     differs: it gains the supertrait `MontyParametersAVX2`. Each variant is
     therefore renamed into its own namespace (`tools/extract/rename-variant.py`),
     and its `Assumptions/` bind its externals to the crate's own model.
213. **aeneas rejects `asm!`.** monty-31's NEON backend has one block, the
     optimisation barrier `confuse_compiler`, whose value is its input. Pre-patch
     `monty-31/030` replaces it with the identity under the cfg, a stand-in that
     TRUST.md lists.
