# Adding a crate

## As a stub

A stub stands in for a crate that is not extracted yet, and contains only what
the extracted crates that depend on it reference.

1. Copy `crates/_template` to `crates/<plonky3 directory name>`, and set
   `lean_lib` to the library hax would emit for the crate (`P3Field` for
   p3-field), with `state = "stub"`.
2. Write `stub/<lean_lib>.lean` in hax's namespaces (`p3_field.field.Field`), so
   that generated code resolves against it unchanged. A trait becomes a
   `structure` with only the members dependent crates project.
3. Declare each item either `opaque` or as a transcription of the upstream item,
   with a `[[mirror]]` entry and the hash printed by `tools/mirror`.
4. Add the `[[lean_lib]]` to `lakefile.toml`, with `srcDir = "crates/<crate>/stub"`.

## As an extraction

1. Set `state = "extracted"`, or `state = "scoped"` with `start_from` roots when
   the whole crate does not extract yet, and fill in `features`, `watch` and
   `[[oracle]]`.
2. Run `tools/extract/extract.sh` ([`extracting.md`](extracting.md)). On the
   first run it stops at step 6 and asks for `extraction/<Lib>/Assumptions/`
   `TypesExternal.lean` and `FunsExternal.lean`: write them from the
   `*External_Template.lean` files hax left in `.lake/extract/out/<crate>/`,
   with each hole an `opaque` constant, and write the library root
   `extraction/<Lib>.lean`.
3. Add `patches/post/` patches until `lake build` is green, and `patches/pre/`
   patches only when nothing else works (see [`patches.md`](patches.md)).
4. Delete `stub/` and point the crate's `[[lean_lib]]` at `extraction/`.
   Dependent crates keep importing the same library.
5. Stub, in their own crate directories, any dependencies that are referenced
   and not yet present.
6. Run `tools/extract/extract.sh --check` and update `STATUS.md`.

Extract from the bottom of the Cargo graph upwards where possible: each crate
extracted retires a stub that every crate above it relied on.
