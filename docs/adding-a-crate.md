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
   `[[oracle]]`. Only a crate outside the workspace, named by `package`, can
   list `features`: `extract.sh` makes them the default features of its copy
   (docs/extractor-issues.md 90).
2. Run `tools/extract/extract.sh` ([`extracting.md`](extracting.md)). On the
   first run it stops at step 6 and asks for `extraction/<Lib>/Assumptions/`
   `TypesExternal.lean` and `FunsExternal.lean`: write them from the
   `*External_Template.lean` files hax left in `.lake/extract/out/<crate>/`,
   with each hole an `opaque` constant, and write the library root
   `extraction/<Lib>.lean`.
3. Add `patches/post/` patches until `lake build` is green, and `patches/pre/`
   patches only when nothing else works (see [`patches.md`](patches.md)). An
   item the extractor drops is given its body by a pre patch that reshapes the
   Rust where the stop rules allow one, and by a transcription only otherwise
   ([`patches.md`](patches.md#pre-patch-or-transcription)). Each pre patch
   brings its own test and recorded mutation.
4. Delete `stub/` and point the crate's `[[lean_lib]]` at `extraction/`.
   Dependent crates keep importing the same library.
5. Stub, in their own crate directories, any dependencies that are referenced
   and not yet present.
6. Run `tools/extract/extract.sh --check` and update `STATUS.md`.

Extract from the bottom of the Cargo graph upwards where possible: each crate
extracted retires a stub that every crate above it relied on.

## A variant

To extract a crate again for another target, add a `[[variant]]` table to its
`crate.toml` ([`extracting.md`](extracting.md#variants)) and a `[[lean_lib]]`
for it in `lakefile.toml`, rooted at `crates/<crate>/variants/<name>/extraction`
and listed in `defaultTargets`. Then follow steps 2, 3 and 6 above, in
`variants/<name>/`. Its `Assumptions/` bind the externals of the `opaque`
modules to the crate's own library where they can, and give each `transmute`
the generated code needs a `core.intrinsics.Transmute` instance whose docstring
says, in a sentence starting "Assumed", which Rust layout it rests on.
