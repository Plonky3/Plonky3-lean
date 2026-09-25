# Adding a crate

## As a stub

A stub stands in for a crate that is not extracted yet, and contains only what
the extracted crates that depend on it reference.

1. Copy `crates/_template` to `crates/<plonky3 directory name>`, and set
   `lean_lib` to the module root hax uses for the crate, with `state = "stub"`.
2. Write `stub/<lean_lib>.lean` in hax's namespaces, so that generated code
   resolves against it unchanged.
3. Declare each item either `opaque` or as a transcription of the upstream item,
   with a `[[mirror]]` entry and the hash printed by `tools/mirror`.
4. Add the `[[lean_lib]]` to `lakefile.toml`.

## As an extraction

1. Set `state = "extracted"` and fill in `features`, `watch` and `[[oracle]]`.
2. Run `xtask extract <crate>`. Add `patches/post/` patches until `lake build` is
   green, and `patches/pre/` patches only when nothing else works (see
   [`patches.md`](patches.md)).
3. Delete `stub/` and point the crate's `[[lean_lib]]` at `extraction/`.
   Dependent crates keep importing the same library.
4. Stub, in their own crate directories, any dependencies that are referenced
   and not yet present.
5. Run `xtask check` and commit the regenerated `STATUS.md`.

Extract from the bottom of the Cargo graph upwards where possible: each crate
extracted retires a stub that every crate above it relied on.
