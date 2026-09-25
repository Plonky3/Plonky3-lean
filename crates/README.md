# `crates/`: the Lean model of Plonky3's Rust

One directory per Plonky3 crate, flat, named exactly as the crate's directory in
`plonky3/` (`crates/baby-bear` models `plonky3/baby-bear`). `_template/` is the
starting point for a new one.

## A crate is either stubbed or extracted

Every crate directory provides one Lean library, named after the module root hax
emits for the crate (`p3_baby_bear`, `p3_monty_31`). `crate.toml` records which of
two states provides it:

| `state` | Library source | Written by |
|---|---|---|
| `extracted` | `extraction/<lean_lib>.lean` | hax, then the `patches/post/` patches |
| `stub` | `stub/<lean_lib>.lean` | hand, only what dependent crates reference |

Moving a crate from `stub` to `extracted` deletes `stub/` and changes nothing
else: dependents import the same library name either way.

A stub stands in for the crate it is named after, not for the crate that uses it.
Two crates that depend on `monty-31` share `crates/monty-31/stub/`.

## Every hand-written body is either assumed or mirrored

A declaration in `stub/` is one of:

- **`opaque`**: assumed. Nothing about its behaviour is claimed.
- **Mirrored**: a transcription of one upstream Rust item, with a `[[mirror]]`
  entry in `crate.toml` giving the Lean name, the Rust path and a hash of the
  Rust item's token stream. When upstream changes the item, the hash changes
  and CI fails until someone re-reads the transcription and updates the hash.

CI rejects a stub declaration that is neither.

## Imports follow the Cargo graph

An extracted crate may import only the libraries of its Cargo dependencies, plus
`Hax` and `HaxExt`. The dependency imports are generated at extraction time from
`cargo metadata`.

## Layout of one crate

```
crates/<crate>/
  crate.toml                   state, extraction settings, re-extraction triggers,
                               oracle tables, mirrored items
  extraction/<lean_lib>.lean   state = extracted: hax output with post patches applied
  stub/<lean_lib>.lean         state = stub
  patches/pre/NNN-slug.patch   Rust-side, applied to plonky3/ before hax and reverted after
  patches/post/NNN-slug.patch  Lean-side, applied to the hax output
```

Patch conventions are in [`docs/patches.md`](../docs/patches.md).
