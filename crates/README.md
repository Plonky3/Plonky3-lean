# `crates/`: the Lean model of Plonky3's Rust

One directory per Plonky3 crate, flat, named exactly as the crate's directory in
`plonky3/` (`crates/baby-bear` models `plonky3/baby-bear`). `_template/` is the
starting point for a new one.

## A crate is extracted, scoped or stubbed

Every crate directory provides one Lean library, named after the library hax
emits for the crate (`P3BabyBear`, `P3Monty31`); its declarations are in the
crate's namespace (`p3_baby_bear`). `crate.toml` records which of three states
provides it:

| `state` | Library source | Written by |
|---|---|---|
| `extracted` | `extraction/`: the whole crate | hax, then the `patches/post/` patches |
| `scoped` | `extraction/`: only the items reachable from the `start_from` roots in `crate.toml` | hax, then the `patches/post/` patches |
| `stub` | `stub/<lean_lib>.lean` | hand, only what dependent crates reference |

`scoped` is for a crate that does not extract whole yet but whose items a
dependent crate needs: the dependent's own extraction never contains them,
because aeneas emits only the crate it runs on. Moving a crate from `stub` to
`scoped` or `extracted` deletes `stub/` and changes nothing else: dependents
import the same library name either way.

A stub stands in for the crate it is named after, not for the crate that uses
it. Two crates that depend on `field` share `crates/field/stub/`.

## Inside `extraction/`

`extraction/` is laid out as hax lays out its own output directory, so the
module names the generated code imports resolve unchanged:

```
extraction/
  <Lib>.lean                 library root, hand-written: imports Extraction (and Assumptions/Mirror, if any)
  <Lib>/Extraction.lean      hax: imports Types and Funs
  <Lib>/Extraction/          hax, with the post patches applied; never edited by hand
    Types.lean  Funs.lean      the crate's types, and everything else
    *External.lean             one-line imports of Assumptions/*External
    *External_Template.lean    what aeneas expects Assumptions/*External to declare; not built
  <Lib>/Assumptions/         hand-written
    TypesExternal.lean  FunsExternal.lean   what the generated code imports by these names
    Mirror.lean                transcriptions of items the extraction does not produce
```

`tools/extract/extract.sh` rewrites `<Lib>/Extraction.lean` and
`<Lib>/Extraction/` and nothing else. It fails if a hand-written
`Assumptions/<X>External.lean` declares different names than the template
aeneas regenerated beside it.

## Every hand-written body is either assumed or mirrored

A declaration in `stub/` or in `extraction/<Lib>/Assumptions/` is one of:

- **`opaque`**: assumed. Nothing about its behaviour is claimed.
- **Mirrored**: a transcription of one upstream Rust item, with a `[[mirror]]`
  entry in `crate.toml` giving the Lean name and the Rust path, and a hash of
  the Rust item's token stream. When upstream changes the item, the hash changes
  and CI fails until someone re-reads the transcription and updates the hash.

CI rejects a hand-written declaration that is neither. Until `tools/mirror`
exists, the entries have no `hash`, and the transcriptions are re-read by hand
when a commit in the crate's `watch` paths touches them.

The `*External.lean` files hold only imports and `opaque` constants. Each
`opaque` constant is listed in [`STATUS.md`](../STATUS.md).

## Imports follow the Cargo graph

A crate's library may import only the libraries of its Cargo dependencies, plus
`Aeneas`, `CoreModels` and `HaxExt`. The generated code imports
`<Lib>.Assumptions.TypesExternal` and `FunsExternal`, which import the
dependencies' libraries.

## Layout of one crate

```
crates/<crate>/
  crate.toml                   state, extraction scope, re-extraction triggers,
                               oracle tables, mirrored items
  extraction/                  state = extracted or scoped (see above)
  stub/<lean_lib>.lean         state = stub
  patches/pre/NNN-slug.patch   Rust-side, applied to plonky3/ before hax and reverted after
  patches/post/NNN-slug.patch  Lean-side, applied to extraction/ after hax
```

Patch conventions are in [`docs/patches.md`](../docs/patches.md).
