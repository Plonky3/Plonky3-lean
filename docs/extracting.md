# Extracting

The generated Lean is committed, so building and checking the proofs needs only
Lean (see the [README](../README.md)). Regenerating it from `plonky3/` needs the
tools below. `tools/extract/extract.sh` checks each one against `toolchain.toml`
and installs nothing; a missing tool stops it with the command to run.

## Requirements

| Tool | Version | Install |
|---|---|---|
| Rust | current `stable`, via `rustup`: step 2 builds upstream's tests with it, as upstream CI does | <https://rustup.rs>; `rustup update stable` |
| `cargo-hax` | the build `toolchain.toml` pins, on `PATH` (or set `HAX_BIN` to another install) | a release: `cargo install --locked cargo-hax@<hax_release> --force`; a commit (`hax_release = ""`): `cargo install --locked --git https://github.com/cryspen/hax --rev <hax_commit> cargo-hax --force` |
| charon and aeneas | the builds the pinned hax resolves (`charon`, `aeneas` in `toolchain.toml`) | `(cd plonky3 && cargo hax tools install)`, checksum-verified, into `~/.cache/hax/` |
| charon's Rust toolchain | `rust_toolchain` in `toolchain.toml`, with `rust_components` and `target` | `rustup toolchain install <rust_toolchain> --profile minimal --component rustc-dev,llvm-tools,rust-src --target thumbv7em-none-eabi` |
| Lean | `lean-toolchain` | [elan](https://github.com/leanprover/elan), which fetches it on first use |
| other | `python3` (3.11 or later), `rsync`, `patch`, `git` | system packages |

## Run

```bash
git submodule update --init
tools/extract/extract.sh              # regenerate, patch, build
tools/extract/extract.sh --check      # the same, and fail unless the output is as committed
tools/extract/extract.sh --tools-only # check the requirements only
```

`--help` lists the steps. A run takes about a minute, most of it the
extractions and `lake build`. The exception is step 2: when `plonky3/` or a
pre-extraction patch has changed, it re-runs Plonky3's test suite on the tree
with and without the patches, which takes 10 to 20 minutes. The result is cached
on the content of the tree, under `.lake/extract/pretest/`.

After a run, `git diff crates/` shows what moved in the generated code, and
`tools/status.py` regenerates `STATUS.md` from it (CI checks that it is current).
`tools/extract/check-patches.sh` and `tools/extract/new-patch.sh` maintain the
patches; see [`patches.md`](patches.md).

## What a run extracts

Every crate whose `crate.toml` `state` is `extracted` (the whole crate) or
`scoped` (only the items reachable from its `start_from` roots). Each crate is a
separate `cargo hax into lean` run, with the pre-extraction patches of every
crate applied to `plonky3/` and the charon flags in `toolchain.toml`. hax writes
into a scratch directory under `.lake/extract/`; the script copies each crate's
`<Lib>/Extraction/` and `<Lib>/Extraction.lean` into
`crates/<crate>/extraction/` and applies the crate's post-extraction patches
there. It also writes `crates/<crate>/extraction/gaps.toml`
(`tools/extract/gap-report.py`): the errors charon reported, and every item of
the crate that charon translated with a body and aeneas did not emit
(extractor issue 4). It is committed, `--check` requires it to reproduce like the
generated Lean, and `tools/status.py` reads it into `STATUS.md`. Nothing else
under `crates/` is written.

A scoped crate also roots every item it transcribes by hand, so that its
`gaps.toml` shows what charon does with each one, and a fix in the extractor
shows up there first.

hax also emits `Extraction/<X>External_Template.lean`: the declarations the
generated code expects someone to supply. Each hand-written
`Assumptions/<X>External.lean` must declare exactly the names its template
does, and must state assumptions as `opaque` constants, not `axiom`s; step 6
fails otherwise. The templates are committed with the rest of `Extraction/` but
are never imported, so they are not built. The generated code is written as Lean
modules, so every hand-written file it imports (`Assumptions/`, the stubs,
`HaxExt.lean`) is one too: `module`, `public import`, and an
`@[expose] public section` so that proofs can unfold its definitions.

hax also writes a `Verification/ProofObligations.lean` scaffold for hand-written
proofs. It is not installed: the proofs live in `Plonky3Lean`.

### Variants

The run extracts every crate for `toolchain.toml`'s `target`, which has no SIMD,
so the models describe the portable code. A `[[variant]]` table in a crate's
`crate.toml` extracts the crate again for another target, such as a SIMD
backend:

```toml
[[variant]]
name = "x86_64-avx2"                   # crates/<crate>/variants/<name>/
target = "x86_64-unknown-linux-gnu"    # charon's --targets
target_features = ["avx2"]             # -Ctarget-feature=+<f>
lean_lib = "P3Monty31Avx2"             # the variant's library
namespace = "p3_monty_31_avx2"         # and namespace
start_from = ["..."]                   # its roots, as for a scoped crate
opaque = ["p3_monty_31::monty_31"]     # charon --opaque: the crate's portable modules
renames = { p3_monty_31 = "p3_monty_31_avx2" }   # optional: other crates' variants
```

A variant is a unit of its own (`<crate>@<name>`, `config.py units`): step 3
checks it for its target, step 4 extracts it and renames hax's library and
namespace to the variant's (`tools/extract/rename-variant.py`), and steps 6 and 7
install it into `crates/<crate>/variants/<name>/extraction/`, with its own
`Assumptions/`, `gaps.toml` and `patches/post/`. The generated code refers to
its own crate's items by names relative to the namespace and to other crates' by
absolute names, so only the `namespace`/`open`/`end` lines and the module root
change. Its `Assumptions/` bind each external from an `opaque` module to the
crate's own model, rather than assume it. A variant whose code refers to
another crate's items that the target re-declares, such as p3-baby-bear's AVX2
variant implementing p3-monty-31's AVX2 traits, maps that crate's namespace to
its variant's with `renames`, which rewrites every absolute `p3_monty_31.`
reference to `p3_monty_31_avx2.`. A variant whose items other variants
call by absolute name keeps the crate's namespace (p3-field's).

The SIMD backends call `core::arch` intrinsics, which have no Rust bodies.
Pre-patch `monty-31/020` redirects them, under the cfg, to `arch/`
(p3-arch-shims), lane-array models with the same names and signatures, which
`crates/arch-shims` extracts as `P3ArchShims` and `arch/tests/` checks against
the hardware. A `transmute` in the generated code means what its
`core.intrinsics.Transmute` instance says (`HaxExt.lean`); `STATUS.md` lists the
instances.

## Reading the extraction

The extracted surface of p3-baby-bear is four modules, `baby_bear`, `mds`,
`poseidon1` and `poseidon2`. All of it lands in
`crates/baby-bear/extraction/P3BabyBear/Extraction/Funs.lean` (about 2900
lines), except the four unit structs, which are `def … := Unit` in `Types.lean`.
Declarations appear in dependency order, not source order. Every generated
declaration carries its Rust path and source span:

```lean
/-- [p3_baby_bear::baby_bear::{impl p3_monty_31::data_traits::MontyParameters for p3_baby_bear::baby_bear::BabyBearParameters}::PRIME]
    Source: 'baby-bear/src/baby_bear.rs', lines 17:4-17:34
    Visibility: public -/
```

so `grep -n "baby_bear.rs', lines 17:" crates/baby-bear/extraction/P3BabyBear/Extraction/Funs.lean`
jumps from a Rust line to its Lean.

Everything is in the namespace of the crate (`p3_baby_bear`), and the Rust
module path becomes a dotted prefix.

| Rust | Lean |
|---|---|
| `pub struct BabyBearParameters;` (unit struct) | `@[reducible] def baby_bear.BabyBearParameters := Unit` |
| `const BABYBEAR_POSEIDON2_HALF_FULL_ROUNDS: usize = 4;` | `def poseidon2.BABYBEAR_POSEIDON2_HALF_FULL_ROUNDS : Std.Usize := 4#usize` |
| a constant computed by a call (`BabyBear::new_array([..])`) | `def … : RustM (Array (MontyField31 BabyBearParameters) 16#usize) := …`: it can fail, so it is in the monad |
| `impl MontyParameters for BabyBearParameters { const PRIME … }` | one `def` per item, `baby_bear.BabyBearParameters.Insts.P3_monty_31Data_traitsMontyParameters.PRIME`, then an instance `…Insts.P3_monty_31Data_traitsMontyParameters` |
| impl of a generic trait, `impl InternalLayerBaseParameters<BabyBearParameters, 16> for …` | the generic arguments are appended to the name: `…Insts.P3_monty_31Poseidon2InternalLayerBaseParametersBabyBearParameters16` |
| `#[derive(Clone, Default, Debug, …)]` | `…Insts.CoreCloneClone`, `…Insts.CoreDefaultDefault`, `…Insts.CoreFmtDebug`, … |
| `fn exp_root_d<R: PrimeCharacteristicRing>(val: R) -> R` | `def …exp_root_d {R : Type} (p3_fieldfieldPrimeCharacteristicRingInst : p3_field.field.PrimeCharacteristicRing R) (val : R) : RustM R`: a trait bound becomes an explicit instance argument |
| `const _: () = assert!(RC.len() == …);` | the first in each module is `def poseidon{1,2}._`; the rest are `def poseidon{1,2}.const_check_N` (renamed from aeneas's `__N` by a post-patch) |
| a `while` loop | `…_loop.body` (one iteration, returning `cont`/`done`) and `…_loop` (the loop over it) |

Trait declarations from other crates (`MontyParameters`, `MDSUtils`, …) are
Lean `structure`s whose fields are the trait's items; supertraits are fields
named `…Inst`.

Code is in `RustM`: `ok x` returns, `fail .panic` panics. Every operation that
can panic is a bind `let x ← …`: arithmetic (`a + b` fails on overflow),
`Array.index_usize`, and `massert c` (Rust's `assert!`, including
`const { assert!(..) }` blocks, which aeneas keeps as runtime checks). Integers
are `Std.U32`, `Std.Usize`, …, with literals written `2013265921#u32`. `[T; N]`
is `Array T N#usize`, `&[T]` is `Slice T`, `Vec<T>` is `alloc.vec.Vec T`.
Shared references are erased; `&mut` becomes a returned updated value.
Generated constants are `@[irreducible]`: to compute with one in a proof,
`unfold` it by name, as `Plonky3Lean/Proofs/Field/BabyBear.lean` does.
