# Patches

Two kinds, per crate, kept apart because they cost different amounts of trust.

| | `patches/pre/` | `patches/post/` |
|---|---|---|
| Patches | Rust in `plonky3/` (any crate in the workspace) | the crate's generated Lean (`extraction/<Lib>/Extraction/`) |
| Paths from | `plonky3/` | `crates/<crate>/` (`extraction/P3BabyBear/Extraction/Funs.lean`) |
| Applied | before `cargo hax` runs, every crate's, for every crate's run | after `cargo hax` runs |
| Reverted | yes, unconditionally, on exit | no: the result is committed |
| Trust cost | **changes the artifact under verification** | changes only the Lean encoding of it |
| Checked by | `test-pre-patches.py`, `check-mutations.py`, and a `cargo check` of the extracted variant | `lake build` |

- **`patches/pre/`** changes the Rust before hax runs. The model then describes
  a patched Plonky3, not the one that ships, and nothing proved on the Lean side
  can close that gap. CODEOWNERS assigns these to the Plonky3 maintainers. Three
  rules keep the cost down:
  1. **Gate on `cfg(hax_backend_lean)`.** Extraction sets that cfg for every
     crate (`rustflags` in `toolchain.toml`); normal builds never do. A patch
     that only changes what exists under the cfg leaves the normal build, and
     so every upstream test, exactly as shipped. What remains unconditional must
     be provably inert, such as a redundant (implied) trait bound or the cfg's
     check-cfg declaration.
  2. **Let rustc check the claim.** `extract.sh` compiles each extracted crate
     under the cfg, the variant charon sees, so anything still reachable that
     used a hidden item fails to compile.
  3. **Make the case in tests, and show they can fail.** Every pre patch adds
     a test, in the normal build, of what it promises leaves that build
     unchanged, and records a mutation that breaks that promise and fails the
     test ([Tests and mutations](#tests-and-mutations)).
- **`patches/post/`** changes the Lean that hax generated. The Rust is
  untouched; the patch is a claim about the encoding. A reviewer checks it by
  reading the diff, or by comparing the committed output with the pristine one
  that the last run left in `.lake/extract/pristine/`.

## Pre-patch or transcription?

When the extractor drops or mistranslates an item, there are two ways to give
the model its body: a pre patch that reshapes the Rust so that the extractor
translates it, or a hand-written Lean transcription with a `[[mirror]]` entry
(`crates/README.md`). Prefer the pre patch. The extractor then translates the
code Plonky3 ships, in its own shape, and the patch's tests and mutation check
the reshaping mechanically, where a transcription is only as faithful as its
author's reading and a reviewer's re-reading.

A pre patch goes too far, and a transcription (or a stub) is used instead, if
it would:

- change behaviour or any public signature in the normal build;
- change constants, arithmetic, the evaluation order of observable effects, or
  the algorithm, rather than only its shape;
- reimplement logic that belongs to a dependency;
- add `unsafe`;
- introduce any upstream-test divergence; or
- rewrite more than the one item it names.

## Rules

- One logical change per file, named `NNN-slug.patch` and applied in order.
- Every patch starts with a header, which `tools/extract/check-patches.sh`
  validates:

  ```
  # Patch:        040-field-cfg-rpitit-bit-plane-expansion
  # Phase:        pre
  # Target:       field/src/field.rs, baby-bear/tests/pre_patch_040.rs
  # Hunks:        2
  # Class:        cfg-hide
  # Gap:          docs/extractor-issues.md 10 (charon#1266, as for 020 and 030).
  # Cost:         none in a normal build: the change is behind
  #               cfg(hax_backend_lean). In the extracted variant,
  #               `Field::prepare_bit_plane_expansion` is absent.
  # Upstreamable: yes: one `cfg` attribute, inert in a normal build.
  # Drop when:    as for 020.
  # Test:         test p3-baby-bear --test pre_patch_040
  # Mutation:     `prepare_bit_plane_expansion` is gated on the wrong cfg, so a
  #               normal build lacks it.
  ```

  A field continues on lines indented to its value. Prose follows, after a
  bare `#` line: why the change is necessary, and why it is the least-bad
  option. A reviewer should be able to judge a patch from its header alone.
- `Class` says what kind of change the patch is:

  | Phase | Class | The patch |
  |---|---|---|
  | pre | `cfg-hide` | removes items, or trait edges, from the extracted variant, under `cfg(hax_backend_lean)` |
  | pre | `bound` | adds an implied (redundant) bound, or an inert declaration such as a check-cfg name |
  | pre | `equiv-rewrite` | gives the extracted variant an equivalent body in a shape the extractor handles ([below](#equivalent-rewrites)) |
  | post | `restore` | re-adds an item the extractor dropped, with the body it stands for |
  | post | `reshape` | keeps the referent and corrects its signature, monad or arguments |
  | post | `rename` | changes names only |

- `Gap` is the extractor bug or limitation the patch works around, cited as
  `docs/extractor-issues.md <n>` (each cited item must exist), with upstream
  links where reported.
- `Cost` is `none` or the axiom or assumption the patch adds. `STATUS.md` lists
  every patch whose `Cost` is not `none`.
- `Upstreamable` is `yes: <where and how>` or `no: <why>`: whether the change
  itself, or a fix that makes it unnecessary, could go into Plonky3 or the
  extractor, so that the gap closes for everyone. It is not the same as `Gap`.
- A pre patch also has `Test` and `Mutation`
  ([Tests and mutations](#tests-and-mutations)).
- The declared `Hunks` must match the diff, and the ordered set must apply with
  zero fuzz, so drift fails loudly instead of landing somewhere plausible.
- In generated Lean, mark every edit `-- PATCHED` and keep a replaced call as a
  comment beside it. In Rust, mark every edit `PATCHED` in a comment.
- Prefer fixing a hand-written `Assumptions/` file or a stub over patching
  generated code, and prefer a patch over a `sorry`. A generated `sorry` is
  never accepted.

## Tests and mutations

Every pre patch makes its own case that it leaves the normal build as shipped,
and shows that the case could fail.

- **The test.** The patch adds a test that is compiled and run in the normal
  build, and that would not compile, or would fail, if the patch broke what it
  promises: a `cfg-hide` patch's test reaches each hidden item through the
  bounds a caller would use and checks its value against an independent
  computation; a `bound` patch's test may be a lint check. A test goes in a new
  file, `<crate>/tests/pre_patch_NNN.rs`, so that it shifts no line of the
  extracted source (the generated Lean records source positions). It is named
  in `# Test:`, a `;`-separated list of
  - `test <package> <cargo test target args>`, e.g.
    `test p3-baby-bear --test pre_patch_020`: the target builds, at least one
    test runs, and every test passes;
  - `lint <package> <lint>`, e.g. `lint p3-field unexpected_cfgs`:
    `cargo check --all-targets` succeeds without reporting `<lint>` for the
    package.
- **The mutation.** `NNN-slug.mutation.patch`, beside the patch, is a diff that
  applies on top of the whole pre set and breaks the patch's promise, for
  example by dropping a supertrait the normal build must keep, or by gating a
  hidden item on the wrong cfg. `# Mutation:` says what it breaks. A mutation
  file starts with `# Mutation of: NNN-slug` and `# Breaks:` lines.

`tools/extract/check-mutations.py`, in step 2 of `extract.sh`, applies every
pre patch to a scratch copy of `plonky3/`, runs each patch's tests and requires
them to pass, then applies its mutation and requires them to fail. Any failure
counts, and is reported: a compile error in the test target, a compile error in
one of its dependencies, a failing test, or the lint. A mutation that every test
survives fails the run. `--list` prints the declarations and runs nothing.
Results are cached under `.lake/extract/mutation/`.

## Equivalent rewrites

An `equiv-rewrite` patch changes a body, so it carries the most trust, and the
tests above must reach it. A body gated on `cfg(hax_backend_lean)` is never
compiled by upstream's tests, so:

- the rewritten body is a separate item, compiled in both the normal build and
  the extracted variant;
- only the selection, which body the original item uses, is gated on the cfg;
- the patch's test is differential and runs in the normal build: it asserts
  that the original body and the rewritten one agree, on representative and
  edge inputs, or exhaustively or property-based where that is cheap;
- the mutation breaks the rewritten body, and the differential test must then
  fail at run time.

The [stop rules](#pre-patch-or-transcription) apply in full.

## Upstream tests

`tools/extract/test-pre-patches.py`, step 2 of `extract.sh`, runs
`cargo test --workspace --no-fail-fast` on two copies of `plonky3/`, one as
shipped and one with every pre-extraction patch applied, and compares them per
test. It also compares the source of every `#[test]` fn, so a patch cannot pass
by weakening a test. A **divergence** is a test that passes as shipped and fails
or disappears with the patches, a patched tree that does not build its tests,
or an edited test. Each divergence is attributed to the first patch that
introduces it, and the script writes it into that patch's header:

```
# Tested:     test-pre-patches.py: 6715 of 6769 upstream tests pass as
#             shipped, 6714 with the pre-patches; 1 divergence from this patch.
# Divergence: p3_mds[unittests src/lib.rs]::util::tests::some_test
#   observed: passes as shipped; FAILED with the patches: assertion failed
#   class:    TODO
#   was:      TODO
#   now:      TODO
```

`Tested:` and `observed:` belong to the script and are rewritten on every run.
`class`, `was` and `now` belong to the patch author and are kept across runs.
While any entry says `TODO`, the run fails, so a divergence is never accepted
without a person having judged it. `class` is one of:

| Class | Meaning |
| --- | --- |
| `totality` | Panic / `Result` / `Option` channel changed |
| `observable` | A different value on some input |
| `signature` | An upstream test no longer compiles against a changed item |
| `test-edited` | The patch changes or removes an upstream test |
| `harness` | Layout only (line numbers, file contents); no semantic change |

The goal is no divergences at all. A test that exists only with the patches is
a patch's own ([Tests and mutations](#tests-and-mutations)): it is not a
divergence and is not counted in `Tested:`, but the run fails unless it passes.
`--check` writes nothing and fails if a header is out of date. Results are cached under `.lake/extract/pretest/`, keyed
on the content of `plonky3/`, each patch's diff (not its header), the script and
`rustc --version`.

## Authoring and updating

Patches are not regenerated, and `new-patch.sh` never overwrites one.

| Situation | Action |
|-----------|--------|
| New deviation in generated Lean | Edit the file under `crates/<crate>/extraction/<Lib>/Extraction/`, then `tools/extract/new-patch.sh <crate> post NNN-slug` (the number must sort last). Fill in the header. |
| New deviation in Rust | Edit `plonky3/` and add the patch's test file (`git -C plonky3 add -N` it, so that `git diff` shows it), run `tools/extract/new-patch.sh <crate> pre NNN-slug`, revert the edit, and fill in the header. |
| Its mutation | Apply every pre patch to `plonky3/` (`tools/extract/config.py pre-patches`, in order), break what the patch promises, run `tools/extract/new-patch.sh <crate> mutation NNN-slug`, revert `plonky3/`, and run `tools/extract/check-mutations.py`. |
| A patch no longer applies | Edit that `.patch` until `tools/extract/check-patches.sh` is green. |
| A patch is obsolete | Delete it. Shrinking the set is the goal. |
