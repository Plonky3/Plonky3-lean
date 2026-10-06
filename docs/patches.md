# Patches

Two kinds, per crate, kept apart because they cost different amounts of trust.

| | `patches/pre/` | `patches/post/` |
|---|---|---|
| Patches | Rust in `plonky3/` (any crate in the workspace) | the crate's generated Lean (`extraction/<Lib>/Extraction/`) |
| Paths from | `plonky3/` | `crates/<crate>/` (`extraction/P3BabyBear/Extraction/Funs.lean`) |
| Applied | before `cargo hax` runs, every crate's, for every crate's run | after `cargo hax` runs |
| Reverted | yes, unconditionally, on exit | no: the result is committed |
| Trust cost | **changes the artifact under verification** | changes only the Lean encoding of it |
| Checked by | `test-pre-patches.py`, and a `cargo check` of the extracted variant | `lake build` |

- **`patches/pre/`** changes the Rust before hax runs. The model then describes
  a patched Plonky3, not the one that ships, and nothing proved on the Lean side
  can close that gap. Use one only when extraction is impossible otherwise.
  CODEOWNERS assigns these to the Plonky3 maintainers. Two rules keep the cost
  down:
  1. **Gate on `cfg(hax_backend_lean)`.** Extraction sets that cfg for every
     crate (`rustflags` in `toolchain.toml`); normal builds never do. A patch
     that only changes what exists under the cfg leaves the normal build, and
     so every upstream test, exactly as shipped. What remains unconditional must
     be provably inert, such as a redundant (implied) trait bound or the cfg's
     check-cfg declaration.
  2. **Let rustc check the claim.** A patch hides items; it does not rewrite
     bodies. `extract.sh` compiles each extracted crate under the cfg, the
     variant charon sees, so anything still reachable that used a hidden item
     fails to compile.
- **`patches/post/`** changes the Lean that hax generated. The Rust is
  untouched; the patch is a claim about the encoding. A reviewer checks it by
  reading the diff, or by comparing the committed output with the pristine one
  that the last run left in `.lake/extract/pristine/`.

## Rules

- One logical change per file, named `NNN-slug.patch` and applied in order.
- Every patch starts with a header, which `tools/extract/check-patches.sh`
  validates:

  ```
  # Patch:     030-name-anonymous-const-assertions
  # Phase:     post
  # Target:    extraction/P3BabyBear/Extraction/Funs.lean
  # Hunks:     9
  # Cost:      none. Renames only; the bodies are untouched.
  # Upstream:  <the extractor bug or limitation, with a link when reported>
  # Drop when: <the condition under which this patch is no longer needed>
  ```

- `Cost` is `none` or the axiom or assumption the patch adds. `STATUS.md` lists
  every patch whose `Cost` is not `none`.
- The declared `Hunks` must match the diff, and the ordered set must apply with
  zero fuzz, so drift fails loudly instead of landing somewhere plausible.
- In generated Lean, mark every edit `-- PATCHED` and keep a replaced call as a
  comment beside it. In Rust, mark every edit `PATCHED` in a comment.
- Prefer fixing a hand-written `Assumptions/` file or a stub over patching
  generated code, and prefer a patch over a `sorry`. A generated `sorry` is
  never accepted.

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

The goal is no divergences at all. `--check` writes nothing and fails if a
header is out of date. Results are cached under `.lake/extract/pretest/`, keyed
on the content of `plonky3/`, each patch's diff (not its header), the script and
`rustc --version`.

## Authoring and updating

Patches are not regenerated, and `new-patch.sh` never overwrites one.

| Situation | Action |
|-----------|--------|
| New deviation in generated Lean | Edit the file under `crates/<crate>/extraction/<Lib>/Extraction/`, then `tools/extract/new-patch.sh <crate> post NNN-slug` (the number must sort last). Fill in the header. |
| New deviation in Rust | Edit `plonky3/`, run `tools/extract/new-patch.sh <crate> pre NNN-slug`, revert the edit, and fill in the header. |
| A patch no longer applies | Edit that `.patch` until `tools/extract/check-patches.sh` is green. |
| A patch is obsolete | Delete it. Shrinking the set is the goal. |
