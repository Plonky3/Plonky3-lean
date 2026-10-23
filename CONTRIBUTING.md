# Contributing

## What this repository is for

Machine-checked proofs about Plonky3's Rust, in Lean 4. The Rust is extracted to
Lean with hax (charon, then aeneas) and compared against CompPoly's
specifications.

What is claimed is exactly the theorems in `Plonky3Lean.Claims`, about the
Plonky3 commit pinned in `plonky3/`, under the assumptions in
[`TRUST.md`](TRUST.md). So far only the portable scalar code paths are modelled.
"Plonky3 is formally verified" is not a claim this repository makes.

[`PROGRESS.md`](PROGRESS.md) says how far each crate is from done: its shipped
paths extracted rather than transcribed, and every public function on them
claimed against a CompPoly specification.

## Layout

| Path | What | Written by |
|---|---|---|
| `crates/<crate>/` | the model of one Plonky3 crate: extracted, scoped or stubbed ([`crates/README.md`](crates/README.md)) | hax, plus patches, `Assumptions/` and transcriptions by hand |
| `crates/<crate>/extraction/gaps.toml` | what charon translated but aeneas did not emit | `tools/extract/extract.sh` |
| `Plonky3Lean/Claims/` | what is asserted, one file per crate | hand |
| `Plonky3Lean/Spec/` | how the model's values are read (`toField`, `toExt`, …) | hand |
| `Plonky3Lean/Proofs/`, `Plonky3Lean/Lib/` | why the claims hold; shared lemmas | hand |
| `ToCompPoly/` | specifications staged for CompPoly ([`ToCompPoly/README.md`](ToCompPoly/README.md)) | hand, in CompPoly's style |
| `HaxExt.lean` | definitions `Aeneas` and `CoreModels` lack | hand |
| `claims.toml` | the axioms each claim may depend on | hand |
| `known-warnings.txt` | the only build warnings accepted | hand |
| `STATUS.md` | the inventory: pin, crates, gaps, assumptions, transcriptions, claims | `tools/status.py` |
| `tools/`, `docs/` | the extraction scripts ([`tools/README.md`](tools/README.md)) and their documentation | hand |

## Building

```bash
git clone --recurse-submodules git@github.com:Plonky3/Plonky3-lean.git
cd Plonky3-lean
lake exe cache get
lake build
```

The generated Lean is committed, so proofs and claims need only Lean. To
re-extract (after changing a crate's roots, a patch, or the pin), install the
cargo-hax build `toolchain.toml` pins and run `tools/extract/extract.sh`; see
[`docs/extracting.md`](docs/extracting.md). It is pinned by commit until a hax
release carries the charon it needs.

## Conventions

**Claims.**
- One file per crate, in a namespace named after the crate's Lean library
  (`Plonky3Lean.Claims.P3BabyBear`).
- Each claim's docstring says what it asserts in Rust terms.
- Every claim has a `claims.toml` entry with its exact axioms. No `sorry`, no
  new axioms, and no `native_decide` unless its entry allows `Lean.ofReduceBool`.
- A PR keeps every existing claim's meaning. A restatement (a renamed model
  definition, a CompPoly type in place of a staged one) is listed in the PR
  description with the reason.

**Specifications.**
- Every field specification comes from CompPoly.
- A missing one is written in `ToCompPoly/`, as CompPoly code at its upstream path,
  and upstreamed.
- How a Rust value is read as one of them (Montgomery decoding, coefficient
  arrays) is model glue, and lives in `Plonky3Lean/Spec/`.

**The model.**
- Prefer extraction. A hand transcription (`[[mirror]]` in `crate.toml`) is the
  last resort, for an item the extractor cannot produce.
- A reviewed pre-patch that lets the extractor translate the real code comes
  first. [`docs/patches.md`](docs/patches.md) gives the classes, the stop rules, and
  the test and recorded mutation every pre-patch carries.
- Patch headers state current facts only.
- An `opaque` constant's docstring gives its reason in a sentence starting
  "Assumed".
- A bug or limitation in hax, charon or aeneas goes in
  [`docs/extractor-issues.md`](docs/extractor-issues.md), stating the current
  behaviour, not a history.

**Warnings.** The build prints exactly the warnings in `known-warnings.txt`. Fix
a new warning rather than suppressing it: no `set_option` silencing a linter in
hand-written code. Only a warning that cannot be fixed without a maintainer's
decision goes in the list, with its reason.

## Before opening a PR

```bash
lake build                          # only the warnings in known-warnings.txt
python3 tools/check-claims.py       # every claim, exactly its allowed axioms
python3 tools/status.py --check     # STATUS.md is current (or run it to regenerate)
tools/extract/check-patches.sh      # patch headers, and each pre-patch's recorded mutation file
tools/extract/extract.sh --check    # if extraction, roots or patches changed; runs each
                                    # pre-patch's tests and mutation (check-mutations.py)
```

CI runs `lake build`, `check-claims.py` and `status.py --check`. The extraction
checks need the pinned toolchain and are run locally.

## Pull requests

- Keep each PR to one change. Commits use a type and an optional scope:
  `feat(extract): …`, `fix(tools): …`, `docs(patches): …`, `refactor: …`, `chore: …`.
  PRs are squash-merged under the PR title.
- After review, push fixes as new commits and reply on each thread. Post an update
  comment rather than rewriting the description.
- A PR stacked on another targets `main`, says "stacked on #N", and is rebased as
  soon as its base merges.
- A PR that changes what is extracted or claimed updates `PROGRESS.md`, and the
  crate's own `PROGRESS.md` if it has one, in the same PR.
- [`.github/CODEOWNERS`](.github/CODEOWNERS) assigns `Plonky3Lean/Claims/`,
  `Plonky3Lean/Spec/`, `ToCompPoly/`, `claims.toml`, the pre-patches, `TRUST.md`
  and `toolchain.toml` to the Plonky3 maintainers. A change there needs their review.
