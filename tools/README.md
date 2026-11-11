# `tools/`

## Now

| Tool | Does |
|---|---|
| `extract/extract.sh` | Regenerates every extracted crate from `plonky3/` with the pinned hax, applies the patches, builds, and with `--check` fails unless the output is byte-identical to what is committed. See [`docs/extracting.md`](../docs/extracting.md). |
| `extract/check-patches.sh` | Checks every patch's header and that each ordered set, and each recorded mutation on top of the pre set, applies with zero fuzz. |
| `extract/new-patch.sh` | Captures a new pre- or post-extraction patch, with a header skeleton, or a pre patch's recorded mutation. |
| `extract/test-pre-patches.py` | Runs Plonky3's tests with and without the pre-extraction patches and records every divergence in the patch headers. |
| `extract/check-mutations.py` | Runs each pre-extraction patch's own tests, and requires them to pass, and to fail under its recorded mutation. |
| `extract/config.py` | Reads `toolchain.toml` and `crates/*/crate.toml` for the scripts above. |
| `extract/patch-necessity.py` | Re-extracts once per patch with that patch left out (`extract.sh --skip-tests --without <crate>/<phase>/<NNN>`), and records the first step that fails without it. How a toolchain bump re-justifies each patch. |
| `extract/gap-report.py` | Writes a crate's `extraction/gaps.toml` from charon's output: its errors, and every item translated but not emitted. Run by `extract.sh`. |
| `check-claims.py` | Checks the axioms of every claim against `claims.toml`. Run by CI. |
| `status.py` | Generates `STATUS.md` from the committed inputs and the Lean build. Run by CI with `--check`. |

The extraction scripts are ported from Plonky3/Plonky3#2154 and are the interim
form of `xtask extract` and `xtask check`; `status.py` is the interim
`xtask status`.

## Planned

A Rust workspace, path-depending on the crates in `../plonky3`:

| Tool | Does |
|---|---|
| `xtask` | The one driver. `extract <crate>`, `check`: every gate in [`docs/runbook.md`](../docs/runbook.md). `status`: regenerate `STATUS.md`. `bump` and `bisect`: move the `plonky3/` pin. |
| `oracle` | Evaluates the `[[oracle]]` tables of every `crate.toml` against the real Rust crates and prints them as canonical values, for comparison with the Lean model. |
| `mirror` | Prints the hash of a Rust item's token stream (`syn`), for the `[[mirror]]` entries of hand-written declarations. |

It uses a stable Rust toolchain. Only `cargo hax`, invoked by `xtask`, uses the
nightly pinned in `toolchain.toml`.
