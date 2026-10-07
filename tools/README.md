# `tools/`

## Now

| Tool | Does |
|---|---|
| `extract/extract.sh` | Regenerates every extracted crate from `plonky3/` with the pinned hax, applies the patches, builds, and with `--check` fails unless the output is byte-identical to what is committed. See [`docs/extracting.md`](../docs/extracting.md). |
| `extract/check-patches.sh` | Checks every patch's header and that each ordered set applies with zero fuzz. |
| `extract/new-patch.sh` | Captures a new pre- or post-extraction patch, with a header skeleton. |
| `extract/test-pre-patches.py` | Runs Plonky3's tests with and without the pre-extraction patches and records every divergence in the patch headers. |
| `extract/config.py` | Reads `toolchain.toml` and `crates/*/crate.toml` for the scripts above. |
| `check-claims.py` | Checks the axioms of every claim against `claims.toml`. Run by CI. |

The extraction scripts are ported from Plonky3/Plonky3#2154 and are the interim
form of `xtask extract` and `xtask check`.

## Planned

A Rust workspace, path-depending on the crates in `../plonky3`:

| Tool | Does |
|---|---|
| `xtask` | The one driver. `extract <crate>`, `check`: every gate in [`docs/runbook.md`](../docs/runbook.md). `status`: regenerate `STATUS.md`. `bump` and `bisect`: move the `plonky3/` pin. |
| `oracle` | Evaluates the `[[oracle]]` tables of every `crate.toml` against the real Rust crates and prints them as canonical values, for comparison with the Lean model. |
| `mirror` | Prints the hash of a Rust item's token stream (`syn`), for the `[[mirror]]` entries of hand-written declarations. |

It uses a stable Rust toolchain. Only `cargo hax`, invoked by `xtask`, uses the
nightly pinned in `toolchain.toml`.
