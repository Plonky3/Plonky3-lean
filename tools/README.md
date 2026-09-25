# `tools/`

A Rust workspace, path-depending on the crates in `../plonky3`. Planned:

| Tool | Does |
|---|---|
| `xtask` | The one driver. `extract <crate>`: apply `patches/pre/`, run `cargo hax`, copy the output into `crates/<crate>/extraction/`, reset `plonky3/`, apply `patches/post/`. `check`: every gate in [`docs/runbook.md`](../docs/runbook.md). `status`: regenerate `STATUS.md`. `bump` and `bisect`: move the `plonky3/` pin. |
| `oracle` | Evaluates the `[[oracle]]` tables of every `crate.toml` against the real Rust crates and prints them as canonical values, for comparison with the Lean model. |
| `mirror` | Prints the hash of a Rust item's token stream (`syn`), for the `[[mirror]]` entries of stub crates. |

It uses a stable Rust toolchain. Only `cargo hax`, invoked by `xtask`, uses the
nightly pinned in `toolchain.toml`.
