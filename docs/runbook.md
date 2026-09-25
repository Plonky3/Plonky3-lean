# Tracking Plonky3

`plonky3/` is a submodule pinned to one Plonky3 commit. Every model, claim and
figure in this repository is about that commit, and `STATUS.md` records it.

The tracking workflow and `xtask` are not written yet. This page is their
specification. Until then, only `.github/workflows/ci.yml` runs: `lake build` on
every pull request.

## Triggers

| Trigger | Runs against | On failure |
|---|---|---|
| Nightly schedule | Plonky3 `main` | Bisect, open or update an issue, keep the pin |
| `workflow_dispatch` | Any ref, including `refs/pull/N/head` | Report in the run summary only |
| Pull request to this repository | The pinned commit | The pull request fails |

Plonky3 itself runs nothing and holds no credentials for this repository.

## Pipeline

1. **Resolve.** Diff every crate's `watch` paths between the pin and the target ref.
   If nothing watched moved, bump the pin and stop. A full run happens weekly
   regardless, to catch toolchain and cache rot.
2. **Extract.** Run `xtask extract` for each affected crate, with the image and
   toolchain pinned in `toolchain.toml`.
3. **Build.** `lake build`, with the mathlib cache.
4. **Check.** `xtask check`:
   - Re-extraction reproduces every committed `extraction/` file byte for byte.
   - The axioms of every claim equal `claims.toml`.
   - No `sorry`, and no warnings beyond the upstream ones `STATUS.md` lists.
   - The set of `opaque` declarations, generated ones included, equals the one
     recorded in `STATUS.md`.
   - Every non-opaque stub declaration has a `[[mirror]]` entry whose hash
     matches the current Rust item.
   - Every `[[oracle]]` table prints the same values from Rust and from Lean.
   - Extracted crates import only the libraries of their Cargo dependencies.
5. **Outcome.**
   - Green, extraction unchanged: a pull request bumping the pin, merged
     automatically.
   - Green, extraction changed: the same pull request, left for review.
   - Red: bisect the first-parent commits in the range that touch watched
     paths, and open or update one issue per affected crate, naming the first
     bad Plonky3 commit. The pin stays at the last green commit. The issue closes
     itself on the next green run.

## By hand

```bash
git submodule update --init
lake exe cache get
lake build
```

Moving the Lean, Hax or CompPoly pins is its own pull request: update
`lean-toolchain`, the `rev`s in `lakefile.toml` and `hax_rev` in
`toolchain.toml` together, then run `lake update` and `lake exe cache get`.
Do not run `lake update` otherwise.
