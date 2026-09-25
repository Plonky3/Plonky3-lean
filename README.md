# Plonky3-lean

Formal models and machine-checked proofs for
[Plonky3](https://github.com/Plonky3/Plonky3), in Lean 4.

Plonky3's Rust crates are extracted to Lean with
[hax](https://github.com/cryspen/hax). The resulting models are specified
against [CompPoly](https://github.com/Verified-zkEVM/CompPoly) and mathlib. A
nightly job moves the pinned Plonky3 commit along `main` whenever every check
passes. [`docs/runbook.md`](docs/runbook.md) specifies it; it is not running yet.

## What is claimed

Exactly the theorems in `Plonky3Lean.Claims` ([`STATUS.md`](STATUS.md) lists them
with their axioms), about the Plonky3 commit pinned in `plonky3/`, under the
assumptions in [`TRUST.md`](TRUST.md). In particular:

- Only the portable scalar code paths are modelled. The AVX2, AVX-512 and NEON
  backends are not.
- A crate that is stubbed rather than extracted is assumed, not modelled.
- "Plonky3 is formally verified" is not a claim this repository makes.

## Layout

```
plonky3/              submodule: the Plonky3 commit everything here is about
toolchain.toml        extractor: backend, hax revision, Rust toolchain, target
lakefile.toml         one Lake workspace: HaxExt, Plonky3Lean, one library per crate
lean-toolchain  lake-manifest.json

crates/               THE MODEL: one directory per Plonky3 crate, extracted or stubbed
  _template/          starting point for a new crate
HaxExt.lean           gaps in the Hax Lean library, shared by every crate

Plonky3Lean.lean      THE CLAIMS: hand-written, organized by property
Plonky3Lean/
  Claims.lean Claims/ what is asserted              (Plonky3 maintainers)
  Spec.lean   Spec/   what the assertions mean      (Plonky3 maintainers)
  Proofs.lean Proofs/ why they hold
  Lib.lean    Lib/    shared lemmas and tactics

claims.toml           the axioms each claim may depend on
STATUS.md             generated: pin, crates, claims, assumptions, patch costs
TRUST.md              the trust layers shared by every crate
tools/                xtask, oracle, mirror
docs/                 runbook, adding a crate, patches
```

- [`crates/README.md`](crates/README.md) describes the model: the stubbed and
  extracted states, and the rule that every hand-written body is either assumed
  or mirrored from a hashed Rust item.
- [`docs/runbook.md`](docs/runbook.md) describes how the pin follows Plonky3 and
  what CI checks.

## Build

```bash
git clone --recurse-submodules git@github.com:Plonky3/Plonky3-lean.git
cd Plonky3-lean
lake exe cache get     # prebuilt mathlib; without it the first build takes hours
lake build
```

## License

MIT, see [`LICENSE`](LICENSE).
