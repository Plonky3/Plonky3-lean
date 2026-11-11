# What is trusted

Everything that, if wrong, could make a claim in `Plonky3Lean.Claims` false
without a Lean error. The layers below are shared by every crate. The per-crate
ones, each crate's `opaque` declarations, its transcriptions (`[[mirror]]`
entries, in stubs and alongside scoped extractions) and its patches, are listed
in the generated [`STATUS.md`](STATUS.md), with the number of claims that rest
on each transcription.

## 1. The Lean kernel and toolchain

Pinned in `lean-toolchain` to an official `leanprover/lean4` release. Claims are
checked by the kernel, except where a proof reaches the compiled evaluator, which
is then trusted too. `native_decide` always reaches it, and `bv_decide` does
whenever it calls the SAT solver: the solver's certificate is checked by a
verified checker, but that check runs compiled, not in the kernel. Each adds an
axiom `<declaration>._native.<tactic>.ax_<n>_<m>`, which states that the compiled
code returned `true` for that one invocation, and `claims.toml` records it like
any other axiom.

No proof here uses `native_decide`. Two use `bv_decide`: one is closed by
`bv_normalize` and adds nothing, and `clear_msb_toNat` calls the solver, which is
why `P3Mersenne31.mersenne_31.Mersenne31.from_int_u32.toField` is the one claim
whose axioms are not just `propext`, `Quot.sound` and `Classical.choice`.

## 2. The Lean libraries the generated code imports

`Aeneas` (`cryspen/aeneas`, `backends/lean`) and `CoreModels`
(`cryspen/hax-lean`), at the `rev`s pinned in `lakefile.toml`. `Aeneas` defines
the Lean meaning of Rust: `RustM`, the integer types, arrays and slices, and the
`⦃ ⦄` specification logic. `CoreModels` defines the models of `core` and `alloc`.
Every model is only as faithful as these definitions. Both are pinned to exactly
what the hax release in `toolchain.toml` resolves, since the generated files and
the libraries that interpret them must come from one aeneas build. `HaxExt.lean`
fills the gaps in them, and is trusted in the same way.

## 3. The extractor

`cargo hax into lean`, which runs [Charon](https://github.com/AeneasVerif/charon)
and [Aeneas](https://github.com/AeneasVerif/aeneas), at the hax release and the
charon and aeneas builds pinned in `toolchain.toml`. Trusted to translate Rust
faithfully and not to drop items silently. It does not always manage the
second: [`docs/extractor-issues.md`](docs/extractor-issues.md) lists the cases
found so far and how each is worked around. This is the layer least open to
mechanical checking.

The charon flags in `toolchain.toml`'s `charon_args` restrict what is extracted
for every crate: `Debug` bodies become `opaque`, and serde is excluded.

Extraction is target-scoped to `thumbv7em-none-eabi`. That target has no SIMD,
so **nothing here describes the AVX2, AVX-512 or NEON code paths**, which are what
production runs on x86-64 and aarch64. The models are of the portable scalar
paths.

## 4. Specification libraries

CompPoly and mathlib (later ArkLib) at the commits locked in
`lake-manifest.json`. Claims compare the models against these specifications,
and a wrong specification yields a wrong claim. Every field specification comes
from CompPoly; one CompPoly lacks is staged in [`ToCompPoly/`](ToCompPoly/README.md),
written as CompPoly code and upstreamed, and is trusted in the same way until
then. `Plonky3Lean.Spec`, which says how a model's values are read as elements
of those specifications, is in the same position. CODEOWNERS assigns both to the
Plonky3 maintainers.

## 5. The build cache

`lake exe cache get` downloads prebuilt mathlib `.olean` files, and `lake build`
does not re-check them. Re-checking the environment with `lean4checker`, or
building mathlib from source, removes this layer.

## Not trusted

- The claims in `Plonky3Lean.Claims`: they are proved.
- The Rust in `plonky3/`: it is the object being modelled.
- `.lake/`: build output.
