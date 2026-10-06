# What is trusted

Everything that, if wrong, could make a claim in `Plonky3Lean.Claims` false
without a Lean error. The layers below are shared by every crate. The per-crate
ones, each stub's `opaque` declarations and transcriptions and each crate's
patches, are listed in the generated [`STATUS.md`](STATUS.md).

## 1. The Lean kernel and toolchain

Pinned in `lean-toolchain` to an official `leanprover/lean4` release. Claims are
checked by the kernel. Where a proof uses `native_decide`, the compiled evaluator
is trusted as well, and the claim's axioms in `claims.toml` show
`Lean.ofReduceBool`.

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
faithfully and not to drop items silently. This is the layer least open to
mechanical checking.

Extraction is target-scoped to `thumbv7em-none-eabi`. That target has no SIMD,
so **nothing here describes the AVX2, AVX-512 or NEON code paths**, which are what
production runs on x86-64 and aarch64. The models are of the portable scalar
paths.

## 4. Specification libraries

CompPoly and mathlib (later ArkLib) at the commits locked in
`lake-manifest.json`. Claims compare the models against these specifications,
and a wrong specification yields a wrong claim. `Plonky3Lean.Spec` is in the same
position: CODEOWNERS assigns it to the Plonky3 maintainers.

## 5. The build cache

`lake exe cache get` downloads prebuilt mathlib `.olean` files, and `lake build`
does not re-check them. Re-checking the environment with `lean4checker`, or
building mathlib from source, removes this layer.

## Not trusted

- The claims in `Plonky3Lean.Claims`: they are proved.
- The Rust in `plonky3/`: it is the object being modelled.
- `.lake/`: build output.
