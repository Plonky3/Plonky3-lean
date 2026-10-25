# What is trusted

Everything that, if wrong, could make a claim in `Plonky3Lean.Claims` false
without a Lean error. The layers below are shared by every crate. The per-crate
ones, each crate's `opaque` declarations, its transcriptions (`[[mirror]]`
entries, in stubs and alongside scoped extractions) and its patches, are listed
in the generated [`STATUS.md`](STATUS.md), with the number of claims that rest
on each transcription.

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
faithfully and not to drop items silently. It does not always manage the
second: [`docs/extractor-issues.md`](docs/extractor-issues.md) lists the cases
found so far and how each is worked around. This is the layer least open to
mechanical checking.

The charon flags in `toolchain.toml`'s `charon_args` restrict what is extracted
for every crate: `Debug` bodies become `opaque`, and serde is excluded.

Extraction is target-scoped to `thumbv7em-none-eabi`. That target has no SIMD,
so the models are of the portable scalar paths. The exceptions are AVX2, NEON
and AVX-512: the `x86_64-avx2`, `aarch64-neon` and `x86_64-avx512` variants of
p3-field, p3-monty-31 and p3-baby-bear are extracted for x86_64 and AArch64
against models of the `core::arch` intrinsics (`arch/`), which are trusted. Of
that code, only BabyBear's packed `Add`, `Sub`, `Mul`, `Neg` and `halve_avx2` /
`halve_neon` / `halve_avx512` are claimed
(`Plonky3Lean/Claims/BabyBear/Avx2.lean`, `Neon.lean` and `Avx512.lean`).
Nothing here describes the rest of these code paths.

The AVX2 and NEON models are reviewed against Intel's and Arm's pseudocode and
checked against the hardware by `arch/tests/`. **The AVX-512 models
(`arch/src/x86_64/avx512.rs`) are reviewed against Intel's pseudocode but not
yet tested against the hardware.** No machine or CI runner available to this
project guarantees AVX-512, so `arch/tests/avx512.rs` and its mutations
(`arch/check-mutations.sh`) only run where the CPU has it, and are otherwise
skipped. Run under Miri instead, the same tests compare each model with
`core::arch`'s own Rust implementation of the intrinsic, which is a second model
rather than the hardware; they agree, and each recorded mutation but those of
`vpermi2d` and `vpermi2q`, which Miri does not implement, is caught there. Until
the tests run on an AVX-512 CPU, a transcription error in an AVX-512 model can
make an AVX-512 claim false.

These variants also rest on stand-ins for the `asm!` blocks the extractor
rejects (docs/extractor-issues.md 213):

- **`confuse_compiler`** (NEON, pre-patch `monty-31/030`; AVX-512's
  `confuse_compiler` and `confuse_compiler_256`, `monty-31/040`): an
  optimisation barrier written as an empty `asm!` block. Under the extraction
  cfg it is the identity. That is its value, since the block's template is a
  comment and the code after it tells the compiler `y == x`, but the stand-in is
  trusted: the models say nothing about the code generation the barrier is there
  to affect.
- **The masked `vmovshdup`** (AVX-512's `mask_movehdup_epi32` and
  `mask_movehdup_epi32_256`, `monty-31/040`): the single instruction
  `vmovshdup dst{k}, a` with merge masking into `src`, written as `asm!` so that
  LLVM keeps that instruction. Under the extraction cfg it is
  `_mm512_mask_movehdup_ps(src, k, a)` (or the 256-bit form) on the vectors
  cast to floats and back, the intrinsic for that instruction. The stand-in is
  trusted to have the block's value: `mul` reaches it, so the AVX-512 `Mul`
  claims rest on it, and on that intrinsic's model.

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
