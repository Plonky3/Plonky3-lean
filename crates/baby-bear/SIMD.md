# BabyBear: verifying the SIMD backends

BabyBear has three optimised backends in p3-monty-31, each selected by the build target: AVX2 and AVX-512 on x86-64 (`x86_64_avx2/`, `x86_64_avx512/`), and NEON on AArch64 (`aarch64_neon/`). Each packs 8 or 16 field elements into one vector register and operates on all lanes at once. The claims so far cover only the portable scalar code ([PROGRESS](PROGRESS.md)).

**Goal, per backend and per packed operation:** for packed inputs whose lanes are canonical, the operation succeeds, its lanes are canonical, and lane `i` of the result is the scalar `MontyField31` operation on lane `i` of the inputs. Composed with the existing scalar claims, this makes each packed operation the lane-wise field operation in `ZMod p`. No field arithmetic has to be re-proved per backend.

## What the code looks like

Each backend is a thin layer of Rust over **intrinsics**: functions in `core::arch` (e.g. `_mm256_mul_epu32`, `vqdmulhq_s32`), each of which compiles to one CPU vector instruction.

| Backend | Distinct intrinsics | `asm!` blocks |
|---|---:|---:|
| AVX2 | 25 | 0 |
| AVX-512 | 45 | 4 (`confuse_compiler`, masked `vmovshdup`) |
| NEON | 35 | 1 (`confuse_compiler`) |

Our extraction spike (charon `nightly-2026.10.17`, aeneas `build-41977a5`) shows the following. The arithmetic helpers extract. Every intrinsic comes through as an undefined `core.core_arch.*` name with its signature, and so do the vector types. aeneas rejects `asm!`. Nothing in Aeneas or CoreModels gives the intrinsics a meaning yet.

## The two strategies

### 1. Intrinsics (recommended)

Under the extraction cfg, redirect every `core::arch` call to a **shim**: a plain Rust function over lane arrays (`[u32; 8]`, …) whose body transcribes the vendor's pseudocode (Intel's *Operation* section, Arm's ASL). The shims extract like any other Rust, so we prove the packed operations about real extracted code, against shims we trust.

- **Precedent:** SymCrypt on Aeneas uses exactly this toolchain and method, with 122 shims, 23 of them AVX2 and 26 NEON; it has no AVX-512 shims ([arXiv 2609.15648](https://arxiv.org/pdf/2609.15648), [blog](https://www.microsoft.com/en-us/research/blog/verifying-rust-cryptography-in-symcrypt-from-standards-to-code/)). Their shims aren't upstreamed yet, so reuse is uncertain.
- **Trusted:** the shims (one per intrinsic), the redirect, and rustc/LLVM's lowering of each intrinsic to its instruction.
- **Validated by:**
  - reviewing each shim against the vendor pseudocode;
  - **differential testing** each shim against the real intrinsic on hardware, exhaustively over small inputs such as every 8-bit immediate, and randomly with edge cases elsewhere.

  This step is not optional: hand-written SIMD semantics routinely have edge-case bugs that such testing catches ([Minotaur](https://arxiv.org/pdf/2306.00229) found 14 in 165 x86 intrinsics, and Cryspen found a bug in Rust core's own `_mm256_bsrli_epi128` ([post](https://cryspen.com/post/specify-rust-simd/))).
- **Fits what we have:** the redirect is a cfg-only pre-patch. Each shim's differential test is its normal-build test, and a mutated shim must fail it, so it falls under the existing [patch rules](../../docs/patches.md).

### 2. Binary-level verification

The alternative is to prove that the compiled machine code meets the spec. That removes the compiler from the trusted base, at the cost of trusting an ISA model.

- **[machine-checked](https://github.com/Verified-zkEVM/machine-checked)** (Lean 4): **not usable for these backends yet.** Only RISC-V has load and lift layers. The x86-64 model explicitly excludes SIMD. The AArch64 model is trusted, not validated. The proof layers above the model aren't started. The repository is very new, so re-check before relying on it.
- **[LNSym](https://github.com/leanprover/LNSym)** (Lean 4, AArch64): has Advanced SIMD semantics, checked against real execution by co-simulation. It's **the only credible binary-level option, and only for NEON.** We haven't checked whether it covers the exact instructions monty-31 uses (e.g. `SQDMULH`, `UMULL`, `UZP`).
- **s2n-bignum** shows this approach is mature for hand-written arithmetic, but in HOL Light, so it doesn't carry over.
- **x86:** no Lean semantics for AVX2 or AVX-512 exists.

## Plan

| Stage | Work | Proves | Adds to trust |
|---|---|---|---|
| **0. Plumbing** | The cfg redirect from `core::arch` to a `shims` module. Under the cfg, `confuse_compiler` (an optimisation barrier) becomes the identity, and `vmovshdup` becomes a shim. Extract each backend once per target (`--targets` with `+avx2`, `+avx512f`, or aarch64). | All three backends extract | the redirect, two `asm` stand-ins |
| **1. AVX2** | 25 shims, each with a differential test (on an x86 CI runner) and a recorded mutation | Each shim agrees with hardware on its tests | 25 reviewed shims |
| **2. AVX2 claims** | `add`, `sub`, `neg`, `mul` and `halve` lane-wise equal to the scalar operation, plus `from_vector`'s "lanes canonical" safety precondition holding at every call | The packed operation is the lane-wise field operation | none |
| **3. NEON** | 35 shims (the signed `vqdmulhq_s32` Montgomery trick is the subtle one), then the same claims. Optionally cross-check the shims against LNSym, or a Sail model generated from Arm's ASL. | as for AVX2 | 35 shims, less with a mechanical cross-check |
| **4. AVX-512** | 45 shims, including masked operations and `__mmask16`, all new work. Needs a runner that guarantees AVX-512; GitHub's x86 runners don't. | as for AVX2 | 45 shims |
| **5. Beyond `+ − ×`** | packed `dot_product`, `exp_const`, interleaving, then the packed Poseidon2 layers | | |
| **6. Optional** | binary-level checks of the NEON kernels with LNSym, using stages 3–4's claims as the spec. Revisit machine-checked once it supports x86 SIMD. | that the compiled code is correct | ISA model instead of compiler |

NEON comes before AVX-512 because its hardware is widely available for testing (Apple silicon, GitHub's arm64 runners), and its shims overlap SymCrypt's.

## Open questions

1. **Shim reuse:** can SymCrypt's AVX2 and NEON shims be reused (licence, upstreaming into Aeneas), or Cryspen's `core-models`? It's unconfirmed that either extracts through our charon and aeneas.
2. **CI hardware:** which runners can we use? We need an x86 runner with guaranteed AVX-512 and an aarch64 runner.
3. **Your colleague's tooling:** does it bind intrinsics in Rust (as above) or directly in Lean? Either fits stage 1, so it may save the shim-writing work.
4. **Mechanical cross-checks:** do LNSym or Sail-ARM cover monty-31's exact NEON instructions?
