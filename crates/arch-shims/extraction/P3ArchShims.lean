/-
The Lean model of p3-arch-shims (`arch/`): hax's extraction of the whole crate,
in `P3ArchShims/Extraction/`. Each `x86_64.avx2._mm*` function is the model of
the `core::arch` intrinsic of that name, which the AVX2 variants of the field
crates call (crates/*/variants/x86_64-avx2/).
-/
module

public import P3ArchShims.Extraction

@[expose] public section
