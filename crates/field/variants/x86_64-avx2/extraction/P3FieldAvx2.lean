/-
The Lean model of p3-field's AVX2 helpers, `mm256_mod_add` and `mm256_mod_sub`:
hax's extraction for x86_64 with AVX2 (crates/field/crate.toml, `[[variant]]`),
in `P3FieldAvx2/Extraction/`, over p3-arch-shims' models of the intrinsics. The
declarations are in the `p3_field` namespace, under the names the AVX2 variants
of the crates that call them refer to.
-/
module

public import P3FieldAvx2.Extraction

@[expose] public section
