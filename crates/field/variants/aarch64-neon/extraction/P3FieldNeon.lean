/-
The Lean model of p3-field's NEON helpers, `uint32x4_mod_add` and
`uint32x4_mod_sub`: hax's extraction for AArch64 (crates/field/crate.toml,
`[[variant]]`), in `P3FieldNeon/Extraction/`, over p3-arch-shims' models of the
intrinsics. The declarations are in the `p3_field` namespace, under the names
the NEON variants of the crates that call them refer to.
-/
module

public import P3FieldNeon.Extraction

@[expose] public section
