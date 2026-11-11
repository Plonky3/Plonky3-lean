/-
The Lean model of p3-field's AVX-512 helpers, `mm512_mod_add` and
`mm512_mod_sub`: hax's extraction for x86_64 with AVX-512F
(crates/field/crate.toml, `[[variant]]`), in `P3FieldAvx512/Extraction/`, over
p3-arch-shims' models of the intrinsics. The declarations are in the `p3_field`
namespace, under the names the AVX-512 variants of the crates that call them
refer to.
-/
module

public import P3FieldAvx512.Extraction

@[expose] public section
