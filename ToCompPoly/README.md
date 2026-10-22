# `ToCompPoly/`: specifications staged for CompPoly

Every field specification a claim is stated against comes from
[CompPoly](https://github.com/Verified-zkEVM/CompPoly). When a claim needs one that
CompPoly does not have yet (a field, an extension, a table of constants, a fact
about them), it is written here first and upstreamed, so that the trust surface
of the claims stays CompPoly's, not this repository's.

## Rules

- **Written as CompPoly code.** Each file uses CompPoly's header, style and
  namespaces (`BabyBear`, `Polynomial`, `Nat`), and sits at the path it will have
  upstream, under `ToCompPoly/` instead of `CompPoly/`. Upstreaming a file is a
  copy, a change of its `ToCompPoly.` imports to `CompPoly.`, and a deletion here.
- **Imports CompPoly and mathlib only**, never `Plonky3Lean`, Aeneas or the
  extraction. Nothing here knows about Rust.
- **No `sorry`, no `native_decide`, no new axioms.** The `ToCompPoly` library
  builds with warnings as errors, and every claim's axioms are checked by
  `tools/check-claims.py`.
- **Specifications, not glue.** How a Rust value is read (`toField`, `Canonical`,
  the coefficient array in `toExt`) is the model's interpretation and stays in
  `Plonky3Lean.Spec`. What it is read *as* (a field, an extension, a constant)
  belongs here.

## Contents

| File | Upstream destination | What |
|---|---|---|
| `Data/Nat/PowMod.lean` | new file | Square-and-multiply that the kernel evaluates, with its correctness lemma |
| `ToMathlib/Order/OrderOfSq.lean` | new file (mathlib candidate) | A square root of a primitive `2 ^ (k + 1)`-th root of unity is a primitive `2 ^ (k + 2)`-th one |
| `ToMathlib/Polynomial/XPowSubC.lean` | new file (mathlib candidate) | `X ^ n - a` is irreducible over `ZMod q`, from finitely many gcds |
| `Fields/BabyBear.lean` | appended to `CompPoly/Fields/BabyBear.lean` | `generator = 31` and its order; `x ↦ x ^ 1725656503` inverts `x ↦ x ^ 7` |
| `Fields/BabyBear/Extension.lean` | new file | `ofCoeffs`; the extensions `Ext4`, `Ext5`, `Ext8` (`X ^ D - W` irreducible); the two-adicity of `p ^ D - 1`; the two-adic generators of `Ext4` and `Ext8` with their orders and squaring chain |

When a file lands upstream, delete it here, bump the CompPoly `rev` in
`lakefile.toml`, and change the imports that named it.
