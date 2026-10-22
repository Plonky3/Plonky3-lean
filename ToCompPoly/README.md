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
| `Fields/BabyBear/Extension.lean` | new file | `ofCoeffs`; the extensions `Ext4`, `Ext5`, `Ext8` (`X ^ D - W` irreducible); the two-adicity of `p ^ D - 1`; the two-adic generators of `Ext4` and `Ext8` with their orders and squaring chain; the multiplicative generators `X + 2` of `Ext4` and `X + 10` of `Ext8` |
| `Fields/KoalaBear/Quintic.lean` | new file | `X ^ 5 + X ^ 2 - 1` is irreducible; `X + 2` generates its quotient's multiplicative group; the Frobenius coefficients `X ^ ((k + 1) p)` |
| `ToMathlib/Polynomial/CoeffList.lean` | new file (mathlib candidate) | Products and powers in `R[X] / (f)` on coefficient lists, which the kernel evaluates; orders of elements from a factorisation |
| `ToMathlib/Polynomial/IrreducibleOfOrder.lean` | new file (mathlib candidate) | A monic `f` over `F_q` is irreducible if `F_q[X] / (f)` has an element of order `q ^ deg f - 1` |
| `Fields/Goldilocks.lean` | appended to `CompPoly/Fields/Goldilocks.lean` | two-adicity `32`; `generator = 7` and its order; a primitive `2 ^ 32`-th root of unity; `x ↦ x ^ 10540996611094048183` inverts `x ↦ x ^ 7` |
| `Fields/KoalaBear.lean` | appended to `CompPoly/Fields/KoalaBear/Basic.lean` | `x ↦ x ^ 1420470955` inverts `x ↦ x ^ 3`; a kernel-checkable `x ^ e ≠ 1` test |
| `Fields/KoalaBear/Extension.lean` | new file | `ofCoeffs`; the extensions `Ext4`, `Ext8` (`X ^ D - 3` irreducible); the two-adicity of `p ^ D - 1` for `D = 4, 5, 8`; the two-adic generators of `Ext4` and `Ext8` with their orders and squaring chain |
| `Fields/Mersenne.lean` | appended to `CompPoly/Fields/Mersenne.lean` | the `Field` instance; `generator = 7` and its order; `x ↦ x ^ 1717986917` inverts `x ↦ x ^ 5`; `-1` and `5` are not squares, `5` is not a cube |
| `Fields/Mersenne/Complex.lean` | new file | `Complex = F[X] / (X ^ 2 + 1)`; Frobenius is conjugation; the two-adic generators of `Complex` with their orders, squaring chain and norms |
| `Fields/Mersenne/Extension.lean` | new file | `X ^ 3 - 5`, `Y ^ 2 - (2 + i)` and `Y ^ 3 - 5i` are irreducible; their `DTH_ROOT`s; `12 + i` generates `Complex`; an element of order `2 ^ 33` in QM31 |
| `Fields/Binary/NatPoly.lean` | appended to `CompPoly/Fields/Binary/Common.lean` | `natPoly n`, the polynomial over `GF(2)` whose coefficients are the bits of `n`; how xor, shifts, splits and bounds act on it |
| `Fields/Binary/Poly64/Basic.lean` | new file | the modulus `X ^ 64 + X ^ 4 + X ^ 3 + X + 1` and its quotient `GF(2 ^ 64)` |
| `Fields/Binary/Poly192/Basic.lean` | new file | the modulus `Y ^ 3 + Y + 1` over `GF(2 ^ 64)` and its quotient `GF(2 ^ 192)` |
| `ToMathlib/Polynomial/Rabin.lean` | new file (mathlib candidate) | Rabin's irreducibility test over `GF(2)` for degree `2 ^ (k + 1)`, also stated in `GF(2)[X] / (P)` |

When a file lands upstream, delete it here, bump the CompPoly `rev` in
`lakefile.toml`, and change the imports that named it.
