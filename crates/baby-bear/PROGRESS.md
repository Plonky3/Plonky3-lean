# BabyBear: scalar path verification progress

| Part of the path | Status | Against |
|---|---|---|
| Constants: `PRIME`, `MONTY_*`, two-adic tables, generator, root of x⁷ | ✅ claimed | extracted code |
| `new`, `new_array`, `new_2d_array` | ✅ claimed | extracted code |
| `+`, `−`, `×`, `neg` | ✅ claimed | extracted code (#8) |
| `halve`, conversions (`from_int` and `from_canonical_checked` for all 6 widths), `as_canonical_*`, `ONE`/`TWO`/`NEG_ONE`/`GENERATOR` | ✅ claimed, generically for any valid monty-31 prime (#7) | extracted code (#14) |
| Reductions: `monty_reduce`, `large_monty_reduce`, `monty_reduce_u128`, `to_monty_*` | ✅ claimed (#7) | extracted code |
| **Inversion** (`try_inverse`), `mul_2exp_u64`, `div_2exp_u64`, `square`, `exp_u64` | ✅ claimed (#7) | **hand copies**, because the extractor can't model what they call (aeneas issue 9) |
| Extension constants: W, `DTH_ROOT`, two-adicity, generators for degrees 4, 5, 8 | ✅ claimed | CompPoly's `Ext` (#16) |
| `dot_product`, `sum_array`, `Sum`/`Product` | ❌ | they extract, but their large-`N` branches use iterator adapters the toolchain can't handle |
| Extension **arithmetic** (mul, square, inverse, Frobenius) | ❌ | blocked: p3-field (aeneas issue 9), and it needs `dot_product` |
| Exponentiation chain `exp_1725656503` | ❌ opaque | blocked: p3-field |
| `sqrt`, `batch_inverse` | ❌ | p3-field, plus `BigUint` and rayon |
| Poseidon1/2, MDS | ❌ (constants and length assertions only) | iterators; needs a permutation spec |

# SIMD backends

See [SIMD](SIMD.md) for the plan. Status: undone