# Progress

How close each crate is to verified. A crate is done when the code paths it
ships are extracted (not transcribed) and every public function on them is
claimed against a CompPoly specification. Only the portable scalar paths are in
scope so far.

Counts (claims, opaque constants, transcriptions, dropped items) are in the
generated [`STATUS.md`](STATUS.md). This table is hand-written: a PR that changes
what is extracted or claimed updates its row, and the crate's own `PROGRESS.md`
if it has one.

| Crate | Extraction | Verified | Not yet | Detail |
|---|---|---|---|---|
| `baby-bear` | extracted | Constants, constructors, `+ - × neg halve`, conversions, inversion, extension constants (degrees 4, 5, 8) | `dot_product`/`sum`, extension arithmetic, exponentiation, `sqrt`, Poseidon | [crates/baby-bear/PROGRESS.md](crates/baby-bear/PROGRESS.md) |
| `monty-31` | scoped | Generic over every valid prime: reductions, `+ - × neg halve`, conversions, inversion (`p ≥ 2^30`) | `dot_product`/`sum_array`/`Sum`; inversion and the power-of-two methods rest on transcriptions | |
| `koala-bear` | extracted | Constants, the generic monty-31 arithmetic at its prime, extension constants, quintic irreducibility, Frobenius coefficients | Exponentiation, conversions, extension arithmetic, Poseidon | |
| `goldilocks` | scoped | Scalar arithmetic for every stored `u64`: reductions, `+ - ×`, inversion, sums, dot products, conversions, generators | Exponentiation, `try_sqrt`, extension fields, Poseidon; arithmetic rests partly on transcriptions | |
| `mersenne-31` | scoped | Scalar arithmetic for every value below `2^31`: `+ - ×`, inversion, sums, dot products, conversions; complex field and extension constants | Exponentiation, `try_sqrt`, `sum_array`, generic extension arithmetic, Poseidon | |
| `binary-field` | scoped | The tower at every level, `GF(2^64)`, GHASH, `GF(2^192)`: arithmetic, inversion, square roots, Frobenius, the basis change, the carry-less paths, the Cantor basis | Trait methods the extraction cannot reach, the generic `Sum` impls, AES and bit-plane code, the hardware kernels | |
| `util` | scoped | `gcd_inversion_prime_field_32` | The rest of the crate | |
| `sha256`, `sha2` | scoped | `Sha256Compress::compress` and `compress256` against FIPS 180-4 | sha2's default (unrolled) backend | |
| `blake2s` | scoped | How `hash_many` splits its input and places digests | `Blake2s256::hash` itself, which is opaque | |
| `blake3` | scoped | Batched `hash_many` against the BLAKE3 paper | `hash_iter`, `hash_iter_slices`, `hash_slice` | |
| `blake3-crate` | stub | Nothing | The upstream `blake3` crate | |
| `field` | stub | Nothing; its traits are hand-written | Extraction is blocked by extractor issue 9 | |
| `mds` | scoped (only what `baby-bear` refers to) | Nothing | The MDS layers | |
| `poseidon1`, `poseidon2` | stub | Round-constant length assertions (in `baby-bear`) | The permutations | |

**Out of scope so far:** the SIMD backends (AVX2, AVX-512, NEON) of every field,
see [crates/baby-bear/SIMD.md](crates/baby-bear/SIMD.md); the DFTs, matrices,
commitments and the STARK prover.
