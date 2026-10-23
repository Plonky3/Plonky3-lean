module

public import Plonky3Lean.Proofs.Hash.Blake3.Spec
public import Plonky3Lean.Proofs.Hash.Blake3.Vectors

@[expose] public section

/-!
# p3-blake3: claims

What this repository asserts about the batched `hash_many`, at the Plonky3 commit pinned in `plonky3/`.

The model is the scoped extraction in `crates/blake3`, on the one-lane portable backend, which takes pre-patch `blake3/010`'s bodies; differential tests equate them with the shipped ones.

`hash_iter`, `hash_iter_slices` and `hash_slice` call the `blake3` crate, which is not extracted.

`m ⦃ v => P v ⦄` states that `m` returns a value `v`, so it does not panic, and that `P v` holds.

The specification is the BLAKE3 paper's, in `Plonky3Lean.Spec.Blake3`, checked against the official test vectors.
-/

open Aeneas Aeneas.Std
open Plonky3Lean.Spec.Blake3

namespace Plonky3Lean.Claims.P3Blake3

/-- With no digests requested, `hash_many` returns `out` unchanged, whatever the input. -/
theorem Blake3.hash_many.empty (self : p3_blake3.Blake3) (input : Slice Std.U8)
    (out : Slice (Std.Array Std.U8 32#usize)) (h : out.val = []) :
    p3_blake3.Blake3.Insts.P3_symmetricHasherCryptographicHasherU8ArrayU832.hash_many self input out = .ok out :=
  Proofs.Blake3.hash_many_empty input out h

/-- With `n > 0` digests requested and an input length that `n` does not divide, `hash_many` panics. -/
theorem Blake3.hash_many.ragged (self : p3_blake3.Blake3) (input : Slice Std.U8)
    (out : Slice (Std.Array Std.U8 32#usize)) (hn : 0 < out.val.length)
    (h : input.val.length % out.val.length ≠ 0) :
    p3_blake3.Blake3.Insts.P3_symmetricHasherCryptographicHasherU8ArrayU832.hash_many self input out =
      .fail .panic :=
  Proofs.Blake3.hash_many_ragged input out hn h

/-- With `n > 0` digests requested and `n · L` input bytes, fewer than `2³² - 1024` of them, digest `i` is the BLAKE3 digest of bytes `[i L, (i + 1) L)`, and nothing panics. -/
theorem Blake3.hash_many.eq_digest (self : p3_blake3.Blake3) (input : Slice Std.U8)
    (out : Slice (Std.Array Std.U8 32#usize)) (L : ℕ) (hn : 0 < out.val.length)
    (hlen : input.val.length = out.val.length * L) (h32 : input.val.length + 1024 < 2 ^ 32)
    (hn32 : out.val.length < 2 ^ 32) :
    p3_blake3.Blake3.Insts.P3_symmetricHasherCryptographicHasherU8ArrayU832.hash_many self input out
      ⦃ r => r.val.map (fun a => a.val.map UScalar.bv) = (List.range out.val.length).map fun i =>
        digest (((input.val.map UScalar.bv).drop (i * L)).take L) ⦄ := by
  obtain ⟨r, e, hr⟩ := Proofs.Blake3.hash_many_spec self input out L hn hlen h32 hn32
  rw [e, WP.spec_ok]
  exact hr

/-- On the 1025-byte test vector, `hash_many` with one digest returns the official BLAKE3 digest. -/
theorem Blake3.hash_many.kat_1025 (self : p3_blake3.Blake3) (input : Slice Std.U8)
    (out : Slice (Std.Array Std.U8 32#usize)) (hi : input.val.map UScalar.bv = Proofs.Blake3.kat 1025)
    (ho : out.val.length = 1) :
    p3_blake3.Blake3.Insts.P3_symmetricHasherCryptographicHasherU8ArrayU832.hash_many self input out
      ⦃ r => r.val.map (fun a => a.val.map UScalar.bv) =
        [Proofs.Blake3.hex "d00278ae47eb27b34faecf67b4fe263f82d5412916c1ffd97c8cb7fb814b8444"] ⦄ := by
  have hl : input.val.length = 1025 := by
    rw [← List.length_map (f := UScalar.bv), hi]; simp [Proofs.Blake3.kat]
  obtain ⟨r, e, hr⟩ := Proofs.Blake3.hash_many_spec self input out 1025 (by omega) (by omega) (by omega)
    (by omega)
  rw [e, WP.spec_ok, hr, ho, hi]
  simp only [List.range_one, List.map_cons, List.map_nil, Nat.zero_mul, List.drop_zero]
  rw [show List.take 1025 (Proofs.Blake3.kat 1025) = Proofs.Blake3.kat 1025 from
    List.take_of_length_le (by simp [Proofs.Blake3.kat]), Proofs.Blake3.digest_1025]

/-- The specification's digest of the empty message is the official one. -/
theorem digest.kat_0 : digest (Proofs.Blake3.kat 0) =
    Proofs.Blake3.hex "af1349b9f5f9a1a6a0404dea36dcc9499bcb25c9adc112b7cc9a93cae41f3262" :=
  Proofs.Blake3.digest_0

/-- The specification's digest of the 1-byte test vector is the official one. -/
theorem digest.kat_1 : digest (Proofs.Blake3.kat 1) =
    Proofs.Blake3.hex "2d3adedff11b61f14c886e35afa036736dcd87a74d27b5c1510225d0f592e213" :=
  Proofs.Blake3.digest_1

/-- The specification's digest of the 65-byte test vector, two blocks, is the official one. -/
theorem digest.kat_65 : digest (Proofs.Blake3.kat 65) =
    Proofs.Blake3.hex "de1e5fa0be70df6d2be8fffd0e99ceaa8eb6e8c93a63f2d8d1c30ecb6b263dee" :=
  Proofs.Blake3.digest_65

/-- The specification's digest of the 1024-byte test vector, one full chunk, is the official one. -/
theorem digest.kat_1024 : digest (Proofs.Blake3.kat 1024) =
    Proofs.Blake3.hex "42214739f095a406f3fc83deb889744ac00df831c10daa55189b5d121c855af7" :=
  Proofs.Blake3.digest_1024

/-- The specification's digest of the 1025-byte test vector, two chunks, is the official one. -/
theorem digest.kat_1025 : digest (Proofs.Blake3.kat 1025) =
    Proofs.Blake3.hex "d00278ae47eb27b34faecf67b4fe263f82d5412916c1ffd97c8cb7fb814b8444" :=
  Proofs.Blake3.digest_1025

/-- The specification's digest of the 2049-byte test vector, three chunks, is the official one. -/
theorem digest.kat_2049 : digest (Proofs.Blake3.kat 2049) =
    Proofs.Blake3.hex "5f4d72f40d7a5f82b15ca2b2e44b1de3c2ef86c426c95c1af0b6879522563030" :=
  Proofs.Blake3.digest_2049

end Plonky3Lean.Claims.P3Blake3
