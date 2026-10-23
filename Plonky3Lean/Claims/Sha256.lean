module

public import Plonky3Lean.Proofs.Hash.Sha256.Vectors

@[expose] public section

/-!
# p3-sha256 and sha2: claims

What this repository asserts about `Sha256Compress::compress` and sha2's `compress256`, at the Plonky3 commit pinned in `plonky3/`.

The models are the scoped extractions in `crates/sha256` and `crates/sha2`.

The p3-sha256 model takes pre-patch `sha256/010`'s body, which a differential test equates with the shipped one.

The sha2 model is its compact portable backend, selected by sha2's own cfg; a default build compiles the unrolled backend (docs/extractor-issues.md 15).

`m ⦃ v => P v ⦄` states that `m` returns a value `v`, so it does not panic, and that `P v` holds.

The specification is FIPS 180-4's, in `Plonky3Lean.Spec.Sha256`, checked against the standard's examples.
-/

open Aeneas Aeneas.Std
open Plonky3Lean.Spec.Sha256

namespace Plonky3Lean.Claims.P3Sha256

/-- `Sha256Compress::compress` never panics, and returns FIPS 180-4's compression of the two halves, in order, from the initial hash value, as big-endian bytes. -/
theorem Sha256Compress.compress.eq_fips (self : p3_sha256.Sha256Compress)
    (input : Std.Array (Std.Array Std.U8 32#usize) 2#usize) :
    p3_sha256.Sha256Compress.Insts.P3_symmetricCompressionPseudoCompressionFunctionArrayU8322.compress
      self input ⦃ out => out.val.map UScalar.bv = bytesOfWords (compress H0
        (wordsOfBytes (((input.val[0]!).val ++ (input.val[1]!).val).map UScalar.bv))) ⦄ :=
  Proofs.Sha256.compress_spec self input

/-- On the two halves of `"abc"` padded, `Sha256Compress::compress` returns the SHA-256 digest of `"abc"` from FIPS 180-4's appendix. -/
theorem Sha256Compress.compress.abc (self : p3_sha256.Sha256Compress)
    (input : Std.Array (Std.Array Std.U8 32#usize) 2#usize)
    (h : (((input.val[0]!).val ++ (input.val[1]!).val).map UScalar.bv) =
      pad (Proofs.Sha256.ascii "abc")) :
    p3_sha256.Sha256Compress.Insts.P3_symmetricCompressionPseudoCompressionFunctionArrayU8322.compress
      self input ⦃ out => out.val.map UScalar.bv =
        Proofs.Sha256.hex "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad" ⦄ := by
  have := Proofs.Sha256.compress_spec self input
  rw [h, Proofs.Sha256.compress_pad_abc] at this
  exact this

/-- sha2's `compress256` never panics, and compresses each block in turn as FIPS 180-4 does, from any hash value. -/
theorem compress256.eq_fips (state : Std.Array Std.U32 8#usize)
    (blocks : Slice (Std.Array Std.U8 64#usize)) :
    sha2.sha256.compress256 state blocks ⦃ r => r.val.map UScalar.bv =
      blocks.val.foldl (fun H b => compress H (wordsOfBytes (b.val.map UScalar.bv)))
        (state.val.map UScalar.bv) ⦄ :=
  Proofs.Sha256.compress256_spec state blocks

/-- The specification's digest of the empty message is FIPS 180-4's. -/
theorem digest.empty : digest [] =
    Proofs.Sha256.hex "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855" :=
  Proofs.Sha256.digest_empty

/-- The specification's digest of `"abc"` (one block) is FIPS 180-4's. -/
theorem digest.abc : digest (Proofs.Sha256.ascii "abc") =
    Proofs.Sha256.hex "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad" :=
  Proofs.Sha256.digest_abc

/-- The specification's digest of FIPS 180-4's 448-bit message (two blocks) is the standard's. -/
theorem digest.two_blocks :
    digest (Proofs.Sha256.ascii "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq") =
      Proofs.Sha256.hex "248d6a61d20638b8e5c026930c3e6039a33ce45964ff2167f6ecedd419db06c1" :=
  Proofs.Sha256.digest_448

end Plonky3Lean.Claims.P3Sha256
