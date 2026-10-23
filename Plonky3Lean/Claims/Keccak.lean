module

public import Plonky3Lean.Proofs.Hash.Keccak.Vectors
public import Plonky3Lean.Proofs.Hash.Keccak.Digest
public import Plonky3Lean.Proofs.Hash.Keccak.Symmetric

@[expose] public section

/-!
# p3-keccak and tiny-keccak: claims

# Overview

These claims hold at the Plonky3 commit pinned in `plonky3/`.

The permutation is tiny-keccak's `keccakf`.

Its tables are extracted, and its body is a transcription with a mirror entry (crates/tiny-keccak).

The p3-keccak model is the scoped extraction in `crates/keccak`, on the one-lane portable backend.

Its batched hash and one-lane permutation take the bodies of pre-patch `keccak/020`, which a differential test equates with the shipped ones.

The specification is FIPS 202, in `Plonky3Lean.Spec.Keccak`, written bit by bit from the standard.

A state array `A[x, y, z]` is read from 25 words with lane `(x, y)` in word `x + 5 y` and bit `z` of the lane at bit `z` of the word.

# What the claims find

- The permutation is Keccak-f[1600] on every state, and never panics.
- The tables of pi, rho and iota are those Algorithm 2 and Algorithm 5 compute.
- The byte permutation reads and writes lanes little-endian, which is FIPS 202's byte order (B.1).
- `Keccak256Hash::hash_many` is Keccak-256 of the SHA-3 submission (first padding byte `0x01`), and `Sha3_256Hash::hash_many` is SHA3-256 (`0x06`), on every message.
- No digests requested returns at once, and an input the digest count does not divide panics.
-/

open Aeneas Aeneas.Std CoreModels
open Plonky3Lean.Spec.Keccak
open Plonky3Lean.Proofs.Keccak (stateOfWords stateOfWords_eq)

namespace Plonky3Lean.Claims.P3Keccak

/-! ## The permutation -/

/-- tiny-keccak's `keccakf` never panics, and computes Keccak-f[1600] of FIPS 202 on every state. -/
theorem tiny_keccak.keccakf.eq_fips (a : Std.Array Std.U64 25#usize) :
    ∃ b, _root_.tiny_keccak.keccakf.keccakf a = .ok b ∧ stateOfWords b.val = keccakP 24 (stateOfWords a.val) := by
  obtain ⟨b, hb, h⟩ := Proofs.Keccak.keccakf_spec a
  exact ⟨b, hb, by rw [stateOfWords_eq, stateOfWords_eq, h]⟩

/-- The order of pi is the walk `(x, y) <- (y, 2 x + 3 y mod 5)` of Algorithm 2 from `(1, 0)`: entry `t` is lane `t + 1` of the walk. -/
theorem tiny_keccak.PI.eq_walk : _root_.tiny_keccak.PI.val.map (·.val) =
    (List.range 24).map fun t => let p := rhoStep^[t + 1] (1, 0); p.1.val + 5 * p.2.val :=
  Proofs.Keccak.PI_eq_walk

/-- The rotations of rho are `(t + 1) (t + 2) / 2 mod 64` for `t = 0, ..., 23`. -/
theorem tiny_keccak.RHO.eq_triangular :
    _root_.tiny_keccak.RHO.val.map (·.val) = (List.range 24).map fun t => (t + 1) * (t + 2) / 2 % 64 :=
  Proofs.Keccak.RHO_eq_triangular

/-- Round constant `i` has bit `z` equal to `RC[z]` of Algorithm 6, computed with the LFSR of Algorithm 5. -/
theorem tiny_keccak.keccakf.RC.eq_lfsr (i : ℕ) (hi : i < 24) (z : Fin 64) :
    (_root_.tiny_keccak.keccakf.RC.val.getD i 0#u64).bv.getLsbD z.val = roundConstant i z := by
  have h := Proofs.Keccak.RC_get i hi
  rw [getElem!_pos _ _ (by simpa using hi)] at h
  rw [List.getD_eq_getElem _ _ (by simpa using hi), h, Proofs.Keccak.getLsbD_rcWord]

/-! ## Known answers -/

/-- tiny-keccak's `keccakf` maps the all-zero state to the first output of the Keccak team's `KeccakF-1600-IntermediateValues.txt`. -/
theorem tiny_keccak.keccakf.zero :
    _root_.tiny_keccak.keccakf.keccakf (Std.Array.from (List.replicate 25 0#u64) (by simp)) =
      .ok (Std.Array.from Proofs.Keccak.zeroOnce (by simp [Proofs.Keccak.zeroOnce])) :=
  Proofs.Keccak.keccakf_zero

/-- FIPS 202's Keccak-f[1600] maps the all-zero state to the same output. -/
theorem keccakP.zero : keccakP 24 (fun _ _ _ => false) = stateOfWords Proofs.Keccak.zeroOnce := by
  rw [Proofs.Keccak.keccakP_zero, stateOfWords_eq]

/-- The specification's Keccak-256 of the empty string is the published digest. -/
theorem keccak256.empty :
    keccak256 [] = Proofs.Keccak.hex "c5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470" :=
  Proofs.Keccak.keccak256_empty

/-- The specification's Keccak-256 of `"abc"` is the published digest. -/
theorem keccak256.abc : keccak256 (Proofs.Keccak.ascii "abc") =
    Proofs.Keccak.hex "4e03657aea45a94fc7d47ba826c8d667c0d1e6e33a64a036ec44f58fa12d6c45" :=
  Proofs.Keccak.keccak256_abc

/-- The specification's SHA3-256 of the empty string is FIPS 202's example digest. -/
theorem sha3_256.empty :
    sha3_256 [] = Proofs.Keccak.hex "a7ffc6f8bf1ed76651c14756a061d662f580ff4de43b49fa82d80a4b80f8434a" :=
  Proofs.Keccak.sha3_256_empty

/-- The specification's SHA3-256 of `"abc"` is FIPS 202's example digest. -/
theorem sha3_256.abc : sha3_256 (Proofs.Keccak.ascii "abc") =
    Proofs.Keccak.hex "3a985da74fe225b2045c172d6bd390bd855f086e3e9d525b46bfe24511431532" :=
  Proofs.Keccak.sha3_256_abc

/-! ## `KeccakF` -/

/-- `KeccakF` on `[u64; 25]`, through `permute`, is tiny-keccak's `keccakf`. -/
theorem KeccakF.permute_u64.eq (s : Std.Array Std.U64 25#usize) :
    p3_keccak.hax_roots.permute_u64 s = _root_.tiny_keccak.keccakf.keccakf s :=
  Proofs.Keccak.permute_u64_eq s

/-- `KeccakF` on `[u64; 25]`, through `permute_mut`, is tiny-keccak's `keccakf`. -/
theorem KeccakF.permute_mut_u64.eq (s : Std.Array Std.U64 25#usize) :
    p3_keccak.hax_roots.permute_mut_u64 s = _root_.tiny_keccak.keccakf.keccakf s :=
  Proofs.Keccak.permute_mut_u64_eq s

/-- `KeccakF` on `[u8; 200]` never panics, and is Keccak-f[1600] on the bit string of the bytes, read back as bytes (FIPS 202, B.1). -/
theorem KeccakF.permute_u8.eq_fips (b : Std.Array Std.U8 200#usize) :
    ∃ out, p3_keccak.hax_roots.permute_u8 b = .ok out ∧
      out.val.map UScalar.bv = bytesOfBits (keccakF (bitsOfBytes (b.val.map UScalar.bv))) :=
  Proofs.Keccak.permute_u8_spec b

/-- `permute_mut` on `[u8; 200]` returns the same bytes. -/
theorem KeccakF.permute_mut_u8.eq_fips (b : Std.Array Std.U8 200#usize) :
    ∃ out, p3_keccak.hax_roots.permute_mut_u8 b = .ok out ∧
      out.val.map UScalar.bv = bytesOfBits (keccakF (bitsOfBytes (b.val.map UScalar.bv))) :=
  Proofs.Keccak.permute_mut_u8_spec b

/-- The one-lane packed permutation copies the 25 words out, permutes them with tiny-keccak, and copies them back. -/
theorem KeccakF.permute_mut_packed.eq (st : Std.Array (Std.Array Std.U64 1#usize) 25#usize) :
    p3_keccak.hax_roots.permute_mut_packed st =
      .ok (Proofs.Keccak.pack (_root_.tiny_keccak.keccakf.rounds (Proofs.Keccak.unpack st))) := by
  rw [p3_keccak.hax_roots.permute_mut_packed]
  exact Proofs.Keccak.permute_packed_eq st

/-- As a `CryptographicPermutation<[u64; 25]>`, `KeccakF` computes tiny-keccak's 24 rounds in `permute` and `permute_mut`, so the sponge claims of p3-symmetric apply to it. -/
theorem KeccakF.perm_computes :
    Proofs.Symmetric.PermComputes Proofs.Keccak.keccakPerm () _root_.tiny_keccak.keccakf.rounds :=
  Proofs.Keccak.keccakPerm_computes

/-! ## The batched hashes -/

/-- With no digests requested, `Keccak256Hash::hash_many` returns `out` unchanged. -/
theorem Keccak256Hash.hash_many.empty (input : Slice Std.U8) (out : Slice (Std.Array Std.U8 32#usize))
    (h : out.val = []) : p3_keccak.hax_roots.keccak256_hash_many input out = .ok out :=
  Proofs.Keccak.hash_many_empty _ input out h

/-- `Keccak256Hash::hash_many` panics when the digest count does not divide the input length. -/
theorem Keccak256Hash.hash_many.ragged (input : Slice Std.U8) (out : Slice (Std.Array Std.U8 32#usize))
    (hn : 0 < out.val.length) (h : input.val.length % out.val.length ≠ 0) :
    p3_keccak.hax_roots.keccak256_hash_many input out = .fail .panic :=
  Proofs.Keccak.hash_many_ragged _ input out hn h

/-- With `n > 0` digests and `n len` input bytes, `Keccak256Hash::hash_many` returns `n` digests, digest `j` being Keccak-256 of bytes `j len` to `(j + 1) len - 1`. -/
theorem Keccak256Hash.hash_many.eq_keccak256 (input : Slice Std.U8) (out : Slice (Std.Array Std.U8 32#usize))
    (len : ℕ) (hn : 0 < out.val.length) (hlen : input.val.length = out.val.length * len) :
    ∃ r, p3_keccak.hax_roots.keccak256_hash_many input out = .ok r ∧ r.val.length = out.val.length ∧
      ∀ j (hj : j < r.val.length), (r.val[j]).val.map UScalar.bv =
        keccak256 (((input.val.map UScalar.bv).drop (j * len)).take len) := by
  obtain ⟨r, hr, hl, hd⟩ := Proofs.Keccak.hash_many_digests 1#u8 input out len hn hlen
  exact ⟨r, hr, hl, fun j hj => by rw [hd j hj, Proofs.Keccak.keccak256_eq]; rfl⟩

/-- With no digests requested, `Sha3_256Hash::hash_many` returns `out` unchanged. -/
theorem Sha3_256Hash.hash_many.empty (input : Slice Std.U8) (out : Slice (Std.Array Std.U8 32#usize))
    (h : out.val = []) : p3_keccak.hax_roots.sha3_256_hash_many input out = .ok out :=
  Proofs.Keccak.hash_many_empty _ input out h

/-- `Sha3_256Hash::hash_many` panics when the digest count does not divide the input length. -/
theorem Sha3_256Hash.hash_many.ragged (input : Slice Std.U8) (out : Slice (Std.Array Std.U8 32#usize))
    (hn : 0 < out.val.length) (h : input.val.length % out.val.length ≠ 0) :
    p3_keccak.hax_roots.sha3_256_hash_many input out = .fail .panic :=
  Proofs.Keccak.hash_many_ragged _ input out hn h

/-- With `n > 0` digests and `n len` input bytes, `Sha3_256Hash::hash_many` returns `n` digests, digest `j` being SHA3-256 of bytes `j len` to `(j + 1) len - 1`. -/
theorem Sha3_256Hash.hash_many.eq_sha3_256 (input : Slice Std.U8) (out : Slice (Std.Array Std.U8 32#usize))
    (len : ℕ) (hn : 0 < out.val.length) (hlen : input.val.length = out.val.length * len) :
    ∃ r, p3_keccak.hax_roots.sha3_256_hash_many input out = .ok r ∧ r.val.length = out.val.length ∧
      ∀ j (hj : j < r.val.length), (r.val[j]).val.map UScalar.bv =
        sha3_256 (((input.val.map UScalar.bv).drop (j * len)).take len) := by
  obtain ⟨r, hr, hl, hd⟩ := Proofs.Keccak.hash_many_digests 6#u8 input out len hn hlen
  exact ⟨r, hr, hl, fun j hj => by rw [hd j hj, Proofs.Keccak.sha3_256_eq]; rfl⟩

end Plonky3Lean.Claims.P3Keccak
