module

public import Plonky3Lean.Spec.Blake3

@[expose] public section

/-!
# BLAKE3: the official test vectors

The input of each vector is the bytes `0, 1, …, 250`, repeated, cut to its length; the digests are the
`hash` entries of the BLAKE3 repository's `test_vectors.json`.
-/

open Plonky3Lean.Spec.Blake3

namespace Plonky3Lean.Proofs.Blake3

/-- The test-vector input of `n` bytes. -/
def kat (n : ℕ) : List Byte := (List.range n).map fun i => BitVec.ofNat 8 (i % 251)

/-- The bytes of a lowercase hexadecimal string. -/
def hex (s : String) : List Byte :=
  let d (c : Char) : ℕ := if c.isDigit then c.toNat - '0'.toNat else c.toNat - 'a'.toNat + 10
  let rec go : List Char → List Byte
    | a :: b :: rest => BitVec.ofNat 8 (16 * d a + d b) :: go rest
    | _ => []
  go s.toList

theorem digest_0 : digest (kat 0) =
    hex "af1349b9f5f9a1a6a0404dea36dcc9499bcb25c9adc112b7cc9a93cae41f3262" := by decide +kernel

theorem digest_1 : digest (kat 1) =
    hex "2d3adedff11b61f14c886e35afa036736dcd87a74d27b5c1510225d0f592e213" := by decide +kernel

theorem digest_65 : digest (kat 65) =
    hex "de1e5fa0be70df6d2be8fffd0e99ceaa8eb6e8c93a63f2d8d1c30ecb6b263dee" := by decide +kernel

theorem digest_1024 : digest (kat 1024) =
    hex "42214739f095a406f3fc83deb889744ac00df831c10daa55189b5d121c855af7" := by decide +kernel

theorem digest_1025 : digest (kat 1025) =
    hex "d00278ae47eb27b34faecf67b4fe263f82d5412916c1ffd97c8cb7fb814b8444" := by decide +kernel

theorem digest_2049 : digest (kat 2049) =
    hex "5f4d72f40d7a5f82b15ca2b2e44b1de3c2ef86c426c95c1af0b6879522563030" := by decide +kernel

end Plonky3Lean.Proofs.Blake3
