module

public import Plonky3Lean.Proofs.Hash.Sha256.P3

@[expose] public section

/-!
# SHA-256: the specification against FIPS 180-4's examples, and sha2 on any state

The specification's digests of the examples in FIPS 180-4's appendices, checked by the kernel.

The compression of the padded message `"abc"`, one block, is its digest.
-/

open Aeneas Aeneas.Std CoreModels
open Plonky3Lean.Spec.Sha256 Plonky3Lean.Lib

namespace Plonky3Lean.Proofs.Sha256

/-- The bytes of an ASCII string. -/
def ascii (s : String) : List Spec.Sha256.Byte := s.toList.map fun c => BitVec.ofNat 8 c.toNat

/-- The bytes of a hexadecimal string. -/
def hex (s : String) : List Spec.Sha256.Byte :=
  let d (c : Char) : ℕ := if c.isDigit then c.toNat - '0'.toNat else c.toNat - 'a'.toNat + 10
  let rec go : List Char → List Spec.Sha256.Byte
    | a :: b :: rest => BitVec.ofNat 8 (16 * d a + d b) :: go rest
    | _ => []
  go s.toList

theorem digest_empty : digest [] =
    hex "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855" := by
  decide +kernel

theorem digest_abc : digest (ascii "abc") =
    hex "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad" := by
  decide +kernel

theorem digest_448 :
    digest (ascii "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq") =
      hex "248d6a61d20638b8e5c026930c3e6039a33ce45964ff2167f6ecedd419db06c1" := by
  decide +kernel

theorem digest_896 :
    digest (ascii ("abcdefghbcdefghicdefghijdefghijkefghijklfghijklmghijklmnhijklmno" ++
      "ijklmnopjklmnopqklmnopqrlmnopqrsmnopqrstnopqrstu")) =
      hex "cf5b16a778af8380036ce59e7b0492370b249b11e8f07a51afac45037afee9d1" := by
  decide +kernel

/-- One block, `"abc"` padded, compresses from `H^(0)` to its digest. -/
theorem compress_pad_abc : bytesOfWords (compress H0 (wordsOfBytes (pad (ascii "abc")))) =
    hex "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad" := by
  decide +kernel

theorem toArray8_bv (s : Std.Array Std.U32 8#usize) : toArray8 (s.val.map UScalar.bv) = s := by
  apply Std.Array.ext
  have hs : s.val.length = 8 := by simp
  simp only [toArray8, Std.Array.make_val]
  rw [List.take_append_of_le_length (by simp [hs]), List.take_of_length_le (by simp [hs]),
    List.map_map]
  conv_rhs => rw [← List.map_id s.val]
  rfl

theorem toArray8_val_bv (H : List Word) (hH : H.length = 8) : (toArray8 H).val.map UScalar.bv = H := by
  simp only [toArray8, Std.Array.make_val, List.map_map]
  rw [List.take_append_of_le_length (by omega), List.take_of_length_le (by omega)]
  conv_rhs => rw [← List.map_id H]
  rfl

/-- sha2's `compress256` from any state: FIPS 180-4's compression of each block in turn. -/
theorem compress256_spec (state : Std.Array Std.U32 8#usize)
    (blocks : Slice (Std.Array Std.U8 64#usize)) :
    sha2.sha256.compress256 state blocks ⦃ r => r.val.map UScalar.bv =
      blocks.val.foldl (fun H b => compress H (wordsOfBytes (b.val.map UScalar.bv)))
        (state.val.map UScalar.bv) ⦄ := by
  have h := compress256_eq (state.val.map UScalar.bv) (by simp) blocks
  rw [toArray8_bv] at h
  rw [h, WP.spec_ok, toArray8_val_bv _ (length_compressBlocks _ (by simp) _)]
  rfl

end Plonky3Lean.Proofs.Sha256
