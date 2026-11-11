module

public import Plonky3Lean.Proofs.Hash.Keccak.Permutation
public import Plonky3Lean.Proofs.Hash.Keccak.Sponge

@[expose] public section

/-!
# Keccak-f[1600]: the Keccak team's known answer

The Keccak team's file KeccakF-1600-IntermediateValues.txt permutes the all-zero state twice.

The first output, lane by lane, is checked here by the kernel on the transcription.

The digests of the empty string and of "abc" are checked on the specification.

They are the values the Keccak team and NIST's examples publish.
-/

open Aeneas Aeneas.Std Plonky3Lean.Spec.Keccak

namespace Plonky3Lean.Proofs.Keccak

/-- The all-zero state after one permutation, word x + 5 y holding lane (x, y). -/
def zeroOnce : List Std.U64 := [
  0xF1258F7940E1DDE7#u64, 0x84D5CCF933C0478A#u64, 0xD598261EA65AA9EE#u64, 0xBD1547306F80494D#u64,
  0x8B284E056253D057#u64, 0xFF97A42D7F8E6FD4#u64, 0x90FEE5A0A44647C4#u64, 0x8C5BDA0CD6192E76#u64,
  0xAD30A6F71B19059C#u64, 0x30935AB7D08FFC64#u64, 0xEB5AA93F2317D635#u64, 0xA9A6E6260D712103#u64,
  0x81A57C16DBCF555F#u64, 0x43B831CD0347C826#u64, 0x01F22F1A11A5569F#u64, 0x05E5635A21D9AE61#u64,
  0x64BEFEF28CC970F2#u64, 0x613670957BC46611#u64, 0xB87C5A554FD00ECB#u64, 0x8C3EE88A1CCF32C8#u64,
  0x940C7922AE3A2614#u64, 0x1841F924A2C509E4#u64, 0x16F53526E70465C2#u64, 0x75F644E97F30A13B#u64,
  0xEAF1FF7B5CECA249#u64]

theorem keccakFL_zero : keccakFL (List.replicate 25 0) = zeroOnce.map UScalar.bv := by
  decide +kernel

theorem ofLanes_zero : ofLanes (List.replicate 25 0) = fun _ _ _ => false := by
  funext x y z
  have h : ∀ i, lane (List.replicate 25 0) i = 0 := by
    intro i
    simp only [lane, List.getD_eq_getElem?_getD, List.getElem?_replicate]
    split <;> rfl
  rw [ofLanes_val, h]
  simp

/-- FIPS 202's Keccak-f[1600] maps the all-zero state to the Keccak team's first output. -/
theorem keccakP_zero : keccakP 24 (fun _ _ _ => false) = ofLanes (zeroOnce.map UScalar.bv) := by
  rw [← ofLanes_zero, ← keccakFL_eq, keccakFL_zero]

theorem map_bv_injective {l l' : List Std.U64} (h : l.map UScalar.bv = l'.map UScalar.bv) : l = l' :=
  List.map_injective_iff.mpr (by intro a b e; cases a; cases b; cases e; rfl) h

/-- tiny-keccak's permutation maps the all-zero array to the Keccak team's first output. -/
theorem keccakf_zero :
    tiny_keccak.keccakf.keccakf (Std.Array.from (List.replicate 25 0#u64) (by simp)) =
      .ok (Std.Array.from zeroOnce (by simp [zeroOnce])) := by
  have h := rounds_eq (List.replicate 25 0#u64) (by simp)
  have hz : (List.replicate 25 0#u64).map UScalar.bv = List.replicate 25 0 := by simp
  rw [hz, keccakFL_zero] at h
  have e := map_bv_injective h.1
  simp only [tiny_keccak.keccakf.keccakf, Std.Array.from_val, e]
  rfl

/-- The bytes of an ASCII string. -/
def ascii (s : String) : List Spec.Keccak.Byte := s.toList.map fun c => BitVec.ofNat 8 c.toNat

/-- The bytes of a hexadecimal string. -/
def hex (s : String) : List Spec.Keccak.Byte :=
  let d (c : Char) : ℕ := if c.isDigit then c.toNat - '0'.toNat else c.toNat - 'a'.toNat + 10
  let rec go : List Char → List Spec.Keccak.Byte
    | a :: b :: rest => BitVec.ofNat 8 (16 * d a + d b) :: go rest
    | _ => []
  go s.toList

theorem keccak256_empty :
    keccak256 [] = hex "c5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470" := by
  rw [keccak256_eq]
  decide +kernel

theorem keccak256_abc :
    keccak256 (ascii "abc") = hex "4e03657aea45a94fc7d47ba826c8d667c0d1e6e33a64a036ec44f58fa12d6c45" := by
  rw [keccak256_eq]
  decide +kernel

theorem sha3_256_empty :
    sha3_256 [] = hex "a7ffc6f8bf1ed76651c14756a061d662f580ff4de43b49fa82d80a4b80f8434a" := by
  rw [sha3_256_eq]
  decide +kernel

theorem sha3_256_abc :
    sha3_256 (ascii "abc") = hex "3a985da74fe225b2045c172d6bd390bd855f086e3e9d525b46bfe24511431532" := by
  rw [sha3_256_eq]
  decide +kernel

end Plonky3Lean.Proofs.Keccak
