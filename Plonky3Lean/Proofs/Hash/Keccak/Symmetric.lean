module

public import Plonky3Lean.Proofs.Hash.Keccak.P3
public import Plonky3Lean.Proofs.Symmetric.Sponge

@[expose] public section

/-!
# p3-keccak in the sponges of p3-symmetric

Merkle trees and challengers over `u64` use Keccak-f as the permutation of a padding-free sponge.

The impl of the permutation on `[u64; 25]` computes tiny-keccak's 24 rounds, so the sponge theorems of p3-symmetric apply to it.
-/

open Aeneas Aeneas.Std CoreModels
open Plonky3Lean.Lib Plonky3Lean.Proofs.Symmetric

namespace Plonky3Lean.Proofs.Keccak

/-- The permutation as a `CryptographicPermutation<[u64; 25]>`; the Rust impl adds no items. -/
def keccakPerm : p3_symmetric.permutation.CryptographicPermutation p3_keccak.KeccakF (Std.Array Std.U64 25#usize) :=
  { PermutationInst := p3_keccak.KeccakF.Insts.P3_symmetricPermutationPermutationArrayU6425
    corecloneCloneInst := CoreModels.core.Array.Insts.CoreCloneClone 25#usize CoreModels.core.U64.Insts.CoreCloneClone }

theorem keccakPerm_computes : PermComputes keccakPerm () tiny_keccak.keccakf.rounds where
  permute s := by
    refine ⟨Std.Array.from (tiny_keccak.keccakf.rounds s.val) (rounds_eq s.val (by simp)).2, ?_,
      Std.Array.from_val _ _⟩
    show keccakPerm.PermutationInst.permute () s = _
    rw [keccakPerm, inst_u64_eq]
    exact (permute_mut_eq s).trans (keccakf_eq s)
  permute_mut s := by
    refine ⟨Std.Array.from (tiny_keccak.keccakf.rounds s.val) (rounds_eq s.val (by simp)).2, ?_,
      Std.Array.from_val _ _⟩
    show keccakPerm.PermutationInst.permute_mut () s = _
    rw [keccakPerm, inst_u64_eq]
    exact (permute_mut_eq s).trans (keccakf_eq s)

end Plonky3Lean.Proofs.Keccak
