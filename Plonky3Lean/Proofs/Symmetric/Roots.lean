module

public import Plonky3Lean.Proofs.Symmetric.Misc
public import Plonky3Lean.Proofs.Symmetric.Collisions

@[expose] public section

/-!
# The extraction roots, on arrays of every length
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open Plonky3Lean.Spec.Sponge

namespace Plonky3Lean.Proofs.Symmetric

theorem root_padding_free_hash {T P : Type} {W RATE OUT LEN : Std.Usize}
    (defInst : core.default.Default T) (copyInst : core.marker.Copy T)
    (permInst : p3_symmetric.permutation.CryptographicPermutation P (Std.Array T W))
    (sp : p3_symmetric.sponge.PaddingFreeSponge P W RATE OUT) (input : Std.Array T LEN)
    (f : List T → List T) (z : T) (hf : PermComputes permInst sp.permutation f)
    (hz : defInst.default = .ok z) (hcl : ∀ x, copyInst.cloneCloneInst.clone x = .ok x)
    (hr : 0 < RATE.val) (hrw : RATE.val < W.val) (hout : OUT.val ≤ RATE.val) :
    ∃ out, p3_symmetric.hax_roots.padding_free_sponge_hash defInst copyInst permInst sp input =
      .ok out ∧ out.val = paddingFree f z W.val RATE.val OUT.val input.val := by
  unfold p3_symmetric.hax_roots.padding_free_sponge_hash
    p3_symmetric.sponge.PaddingFreeSponge.Insts.P3_symmetricHasherCryptographicHasherTArray.hash_iter
  exact padding_free_hash_eq RATE OUT defInst copyInst permInst _ sp.permutation input f z
    input.val hf hz hcl (array_into_iter_yields input) hr hrw (by omega)

theorem root_pad10_hash {T P D : Type} {W RATE OUT LEN : Std.Usize}
    (defInst : core.default.Default T) (copyInst : core.marker.Copy T)
    (permInst : p3_symmetric.permutation.CryptographicPermutation P (Std.Array T W))
    (derInst : p3_symmetric.permutation.Derangement D T)
    (sp : p3_symmetric.sponge.Pad10Sponge T P D W RATE OUT) (input : Std.Array T LEN)
    (f : List T → List T) (d : T → T) (z : T) (hf : PermComputes permInst sp.permutation f)
    (hd : ∀ x, derInst.PermutationInst.permute sp.padding_derangement x = .ok (d x))
    (hz : defInst.default = .ok z) (hcl : ∀ x, copyInst.cloneCloneInst.clone x = .ok x)
    (hr : 0 < RATE.val) (hrw : RATE.val < W.val) (hout : OUT.val ≤ RATE.val) :
    ∃ out, p3_symmetric.hax_roots.pad10_sponge_hash defInst copyInst permInst derInst sp input =
      .ok out ∧ out.val = pad10 f d z W.val RATE.val OUT.val input.val := by
  unfold p3_symmetric.hax_roots.pad10_sponge_hash
    p3_symmetric.sponge.Pad10Sponge.Insts.P3_symmetricHasherCryptographicHasherTArray.hash_iter
  exact pad10_hash_eq RATE OUT defInst copyInst permInst derInst _ sp.permutation
    sp.padding_derangement input f d z input.val hf hd hz hcl (array_into_iter_yields input) hr hrw
    (by omega)

end Plonky3Lean.Proofs.Symmetric
