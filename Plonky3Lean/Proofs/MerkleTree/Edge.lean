module

public import Plonky3Lean.Proofs.MerkleTree.Schedule
public import Plonky3Lean.Proofs.MerkleTree.Bind
public import Plonky3Lean.Proofs.MerkleTree.Total

@[expose] public section

/-!
# What an accepting run rules out, and what the commitment does not bind

An accepting run had:

- a nonempty batch with a positive tallest height
- an index below it
- one row per matrix, at its width
- exactly the siblings the walked levels take.

The commitment binds rows only to the dimensions the verifier is given.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open p3_merkle_tree

namespace Plonky3Lean.Proofs.MerkleTree

/-- What every accepting run checked: the batch, the index, the widths and the number of siblings. -/
theorem verify_accepts_shape {P PW F W H C : Type} {N DIGEST_ELEMS : Std.Usize}
    (cl : core.clone.Clone F) (cp : core.marker.Copy W)
    (dfInst : core.default.Default W) (eqInst : core.cmp.PartialEq W W)
    (hInst : p3_symmetric.hasher.CryptographicHasher H F (Std.Array W DIGEST_ELEMS))
    (cInst : p3_symmetric.compression.PseudoCompressionFunction C (Std.Array W DIGEST_ELEMS) N)
    (mt : mmcs.MerkleTreeMmcs P PW H C N DIGEST_ELEMS)
    (commit : p3_symmetric.hash.MerkleCap F (Std.Array W DIGEST_ELEMS))
    (dims : Slice p3_matrix.Dimensions) (index : Std.Usize) (opened : Slice (alloc.vec.Vec F))
    (proof : Slice (Std.Array W DIGEST_ELEMS))
    (h : mmcs.hax_reshaped.verify_batch cl cp dfInst eqInst hInst cInst mt commit dims index opened
      proof = RustM.ok (core.result.Result.Ok ())) :
    0 < maxHeight dims ∧ index.val < maxHeight dims ∧
    opened.val.length = dims.val.length ∧
    (∀ m (hm : m < dims.val.length) (hm' : m < opened.val.length),
      (opened.val[m]).val.length = (dims.val[m]).width.val) ∧
    ∃ (sched : alloc.vec.Vec Std.Usize) (pl : Std.Usize),
      mmcs.hax_reshaped.arity_schedule_and_proof_levels N mt.cap_height dims =
        RustM.ok (core.result.Result.Ok (sched, pl)) ∧
      proof.val.length = ((sched.val.take pl.val).map fun s => s.val - 1).sum := by
  obtain ⟨val, sched, pl, sched1, order, curr, lnpt, pos, t, dflt, d0, ci, df, a,
    hval, hsched, hsched1, hw, horder, hcurr, hidx, hlnpt, hpos, hd0, ht, hdflt, hloop, ha,
    heq, epl, hepl, hplen⟩ := verify_accepts cl cp dfInst eqInst hInst cInst mt commit dims index opened proof h
  obtain ⟨hv, hv0⟩ := validate_ok_val hval
  obtain ⟨hl, hwd⟩ := check_widths_ok hw
  refine ⟨hv ▸ hv0, hv ▸ hidx, hl, hwd, sched, pl, hsched, ?_⟩
  -- The sibling count was checked against the sum over the walked levels.
  rw [hplen, sum_loop_ok hepl, sibSum, vec_truncate_ok hsched1]
  simp

end Plonky3Lean.Proofs.MerkleTree
