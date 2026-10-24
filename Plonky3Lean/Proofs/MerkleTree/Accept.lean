module

public import Plonky3Lean.Proofs.MerkleTree.Panics
public import Plonky3Lean.Proofs.MerkleTree.Complete

@[expose] public section

/-!
# When the single-index verifier accepts

The verifier accepts an opening when:

- its rows have their matrices' widths
- its siblings number as the walked levels take
- its index is below the tallest height
- its cap holds as many roots as the top layers produce
- its walk reaches the cap entry at its index.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open p3_merkle_tree

namespace Plonky3Lean.Proofs.MerkleTree

theorem verify_ok_of {P PW F W H C : Type} {N DIGEST_ELEMS : Std.Usize}
    (cl : core.clone.Clone F) (cp : core.marker.Copy W)
    (dfInst : core.default.Default W) (eqInst : core.cmp.PartialEq W W)
    (hInst : p3_symmetric.hasher.CryptographicHasher H F (Std.Array W DIGEST_ELEMS))
    (cInst : p3_symmetric.compression.PseudoCompressionFunction C (Std.Array W DIGEST_ELEMS) N)
    (mt : mmcs.MerkleTreeMmcs P PW H C N DIGEST_ELEMS)
    (h : List (List F) → Std.Array W DIGEST_ELEMS)
    (c : List (Std.Array W DIGEST_ELEMS) → Std.Array W DIGEST_ELEMS)
    (hH : HashOn hInst mt.hash h) (hC : CompressOn cInst mt.compress c)
    (hcl : ∀ x, ∃ v, cp.cloneCloneInst.clone x = RustM.ok v)
    (hdf : ∃ t, dfInst.default = RustM.ok t)
    (hrefl : ∀ x, eqInst.eq x x = RustM.ok true) (hN : 2 ≤ N.val)
    (dims : Slice p3_matrix.Dimensions) (val : Std.Usize) (sched : alloc.vec.Vec Std.Usize)
    (pl expected : Std.Usize) (sched1 : alloc.vec.Vec Std.Usize) (epl : Std.Usize)
    (order : alloc.vec.Vec Std.Usize) (curr lnpt pos : Std.Usize)
    (hval : mmcs.hax_reshaped.validate_heights dims = RustM.ok (core.result.Result.Ok val))
    (hsched : mmcs.hax_reshaped.arity_schedule_and_proof_levels N mt.cap_height dims =
      RustM.ok (core.result.Result.Ok (sched, pl)))
    (hexp : mmcs.hax_reshaped.check_cap_size_loop sched 1#usize pl = RustM.ok expected)
    (hsched1 : alloc.vec.Vec.truncate sched pl = RustM.ok sched1)
    (hepl : mmcs.hax_reshaped.verify_batch_loop0 sched1 0#usize 0#usize = RustM.ok epl)
    (horder : mmcs.hax_reshaped.tallest_first dims = RustM.ok order)
    (hcurr : p3_merkle_tree.merkle_tree.padded_len val N = RustM.ok curr)
    (hlnpt : core.num.Usize.next_power_of_two val = RustM.ok lnpt)
    (hpos : mmcs.hax_reshaped.verify_batch_loop1 dims order lnpt 0#usize = RustM.ok pos)
    (hheights : ∀ d ∈ dims.val, d.height.val ≤ 2 ^ (UScalarTy.Usize.numBits - 1))
    (commit : p3_symmetric.hash.MerkleCap F (Std.Array W DIGEST_ELEMS)) (index : Std.Usize)
    (opened : Slice (alloc.vec.Vec F)) (proof : Slice (Std.Array W DIGEST_ELEMS))
    (hlen0 : opened.val.length = dims.val.length)
    (hw : ∀ m (hm : m < dims.val.length) (hm' : m < opened.val.length),
      (opened.val[m]).val.length = (dims.val[m]).width.val)
    (hproof : proof.val.length = sibSum sched1 0) (hidx : index.val < val.val)
    (hcapl : commit.cap.val.length = expected.val)
    (hroot : ∀ (t : W) (dflt : Std.Array W DIGEST_ELEMS) (padA : Std.Array (Std.Array W DIGEST_ELEMS) N),
      dfInst.default = RustM.ok t → core.array.repeat DIGEST_ELEMS cp.cloneCloneInst t = RustM.ok dflt →
      core.array.repeat N (core.Array.Insts.CoreCloneClone DIGEST_ELEMS cp.cloneCloneInst) dflt =
        RustM.ok padA →
      let pl0 := plan N.val (heightOf dims) (ordL order) (schedFrom sched1 0) curr.val pos.val
      let w := walk h c padA.val dflt (ordL order) (openedL opened) proof.val pl0 index.val 0
        (h (group (ordL order) (openedL opened) 0 pos.val))
      commit.cap.val[w.1]? = some w.2) :
    mmcs.hax_reshaped.verify_batch cl cp dfInst eqInst hInst cInst mt commit dims index opened
      proof = RustM.ok (core.result.Result.Ok ()) := by
  unfold mmcs.hax_reshaped.verify_batch
  simp only [core.slice.Slice.len, rust_primitives.slice.slice_length, bind_ok]
  rw [ite_eq_right (by simp; omega)]
  have hlen : dims.val.length = opened.val.length := hlen0.symm
  rw [hval, bind_ok, branch_ok_eq, bind_ok]
  dsimp only
  -- The cap holds as many roots as the top layers produce.
  have hcap : mmcs.hax_reshaped.check_cap_size N mt.cap_height commit dims =
      RustM.ok (core.result.Result.Ok ()) := by
    unfold mmcs.hax_reshaped.check_cap_size
    rw [hsched, bind_ok, branch_ok_eq, bind_ok]
    refine bind_eq_of hexp ?_
    refine bind_eq_of (x := p3_symmetric.hash.MerkleCap.num_roots commit) rfl ?_
    split
    · rename_i hne
      exfalso
      simp only [bne_iff_ne, ne_eq] at hne
      apply hne
      apply UScalar.eq_of_val_eq
      simpa using hcapl
    · rfl
  rw [hcap, bind_ok, branch_ok_eq, bind_ok]
  dsimp only
  rw [hsched, bind_ok, branch_ok_eq, bind_ok]
  show Std.bind (alloc.vec.Vec.truncate sched pl) _ = _
  rw [hsched1, bind_ok, hepl, bind_ok]
  have hplen : proof.val.length = epl.val := by rw [hproof, sum_loop_ok hepl]
  rw [ite_eq_right (by
    simp only [bne_iff_ne, ne_eq, Decidable.not_not]
    apply UScalar.eq_of_val_eq; simpa using hplen)]
  rw [check_widths_eq_ok dims opened hlen0 hw, bind_ok, branch_ok_eq, bind_ok]
  dsimp only
  rw [horder, bind_ok, hcurr, bind_ok, ite_eq_right (by
    intro hge; have : index.val ≥ val.val := hge; omega)]
  rw [hlnpt, bind_ok, hpos, bind_ok]
  rw [show alloc.vec.Vec.Insts.CoreOpsDerefDerefSlice.deref order = RustM.ok (vs order) from rfl,
    bind_ok]
  have hordD := tallest_first_ok horder
  have hordO : ∀ i ∈ order.val, i.val < opened.val.length := fun i hi => hlen ▸ hordD i hi
  have hpos_le := leaf_pos_le hpos
  rw [hH _ _ (rowsList opened (vs order) 0 pos.val)
    ⟨_, rfl, rows_yields opened (vs order) (by rw [vs_val]; exact hordO) _ 0#usize pos rfl
      (by rw [vs_val]; exact hpos_le)⟩, bind_ok]
  obtain ⟨t, ht⟩ := hdf
  rw [ht, bind_ok]
  obtain ⟨dflt, hdflt⟩ := Lib.array_repeat_ok DIGEST_ELEMS cp.cloneCloneInst hcl t
  rw [hdflt, bind_ok]
  obtain ⟨padA, hpad⟩ := Lib.array_repeat_ok N
    (core.Array.Insts.CoreCloneClone DIGEST_ELEMS cp.cloneCloneInst)
    (Lib.array_clone_ok cp.cloneCloneInst hcl) dflt
  have hsteps : ∀ s ∈ sched1.val, s.val = 2 ∨ s = N := by
    intro s hs
    rw [vec_truncate_ok hsched1] at hs
    exact (arity_schedule_ok hsched).1 s (List.mem_of_mem_take hs)
  obtain ⟨⟨ci, df⟩, hloop⟩ := loop2_total cl cp hInst cInst mt.hash mt.compress h c hH hC dims opened
    proof sched1 order dflt padA hpad hN hsteps hordD hordO hheights index curr pos _ 0#usize 0#usize
    hpos_le (by simp) (by rw [hproof]; simp)
  have hw2 := walk_ok cl cp hInst cInst mt.hash mt.compress h c hH hC dims opened proof sched1 order
    dflt padA hpad hordO _ index curr pos
    (h ((rowsList opened (vs order) 0 pos.val).map fun x => x.val)) 0#usize 0#usize ci df rfl hloop
  have hr := hroot t dflt padA ht hdflt hpad
  simp only at hr
  rw [rowsList_val opened order hordO] at hw2
  have hci : commit.cap.val[ci.val]? = some df := by
    have e1 := congrArg Prod.fst hw2
    have e2 := congrArg Prod.snd hw2
    simp only at e1 e2
    rw [e1, e2]
    exact hr
  have hcil : ci.val < commit.cap.val.length := (List.getElem?_eq_some_iff.mp hci).1
  refine bind_eq_of hloop ?_
  refine bind_eq_of (x := p3_symmetric.hash.MerkleCap.num_roots commit) rfl ?_
  split
  swap
  · rename_i hn
    exact absurd (by simpa using hcil) hn
  simp only [p3_symmetric.hash.MerkleCap.Insts.CoreOpsIndexIndexUsizeDigest.index]
  rw [vec_index_eq commit.cap ci hcil, bind_ok]
  rw [List.getElem?_eq_getElem hcil] at hci
  rw [Option.some.inj hci, array_eq_self eqInst hrefl, bind_ok, ite_eq_left rfl]

open Plonky3Lean.Spec.MerkleTree in
/-- Completeness: the verifier accepts an honest opening of the tree.

In an honest opening:

- the tree's padding digest and padded children are the verifier's own
- its layers match the verifier's plan along the path
- the leaf is the hash of the leaf rows
- the siblings are the path's
- the cap holds the top layer. -/
theorem verify_complete {P PW F W H C : Type} {N DIGEST_ELEMS : Std.Usize}
    (cl : core.clone.Clone F) (cp : core.marker.Copy W)
    (dfInst : core.default.Default W) (eqInst : core.cmp.PartialEq W W)
    (hInst : p3_symmetric.hasher.CryptographicHasher H F (Std.Array W DIGEST_ELEMS))
    (cInst : p3_symmetric.compression.PseudoCompressionFunction C (Std.Array W DIGEST_ELEMS) N)
    (mt : mmcs.MerkleTreeMmcs P PW H C N DIGEST_ELEMS)
    (h : List (List F) → Std.Array W DIGEST_ELEMS)
    (c : List (Std.Array W DIGEST_ELEMS) → Std.Array W DIGEST_ELEMS)
    (hH : HashOn hInst mt.hash h) (hC : CompressOn cInst mt.compress c)
    (hcl : ∀ x, ∃ v, cp.cloneCloneInst.clone x = RustM.ok v)
    (hrefl : ∀ x, eqInst.eq x x = RustM.ok true) (hN : 2 ≤ N.val)
    (dims : Slice p3_matrix.Dimensions) (val : Std.Usize) (sched : alloc.vec.Vec Std.Usize)
    (pl expected : Std.Usize) (sched1 : alloc.vec.Vec Std.Usize) (epl : Std.Usize)
    (order : alloc.vec.Vec Std.Usize) (curr lnpt pos : Std.Usize)
    (hval : mmcs.hax_reshaped.validate_heights dims = RustM.ok (core.result.Result.Ok val))
    (hsched : mmcs.hax_reshaped.arity_schedule_and_proof_levels N mt.cap_height dims =
      RustM.ok (core.result.Result.Ok (sched, pl)))
    (hexp : mmcs.hax_reshaped.check_cap_size_loop sched 1#usize pl = RustM.ok expected)
    (hsched1 : alloc.vec.Vec.truncate sched pl = RustM.ok sched1)
    (hepl : mmcs.hax_reshaped.verify_batch_loop0 sched1 0#usize 0#usize = RustM.ok epl)
    (horder : mmcs.hax_reshaped.tallest_first dims = RustM.ok order)
    (hcurr : p3_merkle_tree.merkle_tree.padded_len val N = RustM.ok curr)
    (hlnpt : core.num.Usize.next_power_of_two val = RustM.ok lnpt)
    (hpos : mmcs.hax_reshaped.verify_batch_loop1 dims order lnpt 0#usize = RustM.ok pos)
    (hheights : ∀ d ∈ dims.val, d.height.val ≤ 2 ^ (UScalarTy.Usize.numBits - 1))
    (commit : p3_symmetric.hash.MerkleCap F (Std.Array W DIGEST_ELEMS)) (index : Std.Usize)
    (opened : Slice (alloc.vec.Vec F)) (proof : Slice (Std.Array W DIGEST_ELEMS))
    (hlen0 : opened.val.length = dims.val.length)
    (hw : ∀ m (hm : m < dims.val.length) (hm' : m < opened.val.length),
      (opened.val[m]).val.length = (dims.val[m]).width.val)
    (hproof : proof.val.length = sibSum sched1 0) (hidx : index.val < val.val)
    (hcapl : commit.cap.val.length = expected.val)
    (t : W) (dflt : Std.Array W DIGEST_ELEMS) (padA : Std.Array (Std.Array W DIGEST_ELEMS) N)
    (ht : dfInst.default = RustM.ok t)
    (hdflt : core.array.repeat DIGEST_ELEMS cp.cloneCloneInst t = RustM.ok dflt)
    (hpad : core.array.repeat N (core.Array.Insts.CoreCloneClone DIGEST_ELEMS cp.cloneCloneInst) dflt =
      RustM.ok padA)
    (ls : List (LayerSpec (Std.Array W DIGEST_ELEMS))) (L0 : ℕ → Std.Array W DIGEST_ELEMS)
    (hmatch : Matches h padA.val (ordL order) (openedL opened)
      (plan N.val (heightOf dims) (ordL order) (schedFrom sched1 0) curr.val pos.val) ls index.val)
    (hleaf : L0 index.val = h (group (ordL order) (openedL opened) 0 pos.val))
    (hpath : proof.val = path c padA.val dflt L0 ls index.val)
    (hcap : commit.cap.val[capIndex (plan N.val (heightOf dims) (ordL order) (schedFrom sched1 0)
        curr.val pos.val) index.val]? =
      some (top c padA.val dflt L0 ls (capIndex (plan N.val (heightOf dims) (ordL order)
        (schedFrom sched1 0) curr.val pos.val) index.val))) :
    mmcs.hax_reshaped.verify_batch cl cp dfInst eqInst hInst cInst mt commit dims index opened
      proof = RustM.ok (core.result.Result.Ok ()) := by
  refine verify_ok_of cl cp dfInst eqInst hInst cInst mt h c hH hC hcl ⟨t, ht⟩ hrefl hN dims val sched
    pl expected sched1 epl order curr lnpt pos hval hsched hexp hsched1 hepl horder hcurr hlnpt hpos
    hheights commit index opened proof hlen0 hw hproof hidx hcapl ?_
  intro t' dflt' padA' ht' hdflt' hpad'
  rw [ht] at ht'; cases ok_inj ht'
  rw [hdflt] at hdflt'; cases ok_inj hdflt'
  rw [hpad] at hpad'; cases ok_inj hpad'
  simp only
  rw [← hleaf, walk_honest h c padA.val dflt (ordL order) (openedL opened) proof.val _ ls L0 index.val 0
    hmatch (by intro j _; rw [hpath]; simp)]
  exact hcap

end Plonky3Lean.Proofs.MerkleTree
