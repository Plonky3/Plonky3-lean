module

public import Plonky3Lean.Proofs.MerkleTree.Total

@[expose] public section

/-!
# What the prover cannot make the verifier do

Once the dimensions pass the verifier's own checks, no index, opened rows, siblings or cap make it panic or loop.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open p3_merkle_tree

namespace Plonky3Lean.Proofs.MerkleTree

/-- A bind whose first step returns `a`, and whose rest returns from `a`, returns. -/
theorem bind_exists {α β : Type _} {x : RustM α} {f : α → RustM β} {a : α} (hx : x = RustM.ok a)
    (h : ∃ r, f a = RustM.ok r) : ∃ r, Std.bind x f = RustM.ok r := by
  rw [hx, bind_ok]; exact h

/-- A bind whose first step returns `a` computes the rest at `a`. -/
theorem bind_eq_of {α β : Type _} {x : RustM α} {f : α → RustM β} {a : α} {v : RustM β}
    (hx : x = RustM.ok a) (h : f a = v) : Std.bind x f = v := by
  rw [hx, bind_ok]; exact h

theorem branch_ok_eq {T E : Type _} (v : T) :
    core.result.Result.Insts.CoreOpsTry_traitTry.branch (core.result.Result.Ok v : core.result.Result T E) =
      RustM.ok (core.ops.control_flow.ControlFlow.Continue v) := rfl

theorem branch_err_eq {T E : Type _} (e : E) :
    core.result.Result.Insts.CoreOpsTry_traitTry.branch (core.result.Result.Err e : core.result.Result T E) =
      RustM.ok (core.ops.control_flow.ControlFlow.Break (core.result.Result.Err e)) := rfl

theorem branch_total {T E : Type _} (r : core.result.Result T E) :
    (∃ v, r = core.result.Result.Ok v ∧
      core.result.Result.Insts.CoreOpsTry_traitTry.branch r =
        RustM.ok (core.ops.control_flow.ControlFlow.Continue v)) ∨
    (∃ e, core.result.Result.Insts.CoreOpsTry_traitTry.branch r =
        RustM.ok (core.ops.control_flow.ControlFlow.Break (core.result.Result.Err e))) := by
  cases r with
  | Ok v => exact Or.inl ⟨v, rfl, rfl⟩
  | Err e => exact Or.inr ⟨e, rfl⟩

/-- The verifier's checks on the dimensions alone: each returns, and every height is at most half the word range.

None of these read the index, the opened rows, the siblings or the cap. -/
def DimsPass (N cap : Std.Usize) (dims : Slice p3_matrix.Dimensions) : Prop :=
  ∃ (val : Std.Usize) (sched : alloc.vec.Vec Std.Usize) (pl expected : Std.Usize)
    (sched1 : alloc.vec.Vec Std.Usize) (epl : Std.Usize) (order : alloc.vec.Vec Std.Usize)
    (curr lnpt pos : Std.Usize),
    mmcs.hax_reshaped.validate_heights dims = RustM.ok (core.result.Result.Ok val) ∧
    mmcs.hax_reshaped.arity_schedule_and_proof_levels N cap dims =
      RustM.ok (core.result.Result.Ok (sched, pl)) ∧
    mmcs.hax_reshaped.check_cap_size_loop sched 1#usize pl = RustM.ok expected ∧
    alloc.vec.Vec.truncate sched pl = RustM.ok sched1 ∧
    mmcs.hax_reshaped.verify_batch_loop0 sched1 0#usize 0#usize = RustM.ok epl ∧
    mmcs.hax_reshaped.tallest_first dims = RustM.ok order ∧
    p3_merkle_tree.merkle_tree.padded_len val N = RustM.ok curr ∧
    core.num.Usize.next_power_of_two val = RustM.ok lnpt ∧
    mmcs.hax_reshaped.verify_batch_loop1 dims order lnpt 0#usize = RustM.ok pos ∧
    ∀ d ∈ dims.val, d.height.val ≤ 2 ^ (UScalarTy.Usize.numBits - 1)

/-- The single-index verifier returns on every index, opened rows, siblings and cap, once the dimensions pass. -/
theorem verify_total {P PW F W H C : Type} {N DIGEST_ELEMS : Std.Usize}
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
    (heqt : ∀ x y, ∃ b, eqInst.eq x y = RustM.ok b) (hN : 2 ≤ N.val)
    (dims : Slice p3_matrix.Dimensions) (hdims : DimsPass N mt.cap_height dims)
    (commit : p3_symmetric.hash.MerkleCap F (Std.Array W DIGEST_ELEMS)) (index : Std.Usize)
    (opened : Slice (alloc.vec.Vec F)) (proof : Slice (Std.Array W DIGEST_ELEMS)) :
    ∃ r, mmcs.hax_reshaped.verify_batch cl cp dfInst eqInst hInst cInst mt commit dims index opened
      proof = RustM.ok r := by
  obtain ⟨val, sched, pl, expected, sched1, epl, order, curr, lnpt, pos, hval, hsched, hexp,
    hsched1, hepl, horder, hcurr, hlnpt, hpos, hheights⟩ := hdims
  unfold mmcs.hax_reshaped.verify_batch
  simp only [core.slice.Slice.len, rust_primitives.slice.slice_length, bind_ok]
  split
  · exact ⟨_, rfl⟩
  rename_i hne
  have hlen : dims.val.length = opened.val.length := by simpa using hne
  rw [hval, bind_ok, branch_ok_eq, bind_ok]
  dsimp only
  -- The cap size check.
  have hcap : ∃ r1, mmcs.hax_reshaped.check_cap_size N mt.cap_height commit dims = RustM.ok r1 := by
    unfold mmcs.hax_reshaped.check_cap_size
    rw [hsched, bind_ok, branch_ok_eq, bind_ok]
    simp only [bind_ok, p3_symmetric.hash.MerkleCap.num_roots, alloc.vec.Vec.len,
      rust_primitives.sequence.seq_len]
    show ∃ r1, (do
      let expected ← mmcs.hax_reshaped.check_cap_size_loop sched 1#usize pl
      if (Slice.len commit.cap != expected) = true then
          RustM.ok (core.result.Result.Err (mmcs.error.MerkleTreeError.WrongCapSize expected
            (Slice.len commit.cap)))
        else RustM.ok (core.result.Result.Ok ())) = RustM.ok r1
    rw [hexp, bind_ok]
    split <;> exact ⟨_, rfl⟩
  obtain ⟨r1, hr1⟩ := hcap
  rw [hr1, bind_ok]
  rcases branch_total r1 with ⟨u1, rfl, hb1⟩ | ⟨e1, hb1⟩
  swap
  · rw [hb1, bind_ok]
    dsimp only
    exact ⟨_, from_residual_err _⟩
  rw [branch_ok_eq, bind_ok]
  dsimp only
  rw [hsched, bind_ok, branch_ok_eq, bind_ok]
  refine bind_exists hsched1 ?_
  rw [hepl, bind_ok]
  split
  · exact ⟨_, rfl⟩
  rename_i hne2
  have hplen : proof.val.length = epl.val := by simpa using hne2
  obtain ⟨r3, hr3⟩ := check_widths_total dims opened
  rw [hr3, bind_ok]
  rcases branch_total r3 with ⟨u, rfl, hb⟩ | ⟨e, hb⟩
  swap
  · rw [hb, bind_ok]
    dsimp only
    exact ⟨_, from_residual_err _⟩
  rw [hb, bind_ok]
  dsimp only
  rw [horder, bind_ok, hcurr, bind_ok]
  split
  · exact ⟨_, rfl⟩
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
    hpos_le (by simp) (by rw [hplen, sum_loop_ok hepl]; simp)
  refine bind_exists hloop ?_
  refine bind_exists (x := p3_symmetric.hash.MerkleCap.num_roots commit) rfl ?_
  split
  · rename_i hci
    simp only [p3_symmetric.hash.MerkleCap.Insts.CoreOpsIndexIndexUsizeDigest.index]
    rw [vec_index_eq commit.cap ci (by simpa using hci), bind_ok]
    obtain ⟨b, hb⟩ := array_eq_total eqInst heqt (commit.cap.val[ci.val]'(by simpa using hci)) df
    rw [hb, bind_ok]
    split <;> exact ⟨_, rfl⟩
  · exact ⟨_, rfl⟩

end Plonky3Lean.Proofs.MerkleTree
