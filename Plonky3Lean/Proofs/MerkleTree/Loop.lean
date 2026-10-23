module

public import Plonky3Lean.Proofs.MerkleTree.Invert

@[expose] public section

/-!
# The verifier's main loop computes the fold of its plan

A run of the main loop that returns reaches the cap index and digest of the fold of the plan.

The plan depends only on the dimensions, the schedule, the matrix order and the starting width and position.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open p3_merkle_tree

namespace Plonky3Lean.Proofs.MerkleTree

variable {F W H C : Type} {N DIGEST_ELEMS : Std.Usize}

/-- The schedule entries from `level` on, as natural numbers. -/
def schedFrom (sched : alloc.vec.Vec Std.Usize) (level : ℕ) : List ℕ :=
  (sched.val.drop level).map fun s => s.val

theorem walk_ok (cl : core.clone.Clone F) (cp : core.marker.Copy W)
    (hInst : p3_symmetric.hasher.CryptographicHasher H F (Std.Array W DIGEST_ELEMS))
    (cInst : p3_symmetric.compression.PseudoCompressionFunction C (Std.Array W DIGEST_ELEMS) N)
    (t : H) (t1 : C) (h : List (List F) → Std.Array W DIGEST_ELEMS)
    (c : List (Std.Array W DIGEST_ELEMS) → Std.Array W DIGEST_ELEMS)
    (hH : HashOn hInst t h) (hC : CompressOn cInst t1 c)
    (dims : Slice p3_matrix.Dimensions) (opened : Slice (alloc.vec.Vec F))
    (proof : Slice (Std.Array W DIGEST_ELEMS)) (sched order : alloc.vec.Vec Std.Usize)
    (dflt : Std.Array W DIGEST_ELEMS) (padA : Std.Array (Std.Array W DIGEST_ELEMS) N)
    (hpad : core.array.repeat N (core.Array.Insts.CoreCloneClone DIGEST_ELEMS cp.cloneCloneInst) dflt =
      RustM.ok padA)
    (hord : ∀ i ∈ order.val, i.val < opened.val.length) :
    ∀ n (index curr pos : Std.Usize) (digest : Std.Array W DIGEST_ELEMS) (pp level ci : Std.Usize)
      (df : Std.Array W DIGEST_ELEMS),
      sched.val.length - level.val = n →
      mmcs.hax_reshaped.verify_batch_loop2 cl cp hInst cInst t t1 dims index opened proof sched order
        curr pos digest dflt pp level = RustM.ok (ci, df) →
      (ci.val, df) = walk h c padA.val dflt (ordL order) (openedL opened) proof.val
        (plan N.val (heightOf dims) (ordL order) (schedFrom sched level.val) curr.val pos.val)
        index.val pp.val digest := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro index curr pos digest pp level ci df hn hrun
  unfold mmcs.hax_reshaped.verify_batch_loop2 at hrun
  obtain ⟨r, hr, hrun⟩ := loop_ok hrun
  dsimp only at hr
  unfold mmcs.hax_reshaped.verify_batch_loop2.body at hr
  obtain ⟨l, hl, hr⟩ := bind_tc_eq_ok hr
  simp only [alloc.vec.Vec.len, rust_primitives.sequence.seq_len] at hl
  cases ok_inj hl
  split at hr
  · rename_i hlev
    have hlev' : level.val < sched.val.length := by simpa using hlev
    obtain ⟨step, hstep, hr⟩ := bind_tc_eq_ok hr
    obtain ⟨-, hstepv⟩ := vec_index_ok hstep
    obtain ⟨ns, hns, hr⟩ := bind_tc_eq_ok hr
    obtain ⟨hnsv, hstep1⟩ := usize_sub_ok hns
    obtain ⟨pg, hpg, hr⟩ := bind_tc_eq_ok hr
    obtain ⟨hpgv, hstep0⟩ := usize_rem_ok hpg
    obtain ⟨inputs, hinputs, hr⟩ := bind_tc_eq_ok hr
    obtain ⟨inputs1, hinputs1, hr⟩ := bind_tc_eq_ok hr
    obtain ⟨pp1, hpp1, hr⟩ := bind_tc_eq_ok hr
    obtain ⟨digest1, hdigest1, hr⟩ := bind_tc_eq_ok hr
    obtain ⟨index1, hindex1, hr⟩ := bind_tc_eq_ok hr
    obtain ⟨ln, hln, hr⟩ := bind_tc_eq_ok hr
    obtain ⟨curr1, hcurr1, hr⟩ := bind_tc_eq_ok hr
    obtain ⟨lnpt, hlnpt, hr⟩ := bind_tc_eq_ok hr
    obtain ⟨l2, hl2, hr⟩ := bind_tc_eq_ok hr
    simp only [alloc.vec.Vec.len, rust_primitives.sequence.seq_len] at hl2
    cases ok_inj hl2
    -- What one level computes before the injection.
    have hpad' : inputs = padA := ok_inj (hinputs.symm.trans hpad)
    subst hpad'
    have hpgs : pg.val < step.val := by rw [hpgv]; exact Nat.mod_lt _ (by omega)
    have hin := children_ok proof digest pp step pg hpgs dflt _ inputs 0#usize 0#usize inputs1 rfl
      (by simp) (by simp [sibCount]) hinputs1
    have hd1 : digest1 = c (children inputs.val step.val (index.val % step.val) digest proof.val
        pp.val dflt) := by
      rw [hC] at hdigest1
      rw [← ok_inj hdigest1, hin, children, ← hpgv]
      congr 1
      simp
    have hidx1 : index1.val = index.val / step.val := (usize_div_ok hindex1).1
    have hlnv : ln.val = curr.val / step.val := (usize_div_ok hln).1
    have hcurr1v : curr1.val = padded (curr.val / step.val) N.val := by
      rw [padded_len_ok hcurr1, hlnv]
    have hlnptv : lnpt.val = npt (curr.val / step.val) := by rw [(npt_ok hlnpt).1, hlnv]
    have hpp1v : pp1.val = pp.val + (step.val - 1) := by rw [usize_add_ok hpp1, hnsv]; rfl
    have hsched : schedFrom sched level.val = step.val :: schedFrom sched (level.val + 1) := by
      simp only [schedFrom]
      rw [List.drop_eq_getElem_cons hlev']
      simp only [List.map_cons]
      congr 1
      rw [List.getElem?_eq_getElem hlev'] at hstepv
      simp only [Option.some.injEq] at hstepv
      rw [hstepv]
    rw [hsched]
    simp only [plan]
    have hrec : ∀ (pos' : Std.Usize) (d' : Std.Array W DIGEST_ELEMS) (level1 : Std.Usize),
        level + 1#usize = RustM.ok level1 →
        mmcs.hax_reshaped.verify_batch_loop2 cl cp hInst cInst t t1 dims index1 opened proof sched
          order curr1 pos' d' dflt pp1 level1 = RustM.ok (ci, df) →
        (ci.val, df) = walk h c inputs.val dflt (ordL order) (openedL opened) proof.val
          (plan N.val (heightOf dims) (ordL order) (schedFrom sched (level.val + 1))
            (padded (curr.val / step.val) N.val) pos'.val)
          (index.val / step.val) (pp.val + (step.val - 1)) d' := by
      intro pos' d' level1 hlevel1 hrun'
      have hl1 : level1.val = level.val + 1 := usize_succ_ok hlevel1
      have := ih _ (by omega) index1 curr1 pos' d' pp1 level1 ci df rfl hrun'
      rw [this, hl1, hcurr1v, hidx1, hpp1v]
    split at hr
    · rename_i hposlt
      have hposlt' : pos.val < order.val.length := by simpa using hposlt
      obtain ⟨i2, hi2, hr⟩ := bind_tc_eq_ok hr
      obtain ⟨-, hi2v⟩ := vec_index_ok hi2
      obtain ⟨d, hd, hr⟩ := bind_tc_eq_ok hr
      obtain ⟨-, hdv⟩ := slice_index_ok hd
      obtain ⟨i3, hi3, hr⟩ := bind_tc_eq_ok hr
      have hi3v := (npt_ok hi3).1
      split at hr
      · rename_i heq
        have hcond : pos.val < (ordL order).length ∧
            npt (heightOf dims ((ordL order).getD pos.val 0)) = npt (curr.val / step.val) := by
          refine ⟨by rw [ordL_length]; exact hposlt', ?_⟩
          rw [ordL_getD hi2v, heightOf_eq hdv, ← hi3v, ← hlnptv, heq]
        rw [ite_eq_left hcond]
        obtain ⟨pos1, hpos1, hr⟩ := bind_tc_eq_ok hr
        have hpos1v := advance_ok dims order d.height _ pos pos1 rfl hpos1
        obtain ⟨sl, hsl, hr⟩ := bind_tc_eq_ok hr
        have hslv : sl = vs order := (ok_inj hsl).symm
        obtain ⟨nh, hnh, hr⟩ := bind_tc_eq_ok hr
        rw [hslv] at hnh
        have hp1le : pos1.val ≤ order.val.length := by
          rw [hpos1v]
          have := advance_le (heightOf dims) (ordL order) d.height.val pos.val
            (by rw [ordL_length]; omega)
          rwa [ordL_length] at this
        have hnhv : nh = h (group (ordL order) (openedL opened) pos.val pos1.val) := by
          rw [hH _ _ (rowsList opened (vs order) pos.val pos1.val)
            ⟨_, rfl, rows_yields opened (vs order) (by rw [vs_val]; exact hord) _ pos pos1 rfl
              (by rw [vs_val]; exact hp1le)⟩] at hnh
          rw [← ok_inj hnh, rowsList_val opened order hord]
        obtain ⟨inj, hinj, hr⟩ := bind_tc_eq_ok hr
        have hinjv : inj = inputs := ok_inj (hinj.symm.trans hinputs)
        obtain ⟨inj1, hinj1, hr⟩ := bind_tc_eq_ok hr
        obtain ⟨inj2, hinj2, hr⟩ := bind_tc_eq_ok hr
        obtain ⟨digest2, hdigest2, hr⟩ := bind_tc_eq_ok hr
        obtain ⟨level1, hlevel1, hr⟩ := bind_tc_eq_ok hr
        cases ok_inj hr
        simp only at hrun
        have hd2 : digest2 = c ((inputs.val.set 0 digest1).set 1 nh) := by
          rw [hC] at hdigest2
          rw [← ok_inj hdigest2, (array_update_ok hinj2).1, (array_update_ok hinj1).1, hinjv]
          rfl
        simp only [walk]
        rw [ordL_getD hi2v, heightOf_eq hdv, ← hpos1v, ← hd1, ← hnhv, ← hd2]
        exact hrec pos1 digest2 level1 hlevel1
          (by unfold mmcs.hax_reshaped.verify_batch_loop2; exact hrun)
      · rename_i hne
        have hcond : ¬ (pos.val < (ordL order).length ∧
            npt (heightOf dims ((ordL order).getD pos.val 0)) = npt (curr.val / step.val)) := by
          rintro ⟨-, h2⟩
          apply hne
          apply UScalar.eq_of_val_eq
          rw [hi3v, hlnptv, ← h2, ordL_getD hi2v, heightOf_eq hdv]
        rw [ite_eq_right hcond]
        obtain ⟨level1, hlevel1, hr⟩ := bind_tc_eq_ok hr
        cases ok_inj hr
        simp only at hrun
        simp only [walk]
        rw [← hd1]
        exact hrec pos digest1 level1 hlevel1 (by unfold mmcs.hax_reshaped.verify_batch_loop2; exact hrun)
    · rename_i hposlt
      have hposlt' : ¬ pos.val < order.val.length := by simpa using hposlt
      have hcond : ¬ (pos.val < (ordL order).length ∧
          npt (heightOf dims ((ordL order).getD pos.val 0)) = npt (curr.val / step.val)) := by
        rintro ⟨h1, -⟩
        rw [ordL_length] at h1
        exact hposlt' h1
      rw [ite_eq_right hcond]
      obtain ⟨level1, hlevel1, hr⟩ := bind_tc_eq_ok hr
      cases ok_inj hr
      simp only at hrun
      simp only [walk]
      rw [← hd1]
      exact hrec pos digest1 level1 hlevel1 (by unfold mmcs.hax_reshaped.verify_batch_loop2; exact hrun)
  · rename_i hlev
    have hlev' : ¬ level.val < sched.val.length := by simpa using hlev
    cases ok_inj hr
    simp only at hrun
    cases hrun
    have : schedFrom sched level.val = [] := by
      simp [schedFrom]; omega
    rw [this]
    rfl

end Plonky3Lean.Proofs.MerkleTree
