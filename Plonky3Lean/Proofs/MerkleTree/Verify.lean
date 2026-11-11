module

public import Plonky3Lean.Proofs.MerkleTree.Loop
public import Plonky3Lean.Proofs.MerkleTree.Geometry
public import Plonky3Lean.Proofs.MerkleTree.Binding

@[expose] public section

/-!
# An accepting run of the single-index verifier

A run that accepts:

- checked every row's width
- hashed the leaf rows
- folded its plan
- found the result in the cap.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open p3_merkle_tree

namespace Plonky3Lean.Proofs.MerkleTree

/-- A width check that passes saw one row per matrix, each as wide as its matrix. -/
theorem check_widths_ok {T : Type} {dims : Slice p3_matrix.Dimensions}
    {opened : Slice (alloc.vec.Vec T)}
    (h : mmcs.hax_reshaped.check_widths dims opened = RustM.ok (core.result.Result.Ok ())) :
    opened.val.length = dims.val.length ∧
      ∀ m (hm : m < dims.val.length) (hm' : m < opened.val.length),
        (opened.val[m]).val.length = (dims.val[m]).width.val := by
  unfold mmcs.hax_reshaped.check_widths at h
  obtain ⟨l1, hl1, h⟩ := bind_tc_eq_ok h
  obtain ⟨l2, hl2, h⟩ := bind_tc_eq_ok h
  simp only [core.slice.Slice.len] at hl1 hl2
  cases ok_inj hl1
  cases ok_inj hl2
  split at h
  · cases ok_inj h
  · rename_i heq
    have hlen : opened.val.length = dims.val.length := by simpa using heq
    refine ⟨hlen, ?_⟩
    unfold mmcs.hax_reshaped.check_widths_loop at h
    have key := loop_inv _
      (fun k : Std.Usize => ∀ m (hm : m < k.val) (hm' : m < dims.val.length)
        (hm'' : m < opened.val.length),
        (opened.val[m]).val.length = (dims.val[m]).width.val)
      (fun v => v = core.result.Result.Ok () →
        ∀ m (hm : m < dims.val.length) (hm' : m < opened.val.length),
          (opened.val[m]).val.length = (dims.val[m]).width.val)
      (by
        intro k hinv r hr
        unfold mmcs.hax_reshaped.check_widths_loop.body at hr
        obtain ⟨l, hl, hr⟩ := bind_tc_eq_ok hr
        simp only [core.slice.Slice.len] at hl
        cases ok_inj hl
        split at hr
        · rename_i hlt
          have hlt' : k.val < dims.val.length := by simpa using hlt
          obtain ⟨v, hv, hr⟩ := bind_tc_eq_ok hr
          obtain ⟨w, hw, hr⟩ := bind_tc_eq_ok hr
          obtain ⟨d, hd, hr⟩ := bind_tc_eq_ok hr
          obtain ⟨-, hvv⟩ := slice_index_ok hv
          obtain ⟨-, hdv⟩ := slice_index_ok hd
          simp only [alloc.vec.Vec.len, rust_primitives.sequence.seq_len] at hw
          cases ok_inj hw
          split at hr
          · cases ok_inj hr
            intro h0
            cases h0
          · rename_i hne
            obtain ⟨k1, hk1, hr⟩ := bind_tc_eq_ok hr
            cases ok_inj hr
            have hk1v : k1.val = k.val + 1 := usize_succ_ok hk1
            intro m hm hm' hm''
            by_cases hmk : m < k.val
            · exact hinv m hmk hm' hm''
            · have : m = k.val := by omega
              subst this
              rw [List.getElem?_eq_getElem hm''] at hvv
              rw [List.getElem?_eq_getElem hm'] at hdv
              rw [Option.some.inj hvv, Option.some.inj hdv]
              simpa using hne
        · rename_i hlt
          have hlt' : ¬ k.val < dims.val.length := by simpa using hlt
          cases ok_inj hr
          intro _ m hm hm'
          exact hinv m (by omega) hm hm')
      _ _ h (by intro m hm; simp at hm)
    exact key rfl

/-- Two arrays that compare equal, with an equality that only says true of equal elements, are equal. -/
theorem array_eq_true {T : Type} {N : Std.Usize} (inst : core.cmp.PartialEq T T)
    (hinst : ∀ x y, inst.eq x y = RustM.ok true → x = y) {a b : Std.Array T N}
    (h : core.Array.Insts.CoreCmpPartialEqArray.eq inst a b = RustM.ok true) : a = b := by
  unfold core.Array.Insts.CoreCmpPartialEqArray.eq core.Array.Insts.CoreCmpPartialEqArray.eq_loop at h
  have key := loop_inv _
    (fun i : Std.Usize => ∀ j < i.val, a.val[j]? = b.val[j]?)
    (fun v => v = true → a = b)
    (by
      intro i hinv r hr
      unfold core.Array.Insts.CoreCmpPartialEqArray.eq_loop.body at hr
      split at hr
      · rename_i hlt
        have hlt' : i.val < N.val := hlt
        obtain ⟨x, hx, hr⟩ := bind_tc_eq_ok hr
        obtain ⟨y, hy, hr⟩ := bind_tc_eq_ok hr
        obtain ⟨bb, hbb, hr⟩ := bind_tc_eq_ok hr
        obtain ⟨-, hxv⟩ := slice_index_ok hx
        obtain ⟨-, hyv⟩ := slice_index_ok hy
        split at hr
        · rename_i hb
          obtain ⟨i1, hi1, hr⟩ := bind_tc_eq_ok hr
          cases ok_inj hr
          have hi1v : i1.val = i.val + 1 := usize_succ_ok hi1
          intro j hj
          by_cases hji : j < i.val
          · exact hinv j hji
          · have : j = i.val := by omega
            subst this
            have hxy : x = y := hinst x y (by rw [hbb, hb])
            simp only [Std.Array.to_slice, Slice.from_val] at hxv hyv
            rw [hxv, hyv, hxy]
        · cases ok_inj hr
          intro h0; cases h0
      · rename_i hlt
        have hlt' : ¬ i.val < N.val := hlt
        cases ok_inj hr
        intro _
        apply Std.Array.ext
        apply List.ext_getElem?
        intro j
        by_cases hj : j < N.val
        · exact hinv j (by omega)
        · rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by simp; omega)])
    _ _ h (by intro j hj; simp at hj)
  exact key rfl

theorem leaf_pos_le {dims : Slice p3_matrix.Dimensions} {order : alloc.vec.Vec Std.Usize}
    {lnpt pos : Std.Usize}
    (h : mmcs.hax_reshaped.verify_batch_loop1 dims order lnpt 0#usize = RustM.ok pos) :
    pos.val ≤ order.val.length := by
  unfold mmcs.hax_reshaped.verify_batch_loop1 at h
  refine loop_inv _ (fun p : Std.Usize => p.val ≤ order.val.length)
    (fun p : Std.Usize => p.val ≤ order.val.length) ?_ _ _ h (by simp)
  intro p hp r hr
  unfold mmcs.hax_reshaped.verify_batch_loop1.body at hr
  obtain ⟨l, hl, hr⟩ := bind_tc_eq_ok hr
  simp only [alloc.vec.Vec.len, rust_primitives.sequence.seq_len] at hl
  cases ok_inj hl
  split at hr
  · rename_i hlt
    have hlt' : p.val < order.val.length := by simpa using hlt
    obtain ⟨i1, _hi1, hr⟩ := bind_tc_eq_ok hr
    obtain ⟨d, _hd, hr⟩ := bind_tc_eq_ok hr
    obtain ⟨i2, _hi2, hr⟩ := bind_tc_eq_ok hr
    split at hr
    · obtain ⟨p1, hp1, hr⟩ := bind_tc_eq_ok hr
      cases ok_inj hr
      have : p1.val = p.val + 1 := by simpa using usize_add_ok hp1
      show p1.val ≤ _
      omega
    · cases ok_inj hr; exact hp
  · cases ok_inj hr; exact hp

variable {P PW F W H C : Type} {N DIGEST_ELEMS : Std.Usize}

/-- What an accepting run of the verifier did.

Most values named here are computed from the dimensions, the arity and the cap height alone.

The exceptions are the leaf digest, the final digest and the width facts. -/
theorem verify_accepts (cl : core.clone.Clone F) (cp : core.marker.Copy W)
    (dfInst : core.default.Default W) (eqInst : core.cmp.PartialEq W W)
    (hInst : p3_symmetric.hasher.CryptographicHasher H F (Std.Array W DIGEST_ELEMS))
    (cInst : p3_symmetric.compression.PseudoCompressionFunction C (Std.Array W DIGEST_ELEMS) N)
    (mt : mmcs.MerkleTreeMmcs P PW H C N DIGEST_ELEMS)
    (commit : p3_symmetric.hash.MerkleCap F (Std.Array W DIGEST_ELEMS))
    (dims : Slice p3_matrix.Dimensions) (index : Std.Usize) (opened : Slice (alloc.vec.Vec F))
    (proof : Slice (Std.Array W DIGEST_ELEMS))
    (h : mmcs.hax_reshaped.verify_batch cl cp dfInst eqInst hInst cInst mt commit dims index opened
      proof = RustM.ok (core.result.Result.Ok ())) :
    ∃ (val : Std.Usize) (sched : alloc.vec.Vec Std.Usize) (pl : Std.Usize)
      (sched1 order : alloc.vec.Vec Std.Usize) (curr lnpt pos : Std.Usize) (t : W)
      (dflt : Std.Array W DIGEST_ELEMS) (d0 : Std.Array W DIGEST_ELEMS) (ci : Std.Usize)
      (df : Std.Array W DIGEST_ELEMS) (a : Std.Array W DIGEST_ELEMS),
      mmcs.hax_reshaped.validate_heights dims = RustM.ok (core.result.Result.Ok val) ∧
      mmcs.hax_reshaped.arity_schedule_and_proof_levels N mt.cap_height dims =
        RustM.ok (core.result.Result.Ok (sched, pl)) ∧
      alloc.vec.Vec.truncate sched pl = RustM.ok sched1 ∧
      mmcs.hax_reshaped.check_widths dims opened = RustM.ok (core.result.Result.Ok ()) ∧
      mmcs.hax_reshaped.tallest_first dims = RustM.ok order ∧
      p3_merkle_tree.merkle_tree.padded_len val N = RustM.ok curr ∧
      index.val < val.val ∧
      core.num.Usize.next_power_of_two val = RustM.ok lnpt ∧
      mmcs.hax_reshaped.verify_batch_loop1 dims order lnpt 0#usize = RustM.ok pos ∧
      hInst.hash_iter_slices
        (core.iter.traits.collect.IntoIterator.Blanket
          (mmcs.hax_reshaped.Rows.Insts.CoreIterTraitsIteratorIteratorSharedASlice F))
        mt.hash { opened_values := opened, order := vs order, pos := 0#usize, «end» := pos } =
        RustM.ok d0 ∧
      dfInst.default = RustM.ok t ∧
      core.array.repeat DIGEST_ELEMS cp.cloneCloneInst t = RustM.ok dflt ∧
      mmcs.hax_reshaped.verify_batch_loop2 cl cp hInst cInst mt.hash mt.compress dims index opened
        proof sched1 order curr pos d0 dflt 0#usize 0#usize = RustM.ok (ci, df) ∧
      p3_symmetric.hash.MerkleCap.Insts.CoreOpsIndexIndexUsizeDigest.index commit ci = RustM.ok a ∧
      core.Array.Insts.CoreCmpPartialEqArray.eq eqInst a df = RustM.ok true ∧
      ∃ epl : Std.Usize, mmcs.hax_reshaped.verify_batch_loop0 sched1 0#usize 0#usize = RustM.ok epl ∧
        proof.val.length = epl.val := by
  unfold mmcs.hax_reshaped.verify_batch at h
  obtain ⟨l1, hl1, g1⟩ := bind_tc_eq_ok h
  obtain ⟨l2, hl2, g2⟩ := bind_tc_eq_ok g1
  split at g2
  · cases ok_inj g2
  obtain ⟨r, hr, g3⟩ := bind_tc_eq_ok g2
  obtain ⟨cf, hcf, g4⟩ := bind_tc_eq_ok g3
  cases cf with
  | Break res => exact (from_residual_ne_ok _ _ g4).elim
  | Continue val =>
  dsimp only at g4
  have hrv := branch_continue hcf
  subst hrv
  obtain ⟨r1, hr1, g5⟩ := bind_tc_eq_ok g4
  obtain ⟨cf1, hcf1, g6⟩ := bind_tc_eq_ok g5
  cases cf1 with
  | Break res => exact (from_residual_ne_ok _ _ g6).elim
  | Continue u =>
  dsimp only at g6
  obtain ⟨r2, hr2, g7⟩ := bind_tc_eq_ok g6
  obtain ⟨cf2, hcf2, g8⟩ := bind_tc_eq_ok g7
  cases cf2 with
  | Break res => exact (from_residual_ne_ok _ _ g8).elim
  | Continue sp =>
  obtain ⟨sched, pl⟩ := sp
  dsimp only at g8
  have hr2v := branch_continue hcf2
  subst hr2v
  obtain ⟨sched1, hsched1, g9⟩ := bind_tc_eq_ok g8
  obtain ⟨epl, hepl, g10⟩ := bind_tc_eq_ok g9
  obtain ⟨l3, hl3, g11⟩ := bind_tc_eq_ok g10
  simp only [core.slice.Slice.len] at hl3
  cases ok_inj hl3
  split at g11
  · cases ok_inj g11
  rename_i hplen
  have hplen' : proof.val.length = epl.val := by simpa using hplen
  obtain ⟨r3, hr3, g12⟩ := bind_tc_eq_ok g11
  obtain ⟨cf3, hcf3, g13⟩ := bind_tc_eq_ok g12
  cases cf3 with
  | Break res => exact (from_residual_ne_ok _ _ g13).elim
  | Continue u3 =>
  dsimp only at g13
  have hr3v := branch_continue hcf3
  subst hr3v
  obtain ⟨order, horder, g14⟩ := bind_tc_eq_ok g13
  obtain ⟨curr, hcurr, g15⟩ := bind_tc_eq_ok g14
  split at g15
  · cases ok_inj g15
  rename_i hidx
  obtain ⟨lnpt, hlnpt, g16⟩ := bind_tc_eq_ok g15
  obtain ⟨pos, hpos, g17⟩ := bind_tc_eq_ok g16
  obtain ⟨sl, hsl, g18⟩ := bind_tc_eq_ok g17
  have hslv : sl = vs order := (ok_inj hsl).symm
  obtain ⟨d0, hd0, g19⟩ := bind_tc_eq_ok g18
  rw [hslv] at hd0
  obtain ⟨t, ht, g20⟩ := bind_tc_eq_ok g19
  obtain ⟨dflt, hdflt, g21⟩ := bind_tc_eq_ok g20
  obtain ⟨cd, hcd, g22⟩ := bind_tc_eq_ok g21
  obtain ⟨ci, df⟩ := cd
  obtain ⟨nr, hnr, g23⟩ := bind_tc_eq_ok g22
  split at g23
  · obtain ⟨a, ha, g24a⟩ := bind_tc_eq_ok g23
    obtain ⟨b, hb, g24⟩ := bind_tc_eq_ok g24a
    split at g24
    · rename_i hbt
      refine ⟨val, sched, pl, sched1, order, curr, lnpt, pos, t, dflt, d0, ci, df, a, hr, hr2,
        hsched1, hr3, horder, hcurr, ?_, hlnpt, hpos, hd0, ht, hdflt, hcd, ha, by rw [hb, hbt],
        epl, hepl, hplen'⟩
      have : ¬ index.val ≥ val.val := hidx
      omega
    · cases ok_inj g24
  · cases ok_inj g23

end Plonky3Lean.Proofs.MerkleTree
