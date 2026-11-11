module

public import Plonky3Lean.Proofs.MerkleTree.Verify
public import Plonky3Lean.Proofs.MerkleTree.Forward
public import Plonky3Lean.Proofs.MerkleTree.Loop

@[expose] public section

/-!
# The verifier's loops always return

The prover controls the index, the opened rows, the siblings and the cap.

None of them can make the main loop panic or run forever.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open p3_merkle_tree

namespace Plonky3Lean.Proofs.MerkleTree

theorem vec_index_eq {α : Type} (v : alloc.vec.Vec α) (i : Std.Usize) (h : i.val < v.val.length) :
    alloc.vec.Vec.Insts.CoreOpsIndexIndex.index
      (core.Usize.Insts.CoreSliceIndexSliceIndexSliceT α) v i = RustM.ok (v.val[i.val]) := by
  simp only [alloc.vec.Vec.Insts.CoreOpsIndexIndex.index,
    alloc.vec.Vec.Insts.CoreOpsDerefDerefSlice.deref, alloc.vec.Vec.as_slice,
    rust_primitives.sequence.seq_to_slice, core.Slice.Insts.CoreOpsIndexIndex.index,
    core.Usize.Insts.CoreSliceIndexSliceIndexSliceT.get, rust_primitives.slice.slice_length,
    rust_primitives.slice.slice_index]
  erw [bind_ok, bind_ok, ite_eq_left (show i < Slice.len v by simpa using h), Lib.slice_index_eq (vs v) i h,
    bind_ok, bind_ok]
  rfl

theorem children_total {W : Type} {N DIGEST_ELEMS : Std.Usize}
    (proof : Slice (Std.Array W DIGEST_ELEMS)) (d : Std.Array W DIGEST_ELEMS) (pp s pg : Std.Usize)
    (hpg : pg.val < s.val) (hlen : pp.val + (s.val - 1) ≤ proof.val.length)
    (inputs : Std.Array (Std.Array W DIGEST_ELEMS) N) :
    ∃ out, mmcs.hax_reshaped.verify_batch_loop2_loop0 proof d pp s pg inputs 0#usize 0#usize =
      RustM.ok out := by
  unfold mmcs.hax_reshaped.verify_batch_loop2_loop0
  refine loop_total _
    (fun x : Std.Array (Std.Array W DIGEST_ELEMS) N × Std.Usize × Std.Usize =>
      x.2.2.val ≤ N.val ∧ x.2.1.val = sibCount s.val pg.val x.2.2.val)
    (fun x => N.val - x.2.2.val) ?_ _ ⟨by simp, by simp [sibCount]⟩
  rintro ⟨inp, sib, k⟩ ⟨hk, hsib⟩
  dsimp only at hk hsib ⊢
  unfold mmcs.hax_reshaped.verify_batch_loop2_loop0.body
  by_cases hkN : k.val < N.val
  · rw [ite_eq_left (show k < N from hkN)]
    have hNmax : N.val ≤ Usize.max := by scalar_tac
    obtain ⟨k1, hk1, hk1v0⟩ := usize_add_eq (x := k) (y := 1#usize) (by simp; omega)
    have hk1v : k1.val = k.val + 1 := by simpa using hk1v0
    have hlenN : k.val < inp.val.length := by simp; omega
    by_cases hks : k.val < s.val
    · rw [ite_eq_left (show k < s from hks)]
      by_cases hkp : k = pg
      · rw [ite_eq_left hkp, Lib.update_eq inp k d hlenN, bind_ok, bind_ok]
        rw [hk1]
        simp only [bind_ok]
        refine ⟨_, rfl, ⟨by dsimp only; omega, ?_⟩, by dsimp only; omega⟩
        dsimp only
        have hkp' : k.val = pg.val := by rw [hkp]
        simp only [sibCount] at hsib ⊢
        rw [hk1v, Nat.min_eq_left (by omega), hsib, Nat.min_eq_left (by omega)]
        split_ifs <;> omega
      · have hkp' : k.val ≠ pg.val := fun e => hkp (UScalar.eq_of_val_eq e)
        rw [ite_eq_right hkp]
        have hsibv : sib.val = if k.val < pg.val then k.val else k.val - 1 := by
          rw [hsib, sibCount, Nat.min_eq_left (by omega)]
          split_ifs <;> omega
        have hpmax : proof.val.length ≤ Usize.max := by scalar_tac
        have hin : pp.val + sib.val < proof.val.length := by
          rw [hsibv]; split_ifs <;> omega
        obtain ⟨i, hi, hiv⟩ := usize_add_eq (x := pp) (y := sib) (by omega)
        obtain ⟨sib2, hsib2, hsib2v⟩ := usize_add_eq (x := sib) (y := 1#usize) (by simp; omega)
        rw [hi, bind_ok, Lib.slice_index_eq proof i (by omega), bind_ok,
          Lib.update_eq inp k _ hlenN, bind_ok, hsib2, bind_ok, bind_ok]
        rw [hk1]
        simp only [bind_ok]
        refine ⟨_, rfl, ⟨by dsimp only; omega, ?_⟩, by dsimp only; omega⟩
        dsimp only
        have hsib2v' : sib2.val = sib.val + 1 := by simpa using hsib2v
        simp only [sibCount]
        rw [hk1v, hsib2v', Nat.min_eq_left (by omega), hsibv]
        split_ifs <;> omega
    · rw [ite_eq_right (show ¬ k < s from hks), bind_ok]
      rw [hk1]
      simp only [bind_ok]
      refine ⟨_, rfl, ⟨by dsimp only; omega, ?_⟩, by dsimp only; omega⟩
      dsimp only
      simp only [sibCount] at hsib ⊢
      rw [hk1v, Nat.min_eq_right (by omega), hsib, Nat.min_eq_right (by omega)]
  · rw [ite_eq_right (show ¬ k < N from hkN)]
    exact ⟨_, rfl, trivial⟩

theorem advance_total (dims : Slice p3_matrix.Dimensions) (order : alloc.vec.Vec Std.Usize)
    (nh : Std.Usize) (hord : ∀ i ∈ order.val, i.val < dims.val.length) (pos : Std.Usize)
    (hpos : pos.val ≤ order.val.length) :
    ∃ p1, mmcs.hax_reshaped.verify_batch_loop2_loop1 dims order pos nh = RustM.ok p1 := by
  unfold mmcs.hax_reshaped.verify_batch_loop2_loop1
  refine loop_total _ (fun p : Std.Usize => p.val ≤ order.val.length)
    (fun p => order.val.length - p.val) ?_ _ hpos
  intro p hp
  unfold mmcs.hax_reshaped.verify_batch_loop2_loop1.body
  simp only [alloc.vec.Vec.len, rust_primitives.sequence.seq_len, bind_ok]
  by_cases hlt : p.val < order.val.length
  · rw [ite_eq_left (show p < Slice.len order by simpa using hlt), vec_index_eq order p hlt, bind_ok,
      Lib.slice_index_eq dims _ (hord _ (List.getElem_mem hlt)), bind_ok]
    split
    · have hmax : order.val.length ≤ Usize.max := by scalar_tac
      obtain ⟨p1, hp1, hp1v⟩ := usize_add_eq (x := p) (y := 1#usize) (by simp; omega)
      have hp1v' : p1.val = p.val + 1 := by simpa using hp1v
      rw [hp1, bind_ok]
      exact ⟨_, rfl, by omega, by omega⟩
    · exact ⟨_, rfl, trivial⟩
  · rw [ite_eq_right (show ¬ p < Slice.len order by simpa using hlt)]
    exact ⟨_, rfl, trivial⟩

/-- Siblings the levels from `level` on take. -/
def sibSum (sched : alloc.vec.Vec Std.Usize) (level : ℕ) : ℕ :=
  ((sched.val.drop level).map fun s => s.val - 1).sum

theorem sibSum_succ (sched : alloc.vec.Vec Std.Usize) (level : ℕ) (h : level < sched.val.length) :
    sibSum sched level = ((sched.val[level]).val - 1) + sibSum sched (level + 1) := by
  simp only [sibSum]
  rw [List.drop_eq_getElem_cons h, List.map_cons, List.sum_cons]

theorem half_le_max (x : Std.Usize) : x.val / 2 ≤ Usize.max / 2 := by
  have : x.val ≤ Usize.max := by scalar_tac
  omega

theorem half_le_pow (x : Std.Usize) : x.val / 2 ≤ 2 ^ (UScalarTy.Usize.numBits - 1) := by
  have := usize_max_half (x := x)
  omega

theorem loop2_total {F W H C : Type} {N DIGEST_ELEMS : Std.Usize}
    (cl : core.clone.Clone F) (cp : core.marker.Copy W)
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
    (hN : 2 ≤ N.val) (hsteps : ∀ s ∈ sched.val, s.val = 2 ∨ s = N)
    (hordD : ∀ i ∈ order.val, i.val < dims.val.length)
    (hordO : ∀ i ∈ order.val, i.val < opened.val.length)
    (hnpt : ∀ d ∈ dims.val, d.height.val ≤ 2 ^ (UScalarTy.Usize.numBits - 1)) :
    ∀ (index curr pos : Std.Usize) (digest : Std.Array W DIGEST_ELEMS) (pp level : Std.Usize),
      pos.val ≤ order.val.length → level.val ≤ sched.val.length →
      pp.val + sibSum sched level.val = proof.val.length →
      ∃ r, mmcs.hax_reshaped.verify_batch_loop2 cl cp hInst cInst t t1 dims index opened proof sched
        order curr pos digest dflt pp level = RustM.ok r := by
  intro index curr pos digest pp level hpos hlev hpp
  unfold mmcs.hax_reshaped.verify_batch_loop2
  refine loop_total _
    (fun x : Std.Usize × Std.Usize × Std.Usize × Std.Array W DIGEST_ELEMS × Std.Usize × Std.Usize =>
      x.2.2.1.val ≤ order.val.length ∧ x.2.2.2.2.2.val ≤ sched.val.length ∧
      x.2.2.2.2.1.val + sibSum sched x.2.2.2.2.2.val = proof.val.length)
    (fun x => sched.val.length - x.2.2.2.2.2.val) ?_ _ ⟨hpos, hlev, hpp⟩
  rintro ⟨index, curr, pos, digest, pp, level⟩ ⟨hpos, hlev, hpp⟩
  dsimp only at hpos hlev hpp ⊢
  unfold mmcs.hax_reshaped.verify_batch_loop2.body
  simp only [alloc.vec.Vec.len, rust_primitives.sequence.seq_len, bind_ok]
  by_cases hl : level.val < sched.val.length
  swap
  · rw [ite_eq_right (show ¬ level < Slice.len sched by simpa using hl)]
    exact ⟨_, rfl, trivial⟩
  rw [ite_eq_left (show level < Slice.len sched by simpa using hl), vec_index_eq sched level hl, bind_ok]
  set step := sched.val[level.val]
  have hst : step.val = 2 ∨ step = N := hsteps step (List.getElem_mem hl)
  have hs2 : 2 ≤ step.val := by rcases hst with h2 | h2 <;> [omega; (rw [h2]; omega)]
  have hsN : step.val ≤ N.val := by rcases hst with h2 | h2 <;> [omega; rw [h2]]
  have hss : sibSum sched level.val = (step.val - 1) + sibSum sched (level.val + 1) :=
    sibSum_succ sched level.val hl
  have hkey : pp.val + (step.val - 1) + sibSum sched (level.val + 1) = proof.val.length := by
    rw [← hpp, hss]; omega
  have hpmax : proof.val.length ≤ Usize.max := by scalar_tac
  have hsmax : sched.val.length ≤ Usize.max := by scalar_tac
  have h1 : (1#usize : Std.Usize).val = 1 := by simp
  obtain ⟨ns, hns, hnsv⟩ := usize_sub_eq (x := step) (y := 1#usize) (by omega)
  obtain ⟨pg, hpg, hpgv⟩ := usize_rem_eq (x := index) (y := step) (by omega)
  have hpgs : pg.val < step.val := by rw [hpgv]; exact Nat.mod_lt _ (by omega)
  obtain ⟨inputs1, hinputs1⟩ := children_total proof digest pp step pg hpgs (by omega) padA
  have hnsv' : ns.val = step.val - 1 := by rw [hnsv, h1]
  obtain ⟨pp1, hpp1, hpp1v⟩ := usize_add_eq (x := pp) (y := ns) (by omega)
  obtain ⟨index1, hindex1, -⟩ := usize_div_eq (x := index) (y := step) (by omega)
  obtain ⟨ln, hln, hlnv⟩ := usize_div_eq (x := curr) (y := step) (by omega)
  have hlnle : ln.val ≤ curr.val / 2 := by rw [hlnv]; exact Nat.div_le_div_left hs2 (by norm_num)
  obtain ⟨curr1, hcurr1⟩ := padded_total (x := ln) (N := N)
    (le_trans hlnle (half_le_max curr)) hN
  obtain ⟨lnpt, hlnpt, -⟩ := npt_eq (x := ln) (le_trans hlnle (half_le_pow curr))
  obtain ⟨level1, hlevel1, hlevel1v⟩ := usize_add_eq (x := level) (y := 1#usize) (by omega)
  have hl1 : level1.val = level.val + 1 := by rw [hlevel1v, h1]
  rw [hns, bind_ok, hpg, bind_ok, hpad, bind_ok, hinputs1, bind_ok, hpp1, bind_ok, hC, bind_ok,
    hindex1, bind_ok, hln, bind_ok, hcurr1, bind_ok, hlnpt, bind_ok]
  have hinv : ∀ p' : Std.Usize, p'.val ≤ order.val.length →
      (p'.val ≤ order.val.length ∧ level1.val ≤ sched.val.length ∧
        pp1.val + sibSum sched level1.val = proof.val.length) ∧
      sched.val.length - level1.val < sched.val.length - level.val := by
    intro p' hp'
    refine ⟨⟨hp', by omega, ?_⟩, by omega⟩
    rw [hpp1v, hl1, hnsv']
    omega
  by_cases hp : pos.val < order.val.length
  swap
  · rw [ite_eq_right (show ¬ pos < Slice.len order by simpa using hp), hlevel1, bind_ok]
    exact ⟨_, rfl, hinv pos hpos⟩
  rw [ite_eq_left (show pos < Slice.len order by simpa using hp), vec_index_eq order pos hp, bind_ok]
  have hi2 := hordD _ (List.getElem_mem hp)
  rw [Lib.slice_index_eq dims _ hi2, bind_ok]
  obtain ⟨i3, hi3, -⟩ := npt_eq (hnpt _ (List.getElem_mem hi2))
  rw [hi3, bind_ok]
  split
  · obtain ⟨pos1, hpos1⟩ := advance_total dims order _ hordD pos hpos
    have hp1le : pos1.val ≤ order.val.length := by
      rw [advance_ok dims order _ _ pos pos1 rfl hpos1, ← ordL_length]
      exact advance_le _ _ _ _ (by rw [ordL_length]; omega)
    rw [hpos1, bind_ok]
    rw [show alloc.vec.Vec.Insts.CoreOpsDerefDerefSlice.deref order = RustM.ok (vs order) from rfl,
      bind_ok]
    rw [hH _ _ (rowsList opened (vs order) pos.val pos1.val)
      ⟨_, rfl, rows_yields opened (vs order) (by rw [vs_val]; exact hordO) _ pos pos1 rfl
        (by rw [vs_val]; exact hp1le)⟩, bind_ok, bind_ok]
    have hpl : padA.val.length = N.val := by simp
    rw [Lib.update_eq padA 0#usize _ (by simp; omega), bind_ok,
      Lib.update_eq _ 1#usize _ (by simp; omega), bind_ok, hC, bind_ok, hlevel1, bind_ok]
    exact ⟨_, rfl, hinv pos1 hp1le⟩
  · rw [hlevel1, bind_ok]
    exact ⟨_, rfl, hinv pos hpos⟩

theorem from_residual_err {T E : Type _} (e : E) :
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResultNeverE.from_residual T
      (core.convert.From.Blanket E) (core.result.Result.Err e) =
      RustM.ok (core.result.Result.Err e) := by
  simp only [core.result.Result.Insts.CoreOpsTry_traitFromResidualResultNeverE.from_residual,
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResultInfallibleE.from_residual,
    core.convert.From.Blanket.from]
  rw [bind_ok]

theorem truncate_total {α : Type _} (v : alloc.vec.Vec α) (n : Std.Usize) :
    ∃ w, alloc.vec.Vec.truncate v n = RustM.ok w := by
  unfold alloc.vec.Vec.truncate
  simp only [rust_primitives.sequence.seq_len, bind_ok]
  split
  · rename_i hlt
    unfold rust_primitives.sequence.seq_drain
    rw [dite_eq_left_of_eq_true (eq_true ⟨by simp at hlt ⊢; omega, by simp⟩), bind_ok]
    exact ⟨_, rfl⟩
  · exact ⟨_, rfl⟩

theorem check_widths_total {T : Type} (dims : Slice p3_matrix.Dimensions)
    (opened : Slice (alloc.vec.Vec T)) :
    ∃ r, mmcs.hax_reshaped.check_widths dims opened = RustM.ok r := by
  unfold mmcs.hax_reshaped.check_widths
  simp only [core.slice.Slice.len, rust_primitives.slice.slice_length, bind_ok]
  split
  · exact ⟨_, rfl⟩
  · rename_i heq
    have hlen : opened.val.length = dims.val.length := by simpa using heq
    unfold mmcs.hax_reshaped.check_widths_loop
    refine loop_total _ (fun k : Std.Usize => k.val ≤ dims.val.length)
      (fun k => dims.val.length - k.val) ?_ _ (by simp)
    intro k hk
    unfold mmcs.hax_reshaped.check_widths_loop.body
    simp only [core.slice.Slice.len, rust_primitives.slice.slice_length, bind_ok]
    by_cases hlt : k.val < dims.val.length
    · rw [ite_eq_left (show k < Slice.len dims by simpa using hlt),
        Lib.slice_index_eq opened k (by omega), bind_ok]
      simp only [alloc.vec.Vec.len, rust_primitives.sequence.seq_len, bind_ok]
      rw [Lib.slice_index_eq dims k hlt, bind_ok]
      split
      · exact ⟨_, rfl, trivial⟩
      · have hmax : dims.val.length ≤ Usize.max := by scalar_tac
        obtain ⟨k1, hk1, hk1v⟩ := usize_add_eq (x := k) (y := 1#usize) (by simp; omega)
        have hk1v' : k1.val = k.val + 1 := by simpa using hk1v
        rw [hk1, bind_ok]
        exact ⟨_, rfl, by omega, by omega⟩
    · rw [ite_eq_right (show ¬ k < Slice.len dims by simpa using hlt)]
      exact ⟨_, rfl, trivial⟩

theorem array_eq_total {T : Type} {N : Std.Usize} (inst : core.cmp.PartialEq T T)
    (htot : ∀ x y, ∃ b, inst.eq x y = RustM.ok b) (a b : Std.Array T N) :
    ∃ r, core.Array.Insts.CoreCmpPartialEqArray.eq inst a b = RustM.ok r := by
  unfold core.Array.Insts.CoreCmpPartialEqArray.eq core.Array.Insts.CoreCmpPartialEqArray.eq_loop
  refine loop_total _ (fun i : Std.Usize => i.val ≤ N.val) (fun i => N.val - i.val) ?_ _ (by simp)
  intro i hi
  unfold core.Array.Insts.CoreCmpPartialEqArray.eq_loop.body
  by_cases hlt : i.val < N.val
  · rw [ite_eq_left (show i < N from hlt)]
    simp only [rust_primitives.slice.array_index]
    rw [Lib.slice_index_eq _ i (by simp; omega), bind_ok, Lib.slice_index_eq _ i (by simp; omega),
      bind_ok]
    obtain ⟨bb, hbb⟩ := htot (a.to_slice.val[i.val]'(by simp; omega)) (b.to_slice.val[i.val]'(by simp; omega))
    rw [hbb, bind_ok]
    split
    · have hmax : N.val ≤ Usize.max := by scalar_tac
      obtain ⟨i1, hi1, hi1v⟩ := usize_add_eq (x := i) (y := 1#usize) (by simp; omega)
      have hi1v' : i1.val = i.val + 1 := by simpa using hi1v
      rw [hi1, bind_ok]
      exact ⟨_, rfl, by omega, by omega⟩
    · exact ⟨_, rfl, trivial⟩
  · rw [ite_eq_right (show ¬ i < N from hlt)]
    exact ⟨_, rfl, trivial⟩

/-- The expected number of siblings is the sum over the walked levels of the arity less one. -/
theorem sum_loop_ok {sched : alloc.vec.Vec Std.Usize} {epl : Std.Usize}
    (h : mmcs.hax_reshaped.verify_batch_loop0 sched 0#usize 0#usize = RustM.ok epl) :
    epl.val = sibSum sched 0 := by
  unfold mmcs.hax_reshaped.verify_batch_loop0 at h
  refine loop_inv _ (fun x : Std.Usize × Std.Usize => x.2.val ≤ sched.val.length ∧
      x.1.val + sibSum sched x.2.val = sibSum sched 0)
    (fun e : Std.Usize => e.val = sibSum sched 0) ?_ _ _ h ⟨by simp, by simp⟩
  rintro ⟨e, l⟩ ⟨hl, he⟩ r hr
  dsimp only at hl he hr
  unfold mmcs.hax_reshaped.verify_batch_loop0.body at hr
  obtain ⟨len, hlen, hr⟩ := bind_tc_eq_ok hr
  simp only [alloc.vec.Vec.len, rust_primitives.sequence.seq_len] at hlen
  cases ok_inj hlen
  split at hr
  · rename_i hlt
    have hlt' : l.val < sched.val.length := by simpa using hlt
    obtain ⟨s1, hs1, hr⟩ := bind_tc_eq_ok hr
    obtain ⟨-, hs1v⟩ := vec_index_ok hs1
    obtain ⟨s2, hs2, hr⟩ := bind_tc_eq_ok hr
    obtain ⟨e1, he1, hr⟩ := bind_tc_eq_ok hr
    obtain ⟨l1, hl1, hr⟩ := bind_tc_eq_ok hr
    cases ok_inj hr
    have := sibSum_succ sched l.val hlt'
    rw [List.getElem?_eq_getElem hlt'] at hs1v
    have hs1e := Option.some.inj hs1v
    have hl1v : l1.val = l.val + 1 := usize_succ_ok hl1
    have hs2v : s2.val = s1.val - 1 := by simpa using (usize_sub_ok hs2).1
    have he1v := usize_add_ok he1
    refine ⟨by dsimp only; omega, ?_⟩
    dsimp only
    rw [he1v, hl1v, hs2v, ← hs1e, ← he, this]
    omega
  · rename_i hlt
    have hlt' : ¬ l.val < sched.val.length := by simpa using hlt
    cases ok_inj hr
    show e.val = _
    have : sibSum sched l.val = 0 := by
      simp [sibSum, List.drop_of_length_le (show sched.val.length ≤ l.val by omega)]
    omega

/-- Rows as wide as their matrices pass the width check. -/
theorem check_widths_eq_ok {T : Type} (dims : Slice p3_matrix.Dimensions)
    (opened : Slice (alloc.vec.Vec T)) (hlen : opened.val.length = dims.val.length)
    (hw : ∀ m (hm : m < dims.val.length) (hm' : m < opened.val.length),
      (opened.val[m]).val.length = (dims.val[m]).width.val) :
    mmcs.hax_reshaped.check_widths dims opened = RustM.ok (core.result.Result.Ok ()) := by
  unfold mmcs.hax_reshaped.check_widths
  simp only [core.slice.Slice.len, rust_primitives.slice.slice_length, bind_ok]
  rw [ite_eq_right (by simp; omega)]
  unfold mmcs.hax_reshaped.check_widths_loop
  obtain ⟨v, hv, hpost⟩ := loop_total_post
    (fun k => mmcs.hax_reshaped.check_widths_loop.body dims opened k)
    (fun k : Std.Usize => k.val ≤ dims.val.length)
    (fun v => v = core.result.Result.Ok ()) (fun k => dims.val.length - k.val) (by
      intro k hk
      unfold mmcs.hax_reshaped.check_widths_loop.body
      simp only [core.slice.Slice.len, rust_primitives.slice.slice_length, bind_ok]
      by_cases hlt : k.val < dims.val.length
      · rw [ite_eq_left (show k < Slice.len dims by simpa using hlt),
          Lib.slice_index_eq opened k (by omega), bind_ok]
        simp only [alloc.vec.Vec.len, rust_primitives.sequence.seq_len, bind_ok]
        rw [Lib.slice_index_eq dims k hlt, bind_ok]
        have hmax : dims.val.length ≤ Usize.max := by scalar_tac
        obtain ⟨k1, hk1, hk1v⟩ := usize_add_eq (x := k) (y := 1#usize) (by simp; omega)
        have hk1v' : k1.val = k.val + 1 := by simpa using hk1v
        rw [ite_eq_right (by
          have := hw k.val hlt (by omega)
          simp only [bne_iff_ne, ne_eq, Decidable.not_not]
          apply UScalar.eq_of_val_eq
          simpa using this), hk1, bind_ok]
        exact ⟨_, rfl, by omega, by omega⟩
      · rw [ite_eq_right (show ¬ k < Slice.len dims by simpa using hlt)]
        exact ⟨_, rfl, rfl⟩) 0#usize (by simp)
  rw [hv, hpost]

theorem array_eq_self {T : Type} {N : Std.Usize} (inst : core.cmp.PartialEq T T)
    (hrefl : ∀ x, inst.eq x x = RustM.ok true) (a : Std.Array T N) :
    core.Array.Insts.CoreCmpPartialEqArray.eq inst a a = RustM.ok true := by
  unfold core.Array.Insts.CoreCmpPartialEqArray.eq core.Array.Insts.CoreCmpPartialEqArray.eq_loop
  obtain ⟨v, hv, hpost⟩ := loop_total_post
    (fun i => core.Array.Insts.CoreCmpPartialEqArray.eq_loop.body inst a a i)
    (fun i : Std.Usize => i.val ≤ N.val) (fun v => v = true) (fun i => N.val - i.val) (by
      intro i hi
      unfold core.Array.Insts.CoreCmpPartialEqArray.eq_loop.body
      by_cases hlt : i.val < N.val
      · rw [ite_eq_left (show i < N from hlt)]
        simp only [rust_primitives.slice.array_index]
        rw [Lib.slice_index_eq _ i (by simp; omega), bind_ok, bind_ok, hrefl, bind_ok, ite_eq_left rfl]
        have hmax : N.val ≤ Usize.max := by scalar_tac
        obtain ⟨i1, hi1, hi1v⟩ := usize_add_eq (x := i) (y := 1#usize) (by simp; omega)
        have hi1v' : i1.val = i.val + 1 := by simpa using hi1v
        rw [hi1, bind_ok]
        exact ⟨_, rfl, by omega, by omega⟩
      · rw [ite_eq_right (show ¬ i < N from hlt)]
        exact ⟨_, rfl, rfl⟩) 0#usize (by simp)
  rw [hv, hpost]

end Plonky3Lean.Proofs.MerkleTree
