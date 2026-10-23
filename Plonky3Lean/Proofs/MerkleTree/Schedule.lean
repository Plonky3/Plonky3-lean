module

public import Plonky3Lean.Proofs.MerkleTree.Geometry

@[expose] public section

/-!
# The schedule, the matrix order and the leaf group, as functions

Each dimension-only computation of the verifier, read backwards, is a function of the heights.

The schedule loop may not return, so its function takes a fuel bound and answers `none` when the fuel runs out.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open p3_merkle_tree

namespace Plonky3Lean.Proofs.MerkleTree

/-- The tallest height, or 0 for no matrix. -/
def maxHeight (dims : Slice p3_matrix.Dimensions) : ℕ :=
  (dims.val.map fun d => d.height.val).foldl max 0

/-- Where a matrix of height `h` goes in an order sorted tallest first: after every matrix at least as tall. -/
def insertPos (height : ℕ → ℕ) (order : List ℕ) (h : ℕ) : ℕ :=
  order.findIdx fun j => decide (height j < h)

/-- The matrix indices `0 .. n`, tallest first, ties in input order, built by insertion. -/
def sortTallest (height : ℕ → ℕ) : ℕ → List ℕ
  | 0 => []
  | n + 1 =>
    let o := sortTallest height n
    let j := insertPos height o (height n)
    o.take j ++ n :: o.drop j

/-- The first position at or after `p` whose matrix does not round up to `lnpt`. -/
def leafEnd (height : ℕ → ℕ) (order : List ℕ) (lnpt : ℕ) (p : ℕ) : ℕ :=
  if p < order.length ∧ npt (height (order.getD p 0)) = lnpt then leafEnd height order lnpt (p + 1)
  else p
termination_by order.length - p

/-- The arity the verifier picks at a layer of padded width `curr`, with the matrices `order[from..]` still to enter. -/
def selectSpec (N curr lnpt : ℕ) (height : ℕ → ℕ) (order : List ℕ) (from' : ℕ) : ℕ :=
  if curr < N then 2
  else if (order.drop from').any (fun k => decide (npt (height k) ≠ lnpt) && decide (npt (height k) > npt (curr / N)))
  then 2 else N

/-- The schedule loop, run for at most `fuel` levels. -/
def schedRun (N lnpt : ℕ) (height : ℕ → ℕ) (order : List ℕ) :
    ℕ → ℕ → ℕ → List ℕ → Option (List ℕ)
  | 0, _, _, _ => none
  | f + 1, curr, pos, acc =>
    if 1 < curr then
      let s := selectSpec N curr lnpt height order pos
      let ln := curr / s
      let pos' := if pos < order.length ∧ npt (height (order.getD pos 0)) = npt ln
        then advance height order (height (order.getD pos 0)) pos else pos
      schedRun N lnpt height order f (padded ln N) pos' (acc ++ [s])
    else some acc

/-- The leaf group's end, as the verifier computes it. -/
theorem leaf_loop_ok (dims : Slice p3_matrix.Dimensions) (order : alloc.vec.Vec Std.Usize)
    (lnpt : Std.Usize) :
    ∀ n (pos p1 : Std.Usize), order.val.length - pos.val = n →
      mmcs.hax_reshaped.verify_batch_loop1 dims order lnpt pos = RustM.ok p1 →
      p1.val = leafEnd (heightOf dims) (ordL order) lnpt.val pos.val := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro pos p1 hn h
  unfold mmcs.hax_reshaped.verify_batch_loop1 at h
  obtain ⟨r, hr, h⟩ := loop_ok h
  unfold mmcs.hax_reshaped.verify_batch_loop1.body at hr
  obtain ⟨l, hl, hr⟩ := bind_tc_eq_ok hr
  simp only [alloc.vec.Vec.len, rust_primitives.sequence.seq_len] at hl
  cases ok_inj hl
  rw [leafEnd]
  split at hr
  · rename_i hlt
    have hlt' : pos.val < order.val.length := by simpa using hlt
    obtain ⟨i1, hi1, hr⟩ := bind_tc_eq_ok hr
    obtain ⟨-, hi1v⟩ := vec_index_ok hi1
    obtain ⟨d, hd, hr⟩ := bind_tc_eq_ok hr
    obtain ⟨-, hdv⟩ := slice_index_ok hd
    obtain ⟨i2, hi2, hr⟩ := bind_tc_eq_ok hr
    have hi2v := (npt_ok hi2).1
    split at hr
    · rename_i heq
      obtain ⟨pos1, hpos1, hr⟩ := bind_tc_eq_ok hr
      cases ok_inj hr
      have hp1 : pos1.val = pos.val + 1 := usize_succ_ok hpos1
      rw [ite_eq_left ⟨by rw [ordL_length]; exact hlt', by
        rw [ordL_getD hi1v, heightOf_eq hdv, ← hi2v, heq]⟩]
      rw [← hp1]
      exact ih _ (by omega) pos1 p1 rfl h
    · rename_i hne
      cases ok_inj hr
      cases h
      rw [ite_eq_right]
      rintro ⟨-, h2⟩
      apply hne
      apply UScalar.eq_of_val_eq
      rw [hi2v, ← h2, ordL_getD hi1v, heightOf_eq hdv]
  · rename_i hlt
    have hlt' : ¬ pos.val < order.val.length := by simpa using hlt
    cases ok_inj hr
    cases h
    rw [ite_eq_right]
    rintro ⟨h1, -⟩
    rw [ordL_length] at h1
    exact hlt' h1

/-- The same, in the schedule walk. -/
theorem sched_leaf_loop_ok (dims : Slice p3_matrix.Dimensions) (order : alloc.vec.Vec Std.Usize)
    (lnpt : Std.Usize) :
    ∀ n (pos p1 : Std.Usize), order.val.length - pos.val = n →
      mmcs.hax_reshaped.arity_schedule_and_proof_levels_loop0 dims order lnpt pos = RustM.ok p1 →
      p1.val = leafEnd (heightOf dims) (ordL order) lnpt.val pos.val := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro pos p1 hn h
  unfold mmcs.hax_reshaped.arity_schedule_and_proof_levels_loop0 at h
  obtain ⟨r, hr, h⟩ := loop_ok h
  unfold mmcs.hax_reshaped.arity_schedule_and_proof_levels_loop0.body at hr
  obtain ⟨l, hl, hr⟩ := bind_tc_eq_ok hr
  simp only [alloc.vec.Vec.len, rust_primitives.sequence.seq_len] at hl
  cases ok_inj hl
  rw [leafEnd]
  split at hr
  · rename_i hlt
    have hlt' : pos.val < order.val.length := by simpa using hlt
    obtain ⟨i1, hi1, hr⟩ := bind_tc_eq_ok hr
    obtain ⟨-, hi1v⟩ := vec_index_ok hi1
    obtain ⟨d, hd, hr⟩ := bind_tc_eq_ok hr
    obtain ⟨-, hdv⟩ := slice_index_ok hd
    obtain ⟨i2, hi2, hr⟩ := bind_tc_eq_ok hr
    have hi2v := (npt_ok hi2).1
    split at hr
    · rename_i heq
      obtain ⟨pos1, hpos1, hr⟩ := bind_tc_eq_ok hr
      cases ok_inj hr
      have hp1 : pos1.val = pos.val + 1 := usize_succ_ok hpos1
      rw [ite_eq_left ⟨by rw [ordL_length]; exact hlt', by
        rw [ordL_getD hi1v, heightOf_eq hdv, ← hi2v, heq]⟩]
      rw [← hp1]
      exact ih _ (by omega) pos1 p1 rfl h
    · rename_i hne
      cases ok_inj hr
      cases h
      rw [ite_eq_right]
      rintro ⟨-, h2⟩
      apply hne
      apply UScalar.eq_of_val_eq
      rw [hi2v, ← h2, ordL_getD hi1v, heightOf_eq hdv]
  · rename_i hlt
    have hlt' : ¬ pos.val < order.val.length := by simpa using hlt
    cases ok_inj hr
    cases h
    rw [ite_eq_right]
    rintro ⟨h1, -⟩
    rw [ordL_length] at h1
    exact hlt' h1

theorem sched_advance_ok (dims : Slice p3_matrix.Dimensions) (order : alloc.vec.Vec Std.Usize)
    (nh : Std.Usize) :
    ∀ n (pos p1 : Std.Usize), order.val.length - pos.val = n →
      mmcs.hax_reshaped.arity_schedule_and_proof_levels_loop1_loop0 dims order pos nh = RustM.ok p1 →
      p1.val = advance (heightOf dims) (ordL order) nh.val pos.val := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro pos p1 hn h
  unfold mmcs.hax_reshaped.arity_schedule_and_proof_levels_loop1_loop0 at h
  obtain ⟨r, hr, h⟩ := loop_ok h
  unfold mmcs.hax_reshaped.arity_schedule_and_proof_levels_loop1_loop0.body at hr
  obtain ⟨l, hl, hr⟩ := bind_tc_eq_ok hr
  simp only [alloc.vec.Vec.len, rust_primitives.sequence.seq_len] at hl
  cases ok_inj hl
  rw [advance]
  split at hr
  · rename_i hlt
    have hlt' : pos.val < order.val.length := by simpa using hlt
    obtain ⟨i1, hi1, hr⟩ := bind_tc_eq_ok hr
    obtain ⟨-, hi1v⟩ := vec_index_ok hi1
    obtain ⟨d, hd, hr⟩ := bind_tc_eq_ok hr
    obtain ⟨-, hdv⟩ := slice_index_ok hd
    split at hr
    · rename_i heq
      obtain ⟨pos1, hpos1, hr⟩ := bind_tc_eq_ok hr
      cases ok_inj hr
      have hp1 : pos1.val = pos.val + 1 := usize_succ_ok hpos1
      rw [ite_eq_left ⟨by rw [ordL_length]; exact hlt', by
        rw [ordL_getD hi1v, heightOf_eq hdv, heq]⟩]
      simp only at h
      rw [← hp1]
      exact ih _ (by omega) pos1 p1 rfl h
    · rename_i hne
      cases ok_inj hr
      simp only at h
      subst h
      rw [ite_eq_right]
      rintro ⟨-, h2⟩
      apply hne
      rw [ordL_getD hi1v, heightOf_eq hdv] at h2
      exact UScalar.eq_of_val_eq h2
  · rename_i hlt
    have hlt' : ¬ pos.val < order.val.length := by simpa using hlt
    cases ok_inj hr
    simp only at h
    subst h
    rw [ite_eq_right]
    rintro ⟨h1, -⟩
    rw [ordL_length] at h1
    exact hlt' h1

/-- The arity choice, as a function of the heights. -/
theorem select_ok_eq {N curr lnpt from' v : Std.Usize} {dims : Slice p3_matrix.Dimensions}
    {order : Slice Std.Usize}
    (h : mmcs.hax_reshaped.select_arity_step N curr lnpt dims order from' = RustM.ok v) :
    v.val = selectSpec N.val curr.val lnpt.val (heightOf dims) (order.val.map fun i => i.val)
      from'.val := by
  unfold mmcs.hax_reshaped.select_arity_step at h
  unfold selectSpec
  split at h
  · rename_i hlt
    rw [ite_eq_left (show curr.val < N.val from hlt), ← ok_inj h]; rfl
  · rename_i hlt
    rw [ite_eq_right (show ¬ curr.val < N.val from hlt)]
    obtain ⟨q, hq, h⟩ := bind_tc_eq_ok h
    obtain ⟨tgt, htgt, h⟩ := bind_tc_eq_ok h
    have hqv := (usize_div_ok hq).1
    have htgtv := (npt_ok htgt).1
    unfold mmcs.hax_reshaped.select_arity_step_loop at h
    -- The scan stops at the first matrix that forces a binary step.
    have key := loop_inv _
      (fun k : Std.Usize =>
        ((order.val.map fun i => i.val).drop from'.val).any (fun k' => decide (npt (heightOf dims k') ≠ lnpt.val) &&
            decide (npt (heightOf dims k') > npt (curr.val / N.val))) =
          ((order.val.map fun i => i.val).drop k.val).any (fun k' => decide (npt (heightOf dims k') ≠ lnpt.val) &&
            decide (npt (heightOf dims k') > npt (curr.val / N.val))))
      (fun v : Std.Usize => v.val = if ((order.val.map fun i => i.val).drop from'.val).any
          (fun k' => decide (npt (heightOf dims k') ≠ lnpt.val) &&
            decide (npt (heightOf dims k') > npt (curr.val / N.val))) then 2 else N.val)
      (by
        intro k hinv r hr
        unfold mmcs.hax_reshaped.select_arity_step_loop.body at hr
        obtain ⟨l, hl, hr⟩ := bind_tc_eq_ok hr
        simp only [core.slice.Slice.len, rust_primitives.slice.slice_length] at hl
        cases ok_inj hl
        split at hr
        · rename_i hk
          have hk' : k.val < order.val.length := by simpa using hk
          obtain ⟨i1, hi1, hr⟩ := bind_tc_eq_ok hr
          obtain ⟨-, hi1v⟩ := slice_index_ok hi1
          obtain ⟨d, hd, hr⟩ := bind_tc_eq_ok hr
          obtain ⟨-, hdv⟩ := slice_index_ok hd
          obtain ⟨np, hnp, hr⟩ := bind_tc_eq_ok hr
          have hnpv := (npt_ok hnp).1
          have hdrop : (order.val.map fun i => i.val).drop k.val =
              i1.val :: (order.val.map fun i => i.val).drop (k.val + 1) := by
            rw [List.drop_eq_getElem_cons (by simpa using hk')]
            rw [List.getElem?_eq_getElem hk'] at hi1v
            simp [Option.some.inj hi1v]
          have hh : heightOf dims i1.val = d.height.val := heightOf_eq hdv
          split at hr
          · rename_i hne
            split at hr
            · rename_i hgt
              cases ok_inj hr
              show (2#usize : Std.Usize).val = _
              rw [hinv, hdrop, List.any_cons, hh, ← hnpv]
              have hne' : np.val ≠ lnpt.val := fun e => by simp [UScalar.eq_of_val_eq e] at hne
              have hgt' : np.val > npt (curr.val / N.val) := by
                have : np.val > tgt.val := hgt
                rw [htgtv, hqv] at this; exact this
              simp [hne', hgt']
            · rename_i hgt
              obtain ⟨k1, hk1, hr⟩ := bind_tc_eq_ok hr
              cases ok_inj hr
              have hk1v : k1.val = k.val + 1 := usize_succ_ok hk1
              show _ = _
              rw [hinv, hdrop, List.any_cons, hh, ← hnpv, hk1v]
              have hgt' : ¬ np.val > npt (curr.val / N.val) := by
                have : ¬ np.val > tgt.val := hgt
                rw [htgtv, hqv] at this; exact this
              simp [hgt']
          · rename_i heq
            obtain ⟨k1, hk1, hr⟩ := bind_tc_eq_ok hr
            cases ok_inj hr
            have hk1v : k1.val = k.val + 1 := usize_succ_ok hk1
            show _ = _
            rw [hinv, hdrop, List.any_cons, hh, ← hnpv, hk1v]
            have heq' : np.val = lnpt.val := by
              have := heq; simp only [bne_iff_ne, ne_eq, Decidable.not_not] at this; rw [this]
            simp [heq']
        · rename_i hk
          have hk' : ¬ k.val < order.val.length := by simpa using hk
          cases ok_inj hr
          show N.val = _
          rw [hinv, List.drop_of_length_le (by simp; omega)]
          simp)
      _ _ h rfl
    exact key

/-- The schedule loop computes the schedule the fuel-bounded run reaches, for some fuel. -/
theorem sched_loop_run {N lnpt : Std.Usize} {dims : Slice p3_matrix.Dimensions}
    {order : alloc.vec.Vec Std.Usize} {curr pos : Std.Usize} {sched sched' : alloc.vec.Vec Std.Usize}
    (h : mmcs.hax_reshaped.arity_schedule_and_proof_levels_loop1 N dims order curr lnpt pos sched =
      RustM.ok sched') :
    ∃ f, schedRun N.val lnpt.val (heightOf dims) (ordL order) f curr.val pos.val
      (sched.val.map fun s => s.val) = some (sched'.val.map fun s => s.val) := by
  unfold mmcs.hax_reshaped.arity_schedule_and_proof_levels_loop1 at h
  refine loop_inv _
    (fun x : Std.Usize × Std.Usize × alloc.vec.Vec Std.Usize =>
      ∀ v : List ℕ, (∃ f, schedRun N.val lnpt.val (heightOf dims) (ordL order) f x.1.val x.2.1.val
          (x.2.2.val.map fun s => s.val) = some v) →
        ∃ f, schedRun N.val lnpt.val (heightOf dims) (ordL order) f curr.val pos.val
          (sched.val.map fun s => s.val) = some v)
    (fun v : alloc.vec.Vec Std.Usize => ∃ f, schedRun N.val lnpt.val (heightOf dims) (ordL order) f
        curr.val pos.val (sched.val.map fun s => s.val) = some (v.val.map fun s => s.val))
    ?_ _ _ h (fun v hv => hv)
  rintro ⟨c, p, sc⟩ hinv r hr
  dsimp only at hinv hr
  unfold mmcs.hax_reshaped.arity_schedule_and_proof_levels_loop1.body at hr
  split at hr
  · rename_i hc
    have hc' : 1 < c.val := hc
    obtain ⟨sl, hsl, hr⟩ := bind_tc_eq_ok hr
    have hslv : sl = vs order := (ok_inj hsl).symm
    obtain ⟨step, hstep, hr⟩ := bind_tc_eq_ok hr
    rw [hslv] at hstep
    have hstepv := select_ok_eq hstep
    rw [show ((vs order).val.map fun i => i.val) = ordL order from rfl] at hstepv
    obtain ⟨sc1, hsc1, hr⟩ := bind_tc_eq_ok hr
    obtain ⟨ln, hln, hr⟩ := bind_tc_eq_ok hr
    have hlnv := (usize_div_ok hln).1
    obtain ⟨c1, hc1, hr⟩ := bind_tc_eq_ok hr
    have hc1v := padded_len_ok hc1
    obtain ⟨lp, hlp, hr⟩ := bind_tc_eq_ok hr
    have hlpv := (npt_ok hlp).1
    obtain ⟨l, hl, hr⟩ := bind_tc_eq_ok hr
    simp only [alloc.vec.Vec.len, rust_primitives.sequence.seq_len] at hl
    cases ok_inj hl
    -- One step of the run.
    have hstepeq : ∀ (p' : ℕ) f v, (p' = if p.val < (ordL order).length ∧
          npt (heightOf dims ((ordL order).getD p.val 0)) = npt (c.val / step.val)
        then advance (heightOf dims) (ordL order) (heightOf dims ((ordL order).getD p.val 0)) p.val
        else p.val) →
        schedRun N.val lnpt.val (heightOf dims) (ordL order) f c1.val p'
          (sc1.val.map fun s => s.val) = some v →
        schedRun N.val lnpt.val (heightOf dims) (ordL order) (f + 1) c.val p.val
          (sc.val.map fun s => s.val) = some v := by
      intro p' f v hp' hrun
      simp only [schedRun, ite_eq_left hc']
      rw [← hstepv, ← hp', hc1v, hlnv] at *
      rw [vec_push_ok hsc1] at hrun
      simpa using hrun
    split at hr
    · rename_i hplt
      have hplt' : p.val < order.val.length := by simpa using hplt
      obtain ⟨i1, hi1, hr⟩ := bind_tc_eq_ok hr
      obtain ⟨-, hi1v⟩ := vec_index_ok hi1
      obtain ⟨d, hd, hr⟩ := bind_tc_eq_ok hr
      obtain ⟨-, hdv⟩ := slice_index_ok hd
      obtain ⟨i2, hi2, hr⟩ := bind_tc_eq_ok hr
      have hi2v := (npt_ok hi2).1
      split at hr
      · rename_i heq
        obtain ⟨p1, hp1, hr⟩ := bind_tc_eq_ok hr
        cases ok_inj hr
        have hp1v := sched_advance_ok dims order d.height _ p p1 rfl hp1
        intro v ⟨f, hf⟩
        obtain ⟨f', hf'⟩ := hinv v ⟨f + 1, hstepeq p1.val f v (by
          rw [ite_eq_left ⟨by rw [ordL_length]; exact hplt', by
            rw [ordL_getD hi1v, heightOf_eq hdv, ← hi2v, heq, hlpv, hlnv]⟩, ordL_getD hi1v,
            heightOf_eq hdv, hp1v]) hf⟩
        exact ⟨f', hf'⟩
      · rename_i hne
        cases ok_inj hr
        intro v ⟨f, hf⟩
        exact hinv v ⟨f + 1, hstepeq p.val f v (by
          rw [ite_eq_right]
          rintro ⟨-, h2⟩
          apply hne
          apply UScalar.eq_of_val_eq
          rw [hi2v, hlpv, hlnv, ← h2, ordL_getD hi1v, heightOf_eq hdv]) hf⟩
    · rename_i hplt
      have hplt' : ¬ p.val < order.val.length := by simpa using hplt
      cases ok_inj hr
      intro v ⟨f, hf⟩
      exact hinv v ⟨f + 1, hstepeq p.val f v (by
        rw [ite_eq_right]
        rintro ⟨h1, -⟩
        rw [ordL_length] at h1
        exact hplt' h1) hf⟩
  · rename_i hc
    have hc' : ¬ 1 < c.val := hc
    cases ok_inj hr
    exact hinv _ ⟨1, by simp [schedRun, hc']⟩

theorem insert_loop_ok (dims : Slice p3_matrix.Dimensions) (order : alloc.vec.Vec Std.Usize)
    (height : Std.Usize) :
    ∀ n (j r : Std.Usize), order.val.length - j.val = n → j.val ≤ order.val.length →
      mmcs.hax_reshaped.tallest_first_loop0_loop0 dims order height j = RustM.ok r →
      r.val = j.val + ((ordL order).drop j.val).findIdx
        (fun k => decide (heightOf dims k < height.val)) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro j r hn hj h
  unfold mmcs.hax_reshaped.tallest_first_loop0_loop0 at h
  obtain ⟨res, hres, h⟩ := loop_ok h
  unfold mmcs.hax_reshaped.tallest_first_loop0_loop0.body at hres
  obtain ⟨l, hl, hres⟩ := bind_tc_eq_ok hres
  simp only [alloc.vec.Vec.len, rust_primitives.sequence.seq_len] at hl
  cases ok_inj hl
  split at hres
  · rename_i hlt
    have hlt' : j.val < order.val.length := by simpa using hlt
    obtain ⟨i1, hi1, hres⟩ := bind_tc_eq_ok hres
    obtain ⟨-, hi1v⟩ := vec_index_ok hi1
    obtain ⟨d, hd, hres⟩ := bind_tc_eq_ok hres
    obtain ⟨-, hdv⟩ := slice_index_ok hd
    have hdrop : (ordL order).drop j.val = i1.val :: (ordL order).drop (j.val + 1) := by
      rw [List.drop_eq_getElem_cons (by rw [ordL_length]; exact hlt')]
      congr 1
      rw [List.getElem?_eq_getElem hlt'] at hi1v
      simp [ordL, Option.some.inj hi1v]
    have hh : heightOf dims i1.val = d.height.val := heightOf_eq hdv
    split at hres
    · rename_i hge
      obtain ⟨j1, hj1, hres⟩ := bind_tc_eq_ok hres
      cases ok_inj hres
      have hj1v : j1.val = j.val + 1 := usize_succ_ok hj1
      rw [ih _ (by omega) j1 r rfl (by omega) h, hdrop, List.findIdx_cons, hh, hj1v]
      have : ¬ d.height.val < height.val := by have : d.height ≥ height := hge; scalar_tac
      simp [this]; omega
    · rename_i hge
      cases ok_inj hres
      cases h
      rw [hdrop, List.findIdx_cons, hh]
      have : d.height.val < height.val := by
        have : ¬ d.height ≥ height := hge; scalar_tac
      simp [this]
  · rename_i hlt
    have hlt' : ¬ j.val < order.val.length := by simpa using hlt
    cases ok_inj hres
    cases h
    rw [List.drop_of_length_le (by rw [ordL_length]; omega)]
    simp

/-- The matrix order is the insertion sort, tallest first, ties in input order. -/
theorem tallest_first_eq {dims : Slice p3_matrix.Dimensions} {order : alloc.vec.Vec Std.Usize}
    (h : mmcs.hax_reshaped.tallest_first dims = RustM.ok order) :
    ordL order = sortTallest (heightOf dims) dims.val.length := by
  unfold mmcs.hax_reshaped.tallest_first at h
  obtain ⟨o0, ho0, h⟩ := bind_tc_eq_ok h
  have ho0' : o0.val = [] := vec_new_val ho0
  unfold mmcs.hax_reshaped.tallest_first_loop0 at h
  refine loop_inv _ (fun x : alloc.vec.Vec Std.Usize × Std.Usize =>
      x.2.val ≤ dims.val.length ∧ ordL x.1 = sortTallest (heightOf dims) x.2.val ∧
      ∀ i ∈ x.1.val, i.val < dims.val.length)
    (fun v : alloc.vec.Vec Std.Usize => ordL v = sortTallest (heightOf dims) dims.val.length)
    ?_ _ _ h ⟨by simp, by simp [ordL, ho0', sortTallest], by simp [ho0']⟩
  rintro ⟨o, i⟩ ⟨hi, ho, hb⟩ r hr
  dsimp only at hi ho hb hr
  unfold mmcs.hax_reshaped.tallest_first_loop0.body at hr
  obtain ⟨l, hl, hr⟩ := bind_tc_eq_ok hr
  simp only [core.slice.Slice.len, rust_primitives.slice.slice_length] at hl
  cases ok_inj hl
  split at hr
  · rename_i hlt
    have hlt' : i.val < dims.val.length := by simpa using hlt
    obtain ⟨d, hd, hr⟩ := bind_tc_eq_ok hr
    obtain ⟨-, hdv⟩ := slice_index_ok hd
    obtain ⟨j, hj, hr⟩ := bind_tc_eq_ok hr
    have hjv := insert_loop_ok dims o d.height _ 0#usize j rfl (by simp) hj
    obtain ⟨o1, ho1, hr⟩ := bind_tc_eq_ok hr
    obtain ⟨i2, hi2, hr⟩ := bind_tc_eq_ok hr
    cases ok_inj hr
    have hi2v : i2.val = i.val + 1 := usize_succ_ok hi2
    have hh : heightOf dims i.val = d.height.val := heightOf_eq hdv
    refine ⟨by dsimp only; omega, ?_, ?_⟩
    · dsimp only
      rw [hi2v, sortTallest, ← ho]
      simp only [ordL, vec_insert_ok ho1, List.map_append, List.map_take, List.map_drop,
        List.map_cons]
      simp only [ordL] at hjv
      rw [hjv, insertPos, hh]
      simp
    · intro x hx
      rw [vec_insert_ok ho1] at hx
      simp only [List.mem_append, List.mem_cons] at hx
      rcases hx with hx | rfl | hx
      · exact hb x (List.mem_of_mem_take hx)
      · exact hlt'
      · exact hb x (List.mem_of_mem_drop hx)
  · rename_i hlt
    have hlt' : ¬ i.val < dims.val.length := by simpa using hlt
    cases ok_inj hr
    show ordL o = _
    rw [ho, show i.val = dims.val.length by omega]

/-- The height check's first loop computes the tallest height. -/
theorem max_loop_ok {dims : Slice p3_matrix.Dimensions} {m : Std.Usize}
    (h : mmcs.hax_reshaped.validate_heights_loop0 dims 0#usize 0#usize = RustM.ok m) :
    m.val = maxHeight dims := by
  unfold mmcs.hax_reshaped.validate_heights_loop0 at h
  refine loop_inv _ (fun x : Std.Usize × Std.Usize => x.2.val ≤ dims.val.length ∧
      x.1.val = ((dims.val.take x.2.val).map fun d => d.height.val).foldl max 0)
    (fun v : Std.Usize => v.val = maxHeight dims) ?_ _ _ h ⟨by simp, by simp⟩
  rintro ⟨mx, i⟩ ⟨hi, hm⟩ r hr
  dsimp only at hi hm hr
  unfold mmcs.hax_reshaped.validate_heights_loop0.body at hr
  obtain ⟨l, hl, hr⟩ := bind_tc_eq_ok hr
  simp only [core.slice.Slice.len, rust_primitives.slice.slice_length] at hl
  cases ok_inj hl
  split at hr
  · rename_i hlt
    have hlt' : i.val < dims.val.length := by simpa using hlt
    obtain ⟨d, hd, hr⟩ := bind_tc_eq_ok hr
    obtain ⟨-, hdv⟩ := slice_index_ok hd
    rw [List.getElem?_eq_getElem hlt'] at hdv
    have hd' : d = dims.val[i.val] := (Option.some.inj hdv).symm
    obtain ⟨m1, hm1, hr⟩ := bind_tc_eq_ok hr
    obtain ⟨i2, hi2, hr⟩ := bind_tc_eq_ok hr
    cases ok_inj hr
    have hi2v : i2.val = i.val + 1 := usize_succ_ok hi2
    have hm1v : m1.val = max mx.val d.height.val := by
      split at hm1
      · rename_i hgt
        cases ok_inj hm1
        have : d.height.val > mx.val := hgt
        omega
      · rename_i hgt
        cases ok_inj hm1
        have : ¬ d.height.val > mx.val := hgt
        omega
    refine ⟨by dsimp only; omega, ?_⟩
    dsimp only
    rw [hi2v, hm1v, hm, List.take_add_one, List.getElem?_eq_getElem hlt', hd', List.map_append,
      List.foldl_append]
    rfl
  · rename_i hlt
    have hlt' : ¬ i.val < dims.val.length := by simpa using hlt
    cases ok_inj hr
    show mx.val = _
    rw [hm, List.take_of_length_le (by omega)]
    rfl

/-- A height check that passes returns the tallest height. -/
theorem validate_ok_val {dims : Slice p3_matrix.Dimensions} {val : Std.Usize}
    (h : mmcs.hax_reshaped.validate_heights dims = RustM.ok (core.result.Result.Ok val)) :
    val.val = maxHeight dims ∧ 0 < val.val := by
  unfold mmcs.hax_reshaped.validate_heights at h
  obtain ⟨m, hm, h⟩ := bind_tc_eq_ok h
  have hmv := max_loop_ok hm
  split at h
  · cases ok_inj h
  rename_i hm0
  obtain ⟨lg, hlg, h⟩ := bind_tc_eq_ok h
  unfold mmcs.hax_reshaped.validate_heights_loop1 at h
  have key := loop_inv _ (fun _ : Std.Usize => True)
    (fun v : core.result.Result Std.Usize mmcs.error.MerkleTreeError =>
      v = core.result.Result.Ok val → val = m) (by
      intro k _ r hr
      unfold mmcs.hax_reshaped.validate_heights_loop1.body at hr
      obtain ⟨l, hl, hr⟩ := bind_tc_eq_ok hr
      split at hr
      · obtain ⟨d, _hd, hr⟩ := bind_tc_eq_ok hr
        obtain ⟨i2, _hi2, hr⟩ := bind_tc_eq_ok hr
        obtain ⟨br, _hbr, hr⟩ := bind_tc_eq_ok hr
        obtain ⟨i3, _hi3, hr⟩ := bind_tc_eq_ok hr
        obtain ⟨i4, _hi4, hr⟩ := bind_tc_eq_ok hr
        obtain ⟨eh, _heh, hr⟩ := bind_tc_eq_ok hr
        split at hr
        · cases ok_inj hr; intro h0; cases h0
        · obtain ⟨i5, _hi5, hr⟩ := bind_tc_eq_ok hr
          cases ok_inj hr; trivial
      · cases ok_inj hr
        intro h0
        cases h0
        rfl) _ _ h trivial
  have hvm := key rfl
  subst hvm
  refine ⟨hmv, ?_⟩
  have : val ≠ 0#usize := hm0
  have : val.val ≠ 0 := fun e => this (UScalar.eq_of_val_eq (by simpa using e))
  omega

/-- The schedule the verifier computes, as a function of the heights. -/
theorem arity_eq {N cap pl : Std.Usize} {dims : Slice p3_matrix.Dimensions}
    {sched : alloc.vec.Vec Std.Usize}
    (h : mmcs.hax_reshaped.arity_schedule_and_proof_levels N cap dims =
      RustM.ok (core.result.Result.Ok (sched, pl))) :
    ∃ (val : Std.Usize) (order : alloc.vec.Vec Std.Usize) (curr lnpt pos0 : Std.Usize) (f : ℕ),
      mmcs.hax_reshaped.validate_heights dims = RustM.ok (core.result.Result.Ok val) ∧
      mmcs.hax_reshaped.tallest_first dims = RustM.ok order ∧
      p3_merkle_tree.merkle_tree.padded_len val N = RustM.ok curr ∧
      core.num.Usize.next_power_of_two val = RustM.ok lnpt ∧
      pos0.val = leafEnd (heightOf dims) (ordL order) lnpt.val 0 ∧
      schedRun N.val lnpt.val (heightOf dims) (ordL order) f curr.val pos0.val [] =
        some (sched.val.map fun s => s.val) ∧
      pl.val = sched.val.length - min cap.val sched.val.length := by
  unfold mmcs.hax_reshaped.arity_schedule_and_proof_levels at h
  obtain ⟨r, hr, g1⟩ := bind_tc_eq_ok h
  obtain ⟨cf, hcf, g2⟩ := bind_tc_eq_ok g1
  cases cf with
  | Break res => exact (from_residual_ne_ok _ _ g2).elim
  | Continue val =>
  dsimp only at g2
  have hrv := branch_continue hcf
  subst hrv
  obtain ⟨order, horder, g3⟩ := bind_tc_eq_ok g2
  obtain ⟨curr, hcurr, g4⟩ := bind_tc_eq_ok g3
  obtain ⟨lnpt, hlnpt, g5⟩ := bind_tc_eq_ok g4
  obtain ⟨pos0, hpos0, g6⟩ := bind_tc_eq_ok g5
  obtain ⟨s0, hs0, g7⟩ := bind_tc_eq_ok g6
  obtain ⟨s1, hs1, g8⟩ := bind_tc_eq_ok g7
  obtain ⟨tl, htl, g9⟩ := bind_tc_eq_ok g8
  simp only [alloc.vec.Vec.len, rust_primitives.sequence.seq_len] at htl
  cases ok_inj htl
  obtain ⟨ech, hech, g10⟩ := bind_tc_eq_ok g9
  obtain ⟨i, hi, g11⟩ := bind_tc_eq_ok g10
  have e := ok_inj g11
  simp only [core.result.Result.Ok.injEq, Prod.mk.injEq] at e
  obtain ⟨rfl, rfl⟩ := e
  have hs0' : s0.val = [] := vec_new_val hs0
  obtain ⟨f, hf⟩ := sched_loop_run hs1
  rw [hs0'] at hf
  refine ⟨val, order, curr, lnpt, pos0, f, hr, horder, hcurr, hlnpt,
    sched_leaf_loop_ok dims order lnpt _ 0#usize pos0 rfl hpos0, hf, ?_⟩
  rw [(usize_sub_ok hi).1]
  have : ech.val = min cap.val (Slice.len s1).val := by
    split at hech
    · rename_i hlt; cases ok_inj hech; have : cap.val < (Slice.len s1).val := hlt; omega
    · rename_i hlt; cases ok_inj hech; have : ¬ cap.val < (Slice.len s1).val := hlt; omega
  rw [this]
  simp

end Plonky3Lean.Proofs.MerkleTree
