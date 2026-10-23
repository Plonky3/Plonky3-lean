module

public import Plonky3Lean.Proofs.MerkleTree.Walk
public import Plonky3Lean.Proofs.Symmetric.Iter

@[expose] public section

/-!
# The extracted walk, read backwards

A run of the verifier's main loop that returns computes the fold of the plan.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open p3_merkle_tree

namespace Plonky3Lean.Proofs.MerkleTree

/-- The height of matrix `m`, or 0 past the end. -/
def heightOf (dims : Slice p3_matrix.Dimensions) (m : ℕ) : ℕ :=
  (dims.val.map fun d => d.height.val).getD m 0

/-- An order of matrices, as natural numbers. -/
def ordL (order : alloc.vec.Vec Std.Usize) : List ℕ := order.val.map fun i => i.val

theorem ordL_length (order : alloc.vec.Vec Std.Usize) : (ordL order).length = order.val.length := by
  simp [ordL]

theorem ordL_getD {order : alloc.vec.Vec Std.Usize} {p : ℕ} {i : Std.Usize}
    (hp : order.val[p]? = some i) : (ordL order).getD p 0 = i.val := by
  simp [ordL, List.getD_eq_getElem?_getD, hp]

theorem heightOf_eq {dims : Slice p3_matrix.Dimensions} {m : ℕ} {d : p3_matrix.Dimensions}
    (hm : dims.val[m]? = some d) : heightOf dims m = d.height.val := by
  simp [heightOf, List.getD_eq_getElem?_getD, hm]

theorem advance_ok (dims : Slice p3_matrix.Dimensions) (order : alloc.vec.Vec Std.Usize)
    (nh : Std.Usize) :
    ∀ n (pos p1 : Std.Usize), order.val.length - pos.val = n →
      mmcs.hax_reshaped.verify_batch_loop2_loop1 dims order pos nh = RustM.ok p1 →
      p1.val = advance (heightOf dims) (ordL order) nh.val pos.val := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro pos p1 hn h
  unfold mmcs.hax_reshaped.verify_batch_loop2_loop1 at h
  obtain ⟨r, hr, h⟩ := loop_ok h
  unfold mmcs.hax_reshaped.verify_batch_loop2_loop1.body at hr
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

/-- Siblings used before slot `k`: every slot below `min k s` except the path's own. -/
def sibCount (s pg k : ℕ) : ℕ := min k s - if pg < min k s then 1 else 0

theorem children_ok {W : Type _} {N DIGEST_ELEMS : Std.Usize}
    (proof : Slice (Std.Array W DIGEST_ELEMS)) (d : Std.Array W DIGEST_ELEMS) (pp s pg : Std.Usize)
    (hpg : pg.val < s.val) (z : Std.Array W DIGEST_ELEMS) :
    ∀ n (inputs : Std.Array (Std.Array W DIGEST_ELEMS) N) (sib k : Std.Usize)
      (out : Std.Array (Std.Array W DIGEST_ELEMS) N),
      N.val - k.val = n → k.val ≤ N.val → sib.val = sibCount s.val pg.val k.val →
      mmcs.hax_reshaped.verify_batch_loop2_loop0 proof d pp s pg inputs sib k = RustM.ok out →
      out.val = (List.range N.val).map fun j =>
        if j < k.val then inputs.val.getD j z
        else if j < s.val then
          (if j = pg.val then d else proof.val.getD (pp.val + if j < pg.val then j else j - 1) z)
        else inputs.val.getD j z := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro inputs sib k out hn hk hsib h
  unfold mmcs.hax_reshaped.verify_batch_loop2_loop0 at h
  obtain ⟨r, hr, h⟩ := loop_ok h
  dsimp only at hr
  unfold mmcs.hax_reshaped.verify_batch_loop2_loop0.body at hr
  split at hr
  · rename_i hkN
    have hkN' : k.val < N.val := hkN
    obtain ⟨st, hst, hr⟩ := bind_tc_eq_ok hr
    obtain ⟨k1, hk1, hr⟩ := bind_tc_eq_ok hr
    have hk1' : k1.val = k.val + 1 := usize_succ_ok hk1
    cases ok_inj hr
    simp only at h
    -- The slot k gets its value, the rest is the induction.
    have key : ∃ v, st.1.val = inputs.val.set k.val v ∧ st.2.val = sibCount s.val pg.val k1.val ∧
        v = (if k.val < s.val then
          (if k.val = pg.val then d
            else proof.val.getD (pp.val + if k.val < pg.val then k.val else k.val - 1) z)
          else inputs.val.getD k.val z) := by
      split at hst
      · rename_i hks
        have hks' : k.val < s.val := hks
        split at hst
        · rename_i hkp
          have hkp' : k.val = pg.val := by simpa using congrArg UScalar.val hkp
          obtain ⟨a, ha, hst⟩ := bind_tc_eq_ok hst
          cases ok_inj hst
          refine ⟨d, (array_update_ok ha).1, ?_, by simp [hkp', hpg]⟩
          simp only [sibCount, hsib, hk1'] at *
          rw [Nat.min_eq_left (by omega), Nat.min_eq_left (by omega)]
          split_ifs <;> omega
        · rename_i hkp
          have hkp' : k.val ≠ pg.val := fun e => hkp (UScalar.eq_of_val_eq e)
          obtain ⟨i, hi, hst⟩ := bind_tc_eq_ok hst
          obtain ⟨a, ha, hst⟩ := bind_tc_eq_ok hst
          obtain ⟨a1, ha1, hst⟩ := bind_tc_eq_ok hst
          obtain ⟨sib2, hsib2, hst⟩ := bind_tc_eq_ok hst
          cases ok_inj hst
          have hi' := usize_add_ok hi
          obtain ⟨-, hav⟩ := slice_index_ok ha
          have e1 : sib.val = (if k.val < pg.val then k.val else k.val - 1) := by
            rw [hsib, sibCount, Nat.min_eq_left (by omega)]
            split_ifs <;> omega
          refine ⟨a, (array_update_ok ha1).1, ?_, ?_⟩
          · have e2 : sib2.val = sib.val + 1 := usize_succ_ok hsib2
            rw [sibCount, hk1', Nat.min_eq_left (by omega), e2, e1]
            split_ifs <;> omega
          · rw [ite_eq_left hks', ite_eq_right hkp', List.getD_eq_getElem?_getD, ← e1, ← hi', hav]
            rfl
      · rename_i hks
        have hks' : ¬ k.val < s.val := hks
        cases ok_inj hst
        refine ⟨inputs.val.getD k.val z, ?_, ?_, by simp [hks']⟩
        · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simpa using hkN')]
          simp
        · simp only [sibCount, hsib, hk1']
          rw [Nat.min_eq_right (by omega), Nat.min_eq_right (by omega)]
    obtain ⟨v, hv1, hv2, hv⟩ := key
    rw [ih _ (by omega) st.1 st.2 k1 out rfl (by omega) hv2
      (by unfold mmcs.hax_reshaped.verify_batch_loop2_loop0; exact h), hv1]
    apply List.map_congr_left
    intro j hj
    simp only [List.mem_range] at hj
    rw [hk1']
    by_cases hjk : j < k.val
    · rw [ite_eq_left (by omega), ite_eq_left hjk, getD_set_of_ne _ _ _ _ _ (by omega)]
    · by_cases hjk' : j = k.val
      · subst hjk'
        rw [ite_eq_left (by omega), ite_eq_right hjk, getD_set_self' _ _ _ _ (by simpa using hkN'), hv]
      · rw [ite_eq_right (by omega), ite_eq_right hjk, getD_set_of_ne _ _ _ _ _ (by omega)]
  · rename_i hkN
    have hkN' : ¬ k.val < N.val := hkN
    cases ok_inj hr
    simp only at h
    subst h
    apply List.ext_getElem (by simp)
    intro j h1 h2
    simp only [List.getElem_map, List.getElem_range]
    have hj : j < k.val := by simp at h2; omega
    rw [ite_eq_left hj, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1]
    simp

/-! ## The hasher and the compression, as functions -/

/-- The hasher's digest of slices depends only on the slices its iterator yields: it is `h` of them. -/
def HashOn {H F D : Type} (hInst : p3_symmetric.hasher.CryptographicHasher H F D) (t : H)
    (h : List (List F) → D) : Prop :=
  ∀ {I J : Type} (inst : core.iter.traits.collect.IntoIterator I (Slice F) J) (it : I)
    (xs : List (Slice F)),
    (∃ s, inst.into_iter it = RustM.ok s ∧ Symmetric.Yields inst.iteratorIteratorInst s xs) →
    hInst.hash_iter_slices inst t it = RustM.ok (h (xs.map fun x => x.val))

/-- The compression returns `c` of its children, and never panics. -/
def CompressOn {C D : Type} {N : Std.Usize}
    (cInst : p3_symmetric.compression.PseudoCompressionFunction C D N) (t : C) (c : List D → D) :
    Prop :=
  ∀ a, cInst.compress t a = RustM.ok (c a.val)

/-- A vector seen as a slice, as `as_slice` returns it. -/
def vs {F : Type} (v : alloc.vec.Vec F) : Slice F := v

theorem vs_val {F : Type} (v : alloc.vec.Vec F) : (vs v).val = v.val := rfl

theorem as_slice_eq {F : Type} (v : alloc.vec.Vec F) : alloc.vec.Vec.as_slice v = RustM.ok (vs v) :=
  rfl

/-- The rows of `order[a..b]`, as the verifier's row iterator yields them. -/
def rowsList {F : Type} (opened : Slice (alloc.vec.Vec F)) (order : Slice Std.Usize) (a b : ℕ) :
    List (Slice F) :=
  (((order.val.drop a).take (b - a)).filterMap fun i => opened.val[i.val]?).map vs

theorem rows_yields {F : Type} (opened : Slice (alloc.vec.Vec F)) (order : Slice Std.Usize)
    (hord : ∀ i ∈ order.val, i.val < opened.val.length) :
    ∀ n (a b : Std.Usize), b.val - a.val = n → b.val ≤ order.val.length →
      Symmetric.Yields (mmcs.hax_reshaped.Rows.Insts.CoreIterTraitsIteratorIteratorSharedASlice F)
        { opened_values := opened, order, pos := a, «end» := b } (rowsList opened order a.val b.val) := by
  intro n
  induction n with
  | zero =>
    intro a b hn hb
    have hl : rowsList opened order a.val b.val = [] := by
      simp only [rowsList, show b.val - a.val = 0 by omega, List.take_zero, List.filterMap_nil,
        List.map_nil]
    rw [hl]
    refine ⟨{ opened_values := opened, order, pos := a, «end» := b }, ?_⟩
    show mmcs.hax_reshaped.Rows.Insts.CoreIterTraitsIteratorIteratorSharedASlice.next _ = _
    unfold mmcs.hax_reshaped.Rows.Insts.CoreIterTraitsIteratorIteratorSharedASlice.next
    dsimp only
    rw [ite_eq_right (by intro h; have : a.val < b.val := h; omega)]
  | succ n ih =>
    intro a b hn hb
    have hab : a.val < b.val := by omega
    have ha : a.val < order.val.length := by omega
    have hi := hord _ (List.getElem_mem ha)
    have hmax : a.val + 1 ≤ Usize.max := by
      have : b.val ≤ Usize.max := by scalar_tac
      omega
    obtain ⟨a1, ha1, ha1v⟩ : ∃ a1 : Std.Usize, a + 1#usize = RustM.ok a1 ∧ a1.val = a.val + 1 := by
      have : a + 1#usize ⦃ z => z.val = a.val + (1#usize : Std.Usize).val ⦄ := by step*
      obtain ⟨j, e1, h1⟩ := Lib.spec_imp_exists this
      exact ⟨j, e1, by simpa using h1⟩
    have hl : rowsList opened order a.val b.val =
        vs (opened.val[(order.val[a.val]).val]) :: rowsList opened order a1.val b.val := by
      simp only [rowsList, ha1v]
      rw [List.drop_eq_getElem_cons ha, show b.val - a.val = (b.val - (a.val + 1)) + 1 by omega,
        List.take_succ_cons, List.filterMap_cons]
      simp [List.getElem?_eq_getElem hi]
    rw [hl]
    refine ⟨{ opened_values := opened, order, pos := a1, «end» := b }, ?_, ih a1 b (by omega) hb⟩
    show mmcs.hax_reshaped.Rows.Insts.CoreIterTraitsIteratorIteratorSharedASlice.next _ = _
    unfold mmcs.hax_reshaped.Rows.Insts.CoreIterTraitsIteratorIteratorSharedASlice.next
    dsimp only
    rw [ite_eq_left (show a < b from hab)]
    rw [Lib.slice_index_eq order a ha, bind_ok, Lib.slice_index_eq opened _ hi, bind_ok,
      as_slice_eq, bind_ok, ha1, bind_ok]

/-- The opened rows, as lists. -/
def openedL {F : Type} (opened : Slice (alloc.vec.Vec F)) : List (List F) :=
  opened.val.map fun v => v.val

theorem rows_aux {F : Type} (opened : Slice (alloc.vec.Vec F)) :
    ∀ l : List Std.Usize, (∀ i ∈ l, i.val < opened.val.length) →
      (l.filterMap fun i => opened.val[i.val]?).map (fun v => (vs v).val) =
        l.map fun i => (openedL opened).getD i.val [] := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons x l ih =>
    intro hl
    have hx := hl x (by simp)
    rw [List.filterMap_cons, List.getElem?_eq_getElem hx]
    simp only [List.map_cons]
    rw [ih (fun i hi => hl i (by simp [hi]))]
    simp [openedL, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hx, vs_val]

theorem rowsList_val {F : Type} (opened : Slice (alloc.vec.Vec F)) (order : alloc.vec.Vec Std.Usize)
    (hord : ∀ i ∈ order.val, i.val < opened.val.length) (a b : ℕ) :
    (rowsList opened (vs order) a b).map (fun x => x.val) =
      group (ordL order) (openedL opened) a b := by
  simp only [rowsList, group, ordL, vs_val, List.map_map]
  rw [← List.map_drop, ← List.map_take, List.map_map]
  rw [show ((fun x : Slice F => x.val) ∘ vs) = fun v => (vs v).val from rfl]
  rw [rows_aux opened _ (fun i hi => hord i (List.mem_of_mem_drop (List.mem_of_mem_take hi)))]
  rfl

end Plonky3Lean.Proofs.MerkleTree
