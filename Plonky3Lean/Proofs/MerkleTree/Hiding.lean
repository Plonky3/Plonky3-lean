module

public import Plonky3Lean.Proofs.MerkleTree.Bind

@[expose] public section

/-!
# The hiding verifier is the plain verifier on salted rows

The hiding commitment appends a salt to every row of every matrix before committing.

Its verifier checks the unsalted widths and appends each salt to its row.

It then widens each width by the salt length and runs the plain verifier.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open p3_merkle_tree

namespace Plonky3Lean.Proofs.MerkleTree

variable {F : Type}

/-- Copying the items of a vector from position j on appends them. -/
theorem copy_loop_ok (cl : core.clone.Clone F) (hcl : ∀ x, cl.clone x = RustM.ok x)
    (src : Slice (alloc.vec.Vec F)) (i : Std.Usize) (row out : alloc.vec.Vec F) (j : Std.Usize)
    (v : alloc.vec.Vec F) (hv : src.val[i.val]? = some v)
    (h : mmcs.hax_reshaped.hiding_verify_batch_loop0_loop0 cl src i row j = RustM.ok out) :
    out.val = row.val ++ v.val.drop j.val := by
  unfold mmcs.hax_reshaped.hiding_verify_batch_loop0_loop0 at h
  have key := loop_inv _
    (fun x : alloc.vec.Vec F × Std.Usize => x.1.val ++ v.val.drop x.2.val = row.val ++ v.val.drop j.val)
    (fun r : alloc.vec.Vec F => r.val = row.val ++ v.val.drop j.val)
    (by
      rintro ⟨r, k⟩ hinv res hres
      dsimp only at hinv hres
      unfold mmcs.hax_reshaped.hiding_verify_batch_loop0_loop0.body at hres
      obtain ⟨v', hv', hres⟩ := bind_tc_eq_ok hres
      obtain ⟨-, hv'v⟩ := slice_index_ok hv'
      rw [hv] at hv'v
      cases Option.some.inj hv'v
      obtain ⟨l, hl, hres⟩ := bind_tc_eq_ok hres
      simp only [alloc.vec.Vec.len, rust_primitives.sequence.seq_len] at hl
      cases ok_inj hl
      split at hres
      · rename_i hlt
        have hlt' : k.val < v.val.length := by simpa using hlt
        obtain ⟨t, ht, hres⟩ := bind_tc_eq_ok hres
        obtain ⟨-, htv⟩ := vec_index_ok ht
        obtain ⟨t1, ht1, hres⟩ := bind_tc_eq_ok hres
        rw [hcl] at ht1
        cases ok_inj ht1
        obtain ⟨r1, hr1, hres⟩ := bind_tc_eq_ok hres
        obtain ⟨k1, hk1, hres⟩ := bind_tc_eq_ok hres
        cases ok_inj hres
        have hk1v : k1.val = k.val + 1 := usize_succ_ok hk1
        show r1.val ++ v.val.drop k1.val = _
        rw [vec_push_ok hr1, hk1v, ← hinv, List.drop_eq_getElem_cons hlt']
        rw [List.getElem?_eq_getElem hlt'] at htv
        rw [Option.some.inj htv]
        simp
      · rename_i hlt
        have hlt' : ¬ k.val < v.val.length := by simpa using hlt
        cases ok_inj hres
        show r.val = _
        rw [← hinv, List.drop_of_length_le (by omega)]
        simp)
    _ _ h rfl
  exact key

/-- The same, for the salts, whose loop is the same loop. -/
theorem copy_loop_ok' (cl : core.clone.Clone F) (hcl : ∀ x, cl.clone x = RustM.ok x)
    (src : Slice (alloc.vec.Vec F)) (i : Std.Usize) (row out : alloc.vec.Vec F) (j : Std.Usize)
    (v : alloc.vec.Vec F) (hv : src.val[i.val]? = some v)
    (h : mmcs.hax_reshaped.hiding_verify_batch_loop0_loop1 cl src i row j = RustM.ok out) :
    out.val = row.val ++ v.val.drop j.val :=
  copy_loop_ok cl hcl src i row out j v hv h

/-- The rows, as lists. -/
def rowsL (o : Slice (alloc.vec.Vec F)) : List (List F) := o.val.map fun v => v.val

/-- Salting appends each salt to its row. -/
theorem salt_loop_ok (cl : core.clone.Clone F) (hcl : ∀ x, cl.clone x = RustM.ok x)
    (opened salts : Slice (alloc.vec.Vec F)) (hlen : opened.val.length = salts.val.length)
    (acc out : alloc.vec.Vec (alloc.vec.Vec F))
    (hacc : acc.val = [])
    (h : mmcs.hax_reshaped.hiding_verify_batch_loop0 cl opened salts acc 0#usize = RustM.ok out) :
    out.val.map (fun v => v.val) = List.zipWith (· ++ ·) (rowsL opened) (rowsL salts) := by
  unfold mmcs.hax_reshaped.hiding_verify_batch_loop0 at h
  have key := loop_inv _
    (fun x : alloc.vec.Vec (alloc.vec.Vec F) × Std.Usize =>
      x.2.val ≤ opened.val.length ∧
      x.1.val.map (fun v => v.val) =
        List.zipWith (· ++ ·) ((rowsL opened).take x.2.val) ((rowsL salts).take x.2.val))
    (fun r : alloc.vec.Vec (alloc.vec.Vec F) =>
      r.val.map (fun v => v.val) = List.zipWith (· ++ ·) (rowsL opened) (rowsL salts))
    (by
      rintro ⟨a, i⟩ ⟨hi, hinv⟩ res hres
      dsimp only at hinv hres hi
      unfold mmcs.hax_reshaped.hiding_verify_batch_loop0.body at hres
      obtain ⟨l, hl, hres⟩ := bind_tc_eq_ok hres
      simp only [core.slice.Slice.len] at hl
      cases ok_inj hl
      split at hres
      · rename_i hlt
        have hlt' : i.val < opened.val.length := by simpa using hlt
        obtain ⟨r0, hr0, hres⟩ := bind_tc_eq_ok hres
        have hr0v : r0.val = [] := vec_new_val hr0
        obtain ⟨r1, hr1, hres⟩ := bind_tc_eq_ok hres
        obtain ⟨r2, hr2, hres⟩ := bind_tc_eq_ok hres
        obtain ⟨a1, ha1, hres⟩ := bind_tc_eq_ok hres
        obtain ⟨i2, hi2, hres⟩ := bind_tc_eq_ok hres
        cases ok_inj hres
        have hi2v : i2.val = i.val + 1 := usize_succ_ok hi2
        have e1 := copy_loop_ok cl hcl opened i r0 r1 0#usize _
          (List.getElem?_eq_getElem hlt') hr1
        have e2 := copy_loop_ok' cl hcl salts i r1 r2 0#usize _
          (List.getElem?_eq_getElem (by omega)) hr2
        refine ⟨by rw [hi2v]; omega, ?_⟩
        show a1.val.map _ = _
        rw [vec_push_ok ha1, List.map_append, hinv, hi2v]
        rw [List.take_add_one, List.take_add_one]
        simp only [rowsL, List.getElem?_map, List.getElem?_eq_getElem hlt',
          List.getElem?_eq_getElem (show i.val < salts.val.length by omega)]
        rw [List.zipWith_append (by simp; omega)]
        simp [e2, e1, hr0v]
      · rename_i hlt
        have hlt' : ¬ i.val < opened.val.length := by simpa using hlt
        cases ok_inj hres
        show a.val.map _ = _
        rw [hinv, List.take_of_length_le (by simp [rowsL]; omega),
          List.take_of_length_le (by simp [rowsL]; omega)])
    _ _ h ⟨by simp, by simp [hacc]⟩
  exact key

/-- Widening the dimensions adds the salt length to each width and keeps each height. -/
theorem widen_loop_ok (SALT : Std.Usize) (dims : Slice p3_matrix.Dimensions)
    (acc out : alloc.vec.Vec p3_matrix.Dimensions) (hacc : acc.val = [])
    (h : mmcs.hax_reshaped.hiding_verify_batch_loop1 SALT dims acc 0#usize = RustM.ok out) :
    out.val.map (fun d => d.height) = dims.val.map (fun d => d.height) ∧
      out.val.map (fun d => d.width.val) = dims.val.map (fun d => d.width.val + SALT.val) := by
  unfold mmcs.hax_reshaped.hiding_verify_batch_loop1 at h
  have key := loop_inv _
    (fun x : alloc.vec.Vec p3_matrix.Dimensions × Std.Usize =>
      x.2.val ≤ dims.val.length ∧
      x.1.val.map (fun d => d.height) = (dims.val.take x.2.val).map (fun d => d.height) ∧
      x.1.val.map (fun d => d.width.val) =
        (dims.val.take x.2.val).map (fun d => d.width.val + SALT.val))
    (fun r : alloc.vec.Vec p3_matrix.Dimensions =>
      r.val.map (fun d => d.height) = dims.val.map (fun d => d.height) ∧
      r.val.map (fun d => d.width.val) = dims.val.map (fun d => d.width.val + SALT.val))
    (by
      rintro ⟨a, i⟩ ⟨hi, hh, hw⟩ res hres
      dsimp only at hi hh hw hres
      unfold mmcs.hax_reshaped.hiding_verify_batch_loop1.body at hres
      obtain ⟨l, hl, hres⟩ := bind_tc_eq_ok hres
      simp only [core.slice.Slice.len] at hl
      cases ok_inj hl
      split at hres
      · rename_i hlt
        have hlt' : i.val < dims.val.length := by simpa using hlt
        obtain ⟨d, hd, hres⟩ := bind_tc_eq_ok hres
        obtain ⟨-, hdv⟩ := slice_index_ok hd
        rw [List.getElem?_eq_getElem hlt'] at hdv
        obtain ⟨w, hw', hres⟩ := bind_tc_eq_ok hres
        obtain ⟨a1, ha1, hres⟩ := bind_tc_eq_ok hres
        obtain ⟨i3, hi3, hres⟩ := bind_tc_eq_ok hres
        cases ok_inj hres
        have hi3v : i3.val = i.val + 1 := usize_succ_ok hi3
        have hwv := usize_add_ok hw'
        have hd' : d = dims.val[i.val] := (Option.some.inj hdv).symm
        refine ⟨by rw [hi3v]; omega, ?_, ?_⟩
        · show a1.val.map _ = _
          rw [vec_push_ok ha1, List.map_append, hh, hi3v]
          rw [List.take_add_one, List.getElem?_eq_getElem hlt', hd']
          simp only [Option.toList_some, List.map_append, List.map_cons, List.map_nil]
        · show a1.val.map _ = _
          rw [vec_push_ok ha1, List.map_append, hw, hi3v]
          rw [List.take_add_one, List.getElem?_eq_getElem hlt']
          simp only [Option.toList_some, List.map_append, List.map_cons, List.map_nil, hwv, hd']
      · rename_i hlt
        have hlt' : ¬ i.val < dims.val.length := by simpa using hlt
        cases ok_inj hres
        refine ⟨?_, ?_⟩
        · show a.val.map _ = _
          rw [hh, List.take_of_length_le (by omega)]
        · show a.val.map _ = _
          rw [hw, List.take_of_length_le (by omega)])
    _ _ h ⟨by simp, by simp [hacc], by simp [hacc]⟩
  exact key

/-- What an accepting run of the hiding verifier did.

The plain verifier accepted the salted rows against the widened dimensions. -/
theorem hiding_accepts {P PW W H C : Type} {N DIGEST_ELEMS : Std.Usize} (SALT : Std.Usize)
    (cl : core.clone.Clone F) (cp : core.marker.Copy W)
    (dfInst : core.default.Default W) (eqInst : core.cmp.PartialEq W W)
    (hInst : p3_symmetric.hasher.CryptographicHasher H F (Std.Array W DIGEST_ELEMS))
    (cInst : p3_symmetric.compression.PseudoCompressionFunction C (Std.Array W DIGEST_ELEMS) N)
    (hcl : ∀ x, cl.clone x = RustM.ok x)
    (mt : mmcs.MerkleTreeMmcs P PW H C N DIGEST_ELEMS)
    (commit : p3_symmetric.hash.MerkleCap F (Std.Array W DIGEST_ELEMS))
    (dims : Slice p3_matrix.Dimensions) (index : Std.Usize) (opened salts : Slice (alloc.vec.Vec F))
    (siblings : Slice (Std.Array W DIGEST_ELEMS))
    (h : mmcs.hax_reshaped.hiding_verify_batch SALT cl cp dfInst eqInst hInst cInst mt commit dims
      index opened salts siblings = RustM.ok (core.result.Result.Ok ())) :
    ∃ (so : alloc.vec.Vec (alloc.vec.Vec F)) (sd : alloc.vec.Vec p3_matrix.Dimensions),
      mmcs.hax_reshaped.check_widths dims opened = RustM.ok (core.result.Result.Ok ()) ∧
      opened.val.length = salts.val.length ∧
      so.val.map (fun v => v.val) = List.zipWith (· ++ ·) (rowsL opened) (rowsL salts) ∧
      mmcs.hax_reshaped.hiding_verify_batch_loop1 SALT dims (Slice.new p3_matrix.Dimensions) 0#usize = RustM.ok sd ∧
      sd.val.map (fun d => d.height) = dims.val.map (fun d => d.height) ∧
      sd.val.map (fun d => d.width.val) = dims.val.map (fun d => d.width.val + SALT.val) ∧
      mmcs.hax_reshaped.verify_batch cl cp dfInst eqInst hInst cInst mt commit (vs sd) index (vs so)
        siblings = RustM.ok (core.result.Result.Ok ()) := by
  unfold mmcs.hax_reshaped.hiding_verify_batch at h
  obtain ⟨r, hr, g1⟩ := bind_tc_eq_ok h
  obtain ⟨cf, hcf, g2⟩ := bind_tc_eq_ok g1
  cases cf with
  | Break res => exact (from_residual_ne_ok _ _ g2).elim
  | Continue u =>
  dsimp only at g2
  have hrv := branch_continue hcf
  subst hrv
  obtain ⟨l1, hl1, g3⟩ := bind_tc_eq_ok g2
  obtain ⟨l2, hl2, g4⟩ := bind_tc_eq_ok g3
  simp only [core.slice.Slice.len] at hl1 hl2
  cases ok_inj hl1
  cases ok_inj hl2
  split at g4
  · cases ok_inj g4
  rename_i hne
  have hlen : opened.val.length = salts.val.length := by simpa using hne
  obtain ⟨a0, ha0, g5⟩ := bind_tc_eq_ok g4
  have ha0v : a0.val = [] := vec_new_val ha0
  obtain ⟨so, hso, g6⟩ := bind_tc_eq_ok g5
  obtain ⟨d0, hd0, g7⟩ := bind_tc_eq_ok g6
  have hd0v : d0 = Slice.new p3_matrix.Dimensions := vec_new_eq hd0
  subst hd0v
  obtain ⟨sd, hsd, g8⟩ := bind_tc_eq_ok g7
  obtain ⟨s1, hs1, g9⟩ := bind_tc_eq_ok g8
  obtain ⟨s2, hs2, g10⟩ := bind_tc_eq_ok g9
  have hs1v : s1 = vs sd := (ok_inj hs1).symm
  have hs2v : s2 = vs so := (ok_inj hs2).symm
  rw [hs1v, hs2v] at g10
  obtain ⟨hh, hw⟩ := widen_loop_ok SALT dims _ sd rfl hsd
  exact ⟨so, sd, hr, hlen, salt_loop_ok cl hcl opened salts hlen a0 so ha0v hso, hsd, hh, hw, g10⟩

theorem rowsL_getD_salted {so : alloc.vec.Vec (alloc.vec.Vec F)} {o s : Slice (alloc.vec.Vec F)}
    (hso : so.val.map (fun v => v.val) = List.zipWith (· ++ ·) (rowsL o) (rowsL s))
    (hlen : o.val.length = s.val.length) (m : ℕ) (hm : m < o.val.length) :
    (openedL (vs so)).getD m [] = (rowsL o).getD m [] ++ (rowsL s).getD m [] := by
  have : openedL (vs so) = so.val.map (fun v => v.val) := rfl
  rw [this, hso]
  simp only [rowsL, List.getD_eq_getElem?_getD, List.getElem?_zipWith, List.getElem?_map,
    List.getElem?_eq_getElem hm, List.getElem?_eq_getElem (show m < s.val.length by omega)]
  rfl

/-- Merkle's binding argument for the hiding commitment.

Two hiding openings at one index that both verify agree on every row and salt the verifier reads.

The exception is a collision of the hasher or the compression. -/
theorem hiding_binding {P PW W H C : Type} {N DIGEST_ELEMS : Std.Usize} (SALT : Std.Usize)
    (cl : core.clone.Clone F) (cp : core.marker.Copy W)
    (dfInst : core.default.Default W) (eqInst : core.cmp.PartialEq W W)
    (hInst : p3_symmetric.hasher.CryptographicHasher H F (Std.Array W DIGEST_ELEMS))
    (cInst : p3_symmetric.compression.PseudoCompressionFunction C (Std.Array W DIGEST_ELEMS) N)
    (mt : mmcs.MerkleTreeMmcs P PW H C N DIGEST_ELEMS)
    (h : List (List F) → Std.Array W DIGEST_ELEMS)
    (c : List (Std.Array W DIGEST_ELEMS) → Std.Array W DIGEST_ELEMS)
    (hH : HashOn hInst mt.hash h) (hC : CompressOn cInst mt.compress c)
    (hclF : ∀ x, cl.clone x = RustM.ok x)
    (hcl : ∀ x, ∃ v, cp.cloneCloneInst.clone x = RustM.ok v)
    (heq : ∀ x y, eqInst.eq x y = RustM.ok true → x = y) (hN : 2 ≤ N.val)
    (commit : p3_symmetric.hash.MerkleCap F (Std.Array W DIGEST_ELEMS))
    (dims : Slice p3_matrix.Dimensions) (index : Std.Usize)
    (o1 s1 o2 s2 : Slice (alloc.vec.Vec F)) (p1 p2 : Slice (Std.Array W DIGEST_ELEMS))
    (h1 : mmcs.hax_reshaped.hiding_verify_batch SALT cl cp dfInst eqInst hInst cInst mt commit dims
      index o1 s1 p1 = RustM.ok (core.result.Result.Ok ()))
    (h2 : mmcs.hax_reshaped.hiding_verify_batch SALT cl cp dfInst eqInst hInst cInst mt commit dims
      index o2 s2 p2 = RustM.ok (core.result.Result.Ok ())) :
    CCollision c ∨ HCollision h ∨
      ∃ sd : alloc.vec.Vec p3_matrix.Dimensions,
        mmcs.hax_reshaped.hiding_verify_batch_loop1 SALT dims (Slice.new p3_matrix.Dimensions) 0#usize =
          RustM.ok sd ∧
        ∀ m, m < dims.val.length → Reads N mt.cap_height (vs sd) m →
          (rowsL o1).getD m [] = (rowsL o2).getD m [] ∧ (rowsL s1).getD m [] = (rowsL s2).getD m [] := by
  obtain ⟨so1, sd, hw1, hl1, hso1, hsd, -, -, hv1⟩ :=
    hiding_accepts SALT cl cp dfInst eqInst hInst cInst hclF mt commit dims index o1 s1 p1 h1
  obtain ⟨so2, sd', hw2, hl2, hso2, hsd', -, -, hv2⟩ :=
    hiding_accepts SALT cl cp dfInst eqInst hInst cInst hclF mt commit dims index o2 s2 p2 h2
  rw [hsd] at hsd'; cases ok_inj hsd'
  rcases verify_binding cl cp dfInst eqInst hInst cInst mt h c hH hC hcl heq hN commit (vs sd) index
    (vs so1) (vs so2) p1 p2 hv1 hv2 with hc | hh | hall
  · exact Or.inl hc
  · exact Or.inr (Or.inl hh)
  refine Or.inr (Or.inr ⟨sd, hsd, fun m hm hr => ?_⟩)
  obtain ⟨hlo1, hwd1⟩ := check_widths_ok hw1
  obtain ⟨hlo2, hwd2⟩ := check_widths_ok hw2
  have e := hall m hr
  rw [rowsL_getD_salted hso1 hl1 m (by omega), rowsL_getD_salted hso2 hl2 m (by omega)] at e
  have hlen : ((rowsL o1).getD m []).length = ((rowsL o2).getD m []).length := by
    simp only [rowsL, List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_getElem (show m < o1.val.length by omega),
      List.getElem?_eq_getElem (show m < o2.val.length by omega), Option.map_some, Option.getD_some]
    rw [hwd1 m hm (by omega), hwd2 m hm (by omega)]
  exact List.append_inj e hlen

/-- Append a salt drawn uniformly from k-tuples to row m.

The result lands in a fixed set Q of hash inputs with probability at most |Q| / |F|^k.

Salting is injective, so at most |Q| salts land in Q. -/
theorem salt_hits_le [Fintype F] [DecidableEq F] (m : List F) (k : ℕ) (Q : Finset (List F)) :
    (Finset.univ.filter fun s : Fin k → F => m ++ List.ofFn s ∈ Q).card ≤ Q.card := by
  apply Finset.card_le_card_of_injOn (fun s => m ++ List.ofFn s)
  · intro s hs
    simpa using hs
  · intro a _ b _ hab
    exact List.ofFn_injective (List.append_cancel_left hab)

end Plonky3Lean.Proofs.MerkleTree
