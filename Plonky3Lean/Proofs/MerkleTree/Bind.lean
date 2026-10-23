module

public import Plonky3Lean.Proofs.MerkleTree.Verify

@[expose] public section

/-!
# The single-index verifier binds every matrix it reads

Two openings at one index that both verify against one cap agree on every matrix row the verifier reads, or they exhibit a collision.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open p3_merkle_tree

namespace Plonky3Lean.Proofs.MerkleTree

/-- The verifier reads matrix `m`: it hashes the leaf rows, or it injects `m` at some level the proof walks. -/
def Reads (N cap : Std.Usize) (dims : Slice p3_matrix.Dimensions) (m : ℕ) : Prop :=
  ∃ (val : Std.Usize) (sched : alloc.vec.Vec Std.Usize) (pl : Std.Usize)
    (sched1 order : alloc.vec.Vec Std.Usize) (curr lnpt pos : Std.Usize),
    mmcs.hax_reshaped.validate_heights dims = RustM.ok (core.result.Result.Ok val) ∧
    mmcs.hax_reshaped.arity_schedule_and_proof_levels N cap dims =
      RustM.ok (core.result.Result.Ok (sched, pl)) ∧
    alloc.vec.Vec.truncate sched pl = RustM.ok sched1 ∧
    mmcs.hax_reshaped.tallest_first dims = RustM.ok order ∧
    p3_merkle_tree.merkle_tree.padded_len val N = RustM.ok curr ∧
    core.num.Usize.next_power_of_two val = RustM.ok lnpt ∧
    mmcs.hax_reshaped.verify_batch_loop1 dims order lnpt 0#usize = RustM.ok pos ∧
    ∃ k, k < order.val.length ∧ m = (ordL order).getD k 0 ∧
      (k < pos.val ∨ ∃ g ∈ injected (plan N.val (heightOf dims) (ordL order) (schedFrom sched1 0)
        curr.val pos.val), g.1 ≤ k ∧ k < g.2)

theorem result_ok_inj {T E : Type _} {a b : T}
    (h : (core.result.Result.Ok a : core.result.Result T E) = core.result.Result.Ok b) : a = b := by
  cases h; rfl

/-- Merkle's binding argument, on the extracted verifier.

Two openings at one index, under one cap and one set of dimensions, that both verify agree on every row the verifier reads, unless the hasher or the compression has a collision.

The hasher's collision is between two row lists of equal row lengths, so a hash that is collision resistant only on inputs of one length suffices. -/
theorem verify_binding {P PW F W H C : Type} {N DIGEST_ELEMS : Std.Usize}
    (cl : core.clone.Clone F) (cp : core.marker.Copy W)
    (dfInst : core.default.Default W) (eqInst : core.cmp.PartialEq W W)
    (hInst : p3_symmetric.hasher.CryptographicHasher H F (Std.Array W DIGEST_ELEMS))
    (cInst : p3_symmetric.compression.PseudoCompressionFunction C (Std.Array W DIGEST_ELEMS) N)
    (mt : mmcs.MerkleTreeMmcs P PW H C N DIGEST_ELEMS)
    (h : List (List F) → Std.Array W DIGEST_ELEMS)
    (c : List (Std.Array W DIGEST_ELEMS) → Std.Array W DIGEST_ELEMS)
    (hH : HashOn hInst mt.hash h) (hC : CompressOn cInst mt.compress c)
    (hcl : ∀ x, ∃ v, cp.cloneCloneInst.clone x = RustM.ok v)
    (heq : ∀ x y, eqInst.eq x y = RustM.ok true → x = y) (hN : 2 ≤ N.val)
    (commit : p3_symmetric.hash.MerkleCap F (Std.Array W DIGEST_ELEMS))
    (dims : Slice p3_matrix.Dimensions) (index : Std.Usize)
    (o1 o2 : Slice (alloc.vec.Vec F)) (p1 p2 : Slice (Std.Array W DIGEST_ELEMS))
    (h1 : mmcs.hax_reshaped.verify_batch cl cp dfInst eqInst hInst cInst mt commit dims index o1 p1 =
      RustM.ok (core.result.Result.Ok ()))
    (h2 : mmcs.hax_reshaped.verify_batch cl cp dfInst eqInst hInst cInst mt commit dims index o2 p2 =
      RustM.ok (core.result.Result.Ok ())) :
    CCollision c ∨ HCollision h ∨
      ∀ m, Reads N mt.cap_height dims m → (openedL o1).getD m [] = (openedL o2).getD m [] := by
  obtain ⟨val, sched, pl, sched1, order, curr, lnpt, pos, t, dflt, d01, ci1, df1, a1,
    hval, hsched, hsched1, hw1, horder, hcurr, hidx, hlnpt, hpos, hd01, ht, hdflt, hloop1, ha1,
    heq1, -⟩ := verify_accepts cl cp dfInst eqInst hInst cInst mt commit dims index o1 p1 h1
  obtain ⟨val', sched', pl', sched1', order', curr', lnpt', pos', t', dflt', d02, ci2, df2, a2,
    hval', hsched', hsched1', hw2, horder', hcurr', -, hlnpt', hpos', hd02, ht', hdflt', hloop2,
    ha2, heq2, -⟩ := verify_accepts cl cp dfInst eqInst hInst cInst mt commit dims index o2 p2 h2
  -- Everything read from the dimensions is the same in both runs.
  rw [hval] at hval'; have := result_ok_inj (ok_inj hval'); subst this
  rw [hsched] at hsched'
  have e := result_ok_inj (ok_inj hsched')
  cases e
  rw [hsched1] at hsched1'; cases ok_inj hsched1'
  rw [horder] at horder'; cases ok_inj horder'
  rw [hcurr] at hcurr'; cases ok_inj hcurr'
  rw [hlnpt] at hlnpt'; cases ok_inj hlnpt'
  rw [hpos] at hpos'; cases ok_inj hpos'
  rw [ht] at ht'; cases ok_inj ht'
  rw [hdflt] at hdflt'; cases ok_inj hdflt'
  -- The widths and the order's entries.
  obtain ⟨hl1, hwd1⟩ := check_widths_ok hw1
  obtain ⟨hl2, hwd2⟩ := check_widths_ok hw2
  have hord1 : ∀ i ∈ order.val, i.val < o1.val.length := fun i hi => hl1 ▸ tallest_first_ok horder i hi
  have hord2 : ∀ i ∈ order.val, i.val < o2.val.length := fun i hi => hl2 ▸ tallest_first_ok horder i hi
  have hlen : ∀ m, ((openedL o1).getD m []).length = ((openedL o2).getD m []).length := by
    intro m
    simp only [openedL, List.getD_eq_getElem?_getD, List.getElem?_map]
    by_cases hm : m < dims.val.length
    · rw [List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem (by omega)]
      simp only [Option.map_some, Option.getD_some]
      rw [hwd1 m hm (by omega), hwd2 m hm (by omega)]
    · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega)]
  -- The padding array.
  obtain ⟨padA, hpad⟩ := Lib.array_repeat_ok N
    (core.Array.Insts.CoreCloneClone DIGEST_ELEMS cp.cloneCloneInst)
    (Lib.array_clone_ok cp.cloneCloneInst hcl) dflt
  -- Both runs fold one plan.
  have w1 := walk_ok cl cp hInst cInst mt.hash mt.compress h c hH hC dims o1 p1 sched1 order dflt padA
    hpad hord1 _ index curr pos d01 0#usize 0#usize ci1 df1 rfl hloop1
  have w2 := walk_ok cl cp hInst cInst mt.hash mt.compress h c hH hC dims o2 p2 sched1 order dflt padA
    hpad hord2 _ index curr pos d02 0#usize 0#usize ci2 df2 rfl hloop2
  set pl0 := plan N.val (heightOf dims) (ordL order) (schedFrom sched1 0) curr.val pos.val
  have hci : ci1 = ci2 := by
    apply UScalar.eq_of_val_eq
    have e1 := congrArg Prod.fst w1
    have e2 := congrArg Prod.fst w2
    simp only at e1 e2
    rw [e1, e2, walk_fst, walk_fst]
  subst hci
  rw [ha1] at ha2; cases ok_inj ha2
  have hdf : df1 = df2 := (array_eq_true eqInst heq heq1).symm.trans (array_eq_true eqInst heq heq2)
  -- The plan's arities are 2 or `N`.
  have hsteps : ∀ l ∈ pl0, 0 < l.1 ∧ l.1 ≤ padA.val.length := by
    intro l hl
    have hmem := plan_steps _ _ _ _ _ _ l hl
    simp only [schedFrom, List.drop_zero, List.mem_map] at hmem
    obtain ⟨s, hs, hsv⟩ := hmem
    rw [vec_truncate_ok hsched1] at hs
    rcases (arity_schedule_ok hsched).1 s (List.mem_of_mem_take hs) with h2 | hNs
    · rw [← hsv, h2]; simp; omega
    · rw [← hsv, hNs]; simp; omega
  have hb := walk_binding h c padA.val dflt (ordL order) (openedL o1) (openedL o2) p1.val p2.val hlen
    (by simp; omega) pl0 hsteps index.val 0 d01 d02
    (by
      have a := congrArg Prod.snd w1
      have b := congrArg Prod.snd w2
      simp only at a b
      exact a.symm.trans (hdf ▸ b))
  rcases hb with hc | hh | ⟨hd0, hgroups⟩
  · exact Or.inl hc
  · exact Or.inr (Or.inl hh)
  -- The leaf rows.
  have hpos_le := leaf_pos_le hpos
  have hleaf : ∀ (o : Slice (alloc.vec.Vec F)) (d0 : Std.Array W DIGEST_ELEMS),
      (∀ i ∈ order.val, i.val < o.val.length) →
      hInst.hash_iter_slices
        (core.iter.traits.collect.IntoIterator.Blanket
          (mmcs.hax_reshaped.Rows.Insts.CoreIterTraitsIteratorIteratorSharedASlice F))
        mt.hash { opened_values := o, order := vs order, pos := 0#usize, «end» := pos } =
        RustM.ok d0 →
      d0 = h (group (ordL order) (openedL o) 0 pos.val) := by
    intro o d0 hord hd0
    rw [hH _ _ (rowsList o (vs order) 0 pos.val)
      ⟨_, rfl, rows_yields o (vs order) (by rw [vs_val]; exact hord) _ 0#usize pos rfl
        (by rw [vs_val]; exact hpos_le)⟩] at hd0
    rw [← ok_inj hd0, rowsList_val o order hord]
  have e1 := hleaf o1 d01 hord1 hd01
  have e2 := hleaf o2 d02 hord2 hd02
  by_cases hg0 : group (ordL order) (openedL o1) 0 pos.val = group (ordL order) (openedL o2) 0 pos.val
  swap
  · exact Or.inr (Or.inl ⟨_, _, hg0, group_lengths _ _ _ hlen _ _, by rw [← e1, ← e2, hd0]⟩)
  refine Or.inr (Or.inr ?_)
  -- Every read row agrees.
  rintro m ⟨val'', sched'', pl'', sched1'', order'', curr'', lnpt'', pos'', hval'', hsched'',
    hsched1'', horder'', hcurr'', hlnpt'', hpos'', k, hk, hm, hread⟩
  rw [hval] at hval''; have := result_ok_inj (ok_inj hval''); subst this
  rw [hsched] at hsched''
  have e := result_ok_inj (ok_inj hsched'')
  cases e
  rw [hsched1] at hsched1''; cases ok_inj hsched1''
  rw [horder] at horder''; cases ok_inj horder''
  rw [hcurr] at hcurr''; cases ok_inj hcurr''
  rw [hlnpt] at hlnpt''; cases ok_inj hlnpt''
  rw [hpos] at hpos''; cases ok_inj hpos''
  subst hm
  have hk' : k < (ordL order).length := by rw [ordL_length]; exact hk
  rcases hread with hk0 | ⟨g, hg, hgk, hkg⟩
  · exact group_eq_get _ _ _ 0 pos.val k hg0 (Nat.zero_le _) hk0 hk'
  · exact group_eq_get _ _ _ g.1 g.2 k (hgroups g hg) hgk hkg hk'

end Plonky3Lean.Proofs.MerkleTree
