module

public import Plonky3Lean.Proofs.MerkleTree.BinaryTotal

@[expose] public section

/-!
# When the verifier accepts on the binary tree

Take arity 2 and a batch of power-of-two heights that is not empty.

The verifier accepts exactly when the opening walks the binary plan to the cap.

It returns on every input, so no opening makes it panic.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open p3_merkle_tree

namespace Plonky3Lean.Proofs.MerkleTree

variable {P PW F W H C : Type} {DIGEST_ELEMS : Std.Usize}

/-- When the verifier accepts on the binary tree over power-of-two heights.

The tallest height is 2^n, c is the cap height, and L = n - min(c, n) is the number of walked levels.

The batch is not empty.

The verifier accepts when all of these hold:

- one row per matrix, at its width
- an index below 2^n
- L siblings
- a cap of 2^min(c, n) digests
- a walk of the binary plan from the hash of the tallest rows that reaches the cap entry at its index. -/
theorem verify_ok_binary (cl : core.clone.Clone F) (cp : core.marker.Copy W)
    (dfInst : core.default.Default W) (eqInst : core.cmp.PartialEq W W)
    (hInst : p3_symmetric.hasher.CryptographicHasher H F (Std.Array W DIGEST_ELEMS))
    (cInst : p3_symmetric.compression.PseudoCompressionFunction C (Std.Array W DIGEST_ELEMS) 2#usize)
    (mt : mmcs.MerkleTreeMmcs P PW H C 2#usize DIGEST_ELEMS)
    (h : List (List F) → Std.Array W DIGEST_ELEMS)
    (c : List (Std.Array W DIGEST_ELEMS) → Std.Array W DIGEST_ELEMS)
    (hH : HashOn hInst mt.hash h) (hC : CompressOn cInst mt.compress c)
    (hcl : ∀ x, ∃ v, cp.cloneCloneInst.clone x = RustM.ok v)
    (hrefl : ∀ x, eqInst.eq x x = RustM.ok true)
    (t : W) (z : Std.Array W DIGEST_ELEMS) (ht : dfInst.default = RustM.ok t)
    (hz : core.array.repeat DIGEST_ELEMS cp.cloneCloneInst t = RustM.ok z)
    (dims : Slice p3_matrix.Dimensions) (hpow : PowHeights dims) (hne : dims.val ≠ [])
    (commit : p3_symmetric.hash.MerkleCap F (Std.Array W DIGEST_ELEMS)) (index : Std.Usize)
    (opened : Slice (alloc.vec.Vec F)) (proof : Slice (Std.Array W DIGEST_ELEMS)) :
    let n := Nat.log 2 (maxHeight dims)
    let lh := logsOf dims
    let w := walk h c [z, z] z (tallOrder lh n) (openedL opened) proof.val
      (bplan lh n n (n - min mt.cap_height.val n)) index.val 0
      (h (group (tallOrder lh n) (openedL opened) 0 (blockEnd lh n n)))
    opened.val.length = dims.val.length →
    (∀ m (hm : m < dims.val.length) (hm' : m < opened.val.length),
      (opened.val[m]).val.length = (dims.val[m]).width.val) →
    index.val < 2 ^ n →
    proof.val.length = n - min mt.cap_height.val n →
    commit.cap.val.length = 2 ^ min mt.cap_height.val n →
    commit.cap.val[w.1]? = some w.2 →
    mmcs.hax_reshaped.verify_batch cl cp dfInst eqInst hInst cInst mt commit dims index opened proof =
      RustM.ok (core.result.Result.Ok ()) := by
  intro n lh w hlen0 hw hidx hproof hcapl hcap
  obtain ⟨val, sched, pl, expected, sched1, epl, order, curr, lnpt, pos, hval, hsched, hexp, hsched1,
    hepl, horder, hcurr, hlnpt, hpos, hheights⟩ := dims_pass_binary (cap := mt.cap_height) hpow hne
  have hvm := (validate_ok_val hval).1
  obtain ⟨hv2, -, hs, hpl, hord, hpv⟩ := layout_binary hpow hval hsched horder hcurr hlnpt hpos
  have hplan := plan_eq_bplan hpow hval hsched hsched1 horder hcurr hlnpt hpos
  rw [hvm] at hv2 hs hpl hord hpv hplan
  refine verify_ok_of cl cp dfInst eqInst hInst cInst mt h c hH hC hcl ⟨t, ht⟩ hrefl (by decide) dims
    val sched pl expected sched1 epl order curr lnpt pos hval hsched hexp hsched1 hepl horder hcurr
    hlnpt hpos hheights commit index opened proof hlen0 hw ?_ (by rw [hvm, hv2]; exact hidx) ?_ ?_
  · -- One sibling per walked level.
    rw [hproof, sibSum, List.drop_zero, vec_truncate_ok hsched1,
      show (fun s : Std.Usize => s.val - 1) = (fun x => x - 1) ∘ (fun s : Std.Usize => s.val) from rfl,
      ← List.map_map, List.map_take, hs, hpl, List.take_replicate]
    simp only [List.map_replicate, List.sum_replicate, smul_eq_mul]
    simp only [n]
    omega
  · -- The cap holds as many digests as the top min(c, n) binary levels produce.
    rw [hcapl, cap_loop_ok hexp, List.map_drop, hs, hpl, List.drop_replicate, List.prod_replicate]
    congr 1
    simp only [n]
    omega
  · -- The run folds the binary plan, whatever the padding array holds.
    intro t' dflt padA ht' hdflt hpad
    rw [ht] at ht'; cases ok_inj ht'
    rw [hz] at hdflt; cases ok_inj hdflt
    simp only [show (2#usize : Std.Usize).val = 2 from rfl]
    rw [hplan, hord, hpv, walk_pad_two h c z _ _ _ padA.val (by simp) _ (bplan_steps _ _ _ _)]
    exact hcap

open Plonky3Lean.Spec.MerkleTree in
/-- Completeness on the binary tree over power-of-two heights.

The tallest height is 2^n, c is the cap height, and L = n - min(c, n).

Take the honest binary tree over matrices whose row j of matrix m is given.

For a batch that is not empty, an honest opening of leaf I verifies:

- for each matrix of height 2^e, its row I / 2^(n - e), at its width
- the siblings of the path of leaf I
- a cap holding the 2^min(c, n) top nodes. -/
theorem verify_complete_binary (cl : core.clone.Clone F) (cp : core.marker.Copy W)
    (dfInst : core.default.Default W) (eqInst : core.cmp.PartialEq W W)
    (hInst : p3_symmetric.hasher.CryptographicHasher H F (Std.Array W DIGEST_ELEMS))
    (cInst : p3_symmetric.compression.PseudoCompressionFunction C (Std.Array W DIGEST_ELEMS) 2#usize)
    (mt : mmcs.MerkleTreeMmcs P PW H C 2#usize DIGEST_ELEMS)
    (h : List (List F) → Std.Array W DIGEST_ELEMS)
    (c : List (Std.Array W DIGEST_ELEMS) → Std.Array W DIGEST_ELEMS)
    (hH : HashOn hInst mt.hash h) (hC : CompressOn cInst mt.compress c)
    (hcl : ∀ x, ∃ v, cp.cloneCloneInst.clone x = RustM.ok v)
    (hrefl : ∀ x, eqInst.eq x x = RustM.ok true)
    (t : W) (z : Std.Array W DIGEST_ELEMS) (ht : dfInst.default = RustM.ok t)
    (hz : core.array.repeat DIGEST_ELEMS cp.cloneCloneInst t = RustM.ok z)
    (dims : Slice p3_matrix.Dimensions) (hpow : PowHeights dims) (hne : dims.val ≠ [])
    (rowsOf : ℕ → ℕ → List F)
    (commit : p3_symmetric.hash.MerkleCap F (Std.Array W DIGEST_ELEMS)) (index : Std.Usize)
    (opened : Slice (alloc.vec.Vec F)) (proof : Slice (Std.Array W DIGEST_ELEMS)) :
    let n := Nat.log 2 (maxHeight dims)
    let L := n - min mt.cap_height.val n
    let lh := logsOf dims
    opened.val.length = dims.val.length →
    (∀ m (hm : m < dims.val.length) (hm' : m < opened.val.length),
      (opened.val[m]).val.length = (dims.val[m]).width.val) →
    index.val < 2 ^ n →
    (∀ m < dims.val.length, (openedL opened).getD m [] = rowsOf m (index.val / 2 ^ (n - lh.getD m 0))) →
    proof.val = path c [z, z] z (bleaf h lh n rowsOf) (bspecs h lh n rowsOf n L) index.val →
    commit.cap.val = (List.range (2 ^ min mt.cap_height.val n)).map
      (top c [z, z] z (bleaf h lh n rowsOf) (bspecs h lh n rowsOf n L)) →
    mmcs.hax_reshaped.verify_batch cl cp dfInst eqInst hInst cInst mt commit dims index opened proof =
      RustM.ok (core.result.Result.Ok ()) := by
  intro n L lh hlen0 hw hidx hop hpath hcap
  have hlh : lh.length = dims.val.length := logsOf_length dims
  refine verify_ok_binary cl cp dfInst eqInst hInst cInst mt h c hH hC hcl hrefl t z ht hz dims hpow
    hne commit index opened proof hlen0 hw hidx (by rw [hpath, length_path_bspecs])
    (by rw [hcap]; simp; rfl) ?_
  rw [hpath, bwalk_honest h c z lh n L rowsOf (openedL opened) index.val (by omega) hidx
    (fun m hm => hop m (hlh ▸ hm)), hcap]
  have hlt : index.val / 2 ^ L < 2 ^ min mt.cap_height.val n := by
    rw [Nat.div_lt_iff_lt_mul (by positivity), ← pow_add,
      show min mt.cap_height.val n + L = n by omega]
    exact hidx
  simp [hlt]

/-- A cap-size check that passes saw as many roots as the loop expects. -/
theorem check_cap_ok {N cap : Std.Usize} {dims : Slice p3_matrix.Dimensions}
    {commit : p3_symmetric.hash.MerkleCap F (Std.Array W DIGEST_ELEMS)}
    (h : mmcs.hax_reshaped.check_cap_size N cap commit dims = RustM.ok (core.result.Result.Ok ())) :
    ∃ sched pl expected, mmcs.hax_reshaped.arity_schedule_and_proof_levels N cap dims =
        RustM.ok (core.result.Result.Ok (sched, pl)) ∧
      mmcs.hax_reshaped.check_cap_size_loop sched 1#usize pl = RustM.ok expected ∧
      commit.cap.val.length = expected.val := by
  unfold mmcs.hax_reshaped.check_cap_size at h
  obtain ⟨r, hr, g1⟩ := bind_tc_eq_ok h
  obtain ⟨cf, hcf, g2⟩ := bind_tc_eq_ok g1
  cases cf with
  | Break res => exact (from_residual_ne_ok _ _ g2).elim
  | Continue sp =>
  obtain ⟨sched, pl⟩ := sp
  dsimp only at g2
  have hrv := branch_continue hcf
  subst hrv
  obtain ⟨e, he, g3⟩ := bind_tc_eq_ok g2
  obtain ⟨i, hi, g4⟩ := bind_tc_eq_ok g3
  simp only [p3_symmetric.hash.MerkleCap.num_roots, alloc.vec.Vec.len,
    rust_primitives.sequence.seq_len] at hi
  cases ok_inj hi
  split at g4
  · cases ok_inj g4
  rename_i hne
  exact ⟨sched, pl, e, hr, he, by simpa using hne⟩

/-- An accepting run passed the cap-size check. -/
theorem verify_cap_check {N : Std.Usize} (cl : core.clone.Clone F) (cp : core.marker.Copy W)
    (dfInst : core.default.Default W) (eqInst : core.cmp.PartialEq W W)
    (hInst : p3_symmetric.hasher.CryptographicHasher H F (Std.Array W DIGEST_ELEMS))
    (cInst : p3_symmetric.compression.PseudoCompressionFunction C (Std.Array W DIGEST_ELEMS) N)
    (mt : mmcs.MerkleTreeMmcs P PW H C N DIGEST_ELEMS)
    (commit : p3_symmetric.hash.MerkleCap F (Std.Array W DIGEST_ELEMS))
    (dims : Slice p3_matrix.Dimensions) (index : Std.Usize) (opened : Slice (alloc.vec.Vec F))
    (proof : Slice (Std.Array W DIGEST_ELEMS))
    (h : mmcs.hax_reshaped.verify_batch cl cp dfInst eqInst hInst cInst mt commit dims index opened
      proof = RustM.ok (core.result.Result.Ok ())) :
    mmcs.hax_reshaped.check_cap_size N mt.cap_height commit dims =
      RustM.ok (core.result.Result.Ok ()) := by
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
  obtain ⟨r1, hr1, g5⟩ := bind_tc_eq_ok g4
  obtain ⟨cf1, hcf1, g6⟩ := bind_tc_eq_ok g5
  cases cf1 with
  | Break res => exact (from_residual_ne_ok _ _ g6).elim
  | Continue u =>
  rw [hr1, branch_continue hcf1]

/-- The verifier on the binary tree over power-of-two heights, exactly.

The batch is not empty, the tallest height is 2^n, c is the cap height, and L = n - min(c, n).

The verifier accepts exactly when all of these hold:

- one row per matrix, at its width
- an index below 2^n
- L siblings
- a cap of 2^min(c, n) digests
- a walk of the binary plan from the hash of the tallest rows that reaches the cap entry at its index. -/
theorem verify_iff_binary (cl : core.clone.Clone F) (cp : core.marker.Copy W)
    (dfInst : core.default.Default W) (eqInst : core.cmp.PartialEq W W)
    (hInst : p3_symmetric.hasher.CryptographicHasher H F (Std.Array W DIGEST_ELEMS))
    (cInst : p3_symmetric.compression.PseudoCompressionFunction C (Std.Array W DIGEST_ELEMS) 2#usize)
    (mt : mmcs.MerkleTreeMmcs P PW H C 2#usize DIGEST_ELEMS)
    (h : List (List F) → Std.Array W DIGEST_ELEMS)
    (c : List (Std.Array W DIGEST_ELEMS) → Std.Array W DIGEST_ELEMS)
    (hH : HashOn hInst mt.hash h) (hC : CompressOn cInst mt.compress c)
    (hcl : ∀ x, ∃ v, cp.cloneCloneInst.clone x = RustM.ok v)
    (heq : ∀ x y, eqInst.eq x y = RustM.ok true ↔ x = y)
    (t : W) (z : Std.Array W DIGEST_ELEMS) (ht : dfInst.default = RustM.ok t)
    (hz : core.array.repeat DIGEST_ELEMS cp.cloneCloneInst t = RustM.ok z)
    (dims : Slice p3_matrix.Dimensions) (hpow : PowHeights dims) (hne : dims.val ≠ [])
    (commit : p3_symmetric.hash.MerkleCap F (Std.Array W DIGEST_ELEMS)) (index : Std.Usize)
    (opened : Slice (alloc.vec.Vec F)) (proof : Slice (Std.Array W DIGEST_ELEMS)) :
    let n := Nat.log 2 (maxHeight dims)
    let lh := logsOf dims
    let w := walk h c [z, z] z (tallOrder lh n) (openedL opened) proof.val
      (bplan lh n n (n - min mt.cap_height.val n)) index.val 0
      (h (group (tallOrder lh n) (openedL opened) 0 (blockEnd lh n n)))
    mmcs.hax_reshaped.verify_batch cl cp dfInst eqInst hInst cInst mt commit dims index opened proof =
        RustM.ok (core.result.Result.Ok ()) ↔
      opened.val.length = dims.val.length ∧
      (∀ m (hm : m < dims.val.length) (hm' : m < opened.val.length),
        (opened.val[m]).val.length = (dims.val[m]).width.val) ∧
      index.val < 2 ^ n ∧ proof.val.length = n - min mt.cap_height.val n ∧
      commit.cap.val.length = 2 ^ min mt.cap_height.val n ∧
      commit.cap.val[w.1]? = some w.2 := by
  intro n lh w
  constructor
  · intro hacc
    obtain ⟨hidx, hl, hwd, hpl, hcap⟩ := verify_accepts_binary cl cp dfInst eqInst hInst cInst mt h c
      hH hC hcl (fun x y => (heq x y).1) t z ht hz commit dims hpow index opened proof hacc
    refine ⟨hl, hwd, hidx, hpl, ?_, hcap⟩
    obtain ⟨sched, pl, expected, hsched, hexp, hcl'⟩ :=
      check_cap_ok (verify_cap_check cl cp dfInst eqInst hInst cInst mt commit dims index opened proof
        hacc)
    obtain ⟨val, sched', pl', e', s1', epl', order, curr, lnpt, pos, hval, hsched', -, -, -, horder,
      hcurr, hlnpt, hpos, -⟩ :=
      dims_pass_binary (cap := mt.cap_height) hpow hne
    rw [hsched] at hsched'
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (result_ok_inj (ok_inj hsched'))
    obtain ⟨-, -, hs, hpl', -, -⟩ := layout_binary hpow hval hsched horder hcurr hlnpt hpos
    have hvm := (validate_ok_val hval).1
    rw [hcl', cap_loop_ok hexp, List.map_drop, hs, hpl', List.drop_replicate, List.prod_replicate, hvm]
    congr 1
    simp only [n]
    omega
  · rintro ⟨hl, hwd, hidx, hpl, hcapl, hcap⟩
    exact verify_ok_binary cl cp dfInst eqInst hInst cInst mt h c hH hC hcl
      (fun x => (heq x x).2 rfl) t z ht hz dims hpow hne commit index opened proof hl hwd hidx hpl
      hcapl hcap

/-- With arity 2, the verifier returns on every opening of a batch of power-of-two heights.

No index, rows, siblings or cap make it panic or loop. -/
theorem verify_total_binary (cl : core.clone.Clone F) (cp : core.marker.Copy W)
    (dfInst : core.default.Default W) (eqInst : core.cmp.PartialEq W W)
    (hInst : p3_symmetric.hasher.CryptographicHasher H F (Std.Array W DIGEST_ELEMS))
    (cInst : p3_symmetric.compression.PseudoCompressionFunction C (Std.Array W DIGEST_ELEMS) 2#usize)
    (mt : mmcs.MerkleTreeMmcs P PW H C 2#usize DIGEST_ELEMS)
    (h : List (List F) → Std.Array W DIGEST_ELEMS)
    (c : List (Std.Array W DIGEST_ELEMS) → Std.Array W DIGEST_ELEMS)
    (hH : HashOn hInst mt.hash h) (hC : CompressOn cInst mt.compress c)
    (hcl : ∀ x, ∃ v, cp.cloneCloneInst.clone x = RustM.ok v)
    (hdf : ∃ t, dfInst.default = RustM.ok t)
    (heqt : ∀ x y, ∃ b, eqInst.eq x y = RustM.ok b)
    (dims : Slice p3_matrix.Dimensions) (hpow : PowHeights dims) (hne : dims.val ≠ [])
    (commit : p3_symmetric.hash.MerkleCap F (Std.Array W DIGEST_ELEMS)) (index : Std.Usize)
    (opened : Slice (alloc.vec.Vec F)) (proof : Slice (Std.Array W DIGEST_ELEMS)) :
    ∃ r, mmcs.hax_reshaped.verify_batch cl cp dfInst eqInst hInst cInst mt commit dims index opened
      proof = RustM.ok r :=
  verify_total cl cp dfInst eqInst hInst cInst mt h c hH hC hcl hdf heqt (by decide) dims
    (dims_pass_binary hpow hne) commit index opened proof

end Plonky3Lean.Proofs.MerkleTree
