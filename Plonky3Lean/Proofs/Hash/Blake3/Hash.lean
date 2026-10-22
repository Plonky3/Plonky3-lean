module

public import Plonky3Lean.Proofs.Hash.Blake3.Tree

@[expose] public section

/-!
# p3-blake3 on the portable backend: hashing a batch

One chunk is its own root, and more chunks fold into the tree, whose root carries the root flag.
-/

open Aeneas Aeneas.Std CoreModels
open Plonky3Lean.Spec.Blake3 Plonky3Lean.Lib

namespace Plonky3Lean.Proofs.Blake3

/-- The chunks of a `len`-byte message: one at least. -/
def nchunks (len : ℕ) : ℕ := if len ≤ 1024 then 1 else (len + 1023) / 1024

/-- The digest of the `len`-byte message at byte `s` of `B`. -/
def laneDigest (B : List (BitVec 8)) (s len : ℕ) : List (BitVec 8) :=
  cvBytes (treeCv B s len 0 (nchunks len) ROOT)

/-- One group of one lane's digest. -/
def ograp (d : List (BitVec 8)) : Std.Array (Std.Array (Std.Array Std.U8 32#usize) 1#usize) 1#usize :=
  Std.Array.make 1#usize [dgrp d] (by rfl)

theorem index_ograp (d : List (BitVec 8)) : Std.Array.index_usize (ograp d) (usz 0) = .ok (dgrp d) := by
  rw [ograp, index_make _ _ _ (by rw [usz_val (by norm_num)]; simp)]
  simp [usz_val (show 0 < 2 ^ 32 by norm_num)]

theorem store_all_eq (cv : List Word) (hcv : cv.length = 8) (old : List (BitVec 8)) (hold : old.length = 32) :
    p3_blake3.batch.store_all p3_blake3.U32.Insts.P3_blake3BatchLanesBackend1 (grp 8#usize cv) (ograp old) =
      .ok (ograp (cvBytes cv)) := by
  unfold p3_blake3.batch.store_all p3_blake3.batch.store_all_loop
  refine lane_loop _ _ (ograp (cvBytes cv)) (ograp (cvBytes cv)) ?_ ?_
  · unfold p3_blake3.batch.store_all_loop.body
    simp only [CoreModels.core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next,
      range_first, bind_ok, Aeneas.Std.uncurry_apply_pair, index_ograp, index_grp]
    erw [store_digests_eq cv hcv old hold]
    rw [bind_ok, update_one, bind_ok]
    rfl
  · unfold p3_blake3.batch.store_all_loop.body
    simp only [CoreModels.core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next,
      range_last, bind_ok, Aeneas.Std.uncurry_apply_pair]

theorem div_ceil_eq (a : ℕ) (ha : a + 1024 < 2 ^ 32) :
    CoreModels.core.num.Usize.div_ceil (usz a) (usz 1024) = .ok (usz ((a + 1023) / 1024)) := by
  unfold CoreModels.core.num.Usize.div_ceil
  rw [usz_div (by omega) (by norm_num) (by norm_num), bind_ok, usz_rem (by omega) (by norm_num) (by norm_num),
    bind_ok, lit0]
  by_cases hr : a % 1024 = 0
  · rw [ite_eq_right_of_eq_false _ _ (eq_false (by
      rw [gt_iff_lt, usz_lt_iff (by norm_num) (by omega)]; omega))]
    congr 2
    omega
  · rw [ite_eq_left_of_eq_true _ _ (eq_true (by
      rw [gt_iff_lt, usz_lt_iff (by norm_num) (by omega)]; omega)), lit1,
      usz_add (by omega)]
    congr 2
    omega

theorem chunks_bound (len : ℕ) : ((len + 1023) / 1024 - 1) * 1024 ≤ len := by
  have := Nat.div_mul_le_self (len + 1023) 1024
  rw [Nat.sub_mul, one_mul]
  generalize (len + 1023) / 1024 * 1024 = t at *
  omega

theorem hash_group_eq (batch : Slice Std.U8) (s len : ℕ) (hB : s + len ≤ batch.val.length)
    (h32 : batch.val.length + 1024 < 2 ^ 32) (old : List (BitVec 8)) (hold : old.length = 32) :
    p3_blake3.batch.hash_group p3_blake3.U32.Insts.P3_blake3BatchLanesBackend1 p3_blake3.batch.Mode.HASH
      (lane1 batch s) (usz len) (ograp old) = .ok (ograp (laneDigest (sbytes batch) s len)) := by
  unfold p3_blake3.batch.hash_group laneDigest nchunks
  rw [CHUNK_LEN_eq, bind_ok]
  by_cases h : len ≤ 1024
  · rw [ite_eq_left_of_eq_true _ _ (eq_true ((usz_le_iff (by omega) (by norm_num)).2 h)), ROOT_eq, bind_ok,
      lit0, chunk_eq batch s len 0 _ (by simp) hB h32, bind_ok,
      store_all_eq _ (length_chunkCv ..) old hold, ite_eq_left_of_eq_true _ _ (eq_true h), treeCv,
      ite_eq_left_of_eq_true _ _ (eq_true le_rfl)]
  · rw [ite_eq_right_of_eq_false _ _ (eq_false (by rw [usz_le_iff (by omega) (by norm_num)]; exact h)),
      div_ceil_eq len (by omega), bind_ok, ROOT_eq, bind_ok, lit0,
      subtree_eq batch s len hB h32 _ 0 _ (by omega) (by simpa using chunks_bound len), bind_ok,
      store_all_eq _ (length_treeCv ..) old hold, ite_eq_right_of_eq_false _ _ (eq_false h)]

theorem start_lane (first len : ℕ) (h : (first + 1) * len < 2 ^ 32) (h1 : first + 1 < 2 ^ 32) :
    p3_blake3.batch.hash_many_with.closure.closure.Insts.CoreOpsFunctionFnMutTupleUsizeUsize.call_mut
      (G := 1#usize) p3_blake3.U32.Insts.P3_blake3BatchLanesBackend1
      ((usz first, usz 0, usz len) : p3_blake3.batch.hash_many_with.closure.closure Std.U32 1#usize 1#usize)
      (usz 0) = .ok (usz (first * len), (usz first, usz 0, usz len)) := by
  unfold p3_blake3.batch.hash_many_with.closure.closure.Insts.CoreOpsFunctionFnMutTupleUsizeUsize.call_mut
  show (do
      let i3 ← usz 0 * (1#usize : Std.Usize)
      let i4 ← usz first + i3
      let i5 ← i4 + usz 0
      let i6 ← i5 * usz len
      RustM.ok (i6, ((usz first, usz 0, usz len) :
        p3_blake3.batch.hash_many_with.closure.closure Std.U32 1#usize 1#usize))) = _
  have hm : (usz 0 * (1#usize : Std.Usize) : RustM Std.Usize) = .ok (usz 0) := by
    rw [lit1]; exact usz_mul (a := 0) (b := 1) (by norm_num) (by norm_num) (by norm_num)
  rw [hm, bind_tc_ok, usz_add (a := first) (b := 0) (by omega), bind_tc_ok, usz_add (a := first + 0) (b := 0) (by omega),
    bind_tc_ok, usz_mul (a := first + 0 + 0) (b := len) (by simp; nlinarith) (by omega) (by nlinarith), bind_tc_ok]
  simp only [add_zero]
  rfl

end Plonky3Lean.Proofs.Blake3
