module

public import Plonky3Lean.Proofs.Hash.Blake3.Bytes

@[expose] public section

/-!
# p3-blake3 on the portable backend: loading blocks from the batch

A lane's block at byte `a` of the batch, with its first `k` bytes kept and the rest zero, is a
window of the batch.
-/

open Aeneas Aeneas.Std CoreModels
open Plonky3Lean.Spec.Blake3 Plonky3Lean.Lib

namespace Plonky3Lean.Proofs.Blake3

/-- The bytes of a slice. -/
def sbytes (batch : Slice Std.U8) : List (BitVec 8) := batch.val.map UScalar.bv

/-- The 64 bytes at `a` of `B`, the first `k` kept and the rest zero. -/
def window (B : List (BitVec 8)) (a k : ℕ) : List (BitVec 8) :=
  (List.range 64).map fun p => if p < k then B.getD (a + p) 0 else 0

theorem length_window (B : List (BitVec 8)) (a k : ℕ) : (window B a k).length = 64 := by
  simp [window]

theorem window_succ (B : List (BitVec 8)) (a k : ℕ) (hk : k < 64) :
    (window B a k).set k (B.getD (a + k) 0) = window B a (k + 1) := by
  apply List.ext_getElem (by simp [window])
  intro p h1 h2
  simp only [window, List.getElem_set, List.getElem_map, List.getElem_range]
  split_ifs <;> first | omega | rfl | (subst_vars; rfl)

/-- One lane of 64-byte rows: the bytes of `d` as the only row. -/
def rgrp (d : List (BitVec 8)) : Std.Array (Std.Array Std.U8 64#usize) 1#usize :=
  Std.Array.make 1#usize [barr 64#usize d] (by rfl)

theorem rgrp_val (d : List (BitVec 8)) : (rgrp d).val = [barr 64#usize d] := by simp [rgrp]

theorem index_rgrp (d : List (BitVec 8)) :
    Std.Array.index_usize (rgrp d) (usz 0) = .ok (barr 64#usize d) := by
  rw [index_usize_eq _ _ (by rw [rgrp_val, usz_val (by norm_num)]; simp)]
  simp [rgrp_val, usz_val (show 0 < 2 ^ 32 by norm_num)]

theorem index_mut_rgrp (d : List (BitVec 8)) :
    Std.Array.index_mut_usize (rgrp d) (usz 0) =
      .ok (barr 64#usize d, fun a => Std.Array.set (rgrp d) (usz 0) a) := by
  simp only [Std.Array.index_mut_usize, index_rgrp]
  rw [bind_tc_ok]

theorem set_rgrp (d e : List (BitVec 8)) :
    Std.Array.set (rgrp d) (usz 0) (barr 64#usize e) = rgrp e := by
  apply Std.Array.ext
  simp [Std.Array.set_val_eq, rgrp_val, usz_val (show 0 < 2 ^ 32 by norm_num)]

theorem slice_index_bytes (batch : Slice Std.U8) (i : ℕ) (hi : i < batch.val.length)
    (h32 : batch.val.length < 2 ^ 32) :
    Slice.index_usize batch (usz i) = .ok ⟨(sbytes batch).getD i 0⟩ := by
  have hi' : i < 2 ^ 32 := by omega
  rw [slice_index_eq _ _ (by rw [usz_val hi']; exact hi)]
  simp [sbytes, usz_val hi', List.getElem?_eq_getElem hi]

/-- Row `0`'s byte loop, at byte `b` of `k`. -/
theorem copy_body (batch : Slice Std.U8) (a b K : ℕ) (hb : b < K) (hK : K ≤ 64)
    (hB : a + K ≤ batch.val.length) (h32 : batch.val.length < 2 ^ 32) :
    p3_blake3.batch.load_parts_loop0_loop0_loop0.body batch (usz 0) (usz a)
      { start := usz b, «end» := usz K } (rgrp (window (sbytes batch) a b)) =
      .ok (.cont ({ start := usz (b + 1), «end» := usz K }, rgrp (window (sbytes batch) a (b + 1)))) := by
  have hl : (window (sbytes batch) a b).length = (64#usize).val := length_window ..
  unfold p3_blake3.batch.load_parts_loop0_loop0_loop0.body
  simp only [CoreModels.core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next,
    range_step b (usz K) (by rw [usz_val (by omega)]; exact hb), bind_ok, Aeneas.Std.uncurry_apply_pair,
    usz_add (show a + b < 2 ^ 32 by omega), slice_index_bytes batch (a + b) (by omega) h32, index_mut_rgrp,
    update_barr _ _ hl b (by simp; omega), window_succ _ a b (by omega), set_rgrp]

theorem BLOCK_LEN_eq : blake3.BLOCK_LEN = .ok (usz 64) := by
  unfold blake3.BLOCK_LEN; exact congrArg _ (eq_usz (by norm_num) rfl)

theorem slice_len_eq (batch : Slice Std.U8) (h32 : batch.val.length < 2 ^ 32) :
    CoreModels.core.slice.Slice.len batch = .ok (usz batch.val.length) := by
  simp only [CoreModels.core.slice.Slice.len, CoreModels.rust_primitives.slice.slice_length]
  exact congrArg RustM.ok (eq_usz h32 rfl)

theorem massert_true (p : Prop) [Decidable p] (h : p) : massert p = .ok () := by
  simp [massert, h]

theorem window_zero (B : List (BitVec 8)) (a : ℕ) : window B a 0 = List.replicate 64 0 := by
  simp [window, List.map_const']

theorem zero_row : CoreModels.core.array.repeat 64#usize CoreModels.core.U8.Insts.CoreCloneClone 0#u8 =
    .ok (barr 64#usize (List.replicate 64 0)) := by
  rw [repeat_eq _ _ _ (fun _ => rfl) (by decide)]
  apply congrArg RustM.ok
  apply Std.Array.ext
  rw [Std.Array.from_val, barr_val _ _ (by simp)]
  simp
  rfl

theorem zero_rows (d : List (BitVec 8)) :
    CoreModels.core.array.repeat 1#usize (CoreModels.core.Array.Insts.CoreCloneClone 64#usize
      CoreModels.core.U8.Insts.CoreCloneClone) (barr 64#usize d) = .ok (rgrp d) := by
  rw [repeat_eq _ _ _ (array_clone_eq _ (fun _ => rfl)) (by decide)]
  apply congrArg RustM.ok
  apply Std.Array.ext
  simp [rgrp_val]

theorem each_ref_rgrp (d : List (BitVec 8)) :
    CoreModels.core.array.Array.each_ref (rgrp d) = .ok (rgrp d) := by
  unfold CoreModels.core.array.Array.each_ref
  rw [array_from_fn_eq 1#usize _ _ (fun _ => barr 64#usize d) (fun k hk => by
    obtain rfl : k = 0 := by simpa using hk
    simp only [CoreModels.core.array.Array.each_ref.closure.Insts.CoreOpsFunctionFnMutTupleUsizeSharedT.call_mut,
      CoreModels.rust_primitives.slice.array_index]
    rw [slice_index_eq _ _ (by simp [rgrp_val, usz_val (show 0 < 2 ^ 32 by norm_num)]), bind_ok]
    simp [rgrp_val, usz_val (show 0 < 2 ^ 32 by norm_num)])]
  apply congrArg RustM.ok
  apply Std.Array.ext
  simp [rgrp_val]

theorem copy_done (batch : Slice Std.U8) (l x : Std.Usize) (K : Std.Usize)
    (r : Std.Array (Std.Array Std.U8 64#usize) 1#usize) :
    p3_blake3.batch.load_parts_loop0_loop0_loop0.body batch l x { start := K, «end» := K } r =
      .ok (.done r) := by
  unfold p3_blake3.batch.load_parts_loop0_loop0_loop0.body
  simp only [CoreModels.core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next, range_stop,
    bind_ok, Aeneas.Std.uncurry_apply_pair]

theorem copy_loop (batch : Slice Std.U8) (a K : ℕ) (hK : K ≤ 64) (hB : a + K ≤ batch.val.length)
    (h32 : batch.val.length < 2 ^ 32) :
    p3_blake3.batch.load_parts_loop0_loop0_loop0 { start := 0#usize, «end» := usz K } batch
      (rgrp (window (sbytes batch) a 0)) (usz 0) (usz a) = .ok (rgrp (window (sbytes batch) a K)) := by
  unfold p3_blake3.batch.load_parts_loop0_loop0_loop0
  rw [lit0]
  exact loop_of_steps (fun x : CoreModels.core.ops.range.Range Std.Usize ×
        Std.Array (Std.Array Std.U8 64#usize) 1#usize =>
      p3_blake3.batch.load_parts_loop0_loop0_loop0.body batch (usz 0) (usz a) x.1 x.2)
    (fun b => (({ start := usz b, «end» := usz K } : CoreModels.core.ops.range.Range Std.Usize),
      rgrp (window (sbytes batch) a b))) K _
    (fun b hb => copy_body batch a b K hb hK hB h32) (copy_done _ _ _ _ _)

/-- Where the only lane's message starts. -/
def sts (s : ℕ) : Std.Array (Std.Array Std.Usize 1#usize) 1#usize :=
  Std.Array.make 1#usize [Std.Array.make 1#usize [usz s] (by rfl)] (by rfl)

theorem index_sts (s : ℕ) :
    Std.Array.index_usize (sts s) (usz 0) = .ok (Std.Array.make 1#usize [usz s] (by rfl)) := by
  rw [sts, index_make _ _ _ (by rw [usz_val (by norm_num)]; simp)]
  simp [usz_val (show 0 < 2 ^ 32 by norm_num)]

theorem index_one (x : Std.Usize) :
    Std.Array.index_usize (Std.Array.make 1#usize [x] (by rfl)) (usz 0) = .ok x := by
  rw [index_make _ _ _ (by rw [usz_val (by norm_num)]; simp)]
  simp [usz_val (show 0 < 2 ^ 32 by norm_num)]

theorem rows_loop (batch : Slice Std.U8) (s off K : ℕ) (hK : K ≤ 64) (hB : s + off + K ≤ batch.val.length)
    (h32 : batch.val.length < 2 ^ 32) :
    p3_blake3.batch.load_parts_loop0_loop0 (usz K) { start := 0#usize, «end» := 1#usize } batch (sts s)
      (usz off) (usz 0) (rgrp (window (sbytes batch) (s + off) 0)) =
      .ok (rgrp (window (sbytes batch) (s + off) K)) := by
  unfold p3_blake3.batch.load_parts_loop0_loop0
  refine lane_loop _ _ _ (rgrp (window (sbytes batch) (s + off) K)) ?_ ?_
  · unfold p3_blake3.batch.load_parts_loop0_loop0.body
    simp only [CoreModels.core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next,
      range_first, bind_ok, Aeneas.Std.uncurry_apply_pair, index_sts, index_one,
      usz_add (show s + off < 2 ^ 32 by omega), copy_loop batch (s + off) K hK hB h32]
  · unfold p3_blake3.batch.load_parts_loop0_loop0.body
    simp only [CoreModels.core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next,
      range_last, bind_ok, Aeneas.Std.uncurry_apply_pair]

theorem update_one {T : Type} (b : Std.Array T 1#usize) (x : T) :
    Std.Array.update b (usz 0) x = .ok (Std.Array.make 1#usize [x] (by rfl)) := by
  have hb : b.val.length = 1 := by simp
  rw [update_eq _ _ _ (by rw [usz_val (by norm_num)]; omega)]
  apply congrArg RustM.ok
  apply Std.Array.ext
  rw [Std.Array.from_val, usz_val (by norm_num)]
  rcases hl : b.val with _ | ⟨y, _ | ⟨z, t⟩⟩ <;> simp_all

theorem make_grp (n : Std.Usize) (s : List Word) :
    Std.Array.make 1#usize [arr n s] (by rfl) = grp n s := rfl

/-- The block of the only lane, the 64 bytes at `a` of the batch with the first `k` kept. -/
abbrev wblock (batch : Slice Std.U8) (a k : ℕ) : Std.Array (Std.Array Std.U32 16#usize) 1#usize :=
  grp 16#usize (blockWords (window (sbytes batch) a k))

theorem load_outer_body (batch : Slice Std.U8) (s off : ℕ) (hB : s + off + 64 ≤ batch.val.length)
    (h32 : batch.val.length < 2 ^ 32) (blk : Std.Array (Std.Array Std.U32 16#usize) 1#usize) :
    p3_blake3.batch.load_parts_loop0.body p3_blake3.U32.Insts.P3_blake3BatchLanesBackend1 (usz 64) batch
      (sts s) (usz off) { start := 0#usize, «end» := 1#usize } blk =
      .ok (.cont ({ start := usz 1, «end» := 1#usize }, wblock batch (s + off) 64)) := by
  unfold p3_blake3.batch.load_parts_loop0.body
  simp only [CoreModels.core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next,
    range_first, bind_ok, Aeneas.Std.uncurry_apply_pair, zero_row, zero_rows,
    ← window_zero (sbytes batch) (s + off), rows_loop batch s off 64 le_rfl hB h32, each_ref_rgrp]
  rw [rgrp, load_block_eq _ (length_window ..), bind_ok, update_one, bind_ok, make_grp]

theorem usz_le_iff {a b : ℕ} (ha : a < 2 ^ 32) (hb : b < 2 ^ 32) : usz a ≤ usz b ↔ a ≤ b := by
  rw [UScalar.le_equiv, usz_val ha, usz_val hb]

theorem load_outer_done (batch : Slice Std.U8) (s off : ℕ)
    (blk : Std.Array (Std.Array Std.U32 16#usize) 1#usize) :
    p3_blake3.batch.load_parts_loop0.body p3_blake3.U32.Insts.P3_blake3BatchLanesBackend1 (usz 64) batch
      (sts s) (usz off) { start := usz 1, «end» := 1#usize } blk = .ok (.done blk) := by
  unfold p3_blake3.batch.load_parts_loop0.body
  simp only [CoreModels.core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next,
    range_last, bind_ok, Aeneas.Std.uncurry_apply_pair]

theorem load_parts_eq (batch : Slice Std.U8) (s last off : ℕ) (hl : last + off + 64 ≤ batch.val.length)
    (hB : s + off + 64 ≤ batch.val.length) (h32 : batch.val.length < 2 ^ 32) :
    p3_blake3.batch.load_parts p3_blake3.U32.Insts.P3_blake3BatchLanesBackend1 batch (sts s) (usz last)
      (usz off) = .ok (wblock batch (s + off) 64) := by
  unfold p3_blake3.batch.load_parts
  rw [usz_add (by omega), bind_ok, BLOCK_LEN_eq, bind_ok, usz_add (by omega), bind_ok,
    slice_len_eq batch h32, bind_ok,
    massert_true _ ((usz_le_iff (by omega) h32).2 hl), bind_ok,
    show p3_blake3.U32.Insts.P3_blake3BatchLanesBackend1.WordInst.splat 0#u32 = .ok 0#u32 from rfl, bind_ok,
    repeat_eq _ _ _ (fun _ => rfl) (by decide), bind_ok,
    repeat_eq _ _ _ (array_clone_eq _ (fun _ => rfl)) (by decide), bind_ok]
  unfold p3_blake3.batch.load_parts_loop0
  exact lane_loop _ _ _ _ (load_outer_body batch s off hB h32 _) (load_outer_done batch s off _)

end Plonky3Lean.Proofs.Blake3
