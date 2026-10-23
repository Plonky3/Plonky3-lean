module

public import Plonky3Lean.Proofs.Hash.Blake3.Bytes
import all Aeneas.Std.Scalar.SaturatingOps

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

theorem spill_body (batch : Slice Std.U8) (s off b K : ℕ) (hb : b < K) (hK : K ≤ 64)
    (hB : s + off + K ≤ batch.val.length) (h32 : batch.val.length < 2 ^ 32) :
    p3_blake3.batch.spill_parts_loop0_loop0_loop0.body batch (usz off) (usz 0) (usz s)
      { start := usz b, «end» := usz K } (rgrp (window (sbytes batch) (s + off) b)) =
      .ok (.cont ({ start := usz (b + 1), «end» := usz K },
        rgrp (window (sbytes batch) (s + off) (b + 1)))) := by
  have hl : (window (sbytes batch) (s + off) b).length = (64#usize).val := length_window ..
  unfold p3_blake3.batch.spill_parts_loop0_loop0_loop0.body
  simp only [CoreModels.core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next,
    range_step b (usz K) (by rw [usz_val (by omega)]; exact hb), bind_ok, Aeneas.Std.uncurry_apply_pair,
    usz_add (show s + off < 2 ^ 32 by omega), usz_add (show s + off + b < 2 ^ 32 by omega),
    slice_index_bytes batch (s + off + b) (by omega) h32, index_mut_rgrp,
    update_barr _ _ hl b (by simp; omega), window_succ _ (s + off) b (by omega), set_rgrp]

theorem spill_done (batch : Slice Std.U8) (o l x : Std.Usize) (K : Std.Usize)
    (r : Std.Array (Std.Array Std.U8 64#usize) 1#usize) :
    p3_blake3.batch.spill_parts_loop0_loop0_loop0.body batch o l x { start := K, «end» := K } r =
      .ok (.done r) := by
  unfold p3_blake3.batch.spill_parts_loop0_loop0_loop0.body
  simp only [CoreModels.core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next, range_stop,
    bind_ok, Aeneas.Std.uncurry_apply_pair]

theorem spill_loop (batch : Slice Std.U8) (s off K : ℕ) (hK : K ≤ 64) (hB : s + off + K ≤ batch.val.length)
    (h32 : batch.val.length < 2 ^ 32) :
    p3_blake3.batch.spill_parts_loop0_loop0_loop0 { start := 0#usize, «end» := usz K } batch (usz off)
      (rgrp (window (sbytes batch) (s + off) 0)) (usz 0) (usz s) =
      .ok (rgrp (window (sbytes batch) (s + off) K)) := by
  unfold p3_blake3.batch.spill_parts_loop0_loop0_loop0
  rw [lit0]
  exact loop_of_steps (fun x : CoreModels.core.ops.range.Range Std.Usize ×
        Std.Array (Std.Array Std.U8 64#usize) 1#usize =>
      p3_blake3.batch.spill_parts_loop0_loop0_loop0.body batch (usz off) (usz 0) (usz s) x.1 x.2)
    (fun b => (({ start := usz b, «end» := usz K } : CoreModels.core.ops.range.Range Std.Usize),
      rgrp (window (sbytes batch) (s + off) b))) K _
    (fun b hb => spill_body batch s off b K hb hK hB h32) (spill_done _ _ _ _ _ _)

theorem spill_rows (batch : Slice Std.U8) (s off K : ℕ) (hK : K ≤ 64) (hB : s + off + K ≤ batch.val.length)
    (h32 : batch.val.length < 2 ^ 32) :
    p3_blake3.batch.spill_parts_loop0_loop0 { start := 0#usize, «end» := 1#usize } batch (sts s)
      (usz off) (usz K) (usz 0) (rgrp (window (sbytes batch) (s + off) 0)) =
      .ok (rgrp (window (sbytes batch) (s + off) K)) := by
  unfold p3_blake3.batch.spill_parts_loop0_loop0
  refine lane_loop _ _ _ (rgrp (window (sbytes batch) (s + off) K)) ?_ ?_
  · unfold p3_blake3.batch.spill_parts_loop0_loop0.body
    simp only [CoreModels.core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next,
      range_first, bind_ok, Aeneas.Std.uncurry_apply_pair, index_sts, index_one,
      spill_loop batch s off K hK hB h32]
  · unfold p3_blake3.batch.spill_parts_loop0_loop0.body
    simp only [CoreModels.core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next,
      range_last, bind_ok, Aeneas.Std.uncurry_apply_pair]

theorem spill_parts_eq (batch : Slice Std.U8) (s off K : ℕ) (hK : K ≤ 64)
    (hB : s + off + K ≤ batch.val.length) (h32 : batch.val.length < 2 ^ 32) :
    p3_blake3.batch.spill_parts p3_blake3.U32.Insts.P3_blake3BatchLanesBackend1 batch (sts s) (usz off)
      (usz K) = .ok (wblock batch (s + off) K) := by
  unfold p3_blake3.batch.spill_parts
  rw [show p3_blake3.U32.Insts.P3_blake3BatchLanesBackend1.WordInst.splat 0#u32 = .ok 0#u32 from rfl, bind_ok,
    repeat_eq _ _ _ (fun _ => rfl) (by decide), bind_ok,
    repeat_eq _ _ _ (array_clone_eq _ (fun _ => rfl)) (by decide), bind_ok]
  unfold p3_blake3.batch.spill_parts_loop0
  refine lane_loop _ _ _ (wblock batch (s + off) K) ?_ ?_
  · unfold p3_blake3.batch.spill_parts_loop0.body
    simp only [CoreModels.core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next,
      range_first, bind_ok, Aeneas.Std.uncurry_apply_pair, zero_row, zero_rows,
      ← window_zero (sbytes batch) (s + off), spill_rows batch s off K hK hB h32, each_ref_rgrp]
    rw [rgrp, load_block_eq _ (length_window ..), bind_ok, update_one, bind_ok, make_grp]
  · unfold p3_blake3.batch.spill_parts_loop0.body
    simp only [CoreModels.core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next,
      range_last, bind_ok, Aeneas.Std.uncurry_apply_pair]

/-- Keeping the first `k` little-endian bytes of a word. -/
theorem and_mask (b₀ b₁ b₂ b₃ : BitVec 8) (k : ℕ) (hk : k ≤ 3) :
    wordOfBytes b₀ b₁ b₂ b₃ &&& ~~~((-1 : BitVec 32) <<< (8 * k)) =
      wordOfBytes (if 0 < k then b₀ else 0) (if 1 < k then b₁ else 0) (if 2 < k then b₂ else 0) 0 := by
  have hm : (-1 : BitVec 32) = BitVec.allOnes 32 := by decide
  ext i hi
  simp only [wordOfBytes, BitVec.getElem_and, BitVec.getElem_not, BitVec.getElem_shiftLeft, hm,
    BitVec.getElem_allOnes]
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl <;>
    simp
  all_goals
    rw [← BitVec.getLsbD_eq_getElem, ← BitVec.getLsbD_eq_getElem]
    repeat rw [BitVec.getLsbD_append]
    split_ifs <;> simp_all <;> omega

theorem usz_sat_sub (a b : ℕ) (ha : a < 2 ^ 32) (hb : b < 2 ^ 32) :
    CoreModels.core.num.Usize.saturating_sub (usz a) (usz b) = .ok (usz (a - b)) := by
  simp only [CoreModels.core.num.Usize.saturating_sub,
    CoreModels.rust_primitives.arithmetic.saturating_sub_usize, UScalar.saturating_sub]
  apply congrArg RustM.ok
  exact eq_usz (by omega) (by
    show (BitVec.ofNat _ (Max.max 0 ((usz a).val - (usz b).val))).toNat = a - b
    rw [usz_val ha, usz_val hb]
    simp only [zero_le, sup_of_le_right]
    exact usz_val (show a - b < 2 ^ 32 by omega))

theorem max_shl (k : ℕ) (hk : k < 32) :
    (CoreModels.core.num.U32.MAX <<< usz k : RustM Std.U32) = .ok ⟨(-1 : BitVec 32) <<< k⟩ := by
  show UScalar.shiftLeft_UScalar _ _ = _
  simp only [UScalar.shiftLeft_UScalar, UScalar.shiftLeft, usz_val (show k < 2 ^ 32 by omega)]
  rw [ite_eq_left_of_eq_true _ _ (eq_true (show k < UScalarTy.U32.numBits from hk))]
  rfl

/-- The block words with words `tail / 4` to `w` masked down to the first `tail` bytes. -/
def masked (B : List (BitVec 8)) (a K tail w : ℕ) : List Word :=
  (List.range 16).map fun i => if i < w then wordAt (window B a tail) i else wordAt (window B a K) i

theorem length_masked (B : List (BitVec 8)) (a K tail w : ℕ) : (masked B a K tail w).length = 16 := by
  simp [masked]

theorem window_getD (B : List (BitVec 8)) (a k p : ℕ) (hp : p < 64) :
    (window B a k).getD p 0 = if p < k then B.getD (a + p) 0 else 0 := by
  simp [window, List.getD_eq_getElem?_getD, hp]

theorem wordAt_window_below (B : List (BitVec 8)) (a K tail i : ℕ) (hK : tail ≤ K) (hT : tail ≤ 64)
    (hi : 4 * i + 4 ≤ tail) :
    wordAt (window B a K) i = wordAt (window B a tail) i := by
  simp only [wordAt]
  rw [window_getD _ _ _ _ (by omega), window_getD _ _ _ _ (by omega), window_getD _ _ _ _ (by omega),
    window_getD _ _ _ _ (by omega), window_getD _ _ _ _ (by omega), window_getD _ _ _ _ (by omega),
    window_getD _ _ _ _ (by omega), window_getD _ _ _ _ (by omega)]
  simp [show 4 * i < K by omega, show 4 * i + 1 < K by omega, show 4 * i + 2 < K by omega,
    show 4 * i + 3 < K by omega, show 4 * i < tail by omega, show 4 * i + 1 < tail by omega,
    show 4 * i + 2 < tail by omega, show 4 * i + 3 < tail by omega]

theorem ite_keep (c₁ c₂ c₃ : Prop) [Decidable c₁] [Decidable c₂] [Decidable c₃] (x : BitVec 8)
    (h : c₁ ∧ c₂ ↔ c₃) : (if c₁ then (if c₂ then x else 0) else 0) = (if c₃ then x else 0) := by
  by_cases h₁ : c₁ <;> by_cases h₂ : c₂ <;> simp_all

theorem wordAt_window_mask (B : List (BitVec 8)) (a K tail i : ℕ) (hK : tail ≤ K)
    (hi : tail / 4 ≤ i) (hi16 : i < 16) :
    wordAt (window B a K) i &&& ~~~((-1 : BitVec 32) <<< (8 * (tail - 4 * i))) =
      wordAt (window B a tail) i := by
  simp only [wordAt]
  rw [and_mask _ _ _ _ _ (by omega)]
  rw [window_getD _ _ _ _ (by omega), window_getD _ _ _ _ (by omega), window_getD _ _ _ _ (by omega),
    window_getD _ _ _ _ (by omega), window_getD _ _ _ _ (by omega), window_getD _ _ _ _ (by omega),
    window_getD _ _ _ _ (by omega)]
  rw [ite_keep _ _ (4 * i < tail) _ (by omega), ite_keep _ _ (4 * i + 1 < tail) _ (by omega),
    ite_keep _ _ (4 * i + 2 < tail) _ (by omega),
    ite_eq_right_of_eq_false _ _ (eq_false (show ¬ 4 * i + 3 < tail by omega))]

theorem usz_div {a b : ℕ} (ha : a < 2 ^ 32) (hb : b < 2 ^ 32) (h0 : b ≠ 0) :
    (usz a / usz b : RustM Std.Usize) = .ok (usz (a / b)) := by
  obtain ⟨z, hz, hv, -⟩ := UScalar.div_bv_spec (usz a) (y := usz b) (by rw [usz_val hb]; exact h0)
  rw [hz, eq_usz (x := z) (k := a / b) (by have := Nat.div_le_self a b; omega)
    (by rw [hv, usz_val ha, usz_val hb])]

theorem blockWords_eq (x : List (BitVec 8)) : blockWords x = (List.range 16).map (wordAt x) := rfl

theorem masked_start (B : List (BitVec 8)) (a K tail : ℕ) (hK : tail ≤ K) (hT : tail ≤ 64) :
    masked B a K tail (tail / 4) = blockWords (window B a K) := by
  rw [blockWords_eq]
  apply List.map_congr_left
  intro i hi
  split_ifs with h
  · exact (wordAt_window_below B a K tail i hK hT (by omega)).symm
  · rfl

theorem masked_full (B : List (BitVec 8)) (a K tail : ℕ) :
    masked B a K tail 16 = blockWords (window B a tail) := by
  rw [blockWords_eq]
  apply List.map_congr_left
  intro i hi
  rw [ite_eq_left_of_eq_true _ _ (eq_true (List.mem_range.1 hi))]

theorem masked_succ (B : List (BitVec 8)) (a K tail w : ℕ) (hK : tail ≤ K) (hw : tail / 4 ≤ w)
    (hw16 : w < 16) :
    (masked B a K tail w).set w ((masked B a K tail w).getD w 0 &&&
      ~~~((-1 : BitVec 32) <<< (8 * (tail - 4 * w)))) = masked B a K tail (w + 1) := by
  have hg : (masked B a K tail w).getD w 0 = wordAt (window B a K) w := by
    simp [masked, List.getD_eq_getElem?_getD, hw16]
  rw [hg, wordAt_window_mask B a K tail w hK hw hw16]
  apply List.ext_getElem (by simp [masked])
  intro p h1 h2
  simp only [masked, List.getElem_set, List.getElem_map, List.getElem_range]
  split_ifs <;> first | omega | rfl | (subst_vars; rfl)

theorem mask_inner (L : List Word) (hL : L.length = 16) (w : ℕ) (hw : w < 16) (m : Std.U32) :
    p3_blake3.batch.mask_tail_loop0_loop0 WI { start := 0#usize, «end» := 1#usize } (grp 16#usize L) (usz w) m =
      .ok (grp 16#usize (L.set w (L.getD w 0 &&& m.bv))) := by
  have hL' : L.length = (16#usize).val := hL
  unfold p3_blake3.batch.mask_tail_loop0_loop0
  refine lane_loop _ _ _ (grp 16#usize (L.set w (L.getD w 0 &&& m.bv))) ?_ ?_
  · unfold p3_blake3.batch.mask_tail_loop0_loop0.body
    simp only [CoreModels.core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next,
      range_first, bind_ok, Aeneas.Std.uncurry_apply_pair, index_grp, index_arr _ _ hL' w (by simp; omega),
      wand, index_mut_grp, update_arr _ _ hL' w (by simp; omega), set_grp, u32_bv_mk]
  · unfold p3_blake3.batch.mask_tail_loop0_loop0.body
    simp only [CoreModels.core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next,
      range_last, bind_ok, Aeneas.Std.uncurry_apply_pair]

theorem mask_inner' (L : List Word) (hL : L.length = 16) (w : ℕ) (hw : w < 16) (m : Std.U32) :
    p3_blake3.batch.mask_tail_loop0_loop0 WI { start := usz 0, «end» := usz 1 } (grp 16#usize L) (usz w) m =
      .ok (grp 16#usize (L.set w (L.getD w 0 &&& m.bv))) := by
  rw [← lit0, ← lit1]
  exact mask_inner L hL w hw m

theorem mask_body (B : List (BitVec 8)) (a K tail w : ℕ) (hK : tail ≤ K) (hT : tail < 64)
    (hw : tail / 4 ≤ w) (hw16 : w < 16) :
    p3_blake3.batch.mask_tail_loop0.body WI (usz tail) { start := usz w, «end» := usz 16 }
      (grp 16#usize (masked B a K tail w)) =
      .ok (.cont ({ start := usz (w + 1), «end» := usz 16 }, grp 16#usize (masked B a K tail (w + 1)))) := by
  unfold p3_blake3.batch.mask_tail_loop0.body
  simp (disch := norm_num) only [ofNatCore_eq_usz]
  have hk : tail - 4 * w ≤ 3 := by omega
  simp only [CoreModels.core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next,
    range_step w (usz 16) (by rw [usz_val (by norm_num)]; exact hw16), bind_ok, Aeneas.Std.uncurry_apply_pair,
    usz_mul (show 4 * w < 2 ^ 32 by omega) (by norm_num) (by omega),
    usz_sat_sub tail (4 * w) (by omega) (by omega),
    usz_mul (show 8 * (tail - 4 * w) < 2 ^ 32 by omega) (by norm_num) (by omega),
    max_shl (8 * (tail - 4 * w)) (by omega), lift_eq, wsplat]
  rw [mask_inner' _ (length_masked ..) w hw16, bind_ok, u32_not_bv, ← masked_succ B a K tail w hK hw hw16]

theorem mask_done (tail : Std.Usize) (x : Std.Array (Std.Array Std.U32 16#usize) 1#usize) :
    p3_blake3.batch.mask_tail_loop0.body WI tail { start := usz 16, «end» := usz 16 } x = .ok (.done x) := by
  unfold p3_blake3.batch.mask_tail_loop0.body
  simp only [CoreModels.core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next, range_stop,
    bind_ok, Aeneas.Std.uncurry_apply_pair]

theorem mask_tail_eq (batch : Slice Std.U8) (a K tail : ℕ) (hK : tail ≤ K) (hK64 : K ≤ 64)
    (hT : tail < 64 ∨ K = tail) :
    p3_blake3.batch.mask_tail WI (wblock batch a K) (usz tail) = .ok (wblock batch a tail) := by
  unfold p3_blake3.batch.mask_tail
  rw [BLOCK_LEN_eq, bind_ok]
  by_cases h : tail < 64
  · rw [ite_eq_left_of_eq_true _ _ (eq_true ((usz_lt_iff (by omega) (by norm_num)).2 h)),
      show (4#usize : Std.Usize) = usz 4 from eq_usz (by norm_num) rfl,
      usz_div (by omega) (by norm_num) (by norm_num), bind_ok, BLOCK_WORDS_eq]
    unfold p3_blake3.batch.mask_tail_loop0
    rw [wblock, ← masked_start _ a K tail hK (by omega), wblock, ← masked_full _ a K tail]
    have := loop_of_steps (fun x : CoreModels.core.ops.range.Range Std.Usize ×
          Std.Array (Std.Array Std.U32 16#usize) 1#usize =>
        p3_blake3.batch.mask_tail_loop0.body WI (usz tail) x.1 x.2)
      (fun k => (({ start := usz (tail / 4 + k), «end» := usz 16 } : CoreModels.core.ops.range.Range Std.Usize),
        grp 16#usize (masked (sbytes batch) a K tail (tail / 4 + k)))) (16 - tail / 4) _
      (fun k hk => mask_body _ a K tail (tail / 4 + k) hK h (by omega) (by omega))
      (by rw [show tail / 4 + (16 - tail / 4) = 16 by omega]; exact mask_done _ _)
    simpa using this
  · obtain rfl : K = tail := by omega
    rw [ite_eq_right_of_eq_false _ _ (eq_false (by rw [usz_lt_iff (by omega) (by norm_num)]; exact h))]

/-- The only lane, whose message starts at byte `s` of the batch. -/
def lane1 (batch : Slice Std.U8) (s : ℕ) : p3_blake3.batch.Lanes 1#usize 1#usize :=
  { batch := batch, starts := sts s, last := usz s }

theorem last_block_eq (batch : Slice Std.U8) (s off tail : ℕ) (hT : tail ≤ 64)
    (hB : s + off + tail ≤ batch.val.length) (h32 : batch.val.length + 64 < 2 ^ 32) :
    p3_blake3.batch.last_block p3_blake3.U32.Insts.P3_blake3BatchLanesBackend1 (lane1 batch s) (usz off)
      (usz tail) = .ok (wblock batch (s + off) tail) := by
  unfold p3_blake3.batch.last_block lane1
  dsimp only
  rw [usz_add (by omega), bind_ok, BLOCK_LEN_eq, bind_ok, usz_add (by omega), bind_ok,
    slice_len_eq batch (by omega), bind_ok]
  by_cases h : s + off + 64 ≤ batch.val.length
  · rw [ite_eq_left_of_eq_true _ _ (eq_true ((usz_le_iff (by omega) (by omega)).2 h)),
      load_parts_eq batch s s off h h (by omega), bind_ok]
    exact mask_tail_eq batch (s + off) 64 tail hT le_rfl (by omega)
  · rw [ite_eq_right_of_eq_false _ _ (eq_false (by rw [usz_le_iff (by omega) (by omega)]; exact h)),
      spill_parts_eq batch s off tail hT hB (by omega), bind_ok]
    exact mask_tail_eq batch (s + off) tail tail le_rfl hT (Or.inr rfl)

end Plonky3Lean.Proofs.Blake3
