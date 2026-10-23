module

public import Plonky3Lean.Proofs.Hash.Blake3.Chunk

@[expose] public section

/-!
# p3-blake3 on the portable backend: parents

A parent's block is the left chaining value, then the right one, compressed under the IV with a
zero counter and the parent flag.
-/

open Aeneas Aeneas.Std CoreModels
open Plonky3Lean.Spec.Blake3 Plonky3Lean.Lib

namespace Plonky3Lean.Proofs.Blake3

/-- The parent block with the first `k` words of each child copied in, the rest zero. -/
def pblock (l r : List Word) (k : ℕ) : List Word :=
  (List.range 16).map fun p => if p < 8 then (if p < k then l.getD p 0 else 0)
    else (if p - 8 < k then r.getD (p - 8) 0 else 0)

theorem length_pblock (l r : List Word) (k : ℕ) : (pblock l r k).length = 16 := by simp [pblock]

theorem pblock_succ (l r : List Word) (k : ℕ) (hk : k < 8) :
    ((pblock l r k).set k (l.getD k 0)).set (8 + k) (r.getD k 0) = pblock l r (k + 1) := by
  apply List.ext_getElem (by simp [pblock])
  intro p h1 h2
  simp only [pblock, List.getElem_set, List.getElem_map, List.getElem_range]
  split_ifs <;> first | omega | rfl | (subst_vars; rfl) | (congr 1; omega)

theorem pblock_zero (l r : List Word) : pblock l r 0 = List.replicate 16 0 := by
  apply List.ext_getElem (by simp [pblock])
  intro p h1 h2
  simp [pblock]

theorem pblock_full (l r : List Word) (hl : l.length = 8) (hr : r.length = 8) :
    pblock l r 8 = l ++ r := by
  apply List.ext_getElem (by simp [pblock, hl, hr])
  intro p h1 h2
  have hp : p < 16 := by simpa [pblock] using h1
  simp only [pblock, List.getElem_map, List.getElem_range]
  by_cases h : p < 8
  · simp [h, List.getElem_append_left (show p < l.length by omega), List.getElem?_eq_getElem (show p < l.length by omega)]
  · simp [h, List.getElem_append_right (show l.length ≤ p by omega), hl,
      List.getElem?_eq_getElem (show p - 8 < r.length by omega), show p - 8 < 8 by omega]

theorem parent_body (l r : List Word) (hl : l.length = 8) (hr : r.length = 8) (k : ℕ) (hk : k < 8) :
    p3_blake3.batch.parent_loop0_loop0.body (grp 8#usize l) (grp 8#usize r) (usz 0)
      { start := usz k, «end» := usz 8 } (grp 16#usize (pblock l r k)) =
      .ok (.cont ({ start := usz (k + 1), «end» := usz 8 }, grp 16#usize (pblock l r (k + 1)))) := by
  have hl' : l.length = (8#usize).val := hl
  have hr' : r.length = (8#usize).val := hr
  have hp : (pblock l r k).length = (16#usize).val := length_pblock ..
  have hp' : ((pblock l r k).set k (l.getD k 0)).length = (16#usize).val := by simpa using hp
  unfold p3_blake3.batch.parent_loop0_loop0.body
  simp only [CoreModels.core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next,
    range_step k (usz 8) (by rw [usz_val (by norm_num)]; exact hk), bind_ok, Aeneas.Std.uncurry_apply_pair,
    index_grp, index_arr _ _ hl' k (by simp; omega), index_mut_grp, update_arr _ _ hp k (by simp; omega),
    index_arr _ _ hr' k (by simp; omega), STATE_WORDS_eq, usz_add (show 8 + k < 2 ^ 32 by omega), set_grp,
    update_arr _ _ hp' (8 + k) (by simp; omega), pblock_succ l r k hk]

theorem parent_done (l r : List Word) (x : Std.Array (Std.Array Std.U32 16#usize) 1#usize) :
    p3_blake3.batch.parent_loop0_loop0.body (grp 8#usize l) (grp 8#usize r) (usz 0)
      { start := usz 8, «end» := usz 8 } x = .ok (.done x) := by
  unfold p3_blake3.batch.parent_loop0_loop0.body
  simp only [CoreModels.core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next, range_stop,
    bind_ok, Aeneas.Std.uncurry_apply_pair]

theorem parent_inner (l r : List Word) (hl : l.length = 8) (hr : r.length = 8) :
    p3_blake3.batch.parent_loop0_loop0 { start := 0#usize, «end» := usz 8 } (grp 8#usize l) (grp 8#usize r)
      (grp 16#usize (pblock l r 0)) (usz 0) = .ok (grp 16#usize (pblock l r 8)) := by
  unfold p3_blake3.batch.parent_loop0_loop0
  rw [lit0]
  exact loop_of_steps (fun x : CoreModels.core.ops.range.Range Std.Usize ×
        Std.Array (Std.Array Std.U32 16#usize) 1#usize =>
      p3_blake3.batch.parent_loop0_loop0.body (grp 8#usize l) (grp 8#usize r) (usz 0) x.1 x.2)
    (fun k => (({ start := usz k, «end» := usz 8 } : CoreModels.core.ops.range.Range Std.Usize),
      grp 16#usize (pblock l r k))) 8 _
    (fun k hk => parent_body l r hl hr k hk) (parent_done _ _ _)

theorem parent_eq (l r : List Word) (hl : l.length = 8) (hr : r.length = 8) (root : Std.U32) :
    p3_blake3.batch.parent WI p3_blake3.batch.Mode.HASH (grp 8#usize l) (grp 8#usize r) root =
      .ok (grp 8#usize ((compress IV (l ++ r) 0 64 (PARENT ||| root.bv)).take 8)) := by
  unfold p3_blake3.batch.parent
  rw [show WI.splat 0#u32 = .ok 0#u32 from rfl, bind_ok,
    repeat_eq _ _ _ (fun _ => rfl) (by decide), bind_ok,
    repeat_eq _ _ _ (array_clone_eq _ (fun _ => rfl)) (by decide), bind_ok]
  have h0 : (Std.Array.from (List.replicate (1#usize).val (Std.Array.from (List.replicate (16#usize).val 0#u32)
      (by simp))) (by simp) : Std.Array (Std.Array Std.U32 16#usize) 1#usize) = grp 16#usize (pblock l r 0) := by
    apply Std.Array.ext
    simp [grp_val, pblock_zero, arr]
    rfl
  rw [h0]
  unfold p3_blake3.batch.parent_loop0
  rw [lane_loop _ _ (grp 16#usize (pblock l r 8)) (grp 16#usize (pblock l r 8)) (by
      unfold p3_blake3.batch.parent_loop0.body
      simp only [CoreModels.core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next,
        range_first, bind_ok, Aeneas.Std.uncurry_apply_pair, STATE_WORDS_eq, parent_inner l r hl hr])
    (by
      unfold p3_blake3.batch.parent_loop0.body
      simp only [CoreModels.core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next,
        range_last, bind_ok, Aeneas.Std.uncurry_apply_pair]), bind_ok, state_eq, bind_ok, BLOCK_LEN_eq,
    bind_ok, lift_eq, bind_ok, cast_64, PARENT_eq, bind_ok, lift_eq, bind_ok, HASH_flags,
    zero_or_u32, lift_eq, bind_ok, pblock_full l r hl hr,
    compress_eq _ _ rfl (by simp [hl, hr])]
  rfl

end Plonky3Lean.Proofs.Blake3
