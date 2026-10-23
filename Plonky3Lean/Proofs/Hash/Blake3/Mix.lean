module

public import Plonky3Lean.Proofs.Hash.Blake3.Lane

@[expose] public section

/-!
# p3-blake3: the quarter-round

`mix` is the BLAKE3 quarter-round `g`, written as eight passes over the groups, one per step.
-/

open Aeneas Aeneas.Std CoreModels
open Plonky3Lean.Spec.Blake3 Plonky3Lean.Lib

namespace Plonky3Lean.Proofs.Blake3

open p3_blake3 in
abbrev WI := U32.Insts.P3_blake3BatchLanesWord

theorem range_first :
    CoreModels.core.IteratorRange.next core.Usize.Insts.CoreIterRangeStep
      { start := 0#usize, «end» := 1#usize } =
      .ok (core.option.Option.Some (usz 0), { start := usz 1, «end» := 1#usize }) := by
  obtain ⟨i', e, hi'⟩ := range_next_some 0#usize 1#usize (by decide)
  rw [show i' = usz 1 from eq_usz (by norm_num) (by rw [hi']; rfl)] at e
  rw [e, show (0#usize : Std.Usize) = usz 0 from eq_usz (by norm_num) rfl]

theorem range_last :
    CoreModels.core.IteratorRange.next core.Usize.Insts.CoreIterRangeStep
      { start := usz 1, «end» := 1#usize } =
      .ok (core.option.Option.None, { start := usz 1, «end» := 1#usize }) :=
  range_next_none _ _ (by rw [usz_val (by norm_num)]; exact le_rfl)

theorem wadd (x y : Std.U32) : p3_blake3.U32.Insts.P3_blake3BatchLanesWord.add x y = .ok ⟨x.bv + y.bv⟩ := rfl
theorem wxor (x y : Std.U32) : p3_blake3.U32.Insts.P3_blake3BatchLanesWord.xor x y = .ok ⟨x.bv ^^^ y.bv⟩ := rfl
theorem wand (x y : Std.U32) : p3_blake3.U32.Insts.P3_blake3BatchLanesWord.and x y = .ok ⟨x.bv &&& y.bv⟩ := rfl
theorem wsplat (x : Std.U32) : p3_blake3.U32.Insts.P3_blake3BatchLanesWord.splat x = .ok x := rfl
theorem wr16 (x : Std.U32) : p3_blake3.U32.Insts.P3_blake3BatchLanesWord.rotr_16 x = .ok ⟨x.bv.rotateRight 16⟩ := u32_rotate_right_eq _ _
theorem wr12 (x : Std.U32) : p3_blake3.U32.Insts.P3_blake3BatchLanesWord.rotr_12 x = .ok ⟨x.bv.rotateRight 12⟩ := u32_rotate_right_eq _ _
theorem wr8 (x : Std.U32) : p3_blake3.U32.Insts.P3_blake3BatchLanesWord.rotr_8 x = .ok ⟨x.bv.rotateRight 8⟩ := u32_rotate_right_eq _ _
theorem wr7 (x : Std.U32) : p3_blake3.U32.Insts.P3_blake3BatchLanesWord.rotr_7 x = .ok ⟨x.bv.rotateRight 7⟩ := u32_rotate_right_eq _ _

theorem mix_loop0_eq (s m : List Word) (hs : s.length = 16) (hm : m.length = 16) (a b x : ℕ)
    (ha : a < 16) (hb : b < 16) (hx : x < 16) :
    p3_blake3.batch.compress.mix_loop0 WI { start := 0#usize, «end» := 1#usize } (grp 16#usize s)
      (grp 16#usize m) (usz a) (usz b) (usz x) =
      .ok (grp 16#usize (s.set a (s.getD a 0 + m.getD x 0 + s.getD b 0))) := by
  have hs' : s.length = (16#usize).val := hs
  have hm' : m.length = (16#usize).val := hm
  unfold p3_blake3.batch.compress.mix_loop0
  refine lane_loop _ _ _ (grp 16#usize (s.set a (s.getD a 0 + m.getD x 0 + s.getD b 0))) ?_ ?_
  · unfold p3_blake3.batch.compress.mix_loop0.body
    simp only [CoreModels.core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next,
      range_first, bind_ok, Aeneas.Std.uncurry_apply_pair, index_grp, index_arr _ _ hs' a ha, index_arr _ _ hs' b hb, index_arr _ _ hm' x hx, wadd,
      index_mut_grp, update_arr _ _ hs' a ha, set_grp]
  · unfold p3_blake3.batch.compress.mix_loop0.body
    simp only [CoreModels.core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next,
      range_last, bind_ok, Aeneas.Std.uncurry_apply_pair]

theorem mix_loop1_eq (s m : List Word) (hs : s.length = 16) (hm : m.length = 16) (a d : ℕ)
    (ha : a < 16) (hd : d < 16) :
    p3_blake3.batch.compress.mix_loop1 WI { start := 0#usize, «end» := 1#usize } (grp 16#usize s)
      (usz a) (usz d) =
      .ok (grp 16#usize (s.set d ((s.getD d 0 ^^^ s.getD a 0).rotateRight 16))) := by
  have hs' : s.length = (16#usize).val := hs
  have hm' : m.length = (16#usize).val := hm
  unfold p3_blake3.batch.compress.mix_loop1
  refine lane_loop _ _ _ (grp 16#usize (s.set d ((s.getD d 0 ^^^ s.getD a 0).rotateRight 16))) ?_ ?_
  · unfold p3_blake3.batch.compress.mix_loop1.body
    simp only [CoreModels.core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next,
      range_first, bind_ok, Aeneas.Std.uncurry_apply_pair, index_grp, index_arr _ _ hs' a ha, index_arr _ _ hs' d hd, wxor, wr16,
      index_mut_grp, update_arr _ _ hs' d hd, set_grp]
  · unfold p3_blake3.batch.compress.mix_loop1.body
    simp only [CoreModels.core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next,
      range_last, bind_ok, Aeneas.Std.uncurry_apply_pair]

theorem mix_loop2_eq (s m : List Word) (hs : s.length = 16) (hm : m.length = 16) (c d : ℕ)
    (hc : c < 16) (hd : d < 16) :
    p3_blake3.batch.compress.mix_loop2 WI { start := 0#usize, «end» := 1#usize } (grp 16#usize s)
      (usz c) (usz d) =
      .ok (grp 16#usize (s.set c (s.getD c 0 + s.getD d 0))) := by
  have hs' : s.length = (16#usize).val := hs
  have hm' : m.length = (16#usize).val := hm
  unfold p3_blake3.batch.compress.mix_loop2
  refine lane_loop _ _ _ (grp 16#usize (s.set c (s.getD c 0 + s.getD d 0))) ?_ ?_
  · unfold p3_blake3.batch.compress.mix_loop2.body
    simp only [CoreModels.core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next,
      range_first, bind_ok, Aeneas.Std.uncurry_apply_pair, index_grp, index_arr _ _ hs' c hc, index_arr _ _ hs' d hd, wadd,
      index_mut_grp, update_arr _ _ hs' c hc, set_grp]
  · unfold p3_blake3.batch.compress.mix_loop2.body
    simp only [CoreModels.core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next,
      range_last, bind_ok, Aeneas.Std.uncurry_apply_pair]

theorem mix_loop3_eq (s m : List Word) (hs : s.length = 16) (hm : m.length = 16) (b c : ℕ)
    (hb : b < 16) (hc : c < 16) :
    p3_blake3.batch.compress.mix_loop3 WI { start := 0#usize, «end» := 1#usize } (grp 16#usize s)
      (usz b) (usz c) =
      .ok (grp 16#usize (s.set b ((s.getD b 0 ^^^ s.getD c 0).rotateRight 12))) := by
  have hs' : s.length = (16#usize).val := hs
  have hm' : m.length = (16#usize).val := hm
  unfold p3_blake3.batch.compress.mix_loop3
  refine lane_loop _ _ _ (grp 16#usize (s.set b ((s.getD b 0 ^^^ s.getD c 0).rotateRight 12))) ?_ ?_
  · unfold p3_blake3.batch.compress.mix_loop3.body
    simp only [CoreModels.core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next,
      range_first, bind_ok, Aeneas.Std.uncurry_apply_pair, index_grp, index_arr _ _ hs' b hb, index_arr _ _ hs' c hc, wxor, wr12,
      index_mut_grp, update_arr _ _ hs' b hb, set_grp]
  · unfold p3_blake3.batch.compress.mix_loop3.body
    simp only [CoreModels.core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next,
      range_last, bind_ok, Aeneas.Std.uncurry_apply_pair]

theorem mix_loop4_eq (s m : List Word) (hs : s.length = 16) (hm : m.length = 16) (a b y : ℕ)
    (ha : a < 16) (hb : b < 16) (hy : y < 16) :
    p3_blake3.batch.compress.mix_loop4 WI { start := 0#usize, «end» := 1#usize } (grp 16#usize s)
      (grp 16#usize m) (usz a) (usz b) (usz y) =
      .ok (grp 16#usize (s.set a (s.getD a 0 + m.getD y 0 + s.getD b 0))) := by
  have hs' : s.length = (16#usize).val := hs
  have hm' : m.length = (16#usize).val := hm
  unfold p3_blake3.batch.compress.mix_loop4
  refine lane_loop _ _ _ (grp 16#usize (s.set a (s.getD a 0 + m.getD y 0 + s.getD b 0))) ?_ ?_
  · unfold p3_blake3.batch.compress.mix_loop4.body
    simp only [CoreModels.core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next,
      range_first, bind_ok, Aeneas.Std.uncurry_apply_pair, index_grp, index_arr _ _ hs' a ha, index_arr _ _ hs' b hb, index_arr _ _ hm' y hy, wadd,
      index_mut_grp, update_arr _ _ hs' a ha, set_grp]
  · unfold p3_blake3.batch.compress.mix_loop4.body
    simp only [CoreModels.core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next,
      range_last, bind_ok, Aeneas.Std.uncurry_apply_pair]

theorem mix_loop5_eq (s m : List Word) (hs : s.length = 16) (hm : m.length = 16) (a d : ℕ)
    (ha : a < 16) (hd : d < 16) :
    p3_blake3.batch.compress.mix_loop5 WI { start := 0#usize, «end» := 1#usize } (grp 16#usize s)
      (usz a) (usz d) =
      .ok (grp 16#usize (s.set d ((s.getD d 0 ^^^ s.getD a 0).rotateRight 8))) := by
  have hs' : s.length = (16#usize).val := hs
  have hm' : m.length = (16#usize).val := hm
  unfold p3_blake3.batch.compress.mix_loop5
  refine lane_loop _ _ _ (grp 16#usize (s.set d ((s.getD d 0 ^^^ s.getD a 0).rotateRight 8))) ?_ ?_
  · unfold p3_blake3.batch.compress.mix_loop5.body
    simp only [CoreModels.core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next,
      range_first, bind_ok, Aeneas.Std.uncurry_apply_pair, index_grp, index_arr _ _ hs' a ha, index_arr _ _ hs' d hd, wxor, wr8,
      index_mut_grp, update_arr _ _ hs' d hd, set_grp]
  · unfold p3_blake3.batch.compress.mix_loop5.body
    simp only [CoreModels.core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next,
      range_last, bind_ok, Aeneas.Std.uncurry_apply_pair]

theorem mix_loop6_eq (s m : List Word) (hs : s.length = 16) (hm : m.length = 16) (c d : ℕ)
    (hc : c < 16) (hd : d < 16) :
    p3_blake3.batch.compress.mix_loop6 WI { start := 0#usize, «end» := 1#usize } (grp 16#usize s)
      (usz c) (usz d) =
      .ok (grp 16#usize (s.set c (s.getD c 0 + s.getD d 0))) := by
  have hs' : s.length = (16#usize).val := hs
  have hm' : m.length = (16#usize).val := hm
  unfold p3_blake3.batch.compress.mix_loop6
  refine lane_loop _ _ _ (grp 16#usize (s.set c (s.getD c 0 + s.getD d 0))) ?_ ?_
  · unfold p3_blake3.batch.compress.mix_loop6.body
    simp only [CoreModels.core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next,
      range_first, bind_ok, Aeneas.Std.uncurry_apply_pair, index_grp, index_arr _ _ hs' c hc, index_arr _ _ hs' d hd, wadd,
      index_mut_grp, update_arr _ _ hs' c hc, set_grp]
  · unfold p3_blake3.batch.compress.mix_loop6.body
    simp only [CoreModels.core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next,
      range_last, bind_ok, Aeneas.Std.uncurry_apply_pair]

theorem mix_loop7_eq (s m : List Word) (hs : s.length = 16) (hm : m.length = 16) (b c : ℕ)
    (hb : b < 16) (hc : c < 16) :
    p3_blake3.batch.compress.mix_loop7 WI { start := 0#usize, «end» := 1#usize } (grp 16#usize s)
      (usz b) (usz c) =
      .ok (grp 16#usize (s.set b ((s.getD b 0 ^^^ s.getD c 0).rotateRight 7))) := by
  have hs' : s.length = (16#usize).val := hs
  have hm' : m.length = (16#usize).val := hm
  unfold p3_blake3.batch.compress.mix_loop7
  refine lane_loop _ _ _ (grp 16#usize (s.set b ((s.getD b 0 ^^^ s.getD c 0).rotateRight 7))) ?_ ?_
  · unfold p3_blake3.batch.compress.mix_loop7.body
    simp only [CoreModels.core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next,
      range_first, bind_ok, Aeneas.Std.uncurry_apply_pair, index_grp, index_arr _ _ hs' b hb, index_arr _ _ hs' c hc, wxor, wr7,
      index_mut_grp, update_arr _ _ hs' b hb, set_grp]
  · unfold p3_blake3.batch.compress.mix_loop7.body
    simp only [CoreModels.core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next,
      range_last, bind_ok, Aeneas.Std.uncurry_apply_pair]

/-- `mix` on columns or diagonals `a b c d`, with message words `x` and `y`, is the quarter-round
`g`. -/
theorem mix_eq (s m : List Word) (hs : s.length = 16) (hm : m.length = 16) (a b c d x y : ℕ)
    (ha : a < 16) (hb : b < 16) (hc : c < 16) (hd : d < 16) (hx : x < 16) (hy : y < 16) :
    p3_blake3.batch.compress.mix WI (grp 16#usize s) (grp 16#usize m)
      (Std.Array.make 4#usize [usz a, usz b, usz c, usz d])
      (Std.Array.make 2#usize [usz x, usz y]) =
      .ok (grp 16#usize (g s a b c d (m.getD x 0) (m.getD y 0))) := by
  unfold p3_blake3.batch.compress.mix
  simp (disch := simp only [List.length_cons, List.length_nil]; decide) only [index_make, bind_ok]
  simp only [UScalar.ofNatCore_val_eq, List.getElem_cons_zero, List.getElem_cons_succ]
  rw [mix_loop0_eq _ _ hs hm a b x ha hb hx, bind_ok]
  rw [mix_loop1_eq _ _ (by simp [hs]) hm a d ha hd, bind_ok]
  rw [mix_loop2_eq _ _ (by simp [hs]) hm c d hc hd, bind_ok]
  rw [mix_loop3_eq _ _ (by simp [hs]) hm b c hb hc, bind_ok]
  rw [mix_loop4_eq _ _ (by simp [hs]) hm a b y ha hb hy, bind_ok]
  rw [mix_loop5_eq _ _ (by simp [hs]) hm a d ha hd, bind_ok]
  rw [mix_loop6_eq _ _ (by simp [hs]) hm c d hc hd, bind_ok]
  rw [mix_loop7_eq _ _ (by simp [hs]) hm b c hb hc]
  simp only [add_right_comm _ (m.getD x 0), add_right_comm _ (m.getD y 0)]
  rfl

end Plonky3Lean.Proofs.Blake3
