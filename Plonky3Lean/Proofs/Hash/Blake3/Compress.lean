module

public import Plonky3Lean.Proofs.Hash.Blake3.Round

@[expose] public section

/-!
# p3-blake3: the compression function

The working vector is the chaining value, then the first four IV words, the counter's two halves,
the block length and the flags. After seven rounds, the new chaining value is the xor of its two
halves.
-/

open Aeneas Aeneas.Std CoreModels
open Plonky3Lean.Spec.Blake3 Plonky3Lean.Lib

namespace Plonky3Lean.Proofs.Blake3

theorem STATE_WORDS_eq : p3_blake3.batch.compress.STATE_WORDS = usz 8 := by
  unfold p3_blake3.batch.compress.STATE_WORDS; exact eq_usz (by norm_num) rfl

theorem from_getD (n : Std.Usize) (s : List Word) (hs : s.length = n.val) (hl) :
    Std.Array.from ((List.range n.val).map fun j => (⟨s.getD j 0⟩ : Std.U32)) hl = arr n s := by
  apply Std.Array.ext
  rw [Std.Array.from_val, arr_val _ _ hs]
  apply List.ext_getElem (by simp [hs])
  intro i h1 h2
  simp only [List.length_map] at h2
  simp [List.getElem?_eq_getElem h2]

/-- The words of an array of `u32`s. -/
def words {n : Std.Usize} (a : Std.Array Std.U32 n) : List Word := a.val.map fun x => x.bv

theorem from_fn_params (params : Std.Array Std.U32 8#usize) :
    CoreModels.core.array.from_fn 8#usize
      (p3_blake3.batch.compress.working_vector.closure.Insts.CoreOpsFunctionFnMutTupleUsizeV
        1#usize WI) params = .ok params := by
  have hpl : params.val.length = 8 := by simp
  simp only [CoreModels.core.array.from_fn]
  rw [array_from_fn_eq _ _ _ (fun k => params.val.getD k 0#u32) (fun k hk => by
    have hk' : k < 8 := hk
    simp only [p3_blake3.batch.compress.working_vector.closure.Insts.CoreOpsFunctionFnMutTupleUsizeV.call_mut]
    rw [index_usize_eq _ _ (by rw [usz_val (by omega)]; simpa [hpl] using hk'), bind_ok, wsplat,
      bind_ok]
    simp only [usz_val (show k < 2 ^ 32 by omega),
      List.getD_eq_getElem _ _ (show k < params.val.length by omega)])]
  congr 1
  apply Std.Array.ext
  rw [Std.Array.from_val]
  apply List.ext_getElem (by simp [hpl])
  intro i h1 h2
  simp [List.getElem?_eq_getElem h2]

theorem wv_word (hw : List Word) (hh : hw.length = 8) (params : Std.Array Std.U32 8#usize) (j : ℕ)
    (hj : j < 16) :
    p3_blake3.batch.compress.working_vector.closure_1.closure.Insts.CoreOpsFunctionFnMutTupleUsizeV.call_mut
      WI ((grp 8#usize hw, usz 0, params) :
        p3_blake3.batch.compress.working_vector.closure_1.closure Std.U32 1#usize) (usz j) =
      .ok (⟨(hw ++ words params).getD j 0⟩, (grp 8#usize hw, usz 0, params)) := by
  simp only [p3_blake3.batch.compress.working_vector.closure_1.closure.Insts.CoreOpsFunctionFnMutTupleUsizeV.call_mut,
    STATE_WORDS_eq]
  show (if usz j < usz 8 then do
      let a2 ← Std.Array.index_usize (grp 8#usize hw) (usz 0)
      let t ← Std.Array.index_usize a2 (usz j)
      RustM.ok (t, ((grp 8#usize hw, usz 0, params) :
        p3_blake3.batch.compress.working_vector.closure_1.closure Std.U32 1#usize))
    else do
      let i1 ← usz j - usz 8
      let t ← Std.Array.index_usize params i1
      RustM.ok (t, ((grp 8#usize hw, usz 0, params) :
        p3_blake3.batch.compress.working_vector.closure_1.closure Std.U32 1#usize))) = _
  have hpl : params.val.length = 8 := by simp
  by_cases hj8 : j < 8
  · rw [ite_eq_left_of_eq_true _ _ (eq_true ((usz_lt_iff (by omega) (by norm_num)).2 hj8)),
      index_grp, bind_tc_ok, index_arr _ _ hh _ hj8, bind_tc_ok,
      List.getD_append _ _ _ _ (by omega)]
    rfl
  · rw [ite_eq_right_of_eq_false _ _ (eq_false (mt (usz_lt_iff (by omega) (by norm_num)).1 hj8)),
      usz_sub (by omega) (by omega)]
    refine (bind_tc_ok _ _).trans ?_
    refine (congrArg (· >>= _) (index_usize_eq params (usz (j - 8))
      (by rw [usz_val (by omega)]; omega))).trans ((bind_tc_ok _ _).trans ?_)
    have e : (⟨(hw ++ words params).getD j 0⟩ : Std.U32) = params.val[j - 8] := by
      rw [List.getD_append_right _ _ _ _ (by omega), hh]
      simp [words, List.getElem?_eq_getElem (show j - 8 < params.val.length by omega)]
    simp only [usz_val (show j - 8 < 2 ^ 32 by omega), e]
    rfl

theorem wv_row (hw : List Word) (hh : hw.length = 8) (params : Std.Array Std.U32 8#usize) :
    p3_blake3.batch.compress.working_vector.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeArrayV16.call_mut
      WI ((grp 8#usize hw, params) :
        p3_blake3.batch.compress.working_vector.closure_1 Std.U32 1#usize) (usz 0) =
      .ok (arr 16#usize (hw ++ words params), (grp 8#usize hw, params)) := by
  simp only [p3_blake3.batch.compress.working_vector.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeArrayV16.call_mut,
    CoreModels.core.array.from_fn]
  show (do
      let a2 ← CoreModels.rust_primitives.slice.array_from_fn 16#usize
        (p3_blake3.batch.compress.working_vector.closure_1.closure.Insts.CoreOpsFunctionFnMutTupleUsizeV
          1#usize WI) ((grp 8#usize hw, usz 0, params) :
            p3_blake3.batch.compress.working_vector.closure_1.closure Std.U32 1#usize)
      RustM.ok (a2, ((grp 8#usize hw, params) :
        p3_blake3.batch.compress.working_vector.closure_1 Std.U32 1#usize))) = _
  erw [array_from_fn_eq 16#usize _ _ _ (fun j hj => wv_word hw hh params j hj), bind_tc_ok]
  rw [from_getD _ _ (by simp [words, hh])]
  rfl

theorem working_vector_eq (hw : List Word) (hh : hw.length = 8) (params : Std.Array Std.U32 8#usize) :
    p3_blake3.batch.compress.working_vector WI (grp 8#usize hw) params =
      .ok (grp 16#usize (hw ++ words params)) := by
  unfold p3_blake3.batch.compress.working_vector
  rw [from_fn_params, bind_ok]
  simp only [CoreModels.core.array.from_fn]
  refine (array_from_fn_eq (F := p3_blake3.batch.compress.working_vector.closure_1 Std.U32 1#usize)
    _ _ _ (fun _ => arr 16#usize (hw ++ words params)) (fun k hk => by
      obtain rfl : k = 0 := by simpa using hk
      exact wv_row hw hh params)).trans ?_
  rfl

/-- The chaining value `h` with its first `k` words replaced by the xor of the state's halves. -/
def xorHalves (h S : List Word) (k : ℕ) : List Word :=
  (List.range 8).map fun i => if i < k then S.getD i 0 ^^^ S.getD (i + 8) 0 else h.getD i 0

theorem length_xorHalves (h S : List Word) (k : ℕ) : (xorHalves h S k).length = 8 := by
  simp [xorHalves]

theorem xorHalves_zero (h S : List Word) (hh : h.length = 8) : xorHalves h S 0 = h := by
  apply List.ext_getElem (by simp [xorHalves, hh])
  intro i h1 h2
  simp [xorHalves, List.getElem?_eq_getElem h2]

theorem xorHalves_succ (h S : List Word) (k : ℕ) (hk : k < 8) :
    (xorHalves h S k).set k (S.getD k 0 ^^^ S.getD (k + 8) 0) = xorHalves h S (k + 1) := by
  apply List.ext_getElem (by simp [xorHalves])
  intro i h1 h2
  simp only [xorHalves, List.getElem_set, List.getElem_map, List.getElem_range]
  split_ifs <;> first | omega | rfl | (subst_vars; rfl)

theorem compress_inner_body (h S : List Word) (hS : S.length = 16) (k : ℕ) (hk : k < 8) :
    p3_blake3.batch.compress.compress_loop0_loop0.body WI (grp 16#usize S) (usz 0)
      { start := usz k, «end» := usz 8 } (grp 8#usize (xorHalves h S k)) =
      .ok (.cont ({ start := usz (k + 1), «end» := usz 8 }, grp 8#usize (xorHalves h S (k + 1)))) := by
  have hS' : S.length = (16#usize).val := hS
  have hx : (xorHalves h S k).length = (8#usize).val := length_xorHalves h S k
  unfold p3_blake3.batch.compress.compress_loop0_loop0.body
  simp only [CoreModels.core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next,
    range_step k (usz 8) (by rw [usz_val (by norm_num)]; exact hk), bind_ok, index_grp,
    index_arr _ _ hS' k (by simp; omega), STATE_WORDS_eq, usz_add (show k + 8 < 2 ^ 32 by omega),
    index_arr _ _ hS' (k + 8) (by simp; omega), wxor, index_mut_grp, Aeneas.Std.uncurry_apply_pair,
    update_arr _ _ hx k (by simp; omega), set_grp, xorHalves_succ h S k hk]

theorem compress_inner_done (S : List Word) (x : Std.Array (Std.Array Std.U32 8#usize) 1#usize) :
    p3_blake3.batch.compress.compress_loop0_loop0.body WI (grp 16#usize S) (usz 0)
      { start := usz 8, «end» := usz 8 } x = .ok (.done x) := by
  unfold p3_blake3.batch.compress.compress_loop0_loop0.body
  simp only [CoreModels.core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next, range_stop,
    bind_ok, Aeneas.Std.uncurry_apply_pair]

theorem compress_inner (h S : List Word) (hh : h.length = 8) (hS : S.length = 16) :
    p3_blake3.batch.compress.compress_loop0_loop0 WI { start := 0#usize, «end» := usz 8 }
      (grp 8#usize h) (grp 16#usize S) (usz 0) = .ok (grp 8#usize (xorHalves h S 8)) := by
  unfold p3_blake3.batch.compress.compress_loop0_loop0
  rw [lit0]
  conv => lhs; rw [← xorHalves_zero h S hh]
  exact loop_of_steps (fun x : CoreModels.core.ops.range.Range Std.Usize ×
      Std.Array (Std.Array Std.U32 8#usize) 1#usize =>
      p3_blake3.batch.compress.compress_loop0_loop0.body WI (grp 16#usize S) (usz 0) x.1 x.2)
    (fun k => (({ start := usz k, «end» := usz 8 } : CoreModels.core.ops.range.Range Std.Usize),
      grp 8#usize (xorHalves h S k))) 8 _
    (fun k hk => compress_inner_body h S hS k hk) (compress_inner_done S _)

theorem compress_loop (h S : List Word) (hh : h.length = 8) (hS : S.length = 16) :
    p3_blake3.batch.compress.compress_loop0 WI { start := 0#usize, «end» := 1#usize }
      (grp 8#usize h) (grp 16#usize S) = .ok (grp 8#usize (xorHalves h S 8)) := by
  unfold p3_blake3.batch.compress.compress_loop0
  refine lane_loop _ _ _ (grp 8#usize (xorHalves h S 8)) ?_ ?_
  · unfold p3_blake3.batch.compress.compress_loop0.body
    simp only [CoreModels.core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next,
      range_first, bind_ok, Aeneas.Std.uncurry_apply_pair, STATE_WORDS_eq, compress_inner h S hh hS]
  · unfold p3_blake3.batch.compress.compress_loop0.body
    simp only [CoreModels.core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next,
      range_last, bind_ok, Aeneas.Std.uncurry_apply_pair]

theorem IV_eq : p3_blake3.batch.compress.IV = arr 8#usize IV := by
  unfold p3_blake3.batch.compress.IV
  apply Std.Array.ext
  rw [arr_val _ _ rfl]
  rfl

theorem length_round (s m : List Word) : (round s m).length = s.length := by
  simp [round, length_g]

theorem compress_loop' (h S : List Word) (hh : h.length = 8) (hS : S.length = 16) :
    p3_blake3.batch.compress.compress_loop0 WI { start := usz 0, «end» := usz 1 }
      (grp 8#usize h) (grp 16#usize S) = .ok (grp 8#usize (xorHalves h S 8)) := by
  rw [← lit0, ← lit1]
  exact compress_loop h S hh hS

theorem rounds_seven (s m : List Word) :
    rounds 7 s m = round (round (round (round (round (round (round s m) (permute^[1] m))
      (permute^[2] m)) (permute^[3] m)) (permute^[4] m)) (permute^[5] m)) (permute^[6] m) := rfl

theorem compress_take (h m : List Word) (counter : ℕ) (blockLen flags : Word) :
    (compress h m counter blockLen flags).take 8 = xorHalves h (rounds 7 (h ++ (IV.take 4 ++
      [BitVec.ofNat 32 counter, BitVec.ofNat 32 (counter / 2 ^ 32), blockLen, flags])) m) 8 := by
  simp only [compress, List.append_assoc]
  rw [List.take_left' (by simp)]
  apply List.map_congr_left
  intro i hi
  rw [ite_eq_left_of_eq_true _ _ (eq_true (List.mem_range.1 hi))]

theorem compress_eq (h m : List Word) (hh : h.length = 8) (hm : m.length = 16) (counter : Std.U64)
    (blockLen flags : Std.U32) :
    p3_blake3.batch.compress.compress WI (grp 8#usize h) (grp 16#usize m) counter blockLen flags =
      .ok (grp 8#usize ((compress h m counter.val blockLen.bv flags.bv).take 8)) := by
  unfold p3_blake3.batch.compress.compress
  rw [IV_eq]
  simp (disch := norm_num) only [ofNatCore_eq_usz]
  simp only [index_arr 8#usize IV rfl 0 (by norm_num), index_arr 8#usize IV rfl 1 (by norm_num),
    index_arr 8#usize IV rfl 2 (by norm_num), index_arr 8#usize IV rfl 3 (by norm_num),
    bind_ok, lift_eq, shiftRight_i32_eq counter 32#i32 (by decide) (by decide),
    working_vector_eq h hh]
  have hw : words (Std.Array.make 8#usize [⟨IV.getD 0 0⟩, ⟨IV.getD 1 0⟩, ⟨IV.getD 2 0⟩, ⟨IV.getD 3 0⟩,
      UScalar.cast UScalarTy.U32 counter, UScalar.cast UScalarTy.U32 (⟨counter.bv >>> I32.toNat 32#i32⟩ : Std.U64),
      blockLen, flags] (by rfl)) =
      IV.take 4 ++ [BitVec.ofNat 32 counter.val, BitVec.ofNat 32 (counter.val / 2 ^ 32), blockLen.bv,
        flags.bv] := by
    simp only [words, IV, Std.Array.make, Std.Array.from_val, List.map_cons, List.map_nil, cast_bv,
      List.take_succ_cons, List.take_zero, List.cons_append, List.nil_append]
    rw [← BitVec.ofNat_toNat, ← BitVec.ofNat_toNat, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
    rfl
  rw [hw]
  have hs0 : (h ++ (IV.take 4 ++ [BitVec.ofNat 32 counter.val, BitVec.ofNat 32 (counter.val / 2 ^ 32),
      blockLen.bv, flags.bv])).length = 16 := by simp [hh, IV]
  rw [round_eq _ m hs0 hm 0 (by norm_num), bind_ok,
    round_eq _ m (by simp only [length_round, hs0]) hm 1 (by norm_num), bind_ok,
    round_eq _ m (by simp only [length_round, hs0]) hm 2 (by norm_num), bind_ok,
    round_eq _ m (by simp only [length_round, hs0]) hm 3 (by norm_num), bind_ok,
    round_eq _ m (by simp only [length_round, hs0]) hm 4 (by norm_num), bind_ok,
    round_eq _ m (by simp only [length_round, hs0]) hm 5 (by norm_num), bind_ok,
    round_eq _ m (by simp only [length_round, hs0]) hm 6 (by norm_num), bind_ok]
  rw [compress_loop' h _ hh (by simp only [length_round, hs0])]
  rw [Function.iterate_zero_apply, ← rounds_seven, ← compress_take h m]

end Plonky3Lean.Proofs.Blake3
