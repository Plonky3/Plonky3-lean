module

public import Plonky3Lean.Proofs.Hash.Keccak.P3
public import Plonky3Lean.Lib.Iter

@[expose] public section

/-!
# p3-keccak: the batched hash on one lane

On the extraction target a packed state has one lane, so each group holds one message.

A message of `len` bytes is absorbed in `len / 136` whole blocks, then a final block of `len % 136` bytes closed by the padding.
-/

open Aeneas Aeneas.Std CoreModels
open Plonky3Lean.Spec.Keccak Plonky3Lean.Lib

namespace Plonky3Lean.Proofs.Keccak

/-! ## Constants -/

theorem VECTOR_LEN_eq : p3_keccak.fallback.VECTOR_LEN = usz 1 := by
  unfold p3_keccak.fallback.VECTOR_LEN
  exact ofNatCore_eq_usz _ _ (by decide)

theorem usz_lit (n : ℕ) (h) (hn : n < 2 ^ 32) : (UScalar.ofNatCore (ty := .Usize) n h) = usz n :=
  ofNatCore_eq_usz _ _ hn

theorem RATE_eq : p3_keccak.RATE = .ok (usz 136) := by
  unfold p3_keccak.RATE
  simp only [usz_lit _ _ (show 2 < 2 ^ 32 by decide), usz_lit _ _ (show 256 < 2 ^ 32 by decide),
    usz_lit _ _ (show 1600 < 2 ^ 32 by decide), usz_lit _ _ (show 8 < 2 ^ 32 by decide)]
  rw [usz_mul (by decide) (by decide) (by decide), bind_ok, usz_sub (by decide) (by decide), bind_ok,
    usz_div (by decide) (by decide) (by decide)]

theorem LAST_RATE_WORD_eq : p3_keccak.LAST_RATE_WORD = .ok (usz 16) := by
  unfold p3_keccak.LAST_RATE_WORD
  simp only [usz_lit _ _ (show 1 < 2 ^ 32 by decide), usz_lit _ _ (show 8 < 2 ^ 32 by decide)]
  rw [RATE_eq, bind_ok, usz_sub (by decide) (by decide), bind_ok, usz_div (by decide) (by decide) (by decide)]

theorem u64_shl_usz (x : Std.U64) (k : ℕ) (hk : k < 64) :
    (x <<< usz k : RustM Std.U64) = .ok ⟨x.bv <<< k⟩ := by
  show UScalar.shiftLeft_UScalar x _ = _
  simp only [UScalar.shiftLeft_UScalar, UScalar.shiftLeft, usz_val (show k < 2 ^ 32 by omega)]
  rw [ite_eq_left_of_eq_true _ _ (eq_true (show k < UScalarTy.U64.numBits from hk))]
  rfl

theorem CLOSING_MARK_eq : p3_keccak.CLOSING_MARK = .ok (0x8000000000000000#u64) := by
  unfold p3_keccak.CLOSING_MARK
  simp only [usz_lit _ _ (show 1 < 2 ^ 32 by decide), usz_lit _ _ (show 8 < 2 ^ 32 by decide)]
  rw [RATE_eq, bind_ok, usz_sub (by decide) (by decide), bind_ok, usz_rem (by decide) (by decide) (by decide),
    bind_ok, usz_mul (by decide) (by decide) (by decide), bind_ok, u64_shl_usz _ _ (by decide)]
  rfl

/-- A loop over the range `0..1`: one step, then the exit. -/
theorem loop_once {S : Type}
    (body : CoreModels.core.ops.range.Range Std.Usize × S →
      RustM (ControlFlow (CoreModels.core.ops.range.Range Std.Usize × S) S)) (x y : S)
    (h0 : body ({ start := usz 0, «end» := usz 1 }, x) = .ok (.cont ({ start := usz 1, «end» := usz 1 }, y)))
    (h1 : body ({ start := usz 1, «end» := usz 1 }, y) = .ok (.done y)) :
    loop body ({ start := usz 0, «end» := usz 1 }, x) = .ok y :=
  loop_of_steps body (fun k => ({ start := usz k, «end» := usz 1 }, if k = 0 then x else y)) 1 y
    (fun k hk => by obtain rfl : k = 0 := (by omega); simpa using h0) (by simpa using h1)

/-! ## One state word -/

theorem single_val (x : Std.U64) : (single x).val = [x] := by simp [single]

theorem pack_unpack (st : Std.Array (Std.Array Std.U64 1#usize) 25#usize) : pack (unpack st) = st := by
  apply Std.Array.ext
  have hs := st.property
  apply List.ext_getElem (by simp [pack, hs])
  intro j h1 h2
  simp only [pack, Std.Array.from_val, List.getElem_map, List.getElem_range]
  apply Std.Array.ext
  obtain ⟨y, hy⟩ := List.length_eq_one_iff.mp (st.val[j]).property
  simp [single_val, unpack, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2, hy]

theorem unpack_pack (w : List Std.U64) (hw : w.length = 25) : unpack (pack w) = w := by
  apply List.ext_getElem (by simp [unpack, pack, hw])
  intro j h1 h2
  simp [unpack, pack, single_val, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2]

theorem eq_single (a : Std.Array Std.U64 1#usize) : a = single (a.val.getD 0 0#u64) := by
  apply Std.Array.ext
  obtain ⟨y, hy⟩ := List.length_eq_one_iff.mp a.property
  simp [single_val, hy]

theorem getElem_one (a : Std.Array Std.U64 1#usize) (i : ℕ) (hi : i = 0) (h) : a.val[i]'h = a.val.getD 0 0#u64 := by
  subst hi
  simp [List.getD_eq_getElem?_getD]

/-- Word `w` of the lanes XORed with `x`. -/
def xorAt (L : List Std.U64) (w : ℕ) (x : Std.U64) : List Std.U64 := L.set w (L.getD w 0#u64 ^^^ x)

theorem length_xorAt (L : List Std.U64) (w : ℕ) (x : Std.U64) : (xorAt L w x).length = L.length := by
  simp [xorAt]

theorem xor_state_word_eq (st : Std.Array (Std.Array Std.U64 1#usize) 25#usize) (w : ℕ) (hw : w < 25)
    (v : Std.Array Std.U64 1#usize) :
    p3_keccak.hax_reshaped.xor_state_word st (usz w) v =
      .ok (pack (xorAt (unpack st) w (v.val.getD 0 0#u64))) := by
  have hs := st.property
  have hv := v.property
  unfold p3_keccak.hax_reshaped.xor_state_word p3_keccak.hax_reshaped.xor_state_word_loop
  rw [VECTOR_LEN_eq, show (0#usize : Std.Usize) = usz 0 from ofNatCore_eq_usz _ _ (by decide)]
  refine loop_once _ st _ ?_ ?_
  · show p3_keccak.hax_reshaped.xor_state_word_loop.body (usz w) v { start := usz 0, «end» := usz 1 } st = _
    unfold p3_keccak.hax_reshaped.xor_state_word_loop.body
    rw [CoreModels.core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next,
      range_step 0 _ (by rw [usz_val (by decide)]; decide), bind_ok]
    simp only [Aeneas.Std.uncurry_apply_pair]
    have h0 : (usz 0).val = 0 := usz_val (by decide)
    have hw' : (usz w).val = w := usz_val (by omega)
    have hlt : (usz w).val < st.val.length := by rw [hw', hs]; exact hw
    rw [index_usize_eq _ _ (by rw [h0, hv]; decide), bind_ok, index_usize_eq _ _ (by rw [hw', hs]; exact hw),
      bind_ok, index_usize_eq _ _ (by rw [h0, (st.val[(usz w).val]'hlt).property]; decide), bind_ok, lift_eq,
      bind_ok]
    simp only [Std.Array.index_mut_usize]
    rw [index_usize_eq _ _ (by rw [hw', hs]; exact hw)]
    simp only [bind_tc_ok, bind_ok, Aeneas.Std.uncurry_apply_pair]
    rw [update_eq _ _ _ (by rw [h0, (st.val[(usz w).val]'hlt).property]; decide), bind_ok]
    congr 3
    rw [set_single _ _ h0]
    apply Std.Array.ext
    rw [Std.Array.set_val_eq]
    apply List.ext_getElem (by simp [pack, hs])
    intro j h1 h2
    simp only [List.getElem_set, pack, Std.Array.from_val, List.getElem_map, List.getElem_range, hw',
      getElem_one _ _ h0]
    have hj : j < st.val.length := by simpa using h1
    split
    · subst j
      simp [xorAt, unpack, List.getD_eq_getElem?_getD, hs, hw]
    · rw [eq_single (st.val[j])]
      simp [xorAt, unpack, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, *]
  · show p3_keccak.hax_reshaped.xor_state_word_loop.body (usz w) v { start := usz 1, «end» := usz 1 } _ = _
    unfold p3_keccak.hax_reshaped.xor_state_word_loop.body
    rw [CoreModels.core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next, range_stop, bind_ok]
    simp

/-! ## Reading message bytes -/

/-- Arithmetic on `usize` values bounded by the value `n` of some `usize`. -/
theorem usz_add_le {a b : ℕ} (n : Std.Usize) (h : a + b ≤ n.val) :
    (usz a + usz b : RustM Std.Usize) = .ok (usz (a + b)) := by
  have hmax : (usz a).val + (usz b).val ≤ UScalar.max .Usize := by
    rw [usz_val_le n (by omega), usz_val_le n (by omega)]
    have := n.hBounds; simp only [UScalar.max]; omega
  obtain ⟨z, hz, hv⟩ := spec_imp_exists (UScalar.add_bv_spec hmax)
  rw [hz, eq_usz_le (x := z) n h (by rw [hv.1, usz_val_le n (by omega), usz_val_le n (by omega)])]

theorem usz_mul_le {a b : ℕ} (n : Std.Usize) (h : a * b ≤ n.val) (ha : a ≤ n.val) (hb : b ≤ n.val) :
    (usz a * usz b : RustM Std.Usize) = .ok (usz (a * b)) := by
  have hmax : (usz a).val * (usz b).val ≤ UScalar.max .Usize := by
    rw [usz_val_le n ha, usz_val_le n hb]
    have := n.hBounds; simp only [UScalar.max]; omega
  obtain ⟨z, hz, hv⟩ := spec_imp_exists (UScalar.mul_spec hmax)
  rw [hz, eq_usz_le (x := z) n h (by rw [hv, usz_val_le n ha, usz_val_le n hb])]

theorem usz_sub_le {a b : ℕ} (n : Std.Usize) (hb : b ≤ a) (ha : a ≤ n.val) :
    (usz a - usz b : RustM Std.Usize) = .ok (usz (a - b)) := by
  obtain ⟨z, hz, hv⟩ := spec_imp_exists
    (UScalar.sub_bv_spec (x := usz a) (y := usz b) (by rw [usz_val_le n ha, usz_val_le n (by omega)]; omega))
  rw [hz, eq_usz_le (x := z) (k := a - b) n (by omega) (by rw [hv.1, usz_val_le n ha, usz_val_le n (by omega)])]

theorem usz_div_le {a b : ℕ} (n : Std.Usize) (ha : a ≤ n.val) (hb : b ≤ n.val) (h0 : b ≠ 0) :
    (usz a / usz b : RustM Std.Usize) = .ok (usz (a / b)) := by
  obtain ⟨z, hz, hv⟩ := UScalar.div_spec (usz a) (y := usz b) (by rw [usz_val_le n hb]; exact h0)
  rw [hz, eq_usz_le (x := z) (k := a / b) n (by have := Nat.div_le_self a b; omega)
    (by rw [hv, usz_val_le n ha, usz_val_le n hb])]

theorem usz_rem_le {a b : ℕ} (n : Std.Usize) (ha : a ≤ n.val) (hb : b ≤ n.val) (h0 : b ≠ 0) :
    (usz a % usz b : RustM Std.Usize) = .ok (usz (a % b)) := by
  obtain ⟨z, hz, hv⟩ := spec_imp_exists
    (UScalar.rem_spec (usz a) (y := usz b) (by rw [usz_val_le n hb]; exact h0))
  rw [hz, eq_usz_le (x := z) (k := a % b) n (by have := Nat.mod_le a b; omega)
    (by rw [hv, usz_val_le n ha, usz_val_le n hb])]

/-- The eight bytes at `p`, zero past the end. -/
def bytes8 (input : Slice Std.U8) (p : ℕ) : Std.Array Std.U8 8#usize :=
  Std.Array.from (((input.val.drop p).take 8 ++ List.replicate 8 0#u8).take 8) (by simp)

theorem bytes8_val (input : Slice Std.U8) (p : ℕ) (hp : p + 8 ≤ input.val.length) :
    (bytes8 input p).val = (input.val.drop p).take 8 := by
  simp only [bytes8, Std.Array.from_val]
  rw [List.take_append_of_le_length (by simp; omega), List.take_take, Nat.min_self]

/-- `u64::from_le_bytes(input[p..][..8].try_into().unwrap())`. -/
theorem read_word {β : Type} (input : Slice Std.U8) (p : ℕ) (hp : p + 8 ≤ input.val.length)
    (f : Std.U64 → RustM β) :
    (do
      let s ← CoreModels.core.Slice.Insts.CoreOpsIndexIndex.index
        (CoreModels.core.ops.range.RangeFromUsize.Insts.CoreSliceIndexSliceIndexSliceSlice Std.U8) input
        { start := usz p }
      let s1 ← CoreModels.core.Slice.Insts.CoreOpsIndexIndex.index
        (CoreModels.core.ops.range.RangeToUsize.Insts.CoreSliceIndexSliceIndexSliceSlice Std.U8) s
        { «end» := 8#usize }
      let r ← CoreModels.core.Array.Insts.CoreConvertTryFromShared0SliceTryFromSliceError.try_from 8#usize
        CoreModels.core.U8.Insts.CoreMarkerCopy s1
      let a ← CoreModels.core.result.Result.unwrap CoreModels.core.array.TryFromSliceError.Insts.CoreFmtDebug r
      let x ← CoreModels.core.num.U64.from_le_bytes a
      f x) =
      f (Aeneas.Std.core.num.U64.from_le_bytes (bytes8 input p)) := by
  have hpv : (usz p).val = p := usz_val_le (Slice.len input) (by simp; omega)
  rw [slice_index_rangeFrom_eq _ _ (by rw [hpv]; omega), bind_ok,
    index_rangeTo_eq _ _ (by simp [List.slice, hpv]; omega), bind_ok,
    try_from_eq _ _ _ (by simp [List.slice, hpv]; omega) (by decide), bind_ok]
  simp only [CoreModels.core.result.Result.unwrap, CoreModels.core.num.U64.from_le_bytes,
    CoreModels.rust_primitives.arithmetic.from_le_bytes_u64]
  rw [bind_ok, bind_ok]
  congr 2
  apply Std.Array.ext
  rw [bytes8_val _ _ hp]
  simp [List.slice, hpv, List.take_take]

theorem repeat_u64 (N : Std.Usize) (hN : 0 < N.val) (v : Std.U64) :
    CoreModels.core.array.repeat N CoreModels.core.U64.Insts.CoreCloneClone v =
      .ok (Std.Array.from (List.replicate N.val v) (by simp)) :=
  repeat_eq N _ v (fun _ => rfl) hN

theorem gather_word_eq (input : Slice Std.U8) (starts : Std.Array Std.Usize 1#usize) (s : ℕ) (hs : starts.val = [usz s]) (o : ℕ)
    (hp : s + o + 8 ≤ input.val.length) :
    p3_keccak.hax_reshaped.gather_word input starts (usz o) =
      .ok (single (Aeneas.Std.core.num.U64.from_le_bytes (bytes8 input (s + o)))) := by
  have hst := starts.property
  unfold p3_keccak.hax_reshaped.gather_word p3_keccak.hax_reshaped.gather_word_loop
  rw [repeat_u64 _ (by decide), bind_ok, VECTOR_LEN_eq,
    show (0#usize : Std.Usize) = usz 0 from ofNatCore_eq_usz _ _ (by decide)]
  refine loop_once _ _ _ ?_ ?_
  · show p3_keccak.hax_reshaped.gather_word_loop.body input starts (usz o) { start := usz 0, «end» := usz 1 } _ = _
    unfold p3_keccak.hax_reshaped.gather_word_loop.body
    rw [CoreModels.core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next,
      range_step 0 _ (by rw [usz_val (by decide)]; decide), bind_ok]
    simp only [Aeneas.Std.uncurry_apply_pair]
    have h0 : (usz 0).val = 0 := usz_val (by decide)
    rw [index_usize_eq _ _ (by rw [h0, hst]; decide), bind_ok]
    have hN : (Slice.len input).val = input.val.length := by simp
    have hsv0 : starts.val[(usz 0).val]'(by rw [h0, hst]; decide) = usz s := by simp [hs, h0]
    rw [hsv0, usz_add_le (Slice.len input) (by rw [hN]; omega), bind_ok, read_word _ _ hp]
    rw [update_eq _ _ _ (by simp [h0]), bind_ok]
    congr 3
  · show p3_keccak.hax_reshaped.gather_word_loop.body input starts (usz o) { start := usz 1, «end» := usz 1 } _ = _
    unfold p3_keccak.hax_reshaped.gather_word_loop.body
    rw [CoreModels.core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next, range_stop, bind_ok]
    simp

/-! ## Whole words of a block -/

theorem massert_of (p : Prop) [Decidable p] (h : p) : massert p = .ok () := by
  simp [massert, h]

/-- The message word at byte `q`. -/
def wordAt (input : Slice Std.U8) (q : ℕ) : Std.U64 := Aeneas.Std.core.num.U64.from_le_bytes (bytes8 input q)

/-- The lanes after XORing the `n` message words from byte `p` into words `0, ..., n - 1`. -/
def absorbL (L : List Std.U64) (input : Slice Std.U8) (p n : ℕ) : List Std.U64 :=
  (List.range n).foldl (fun L j => xorAt L j (wordAt input (p + 8 * j))) L

theorem absorbL_succ (L : List Std.U64) (input : Slice Std.U8) (p n : ℕ) :
    absorbL L input p (n + 1) = xorAt (absorbL L input p n) n (wordAt input (p + 8 * n)) := by
  simp [absorbL, List.range_succ]

theorem length_absorbL (L : List Std.U64) (input : Slice Std.U8) (p n : ℕ) :
    (absorbL L input p n).length = L.length := by
  induction n with
  | zero => rfl
  | succ n ih => rw [absorbL_succ, length_xorAt, ih]

theorem absorb_words_eq (st : Std.Array (Std.Array Std.U64 1#usize) 25#usize) (input : Slice Std.U8)
    (starts : Std.Array Std.Usize 1#usize) (s : ℕ) (hs : starts.val = [usz s]) (o n : ℕ) (hn : n ≤ 17)
    (hp : s + o + 8 * n ≤ input.val.length) :
    p3_keccak.hax_reshaped.absorb_words st input starts (usz o) (usz n) =
      .ok (pack (absorbL (unpack st) input (s + o) n)) := by
  have hN : (Slice.len input).val = input.val.length := by simp
  have hnv : (usz n).val = n := usz_val (by omega)
  unfold p3_keccak.hax_reshaped.absorb_words p3_keccak.hax_reshaped.absorb_words_loop
  rw [RATE_eq, bind_ok, show (8#usize : Std.Usize) = usz 8 from ofNatCore_eq_usz _ _ (by decide),
    usz_div (by decide) (by decide) (by decide), bind_ok,
    massert_of _ (by rw [UScalar.le_equiv, hnv, usz_val (by decide)]; omega), bind_ok,
    show (0#usize : Std.Usize) = usz 0 from ofNatCore_eq_usz _ _ (by decide)]
  have h0 : st = pack (absorbL (unpack st) input (s + o) 0) := by
    simp [absorbL, pack_unpack]
  conv => lhs; arg 2; rw [h0]
  refine loop_of_steps _ (fun k => (({ start := usz k, «end» := usz n } : CoreModels.core.ops.range.Range Std.Usize),
    pack (absorbL (unpack st) input (s + o) k))) n _ ?_ ?_
  · intro k hk
    show p3_keccak.hax_reshaped.absorb_words_loop.body input starts (usz o) { start := usz k, «end» := usz n } _ = _
    unfold p3_keccak.hax_reshaped.absorb_words_loop.body
    rw [CoreModels.core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next,
      range_step k _ (by rw [hnv]; exact hk), bind_ok]
    simp only [Aeneas.Std.uncurry_apply_pair]
    rw [show (8#usize : Std.Usize) = usz 8 from ofNatCore_eq_usz _ _ (by decide),
      usz_mul (by omega) (by decide) (by omega), bind_ok,
      usz_add_le (Slice.len input) (by rw [hN]; omega), bind_ok,
      gather_word_eq _ _ s hs _ (by omega), bind_ok,
      xor_state_word_eq _ _ (by omega), bind_ok, unpack_pack _ (by simp [length_absorbL, length_unpack]),
      absorbL_succ]
    simp [single_val, wordAt, Nat.add_assoc]
  · show p3_keccak.hax_reshaped.absorb_words_loop.body input starts (usz o) { start := usz n, «end» := usz n } _ = _
    unfold p3_keccak.hax_reshaped.absorb_words_loop.body
    rw [CoreModels.core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next, range_stop, bind_ok]
    simp

theorem eight_mul (w : ℕ) (n : Std.Usize) (h : 8 * w ≤ n.val) :
    (8#usize * usz w : RustM Std.Usize) = .ok (usz (8 * w)) := by
  rw [show (8#usize : Std.Usize) = usz 8 from ofNatCore_eq_usz _ _ (by decide)]
  have hmax : (usz 8).val * (usz w).val ≤ UScalar.max .Usize := by
    rw [usz_val (by decide), usz_val_le n (by omega)]
    have := n.hBounds; simp only [UScalar.max]; omega
  obtain ⟨z, hz, hv⟩ := spec_imp_exists (UScalar.mul_spec hmax)
  rw [hz, eq_usz_le (x := z) n h (by rw [hv, usz_val (by decide), usz_val_le n (by omega)])]

/-! ## The final block -/

/-- The closing mark `0x80`, in the last byte of a word. -/
def closing : Std.U64 := 0x8000000000000000#u64

/-- The first `j` of the `t` leftover bytes from byte `q`, zero-padded to a word. -/
def tailBytes (input : Slice Std.U8) (q j : ℕ) : Std.Array Std.U8 8#usize :=
  Std.Array.from ((List.range 8).map fun i => if i < j then input.val.getD (q + i) 0#u8 else 0#u8) (by simp)

/-- The lanes after the final block of `k < 136` bytes from byte `p`, with first padding byte `d`. -/
def finalL (L : List Std.U64) (input : Slice Std.U8) (p k : ℕ) (d : Std.U8) : List Std.U64 :=
  let w := k / 8
  let t := k % 8
  let L1 := absorbL L input p w
  let marks := (⟨(UScalar.cast .U64 d).bv <<< (8 * t)⟩ : Std.U64)
  let marks1 := if w = 16 then marks ^^^ closing else marks
  let L2 := xorAt L1 w (Aeneas.Std.core.num.U64.from_le_bytes (tailBytes input (p + 8 * w) t) ^^^ marks1)
  if w ≠ 16 then xorAt L2 16 closing else L2

theorem length_finalL (L : List Std.U64) (input : Slice Std.U8) (p k : ℕ) (d : Std.U8) :
    (finalL L input p k d).length = L.length := by
  simp only [finalL]
  split <;> simp [length_xorAt, length_absorbL]

theorem tail_step (input : Slice Std.U8) (starts : Std.Array Std.Usize 1#usize) (s : ℕ) (hs : starts.val = [usz s]) (o w t j : ℕ) (hj : j < t)
    (ht : t ≤ 8) (hp : s + o + 8 * w + t ≤ input.val.length) :
    p3_keccak.hax_reshaped.absorb_final_block_loop0_loop0.body input starts (usz o) (usz w) (usz 0)
        { start := usz j, «end» := usz t } (tailBytes input (s + o + 8 * w) j) =
      .ok (.cont ({ start := usz (j + 1), «end» := usz t },
        tailBytes input (s + o + 8 * w) (j + 1))) := by
  have hN : (Slice.len input).val = input.val.length := by simp
  have hst := starts.property
  unfold p3_keccak.hax_reshaped.absorb_final_block_loop0_loop0.body
  rw [CoreModels.core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next,
    range_step j _ (by rw [usz_val (by omega)]; exact hj), bind_ok]
  simp only [Aeneas.Std.uncurry_apply_pair]
  have h0 : (usz 0).val = 0 := usz_val (by decide)
  rw [index_usize_eq _ _ (by rw [h0, hst]; decide), bind_ok]
  have hsv0 : starts.val[(usz 0).val]'(by rw [h0, hst]; decide) = usz s := by simp [hs, h0]
  rw [hsv0, usz_add_le (Slice.len input) (by rw [hN]; omega), bind_ok,
    eight_mul w (Slice.len input) (by rw [hN]; omega), bind_ok,
    usz_add_le (Slice.len input) (by rw [hN]; omega), bind_ok,
    usz_add_le (Slice.len input) (by rw [hN]; omega), bind_ok,
    slice_index_eq _ _ (by rw [usz_val_le (Slice.len input) (by rw [hN]; omega)]; omega), bind_ok,
    update_eq _ _ _ (by rw [usz_val (by omega)]; simp [tailBytes]; omega), bind_ok]
  congr 3
  apply Std.Array.ext
  simp only [tailBytes, Std.Array.from_val, usz_val (show j < 2 ^ 32 by omega),
    usz_val_le (Slice.len input) (show s + o + 8 * w + j ≤ (Slice.len input).val by rw [hN]; omega)]
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp only [List.getElem_set, List.getElem_map, List.getElem_range]
  rcases Nat.lt_trichotomy i j with h | rfl | h
  · simp [show ¬ j = i by omega, h, show i < j + 1 by omega]
  · simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show s + o + 8 * w + i < input.val.length by omega)]
  · simp [show ¬ j = i by omega, show ¬ i < j by omega, show ¬ i < j + 1 by omega]

theorem tail_loop (input : Slice Std.U8) (starts : Std.Array Std.Usize 1#usize) (s : ℕ) (hs : starts.val = [usz s]) (o w t : ℕ) (ht : t ≤ 8)
    (hp : s + o + 8 * w + t ≤ input.val.length) :
    p3_keccak.hax_reshaped.absorb_final_block_loop0_loop0 { start := usz 0, «end» := usz t } input starts (usz o)
        (usz w) (usz 0) (tailBytes input (s + o + 8 * w) 0) =
      .ok (tailBytes input (s + o + 8 * w) t) := by
  unfold p3_keccak.hax_reshaped.absorb_final_block_loop0_loop0
  refine loop_of_steps _ (fun j => (({ start := usz j, «end» := usz t } : CoreModels.core.ops.range.Range Std.Usize),
    tailBytes input (s + o + 8 * w) j)) t _
    (fun j hj => tail_step input starts s hs o w t j hj ht hp) ?_
  show p3_keccak.hax_reshaped.absorb_final_block_loop0_loop0.body input starts (usz o) (usz w) (usz 0)
    { start := usz t, «end» := usz t } _ = _
  unfold p3_keccak.hax_reshaped.absorb_final_block_loop0_loop0.body
  rw [CoreModels.core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next, range_stop, bind_ok]
  simp

theorem tailBytes_zero (input : Slice Std.U8) (q : ℕ) :
    tailBytes input q 0 = Std.Array.from (List.replicate (8#usize : Std.Usize).val 0#u8) (by simp) := by
  apply Std.Array.ext
  simp [tailBytes]

theorem repeat_u8 (N : Std.Usize) (hN : 0 < N.val) (v : Std.U8) :
    CoreModels.core.array.repeat N CoreModels.core.U8.Insts.CoreCloneClone v =
      .ok (Std.Array.from (List.replicate N.val v) (by simp)) :=
  repeat_eq N _ v (fun _ => rfl) hN

theorem value_loop (input : Slice Std.U8) (starts : Std.Array Std.Usize 1#usize) (s : ℕ) (hs : starts.val = [usz s]) (o w t : ℕ) (ht : t ≤ 8)
    (hp : s + o + 8 * w + t ≤ input.val.length) (marks : Std.U64) :
    p3_keccak.hax_reshaped.absorb_final_block_loop0 { start := usz 0, «end» := usz 1 } input starts (usz o)
        (usz w) (usz t) marks (Std.Array.from (List.replicate (1#usize : Std.Usize).val 0#u64) (by simp)) =
      .ok (single (Aeneas.Std.core.num.U64.from_le_bytes
        (tailBytes input (s + o + 8 * w) t) ^^^ marks)) := by
  unfold p3_keccak.hax_reshaped.absorb_final_block_loop0
  refine loop_once _ _ _ ?_ ?_
  · show p3_keccak.hax_reshaped.absorb_final_block_loop0.body input starts (usz o) (usz w) (usz t) marks
      { start := usz 0, «end» := usz 1 } _ = _
    unfold p3_keccak.hax_reshaped.absorb_final_block_loop0.body
    rw [CoreModels.core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next,
      range_step 0 _ (by rw [usz_val (by decide)]; decide), bind_ok]
    simp only [Aeneas.Std.uncurry_apply_pair]
    rw [repeat_u8 _ (by decide), bind_ok, ← tailBytes_zero input (s + o + 8 * w),
      show (0#usize : Std.Usize) = usz 0 from ofNatCore_eq_usz _ _ (by decide), tail_loop input starts s hs o w t ht hp, bind_ok]
    simp only [CoreModels.core.num.U64.from_le_bytes, CoreModels.rust_primitives.arithmetic.from_le_bytes_u64,
      bind_ok, lift_eq]
    rw [update_eq _ _ _ (by simp [usz_val (show 0 < 2 ^ 32 by decide)]), bind_ok]
    rfl
  · show p3_keccak.hax_reshaped.absorb_final_block_loop0.body input starts (usz o) (usz w) (usz t) marks
      { start := usz 1, «end» := usz 1 } _ = _
    unfold p3_keccak.hax_reshaped.absorb_final_block_loop0.body
    rw [CoreModels.core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next, range_stop, bind_ok]
    simp

theorem usz_eq_iff {a b : ℕ} (ha : a < 2 ^ 32) (hb : b < 2 ^ 32) : usz a = usz b ↔ a = b := by
  constructor
  · intro h; have := congrArg UScalar.val h; rwa [usz_val ha, usz_val hb] at this
  · rintro rfl; rfl

theorem absorb_final_block_eq (d : Std.U8) (st : Std.Array (Std.Array Std.U64 1#usize) 25#usize)
    (input : Slice Std.U8) (starts : Std.Array Std.Usize 1#usize) (s : ℕ) (hs : starts.val = [usz s]) (o k : ℕ)
    (hk : k < 136) (hp : s + o + k ≤ input.val.length) :
    p3_keccak.hax_reshaped.absorb_final_block d st input starts (usz o) (usz k) =
      .ok (pack (finalL (unpack st) input (s + o) k d)) := by
  have hN : (Slice.len input).val = input.val.length := by simp
  have hk8 : 8 * (k / 8) + k % 8 = k := Nat.div_add_mod k 8
  unfold p3_keccak.hax_reshaped.absorb_final_block
  rw [RATE_eq, bind_ok, massert_of _ (by rw [UScalar.lt_equiv, usz_val (by omega), usz_val (by decide)]; exact hk),
    bind_ok, usz_div8 (by omega), bind_ok, usz_rem8 (by omega), bind_ok,
    absorb_words_eq _ _ _ s hs _ _ (by omega) (by omega), bind_ok]
  simp only [CoreModels.core.U64.Insts.CoreConvertFromU8.from, bind_ok]
  rw [eight_mul _ (usz 64) (by rw [usz_val (by decide)]; omega), bind_ok, u64_shl_usz _ _ (by omega), bind_ok,
    LAST_RATE_WORD_eq, bind_ok]
  have hw16 : usz (k / 8) = usz 16 ↔ k / 8 = 16 := usz_eq_iff (by omega) (by decide)
  have hlen1 : ∀ L : List Std.U64, L.length = 25 → (pack L).val.length = 25 := fun L _ => by simp [pack]
  have hab : (absorbL (unpack st) input (s + o) (k / 8)).length = 25 := by rw [length_absorbL, length_unpack]
  by_cases hw : k / 8 = 16
  · simp only [hw16.mpr hw, ite_true, CLOSING_MARK_eq, bind_ok, bne_self_eq_false, Bool.false_eq_true, ite_false]
    rw [repeat_u64 _ (by decide), bind_ok, VECTOR_LEN_eq,
      show (0#usize : Std.Usize) = usz 0 from ofNatCore_eq_usz _ _ (by decide),
      value_loop _ _ s hs _ _ _ (by omega) (by omega), bind_ok, xor_state_word_eq _ _ (by omega), bind_ok,
      unpack_pack _ hab]
    simp [finalL, hw, single_val, closing]
  · have hne : ¬ usz (k / 8) = usz 16 := fun h => hw (hw16.mp h)
    simp only [hne, ite_false, bind_ok, bne_iff_ne, ne_eq, not_false_eq_true, ite_true, CLOSING_MARK_eq]
    rw [repeat_u64 _ (by decide), bind_ok, VECTOR_LEN_eq,
      show (0#usize : Std.Usize) = usz 0 from ofNatCore_eq_usz _ _ (by decide),
      value_loop _ _ s hs _ _ _ (by omega) (by omega), bind_ok, xor_state_word_eq _ _ (by omega), bind_ok,
      repeat_u64 _ (by decide), bind_ok, xor_state_word_eq _ _ (by decide), unpack_pack _ hab,
      unpack_pack _ (by simp [length_xorAt, hab])]
    simp [finalL, hw, closing, single_val]

/-! ## Squeezing -/

/-- Byte `p` of the lanes, little-endian. -/
def byteOf (L : List Std.U64) (p : ℕ) : Std.U8 := ⟨(bytesOfWord (L.getD (p / 8) 0#u64).bv).getD (p % 8) 0⟩

/-- The digest with its first `m` bytes written. -/
def digestAt (L : List Std.U64) (m : ℕ) : Std.Array Std.U8 32#usize :=
  Std.Array.from ((List.range 32).map fun p => if p < m then byteOf L p else 0#u8) (by simp)

theorem squeeze_inner_step (st : Std.Array (Std.Array Std.U64 1#usize) 25#usize) (w j : ℕ) (hw : w < 4)
    (hj : j < 8) :
    p3_keccak.hax_reshaped.squeeze_lane_loop0_loop0.body (usz w)
        (Std.Array.from ((bytesOfWord ((unpack st).getD w 0#u64).bv).map fun b => ⟨b⟩) (by simp [bytesOfWord]))
        { start := usz j, «end» := usz 8 } (digestAt (unpack st) (8 * w + j)) =
      .ok (.cont ({ start := usz (j + 1), «end» := usz 8 }, digestAt (unpack st) (8 * w + j + 1))) := by
  unfold p3_keccak.hax_reshaped.squeeze_lane_loop0_loop0.body
  rw [CoreModels.core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next,
    range_step j _ (by rw [usz_val (by decide)]; exact hj), bind_ok]
  simp only [Aeneas.Std.uncurry_apply_pair]
  rw [index_usize_eq _ _ (by simp [bytesOfWord, usz_val (show j < 2 ^ 32 by omega)]; exact hj), bind_ok,
    eight_mul w (usz 64) (by rw [usz_val (by decide)]; omega), bind_ok,
    usz_add (by omega), bind_ok, update_eq _ _ _ (by simp [digestAt, usz_val (show 8 * w + j < 2 ^ 32 by omega)]; omega),
    bind_ok]
  congr 3
  apply Std.Array.ext
  simp only [digestAt, Std.Array.from_val, usz_val (show 8 * w + j < 2 ^ 32 by omega)]
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp only [List.getElem_set, List.getElem_map, List.getElem_range]
  rcases Nat.lt_trichotomy i (8 * w + j) with h | h | h
  · simp [show ¬ 8 * w + j = i by omega, h, show i < 8 * w + j + 1 by omega]
  · subst h
    have e1 : (8 * w + j) / 8 = w := by omega
    have e2 : (8 * w + j) % 8 = j := by omega
    simp [byteOf, e1, e2, List.getD_eq_getElem?_getD, usz_val (show j < 2 ^ 32 by omega)]
    simp only [List.getElem?_eq_getElem (by simp [bytesOfWord]; omega :
      j < (bytesOfWord ((unpack st)[w]?.getD 0#u64).bv).length), Option.getD_some]
  · simp [show ¬ 8 * w + j = i by omega, show ¬ i < 8 * w + j by omega, show ¬ i < 8 * w + j + 1 by omega]

theorem range_0_8 : ({ start := 0#usize, «end» := 8#usize } : CoreModels.core.ops.range.Range Std.Usize) =
    { start := usz 0, «end» := usz 8 } := by
  rw [show (0#usize : Std.Usize) = usz 0 from ofNatCore_eq_usz _ _ (by decide),
    show (8#usize : Std.Usize) = usz 8 from ofNatCore_eq_usz _ _ (by decide)]

theorem squeeze_inner (st : Std.Array (Std.Array Std.U64 1#usize) 25#usize) (w : ℕ) (hw : w < 4) :
    p3_keccak.hax_reshaped.squeeze_lane_loop0_loop0 { start := usz 0, «end» := usz 8 } (digestAt (unpack st) (8 * w))
        (usz w) (Std.Array.from ((bytesOfWord ((unpack st).getD w 0#u64).bv).map fun b => ⟨b⟩) (by simp [bytesOfWord])) =
      .ok (digestAt (unpack st) (8 * w + 8)) := by
  unfold p3_keccak.hax_reshaped.squeeze_lane_loop0_loop0
  exact loop_of_steps _ (fun j => (({ start := usz j, «end» := usz 8 } : CoreModels.core.ops.range.Range Std.Usize),
    digestAt (unpack st) (8 * w + j))) 8 _ (fun j hj => squeeze_inner_step st w j hw hj) (by
      show p3_keccak.hax_reshaped.squeeze_lane_loop0_loop0.body _ _ { start := usz 8, «end» := usz 8 } _ = _
      unfold p3_keccak.hax_reshaped.squeeze_lane_loop0_loop0.body
      rw [CoreModels.core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next, range_stop, bind_ok]
      rfl)

theorem unpack_get (st : Std.Array (Std.Array Std.U64 1#usize) 25#usize) (k : ℕ) (hk : k < st.val.length) (h0) :
    (st.val[k]'hk).val[0]'h0 = (unpack st).getD k 0#u64 := by
  simp [unpack, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]

theorem squeeze_lane_eq (st : Std.Array (Std.Array Std.U64 1#usize) 25#usize) :
    p3_keccak.hax_reshaped.squeeze_lane st (usz 0) = .ok (digestAt (unpack st) 32) := by
  have hs := st.property
  unfold p3_keccak.hax_reshaped.squeeze_lane p3_keccak.hax_reshaped.squeeze_lane_loop0
  rw [repeat_u8 _ (by decide), bind_ok]
  rw [show p3_keccak.DIGEST_BYTES = usz 32 from by unfold p3_keccak.DIGEST_BYTES; exact ofNatCore_eq_usz _ _ (by decide),
    show (8#usize : Std.Usize) = usz 8 from ofNatCore_eq_usz _ _ (by decide),
    usz_div (by decide) (by decide) (by decide), bind_ok,
    show (0#usize : Std.Usize) = usz 0 from ofNatCore_eq_usz _ _ (by decide)]
  have hd0 : Std.Array.from (List.replicate (32#usize : Std.Usize).val 0#u8) (by simp) = digestAt (unpack st) (8 * 0) := by
    apply Std.Array.ext; simp [digestAt]
  rw [hd0]
  refine loop_of_steps _ (fun k => (({ start := usz k, «end» := usz (32 / 8) } : CoreModels.core.ops.range.Range Std.Usize),
    digestAt (unpack st) (8 * k))) 4 _ ?_ ?_
  · intro k hk
    show p3_keccak.hax_reshaped.squeeze_lane_loop0.body st (usz 0) { start := usz k, «end» := usz (32 / 8) } _ = _
    unfold p3_keccak.hax_reshaped.squeeze_lane_loop0.body
    rw [CoreModels.core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next,
      range_step k _ (by rw [usz_val (by decide)]; omega), bind_ok]
    simp only [Aeneas.Std.uncurry_apply_pair]
    rw [index_usize_eq _ _ (by rw [usz_val (by omega), hs]; simp; omega), bind_ok,
      index_usize_eq _ _ (by rw [usz_val (by decide)]; simp), bind_ok, to_le_bytes_eq, bind_ok]
    have e : (st.val[(usz k).val]'(by rw [usz_val (by omega), hs]; simp; omega)).val[(usz 0).val]'(by
        rw [usz_val (by decide)]; simp) = (unpack st).getD k 0#u64 := by
      simp only [usz_val (show k < 2 ^ 32 by omega), usz_val (show 0 < 2 ^ 32 by decide)]
      exact unpack_get st k (by rw [hs]; simp; omega) _
    simp only [e, range_0_8]
    rw [squeeze_inner st k hk, bind_ok]
    rfl
  · show p3_keccak.hax_reshaped.squeeze_lane_loop0.body st (usz 0) { start := usz 4, «end» := usz (32 / 8) } _ = _
    unfold p3_keccak.hax_reshaped.squeeze_lane_loop0.body
    rw [CoreModels.core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next, range_stop, bind_ok]
    rfl

/-! ## One group: one message -/

theorem starts_loop (len g : ℕ) (N : Std.Usize) (hN : g * len ≤ N.val) (hg : g ≤ N.val) (hl : len ≤ N.val) :
    p3_keccak.hax_reshaped.hash_many_with_domain_loop1_loop0 { start := usz 0, «end» := usz 1 } (usz len) (usz g)
        (usz 1) (Std.Array.from (List.replicate (1#usize : Std.Usize).val 0#usize) (by simp)) =
      .ok (Std.Array.from [usz (g * len)] rfl) := by
  unfold p3_keccak.hax_reshaped.hash_many_with_domain_loop1_loop0
  refine loop_once _ _ _ ?_ ?_
  · show p3_keccak.hax_reshaped.hash_many_with_domain_loop1_loop0.body (usz len) (usz g) (usz 1)
      { start := usz 0, «end» := usz 1 } _ = _
    unfold p3_keccak.hax_reshaped.hash_many_with_domain_loop1_loop0.body
    rw [CoreModels.core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next,
      range_step 0 _ (by rw [usz_val (by decide)]; decide), bind_ok]
    simp only [Aeneas.Std.uncurry_apply_pair]
    have hlt : usz 0 < usz 1 := by rw [UScalar.lt_equiv, usz_val (by decide), usz_val (by decide)]; decide
    simp only [hlt, ite_true, bind_ok]
    rw [usz_add_le N (by omega), bind_ok, Nat.add_zero, usz_mul_le N hN hg hl, bind_ok,
      update_eq _ _ _ (by simp [usz_val (show 0 < 2 ^ 32 by decide)]), bind_ok]
    rfl
  · show p3_keccak.hax_reshaped.hash_many_with_domain_loop1_loop0.body (usz len) (usz g) (usz 1)
      { start := usz 1, «end» := usz 1 } _ = _
    unfold p3_keccak.hax_reshaped.hash_many_with_domain_loop1_loop0.body
    rw [CoreModels.core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next, range_stop, bind_ok]
    rfl

/-- The lanes after the first `k` whole blocks of the message from byte `p`. -/
def blocksL (input : Slice Std.U8) (p k : ℕ) : List Std.U64 :=
  (List.range k).foldl (fun L b => tiny_keccak.keccakf.rounds (absorbL L input (p + b * 136) 17))
    (List.replicate 25 0#u64)

theorem blocksL_succ (input : Slice Std.U8) (p k : ℕ) :
    blocksL input p (k + 1) = tiny_keccak.keccakf.rounds (absorbL (blocksL input p k) input (p + k * 136) 17) := by
  rw [blocksL, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, ← blocksL]

theorem length_blocksL (input : Slice Std.U8) (p k : ℕ) : (blocksL input p k).length = 25 := by
  induction k with
  | zero => simp only [blocksL, List.range_zero, List.foldl_nil, List.length_replicate]
  | succ k ih =>
    rw [blocksL_succ]
    exact (rounds_eq _ (by rw [length_absorbL, ih])).2

theorem permute_packed_eq (st : Std.Array (Std.Array Std.U64 1#usize) 25#usize) :
    p3_keccak.KeccakF.Insts.P3_symmetricPermutationPermutationArrayArrayU64125.permute_mut () st =
      .ok (pack (tiny_keccak.keccakf.rounds (unpack st))) := by
  rw [p3_keccak.KeccakF.Insts.P3_symmetricPermutationPermutationArrayArrayU64125.permute_mut.eq_1]
  exact permute_one_lane_eq st

theorem array_clone_self {T : Type} {N : Std.Usize} (inst : CoreModels.core.clone.Clone T)
    (hclone : ∀ x, inst.clone x = .ok x) (a : Std.Array T N) :
    (CoreModels.core.Array.Insts.CoreCloneClone N inst).clone a = .ok a := by
  show CoreModels.core.Array.Insts.CoreCloneClone.clone inst a = .ok a
  unfold CoreModels.core.Array.Insts.CoreCloneClone.clone CoreModels.core.array.Array.map
  rw [array_map_eq _ a () id (fun x => by
    simp only [CoreModels.core.array.CloneArray.clone.closure.Insts.CoreOpsFunctionFnMutTupleTT.call_mut,
      hclone, bind_ok, id])]
  congr 1
  apply Std.Array.ext
  simp

theorem zero_state :
    CoreModels.core.array.repeat 25#usize (CoreModels.core.Array.Insts.CoreCloneClone 1#usize
        CoreModels.core.U64.Insts.CoreCloneClone) (Std.Array.from (List.replicate (1#usize : Std.Usize).val 0#u64)
          (by simp)) = .ok (pack (List.replicate 25 0#u64)) := by
  rw [repeat_eq _ _ _ (array_clone_self _ (fun _ => rfl)) (by decide)]
  congr 1

theorem blocks_loop (input : Slice Std.U8) (starts : Std.Array Std.Usize 1#usize) (s : ℕ)
    (hs : starts.val = [usz s]) (fb : ℕ) (hp : s + 136 * fb ≤ input.val.length) :
    p3_keccak.hax_reshaped.hash_many_with_domain_loop1_loop1 (usz 136) { start := usz 0, «end» := usz fb } input
        starts (pack (List.replicate 25 0#u64)) = .ok (pack (blocksL input s fb)) := by
  have hN : (Slice.len input).val = input.val.length := by simp
  unfold p3_keccak.hax_reshaped.hash_many_with_domain_loop1_loop1
  refine loop_of_steps _ (fun k => (({ start := usz k, «end» := usz fb } : CoreModels.core.ops.range.Range Std.Usize),
    pack (blocksL input s k))) fb _ ?_ ?_
  · intro k hk
    show p3_keccak.hax_reshaped.hash_many_with_domain_loop1_loop1.body (usz 136) input starts
      { start := usz k, «end» := usz fb } _ = _
    unfold p3_keccak.hax_reshaped.hash_many_with_domain_loop1_loop1.body
    rw [CoreModels.core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next,
      range_step k _ (by rw [usz_val_le (Slice.len input) (by rw [hN]; omega)]; exact hk), bind_ok]
    simp only [Aeneas.Std.uncurry_apply_pair]
    rw [usz_mul_le (Slice.len input) (by rw [hN]; omega) (by rw [hN]; omega) (by rw [hN]; omega), bind_ok,
      usz_div8 (by decide), bind_ok, absorb_words_eq _ _ _ s hs _ _ (by decide) (by omega), bind_ok,
      unpack_pack _ (length_blocksL _ _ _), permute_packed_eq,
      unpack_pack _ (by rw [length_absorbL, length_blocksL]), bind_ok, blocksL_succ]
  · show p3_keccak.hax_reshaped.hash_many_with_domain_loop1_loop1.body (usz 136) input starts
      { start := usz fb, «end» := usz fb } _ = _
    unfold p3_keccak.hax_reshaped.hash_many_with_domain_loop1_loop1.body
    rw [CoreModels.core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next, range_stop, bind_ok]
    rfl

/-- The lanes after the whole blocks and the final block of the `len` bytes from byte `p`, permuted. -/
def msgLanes (input : Slice Std.U8) (p len : ℕ) (d : Std.U8) : List Std.U64 :=
  tiny_keccak.keccakf.rounds (finalL (blocksL input p (len / 136)) input (p + len / 136 * 136) (len % 136) d)

/-- The digests after the first `m` groups: the first `m` digests, then what `out` held. -/
def outAt (out : Slice (Std.Array Std.U8 32#usize)) (D : ℕ → Std.Array Std.U8 32#usize) (m : ℕ) :
    Slice (Std.Array Std.U8 32#usize) :=
  Slice.from ((List.range out.val.length).map fun j => if j < m then D j else out.val[j]!) (by simp)

theorem outAt_val (out : Slice (Std.Array Std.U8 32#usize)) (D : ℕ → Std.Array Std.U8 32#usize) (m : ℕ) :
    (outAt out D m).val = (List.range out.val.length).map fun j => if j < m then D j else out.val[j]! := by
  simp [outAt]

theorem length_outAt (out : Slice (Std.Array Std.U8 32#usize)) (D : ℕ → Std.Array Std.U8 32#usize) (m : ℕ) :
    (outAt out D m).val.length = out.val.length := by
  simp [outAt]

theorem write_loop (out : Slice (Std.Array Std.U8 32#usize)) (D : ℕ → Std.Array Std.U8 32#usize) (g : ℕ)
    (hg : g < out.val.length) (st : Std.Array (Std.Array Std.U64 1#usize) 25#usize) (hD : D g = digestAt (unpack st) 32) :
    p3_keccak.hax_reshaped.hash_many_with_domain_loop1_loop2 { start := usz 0, «end» := usz 1 } (outAt out D g)
        (usz g) st = .ok (outAt out D (g + 1)) := by
  have hN : (Slice.len out).val = out.val.length := by simp
  unfold p3_keccak.hax_reshaped.hash_many_with_domain_loop1_loop2
  refine loop_of_steps _ (fun k => (({ start := usz k, «end» := usz 1 } : CoreModels.core.ops.range.Range Std.Usize),
    outAt out D (g + k))) 1 _ ?_ ?_
  · intro k hk
    obtain rfl : k = 0 := by omega
    show p3_keccak.hax_reshaped.hash_many_with_domain_loop1_loop2.body (usz g) st
      { start := usz 0, «end» := usz 1 } _ = _
    unfold p3_keccak.hax_reshaped.hash_many_with_domain_loop1_loop2.body
    rw [CoreModels.core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next,
      range_step 0 _ (by rw [usz_val (by decide)]; decide), bind_ok]
    simp only [Aeneas.Std.uncurry_apply_pair]
    rw [squeeze_lane_eq, bind_ok, usz_add_le (Slice.len out) (by rw [hN]; omega), bind_ok,
      slice_update_eq _ _ _ (by rw [usz_val_le (Slice.len out) (by rw [hN]; omega), length_outAt]; omega), bind_ok]
    congr 3
    apply Slice.ext
    simp only [Slice.from_val, outAt_val, usz_val_le (Slice.len out) (show g + 0 ≤ (Slice.len out).val by rw [hN]; omega)]
    apply List.ext_getElem (by simp)
    intro j h1 h2
    simp only [List.getElem_set, List.getElem_map, List.getElem_range]
    split_ifs <;> first | omega | rfl | (subst_vars; simp_all)
  · show p3_keccak.hax_reshaped.hash_many_with_domain_loop1_loop2.body (usz g) st
      { start := usz 1, «end» := usz 1 } _ = _
    unfold p3_keccak.hax_reshaped.hash_many_with_domain_loop1_loop2.body
    rw [CoreModels.core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next, range_stop, bind_ok]
    rfl

theorem usz_mul_lit (a c : ℕ) (hc : c < 2 ^ 32) (hc0 : 0 < c) (n : Std.Usize) (h : a * c ≤ n.val) :
    (usz a * usz c : RustM Std.Usize) = .ok (usz (a * c)) := by
  · have ha : a ≤ n.val := le_trans (Nat.le_mul_of_pos_right a hc0) h
    have hmax : (usz a).val * (usz c).val ≤ UScalar.max .Usize := by
      rw [usz_val_le n ha, usz_val hc]
      have := n.hBounds; simp only [UScalar.max]; omega
    obtain ⟨z, hz, hv⟩ := spec_imp_exists (UScalar.mul_spec hmax)
    rw [hz, eq_usz_le (x := z) n h (by rw [hv, usz_val_le n ha, usz_val hc])]

theorem range0 (e : Std.Usize) : ({ start := 0#usize, «end» := e } : CoreModels.core.ops.range.Range Std.Usize) =
    { start := usz 0, «end» := e } := by
  rw [show (0#usize : Std.Usize) = usz 0 from ofNatCore_eq_usz _ _ (by decide)]

theorem repeat_usize (N : Std.Usize) (hN : 0 < N.val) (v : Std.Usize) :
    CoreModels.core.array.repeat N CoreModels.core.Usize.Insts.CoreCloneClone v =
      .ok (Std.Array.from (List.replicate N.val v) (by simp)) :=
  repeat_eq N _ v (fun _ => rfl) hN

/-- Digest `j` of the batch: message `j`, bytes `j len` to `(j + 1) len - 1`. -/
def digestOf (input : Slice Std.U8) (len : ℕ) (d : Std.U8) (j : ℕ) : Std.Array Std.U8 32#usize :=
  digestAt (msgLanes input (j * len) len d) 32

theorem group_step (d : Std.U8) (input : Slice Std.U8) (out : Slice (Std.Array Std.U8 32#usize)) (len : ℕ)
    (hlen : input.val.length = out.val.length * len) (hl : 0 < len) (g : ℕ) (hg : g < out.val.length) :
    p3_keccak.hax_reshaped.hash_many_with_domain_loop1.body d (usz 136) input (usz len) (usz (len / 136))
        (usz (len % 136)) (usz out.val.length) { start := usz g, «end» := usz out.val.length }
        (outAt out (digestOf input len d) g) =
      .ok (.cont ({ start := usz (g + 1), «end» := usz out.val.length }, outAt out (digestOf input len d) (g + 1))) := by
  have hN : (Slice.len out).val = out.val.length := by simp
  have hI : (Slice.len input).val = input.val.length := by simp
  have hgl : g * len + len ≤ input.val.length := by rw [hlen]; nlinarith
  have hlI : len ≤ input.val.length := by rw [hlen]; nlinarith
  have hglI : g * len ≤ input.val.length := by omega
  unfold p3_keccak.hax_reshaped.hash_many_with_domain_loop1.body
  rw [CoreModels.core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next,
    range_step g _ (by rw [usz_val_le (Slice.len out) (by rw [hN])]; exact hg), bind_ok]
  simp only [Aeneas.Std.uncurry_apply_pair]
  rw [VECTOR_LEN_eq, usz_mul_le (Slice.len out) (by rw [hN]; omega) (by rw [hN]; omega) (by rw [hN]; omega), bind_ok,
    Nat.mul_one, usz_sub_le (Slice.len out) (by omega) (by rw [hN]), bind_ok]
  have hpres : ¬ usz (out.val.length - g) < usz 1 := by
    rw [UScalar.lt_equiv, usz_val_le (Slice.len out) (by rw [hN]; omega), usz_val (by decide)]; omega
  simp only [hpres, ite_false, bind_ok]
  rw [repeat_usize _ (by decide), bind_ok, range0, starts_loop len g (Slice.len input) (by rw [hI]; omega)
      (by rw [hI]; nlinarith) (by rw [hI]; omega), bind_ok, repeat_u64 _ (by decide), bind_ok, zero_state, bind_ok,
    range0, blocks_loop _ _ (g * len) rfl _ (by omega), bind_ok,
    usz_mul_lit _ _ (by decide) (by decide) (Slice.len input) (by rw [hI]; omega), bind_ok,
    absorb_final_block_eq _ _ _ _ (g * len) rfl _ _ (by omega) (by omega), bind_ok, permute_packed_eq, bind_ok,
    write_loop _ _ _ hg _ ?_, bind_ok]
  rw [unpack_pack _ ((rounds_eq _ (length_unpack _)).2), unpack_pack _ (by rw [length_finalL, length_unpack]),
    unpack_pack _ (length_blocksL _ _ _)]
  rfl

theorem outAt_zero (out : Slice (Std.Array Std.U8 32#usize)) (D : ℕ → Std.Array Std.U8 32#usize) :
    outAt out D 0 = out := by
  apply Slice.ext
  rw [outAt_val]
  apply List.ext_getElem (by simp)
  intro j h1 h2
  simp [List.getElem?_eq_getElem h2]

theorem groups_loop (d : Std.U8) (input : Slice Std.U8) (out : Slice (Std.Array Std.U8 32#usize)) (len : ℕ)
    (hlen : input.val.length = out.val.length * len) (hl : 0 < len) :
    p3_keccak.hax_reshaped.hash_many_with_domain_loop1 d (usz 136) { start := usz 0, «end» := usz out.val.length }
        input out (usz len) (usz (len / 136)) (usz (len % 136)) (usz out.val.length) =
      .ok (outAt out (digestOf input len d) out.val.length) := by
  have hN : (Slice.len out).val = out.val.length := by simp
  unfold p3_keccak.hax_reshaped.hash_many_with_domain_loop1
  have h := loop_of_steps (fun x => match x with
      | (iter1, out1) => p3_keccak.hax_reshaped.hash_many_with_domain_loop1.body d (usz 136) input (usz len)
        (usz (len / 136)) (usz (len % 136)) (usz out.val.length) iter1 out1)
    (fun g => (({ start := usz g, «end» := usz out.val.length } : CoreModels.core.ops.range.Range Std.Usize),
      outAt out (digestOf input len d) g)) out.val.length _
    (fun g hg => group_step d input out len hlen hl g hg) (by
      show p3_keccak.hax_reshaped.hash_many_with_domain_loop1.body _ _ _ _ _ _ _
        { start := usz out.val.length, «end» := usz out.val.length } _ = _
      unfold p3_keccak.hax_reshaped.hash_many_with_domain_loop1.body
      rw [CoreModels.core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next, range_stop, bind_ok]
      rfl)
  rw [outAt_zero] at h
  exact h

theorem fill_loop (out : Slice (Std.Array Std.U8 32#usize)) (digest : Std.Array Std.U8 32#usize) :
    p3_keccak.hax_reshaped.hash_many_with_domain_loop0 { start := usz 0, «end» := Slice.len out } out digest =
      .ok (outAt out (fun _ => digest) out.val.length) := by
  have hN : (Slice.len out).val = out.val.length := by simp
  unfold p3_keccak.hax_reshaped.hash_many_with_domain_loop0
  have h := loop_of_steps (fun x => match x with
      | (iter1, out1) => p3_keccak.hax_reshaped.hash_many_with_domain_loop0.body digest iter1 out1)
    (fun g => (({ start := usz g, «end» := Slice.len out } : CoreModels.core.ops.range.Range Std.Usize),
      outAt out (fun _ => digest) g)) out.val.length _
    (fun g hg => by
      show p3_keccak.hax_reshaped.hash_many_with_domain_loop0.body digest { start := usz g, «end» := Slice.len out } _ = _
      unfold p3_keccak.hax_reshaped.hash_many_with_domain_loop0.body
      rw [CoreModels.core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next,
        range_step g _ (by rw [hN]; exact hg), bind_ok]
      simp only [Aeneas.Std.uncurry_apply_pair]
      rw [slice_update_eq _ _ _ (by rw [usz_val_le (Slice.len out) (by omega), length_outAt]; exact hg), bind_ok]
      congr 3
      apply Slice.ext
      simp only [Slice.from_val, outAt_val, usz_val_le (Slice.len out) (show g ≤ (Slice.len out).val by omega)]
      apply List.ext_getElem (by simp)
      intro j h1 h2
      simp only [List.getElem_set, List.getElem_map, List.getElem_range]
      split_ifs <;> first | omega | rfl)
    (by
      show p3_keccak.hax_reshaped.hash_many_with_domain_loop0.body digest
        { start := usz out.val.length, «end» := Slice.len out } _ = _
      unfold p3_keccak.hax_reshaped.hash_many_with_domain_loop0.body
      rw [CoreModels.core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next,
        range_next_none _ _ (by rw [hN, usz_val_le (Slice.len out) (by omega)]), bind_ok]
      rfl)
  rw [outAt_zero] at h
  exact h

theorem usz_div_lit {a c : ℕ} (n : Std.Usize) (ha : a ≤ n.val) (hc : c < 2 ^ 32) (h0 : c ≠ 0) :
    (usz a / usz c : RustM Std.Usize) = .ok (usz (a / c)) := by
  obtain ⟨z, hz, hv⟩ := UScalar.div_spec (usz a) (y := usz c) (by rw [usz_val hc]; exact h0)
  rw [hz, eq_usz_le (x := z) (k := a / c) n (by have := Nat.div_le_self a c; omega)
    (by rw [hv, usz_val_le n ha, usz_val hc])]

theorem usz_rem_lit {a c : ℕ} (n : Std.Usize) (ha : a ≤ n.val) (hc : c < 2 ^ 32) (h0 : c ≠ 0) :
    (usz a % usz c : RustM Std.Usize) = .ok (usz (a % c)) := by
  obtain ⟨z, hz, hv⟩ := spec_imp_exists
    (UScalar.rem_spec (usz a) (y := usz c) (by rw [usz_val hc]; exact h0))
  rw [hz, eq_usz_le (x := z) (k := a % c) n (by have := Nat.mod_le a c; omega)
    (by rw [hv, usz_val_le n ha, usz_val hc])]

/-! ## The batched hash -/

/-- No digests requested: `out` comes back unchanged, whatever the input. -/
theorem hash_many_empty (d : Std.U8) (input : Slice Std.U8) (out : Slice (Std.Array Std.U8 32#usize))
    (h : out.val = []) : p3_keccak.hax_reshaped.hash_many_with_domain d input out = .ok out := by
  unfold p3_keccak.hax_reshaped.hash_many_with_domain
  have he : Slice.len out = 0#usize := UScalar.eq_of_val_eq (by simp [h])
  simp only [CoreModels.core.slice.Slice.is_empty, CoreModels.core.slice.Slice.len,
    CoreModels.rust_primitives.slice.slice_length, bind_ok, he, decide_true, ite_true]

/-- An input whose length the digest count does not divide panics. -/
theorem hash_many_ragged (d : Std.U8) (input : Slice Std.U8) (out : Slice (Std.Array Std.U8 32#usize))
    (hn : 0 < out.val.length) (h : input.val.length % out.val.length ≠ 0) :
    p3_keccak.hax_reshaped.hash_many_with_domain d input out = .fail .panic := by
  unfold p3_keccak.hax_reshaped.hash_many_with_domain
  have hlv : (Slice.len out).val = out.val.length := by simp
  have hli : (Slice.len input).val = input.val.length := by simp
  have h0 : (Slice.len out).val ≠ 0 := by rw [hlv]; omega
  have hne : ¬ Slice.len out = 0#usize := fun e => h0 (by rw [e]; rfl)
  obtain ⟨m, hm, hmv⟩ := spec_imp_exists (UScalar.rem_spec (Slice.len input) h0)
  have hm0 : ¬ m = 0#usize := fun e => h (by
    have := congrArg UScalar.val e; rw [hmv, hli, hlv] at this; simpa using this)
  simp only [CoreModels.core.slice.Slice.is_empty, CoreModels.core.slice.Slice.len,
    CoreModels.rust_primitives.slice.slice_length, bind_ok, hne, decide_false, ite_false,
    CoreModels.core.num.Usize.is_multiple_of, Bool.false_eq_true, hm, hm0,
    CoreModels.core.fmt.rt.Argument.new_display, CoreModels.core.fmt.Arguments.new]

theorem digestOf_zero (input : Slice Std.U8) (d : Std.U8) (j : ℕ) :
    digestOf input 0 d j = digestAt (tiny_keccak.keccakf.rounds (finalL (List.replicate 25 0#u64) input 0 0 d)) 32 := by
  simp [digestOf, msgLanes, blocksL]

/-- `n` digests of messages of `len` bytes: digest `j` is the sponge of bytes `j len` to `(j + 1) len - 1`. -/
theorem hash_many_eq (d : Std.U8) (input : Slice Std.U8) (out : Slice (Std.Array Std.U8 32#usize)) (len : ℕ)
    (hn : 0 < out.val.length) (hlen : input.val.length = out.val.length * len) :
    p3_keccak.hax_reshaped.hash_many_with_domain d input out =
      .ok (outAt out (digestOf input len d) out.val.length) := by
  unfold p3_keccak.hax_reshaped.hash_many_with_domain
  have hlv : (Slice.len out).val = out.val.length := by simp
  have hli : (Slice.len input).val = input.val.length := by simp
  have h0 : (Slice.len out).val ≠ 0 := by rw [hlv]; omega
  have hne : ¬ Slice.len out = 0#usize := fun e => h0 (by rw [e]; rfl)
  obtain ⟨m, hm, hmv⟩ := spec_imp_exists (UScalar.rem_spec (Slice.len input) h0)
  have hm0 : m = 0#usize := UScalar.eq_of_val_eq (by rw [hmv, hli, hlv, hlen]; simp)
  obtain ⟨q, hq, hqv⟩ := UScalar.div_spec (Slice.len input) h0
  have hql : q = usz len := eq_usz_le (Slice.len input) (by rw [hli, hlen]; nlinarith)
    (by rw [hqv, hli, hlv, hlen]; exact Nat.mul_div_cancel_left _ hn)
  simp only [CoreModels.core.slice.Slice.is_empty, CoreModels.core.slice.Slice.len,
    CoreModels.rust_primitives.slice.slice_length, bind_ok, hne, decide_false, ite_false,
    CoreModels.core.num.Usize.is_multiple_of]
  simp only [Bool.false_eq_true, ite_false, hm, bind_ok, hm0, decide_true, ite_true, hq, hql]
  have hon : Slice.len out = usz out.val.length := eq_usz_le (Slice.len out) (by rw [hlv]) hlv
  rcases Nat.eq_zero_or_pos len with rfl | hl
  · rw [show (0#usize : Std.Usize) = usz 0 from ofNatCore_eq_usz _ _ (by decide)]
    simp only [ite_true]
    rw [repeat_u64 _ (by decide), bind_ok, zero_state, bind_ok, repeat_usize _ (by decide), bind_ok,
      absorb_final_block_eq _ _ _ _ 0 (by simp) 0 0 (by decide) (by simp), bind_ok, permute_packed_eq, bind_ok,
      squeeze_lane_eq, bind_ok, fill_loop]
    have hD : digestOf input 0 d = fun _ => digestAt (unpack (pack (tiny_keccak.keccakf.rounds (unpack (pack
        (finalL (unpack (pack (List.replicate 25 0#u64))) input (0 + 0) 0 d)))))) 32 := by
      funext j
      rw [digestOf_zero, unpack_pack _ ((rounds_eq _ (length_unpack _)).2),
        unpack_pack _ (by rw [length_finalL, length_unpack]), unpack_pack _ (by simp)]
    rw [hD]
  · have hlI : len ≤ (Slice.len input).val := by rw [hli, hlen]; nlinarith
    have hne0 : ¬ usz len = 0#usize := by
      intro e
      have := congrArg UScalar.val e
      rw [usz_val_le (Slice.len input) hlI] at this
      simp at this; omega
    have h1 : (usz (out.val.length % 1) = 0#usize) := by
      rw [Nat.mod_one]; exact (ofNatCore_eq_usz _ _ (by decide)).symm
    simp only [hne0, ite_false]
    rw [RATE_eq, bind_ok, usz_div_lit _ hlI (by decide) (by decide), bind_ok,
      usz_rem_lit _ hlI (by decide) (by decide), bind_ok, VECTOR_LEN_eq, hon,
      usz_rem_lit (Slice.len out) (by rw [hlv]) (by decide) (by decide), bind_ok]
    simp only [h1, ite_true]
    rw [usz_div_lit (Slice.len out) (by rw [hlv]) (by decide) (by decide), bind_ok, Nat.div_one, range0]
    exact groups_loop d input out len hlen hl

end Plonky3Lean.Proofs.Keccak
