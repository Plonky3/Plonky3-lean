module

public import Plonky3Lean.Proofs.Hash.Blake3.Compress

@[expose] public section

/-!
# p3-blake3 on the portable backend: bytes and words

A block's sixteen words are its bytes, four at a time, little-endian, and a digest is the bytes of
the first eight words of the chaining value.
-/

open Aeneas Aeneas.Std CoreModels
open Plonky3Lean.Spec.Blake3 Plonky3Lean.Lib

namespace Plonky3Lean.Proofs.Blake3

/-- The bytes of `s`, as an array of `n` `u8`s, padded with zeros or cut to the array's length. -/
def barr (n : Std.Usize) (s : List (BitVec 8)) : Std.Array Std.U8 n :=
  Std.Array.make n (((s ++ List.replicate n.val 0).take n.val).map fun b => ⟨b⟩) (by simp)

theorem barr_val (n : Std.Usize) (s : List (BitVec 8)) (h : s.length = n.val) :
    (barr n s).val = s.map fun b => ⟨b⟩ := by
  simp [barr, List.take_append_of_le_length (by omega : n.val ≤ s.length), h]

theorem index_barr (n : Std.Usize) (s : List (BitVec 8)) (h : s.length = n.val) (i : ℕ) (hi : i < n.val) :
    Std.Array.index_usize (barr n s) (usz i) = .ok ⟨s.getD i 0⟩ := by
  rw [index_usize_eq _ _ (by rw [barr_val n s h, usz_val_le n hi.le]; simpa [h] using hi)]
  simp [barr_val n s h, usz_val_le n hi.le, List.getElem?_eq_getElem (show i < s.length by omega)]

theorem update_barr (n : Std.Usize) (s : List (BitVec 8)) (h : s.length = n.val) (i : ℕ) (hi : i < n.val)
    (x : Std.U8) :
    Std.Array.update (barr n s) (usz i) x = .ok (barr n (s.set i x.bv)) := by
  rw [update_eq _ _ _ (by rw [barr_val n s h, usz_val_le n hi.le]; simpa [h] using hi)]
  congr 1
  apply Std.Array.ext
  rw [Std.Array.from_val, barr_val n s h, barr_val n _ (by simpa using h), usz_val_le n hi.le,
    List.map_set]

/-- Four little-endian bytes, as one word. -/
theorem fromLEBytes_four (b₀ b₁ b₂ b₃ : BitVec 8) :
    (BitVec.fromLEBytes [b₀, b₁, b₂, b₃]).cast (by simp) = wordOfBytes b₀ b₁ b₂ b₃ := by
  have h := fromBEBytes_four b₃ b₂ b₁ b₀
  simp only [BitVec.fromBEBytes] at h
  exact h

theorem from_le_bytes_make (b₀ b₁ b₂ b₃ : Std.U8) (h) :
    Aeneas.Std.core.num.U32.from_le_bytes (Std.Array.make 4#usize [b₀, b₁, b₂, b₃] h) =
      ⟨wordOfBytes b₀.bv b₁.bv b₂.bv b₃.bv⟩ :=
  congrArg UScalar.mk (fromLEBytes_four b₀.bv b₁.bv b₂.bv b₃.bv)

/-- The word at byte `4 * w` of a block, little-endian. -/
def wordAt (bs : List (BitVec 8)) (w : ℕ) : Word :=
  wordOfBytes (bs.getD (4 * w) 0) (bs.getD (4 * w + 1) 0) (bs.getD (4 * w + 2) 0) (bs.getD (4 * w + 3) 0)

theorem lit (k : ℕ) (h : k < 2 ^ 32) (h' : k < 2 ^ UScalarTy.Usize.numBits) :
    (UScalar.ofNatCore k h' : Std.Usize) = usz k := ofNatCore_eq_usz k h' h

theorem load_word (bs : List (BitVec 8)) (h : bs.length = 64) (w : ℕ) (hw : w < 16) :
    p3_blake3.batch.lanes.portable.BackendU321.load_block.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU32.call_mut
      (barr 64#usize bs) (usz w) = .ok (⟨wordAt bs w⟩, barr 64#usize bs) := by
  have h' : bs.length = (64#usize).val := h
  unfold p3_blake3.batch.lanes.portable.BackendU321.load_block.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU32.call_mut
  simp (disch := norm_num) only [ofNatCore_eq_usz]
  rw [usz_mul (by omega) (by norm_num) (by omega), bind_ok, index_barr _ _ h' _ (by simp; omega), bind_ok,
    usz_add (by omega), bind_ok, index_barr _ _ h' _ (by simp; omega), bind_ok,
    usz_add (by omega), bind_ok, index_barr _ _ h' _ (by simp; omega), bind_ok,
    usz_add (by omega), bind_ok, index_barr _ _ h' _ (by simp; omega), bind_ok]
  simp only [CoreModels.core.num.U32.from_le_bytes, CoreModels.rust_primitives.arithmetic.from_le_bytes_u32,
    bind_ok, from_le_bytes_make]
  rfl

theorem load_block_eq (bs : List (BitVec 8)) (h : bs.length = 64) :
    p3_blake3.U32.Insts.P3_blake3BatchLanesBackend1.load_block (Std.Array.make 1#usize [barr 64#usize bs] (by rfl)) =
      .ok (arr 16#usize (blockWords bs)) := by
  unfold p3_blake3.U32.Insts.P3_blake3BatchLanesBackend1.load_block
  rw [show (0#usize : Std.Usize) = usz 0 from lit0, index_make _ _ _ (by rw [usz_val (by norm_num)]; simp),
    bind_ok]
  simp only [CoreModels.core.array.from_fn]
  rw [array_from_fn_eq 16#usize _ _ _ (fun w hw => load_word bs h w hw)]
  apply congrArg RustM.ok
  apply Std.Array.ext
  rw [Std.Array.from_val, arr_val _ _ (by simp [blockWords])]
  simp [blockWords, wordAt]

/-- The `u32` of value `k`. -/
def u32n (k : ℕ) : Std.U32 := ⟨BitVec.ofNat 32 k⟩

theorem u32n_val {k : ℕ} (h : k < 2 ^ 32) : (u32n k).val = k := by
  show (BitVec.ofNat 32 k).toNat = k
  rw [BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt h

theorem eq_u32n {x : Std.U32} {k : ℕ} (h : k < 2 ^ 32) (hx : x.val = k) : x = u32n k :=
  UScalar.eq_of_val_eq (by rw [hx, u32n_val h])

theorem cast_usz_u32 (j : ℕ) (h : j < 2 ^ 32) : UScalar.cast .U32 (usz j) = u32n j :=
  eq_u32n h (by rw [UScalar.cast_val_eq, usz_val h]; exact Nat.mod_eq_of_lt h)

theorem u32n_mul {a b : ℕ} (h : a * b < 2 ^ 32) (ha : a < 2 ^ 32) (hb : b < 2 ^ 32) :
    (u32n a * u32n b : RustM Std.U32) = .ok (u32n (a * b)) := by
  have hmax : (u32n a).val * (u32n b).val ≤ UScalar.max .U32 := by
    rw [u32n_val ha, u32n_val hb]
    simp only [UScalar.max, UScalarTy.U32_numBits_eq]
    omega
  obtain ⟨z, hz, hv⟩ := spec_imp_exists (UScalar.mul_spec hmax)
  rw [hz, eq_u32n (x := z) h (by rw [hv, u32n_val ha, u32n_val hb])]

theorem u32n_rem {a b : ℕ} (ha : a < 2 ^ 32) (hb : b < 2 ^ 32) (h0 : b ≠ 0) :
    (u32n a % u32n b : RustM Std.U32) = .ok (u32n (a % b)) := by
  obtain ⟨z, hz, hv⟩ := spec_imp_exists
    (UScalar.rem_spec (u32n a) (y := u32n b) (by rw [u32n_val hb]; exact h0))
  rw [hz, eq_u32n (x := z) (k := a % b) (by have := Nat.mod_le a b; omega)
    (by rw [hv, u32n_val ha, u32n_val hb])]

theorem u32n_shr (x : Std.U32) (k : ℕ) (hk : k < 32) :
    (x >>> u32n k : RustM Std.U32) = .ok ⟨x.bv >>> k⟩ := by
  show UScalar.shiftRight_UScalar x _ = _
  simp only [UScalar.shiftRight_UScalar, UScalar.shiftRight, u32n_val (show k < 2 ^ 32 by omega)]
  rw [ite_eq_left_of_eq_true _ _ (eq_true (show k < UScalarTy.U32.numBits from hk))]
  rfl

theorem le_byte (x : Std.U32) (j : ℕ) (hj : j < 4) :
    CoreModels.core.num.U32.to_le_bytes.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU8.call_mut x (usz j) =
      .ok (⟨x.bv.extractLsb' (8 * j) 8⟩, x) := by
  unfold CoreModels.core.num.U32.to_le_bytes.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU8.call_mut
  rw [show (8#u32 : Std.U32) = u32n 8 from eq_u32n (by norm_num) rfl,
    show (32#u32 : Std.U32) = u32n 32 from eq_u32n (by norm_num) rfl]
  simp only [lift_eq, bind_ok, cast_usz_u32 j (by omega), u32n_mul (show 8 * j < 2 ^ 32 by omega)
    (by norm_num) (by omega), u32n_rem (a := 8 * j) (b := 32) (by omega) (by norm_num) (by norm_num),
    Nat.mod_eq_of_lt (show 8 * j < 32 by omega), u32n_shr x (8 * j) (by omega)]
  have e : UScalar.cast .U8 (⟨x.bv >>> (8 * j)⟩ : Std.U32) = ⟨x.bv.extractLsb' (8 * j) 8⟩ := by
    show (⟨(x.bv >>> (8 * j)).setWidth 8⟩ : Std.U8) = _
    congr 1
  rw [e]

theorem to_le_bytes_eq (x : Std.U32) :
    CoreModels.core.num.U32.to_le_bytes x = .ok (barr 4#usize (bytesOfWord x.bv)) := by
  unfold CoreModels.core.num.U32.to_le_bytes
  rw [array_from_fn_eq 4#usize _ _ _ (fun j hj => le_byte x j hj)]
  apply congrArg RustM.ok
  apply Std.Array.ext
  rw [Std.Array.from_val, barr_val _ _ (by simp [bytesOfWord])]
  simp [bytesOfWord, List.range_succ]

/-- The little-endian bytes of the first eight words of `cv`. -/
def cvBytes (cv : List Word) : List (BitVec 8) :=
  (List.range 32).map fun p => (bytesOfWord (cv.getD (p / 4) 0)).getD (p % 4) 0

/-- The digest `old` with its first `k` bytes overwritten by those of `cv`. -/
def bytesUpTo (cv : List Word) (old : List (BitVec 8)) (k : ℕ) : List (BitVec 8) :=
  (List.range 32).map fun p => if p < k then (cvBytes cv).getD p 0 else old.getD p 0

theorem length_bytesUpTo (cv : List Word) (old : List (BitVec 8)) (k : ℕ) :
    (bytesUpTo cv old k).length = 32 := by simp [bytesUpTo]

theorem bytesUpTo_zero (cv : List Word) (old : List (BitVec 8)) (h : old.length = 32) :
    bytesUpTo cv old 0 = old := by
  apply List.ext_getElem (by simp [bytesUpTo, h])
  intro i h1 h2
  simp [bytesUpTo, List.getElem?_eq_getElem h2]

theorem bytesUpTo_full (cv : List Word) (old : List (BitVec 8)) :
    bytesUpTo cv old 32 = cvBytes cv := by
  apply List.ext_getElem (by simp [bytesUpTo, cvBytes])
  intro i h1 h2
  have hi : i < 32 := by simpa [bytesUpTo] using h1
  simp [bytesUpTo, hi, List.getElem?_eq_getElem h2]

theorem bytesUpTo_succ (cv : List Word) (old : List (BitVec 8)) (i j : ℕ) (hi : i < 8) (hj : j < 4) :
    (bytesUpTo cv old (4 * i + j)).set (4 * i + j) ((bytesOfWord (cv.getD i 0)).getD j 0) =
      bytesUpTo cv old (4 * i + j + 1) := by
  apply List.ext_getElem (by simp [bytesUpTo])
  intro p h1 h2
  simp only [bytesUpTo, List.getElem_set, List.getElem_map, List.getElem_range]
  by_cases hp : 4 * i + j = p
  · subst hp
    have hq : (4 * i + j) / 4 = i := by omega
    have hr : (4 * i + j) % 4 = j := by omega
    simp [cvBytes, hq, hr, show 4 * i + j < 32 by omega]
  · simp only [hp, ite_false]
    split_ifs <;> first | omega | rfl

theorem store_inner_body (cv : List Word) (old : List (BitVec 8)) (i j : ℕ) (hi : i < 8) (hj : j < 4) :
    p3_blake3.U32.Insts.P3_blake3BatchLanesBackend1.store_digests_loop0_loop0.body (usz i)
      (barr 4#usize (bytesOfWord (cv.getD i 0))) { start := usz j, «end» := usz 4 }
      (barr 32#usize (bytesUpTo cv old (4 * i + j))) =
      .ok (.cont ({ start := usz (j + 1), «end» := usz 4 },
        barr 32#usize (bytesUpTo cv old (4 * i + j + 1)))) := by
  have hb : (bytesOfWord (cv.getD i 0)).length = (4#usize).val := by simp [bytesOfWord]
  have hu : (bytesUpTo cv old (4 * i + j)).length = (32#usize).val := length_bytesUpTo ..
  unfold p3_blake3.U32.Insts.P3_blake3BatchLanesBackend1.store_digests_loop0_loop0.body
  simp (disch := norm_num) only [ofNatCore_eq_usz]
  simp only [CoreModels.core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next,
    range_step j (usz 4) (by rw [usz_val (by norm_num)]; exact hj), bind_ok, Aeneas.Std.uncurry_apply_pair,
    index_barr _ _ hb j (by simp; omega), usz_mul (show 4 * i < 2 ^ 32 by omega) (by norm_num) (by omega),
    usz_add (show 4 * i + j < 2 ^ 32 by omega), update_barr _ _ hu (4 * i + j) (by simp; omega),
    bytesUpTo_succ cv old i j hi hj]

theorem store_inner_done (i : Std.Usize) (bytes : Std.Array Std.U8 4#usize) (x : Std.Array Std.U8 32#usize) :
    p3_blake3.U32.Insts.P3_blake3BatchLanesBackend1.store_digests_loop0_loop0.body i bytes
      { start := usz 4, «end» := usz 4 } x = .ok (.done x) := by
  unfold p3_blake3.U32.Insts.P3_blake3BatchLanesBackend1.store_digests_loop0_loop0.body
  simp only [CoreModels.core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next, range_stop,
    bind_ok, Aeneas.Std.uncurry_apply_pair]

theorem store_inner (cv : List Word) (old : List (BitVec 8)) (i : ℕ) (hi : i < 8) :
    p3_blake3.U32.Insts.P3_blake3BatchLanesBackend1.store_digests_loop0_loop0
      { start := 0#usize, «end» := 4#usize } (barr 32#usize (bytesUpTo cv old (4 * i))) (usz i)
      (barr 4#usize (bytesOfWord (cv.getD i 0))) =
      .ok (barr 32#usize (bytesUpTo cv old (4 * (i + 1)))) := by
  unfold p3_blake3.U32.Insts.P3_blake3BatchLanesBackend1.store_digests_loop0_loop0
  simp only [lit0, show (4#usize : Std.Usize) = usz 4 from eq_usz (by norm_num) rfl]
  rw [show 4 * (i + 1) = 4 * i + 4 by ring]
  exact loop_of_steps (fun x : CoreModels.core.ops.range.Range Std.Usize × Std.Array Std.U8 32#usize =>
      p3_blake3.U32.Insts.P3_blake3BatchLanesBackend1.store_digests_loop0_loop0.body (usz i)
        (barr 4#usize (bytesOfWord (cv.getD i 0))) x.1 x.2)
    (fun j => (({ start := usz j, «end» := usz 4 } : CoreModels.core.ops.range.Range Std.Usize),
      barr 32#usize (bytesUpTo cv old (4 * i + j)))) 4 _
    (fun j hj => store_inner_body cv old i j hi hj) (store_inner_done _ _ _)

theorem store_outer_body (cv : List Word) (hcv : cv.length = 8) (old : List (BitVec 8)) (i : ℕ)
    (hi : i < 8) :
    p3_blake3.U32.Insts.P3_blake3BatchLanesBackend1.store_digests_loop0.body (arr 8#usize cv)
      { start := usz i, «end» := usz 8 } (barr 32#usize (bytesUpTo cv old (4 * i))) =
      .ok (.cont ({ start := usz (i + 1), «end» := usz 8 },
        barr 32#usize (bytesUpTo cv old (4 * (i + 1))))) := by
  have hcv' : cv.length = (8#usize).val := hcv
  unfold p3_blake3.U32.Insts.P3_blake3BatchLanesBackend1.store_digests_loop0.body
  simp only [CoreModels.core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next,
    range_step i (usz 8) (by rw [usz_val (by norm_num)]; exact hi), bind_ok, Aeneas.Std.uncurry_apply_pair,
    index_arr _ _ hcv' i (by simp; omega), to_le_bytes_eq, u32_bv_mk, store_inner cv old i hi]

theorem store_outer_done (st : Std.Array Std.U32 8#usize) (x : Std.Array Std.U8 32#usize) :
    p3_blake3.U32.Insts.P3_blake3BatchLanesBackend1.store_digests_loop0.body st
      { start := usz 8, «end» := usz 8 } x = .ok (.done x) := by
  unfold p3_blake3.U32.Insts.P3_blake3BatchLanesBackend1.store_digests_loop0.body
  simp only [CoreModels.core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next, range_stop,
    bind_ok, Aeneas.Std.uncurry_apply_pair]

/-- One lane of digests: the bytes of `d` as the only digest. -/
def dgrp (d : List (BitVec 8)) : Std.Array (Std.Array Std.U8 32#usize) 1#usize :=
  Std.Array.make 1#usize [barr 32#usize d] (by rfl)

theorem dgrp_val (d : List (BitVec 8)) : (dgrp d).val = [barr 32#usize d] := by simp [dgrp]

theorem index_dgrp (d : List (BitVec 8)) :
    Std.Array.index_usize (dgrp d) (usz 0) = .ok (barr 32#usize d) := by
  rw [index_usize_eq _ _ (by rw [dgrp_val, usz_val (by norm_num)]; simp)]
  simp [dgrp_val, usz_val (show 0 < 2 ^ 32 by norm_num)]

theorem index_mut_dgrp (d : List (BitVec 8)) :
    Std.Array.index_mut_usize (dgrp d) (usz 0) =
      .ok (barr 32#usize d, fun a => Std.Array.set (dgrp d) (usz 0) a) := by
  simp only [Std.Array.index_mut_usize, index_dgrp]
  rw [bind_tc_ok]

theorem set_dgrp (d e : List (BitVec 8)) :
    Std.Array.set (dgrp d) (usz 0) (barr 32#usize e) = dgrp e := by
  apply Std.Array.ext
  simp [Std.Array.set_val_eq, dgrp_val, usz_val (show 0 < 2 ^ 32 by norm_num)]

theorem store_digests_eq (cv : List Word) (hcv : cv.length = 8) (old : List (BitVec 8))
    (hold : old.length = 32) :
    p3_blake3.U32.Insts.P3_blake3BatchLanesBackend1.store_digests (arr 8#usize cv) (dgrp old) =
      .ok (dgrp (cvBytes cv)) := by
  unfold p3_blake3.U32.Insts.P3_blake3BatchLanesBackend1.store_digests
  rw [lit0, index_mut_dgrp, bind_ok]
  simp only [Aeneas.Std.uncurry_apply_pair, STATE_WORDS_eq]
  unfold p3_blake3.U32.Insts.P3_blake3BatchLanesBackend1.store_digests_loop0
  conv => lhs; rw [← bytesUpTo_zero cv old hold]
  erw [loop_of_steps (fun x : CoreModels.core.ops.range.Range Std.Usize × Std.Array Std.U8 32#usize =>
      p3_blake3.U32.Insts.P3_blake3BatchLanesBackend1.store_digests_loop0.body (arr 8#usize cv) x.1 x.2)
    (fun i => (({ start := usz i, «end» := usz 8 } : CoreModels.core.ops.range.Range Std.Usize),
      barr 32#usize (bytesUpTo cv old (4 * i)))) 8 _
    (fun i hi => store_outer_body cv hcv old i hi) (store_outer_done _ _), bind_ok, bytesUpTo_full,
    set_dgrp]

theorem state_word (i : ℕ) (hi : i < 8) :
    p3_blake3.batch.Mode.state.closure.Insts.CoreOpsFunctionFnMutTupleUsizeV.call_mut (G := 1#usize) WI
      (arr 8#usize IV) (usz i) = .ok (⟨IV.getD i 0⟩, arr 8#usize IV) := by
  unfold p3_blake3.batch.Mode.state.closure.Insts.CoreOpsFunctionFnMutTupleUsizeV.call_mut
  rw [index_arr 8#usize IV rfl i hi, bind_ok]
  exact bind_ok _ _

theorem state_eq : p3_blake3.batch.Mode.state 1#usize WI p3_blake3.batch.Mode.HASH = .ok (grp 8#usize IV) := by
  unfold p3_blake3.batch.Mode.state p3_blake3.batch.Mode.HASH
  simp only [IV_eq, CoreModels.core.array.from_fn]
  rw [array_from_fn_eq 8#usize _ _ _ (fun i hi => state_word i hi), bind_ok,
    from_getD _ _ rfl, repeat_eq _ _ _ (array_clone_eq _ (fun _ => rfl)) (by decide)]
  apply congrArg RustM.ok
  apply Std.Array.ext
  simp [grp_val]

end Plonky3Lean.Proofs.Blake3
