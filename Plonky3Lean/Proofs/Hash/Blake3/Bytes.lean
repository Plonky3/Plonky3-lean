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

end Plonky3Lean.Proofs.Blake3
