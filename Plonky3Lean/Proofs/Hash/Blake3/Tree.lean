module

public import Plonky3Lean.Proofs.Hash.Blake3.Parent

@[expose] public section

/-!
# p3-blake3 on the portable backend: the tree over the chunks

The left subtree of `c > 1` chunks holds the largest power of two below `c`.
-/

open Aeneas Aeneas.Std CoreModels
open Plonky3Lean.Spec.Blake3 Plonky3Lean.Lib

namespace Plonky3Lean.Proofs.Blake3

theorem numBits_cases : UScalarTy.Usize.numBits = 32 ∨ UScalarTy.Usize.numBits = 64 := by
  rw [UScalarTy.Usize_numBits_eq]; exact System.Platform.numBits_eq

theorem usz_val' {k : ℕ} (h : k < 2 ^ 32) : (usz k).bv.toNat = k := usz_val h

theorem BITS_sub : (CoreModels.core.num.Usize.BITS - 1#u32 : RustM Std.U32) =
    .ok (u32n (UScalarTy.Usize.numBits - 1)) := by
  have hN := numBits_cases
  have hv0 : (Std.core.num.Usize.BITS : Std.U32).val = UScalarTy.Usize.numBits := by
    simp [Std.core.num.Usize.BITS]
  obtain ⟨z, hz, hv⟩ := spec_imp_exists
    (UScalar.sub_bv_spec (x := Std.core.num.Usize.BITS) (y := 1#u32) (by rw [hv0, show (1#u32 : Std.U32).val = 1 from rfl]; omega))
  rw [CoreModels.core.num.Usize.BITS]
  erw [hz]
  rw [eq_u32n (x := z) (k := UScalarTy.Usize.numBits - 1) (by omega)
    (by rw [hv.1, hv0, show (1#u32 : Std.U32).val = 1 from rfl])]

theorem lz_eq (m : ℕ) (hm : 0 < m) (hm32 : m < 2 ^ 32) :
    CoreModels.core.num.Usize.leading_zeros (usz m) =
      .ok (u32n (UScalarTy.Usize.numBits - Nat.log 2 m - 1)) := by
  have hN := numBits_cases
  have hN' := System.Platform.numBits_eq
  simp only [CoreModels.core.num.Usize.leading_zeros,
    CoreModels.rust_primitives.arithmetic.leading_zeros_usize]
  apply congrArg RustM.ok
  apply eq_u32n (by omega)
  show (BitVec.ofNat 32 (BitVec.leadingZeros (usz m).bv)).toNat = _
  have h0 : (usz m).bv ≠ 0 := fun h => by
    have := congrArg BitVec.toNat h
    rw [usz_val' hm32] at this; simp at this; omega
  rw [BitVec.leadingZeros, ite_eq_right_of_eq_false _ _ (eq_false h0), usz_val' hm32, BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt (by omega)

theorem u32n_sub {a b : ℕ} (hb : b ≤ a) (ha : a < 2 ^ 32) :
    (u32n a - u32n b : RustM Std.U32) = .ok (u32n (a - b)) := by
  obtain ⟨z, hz, hv⟩ := spec_imp_exists
    (UScalar.sub_bv_spec (x := u32n a) (y := u32n b) (by rw [u32n_val ha, u32n_val (by omega)]; omega))
  rw [hz, eq_u32n (x := z) (k := a - b) (by omega) (by rw [hv.1, u32n_val ha, u32n_val (by omega)])]

theorem one_shl (k : ℕ) (hk : k < 32) : (1#usize <<< u32n k : RustM Std.Usize) = .ok (usz (2 ^ k)) := by
  have hN := numBits_cases
  show UScalar.shiftLeft_UScalar _ _ = _
  simp only [UScalar.shiftLeft_UScalar, UScalar.shiftLeft, u32n_val (show k < 2 ^ 32 by omega)]
  rw [ite_eq_left_of_eq_true _ _ (eq_true (show k < UScalarTy.Usize.numBits by omega))]
  apply congrArg RustM.ok
  apply eq_usz (by have := Nat.pow_lt_pow_right (a := 2) (by norm_num) (show k < 32 from hk); omega)
  show ((1#usize : Std.Usize).bv.shiftLeft k).toNat = 2 ^ k
  rw [BitVec.shiftLeft_eq, BitVec.toNat_shiftLeft]
  have h1 : (1#usize : Std.Usize).bv.toNat = 1 := by
    have := lit1
    rw [this]; exact usz_val (by norm_num)
  rw [h1, Nat.one_shiftLeft]
  apply Nat.mod_eq_of_lt
  rcases hN with h | h <;> rw [h] <;> exact Nat.pow_lt_pow_right (by norm_num) (by omega)

/-- The chunks of the left subtree of `c` chunks: the largest power of two below `c`. -/
def leftChunks (c : ℕ) : ℕ := 2 ^ Nat.log 2 (c - 1)

theorem leftChunks_lt (c : ℕ) (hc : 2 ≤ c) : leftChunks c < c := by
  have := Nat.pow_log_le_self 2 (show c - 1 ≠ 0 by omega)
  unfold leftChunks; omega

theorem leftChunks_pos (c : ℕ) : 0 < leftChunks c := by unfold leftChunks; positivity

theorem log_lt_32 (m : ℕ) (hm : 0 < m) (hm32 : m < 2 ^ 32) : Nat.log 2 m < 32 :=
  Nat.log_lt_of_lt_pow (by omega) hm32

/-- The chaining value of `c` chunks from chunk `first` of the `len`-byte message at byte `s` of
`B`, its top compression flagged with `root` as well. -/
def treeCv (B : List (BitVec 8)) (s len first c : ℕ) (root : Word) : List Word :=
  if c ≤ 1 then chunkCv B s len first root
  else
    (compress IV (treeCv B s len first (leftChunks c) 0 ++
      treeCv B s len (first + leftChunks c) (c - leftChunks c) 0) 0 64 (PARENT ||| root)).take 8
termination_by c
decreasing_by
  · exact leftChunks_lt c (by omega)
  · have := leftChunks_pos c; omega

theorem length_chunkCv (B : List (BitVec 8)) (s len idx : ℕ) (root : Word) :
    (chunkCv B s len idx root).length = 8 := by
  simp [chunkCv, compress]

theorem length_treeCv (B : List (BitVec 8)) (s len first c : ℕ) (root : Word) :
    (treeCv B s len first c root).length = 8 := by
  rw [treeCv]
  split
  · exact length_chunkCv ..
  · simp [compress]

theorem usz_sub_one (c : ℕ) (hc : 1 ≤ c) (hc32 : c < 2 ^ 32) :
    (usz c - 1#usize : RustM Std.Usize) = .ok (usz (c - 1)) := by
  rw [lit1]; exact usz_sub hc hc32

theorem usz_eq_one (c : ℕ) (hc32 : c < 2 ^ 32) : (usz c = 1#usize) ↔ c = 1 := by
  rw [lit1]
  constructor
  · intro h; have := congrArg UScalar.val h; rwa [usz_val hc32, usz_val (by norm_num)] at this
  · rintro rfl; rfl

theorem subtree_eq (batch : Slice Std.U8) (s len : ℕ) (hB : s + len ≤ batch.val.length)
    (h32 : batch.val.length + 1024 < 2 ^ 32) (c : ℕ) :
    ∀ (first : ℕ) (root : Std.U32), 1 ≤ c → (first + c - 1) * 1024 ≤ len →
    p3_blake3.batch.subtree p3_blake3.U32.Insts.P3_blake3BatchLanesBackend1 p3_blake3.batch.Mode.HASH
      (lane1 batch s) (usz len) (usz first) (usz c) root =
      .ok (grp 8#usize (treeCv (sbytes batch) s len first c root.bv)) := by
  induction c using Nat.strong_induction_on with
  | _ c ih =>
  intro first root hc hfc
  have hx : first + c - 1 ≤ len := le_trans (Nat.le_mul_of_pos_right _ (by norm_num)) hfc
  have hc32 : c < 2 ^ 32 := by omega
  have hf32 : first + c < 2 ^ 32 := by omega
  rw [p3_blake3.batch.subtree, treeCv]
  by_cases h1 : c = 1
  · subst h1
    rw [ite_eq_left_of_eq_true _ _ (eq_true ((usz_eq_one 1 (by norm_num)).2 rfl)),
      ite_eq_left_of_eq_true _ _ (eq_true le_rfl)]
    exact chunk_eq batch s len first root (by simpa using hfc) hB h32
  · rw [ite_eq_right_of_eq_false _ _ (eq_false (fun h => h1 ((usz_eq_one c hc32).1 h))),
      ite_eq_right_of_eq_false _ _ (eq_false (by omega))]
    have hN := numBits_cases
    have hlog := log_lt_32 (c - 1) (by omega) (by omega)
    have hL := leftChunks_lt c (by omega)
    have hL0 := leftChunks_pos c
    rw [BITS_sub, bind_ok, usz_sub_one c (by omega) hc32, bind_ok, lz_eq (c - 1) (by omega) (by omega), bind_ok,
      u32n_sub (by omega) (by omega), bind_ok,
      show UScalarTy.Usize.numBits - 1 - (UScalarTy.Usize.numBits - Nat.log 2 (c - 1) - 1) = Nat.log 2 (c - 1)
        by omega, one_shl _ (by omega), bind_ok]
    rw [show (0#u32 : Std.U32) = ⟨0⟩ from rfl, show 2 ^ Nat.log 2 (c - 1) = leftChunks c from rfl]
    rw [ih (leftChunks c) hL first ⟨0⟩ hL0 (le_trans (Nat.mul_le_mul_right 1024 (by omega)) hfc), bind_ok,
      usz_add (by unfold leftChunks at *; omega), bind_ok, usz_sub hL.le hc32, bind_ok,
      ih (c - leftChunks c) (by omega) (first + leftChunks c) ⟨0⟩ (by omega)
        (le_trans (Nat.mul_le_mul_right 1024 (by omega)) hfc), bind_ok,
      parent_eq _ _ (length_treeCv ..) (length_treeCv ..)]

end Plonky3Lean.Proofs.Blake3
