module

public import P3Word
public import Plonky3Lean.Lib
public import Plonky3Lean.Proofs.Word.Spec

@[expose] public section

open Aeneas Aeneas.Std CoreModels p3_word
open Plonky3Lean.Lib

namespace Plonky3Lean.Proofs.Word

theorem u64_rotate_right_eq (x : Std.U64) (n : Std.U32) :
    CoreModels.core.num.U64.rotate_right x n = .ok ⟨x.bv.rotateRight n.val⟩ := by
  unfold CoreModels.core.num.U64.rotate_right
  simp only [HMod.hMod]
  have hr : UScalar.rem n 64#u32 = .ok ⟨n.bv % 64#32⟩ := by
    simp [UScalar.rem]
  rw [hr, bind_ok]
  have hm : (⟨n.bv % 64#32⟩ : Std.U32).val = n.val % 64 := by
    show (n.bv % 64#32).toNat = _
    rw [BitVec.toNat_umod, UScalar.bv_toNat]
    rfl
  split
  · rename_i h0
    have h0' : n.val % 64 = 0 := by rw [← hm, h0]; rfl
    congr 1
    rw [← BitVec.rotateRight_mod_eq_rotateRight, h0']
    cases x
    simp [BitVec.rotateRight, BitVec.rotateRightAux]
    exact (BitVec.or_zero ..).symm
  · rename_i h0
    have hpos : n.val % 64 ≠ 0 := fun h => h0 (UScalar.eq_of_val_eq (by rw [hm, h]; rfl))
    have hlt : n.val % 64 < 64 := Nat.mod_lt _ (by norm_num)
    simp only [HShiftRight.hShiftRight, HShiftLeft.hShiftLeft, HSub.hSub]
    simp only [UScalar.shiftRight_UScalar, UScalar.shiftRight, UScalar.sub, hm]
    have h32 : (64#u32).val = 64 := rfl
    simp only [UScalarTy.U64_numBits_eq, UScalarTy.U32_numBits_eq, hlt, ite_true, h32, show ¬ 64 < n.val % 64 by omega,
      ite_false, bind_ok, UScalar.shiftLeft_UScalar, UScalar.shiftLeft]
    have hsub : (⟨BitVec.ofNat 32 (64 - n.val % 64)⟩ : Std.U32).val = 64 - n.val % 64 := by
      show (BitVec.ofNat 32 _).toNat = _
      rw [BitVec.toNat_ofNat]; omega
    rw [hsub]
    simp only [show 64 - n.val % 64 < 64 by omega, ite_true, bind_ok]
    congr 2
    rw [BitVec.rotateRight_def]
    ext i hi
    simp only [UScalarTy.U64_numBits_eq] at hi
    simp only [BitVec.getElem_or]
    simp only [BitVec.getElem_ushiftRight, BitVec.getElem_shiftLeft, UScalarTy.U64_numBits_eq]
    by_cases h : i < 64 - n.val % 64
    · simp [h]
    · have : x.bv.getLsbD (n.val % 64 + i) = false :=
        BitVec.getLsbD_of_ge _ _ (by show 64 ≤ _; omega)
      simp [h, this]

theorem ushl_eq {ty} (x : UScalar ty) (a : Std.U32) :
    (x <<< a : RustM (UScalar ty)) =
      if a.val < ty.numBits then .ok ⟨x.bv <<< a.val⟩ else .fail .panic := rfl

theorem ushr_eq {ty} (x : UScalar ty) (a : Std.U32) :
    (x >>> a : RustM (UScalar ty)) =
      if a.val < ty.numBits then .ok ⟨x.bv >>> a.val⟩ else .fail .panic := rfl

theorem ishr_eq {ty} (x : IScalar ty) (a : Std.U32) :
    (x >>> a : RustM (IScalar ty)) =
      if a.val < ty.numBits then .ok ⟨x.bv.sshiftRight a.val⟩ else .fail .panic := rfl

/-! ## 32-bit words -/

namespace W32
open word.Word32.Insts.P3_wordWordSealedSealed

theorem xor_eq (x y : word.Word32) : xor x y = RustM.ok ⟨x.bv ^^^ y.bv⟩ := by
  simp [word.Word32.Insts.P3_wordWordSealedSealed.xor, Plonky3Lean.Lib.lift_eq]; rfl

theorem and_eq (x y : word.Word32) : and x y = RustM.ok ⟨x.bv &&& y.bv⟩ := by
  simp [word.Word32.Insts.P3_wordWordSealedSealed.and, Plonky3Lean.Lib.lift_eq]; rfl

theorem logical_left_eq (x : word.Word32) (a : Std.U32) :
    logical_left x a = if a.val < 32 then RustM.ok ⟨x.bv <<< a.val⟩ else RustM.fail .panic := by
  simp [logical_left, ushl_eq]

theorem logical_right_eq (x : word.Word32) (a : Std.U32) :
    logical_right x a = if a.val < 32 then RustM.ok ⟨x.bv >>> a.val⟩ else RustM.fail .panic := by
  simp [logical_right, ushr_eq]

theorem arithmetic_right_eq (x : word.Word32) (a : Std.U32) :
    arithmetic_right x a =
      if a.val < 32 then RustM.ok ⟨x.bv.sshiftRight a.val⟩ else RustM.fail .panic := by
  simp only [arithmetic_right, ishr_eq, Plonky3Lean.Lib.lift_eq, bind_ok,
    IScalarTy.I32_numBits_eq]
  by_cases h : a.val < 32
  · simp only [h, ite_true, bind_ok, UScalar.hcast, IScalar.hcast]
    congr 1
    simp
  · simp [h]

theorem rotate_right_eq (x : word.Word32) (a : Std.U32) :
    rotate_right x a = RustM.ok ⟨x.bv.rotateRight a.val⟩ := by
  simp [rotate_right, Plonky3Lean.Lib.u32_rotate_right_eq]

theorem lane32_left_eq (x : word.Word32) (a : Std.U32) :
    lane32_left x a = RustM.ok .None := rfl

theorem lane32_right_eq (x : word.Word32) (a : Std.U32) :
    lane32_right x a = RustM.ok .None := rfl

theorem lane32_arithmetic_right_eq (x : word.Word32) (a : Std.U32) :
    lane32_arithmetic_right x a = RustM.ok .None := rfl

theorem lane32_rotate_right_eq (x : word.Word32) (a : Std.U32) :
    lane32_rotate_right x a = RustM.ok .None := rfl

/-- The full product: the low word is the product modulo `2^32`, the high word its quotient. -/
theorem wide_mul_spec (x y : word.Word32) :
    ∃ lo hi : word.Word32, wide_mul x y = RustM.ok (lo, hi) ∧
      lo.val = x.val * y.val % 2 ^ 32 ∧ hi.val = x.val * y.val / 2 ^ 32 := by
  have hx : x.val < 2 ^ 32 := x.hBounds
  have hy : y.val < 2 ^ 32 := y.hBounds
  have hc : ∀ v : word.Word32, (UScalar.cast .U64 v).val = v.val :=
    fun v => UScalar.cast_val_mod_pow_greater_numBits_eq _ _ (by decide)
  have hmax : (UScalar.cast .U64 x).val * (UScalar.cast .U64 y).val ≤ UScalar.max .U64 := by
    have := Nat.mul_le_mul (Nat.le_pred_of_lt hx) (Nat.le_pred_of_lt hy)
    rw [hc, hc]; simp only [UScalar.max, UScalarTy.U64_numBits_eq]
    exact this.trans (by norm_num)
  obtain ⟨z, hz, hzv⟩ := spec_imp_exists (UScalar.mul_spec hmax)
  rw [hc, hc] at hzv
  simp only [wide_mul, core.U64.Insts.CoreConvertFromU32.from, bind_ok, hz, lift_eq,
    shiftRight_i32_eq z 32#i32 (by decide) (by decide)]
  refine ⟨_, _, rfl, ?_, ?_⟩
  · rw [UScalar.cast_val_eq, hzv]; rfl
  · rw [UScalar.cast_val_eq]
    show (z.bv >>> 32).toNat % 2 ^ 32 = _
    rw [BitVec.toNat_ushiftRight, UScalar.bv_toNat, hzv, Nat.shiftRight_eq_div_pow]
    exact Nat.mod_eq_of_lt (by rw [Nat.div_lt_iff_lt_mul (by norm_num)]; nlinarith)

end W32

/-! ## 64-bit words -/

theorem cast32_bv (x : Std.U64) : (UScalar.cast .U32 x).bv = x.bv.extractLsb' 0 32 := by
  ext i hi; simp [UScalar.cast_bv_eq] at *

theorem cast32_high_bv (x : Std.U64) :
    (UScalar.cast .U32 (⟨x.bv >>> 32⟩ : Std.U64)).bv = x.bv.extractLsb' 32 32 := by
  ext i hi; simp [UScalar.cast_bv_eq] at *

theorem join_bv (lo hi : Std.U32) :
    (UScalar.cast .U64 lo ||| (⟨(UScalar.cast .U64 hi).bv <<< 32⟩ : Std.U64)).bv = hi.bv ++ lo.bv := by
  ext i hi'
  simp only [UScalarTy.U64_numBits_eq] at hi'
  have hlo : i ≥ 32 → lo.bv.getLsbD i = false := fun h => BitVec.getLsbD_of_ge _ _ (by simpa using h)
  simp only [UScalar.cast_bv_eq, or_bv, ← BitVec.getLsbD_eq_getElem, BitVec.getLsbD_or,
    BitVec.getLsbD_append]
  by_cases h : i < 32
  · simp [h, hi']
  · simp [h, hi', hlo (by omega)]

theorem u64_mk_bv (x : Std.U64) : (⟨x.bv⟩ : Std.U64) = x := rfl

theorem i32_32_toNat : I32.toNat 32#i32 = 32 := by decide

/-- The tail shared by the four lane operations: the two lane results, joined. -/
theorem lane_join (f : BitVec 32 → BitVec 32) (x : Std.U64) (lo hi : Std.U32)
    (hlo : lo.bv = f (x.bv.extractLsb' 0 32)) (hhi : hi.bv = f (x.bv.extractLsb' 32 32)) :
    (do
      let i3 ← core.U64.Insts.CoreConvertFromU32.from lo
      let i4 ← core.U64.Insts.CoreConvertFromU32.from hi
      let i5 ← i4 <<< 32#i32
      RustM.ok (core.option.Option.Some (i3 ||| i5))) =
      RustM.ok (.Some (⟨lanes f x.bv⟩ : Std.U64)) := by
  simp only [core.U64.Insts.CoreConvertFromU32.from, bind_ok,
    shiftLeft_i32_eq (UScalar.cast .U64 hi) 32#i32 (by decide) (by decide), i32_32_toNat]
  have : (UScalar.cast .U64 lo ||| (⟨(UScalar.cast .U64 hi).bv <<< 32⟩ : Std.U64)) =
      ⟨lanes f x.bv⟩ :=
    (UScalar.eq_equiv_bv_eq _ _).mpr (by rw [join_bv, hlo, hhi]; rfl)
  rw [this]

namespace W64
open word.Word64.Insts.P3_wordWordSealedSealed

theorem xor_eq (x y : word.Word64) : xor x y = RustM.ok ⟨x.bv ^^^ y.bv⟩ := by
  simp [word.Word64.Insts.P3_wordWordSealedSealed.xor, lift_eq]; rfl

theorem and_eq (x y : word.Word64) : and x y = RustM.ok ⟨x.bv &&& y.bv⟩ := by
  simp [word.Word64.Insts.P3_wordWordSealedSealed.and, lift_eq]; rfl

theorem logical_left_eq (x : word.Word64) (a : Std.U32) :
    logical_left x a = if a.val < 64 then RustM.ok ⟨x.bv <<< a.val⟩ else RustM.fail .panic := by
  simp [logical_left, ushl_eq]

theorem logical_right_eq (x : word.Word64) (a : Std.U32) :
    logical_right x a = if a.val < 64 then RustM.ok ⟨x.bv >>> a.val⟩ else RustM.fail .panic := by
  simp [logical_right, ushr_eq]

theorem arithmetic_right_eq (x : word.Word64) (a : Std.U32) :
    arithmetic_right x a =
      if a.val < 64 then RustM.ok ⟨x.bv.sshiftRight a.val⟩ else RustM.fail .panic := by
  simp only [arithmetic_right, ishr_eq, lift_eq, bind_ok, IScalarTy.I64_numBits_eq]
  by_cases h : a.val < 64
  · simp only [h, ite_true, bind_ok, UScalar.hcast, IScalar.hcast]
    congr 1
    simp
  · simp [h]

theorem rotate_right_eq (x : word.Word64) (a : Std.U32) :
    rotate_right x a = RustM.ok ⟨x.bv.rotateRight a.val⟩ := by
  simp [rotate_right, u64_rotate_right_eq]

theorem lane32_left_eq (x : word.Word64) (a : Std.U32) :
    lane32_left x a = if a.val < 32 then RustM.ok (.Some ⟨lanes (· <<< a.val) x.bv⟩)
      else RustM.fail .panic := by
  by_cases h : a.val < 32
  · simp only [lane32_left, lift_eq, bind_ok, ushl_eq, UScalarTy.U32_numBits_eq, h, ite_true,
      shiftRight_i32_eq x 32#i32 (by decide) (by decide), i32_32_toNat]
    exact lane_join (· <<< a.val) x _ _ (by show (UScalar.cast .U32 x).bv <<< a.val = _; rw [cast32_bv])
      (by show (UScalar.cast .U32 (⟨x.bv >>> 32⟩ : Std.U64)).bv <<< a.val = _
          rw [cast32_high_bv])
  · simp [lane32_left, ushl_eq, h, lift_eq]

theorem lane32_right_eq (x : word.Word64) (a : Std.U32) :
    lane32_right x a = if a.val < 32 then RustM.ok (.Some ⟨lanes (· >>> a.val) x.bv⟩)
      else RustM.fail .panic := by
  by_cases h : a.val < 32
  · simp only [lane32_right, lift_eq, bind_ok, ushr_eq, UScalarTy.U32_numBits_eq, h, ite_true,
      shiftRight_i32_eq x 32#i32 (by decide) (by decide), i32_32_toNat]
    exact lane_join (· >>> a.val) x _ _ (by show (UScalar.cast .U32 x).bv >>> a.val = _; rw [cast32_bv])
      (by show (UScalar.cast .U32 (⟨x.bv >>> 32⟩ : Std.U64)).bv >>> a.val = _
          rw [cast32_high_bv])
  · simp [lane32_right, ushr_eq, h, lift_eq]

theorem lane32_rotate_right_eq (x : word.Word64) (a : Std.U32) :
    lane32_rotate_right x a = RustM.ok (.Some ⟨lanes (·.rotateRight a.val) x.bv⟩) := by
  simp only [lane32_rotate_right, lift_eq, bind_ok, u32_rotate_right_eq,
    shiftRight_i32_eq x 32#i32 (by decide) (by decide), i32_32_toNat]
  exact lane_join (·.rotateRight a.val) x _ _
    (by show (UScalar.cast .U32 x).bv.rotateRight a.val = _; rw [cast32_bv])
    (by show (UScalar.cast .U32 (⟨x.bv >>> 32⟩ : Std.U64)).bv.rotateRight a.val = _
        rw [cast32_high_bv])

theorem lane32_arithmetic_right_eq (x : word.Word64) (a : Std.U32) :
    lane32_arithmetic_right x a =
      if a.val < 32 then RustM.ok (.Some ⟨lanes (·.sshiftRight a.val) x.bv⟩)
      else RustM.fail .panic := by
  by_cases h : a.val < 32
  · simp only [lane32_arithmetic_right, lift_eq, bind_ok, ishr_eq, IScalarTy.I32_numBits_eq, h,
      ite_true, shiftRight_i32_eq x 32#i32 (by decide) (by decide), i32_32_toNat]
    refine lane_join (·.sshiftRight a.val) x _ _ ?_ ?_
    · simp only [IScalar.hcast, UScalar.hcast, cast32_bv]; simp
    · simp only [IScalar.hcast, UScalar.hcast]
      rw [show (UScalar.cast .U32 (⟨x.bv >>> 32⟩ : Std.U64)).bv = _ from cast32_high_bv x]; simp
  · simp [lane32_arithmetic_right, ishr_eq, h, lift_eq]

/-- The full product: the low word is the product modulo `2^64`, the high word its quotient. -/
theorem wide_mul_spec (x y : word.Word64) :
    ∃ lo hi : word.Word64, wide_mul x y = RustM.ok (lo, hi) ∧
      lo.val = x.val * y.val % 2 ^ 64 ∧ hi.val = x.val * y.val / 2 ^ 64 := by
  have hx : x.val < 2 ^ 64 := x.hBounds
  have hy : y.val < 2 ^ 64 := y.hBounds
  have hc : ∀ v : word.Word64, (UScalar.cast .U128 v).val = v.val :=
    fun v => UScalar.cast_val_mod_pow_greater_numBits_eq _ _ (by decide)
  have hmax : (UScalar.cast .U128 x).val * (UScalar.cast .U128 y).val ≤ UScalar.max .U128 := by
    have := Nat.mul_le_mul (Nat.le_pred_of_lt hx) (Nat.le_pred_of_lt hy)
    rw [hc, hc]; simp only [UScalar.max, UScalarTy.U128_numBits_eq]
    exact this.trans (by norm_num)
  obtain ⟨z, hz, hzv⟩ := spec_imp_exists (UScalar.mul_spec hmax)
  rw [hc, hc] at hzv
  simp only [wide_mul, from_u64_u128_eq, bind_ok, hz, lift_eq,
    shiftRight_i32_eq z 64#i32 (by decide) (by decide)]
  refine ⟨_, _, rfl, ?_, ?_⟩
  · rw [UScalar.cast_val_eq, hzv]; rfl
  · rw [UScalar.cast_val_eq]
    show (z.bv >>> 64).toNat % 2 ^ 64 = _
    rw [BitVec.toNat_ushiftRight, UScalar.bv_toNat, hzv, Nat.shiftRight_eq_div_pow]
    exact Nat.mod_eq_of_lt (by rw [Nat.div_lt_iff_lt_mul (by norm_num)]; nlinarith)

end W64

end Plonky3Lean.Proofs.Word
