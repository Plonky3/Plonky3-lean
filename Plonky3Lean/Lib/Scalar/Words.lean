module

public import Aeneas
public import CoreModels
public import HaxExt

@[expose] public section

/-!
# 32-bit word operations, as bit vectors

The hash functions compute on `u32` words with rotations, wrapping additions and bitwise operations.

Each lemma rewrites one such call to `ok` of a bit-vector expression, so that straight-line code evaluates by `simp`.
-/

open Aeneas Aeneas.Std CoreModels

namespace Plonky3Lean.Lib

theorem u32_rotate_right_eq (x n : Std.U32) :
    CoreModels.core.num.U32.rotate_right x n = .ok ⟨x.bv.rotateRight n.val⟩ := by
  unfold CoreModels.core.num.U32.rotate_right
  simp only [HMod.hMod]
  have hr : UScalar.rem n 32#u32 = .ok ⟨n.bv % 32#32⟩ := by
    simp [UScalar.rem]
  rw [hr, bind_ok]
  have hm : (⟨n.bv % 32#32⟩ : Std.U32).val = n.val % 32 := by
    show (n.bv % 32#32).toNat = _
    rw [BitVec.toNat_umod, UScalar.bv_toNat]
    rfl
  split
  · rename_i h0
    have h0' : n.val % 32 = 0 := by rw [← hm, h0]; rfl
    congr 1
    rw [← BitVec.rotateRight_mod_eq_rotateRight, h0']
    cases x
    simp [BitVec.rotateRight, BitVec.rotateRightAux]
    exact (BitVec.or_zero ..).symm
  · rename_i h0
    have hpos : n.val % 32 ≠ 0 := fun h => h0 (UScalar.eq_of_val_eq (by rw [hm, h]; rfl))
    have hlt : n.val % 32 < 32 := Nat.mod_lt _ (by norm_num)
    simp only [HShiftRight.hShiftRight, HShiftLeft.hShiftLeft, HSub.hSub]
    simp only [UScalar.shiftRight_UScalar, UScalar.shiftRight, UScalar.sub, hm]
    have h32 : (32#u32).val = 32 := rfl
    simp only [UScalarTy.U32_numBits_eq, hlt, ite_true, h32, show ¬ 32 < n.val % 32 by omega,
      ite_false, bind_ok, UScalar.shiftLeft_UScalar, UScalar.shiftLeft]
    have hsub : (⟨BitVec.ofNat 32 (32 - n.val % 32)⟩ : Std.U32).val = 32 - n.val % 32 := by
      show (BitVec.ofNat 32 _).toNat = _
      rw [BitVec.toNat_ofNat]; omega
    rw [hsub]
    simp only [show 32 - n.val % 32 < 32 by omega, ite_true, bind_ok]
    congr 2
    rw [BitVec.rotateRight_def]
    ext i hi
    simp only [UScalarTy.U32_numBits_eq] at hi
    simp only [BitVec.getElem_or]
    simp only [BitVec.getElem_ushiftRight, BitVec.getElem_shiftLeft, UScalarTy.U32_numBits_eq]
    by_cases h : i < 32 - n.val % 32
    · simp [h]
    · have : x.bv.getLsbD (n.val % 32 + i) = false :=
        BitVec.getLsbD_of_ge _ _ (by show 32 ≤ _; omega)
      simp [h, this]

theorem u32_wrapping_add_eq (x y : Std.U32) :
    CoreModels.core.num.U32.wrapping_add x y = .ok ⟨x.bv + y.bv⟩ := rfl

theorem lift_eq {α : Type} (x : α) : lift x = .ok x := rfl

/-- A logical right shift by a nonnegative `i32` below the width. -/
theorem u32_shiftRight_i32_eq (x : Std.U32) (s : Std.I32) (h0 : 0 ≤ s.val) (h : s.toNat < 32) :
    (x >>> s : RustM Std.U32) = .ok ⟨x.bv >>> s.toNat⟩ := by
  show UScalar.shiftRight_IScalar x s = _
  simp only [UScalar.shiftRight_IScalar, UScalar.shiftRight, ite_eq_left h0,
    ite_eq_left (show s.toNat < UScalarTy.U32.numBits from h)]
  rfl

theorem u32_bv_mk (x : BitVec UScalarTy.U32.numBits) : (⟨x⟩ : Std.U32).bv = x := rfl

theorem u32_mk_bv (x : Std.U32) : (⟨x.bv⟩ : Std.U32) = x := rfl

theorem u32_xor_bv (x y : Std.U32) : (x ^^^ y).bv = x.bv ^^^ y.bv := rfl

theorem u32_and_bv (x y : Std.U32) : (x &&& y).bv = x.bv &&& y.bv := rfl

theorem u32_not_bv (x : Std.U32) : (~~~x).bv = ~~~x.bv := rfl

/-- Four big-endian bytes, as one word. -/
theorem fromBEBytes_four (b₀ b₁ b₂ b₃ : BitVec 8) :
    (BitVec.fromBEBytes [b₀, b₁, b₂, b₃]).cast (by simp) = b₀ ++ b₁ ++ b₂ ++ b₃ := by
  ext i hi
  simp only [BitVec.getElem_cast]
  simp [BitVec.fromBEBytes]
  have hq : i / 8 < 4 := by omega
  rcases (by omega : i / 8 = 0 ∨ i / 8 = 1 ∨ i / 8 = 2 ∨ i / 8 = 3) with h | h | h | h <;>
    simp [h, Byte.testBit, BitVec.testBit_toNat]
  all_goals
    rw [← BitVec.getLsbD_eq_getElem, BitVec.getLsbD_append, BitVec.getLsbD_append,
      BitVec.getLsbD_append]
    split_ifs <;> first | omega | (congr 1; omega)

end Plonky3Lean.Lib
