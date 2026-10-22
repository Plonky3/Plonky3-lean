module

public import Aeneas
public import CoreModels
public import HaxExt

@[expose] public section

/-!
# Rust bit operations, as bit vectors

Straight-line bit manipulation evaluates to `ok` of a bit-vector expression.

Each lemma states one operation exactly, together with the condition under which it cannot panic.
-/

open Aeneas Aeneas.Std CoreModels

namespace Plonky3Lean.Lib

theorem lift_eq {α : Type} (x : α) : lift x = .ok x := rfl

/-- A bind whose first step is known to return `v` continues with `v`. -/
theorem spec_bind_of_eq {α β : Type} {m : RustM α} {v : α} {k : α → RustM β} {P : β → Prop}
    (h : m = .ok v) (hk : k v ⦃ P ⦄) : (m >>= k) ⦃ P ⦄ := by
  rw [h, bind_tc_ok]
  exact hk

/-- A bind on a pair known to be `(a, b)` continues with `a` and `b`. -/
theorem spec_bind_pair_of_eq {α β γ : Type} {m : RustM (α × β)} {a : α} {b : β}
    {k : α → β → RustM γ} {P : γ → Prop} (h : m = .ok (a, b)) (hk : k a b ⦃ P ⦄) :
    (m >>= Aeneas.Std.uncurry k) ⦃ P ⦄ := by
  rw [h, bind_tc_ok]
  exact hk

/-- A left shift by a nonnegative `i32` below the width. -/
theorem shiftLeft_i32_eq {ty} (x : UScalar ty) (s : Std.I32) (h0 : 0 ≤ s.val)
    (h : s.toNat < ty.numBits) : (x <<< s : RustM (UScalar ty)) = .ok ⟨x.bv <<< s.toNat⟩ := by
  show UScalar.shiftLeft_IScalar x s = _
  simp only [UScalar.shiftLeft_IScalar, UScalar.shiftLeft, if_pos h0, if_pos h]
  rfl

/-- A logical right shift by a nonnegative `i32` below the width. -/
theorem shiftRight_i32_eq {ty} (x : UScalar ty) (s : Std.I32) (h0 : 0 ≤ s.val)
    (h : s.toNat < ty.numBits) : (x >>> s : RustM (UScalar ty)) = .ok ⟨x.bv >>> s.toNat⟩ := by
  show UScalar.shiftRight_IScalar x s = _
  simp only [UScalar.shiftRight_IScalar, UScalar.shiftRight, if_pos h0, if_pos h]
  rfl

theorem wrapping_mul_u64_eq (x y : Std.U64) :
    CoreModels.core.num.U64.wrapping_mul x y = .ok ⟨x.bv * y.bv⟩ := rfl

theorem wrapping_sub_u8_eq (x y : Std.U8) :
    CoreModels.core.num.U8.wrapping_sub x y = .ok ⟨x.bv - y.bv⟩ := rfl

theorem reverse_bits_u64_eq (x : Std.U64) :
    CoreModels.core.num.U64.reverse_bits x = .ok ⟨x.bv.reverse⟩ := rfl

theorem from_u64_u128_eq (x : Std.U64) :
    CoreModels.core.U128.Insts.CoreConvertFromU64.from x = .ok (UScalar.cast .U128 x) := rfl

theorem and_bv {ty} (x y : UScalar ty) : (x &&& y).bv = x.bv &&& y.bv := rfl

theorem or_bv {ty} (x y : UScalar ty) : (x ||| y).bv = x.bv ||| y.bv := rfl

theorem xor_bv {ty} (x y : UScalar ty) : (x ^^^ y).bv = x.bv ^^^ y.bv := rfl

theorem cast_bv {ty} (ty' : UScalarTy) (x : UScalar ty) :
    (UScalar.cast ty' x).bv = x.bv.setWidth ty'.numBits := rfl

end Plonky3Lean.Lib
