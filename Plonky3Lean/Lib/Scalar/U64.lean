import HaxExt
import Plonky3Lean.Lib.Scalar

/-!
# `u64` and `u128` primitives, as natural numbers

More `@[step]` specifications of `core::num` and `core::convert`, for code that
works with 64-bit words and their 128-bit products.
-/

open Aeneas Aeneas.Std CoreModels

namespace Plonky3Lean.Lib

/-! ## `overflowing_add` -/

theorem overflowing_add_val {ty} (x y : UScalar ty) :
    (UScalar.overflowing_add x y).2 = decide (UScalar.size ty ≤ x.val + y.val) ∧
      (UScalar.overflowing_add x y).1.val = (x.val + y.val) % UScalar.size ty := by
  have h := UScalar.overflowing_add_eq x y
  have hs : UScalar.size ty = 2 ^ ty.numBits := by simp only [UScalar.size]
  have hm : UScalar.max ty = 2 ^ ty.numBits - 1 := by simp only [UScalar.max]
  have hx := x.hBounds
  have hy := y.hBounds
  have hr := (UScalar.overflowing_add x y).1.hBounds
  have hpos : 0 < 2 ^ ty.numBits := Nat.two_pow_pos _
  split at h <;> rename_i hlt <;> obtain ⟨h1, h2⟩ := h
  · refine ⟨?_, ?_⟩
    · rw [h2]; symm; simp only [decide_eq_true_eq]; omega
    rw [show x.val + y.val = (UScalar.overflowing_add x y).1.val + UScalar.size ty by omega,
      Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
  · refine ⟨?_, ?_⟩
    · rw [h2]; symm; simp only [decide_eq_false_iff_not]; omega
    rw [Nat.mod_eq_of_lt (by omega)]
    omega

@[step]
theorem core.num.U64.overflowing_add.spec (x y : Std.U64) :
    CoreModels.core.num.U64.overflowing_add x y ⦃ r =>
      r.2 = decide (2 ^ 64 ≤ x.val + y.val) ∧ r.1.val = (x.val + y.val) % 2 ^ 64 ⦄ := by
  simp only [CoreModels.core.num.U64.overflowing_add,
    CoreModels.rust_primitives.arithmetic.overflowing_add_u64, WP.spec_ok]
  rw [← size_u64]; exact overflowing_add_val x y

@[step]
theorem core.num.U128.overflowing_add.spec (x y : Std.U128) :
    CoreModels.core.num.U128.overflowing_add x y ⦃ r =>
      r.2 = decide (2 ^ 128 ≤ x.val + y.val) ∧ r.1.val = (x.val + y.val) % 2 ^ 128 ⦄ := by
  simp only [CoreModels.core.num.U128.overflowing_add,
    CoreModels.rust_primitives.arithmetic.overflowing_add_u128, WP.spec_ok]
  rw [← size_u128]; exact overflowing_add_val x y

/-! ## `wrapping_*` -/

@[step]
theorem core.num.U64.wrapping_add.spec (x y : Std.U64) :
    CoreModels.core.num.U64.wrapping_add x y ⦃ r => r.val = (x.val + y.val) % 2 ^ 64 ⦄ := by
  simp only [CoreModels.core.num.U64.wrapping_add,
    CoreModels.rust_primitives.arithmetic.wrapping_add_u64, WP.spec_ok,
    U64.wrapping_add_val_eq, size_u64]

@[step]
theorem core.num.U128.wrapping_add.spec (x y : Std.U128) :
    CoreModels.core.num.U128.wrapping_add x y ⦃ r => r.val = (x.val + y.val) % 2 ^ 128 ⦄ := by
  simp only [CoreModels.core.num.U128.wrapping_add,
    CoreModels.rust_primitives.arithmetic.wrapping_add_u128, WP.spec_ok,
    U128.wrapping_add_val_eq, size_u128]

@[step]
theorem core.num.U128.wrapping_sub.spec (x y : Std.U128) :
    CoreModels.core.num.U128.wrapping_sub x y ⦃ r =>
      r.val = (x.val + 2 ^ 128 - y.val) % 2 ^ 128 ⦄ := by
  simp only [CoreModels.core.num.U128.wrapping_sub,
    CoreModels.rust_primitives.arithmetic.wrapping_sub_u128, WP.spec_ok,
    U128.wrapping_sub_val_eq, size_u128]
  have := y.hBounds
  rw [UScalarTy.U128_numBits_eq] at this
  congr 1; omega

@[step]
theorem core.num.U64.wrapping_neg.spec (x : Std.U64) :
    CoreModels.core.num.U64.wrapping_neg x ⦃ r => r.val = (2 ^ 64 - x.val) % 2 ^ 64 ⦄ := by
  unfold CoreModels.core.num.U64.wrapping_neg
  simp only [CoreModels.rust_primitives.arithmetic.wrapping_sub_u64, WP.spec_ok,
    U64.wrapping_sub_val_eq, size_u64]
  simp

/-- `u64::wrapping_add_signed(x, y)` is `x + y` modulo `2^64`, for a signed `y`. -/
@[step]
theorem core.num.U64.wrapping_add_signed.spec (x : Std.U64) (y : Std.I64) :
    CoreModels.core.num.U64.wrapping_add_signed x y ⦃ r =>
      (r.val : ℤ) = (x.val + y.val) % 2 ^ 64 ⦄ := by
  unfold CoreModels.core.num.U64.wrapping_add_signed
  simp only [CoreModels.core.num.U64.wrapping_add,
    CoreModels.rust_primitives.arithmetic.wrapping_add_u64, WP.spec_ok,
    U64.wrapping_add_val_eq, size_u64, IScalar.hcast_val_eq, UScalarTy.U64_numBits_eq]
  have h0 : (0 : ℤ) ≤ y.val % 2 ^ 64 := Int.emod_nonneg _ (by norm_num)
  rw [Int.natCast_mod, Nat.cast_add, Int.toNat_of_nonneg h0]
  push_cast
  rw [Int.add_emod, Int.emod_emod_of_dvd _ (by norm_num), ← Int.add_emod]

/-! ## Conversions -/

@[step]
theorem core.U64.from_bool.spec (b : Bool) :
    CoreModels.core.U64.Insts.CoreConvertFromBool.from b ⦃ r => r.val = if b then 1 else 0 ⦄ := by
  unfold CoreModels.core.U64.Insts.CoreConvertFromBool.from
  by_cases hb : b <;> simp [hb]

@[step]
theorem core.U128.from_u64.spec (x : Std.U64) :
    CoreModels.core.U128.Insts.CoreConvertFromU64.from x ⦃ r => r.val = x.val ⦄ := by
  unfold CoreModels.core.U128.Insts.CoreConvertFromU64.from
  simp only [WP.spec_ok, cast_u64_u128_val]

/-- `i128::unsigned_abs` is the absolute value. -/
@[step]
theorem core.num.I128.unsigned_abs.spec (x : Std.I128) :
    CoreModels.core.num.I128.unsigned_abs x ⦃ r => r.val = x.val.natAbs ⦄ := by
  unfold CoreModels.core.num.I128.unsigned_abs
  simp only [WP.spec_ok]
  have h := x.hBounds
  simp only [IScalarTy.I128_numBits_eq] at h
  show (BitVec.ofNat _ x.val.natAbs).toNat = _
  rw [BitVec.toNat_ofNat, UScalarTy.U128_numBits_eq, Nat.mod_eq_of_lt]
  omega

/-! ## Hints -/

/-- `assert_unchecked(cond)` does not fail exactly when `cond` holds. -/
@[step]
theorem core.hint.assert_unchecked.spec (b : Bool) (h : b = true) :
    CoreModels.core.hint.assert_unchecked b ⦃ _ => True ⦄ := by
  simp [CoreModels.core.hint.assert_unchecked, h]

end Plonky3Lean.Lib
