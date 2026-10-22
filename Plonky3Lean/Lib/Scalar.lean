import Aeneas
import CoreModels
import HaxExt

/-!
# Rust integer primitives, as natural numbers

The extracted code calls `core::num` through `CoreModels`, which wraps each method in `RustM`.

These are their specifications on `.val`, tagged `@[step]` so that `step*` applies them.

Each lemma states the whole behaviour:

- an `overflowing_*` returns the wrapped value and whether it wrapped,
- a `wrapping_*` returns the value modulo the width.

A proof that uses them never reasons about `BitVec`.
-/

open Aeneas Aeneas.Std CoreModels

namespace Plonky3Lean.Lib

theorem size_u32 : UScalar.size .U32 = 2 ^ 32 := by
  simp only [UScalar.size, UScalarTy.U32_numBits_eq]

theorem size_u64 : UScalar.size .U64 = 2 ^ 64 := by
  simp only [UScalar.size, UScalarTy.U64_numBits_eq]

theorem size_u128 : UScalar.size .U128 = 2 ^ 128 := by
  simp only [UScalar.size, UScalarTy.U128_numBits_eq]

/-! ## Casts -/

@[simp]
theorem cast_u32_u64_val (x : Std.U32) : (UScalar.cast .U64 x).val = x.val := by
  have := x.hBounds
  rw [UScalar.cast_val_eq, UScalarTy.U64_numBits_eq]
  rw [UScalarTy.U32_numBits_eq] at this
  omega

@[simp]
theorem cast_u32_u128_val (x : Std.U32) : (UScalar.cast .U128 x).val = x.val := by
  have := x.hBounds
  rw [UScalar.cast_val_eq, UScalarTy.U128_numBits_eq]
  rw [UScalarTy.U32_numBits_eq] at this
  omega

@[simp]
theorem cast_u64_u128_val (x : Std.U64) : (UScalar.cast .U128 x).val = x.val := by
  have := x.hBounds
  rw [UScalar.cast_val_eq, UScalarTy.U128_numBits_eq]
  rw [UScalarTy.U64_numBits_eq] at this
  omega

@[simp]
theorem cast_u64_u32_val (x : Std.U64) : (UScalar.cast .U32 x).val = x.val % 2 ^ 32 := by
  rw [UScalar.cast_val_eq, UScalarTy.U32_numBits_eq]

@[simp]
theorem cast_u128_u64_val (x : Std.U128) : (UScalar.cast .U64 x).val = x.val % 2 ^ 64 := by
  rw [UScalar.cast_val_eq, UScalarTy.U64_numBits_eq]

@[simp]
theorem cast_u128_u32_val (x : Std.U128) : (UScalar.cast .U32 x).val = x.val % 2 ^ 32 := by
  rw [UScalar.cast_val_eq, UScalarTy.U32_numBits_eq]

theorem u32_lt (x : Std.U32) : x.val < 2 ^ 32 := by
  have := x.hBounds; rwa [UScalarTy.U32_numBits_eq] at this

theorem u64_lt (x : Std.U64) : x.val < 2 ^ 64 := by
  have := x.hBounds; rwa [UScalarTy.U64_numBits_eq] at this

/-! ## `overflowing_sub` -/

theorem overflowing_sub_val {ty} (x y : UScalar ty) :
    (UScalar.overflowing_sub x y).2 = decide (x.val < y.val) ∧
      (UScalar.overflowing_sub x y).1.val = (x.val + UScalar.size ty - y.val) % UScalar.size ty := by
  have h := UScalar.overflowing_sub_eq x y
  have hs : UScalar.size ty = 2 ^ ty.numBits := by simp only [UScalar.size]
  have hx := x.hBounds
  have hy := y.hBounds
  have hr := (UScalar.overflowing_sub x y).1.hBounds
  split at h <;> rename_i hlt <;> obtain ⟨h1, h2⟩ := h
  · refine ⟨by simp [h2, hlt], ?_⟩
    rw [Nat.mod_eq_of_lt (by omega)]
    omega
  · refine ⟨by simp [h2, hlt], ?_⟩
    rw [show x.val + UScalar.size ty - y.val = (x.val - y.val) + UScalar.size ty by omega,
      Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    omega

@[step]
theorem core.num.U32.overflowing_sub.spec (x y : Std.U32) :
    CoreModels.core.num.U32.overflowing_sub x y ⦃ r =>
      r.2 = decide (x.val < y.val) ∧ r.1.val = (x.val + 2 ^ 32 - y.val) % 2 ^ 32 ⦄ := by
  simp only [CoreModels.core.num.U32.overflowing_sub,
    CoreModels.rust_primitives.arithmetic.overflowing_sub_u32, WP.spec_ok]
  rw [← size_u32]; exact overflowing_sub_val x y

@[step]
theorem core.num.U64.overflowing_sub.spec (x y : Std.U64) :
    CoreModels.core.num.U64.overflowing_sub x y ⦃ r =>
      r.2 = decide (x.val < y.val) ∧ r.1.val = (x.val + 2 ^ 64 - y.val) % 2 ^ 64 ⦄ := by
  simp only [CoreModels.core.num.U64.overflowing_sub,
    CoreModels.rust_primitives.arithmetic.overflowing_sub_u64, WP.spec_ok]
  rw [← size_u64]; exact overflowing_sub_val x y

/-! ## `wrapping_*` -/

@[step]
theorem core.num.U32.wrapping_add.spec (x y : Std.U32) :
    CoreModels.core.num.U32.wrapping_add x y ⦃ r => r.val = (x.val + y.val) % 2 ^ 32 ⦄ := by
  simp only [CoreModels.core.num.U32.wrapping_add,
    CoreModels.rust_primitives.arithmetic.wrapping_add_u32, WP.spec_ok,
    U32.wrapping_add_val_eq, size_u32]

@[step]
theorem core.num.U32.wrapping_mul.spec (x y : Std.U32) :
    CoreModels.core.num.U32.wrapping_mul x y ⦃ r => r.val = x.val * y.val % 2 ^ 32 ⦄ := by
  simp only [CoreModels.core.num.U32.wrapping_mul,
    CoreModels.rust_primitives.arithmetic.wrapping_mul_u32, WP.spec_ok,
    U32.wrapping_mul_val_eq, size_u32]

@[step]
theorem core.num.U64.wrapping_mul.spec (x y : Std.U64) :
    CoreModels.core.num.U64.wrapping_mul x y ⦃ r => r.val = x.val * y.val % 2 ^ 64 ⦄ := by
  simp only [CoreModels.core.num.U64.wrapping_mul,
    CoreModels.rust_primitives.arithmetic.wrapping_mul_u64, WP.spec_ok,
    U64.wrapping_mul_val_eq, size_u64]

@[step]
theorem core.num.U64.wrapping_sub.spec (x y : Std.U64) :
    CoreModels.core.num.U64.wrapping_sub x y ⦃ r => r.val = (x.val + 2 ^ 64 - y.val) % 2 ^ 64 ⦄ := by
  simp only [CoreModels.core.num.U64.wrapping_sub,
    CoreModels.rust_primitives.arithmetic.wrapping_sub_u64, WP.spec_ok,
    U64.wrapping_sub_val_eq, size_u64]
  have := y.hBounds
  rw [UScalarTy.U64_numBits_eq] at this
  congr 1; omega

@[step]
theorem core.num.U32.wrapping_add_signed.spec (x : Std.U32) (y : Std.I32) :
    CoreModels.core.num.U32.wrapping_add_signed x y ⦃ r =>
      (r.val : ℤ) = (x.val + y.val) % 2 ^ 32 ⦄ := by
  simp only [CoreModels.core.num.U32.wrapping_add_signed, WP.spec_ok,
    U32.wrapping_add_val_eq, IScalar.hcast_val_eq, size_u32, UScalarTy.U32_numBits_eq]
  have h0 : (0 : ℤ) ≤ y.val % 4294967296 := Int.emod_nonneg _ (by norm_num)
  push_cast
  rw [Int.toNat_of_nonneg h0, Int.add_emod_emod]

end Plonky3Lean.Lib
