module

public import Aeneas
public import CoreModels
public import HaxExt

@[expose] public section

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

theorem size_u8 : UScalar.size .U8 = 2 ^ 8 := by
  simp only [UScalar.size, UScalarTy.U8_numBits_eq]

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

/-- `uoverflowing_sub x y`, the value behind `overflowing_sub` on unsigned integers:
the wrapped difference, and whether it wrapped. The same statement as Aeneas's
`UScalar.overflowing_sub_eq`, for CoreModels' definition. -/
theorem uoverflowing_sub_eq {ty : UScalarTy} (x y : UScalar ty) :
    let z := uoverflowing_sub x y
    if x.val < y.val then
      z.fst.val + y.val = x.val + UScalar.size ty ∧ z.snd = true
    else
      z.fst.val = x.val - y.val ∧ z.snd = false := by
  have hx := x.hBounds
  have hy := y.hBounds
  simp only [uoverflowing_sub, UScalar.size]
  split
  · rename_i h
    refine ⟨?_, by simpa using h⟩
    show (x.bv - y.bv).toNat + y.val = x.val + 2 ^ ty.numBits
    rw [BitVec.toNat_sub]
    simp only [UScalar.bv_toNat] at *
    rw [Nat.mod_eq_of_lt (by omega)]
    omega
  · rename_i h
    refine ⟨?_, by simpa using h⟩
    show (x.bv - y.bv).toNat = x.val - y.val
    rw [BitVec.toNat_sub]
    simp only [UScalar.bv_toNat] at *
    rw [show 2 ^ ty.numBits - y.val + x.val = (x.val - y.val) + 2 ^ ty.numBits by omega,
      Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]

/-- `overflowing_sub_val`, for CoreModels' `uoverflowing_sub`. -/
theorem uoverflowing_sub_val {ty} (x y : UScalar ty) :
    (uoverflowing_sub x y).2 = decide (x.val < y.val) ∧
      (uoverflowing_sub x y).1.val = (x.val + UScalar.size ty - y.val) % UScalar.size ty := by
  have h := uoverflowing_sub_eq x y
  have hs : UScalar.size ty = 2 ^ ty.numBits := by simp only [UScalar.size]
  have hx := x.hBounds
  have hy := y.hBounds
  have hr := (uoverflowing_sub x y).1.hBounds
  simp only at h
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
  rw [← size_u32]; exact uoverflowing_sub_val x y

@[step]
theorem core.num.U64.overflowing_sub.spec (x y : Std.U64) :
    CoreModels.core.num.U64.overflowing_sub x y ⦃ r =>
      r.2 = decide (x.val < y.val) ∧ r.1.val = (x.val + 2 ^ 64 - y.val) % 2 ^ 64 ⦄ := by
  simp only [CoreModels.core.num.U64.overflowing_sub,
    CoreModels.rust_primitives.arithmetic.overflowing_sub_u64, WP.spec_ok]
  rw [← size_u64]; exact uoverflowing_sub_val x y

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
theorem core.num.U8.wrapping_sub.spec (x y : Std.U8) :
    CoreModels.core.num.U8.wrapping_sub x y ⦃ r => r.val = (x.val + 2 ^ 8 - y.val) % 2 ^ 8 ⦄ := by
  simp only [CoreModels.core.num.U8.wrapping_sub,
    CoreModels.rust_primitives.arithmetic.wrapping_sub_u8, WP.spec_ok,
    U8.wrapping_sub_val_eq, size_u8]
  have := y.hBounds
  rw [UScalarTy.U8_numBits_eq] at this
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
