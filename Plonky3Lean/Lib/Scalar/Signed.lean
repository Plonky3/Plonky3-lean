module

public import Plonky3Lean.Lib.Scalar
public import Plonky3Lean.Lib.Scalar.U64
public import HaxExt
-- `IScalar.overflowing_add`'s body, which Aeneas does not expose and which the proofs below unfold.
import all Aeneas.Std.Scalar.OverflowingOps.Add

@[expose] public section

/-!
# Signed integer primitives, as natural numbers and integers

Specifications of the `core::num` methods on signed integers, and of the casts between signed and unsigned integers, that the field crates call.

The `HaxExt` models `Ord::min`, `bool::then` and `i64::unsigned_abs` are specified here too.
-/

open Aeneas Aeneas.Std CoreModels

namespace Plonky3Lean.Lib

/-! ## `u32` and `i32` -/

/-- A `u32` below `2^31` keeps its value as an `i32`. -/
theorem hcast_u32_i32_val (x : Std.U32) (hx : x.val < 2 ^ 31) :
    (UScalar.hcast .I32 x).val = x.val := by
  rw [UScalar.hcast_val_eq]
  simp only [IScalarTy.I32_numBits_eq]
  rw [Int.bmod_def]; split <;> omega

/-- The sum of two non-negative 32-bit signed values: its bits read as unsigned are the exact sum, and it overflows exactly when the sum reaches `2^31`. -/
theorem bv32_add_nonneg (a b : BitVec 32) (ha : a.toNat < 2 ^ 31) (hb : b.toNat < 2 ^ 31) :
    (a + b).toNat = a.toNat + b.toNat ∧
      BitVec.saddOverflow a b = decide (2 ^ 31 ≤ a.toNat + b.toNat) := by
  refine ⟨by rw [BitVec.toNat_add]; exact Nat.mod_eq_of_lt (by omega), ?_⟩
  have hai : a.toInt = (a.toNat : Int) := by
    rw [BitVec.toInt_eq_toNat_cond, ite_eq_left (by omega)]
  have hbi : b.toInt = (b.toNat : Int) := by
    rw [BitVec.toInt_eq_toNat_cond, ite_eq_left (by omega)]
  simp only [BitVec.saddOverflow, hai, hbi]
  by_cases h : 2 ^ 31 ≤ a.toNat + b.toNat
  · rw [decide_eq_true h, decide_eq_true (by omega)]; rfl
  · rw [decide_eq_false h, decide_eq_false (by omega), decide_eq_false (by omega)]; rfl

/-- `(x as i32).overflowing_add(y as i32)` for `x, y < 2^31`, read back as a `u32`: the exact sum, with the overflow flag set exactly when the sum reaches `2^31`. -/
theorem i32_overflowing_add_of_u32 (x y : Std.U32) (hx : x.val < 2 ^ 31) (hy : y.val < 2 ^ 31) :
    let r := IScalar.overflowing_add (UScalar.hcast .I32 x) (UScalar.hcast .I32 y)
    (IScalar.hcast .U32 r.1).val = x.val + y.val ∧ r.2 = decide (2 ^ 31 ≤ x.val + y.val) := by
  intro r
  have h := bv32_add_nonneg x.bv y.bv hx hy
  simp only [r, IScalar.overflowing_add]
  refine ⟨?_, h.2⟩
  show ((x.bv.setWidth 32 + y.bv.setWidth 32).signExtend 32).toNat = x.bv.toNat + y.bv.toNat
  rw [BitVec.signExtend_eq]
  exact h.1

/-- A non-negative `i32` keeps its value as a `u32`. -/
theorem hcast_i32_u32_val (x : Std.I32) (hx : 0 ≤ x.val) :
    ((IScalar.hcast .U32 x).val : Int) = x.val := by
  have := x.hBounds
  rw [IScalar.hcast_val_eq, UScalarTy.U32_numBits_eq, Int.toNat_of_nonneg (Int.emod_nonneg _ (by norm_num))]
  simp only [IScalarTy.I32_numBits_eq] at this
  omega

/-- An `i64` in the `i32` range keeps its value as an `i32`. -/
theorem cast_i64_i32_val (x : Std.I64) (h1 : -2147483648 ≤ x.val) (h2 : x.val < 2147483648) :
    (IScalar.cast .I32 x).val = x.val := by
  rw [IScalar.cast_val_eq, IScalarTy.I32_numBits_eq, IScalarTy.I64_numBits_eq, Int.bmod_def]
  simp only [show min 32 64 = 32 from rfl]
  split <;> omega

/-- An `i128` in the `i32` range keeps its value as an `i32`. -/
theorem cast_i128_i32_val (x : Std.I128) (h1 : -2147483648 ≤ x.val) (h2 : x.val < 2147483648) :
    (IScalar.cast .I32 x).val = x.val := by
  rw [IScalar.cast_val_eq, IScalarTy.I32_numBits_eq, IScalarTy.I128_numBits_eq, Int.bmod_def]
  simp only [show min 32 128 = 32 from rfl]
  split <;> omega

@[step]
theorem core.num.U32.wrapping_sub.spec (x y : Std.U32) :
    CoreModels.core.num.U32.wrapping_sub x y ⦃ r => r.val = (x.val + 2 ^ 32 - y.val) % 2 ^ 32 ⦄ := by
  simp only [CoreModels.core.num.U32.wrapping_sub,
    CoreModels.rust_primitives.arithmetic.wrapping_sub_u32, WP.spec_ok,
    U32.wrapping_sub_val_eq, size_u32]
  have := y.hBounds
  rw [UScalarTy.U32_numBits_eq] at this
  congr 1; omega

/-- `i64::unsigned_abs`: the magnitude. -/
@[step]
theorem core.num.I64.unsigned_abs.spec (x : Std.I64) :
    CoreModels.core.num.I64.unsigned_abs x ⦃ r => r.val = x.val.natAbs ⦄ := by
  simp only [CoreModels.core.num.I64.unsigned_abs, WP.spec_ok, UScalar.val, BitVec.toNat_ofNat]
  have := x.hBounds
  simp only [IScalarTy.I64_numBits_eq, UScalarTy.U64_numBits_eq] at *
  exact Nat.mod_eq_of_lt (by omega)

/-! ## Conversions and comparisons -/

/-- `u64::from(x)` for a `u32` `x`. -/
@[step]
theorem core.U64.Insts.CoreConvertFromU32.from.spec (x : Std.U32) :
    CoreModels.core.U64.Insts.CoreConvertFromU32.from x ⦃ r => r.val = x.val ⦄ := by
  simp only [CoreModels.core.U64.Insts.CoreConvertFromU32.from, WP.spec_ok, cast_u32_u64_val]

/-- `x.min(y)` on `u32`s. -/
@[step]
theorem core.cmp.Ord.min.default_u32.spec (x y : Std.U32) :
    CoreModels.core.cmp.Ord.min.default CoreModels.core.U32.Insts.CoreCmpOrd x y
      ⦃ r => r.val = min x.val y.val ⦄ := by
  simp only [CoreModels.core.cmp.Ord.min.default, CoreModels.core.cmp.min,
    CoreModels.core.U32.Insts.CoreCmpOrd, CoreModels.core.mkUOrd]
  rcases Nat.lt_trichotomy x.val y.val with h | h | h
  · simp [compare_lt_iff_lt.mpr h]; omega
  · simp [h]
  · simp [compare_gt_iff_gt.mpr h]; omega

/-- `x.min(y)` on `u32`s, called as the method of `u32`'s `Ord` instance. -/
@[step]
theorem core.U32.Insts.CoreCmpOrd.min.spec (x y : Std.U32) :
    CoreModels.core.U32.Insts.CoreCmpOrd.min x y ⦃ r => r.val = min x.val y.val ⦄ :=
  core.cmp.Ord.min.default_u32.spec x y

/-- `x.min(y)` on `usize`s, called as the method of `usize`'s `Ord` instance. -/
@[step]
theorem core.Usize.Insts.CoreCmpOrd.min.spec (x y : Std.Usize) :
    CoreModels.core.Usize.Insts.CoreCmpOrd.min x y ⦃ r => r.val = min x.val y.val ⦄ := by
  simp only [CoreModels.core.Usize.Insts.CoreCmpOrd.min, CoreModels.core.cmp.Ord.min.default,
    CoreModels.core.cmp.min, CoreModels.core.Usize.Insts.CoreCmpOrd, CoreModels.core.mkUOrd]
  rcases Nat.lt_trichotomy x.val y.val with h | h | h
  · simp [compare_lt_iff_lt.mpr h]; omega
  · simp [h]
  · simp [compare_gt_iff_gt.mpr h]; omega

/-- `x.cmp(y)` on `u32`s. -/
theorem core.U32.Insts.CoreCmpOrd.cmp.eq (x y : Std.U32) :
    CoreModels.core.U32.Insts.CoreCmpOrd.cmp x y =
      .ok (match compare x.val y.val with
        | .lt => .Less
        | .eq => .Equal
        | .gt => .Greater) := rfl

end Plonky3Lean.Lib
