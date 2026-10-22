import Plonky3Lean.Proofs.Field.Mersenne31.Basic

/-!
# Mersenne31: integer conversions (`QuotientMap`)
-/

open Aeneas Aeneas.Std CoreModels
open p3_mersenne_31
open Plonky3Lean.Spec.Mersenne31 Plonky3Lean.Lib

namespace Plonky3Lean.Proofs.Mersenne31

/-! ## Unsigned -/

/-- Clearing the top bit of a 32-bit value leaves its value modulo `2^31`. -/
theorem clear_msb_toNat (a : BitVec 32) :
    (a ^^^ (a &&& 0x80000000#32)).toNat = a.toNat % 2 ^ 31 := by
  have : a ^^^ (a &&& 0x80000000#32) = a &&& 0x7fffffff#32 := by bv_decide
  rw [this, BitVec.toNat_and, show (0x7fffffff#32).toNat = 2 ^ 31 - 1 from rfl,
    Nat.and_two_pow_sub_one_eq_mod]

/-- The top bit of a 32-bit value, shifted down, is its quotient by `2^31`. -/
theorem msb_toNat (a : BitVec 32) : ((a &&& 0x80000000#32) >>> 31).toNat = a.toNat / 2 ^ 31 := by
  have : (a &&& 0x80000000#32) >>> 31 = a >>> 31 := by bv_decide
  rw [this, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

@[step]
theorem from_canonical_unchecked_u32.spec (x : Std.U32) (hx : x.val < 2147483647) :
    mersenne_31.Mersenne31.Insts.P3_fieldIntegersQuotientMapU32.from_canonical_unchecked x
      ⦃ r => r.value = x ⦄ := by
  unfold mersenne_31.Mersenne31.Insts.P3_fieldIntegersQuotientMapU32.from_canonical_unchecked
  rw [ORDER_U32.eq]
  step*

theorem from_int_u8.spec (x : Std.U8) :
    mersenne_31.Mersenne31.Insts.P3_fieldIntegersQuotientMapU8.from_int x
      ⦃ r => r.value.val = x.val ⦄ := by
  unfold mersenne_31.Mersenne31.Insts.P3_fieldIntegersQuotientMapU8.from_int
  step*

theorem from_int_u16.spec (x : Std.U16) :
    mersenne_31.Mersenne31.Insts.P3_fieldIntegersQuotientMapU16.from_int x
      ⦃ r => r.value.val = x.val ⦄ := by
  unfold mersenne_31.Mersenne31.Insts.P3_fieldIntegersQuotientMapU16.from_int
  step*

theorem from_int_u32.spec (x : Std.U32) :
    mersenne_31.Mersenne31.Insts.P3_fieldIntegersQuotientMapU32.from_int x
      ⦃ r => Valid r ∧ r.value.val % 2147483647 = x.val % 2147483647 ⦄ := by
  unfold mersenne_31.Mersenne31.Insts.P3_fieldIntegersQuotientMapU32.from_int
  step*
  all_goals
    have hi : i = 2147483648#u32 := UScalar.eq_of_val_eq (by
      rw [i_post1, one_shl_u32 31 (by norm_num)]; rfl)
    have h1 : i1.val = x.val % 2 ^ 31 := by
      have e : i1.bv = x.bv ^^^ (x.bv &&& i.bv) :=
        i1_post2.trans (congrArg (x.bv ^^^ ·) msb_post2)
      rw [hi] at e
      exact (congrArg BitVec.toNat e).trans (clear_msb_toNat x.bv)
    have h2 : msb_reduced.val = x.val / 2 ^ 31 := by
      have e := msb_reduced_post2
      simp only [msb_post2, hi] at e
      exact (congrArg BitVec.toNat e).trans (msb_toNat x.bv)
    have hx := u32_lt x
  · omega
  · omega
  · refine WP.spec_mono (add.spec m m1 (by simp only [Valid, m_post]; omega)
      (by simp only [Valid, m1_post]; omega)) ?_
    rintro r ⟨hv, hr⟩
    refine ⟨hv, ?_⟩
    rw [hr, m_post, m1_post, h1, h2]
    split_ifs <;> omega

@[step]
theorem from_int_u64.spec (x : Std.U64) :
    mersenne_31.Mersenne31.Insts.P3_fieldIntegersQuotientMapU64.from_int x
      ⦃ r => r.value.val = x.val % 2147483647 ⦄ := by
  unfold mersenne_31.Mersenne31.Insts.P3_fieldIntegersQuotientMapU64.from_int
  rw [ORDER_U32.eq]
  step*

@[step]
theorem from_int_u128.spec (x : Std.U128) :
    mersenne_31.Mersenne31.Insts.P3_fieldIntegersQuotientMapU128.from_int x
      ⦃ r => r.value.val = x.val % 2147483647 ⦄ := by
  unfold mersenne_31.Mersenne31.Insts.P3_fieldIntegersQuotientMapU128.from_int
  rw [ORDER_U32.eq]
  step*

/-! ## Signed -/

theorem from_int_i32.spec (x : Std.I32) :
    mersenne_31.Mersenne31.Insts.P3_fieldIntegersQuotientMapI32.from_int x
      ⦃ r => Valid r ∧ (r.value.val : Int) % 2147483647 = x.val % 2147483647 ⦄ := by
  unfold mersenne_31.Mersenne31.Insts.P3_fieldIntegersQuotientMapI32.from_int
  rw [ORDER_U32.eq, NEG_ONE.eq]
  have hx := x.hBounds
  simp only [IScalarTy.I32_numBits_eq] at hx
  step*
  · rw [i_post, IScalar.hcast_val_eq]; scalar_tac
  · simp only [Valid, r_post, i_post, IScalar.hcast_val_eq, UScalarTy.U32_numBits_eq]
    have : 0 ≤ x.val := by scalar_tac
    refine ⟨by omega, ?_⟩
    rw [Int.toNat_of_nonneg (by omega)]
    omega
  all_goals
    have hi : i.val = -2147483648 := by
      rw [i_post1, I32.size_def, I32.numBits_def]; decide
    have hlt : x.val < 0 := by scalar_tac
  · have hgt : i.val < x.val := by scalar_tac
    have : (i2.val : Int) = 2147483647 + x.val := by rw [i2_post]; omega
    simp only [Valid, r_post]
    omega
  · have hle : x.val ≤ i.val := by scalar_tac
    simp only [Valid]
    have : x.val = -2147483648 := by omega
    rw [this]
    decide

theorem from_int_i64.spec (x : Std.I64) :
    mersenne_31.Mersenne31.Insts.P3_fieldIntegersQuotientMapI64.from_int x
      ⦃ r => Valid r ∧ (r.value.val : Int) % 2147483647 = x.val % 2147483647 ⦄ := by
  unfold mersenne_31.Mersenne31.Insts.P3_fieldIntegersQuotientMapI64.from_int
  step*
  · have : 0 ≤ x.val := by scalar_tac
    simp only [Valid, r_post, i_post, IScalar.hcast_val_eq, UScalarTy.U64_numBits_eq]
    have hx := x.hBounds
    simp only [IScalarTy.I64_numBits_eq] at hx
    rw [Int.emod_eq_of_lt this (by omega)]
    omega
  · have : x.val < 0 := by scalar_tac
    have ha : ((x.val.natAbs : ℕ) : Int) = -x.val := by omega
    refine WP.spec_mono (neg.spec m (by simp only [Valid, m_post]; omega)) ?_
    rintro r ⟨hv, hr⟩
    refine ⟨hv, ?_⟩
    rw [hr, m_post, i_post]
    omega

theorem from_int_i128.spec (x : Std.I128) :
    mersenne_31.Mersenne31.Insts.P3_fieldIntegersQuotientMapI128.from_int x
      ⦃ r => Valid r ∧ (r.value.val : Int) % 2147483647 = x.val % 2147483647 ⦄ := by
  unfold mersenne_31.Mersenne31.Insts.P3_fieldIntegersQuotientMapI128.from_int
  step*
  · have : 0 ≤ x.val := by scalar_tac
    simp only [Valid, r_post, i_post, IScalar.hcast_val_eq, UScalarTy.U128_numBits_eq]
    have hx := x.hBounds
    simp only [IScalarTy.I128_numBits_eq] at hx
    rw [Int.emod_eq_of_lt this (by omega)]
    omega
  · have : x.val < 0 := by scalar_tac
    have ha : ((x.val.natAbs : ℕ) : Int) = -x.val := by omega
    refine WP.spec_mono (neg.spec m (by simp only [Valid, m_post]; omega)) ?_
    rintro r ⟨hv, hr⟩
    refine ⟨hv, ?_⟩
    rw [hr, m_post, i_post]
    omega

/-! ## Small signed widths, and the unchecked conversions -/

@[step]
theorem from_canonical_unchecked_i32.spec (x : Std.I32) (hx : -2147483648 < x.val) :
    mersenne_31.Mersenne31.Insts.P3_fieldIntegersQuotientMapI32.from_canonical_unchecked x
      ⦃ r => Valid r ∧ (r.value.val : Int) % 2147483647 = x.val % 2147483647 ⦄ := by
  unfold mersenne_31.Mersenne31.Insts.P3_fieldIntegersQuotientMapI32.from_canonical_unchecked
  rw [ORDER_U32.eq]
  have hb := x.hBounds
  simp only [IScalarTy.I32_numBits_eq] at hb
  step*
  · have : 0 ≤ x.val := by scalar_tac
    have := hcast_i32_u32_val x this
    rw [i_post]; omega
  · have : 0 ≤ x.val := by scalar_tac
    have := hcast_i32_u32_val x this
    simp only [Valid, r_post, i_post]; omega
  · have : x.val < 0 := by scalar_tac
    simp only [Valid, r_post]; omega

theorem from_int_i8.spec (x : Std.I8) :
    mersenne_31.Mersenne31.Insts.P3_fieldIntegersQuotientMapI8.from_int x
      ⦃ r => Valid r ∧ (r.value.val : Int) % 2147483647 = x.val % 2147483647 ⦄ := by
  unfold mersenne_31.Mersenne31.Insts.P3_fieldIntegersQuotientMapI8.from_int
  step*

theorem from_int_i16.spec (x : Std.I16) :
    mersenne_31.Mersenne31.Insts.P3_fieldIntegersQuotientMapI16.from_int x
      ⦃ r => Valid r ∧ (r.value.val : Int) % 2147483647 = x.val % 2147483647 ⦄ := by
  unfold mersenne_31.Mersenne31.Insts.P3_fieldIntegersQuotientMapI16.from_int
  step*

theorem from_canonical_unchecked_u64.spec (x : Std.U64) (hx : x.val < 2147483647) :
    mersenne_31.Mersenne31.Insts.P3_fieldIntegersQuotientMapU64.from_canonical_unchecked x
      ⦃ r => r.value.val = x.val ⦄ := by
  unfold mersenne_31.Mersenne31.Insts.P3_fieldIntegersQuotientMapU64.from_canonical_unchecked
  step*

theorem from_canonical_unchecked_i64.spec (x : Std.I64) (hx : -2147483648 < x.val)
    (hx' : x.val < 2147483648) :
    mersenne_31.Mersenne31.Insts.P3_fieldIntegersQuotientMapI64.from_canonical_unchecked x
      ⦃ r => Valid r ∧ (r.value.val : Int) % 2147483647 = x.val % 2147483647 ⦄ := by
  unfold mersenne_31.Mersenne31.Insts.P3_fieldIntegersQuotientMapI64.from_canonical_unchecked
  have hi := cast_i64_i32_val x (by omega) hx'
  step*

/-- The `u32` conversion that the doc comment allows on `[0, 2^31 - 1]` panics, in a debug build, at `2^31 - 1`. -/
theorem from_canonical_unchecked_u32.panics_at_p :
    mersenne_31.Mersenne31.Insts.P3_fieldIntegersQuotientMapU32.from_canonical_unchecked
      2147483647#u32 = .fail .panic := by
  unfold mersenne_31.Mersenne31.Insts.P3_fieldIntegersQuotientMapU32.from_canonical_unchecked
  rw [ORDER_U32.eq]
  rfl

/-! ## The checked conversions -/

theorem from_canonical_checked_u32.spec (x : Std.U32) :
    mersenne_31.Mersenne31.Insts.P3_fieldIntegersQuotientMapU32.from_canonical_checked x
      ⦃ r => r = if x.val < 2147483647 then .Some { value := x } else .None ⦄ := by
  unfold mersenne_31.Mersenne31.Insts.P3_fieldIntegersQuotientMapU32.from_canonical_checked
  rw [ORDER_U32.eq]
  unfold CoreModels.core.bool.Bool.then
  simp only [bind_tc_ok]
  by_cases h : x.val < 2147483647
  · have h' : x < 2147483647#u32 := by scalar_tac
    rw [if_pos (by simpa using h'), if_pos h]
    unfold mersenne_31.QuotientMapMersenne31U32.from_canonical_checked.closure.Insts.CoreOpsFunctionFnOnceTupleMersenne31.call_once
    step*
    rw [← x_post]
  · have h' : ¬ x < 2147483647#u32 := by scalar_tac
    rw [if_neg (by simpa using h'), if_neg h]
    rfl

theorem from_canonical_checked_u64.spec (x : Std.U64) :
    mersenne_31.Mersenne31.Insts.P3_fieldIntegersQuotientMapU64.from_canonical_checked x
      ⦃ r => match r with
        | .Some y => x.val < 2147483647 ∧ y.value.val = x.val
        | .None => 2147483647 ≤ x.val ⦄ := by
  unfold mersenne_31.Mersenne31.Insts.P3_fieldIntegersQuotientMapU64.from_canonical_checked
  rw [ORDER_U32.eq]
  step*

@[step]
theorem from_canonical_checked_i32.spec (x : Std.I32) :
    mersenne_31.Mersenne31.Insts.P3_fieldIntegersQuotientMapI32.from_canonical_checked x
      ⦃ r => match r with
        | .Some y => -1073741824 < x.val ∧ x.val < 1073741824 ∧ Valid y ∧
            (y.value.val : Int) % 2147483647 = x.val % 2147483647
        | .None => ¬ (-1073741824 < x.val ∧ x.val < 1073741824) ⦄ := by
  unfold mersenne_31.Mersenne31.Insts.P3_fieldIntegersQuotientMapI32.from_canonical_checked
  rw [ORDER_U32.eq]
  have hb := x.hBounds
  simp only [IScalarTy.I32_numBits_eq] at hb
  step*
  · have h0 : 0 ≤ x.val := by scalar_tac
    have := hcast_i32_u32_val x h0
    have : x.val < 1073741824 := by scalar_tac
    rw [i_post]; omega
  · have h0 : 0 ≤ x.val := by scalar_tac
    have := hcast_i32_u32_val x h0
    have : x.val < 1073741824 := by scalar_tac
    simp only [Valid, m_post, i_post]; omega
  · have : x.val < 0 := by scalar_tac
    have : -1073741823 ≤ x.val := by scalar_tac
    simp only [Valid, m_post]; omega

theorem from_canonical_checked_u128.spec (x : Std.U128) :
    mersenne_31.Mersenne31.Insts.P3_fieldIntegersQuotientMapU128.from_canonical_checked x
      ⦃ r => match r with
        | .Some y => x.val < 2147483647 ∧ y.value.val = x.val
        | .None => 2147483647 ≤ x.val ⦄ := by
  unfold mersenne_31.Mersenne31.Insts.P3_fieldIntegersQuotientMapU128.from_canonical_checked
  rw [ORDER_U32.eq]
  step*

theorem from_canonical_checked_i64.spec (x : Std.I64) :
    mersenne_31.Mersenne31.Insts.P3_fieldIntegersQuotientMapI64.from_canonical_checked x
      ⦃ r => match r with
        | .Some y => -1073741824 < x.val ∧ x.val < 1073741824 ∧ Valid y ∧
            (y.value.val : Int) % 2147483647 = x.val % 2147483647
        | .None => ¬ (-1073741824 < x.val ∧ x.val < 1073741824) ⦄ := by
  unfold mersenne_31.Mersenne31.Insts.P3_fieldIntegersQuotientMapI64.from_canonical_checked
  unfold CoreModels.core.I32.Insts.CoreConvertTryFromI64TryFromIntError.try_from
  have hmax : IScalar.cast .I64 core.num.I32.MAX = 2147483647#i64 := by rfl
  have hmin : IScalar.cast .I64 core.num.I32.MIN = (-2147483648)#i64 := by rfl
  simp only [lift, bind_tc_ok, hmax, hmin]
  simp only [CoreModels.core.result.Result.ok, CoreModels.core.option.Option.map,
    CoreModels.core.option.Option.Insts.CoreOpsTry_traitTry.branch,
    CoreModels.core.option.Option.Insts.CoreOpsTry_traitTryTOptionInfallible.branch,
    CoreModels.core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual,
    P.Insts.CoreOpsFunctionFnOnceTupleI32OptionMersenne31.call_once]
  by_cases h1 : x > 2147483647#i64
  · have : 2147483647 < x.val := by scalar_tac
    simp only [h1, if_true, bind_tc_ok, WP.spec_ok]
    omega
  · simp only [h1, if_false]
    by_cases h2 : x < (-2147483648)#i64
    · have : x.val < -2147483648 := by scalar_tac
      simp only [h2, if_true, bind_tc_ok, WP.spec_ok]
      omega
    · have : -2147483648 ≤ x.val := by scalar_tac
      have : x.val ≤ 2147483647 := by scalar_tac
      have hc := cast_i64_i32_val x (by omega) (by omega)
      simp only [h2, if_false, bind_tc_ok]
      step*
      rw [hc] at val_post
      exact val_post

theorem from_canonical_checked_i128.spec (x : Std.I128) :
    mersenne_31.Mersenne31.Insts.P3_fieldIntegersQuotientMapI128.from_canonical_checked x
      ⦃ r => match r with
        | .Some y => -1073741824 < x.val ∧ x.val < 1073741824 ∧ Valid y ∧
            (y.value.val : Int) % 2147483647 = x.val % 2147483647
        | .None => ¬ (-1073741824 < x.val ∧ x.val < 1073741824) ⦄ := by
  unfold mersenne_31.Mersenne31.Insts.P3_fieldIntegersQuotientMapI128.from_canonical_checked
  unfold CoreModels.core.I32.Insts.CoreConvertTryFromI128TryFromIntError.try_from
  have hmax : IScalar.cast .I128 core.num.I32.MAX = 2147483647#i128 := by rfl
  have hmin : IScalar.cast .I128 core.num.I32.MIN = (-2147483648)#i128 := by rfl
  simp only [lift, bind_tc_ok, hmax, hmin]
  simp only [CoreModels.core.result.Result.ok, CoreModels.core.option.Option.map,
    CoreModels.core.option.Option.Insts.CoreOpsTry_traitTry.branch,
    CoreModels.core.option.Option.Insts.CoreOpsTry_traitTryTOptionInfallible.branch,
    CoreModels.core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual,
    P.Insts.CoreOpsFunctionFnOnceTupleI32OptionMersenne31.call_once]
  by_cases h1 : x > 2147483647#i128
  · have : 2147483647 < x.val := by scalar_tac
    simp only [h1, if_true, bind_tc_ok, WP.spec_ok]
    omega
  · simp only [h1, if_false]
    by_cases h2 : x < (-2147483648)#i128
    · have : x.val < -2147483648 := by scalar_tac
      simp only [h2, if_true, bind_tc_ok, WP.spec_ok]
      omega
    · have : -2147483648 ≤ x.val := by scalar_tac
      have : x.val ≤ 2147483647 := by scalar_tac
      have hc := cast_i128_i32_val x (by omega) (by omega)
      simp only [h2, if_false, bind_tc_ok]
      step*
      rw [hc] at val_post
      exact val_post

attribute [step] add.spec sub.spec neg.spec from_u62.spec mul.spec from_int_u32.spec
  from_int_i32.spec from_int_i64.spec from_int_i128.spec

end Plonky3Lean.Proofs.Mersenne31
