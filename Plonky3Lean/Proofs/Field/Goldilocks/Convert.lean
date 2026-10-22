import Plonky3Lean.Proofs.Field.Goldilocks.PowersOfTwo

/-!
# Goldilocks: the `QuotientMap` integer conversions

`from_int`, `from_canonical_checked` and `from_canonical_unchecked` from `u64`, `u128`, `i64` and `i128`.

Every input of each integer type is covered.

The `i128` unchecked conversion truncates to an `i64`, which its documented range does not allow for.
-/

open Aeneas Aeneas.Std CoreModels p3_goldilocks Plonky3Lean.Lib
open Plonky3Lean.Spec.Goldilocks

namespace Plonky3Lean.Proofs.Goldilocks


/-- `from_int` on a `u64` stores the integer unchanged. -/
theorem U64.from_int.spec (int : Std.U64) :
    goldilocks.Goldilocks.Insts.P3_fieldIntegersQuotientMapU64.from_int int ⦃ r =>
      r.value = int ⦄ := by
  unfold goldilocks.Goldilocks.Insts.P3_fieldIntegersQuotientMapU64.from_int
  step*

/-- `from_int` on a `u128` stores the canonical residue. -/
theorem U128.from_int.spec (int : Std.U128) :
    goldilocks.Goldilocks.Insts.P3_fieldIntegersQuotientMapU128.from_int int ⦃ r =>
      r.value.val = int.val % 18446744069414584321 ⦄ := by
  unfold goldilocks.Goldilocks.Insts.P3_fieldIntegersQuotientMapU128.from_int
  step*

/-- `from_int` on an `i64` stands for the integer. -/
theorem I64.from_int.spec (int : Std.I64) :
    goldilocks.Goldilocks.Insts.P3_fieldIntegersQuotientMapI64.from_int int ⦃ r =>
      (r.value.val : Goldilocks.Field) = (int.val : Goldilocks.Field) ∧
        r.value.val < 18446744069414584321 ⦄ := by
  unfold goldilocks.Goldilocks.Insts.P3_fieldIntegersQuotientMapI64.from_int
  rw [ORDER_U64.eq]
  have hb := int.hBounds
  simp only [IScalarTy.I64_numBits_eq] at hb
  split
  · rename_i h
    simp only [ge_iff_le, IScalar.le_equiv] at h
    step*
    have hc : i.val = int.val.toNat := by
      rw [i_post, IScalar.hcast_val_eq, UScalarTy.U64_numBits_eq, Int.emod_eq_of_lt (by simpa using h) (by omega)]
    rw [r_post, hc]
    refine ⟨?_, by omega⟩
    have : ((int.val.toNat : ℕ) : ℤ) = int.val := Int.toNat_of_nonneg (by simpa using h)
    rw [← this]; push_cast; rfl
  · rename_i h
    simp only [ge_iff_le, IScalar.le_equiv, not_le, show (0#i64).val = 0 from rfl] at h
    step*
    have hv : (i.val : ℤ) = 18446744069414584321 + int.val := by
      rw [i_post]; push_cast; rw [Int.emod_eq_of_lt (by omega) (by omega)]
    rw [r_post]
    refine ⟨?_, by omega⟩
    have : ((i.val : ℕ) : Goldilocks.Field) = (((i.val : ℕ) : ℤ) : Goldilocks.Field) := by push_cast; rfl
    rw [this, hv]; push_cast; rw [p_eq_zero, zero_add]

/-- `from_int` on a `u128`, read in the field. -/
theorem U128.from_int.field (int : Std.U128) :
    goldilocks.Goldilocks.Insts.P3_fieldIntegersQuotientMapU128.from_int int ⦃ r =>
      (r.value.val : Goldilocks.Field) = int.val ∧ r.value.val < 18446744069414584321 ⦄ :=
  WP.spec_mono (U128.from_int.spec int) (fun r hr => by
    rw [hr]; exact ⟨by rw [ZMod.natCast_mod], Nat.mod_lt _ (by norm_num)⟩)

/-- `from_int` on an `i128` stands for the integer. -/
theorem I128.from_int.spec (int : Std.I128) :
    goldilocks.Goldilocks.Insts.P3_fieldIntegersQuotientMapI128.from_int int ⦃ r =>
      (r.value.val : Goldilocks.Field) = (int.val : Goldilocks.Field) ⦄ := by
  unfold goldilocks.Goldilocks.Insts.P3_fieldIntegersQuotientMapI128.from_int
  have hb := int.hBounds
  simp only [IScalarTy.I128_numBits_eq] at hb
  split
  · rename_i h
    simp only [ge_iff_le, IScalar.le_equiv, show (0#i128).val = 0 from rfl] at h
    simp only [lift, bind_tc_ok]
    apply WP.spec_mono (U128.from_int.field _)
    intro r ⟨hr, _⟩
    rw [hr, IScalar.hcast_val_eq, UScalarTy.U128_numBits_eq,
      Int.emod_eq_of_lt h (by omega)]
    have : ((int.val.toNat : ℕ) : ℤ) = int.val := Int.toNat_of_nonneg h
    rw [← this]; push_cast; rfl
  · rename_i h
    simp only [ge_iff_le, IScalar.le_equiv, not_le, show (0#i128).val = 0 from rfl] at h
    step
    apply WP.spec_bind (U128.from_int.field i)
    intro g ⟨hg, _⟩
    apply WP.spec_mono (neg.field g)
    intro r hr
    rw [hr, hg, i_post]
    have : ((int.val.natAbs : ℕ) : ℤ) = -int.val := by omega
    have h2 : ((int.val.natAbs : ℕ) : Goldilocks.Field) = (((int.val.natAbs : ℕ) : ℤ) : Goldilocks.Field) :=
      (Int.cast_natCast _).symm
    rw [h2, this]; push_cast; ring

/-- `from_canonical_checked` on a `u64` accepts exactly the integers below `p`. -/
theorem U64.from_canonical_checked.spec (int : Std.U64) :
    goldilocks.Goldilocks.Insts.P3_fieldIntegersQuotientMapU64.from_canonical_checked int ⦃ r =>
      r = if int.val < 18446744069414584321 then .Some ⟨int⟩ else .None ⦄ := by
  unfold goldilocks.Goldilocks.Insts.P3_fieldIntegersQuotientMapU64.from_canonical_checked
  rw [ORDER_U64.eq]
  split <;> rename_i h <;> simp only [UScalar.lt_equiv, show (18446744069414584321#u64).val = 18446744069414584321 from rfl] at h
  · step*; rw [if_pos h, ← g_post]
  · simp [h]

/-- `from_canonical_checked` on a `u128` accepts exactly the integers below `p`. -/
theorem U128.from_canonical_checked.spec (int : Std.U128) :
    goldilocks.Goldilocks.Insts.P3_fieldIntegersQuotientMapU128.from_canonical_checked int ⦃ r =>
      r = if int.val < 18446744069414584321 then .Some ⟨UScalar.cast .U64 int⟩ else .None ⦄ := by
  unfold goldilocks.Goldilocks.Insts.P3_fieldIntegersQuotientMapU128.from_canonical_checked
  rw [ORDER_U64.eq]
  have hc : (UScalar.cast .U128 18446744069414584321#u64).val = 18446744069414584321 := by
    rw [cast_u64_u128_val]; rfl
  simp only [lift, bind_tc_ok]
  split <;> rename_i h <;> simp only [UScalar.lt_equiv, hc] at h
  · step*; simp [h, ← g_post]
  · simp [h]

/-- `from_canonical_unchecked` on a `u128` below `2^64` stands for the integer. -/
theorem U128.from_canonical_unchecked.spec (int : Std.U128) (h : int.val < 2 ^ 64) :
    goldilocks.Goldilocks.Insts.P3_fieldIntegersQuotientMapU128.from_canonical_unchecked int ⦃ r =>
      (r.value.val : Goldilocks.Field) = int.val ⦄ := by
  unfold goldilocks.Goldilocks.Insts.P3_fieldIntegersQuotientMapU128.from_canonical_unchecked
  step*
  rw [r_post, cast_u128_u64_val, Nat.mod_eq_of_lt h]

/-- `from_canonical_checked` on an `i64` accepts exactly `[-(p - 1)/2, (p - 1)/2]`. -/
theorem I64.from_canonical_checked.spec (int : Std.I64) :
    goldilocks.Goldilocks.Insts.P3_fieldIntegersQuotientMapI64.from_canonical_checked int ⦃ r =>
      match r with
      | .Some x => -9223372034707292160 ≤ int.val ∧ int.val ≤ 9223372034707292160 ∧
          (x.value.val : Goldilocks.Field) = (int.val : Goldilocks.Field)
      | .None => ¬ (-9223372034707292160 ≤ int.val ∧ int.val ≤ 9223372034707292160) ⦄ := by
  unfold goldilocks.Goldilocks.Insts.P3_fieldIntegersQuotientMapI64.from_canonical_checked
  rw [ORDER_U64.eq]
  have hb := int.hBounds
  simp only [IScalarTy.I64_numBits_eq] at hb
  have e0 : (0#i64).val = 0 := rfl
  have e1 : (9223372034707292160#i64).val = 9223372034707292160 := rfl
  have e2 : ((-9223372034707292160)#i64).val = -9223372034707292160 := rfl
  split
  · rename_i h
    simp only [IScalar.le_equiv, e0, e1] at h
    simp only [lift, bind_tc_ok]
    step*
    refine ⟨by omega, h.2, ?_⟩
    rw [g_post, IScalar.hcast_val_eq, UScalarTy.U64_numBits_eq, Int.emod_eq_of_lt h.1 (by omega)]
    have : ((int.val.toNat : ℕ) : ℤ) = int.val := Int.toNat_of_nonneg h.1
    rw [← this]; push_cast; rfl
  · rename_i h
    simp only [IScalar.le_equiv, e0, e1, not_and, not_le] at h
    split
    · rename_i h'
      simp only [IScalar.le_equiv, IScalar.lt_equiv, e0, e2] at h'
      step*
      refine ⟨h'.1, by omega, ?_⟩
      have hv : (i.val : ℤ) = 18446744069414584321 + int.val := by
        rw [i_post]; push_cast; rw [Int.emod_eq_of_lt (by omega) (by omega)]
      have : ((i.val : ℕ) : Goldilocks.Field) = (((i.val : ℕ) : ℤ) : Goldilocks.Field) :=
        (Int.cast_natCast _).symm
      rw [g_post, this, hv]; push_cast; rw [p_eq_zero, zero_add]
    · rename_i h'
      simp only [IScalar.le_equiv, IScalar.lt_equiv, e0, e2, not_and, not_lt] at h'
      simp only [WP.spec_ok]
      omega

/-- `from_canonical_checked` on an `i128` accepts exactly `[-(p - 1)/2, (p - 1)/2]`. -/
theorem I128.from_canonical_checked.spec (int : Std.I128) :
    goldilocks.Goldilocks.Insts.P3_fieldIntegersQuotientMapI128.from_canonical_checked int ⦃ r =>
      match r with
      | .Some x => -9223372034707292160 ≤ int.val ∧ int.val ≤ 9223372034707292160 ∧
          (x.value.val : Goldilocks.Field) = (int.val : Goldilocks.Field)
      | .None => ¬ (-9223372034707292160 ≤ int.val ∧ int.val ≤ 9223372034707292160) ⦄ := by
  unfold goldilocks.Goldilocks.Insts.P3_fieldIntegersQuotientMapI128.from_canonical_checked
  unfold CoreModels.core.I64.Insts.CoreConvertTryFromI128TryFromIntError.try_from
  have hb := int.hBounds
  simp only [IScalarTy.I128_numBits_eq] at hb
  have hmax : (IScalar.cast .I128 CoreModels.core.num.I64.MAX).val = 9223372036854775807 := by
    rw [IScalar.cast_val_eq]; rfl
  have hmin : (IScalar.cast .I128 CoreModels.core.num.I64.MIN).val = -9223372036854775808 := by
    rw [IScalar.cast_val_eq]; rfl
  simp only [lift, bind_tc_ok]
  split
  · rename_i h
    simp only [IScalar.lt_equiv, hmax] at h
    simp only [bind_tc_ok, WP.spec_ok]
    omega
  · rename_i h
    simp only [IScalar.lt_equiv, hmax, not_lt] at h
    split
    · rename_i h'
      simp only [IScalar.lt_equiv, hmin] at h'
      simp only [bind_tc_ok, WP.spec_ok]
      omega
    · rename_i h'
      simp only [IScalar.lt_equiv, hmin, not_lt] at h'
      simp only [bind_tc_ok]
      have hc : (IScalar.cast .I64 int).val = int.val := by
        rw [IScalar.cast_val_eq, IScalarTy.I64_numBits_eq, IScalarTy.I128_numBits_eq,
          show min 64 128 = 63 + 1 from rfl]
        exact Aeneas.Arith.Int.bmod_pow2_eq_of_inBounds 63 _ (by omega) (by omega)
      apply WP.spec_mono (I64.from_canonical_checked.spec _)
      intro r hr
      rw [hc] at hr
      exact hr

/-- `from_canonical_unchecked` on an `i64` is `from_int`, correct on every input. -/
theorem I64.from_canonical_unchecked.spec (int : Std.I64) :
    goldilocks.Goldilocks.Insts.P3_fieldIntegersQuotientMapI64.from_canonical_unchecked int ⦃ r =>
      (r.value.val : Goldilocks.Field) = (int.val : Goldilocks.Field) ⦄ := by
  unfold goldilocks.Goldilocks.Insts.P3_fieldIntegersQuotientMapI64.from_canonical_unchecked
  exact WP.spec_mono (I64.from_int.spec int) (fun r hr => hr.1)

/-- `from_canonical_unchecked` on an `i128` reads the input truncated to an `i64`. -/
theorem I128.from_canonical_unchecked.truncates (int : Std.I128) :
    goldilocks.Goldilocks.Insts.P3_fieldIntegersQuotientMapI128.from_canonical_unchecked int ⦃ r =>
      (r.value.val : Goldilocks.Field) = (Int.bmod int.val (2 ^ 64) : Goldilocks.Field) ⦄ := by
  unfold goldilocks.Goldilocks.Insts.P3_fieldIntegersQuotientMapI128.from_canonical_unchecked
  simp only [lift, bind_tc_ok]
  apply WP.spec_mono (I64.from_canonical_unchecked.spec _)
  intro r hr
  rw [hr, IScalar.cast_val_eq, IScalarTy.I64_numBits_eq, IScalarTy.I128_numBits_eq]
  rfl

/-- On the inputs an `i64` holds, `from_canonical_unchecked` on an `i128` stands for the integer. -/
theorem I128.from_canonical_unchecked.spec (int : Std.I128)
    (h0 : -2 ^ 63 ≤ int.val) (h1 : int.val < 2 ^ 63) :
    goldilocks.Goldilocks.Insts.P3_fieldIntegersQuotientMapI128.from_canonical_unchecked int ⦃ r =>
      (r.value.val : Goldilocks.Field) = (int.val : Goldilocks.Field) ⦄ := by
  apply WP.spec_mono (I128.from_canonical_unchecked.truncates int)
  intro r hr
  rw [hr, show (2 : ℕ) ^ 64 = 2 ^ (63 + 1) from rfl,
    Aeneas.Arith.Int.bmod_pow2_eq_of_inBounds 63 _ h0 h1]

/-- FINDING: the documented safe range of `from_canonical_unchecked` on an `i128` is wrong.

The doc comment allows `[1 + 2^32 - 2^64, 2^64 - 1]`.

At `2^64 - 1`, inside that range, the result stands for `-1`, not for `2^64 - 1`. -/
theorem I128.from_canonical_unchecked.doc_range_counterexample :
    goldilocks.Goldilocks.Insts.P3_fieldIntegersQuotientMapI128.from_canonical_unchecked
      18446744073709551615#i128 ⦃ r =>
      (r.value.val : Goldilocks.Field) = -1 ∧
        (r.value.val : Goldilocks.Field) ≠ ((18446744073709551615 : ℤ) : Goldilocks.Field) ⦄ := by
  apply WP.spec_mono (I128.from_canonical_unchecked.truncates _)
  intro r hr
  rw [hr]
  have hv : (18446744073709551615#i128).val = 18446744073709551615 := rfl
  rw [hv, show Int.bmod 18446744073709551615 (2 ^ 64) = -1 by decide]
  refine ⟨by push_cast; rfl, by push_cast; decide⟩

end Plonky3Lean.Proofs.Goldilocks
