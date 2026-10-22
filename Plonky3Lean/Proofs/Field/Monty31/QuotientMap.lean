module

public import Plonky3Lean.Proofs.Field.Monty31.Element

@[expose] public section

/-!
# Monty31: integers into the field, for any valid parameters

`from_int` maps any integer `x` to the element `x mod p`, stored canonically.

`from_canonical_checked` does the same on the documented range and returns `None` outside it.

- An unsigned input must lie in `[0, p - 1]`.
- A signed input must lie in `[-(p - 1)/2, (p - 1)/2]`.
-/

open Aeneas Aeneas.Std CoreModels
open p3_monty_31
open Plonky3Lean.Spec.Monty31 Plonky3Lean.Lib

namespace Plonky3Lean.Proofs.Monty31

variable {FP : Type} {inst : data_traits.FieldParameters FP} {p mu : Std.U32}

open monty_31.MontyField31.Insts in
theorem from_int_i32.spec (hv : FieldValid inst p mu) (x : Std.I32) :
    P3_fieldIntegersQuotientMapI32.from_int inst x ⦃ r => r.value.val < p.val ∧
      (r.value.val : ℤ) % p.val = x.val * 2 ^ 32 % p.val ⦄ := by
  unfold P3_fieldIntegersQuotientMapI32.from_int
  have hm := hv.monty
  step*

open monty_31.MontyField31.Insts in
theorem from_int_u64.spec (hv : FieldValid inst p mu) (x : Std.U64) :
    P3_fieldIntegersQuotientMapU64.from_int inst x ⦃ r =>
      r.value.val = x.val * 2 ^ 32 % p.val ⦄ := by
  unfold P3_fieldIntegersQuotientMapU64.from_int
  have hm := hv.monty
  step*

open monty_31.MontyField31.Insts in
theorem from_int_i64.spec (hv : FieldValid inst p mu) (x : Std.I64) :
    P3_fieldIntegersQuotientMapI64.from_int inst x ⦃ r => r.value.val < p.val ∧
      (r.value.val : ℤ) % p.val = x.val * 2 ^ 32 % p.val ⦄ := by
  unfold P3_fieldIntegersQuotientMapI64.from_int
  have hm := hv.monty
  step*

open monty_31.MontyField31.Insts in
theorem from_int_u128.spec (hv : FieldValid inst p mu) (x : Std.U128) :
    P3_fieldIntegersQuotientMapU128.from_int inst x ⦃ r =>
      r.value.val = x.val % p.val * 2 ^ 32 % p.val ⦄ := by
  unfold P3_fieldIntegersQuotientMapU128.from_int
  have hm := hv.monty
  dsimp only
  rw [hm.prime]
  have hp0 : 0 < p.val := by have := hm.odd; omega
  step*

open monty_31.MontyField31.Insts in
theorem from_int_i128.spec (hv : FieldValid inst p mu) (x : Std.I128) :
    P3_fieldIntegersQuotientMapI128.from_int inst x ⦃ r => r.value.val < p.val ∧
      (r.value.val : ℤ) % p.val = x.val * 2 ^ 32 % p.val ⦄ := by
  unfold P3_fieldIntegersQuotientMapI128.from_int
  have hm := hv.monty
  dsimp only
  rw [hm.prime]
  have hp0 : 0 < p.val := by have := hm.odd; omega
  have hp := hm.lt
  have hc : (UScalar.hcast .I128 p).val = p.val := by
    rw [UScalar.hcast_val_eq, IScalarTy.I128_numBits_eq]
    exact Int.bmod_eq_of_le (by omega) (by omega)
  step*
  rename r.value = v => hrv
  rename_i r1 _ _
  have hr1 := r_post
  have hp' : (0 : ℤ) < p.val := by omega
  rw [hc] at hr1
  have hlt := Int.tmod_lt_of_pos x.val hp'
  have hgt := Int.lt_tmod_of_pos x.val hp'
  have h32 : (IScalar.cast .I32 r1).val = r1.val := by
    rw [IScalar.cast_val_eq, IScalarTy.I32_numBits_eq, IScalarTy.I128_numBits_eq,
      show Min.min 32 128 = 32 from rfl]
    exact Int.bmod_eq_of_le (by push_cast; omega) (by push_cast; omega)
  rw [hrv]
  refine ⟨v_post, ?_⟩
  rw [v_post1, h32, hr1, Int.mul_emod, Int.tmod_def]
  simp [Int.sub_emod, Int.mul_emod_right, ← Int.mul_emod]

open monty_31.MontyField31.Insts in
theorem from_canonical_checked_u32.spec (hv : FieldValid inst p mu) (x : Std.U32) :
    P3_fieldIntegersQuotientMapU32.from_canonical_checked inst x ⦃ r =>
      (x.val < p.val → ∃ e, r = some e ∧ e.value.val = x.val * 2 ^ 32 % p.val) ∧
      (p.val ≤ x.val → r = none) ⦄ := by
  unfold P3_fieldIntegersQuotientMapU32.from_canonical_checked
  have hm := hv.monty
  dsimp only
  rw [hm.prime]
  step*

open monty_31.MontyField31.Insts in
theorem from_canonical_checked_i32.spec (hv : FieldValid inst p mu) (x : Std.I32) :
    P3_fieldIntegersQuotientMapI32.from_canonical_checked inst x ⦃ r =>
      (-((p.val - 1) / 2 : ℕ) ≤ x.val → x.val ≤ ((p.val - 1) / 2 : ℕ) →
        ∃ e, r = some e ∧ e.value.val < p.val ∧
          (e.value.val : ℤ) % p.val = x.val * 2 ^ 32 % p.val) ∧
      ((x.val < -((p.val - 1) / 2 : ℕ) ∨ ((p.val - 1) / 2 : ℕ) < x.val) → r = none) ⦄ := by
  unfold P3_fieldIntegersQuotientMapI32.from_canonical_checked
  have hm := hv.monty
  dsimp only
  rw [hm.prime]
  have hp := hm.lt
  have hodd := hm.odd
  have hhalf : ∀ h : Std.U32, h.val = p.val >>> 1 →
      (UScalar.hcast .I32 h).val = (((p.val - 1) / 2 : ℕ) : ℤ) := by
    intro h hh
    rw [UScalar.hcast_val_eq, IScalarTy.I32_numBits_eq, hh, Nat.shiftRight_eq_div_pow, pow_one]
    rw [Int.bmod_eq_of_le (by push_cast; omega) (by push_cast; omega)]
    push_cast; omega
  step*
  all_goals have hb := hhalf half half_post
  all_goals simp only [IScalar.le_equiv, ge_iff_le] at *
  · refine ⟨fun _ _ => ⟨e, rfl, ‹e.value = v› ▸ ‹v.val < p.val›, ‹e.value = v› ▸ v_post1⟩, fun h => ?_⟩
    omega

open monty_31.MontyField31.Insts in
theorem from_canonical_checked_u64.spec (hv : FieldValid inst p mu) (x : Std.U64) :
    P3_fieldIntegersQuotientMapU64.from_canonical_checked inst x ⦃ r =>
      (x.val < p.val → ∃ e, r = some e ∧ e.value.val = x.val * 2 ^ 32 % p.val) ∧
      (p.val ≤ x.val → r = none) ⦄ := by
  unfold P3_fieldIntegersQuotientMapU64.from_canonical_checked
  have hm := hv.monty
  dsimp only
  rw [hm.prime]
  have hp := hm.lt
  step*

open monty_31.MontyField31.Insts in
theorem from_canonical_checked_u128.spec (hv : FieldValid inst p mu) (x : Std.U128) :
    P3_fieldIntegersQuotientMapU128.from_canonical_checked inst x ⦃ r =>
      (x.val < p.val → ∃ e, r = some e ∧ e.value.val = x.val * 2 ^ 32 % p.val) ∧
      (p.val ≤ x.val → r = none) ⦄ := by
  unfold P3_fieldIntegersQuotientMapU128.from_canonical_checked
  have hm := hv.monty
  dsimp only
  rw [hm.prime]
  have hp := hm.lt
  step*

open monty_31.MontyField31.Insts in
theorem from_canonical_checked_i64.spec (hv : FieldValid inst p mu) (x : Std.I64) :
    P3_fieldIntegersQuotientMapI64.from_canonical_checked inst x ⦃ r =>
      (-((p.val - 1) / 2 : ℕ) ≤ x.val → x.val ≤ ((p.val - 1) / 2 : ℕ) →
        ∃ e, r = some e ∧ e.value.val < p.val ∧
          (e.value.val : ℤ) % p.val = x.val * 2 ^ 32 % p.val) ∧
      ((x.val < -((p.val - 1) / 2 : ℕ) ∨ ((p.val - 1) / 2 : ℕ) < x.val) → r = none) ⦄ := by
  unfold P3_fieldIntegersQuotientMapI64.from_canonical_checked
  have hm := hv.monty
  dsimp only
  rw [hm.prime]
  have hp := hm.lt
  have hodd := hm.odd
  have hhalf : ∀ h : Std.U32, h.val = p.val >>> 1 →
      (UScalar.hcast .I64 h).val = (((p.val - 1) / 2 : ℕ) : ℤ) := by
    intro h hh
    rw [UScalar.hcast_val_eq, IScalarTy.I64_numBits_eq, hh, Nat.shiftRight_eq_div_pow, pow_one]
    rw [Int.bmod_eq_of_le (by push_cast; omega) (by push_cast; omega)]
    push_cast; omega
  step*
  all_goals have hb := hhalf half half_post
  all_goals simp only [IScalar.le_equiv, ge_iff_le] at *
  · have hc : (IScalar.cast .I32 x).val = x.val := by
      rw [IScalar.cast_val_eq, IScalarTy.I32_numBits_eq, IScalarTy.I64_numBits_eq,
        show Min.min 32 64 = 32 from rfl]
      exact Int.bmod_eq_of_le (by push_cast; omega) (by push_cast; omega)
    rw [hc] at v_post1
    refine ⟨fun _ _ => ⟨e, rfl, ‹e.value = v› ▸ ‹v.val < p.val›, ‹e.value = v› ▸ v_post1⟩, fun h => ?_⟩
    omega

open monty_31.MontyField31.Insts in
theorem from_canonical_checked_i128.spec (hv : FieldValid inst p mu) (x : Std.I128) :
    P3_fieldIntegersQuotientMapI128.from_canonical_checked inst x ⦃ r =>
      (-((p.val - 1) / 2 : ℕ) ≤ x.val → x.val ≤ ((p.val - 1) / 2 : ℕ) →
        ∃ e, r = some e ∧ e.value.val < p.val ∧
          (e.value.val : ℤ) % p.val = x.val * 2 ^ 32 % p.val) ∧
      ((x.val < -((p.val - 1) / 2 : ℕ) ∨ ((p.val - 1) / 2 : ℕ) < x.val) → r = none) ⦄ := by
  unfold P3_fieldIntegersQuotientMapI128.from_canonical_checked
  have hm := hv.monty
  dsimp only
  rw [hm.prime]
  have hp := hm.lt
  have hodd := hm.odd
  have hhalf : ∀ h : Std.U32, h.val = p.val >>> 1 →
      (UScalar.hcast .I128 h).val = (((p.val - 1) / 2 : ℕ) : ℤ) := by
    intro h hh
    rw [UScalar.hcast_val_eq, IScalarTy.I128_numBits_eq, hh, Nat.shiftRight_eq_div_pow, pow_one]
    rw [Int.bmod_eq_of_le (by push_cast; omega) (by push_cast; omega)]
    push_cast; omega
  step*
  all_goals have hb := hhalf half half_post
  all_goals simp only [IScalar.le_equiv, ge_iff_le] at *
  · have hc : (IScalar.cast .I32 x).val = x.val := by
      rw [IScalar.cast_val_eq, IScalarTy.I32_numBits_eq, IScalarTy.I128_numBits_eq,
        show Min.min 32 128 = 32 from rfl]
      exact Int.bmod_eq_of_le (by push_cast; omega) (by push_cast; omega)
    rw [hc] at v_post1
    refine ⟨fun _ _ => ⟨e, rfl, ‹e.value = v› ▸ ‹v.val < p.val›, ‹e.value = v› ▸ v_post1⟩, fun h => ?_⟩
    omega

end Plonky3Lean.Proofs.Monty31
