import Plonky3Lean.Proofs.Field.Monty31.Utils

/-!
# Monty31: integers into Montgomery form, for any valid parameters

The conversions of `monty-31/src/utils.rs` from `i32`, `u64` and `i64`.

Each is total: every input of its type is accepted, and the output is canonical.
-/

open Aeneas Aeneas.Std CoreModels
open p3_monty_31
open Plonky3Lean.Spec.Monty31 Plonky3Lean.Lib

namespace Plonky3Lean.Proofs.Monty31

variable {MP : Type} {inst : data_traits.MontyParameters MP} {p mu : Std.U32}

/-- `to_monty_signed(x)` puts any `i32` into Montgomery form: the canonical
representative of `x · 2^32 mod p`.

The shift is done in `i64`, where `|x| · 2^32 <= 2^63`.

The remainder truncates toward zero, so a negative input gives a negative
remainder, which is shifted back into `[0, p)` by adding `p`. -/
@[step]
theorem utils.to_monty_signed.spec (hv : Valid inst p mu) (x : Std.I32) :
    utils.to_monty_signed inst x ⦃ r => r.val < p.val ∧
      (r.val : ℤ) % p.val = x.val * 2 ^ 32 % p.val ⦄ := by
  unfold utils.to_monty_signed
  rw [hv.bits, hv.prime]
  have hp0 : 0 < p.val := by have := hv.odd; omega
  have hp := hv.lt
  have hx := x.hBounds
  simp only [IScalarTy.I32_numBits_eq] at hx
  have hi : ∀ i : Std.I64, i = IScalar.cast .I64 x → i.val = x.val := by
    rintro i rfl; exact IScalar.val_mod_pow_greater_numBits _ x (by decide)
  have hi4 : ∀ i4 : Std.I64, i4 = UScalar.hcast .I64 p → i4.val = p.val := by
    rintro i4 rfl
    rw [UScalar.hcast_val_eq, IScalarTy.I64_numBits_eq]
    exact Int.bmod_eq_of_le (by omega) (by omega)
  have hi2 : ∀ i i2 : Std.I64, i.val = x.val → i2.val = (i.val <<< 32).bmod I64.size →
      i2.val = x.val * 2 ^ 32 := by
    intro i i2 h h2
    have hs : I64.size = 2 ^ 64 := by simp [I64.size, I64.numBits]
    rw [h2, h, Int.shiftLeft_eq, hs]
    exact Int.bmod_eq_of_le (by push_cast; omega) (by push_cast; omega)
  step*
  all_goals
    have hi' := hi i i_post
    have hi4' := hi4 i4 i4_post
    have hi2' := hi2 i i2 hi' i2_post1
    have hp' : (0 : ℤ) < p.val := by omega
    have h5lt := Int.tmod_lt_of_pos (i2.val) (hi4' ▸ hp')
    have h5gt := Int.lt_tmod_of_pos (i2.val) (hi4' ▸ hp')
    have h5mod : Int.tmod i2.val i4.val % p.val = x.val * 2 ^ 32 % p.val := by
      rw [Int.tmod_def, hi2', hi4']; simp [Int.sub_emod, Int.mul_emod_right]
    have hred : red.val = i5.val := by
      rw [red_post, IScalar.cast_val_eq, IScalarTy.I32_numBits_eq, IScalarTy.I64_numBits_eq,
        show Min.min 32 64 = 32 from rfl, i5_post]
      exact Int.bmod_eq_of_le (by push_cast; omega) (by push_cast; omega)
  case h1 hge =>
    rw [IScalar.hcast_val_eq, UScalarTy.U32_numBits_eq]
    have hr0 : (0 : ℤ) ≤ red.val := by scalar_tac
    have hrv : red.val = Int.tmod i2.val i4.val := by rw [hred, i5_post]
    rw [Int.emod_eq_of_lt hr0 (by omega)]
    refine ⟨by omega, ?_⟩
    rw [Int.toNat_of_nonneg hr0, hrv, h5mod]
  all_goals
    rename_i hlt
    have hr0 : red.val < 0 := by scalar_tac
    have hrv : red.val = Int.tmod i2.val i4.val := by rw [hred, i5_post]
    have hr : (r.val : ℤ) = p.val + red.val := by
      rw [r_post, Int.emod_eq_of_lt (by omega) (by omega)]
    refine ⟨by omega, ?_⟩
    rw [hr, Int.add_emod, Int.emod_self, zero_add, Int.emod_emod_of_dvd _ (dvd_refl _), hrv, h5mod]

/-- `to_monty_64(x)` puts any `u64` into Montgomery form: `x · 2^32 mod p`.

The shift is done in `u128`, where `x · 2^32 < 2^96`. -/
@[step]
theorem utils.to_monty_64.spec (hv : Valid inst p mu) (x : Std.U64) :
    utils.to_monty_64 inst x ⦃ r => r.val = x.val * 2 ^ 32 % p.val ⦄ := by
  unfold utils.to_monty_64
  rw [hv.bits, hv.prime]
  have hp0 : 0 < p.val := by have := hv.odd; omega
  have hp := hv.lt
  have hx := u64_lt x
  step*

/-- `to_monty_64_signed(x)` puts any `i64` into Montgomery form: the canonical
representative of `x · 2^32 mod p`.

The shift is done in `i128`, and the remainder is shifted back into `[0, p)`
when it is negative, as for `i32`. -/
@[step]
theorem utils.to_monty_64_signed.spec (hv : Valid inst p mu) (x : Std.I64) :
    utils.to_monty_64_signed inst x ⦃ r => r.val < p.val ∧
      (r.val : ℤ) % p.val = x.val * 2 ^ 32 % p.val ⦄ := by
  unfold utils.to_monty_64_signed
  rw [hv.bits, hv.prime]
  have hp0 : 0 < p.val := by have := hv.odd; omega
  have hp := hv.lt
  have hx := x.hBounds
  simp only [IScalarTy.I64_numBits_eq] at hx
  have hi : ∀ i : Std.I128, i = IScalar.cast .I128 x → i.val = x.val := by
    rintro i rfl; exact IScalar.val_mod_pow_greater_numBits _ x (by decide)
  have hi4 : ∀ i4 : Std.I128, i4 = UScalar.hcast .I128 p → i4.val = p.val := by
    rintro i4 rfl
    rw [UScalar.hcast_val_eq, IScalarTy.I128_numBits_eq]
    exact Int.bmod_eq_of_le (by omega) (by omega)
  have hi2 : ∀ i i2 : Std.I128, i.val = x.val → i2.val = (i.val <<< 32).bmod I128.size →
      i2.val = x.val * 2 ^ 32 := by
    intro i i2 h h2
    have hs : I128.size = 2 ^ 128 := by simp [I128.size, I128.numBits]
    rw [h2, h, Int.shiftLeft_eq, hs]
    exact Int.bmod_eq_of_le (by push_cast; omega) (by push_cast; omega)
  step*
  all_goals
    have hi' := hi i i_post
    have hi4' := hi4 i4 i4_post
    have hi2' := hi2 i i2 hi' i2_post1
    have hp' : (0 : ℤ) < p.val := by omega
    have h5lt := Int.tmod_lt_of_pos (i2.val) (hi4' ▸ hp')
    have h5gt := Int.lt_tmod_of_pos (i2.val) (hi4' ▸ hp')
    have h5mod : Int.tmod i2.val i4.val % p.val = x.val * 2 ^ 32 % p.val := by
      rw [Int.tmod_def, hi2', hi4']; simp [Int.sub_emod, Int.mul_emod_right]
    have hred : red.val = i5.val := by
      rw [red_post, IScalar.cast_val_eq, IScalarTy.I32_numBits_eq, IScalarTy.I128_numBits_eq,
        show Min.min 32 128 = 32 from rfl, i5_post]
      exact Int.bmod_eq_of_le (by push_cast; omega) (by push_cast; omega)
  case h1 hge =>
    rw [IScalar.hcast_val_eq, UScalarTy.U32_numBits_eq]
    have hr0 : (0 : ℤ) ≤ red.val := by scalar_tac
    have hrv : red.val = Int.tmod i2.val i4.val := by rw [hred, i5_post]
    rw [Int.emod_eq_of_lt hr0 (by omega)]
    refine ⟨by omega, ?_⟩
    rw [Int.toNat_of_nonneg hr0, hrv, h5mod]
  all_goals
    rename_i hlt
    have hr0 : red.val < 0 := by scalar_tac
    have hrv : red.val = Int.tmod i2.val i4.val := by rw [hred, i5_post]
    have hr : (r.val : ℤ) = p.val + red.val := by
      rw [r_post, Int.emod_eq_of_lt (by omega) (by omega)]
    refine ⟨by omega, ?_⟩
    rw [hr, Int.add_emod, Int.emod_self, zero_add, Int.emod_emod_of_dvd _ (dvd_refl _), hrv, h5mod]

end Plonky3Lean.Proofs.Monty31
