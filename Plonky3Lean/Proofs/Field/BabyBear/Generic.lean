module

public import Plonky3Lean.Proofs.Field.BabyBear.Arith
public import Plonky3Lean.Proofs.Field.BabyBear.Constants
public import Plonky3Lean.Proofs.Field.Monty31.Inverse

@[expose] public section

/-!
# BabyBear: the generic Monty31 results, at BabyBear's parameters
-/

open Aeneas Aeneas.Std CoreModels
open p3_baby_bear
open Plonky3Lean.Spec.Monty31
open Plonky3Lean.Spec.BabyBear (MontyParams FieldParams)

namespace Plonky3Lean.Proofs.P3BabyBear

/-- BabyBear's `MontyParameters` pass the checks of `MontyField31::new`. -/
theorem valid : Valid MontyParams 2013265921#u32 2281701377#u32 where
  prime := by
    show RustM.ok baby_bear.BabyBearParameters.Insts.P3_monty_31Data_traitsMontyParameters.PRIME = _
    unfold baby_bear.BabyBearParameters.Insts.P3_monty_31Data_traitsMontyParameters.PRIME; rfl
  bits := by
    show RustM.ok baby_bear.BabyBearParameters.Insts.P3_monty_31Data_traitsMontyParameters.MONTY_BITS = _
    unfold baby_bear.BabyBearParameters.Insts.P3_monty_31Data_traitsMontyParameters.MONTY_BITS; rfl
  monty_mu := by
    show RustM.ok baby_bear.BabyBearParameters.Insts.P3_monty_31Data_traitsMontyParameters.MONTY_MU = _
    unfold baby_bear.BabyBearParameters.Insts.P3_monty_31Data_traitsMontyParameters.MONTY_MU; rfl
  mask := Plonky3Lean.Proofs.P3BabyBear.MontyParams.MONTY_MASK.eq
  odd := by decide
  lt := by decide
  inv := by decide

/-- BabyBear's `FieldParameters` keep `HALF_P_PLUS_1` at its default. -/
theorem fieldValid : FieldValid FieldParams 2013265921#u32 2281701377#u32 where
  monty := valid
  half := by
    obtain ⟨h, hh, hv, -⟩ := WP.spec_imp_exists FieldParams.HALF_P_PLUS_1.spec
    exact ⟨h, hh, by rw [hv]; rfl⟩

/-- BabyBear's named elements zero, one and two keep their defaults. -/
theorem fieldDefaults : FieldDefaults FieldParams where
  zero := by
    simp
  one := by
    simp
  two := by
    simp

end Plonky3Lean.Proofs.P3BabyBear

namespace Plonky3Lean.Proofs.P3BabyBear

open Plonky3Lean.Spec.BabyBear

/-- `try_inverse(a)` of a canonical BabyBear element `a`, read as field elements.

- Zero gives `None`.
- Otherwise `Some(c)`, with `c` canonical and `c · a = 1` in the field. -/
theorem baby_bear.BabyBear.try_inverse.toField (a : Element) (ha : Spec.BabyBear.Canonical a) :
    p3_monty_31.monty_31.MontyField31.try_inverse FieldParams a ⦃ r =>
      (Spec.BabyBear.toField a = 0 → r = none) ∧
      (Spec.BabyBear.toField a ≠ 0 → ∃ c, r = some c ∧ Spec.BabyBear.Canonical c ∧
        Spec.BabyBear.toField c * Spec.BabyBear.toField a = 1) ⦄ := by
  have hprime : Nat.Prime (2013265921#u32 : Std.U32).val := by
    have := BabyBear.is_prime; unfold BabyBear.fieldSize at this; exact this
  refine WP.spec_mono (Proofs.Monty31.monty_31.MontyField31.try_inverse.spec fieldValid
    fieldDefaults hprime (by decide) a ha) ?_
  rintro r ⟨h0, h1⟩
  have hR : (2 ^ 32 : BabyBear.Field) ≠ 0 := by decide
  have hza : Spec.BabyBear.toField a = 0 ↔ a.value.val = 0 := by
    unfold Spec.BabyBear.toField
    rw [mul_eq_zero, or_iff_left (inv_ne_zero hR), ZMod.natCast_eq_zero_iff]
    unfold Spec.BabyBear.Canonical at ha
    constructor
    · intro hd; exact Nat.eq_zero_of_dvd_of_lt hd ha
    · intro h0; rw [h0]; exact dvd_zero _
  refine ⟨fun h => h0 (hza.mp h), fun h => ?_⟩
  obtain ⟨c, rfl, hc, hca⟩ := h1 (fun h' => h (hza.mpr h'))
  refine ⟨c, rfl, hc, ?_⟩
  have hca' : (c.value.val : BabyBear.Field) * a.value.val = 2 ^ 64 := by
    have := (ZMod.natCast_eq_natCast_iff _ _ BabyBear.fieldSize).mpr hca
    push_cast at this; exact this
  unfold Spec.BabyBear.toField
  calc (c.value.val : BabyBear.Field) * (2 ^ 32)⁻¹ * (a.value.val * (2 ^ 32)⁻¹)
      = (c.value.val * a.value.val) * ((2 ^ 32)⁻¹ * (2 ^ 32)⁻¹) := by ring
    _ = 2 ^ 64 * ((2 ^ 32)⁻¹ * (2 ^ 32)⁻¹) := by rw [hca']
    _ = 1 := by rw [show (2 : BabyBear.Field) ^ 64 = 2 ^ 32 * 2 ^ 32 by ring]; field_simp

end Plonky3Lean.Proofs.P3BabyBear
