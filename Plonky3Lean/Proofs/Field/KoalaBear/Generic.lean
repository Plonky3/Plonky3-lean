module

public import Plonky3Lean.Proofs.Field.KoalaBear.Arith
public import Plonky3Lean.Proofs.Field.Monty31.Inverse

@[expose] public section

/-!
# KoalaBear: the generic Monty31 results, at KoalaBear's parameters

`MontyParams.valid` and `FieldParams.valid` are in `Plonky3Lean.Proofs.Field.KoalaBear`.
-/

open Aeneas Aeneas.Std CoreModels
open p3_koala_bear
open Plonky3Lean.Spec.KoalaBear

namespace Plonky3Lean.Proofs.P3KoalaBear

/-- KoalaBear's `FieldParameters` keep `MONTY_ZERO`, `MONTY_ONE` and `MONTY_TWO` at their defaults. -/
theorem FieldParams.defaults : Spec.Monty31.FieldDefaults FieldParams where
  zero := by simp
  one := by simp
  two := by simp

/-- `try_inverse(a)` of a canonical KoalaBear element `a`, read as field elements.

Zero gives `None`.

Otherwise it gives `Some(c)`, with `c` canonical and `c · a = 1` in the field. -/
theorem koala_bear.KoalaBear.try_inverse.toField (a : Element) (ha : Canonical a) :
    p3_monty_31.monty_31.MontyField31.try_inverse FieldParams a ⦃ r =>
      (toField a = 0 → r = none) ∧
      (toField a ≠ 0 → ∃ c, r = some c ∧ Canonical c ∧ toField c * toField a = 1) ⦄ := by
  have hP := koala_bear.KoalaBearParameters.PRIME.eq_fieldSize
  have hprime := koala_bear.KoalaBearParameters.PRIME.is_prime
  have ha' : a.value.val < PRIME.val := by rw [hP]; exact ha
  refine WP.spec_mono (Proofs.Monty31.monty_31.MontyField31.try_inverse.spec FieldParams.valid
    FieldParams.defaults hprime (by rw [hP]; decide) a ha') ?_
  rintro r ⟨h0, h1⟩
  have hR : (2 ^ 32 : KoalaBear.Field) ≠ 0 := by decide
  have hza : Spec.KoalaBear.toField a = 0 ↔ a.value.val = 0 := by
    unfold Spec.KoalaBear.toField Spec.Monty31.toField
    rw [mul_eq_zero, or_iff_left (inv_ne_zero hR), ZMod.natCast_eq_zero_iff]
    constructor
    · intro hd; exact Nat.eq_zero_of_dvd_of_lt hd ha
    · intro h0; rw [h0]; exact dvd_zero _
  refine ⟨fun h => h0 (hza.mp h), fun h => ?_⟩
  obtain ⟨c, rfl, hc, hca⟩ := h1 (fun h' => h (hza.mpr h'))
  refine ⟨c, rfl, by unfold Spec.KoalaBear.Canonical Spec.Monty31.Canonical; rw [← hP]; exact hc, ?_⟩
  rw [hP] at hca
  have hca' : (c.value.val : KoalaBear.Field) * a.value.val = 2 ^ 64 := by
    have := (ZMod.natCast_eq_natCast_iff _ _ KoalaBear.fieldSize).mpr hca
    push_cast at this; exact this
  unfold Spec.KoalaBear.toField Spec.Monty31.toField
  calc (c.value.val : KoalaBear.Field) * (2 ^ 32)⁻¹ * (a.value.val * (2 ^ 32)⁻¹)
      = (c.value.val * a.value.val) * ((2 ^ 32)⁻¹ * (2 ^ 32)⁻¹) := by ring
    _ = 2 ^ 64 * ((2 ^ 32)⁻¹ * (2 ^ 32)⁻¹) := by rw [hca']
    _ = 1 := by rw [show (2 : KoalaBear.Field) ^ 64 = 2 ^ 32 * 2 ^ 32 by ring]; field_simp

end Plonky3Lean.Proofs.P3KoalaBear
