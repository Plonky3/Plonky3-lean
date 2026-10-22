module

public import Plonky3Lean.Proofs.Field.KoalaBear.Constants

@[expose] public section

/-!
# KoalaBear: scalar arithmetic

The `MontyField31` operators at KoalaBear's parameters, read through `Plonky3Lean.Spec.KoalaBear.toField`.

Each is the generic theorem of `Plonky3Lean.Proofs.Monty31` at `MontyParams.valid` and `p = KoalaBear.fieldSize`.
-/

open Aeneas Aeneas.Std CoreModels
open p3_koala_bear
open Plonky3Lean.Spec.KoalaBear

namespace Plonky3Lean.Proofs.P3KoalaBear

/-- `a + b`, for canonical `a` and `b`, is canonical and stands for `toField a + toField b`. -/
theorem koala_bear.KoalaBear.add.toField (a b : Element) (ha : Canonical a) (hb : Canonical b) :
    p3_monty_31.monty_31.MontyField31.Insts.CoreOpsArithAddMontyField31MontyField31.add MontyParams a b
      ⦃ c => Canonical c ∧ toField c = toField a + toField b ⦄ :=
  Monty31.monty_31.MontyField31.add.toField MontyParams.valid
    koala_bear.KoalaBearParameters.PRIME.eq_fieldSize a b ha hb

/-- `a - b`, for canonical `a` and `b`, is canonical and stands for `toField a - toField b`. -/
theorem koala_bear.KoalaBear.sub.toField (a b : Element) (ha : Canonical a) (hb : Canonical b) :
    p3_monty_31.monty_31.MontyField31.Insts.CoreOpsArithSubMontyField31MontyField31.sub MontyParams a b
      ⦃ c => Canonical c ∧ toField c = toField a - toField b ⦄ :=
  Monty31.monty_31.MontyField31.sub.toField MontyParams.valid
    koala_bear.KoalaBearParameters.PRIME.eq_fieldSize a b ha hb

/-- `a · b`, for canonical `a` and `b`, is canonical and stands for `toField a · toField b`. -/
theorem koala_bear.KoalaBear.mul.toField (a b : Element) (ha : Canonical a) (hb : Canonical b) :
    p3_monty_31.monty_31.MontyField31.Insts.CoreOpsArithMulMontyField31MontyField31.mul MontyParams a b
      ⦃ c => Canonical c ∧ toField c = toField a * toField b ⦄ :=
  Monty31.monty_31.MontyField31.mul.toField MontyParams.valid
    koala_bear.KoalaBearParameters.PRIME.eq_fieldSize a b ha hb

/-- `-a`, for canonical `a`, is canonical and stands for `-toField a`. -/
theorem koala_bear.KoalaBear.neg.toField (a : Element) (ha : Canonical a) :
    p3_monty_31.monty_31.MontyField31.Insts.CoreOpsArithNegMontyField31.neg FieldParams a
      ⦃ c => Canonical c ∧ toField c = -toField a ⦄ :=
  Monty31.monty_31.MontyField31.neg.toField FieldParams.valid
    koala_bear.KoalaBearParameters.PRIME.eq_fieldSize FieldParams.MONTY_ZERO.toField a ha

/-- `a.halve()`, for canonical `a`, is canonical and stands for `toField a / 2`. -/
theorem koala_bear.KoalaBear.halve.toField (a : Element) (ha : Canonical a) :
    p3_monty_31.monty_31.MontyField31.halve FieldParams a
      ⦃ c => Canonical c ∧ toField c * 2 = toField a ⦄ :=
  Monty31.monty_31.MontyField31.halve.toField FieldParams.valid
    koala_bear.KoalaBearParameters.PRIME.eq_fieldSize a ha

/-- `from_monty(a.value)`, the body of `as_canonical_u32`, is the canonical `u32` for the field element `a` stands for. -/
theorem koala_bear.KoalaBear.from_monty.toField (a : Element) :
    p3_monty_31.utils.from_monty MontyParams a.value
      ⦃ r => r.val < KoalaBear.fieldSize ∧ (r.val : KoalaBear.Field) = toField a ⦄ :=
  Monty31.from_monty.toField MontyParams.valid
    koala_bear.KoalaBearParameters.PRIME.eq_fieldSize a

/-! ## `RelativelyPrimePower<3>` -/

/-- `exp_root_d` is `exp_1420470955`, and raising to the power `1420470955` inverts `x ↦ x^3`. -/
theorem koala_bear.KoalaBearParameters.exp_root_d.exponent :
    (∀ {R : Type} (inst : p3_field.field.PrimeCharacteristicRing R) (x : R),
      koala_bear.KoalaBearParameters.Insts.P3_monty_31Data_traitsRelativelyPrimePower3.exp_root_d
          inst x =
        p3_field.exponentiation.exp_1420470955 inst x) ∧
    ∀ x : KoalaBear.Field, (x ^ 1420470955) ^ 3 = x :=
  ⟨fun _ _ => rfl, KoalaBear.pow_1420470955_pow_three⟩

end Plonky3Lean.Proofs.P3KoalaBear
