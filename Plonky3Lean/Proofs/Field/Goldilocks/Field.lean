module

public import Plonky3Lean.Proofs.Field.Goldilocks.PowersOfTwo

@[expose] public section

/-!
# Goldilocks: the operators read in the field

The residue statements of `Arith`, restated through `toField`.
-/

open Aeneas Aeneas.Std CoreModels p3_goldilocks Plonky3Lean.Lib
open Plonky3Lean.Spec.Goldilocks

namespace Plonky3Lean.Proofs.P3Goldilocks

/-- `reduce128(x)` stands for `x`. -/
theorem reduce128.field (x : Std.U128) :
    goldilocks.reduce128 x ⦃ r => toField r = (x.val : Goldilocks.Field) ⦄ :=
  WP.spec_mono (reduce128.spec x) (fun _ hr => natCast_eq_of_mod hr)

/-- `Sub`, read in the field. -/
theorem sub.field (a b : goldilocks.Goldilocks) :
    goldilocks.Goldilocks.Insts.CoreOpsArithSubGoldilocksGoldilocks.sub a b ⦃ r =>
      toField r = toField a - toField b ⦄ :=
  WP.spec_mono (sub.spec a b) (fun r hr => by
    have := natCast_eq_of_mod hr
    push_cast at this
    unfold toField
    rw [← this]; ring)

/-- `as_canonical_u64` returns the canonical representative. -/
theorem as_canonical_u64.field (a : goldilocks.Goldilocks) :
    goldilocks.Goldilocks.Insts.P3_fieldFieldPrimeField64.as_canonical_u64 a ⦃ r =>
      (r.val : Goldilocks.Field) = toField a ∧ r.val < Goldilocks.fieldSize ⦄ :=
  WP.spec_mono (as_canonical_u64.spec a) (fun r hr => by
    rw [hr]; exact ⟨ZMod.natCast_mod _ _, Nat.mod_lt _ (by decide)⟩)

/-- `PartialEq::eq` compares field elements, not stored values. -/
theorem eq.field (a b : goldilocks.Goldilocks) :
    goldilocks.Goldilocks.Insts.CoreCmpPartialEqGoldilocks.eq a b ⦃ r =>
      r = decide (toField a = toField b) ⦄ :=
  WP.spec_mono (eq.spec a b) (fun r hr => by rw [hr, decide_eq_decide, toField_eq_iff])

/-- `is_zero` tests the field element, so it accepts both `0` and `p`. -/
theorem is_zero.field (a : goldilocks.Goldilocks) :
    goldilocks.Goldilocks.Insts.P3_fieldFieldField.is_zero a ⦃ r => r = decide (toField a = 0) ⦄ :=
  WP.spec_mono (is_zero.spec a) (fun r hr => by
    rw [hr, decide_eq_decide]
    unfold toField
    rw [ZMod.natCast_eq_zero_iff, Nat.dvd_iff_mod_eq_zero]
    rfl)

end Plonky3Lean.Proofs.P3Goldilocks
