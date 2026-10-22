import Plonky3Lean.Lib.Scalar.U64
import Plonky3Lean.Spec.Goldilocks

/-!
# Goldilocks: the constants the arithmetic reads, and reading values as field elements

The literal `18446744069414584321` is `p = 2^64 - 2^32 + 1`.
-/

open Aeneas Aeneas.Std CoreModels p3_goldilocks Plonky3Lean.Lib
open Plonky3Lean.Spec.Goldilocks

namespace Plonky3Lean.Proofs.Goldilocks

theorem fieldSize_eq : Goldilocks.fieldSize = 18446744069414584321 := rfl


/-- `PrimeField64::ORDER_U64` is `p`. -/
theorem ORDER_U64.val_eq : goldilocks.Goldilocks.Insts.P3_fieldFieldPrimeField64.ORDER_U64.val = 18446744069414584321 := by
  unfold goldilocks.Goldilocks.Insts.P3_fieldFieldPrimeField64.ORDER_U64 goldilocks.P; rfl

/-- `PrimeField64::ORDER_U64` is the literal `p`. -/
theorem ORDER_U64.eq : goldilocks.Goldilocks.Insts.P3_fieldFieldPrimeField64.ORDER_U64 = 18446744069414584321#u64 := by
  unfold goldilocks.Goldilocks.Insts.P3_fieldFieldPrimeField64.ORDER_U64 goldilocks.P; rfl

/-- `NEG_ORDER = 2^64 - p = 2^32 - 1`. -/
theorem NEG_ORDER.eq : goldilocks.Goldilocks.NEG_ORDER = .ok 4294967295#u64 := by
  unfold goldilocks.Goldilocks.NEG_ORDER goldilocks.Goldilocks.Insts.P3_fieldFieldPrimeField64.ORDER_U64 goldilocks.P
  rfl

/-- `Goldilocks::new` stores its input unchanged. -/
@[step]
theorem new.spec (v : Std.U64) : goldilocks.Goldilocks.new v ⦃ r => r.value = v ⦄ := by
  simp [goldilocks.Goldilocks.new]

/-- `assert_unchecked(true)` returns. -/
@[simp]
theorem assert_unchecked_true : CoreModels.core.hint.assert_unchecked true = .ok () := rfl

/-- Two naturals that differ by a multiple of `p` have the same residue. -/
theorem mod_p_of_eq (x y k : ℕ) (h : x = y + 18446744069414584321 * k) :
    x % 18446744069414584321 = y % 18446744069414584321 := by
  rw [h, Nat.add_mul_mod_self_left]

/-- `branch_hint` returns. -/
theorem branch_hint.eq : p3_util.branch_hint = .ok () := rfl

/-- Two `Goldilocks` values stand for the same field element exactly when their residues agree. -/
theorem toField_eq_iff (x y : Element) :
    toField x = toField y ↔ x.value.val % 18446744069414584321 = y.value.val % 18446744069414584321 :=
  ZMod.natCast_eq_natCast_iff' _ _ _

/-- A residue equation on naturals, read in the field. -/
theorem natCast_eq_of_mod {x y : ℕ} (h : x % 18446744069414584321 = y % 18446744069414584321) :
    (x : Goldilocks.Field) = y :=
  (ZMod.natCast_eq_natCast_iff' _ _ _).mpr h

end Plonky3Lean.Proofs.Goldilocks
