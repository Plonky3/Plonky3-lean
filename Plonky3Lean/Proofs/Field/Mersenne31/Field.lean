module

public import CompPoly.Fields.Mersenne31
public import Plonky3Lean.Proofs.Field.Mersenne31.DotProduct
public import Plonky3Lean.Proofs.Field.Mersenne31.Inverse

@[expose] public section

/-!
# Mersenne31: the scalar operations, as field operations

Each value-level specification, read through `toField` in CompPoly's `Mersenne31.Field`.
-/

open Aeneas Aeneas.Std CoreModels
open p3_mersenne_31
open Plonky3Lean.Spec.Mersenne31 Plonky3Lean.Lib

namespace Plonky3Lean.Proofs.P3Mersenne31

theorem fieldSize_val : Mersenne31.fieldSize = 2147483647 := rfl

/-- Two stored values stand for the same field element exactly when they agree modulo `p`. -/
theorem natCast_eq_iff (m n : ℕ) :
    (m : Mersenne31.Field) = n ↔ m % 2147483647 = n % 2147483647 :=
  ZMod.natCast_eq_natCast_iff' m n _

theorem intCast_eq_iff (m n : ℤ) :
    (m : Mersenne31.Field) = n ↔ m % 2147483647 = n % 2147483647 :=
  ZMod.intCast_eq_intCast_iff' m n _

/-- A stored value below `2^31` is zero in the field exactly when it is `0` or `p`. -/
theorem toField_eq_zero_iff (x : Element) (hx : Valid x) :
    toField x = 0 ↔ x.value.val = 0 ∨ x.value.val = 2147483647 := by
  have hx' : x.value.val < 2 ^ 31 := hx
  rw [toField, ← Nat.cast_zero, natCast_eq_iff]
  omega

/-- The canonical representative that `as_canonical_u32` returns. -/
theorem canon_toField (x : Element) (hx : Valid x) :
    (if x.value.val = 2147483647 then 0 else x.value.val) < 2147483647 ∧
      ((if x.value.val = 2147483647 then 0 else x.value.val : ℕ) : Mersenne31.Field) = toField x := by
  have hx' : x.value.val < 2 ^ 31 := hx
  refine ⟨by split_ifs <;> omega, ?_⟩
  rw [toField, natCast_eq_iff]
  split_ifs <;> omega

/-! ## Arithmetic -/

theorem add.toField (a b : Element) (ha : Valid a) (hb : Valid b) :
    mersenne_31.Mersenne31.Insts.CoreOpsArithAddMersenne31Mersenne31.add a b
      ⦃ r => Valid r ∧ toField r = toField a + toField b ⦄ := by
  refine WP.spec_mono (add.spec a b ha hb) ?_
  rintro r ⟨hv, hr⟩
  refine ⟨hv, ?_⟩
  unfold Spec.Mersenne31.toField
  rw [← Nat.cast_add, natCast_eq_iff, hr]
  split_ifs <;> omega

theorem sub.toField (a b : Element) (ha : Valid a) (hb : Valid b) :
    mersenne_31.Mersenne31.Insts.CoreOpsArithSubMersenne31Mersenne31.sub a b
      ⦃ r => Valid r ∧ toField r = toField a - toField b ⦄ := by
  refine WP.spec_mono (sub.spec a b ha hb) ?_
  rintro r ⟨hv, hr⟩
  refine ⟨hv, ?_⟩
  have ha' : a.value.val < 2 ^ 31 := ha
  have hb' : b.value.val < 2 ^ 31 := hb
  rw [eq_sub_iff_add_eq]
  unfold Spec.Mersenne31.toField
  rw [← Nat.cast_add, natCast_eq_iff, hr]
  split_ifs <;> omega

theorem neg.toField (a : Element) (ha : Valid a) :
    mersenne_31.Mersenne31.Insts.CoreOpsArithNegMersenne31.neg a
      ⦃ r => Valid r ∧ toField r = -toField a ⦄ := by
  refine WP.spec_mono (neg.spec a ha) ?_
  rintro r ⟨hv, hr⟩
  refine ⟨hv, ?_⟩
  have ha' : a.value.val < 2 ^ 31 := ha
  rw [eq_neg_iff_add_eq_zero]
  unfold Spec.Mersenne31.toField
  rw [← Nat.cast_add, ← Nat.cast_zero, natCast_eq_iff, hr]
  omega

theorem mul.toField (a b : Element) (ha : Valid a) (hb : Valid b) :
    mersenne_31.Mersenne31.Insts.CoreOpsArithMulMersenne31Mersenne31.mul a b
      ⦃ r => Valid r ∧ toField r = toField a * toField b ⦄ := by
  refine WP.spec_mono (mul.spec a b ha hb) ?_
  rintro r ⟨hv, hr⟩
  refine ⟨hv, ?_⟩
  unfold Spec.Mersenne31.toField
  rw [← Nat.cast_mul, natCast_eq_iff, hr]

theorem halve.toField (a : Element) (ha : Valid a) :
    mersenne_31.Mersenne31.Insts.P3_fieldFieldPrimeCharacteristicRing.halve a
      ⦃ r => Valid r ∧ toField r * 2 = toField a ⦄ := by
  refine WP.spec_mono (halve.spec a ha) ?_
  rintro r ⟨hv, hr⟩
  refine ⟨hv, ?_⟩
  unfold Spec.Mersenne31.toField
  rw [show (2 : Mersenne31.Field) = ((2 : ℕ) : Mersenne31.Field) by norm_num, ← Nat.cast_mul,
    natCast_eq_iff, hr]

theorem mul_2exp_u64.toField (a : Element) (ha : Valid a) (e : Std.U64) :
    mersenne_31.Mersenne31.Insts.P3_fieldFieldPrimeCharacteristicRing.mul_2exp_u64 a e
      ⦃ r => Valid r ∧ toField r = toField a * 2 ^ e.val ⦄ := by
  refine WP.spec_mono (mul_2exp_u64.spec a ha e) ?_
  rintro r ⟨hv, hr⟩
  refine ⟨hv, ?_⟩
  unfold Spec.Mersenne31.toField
  rw [show (2 : Mersenne31.Field) ^ e.val = ((2 ^ e.val : ℕ) : Mersenne31.Field) by norm_num,
    ← Nat.cast_mul, natCast_eq_iff, hr]

theorem div_2exp_u64.toField (a : Element) (ha : Valid a) (e : Std.U64) :
    mersenne_31.Mersenne31.Insts.P3_fieldFieldPrimeCharacteristicRing.div_2exp_u64 a e
      ⦃ r => Valid r ∧ toField r * 2 ^ e.val = toField a ⦄ := by
  refine WP.spec_mono (div_2exp_u64.spec a ha e) ?_
  rintro r ⟨hv, hr⟩
  refine ⟨hv, ?_⟩
  unfold Spec.Mersenne31.toField
  rw [show (2 : Mersenne31.Field) ^ e.val = ((2 ^ e.val : ℕ) : Mersenne31.Field) by norm_num,
    ← Nat.cast_mul, natCast_eq_iff, hr]

/-! ## Constructors -/

theorem new.toField (x : Std.U32) :
    mersenne_31.Mersenne31.new x ⦃ r => Canonical r ∧ toField r = (x.val : Mersenne31.Field) ⦄ := by
  refine WP.spec_mono (new.spec x) ?_
  intro r hr
  refine ⟨by rw [Canonical, hr, fieldSize_val]; omega, ?_⟩
  unfold Spec.Mersenne31.toField
  rw [natCast_eq_iff, hr]; omega

theorem new_checked.toField (x : Std.U32) :
    mersenne_31.Mersenne31.new_checked x ⦃ r =>
      match r with
      | .Some y => x.val < 2 ^ 31 ∧ y.value = x ∧ Valid y ∧ toField y = (x.val : Mersenne31.Field)
      | .None => 2 ^ 31 ≤ x.val ⦄ := by
  refine WP.spec_mono (new_checked.spec x) ?_
  intro r hr
  subst hr
  split_ifs with h
  · exact ⟨h, rfl, h, rfl⟩
  · omega

theorem from_bool.toField (b : Bool) :
    mersenne_31.Mersenne31.Insts.P3_fieldFieldPrimeCharacteristicRing.from_bool b
      ⦃ r => Canonical r ∧ toField r = if b then 1 else 0 ⦄ := by
  refine WP.spec_mono (from_bool.spec b) ?_
  intro r hr
  unfold Spec.Mersenne31.toField Canonical
  rw [hr]
  cases b <;> simp [fieldSize_val]

/-! ## Reading an element -/

theorem as_canonical_u32.toField (a : Element) (ha : Valid a) :
    mersenne_31.Mersenne31.Insts.P3_fieldFieldPrimeField32.as_canonical_u32 a
      ⦃ r => r.val < Mersenne31.fieldSize ∧ (r.val : Mersenne31.Field) = toField a ⦄ := by
  refine WP.spec_mono (as_canonical_u32.spec a) ?_
  intro r hr
  rw [hr]
  exact canon_toField a ha

theorem is_zero.toField (a : Element) (ha : Valid a) :
    mersenne_31.Mersenne31.Insts.P3_fieldFieldField.is_zero a ⦃ r => r = decide (toField a = 0) ⦄ := by
  refine WP.spec_mono (is_zero.spec a) ?_
  intro r hr
  rw [hr]
  exact decide_eq_decide.mpr (toField_eq_zero_iff a ha).symm

theorem eq.toField (a b : Element) (ha : Valid a) (hb : Valid b) :
    mersenne_31.Mersenne31.Insts.CoreCmpPartialEqMersenne31.eq a b
      ⦃ r => r = decide (toField a = toField b) ⦄ := by
  refine WP.spec_mono (eq.spec a b) ?_
  intro r hr
  rw [hr]
  apply decide_eq_decide.mpr
  obtain ⟨hal, hae⟩ := canon_toField a ha
  obtain ⟨hbl, hbe⟩ := canon_toField b hb
  rw [← hae, ← hbe, natCast_eq_iff, Nat.mod_eq_of_lt hal, Nat.mod_eq_of_lt hbl]

/-! ## Integer conversions -/

theorem from_int_u64.toField (x : Std.U64) :
    mersenne_31.Mersenne31.Insts.P3_fieldIntegersQuotientMapU64.from_int x
      ⦃ r => Canonical r ∧ toField r = (x.val : Mersenne31.Field) ⦄ := by
  refine WP.spec_mono (from_int_u64.spec x) ?_
  intro r hr
  refine ⟨by rw [Canonical, hr, fieldSize_val]; omega, ?_⟩
  unfold Spec.Mersenne31.toField
  rw [natCast_eq_iff, hr]; omega

theorem from_int_u128.toField (x : Std.U128) :
    mersenne_31.Mersenne31.Insts.P3_fieldIntegersQuotientMapU128.from_int x
      ⦃ r => Canonical r ∧ toField r = (x.val : Mersenne31.Field) ⦄ := by
  refine WP.spec_mono (from_int_u128.spec x) ?_
  intro r hr
  refine ⟨by rw [Canonical, hr, fieldSize_val]; omega, ?_⟩
  unfold Spec.Mersenne31.toField
  rw [natCast_eq_iff, hr]; omega

theorem from_int_u32.toField (x : Std.U32) :
    mersenne_31.Mersenne31.Insts.P3_fieldIntegersQuotientMapU32.from_int x
      ⦃ r => Valid r ∧ toField r = (x.val : Mersenne31.Field) ⦄ := by
  refine WP.spec_mono (from_int_u32.spec x) ?_
  rintro r ⟨hv, hr⟩
  exact ⟨hv, (natCast_eq_iff _ _).mpr hr⟩

theorem intCast_of_mod (r : Element) (x : ℤ)
    (h : (r.value.val : ℤ) % 2147483647 = x % 2147483647) :
    toField r = (x : Mersenne31.Field) := by
  unfold Spec.Mersenne31.toField
  rw [← Int.cast_natCast, intCast_eq_iff]; exact h

theorem from_int_i32.toField (x : Std.I32) :
    mersenne_31.Mersenne31.Insts.P3_fieldIntegersQuotientMapI32.from_int x
      ⦃ r => Valid r ∧ toField r = (x.val : Mersenne31.Field) ⦄ := by
  refine WP.spec_mono (from_int_i32.spec x) ?_
  rintro r ⟨hv, hr⟩
  exact ⟨hv, intCast_of_mod r _ hr⟩

theorem from_int_i64.toField (x : Std.I64) :
    mersenne_31.Mersenne31.Insts.P3_fieldIntegersQuotientMapI64.from_int x
      ⦃ r => Valid r ∧ toField r = (x.val : Mersenne31.Field) ⦄ := by
  refine WP.spec_mono (from_int_i64.spec x) ?_
  rintro r ⟨hv, hr⟩
  exact ⟨hv, intCast_of_mod r _ hr⟩

theorem from_int_i128.toField (x : Std.I128) :
    mersenne_31.Mersenne31.Insts.P3_fieldIntegersQuotientMapI128.from_int x
      ⦃ r => Valid r ∧ toField r = (x.val : Mersenne31.Field) ⦄ := by
  refine WP.spec_mono (from_int_i128.spec x) ?_
  rintro r ⟨hv, hr⟩
  exact ⟨hv, intCast_of_mod r _ hr⟩

/-! ## Inversion -/

theorem try_inverse.toField (hg : GcdInversionContract) (a : Element) (ha : Valid a) :
    mersenne_31.Mersenne31.Insts.P3_fieldFieldField.try_inverse a ⦃ r =>
      match r with
      | .None => toField a = 0
      | .Some y => Valid y ∧ toField y = (toField a)⁻¹ ⦄ := by
  refine WP.spec_mono (try_inverse.spec hg a ha) ?_
  intro r hr
  match r, hr with
  | .None, hr => exact (toField_eq_zero_iff a ha).mpr hr
  | .Some y, ⟨hv, hy⟩ =>
    refine ⟨hv, ?_⟩
    have : Fact (Nat.Prime Mersenne31.fieldSize) := ⟨Mersenne31.is_prime⟩
    have h1 : Spec.Mersenne31.toField y * Spec.Mersenne31.toField a = 1 := by
      unfold Spec.Mersenne31.toField
      rw [← Nat.cast_mul, ← Nat.cast_one, natCast_eq_iff, hy]
    exact eq_inv_of_mul_eq_one_left h1

end Plonky3Lean.Proofs.P3Mersenne31
