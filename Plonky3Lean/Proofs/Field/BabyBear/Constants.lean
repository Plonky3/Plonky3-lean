import Mathlib.FieldTheory.Finite.Basic
import Plonky3Lean.Lib.OrderOf
import Plonky3Lean.Lib.PowMod
import Plonky3Lean.Proofs.Field.BabyBear.Element

/-!
# BabyBear: the base-field constants

The constants of `baby-bear/src/baby_bear.rs` and the p3-monty-31 defaults they
inherit, read as field elements through `Plonky3Lean.Spec.BabyBear.toField`.
-/

open Aeneas Aeneas.Std CoreModels
open p3_baby_bear
open Plonky3Lean.Spec.BabyBear
open Plonky3Lean.Lib

namespace Plonky3Lean.Proofs.BabyBear

/-! ## `FieldParameters` -/

theorem FieldParams.MONTY_ZERO.toField :
    FieldParams.MONTY_ZERO ⦃ r => Canonical r ∧ Spec.BabyBear.toField r = 0 ⦄ := by
  simpa using baby_bear.BabyBear.new.toField 0#u32

theorem FieldParams.MONTY_ONE.toField :
    FieldParams.MONTY_ONE ⦃ r => Canonical r ∧ Spec.BabyBear.toField r = 1 ⦄ := by
  simpa using baby_bear.BabyBear.new.toField 1#u32

theorem FieldParams.MONTY_TWO.toField :
    FieldParams.MONTY_TWO ⦃ r => Canonical r ∧ Spec.BabyBear.toField r = 2 ⦄ := by
  simpa using baby_bear.BabyBear.new.toField 2#u32

theorem FieldParams.MONTY_NEG_ONE.toField :
    FieldParams.MONTY_NEG_ONE ⦃ r => Canonical r ∧ Spec.BabyBear.toField r = -1 ⦄ := by
  dsimp only
  unfold baby_bear.BabyBearParameters.Insts.P3_monty_31Data_traitsMontyParameters.PRIME
  step*
  refine Aeneas.Std.WP.spec_mono (baby_bear.BabyBear.new.toField i1) ?_
  rintro r ⟨hc, hr⟩
  refine ⟨hc, ?_⟩
  rw [hr, i1_post1]
  decide

theorem FieldParams.HALF_P_PLUS_1.spec :
    FieldParams.HALF_P_PLUS_1 ⦃ h => h.val = (BabyBear.fieldSize + 1) / 2 ∧
      (h.val : BabyBear.Field) * 2 = 1 ⦄ := by
  dsimp only
  unfold baby_bear.BabyBearParameters.Insts.P3_monty_31Data_traitsMontyParameters.PRIME
  step*
  have hh : h.val = (BabyBear.fieldSize + 1) / 2 := by
    rw [h_post1, i1_post, Nat.shiftRight_eq_div_pow]; rfl
  refine ⟨hh, ?_⟩
  rw [hh]
  decide

/-- `b ^ e ≠ 1` in `BabyBear.Field`, from a `powMod` the kernel can evaluate. -/
theorem pow_ne_one_of_powMod {e : ℕ} (b : ℕ) (he : e < 2 ^ 64)
    (h : (Lib.powMod b e BabyBear.fieldSize : BabyBear.Field) ≠ 1) :
    (b : BabyBear.Field) ^ e ≠ 1 := by
  rwa [zmod_pow_eq_powMod b e he]

/-- The primes dividing `p - 1 = 2^27 · 3 · 5`. -/
theorem prime_dvd_fieldSize_sub_one {q : ℕ} (hq : q.Prime) (h : q ∣ BabyBear.fieldSize - 1) :
    q = 2 ∨ q = 3 ∨ q = 5 := by
  rw [show BabyBear.fieldSize - 1 = 2 ^ 27 * 3 * 5 by decide] at h
  rcases (Nat.Prime.dvd_mul hq).mp h with h | h
  · rcases (Nat.Prime.dvd_mul hq).mp h with h | h
    · exact .inl ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp (hq.dvd_of_dvd_pow h))
    · exact .inr (.inl ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp h))
  · exact .inr (.inr ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_five).mp h))

/-- `31` generates the multiplicative group of the BabyBear field. -/
theorem orderOf_thirtyOne : orderOf (31 : BabyBear.Field) = BabyBear.fieldSize - 1 := by
  apply orderOf_eq_of_pow_and_pow_div_prime (by decide)
  · exact ZMod.pow_card_sub_one_eq_one (by decide)
  · intro q hq hdvd
    rcases prime_dvd_fieldSize_sub_one hq hdvd with rfl | rfl | rfl <;>
    · exact_mod_cast pow_ne_one_of_powMod 31 (by unfold BabyBear.fieldSize; norm_num) (by decide)

theorem FieldParams.MONTY_GEN.generator :
    FieldParams.MONTY_GEN ⦃ g => Canonical g ∧
      orderOf (Spec.BabyBear.toField g) = BabyBear.fieldSize - 1 ⦄ := by
  dsimp only
  unfold baby_bear.BabyBearParameters.Insts.P3_monty_31Data_traitsFieldParameters.MONTY_GEN
  refine Aeneas.Std.WP.spec_mono (baby_bear.BabyBear.new.toField 31#u32) ?_
  rintro g ⟨hc, hg⟩
  refine ⟨hc, ?_⟩
  rw [hg]
  exact_mod_cast orderOf_thirtyOne

/-! ## `TwoAdicData` -/

/-- A table built as `&BabyBear::new_array([..])`: its entries are canonical and
stand for the literals mod `p`. -/
theorem slice_of_new_array {N : Std.Usize} (input : Array Std.U32 N) {L : List BabyBear.Field}
    (hL : input.val.map (fun x => (x.val : BabyBear.Field)) = L) :
    (do
      let a ← p3_monty_31.monty_31.MontyField31.new_array MontyParams input
      RustM.ok (Array.to_slice a))
      ⦃ s => (∀ y ∈ s.val, Canonical y) ∧ s.val.map Spec.BabyBear.toField = L ⦄ := by
  apply Aeneas.Std.WP.spec_bind (baby_bear.BabyBear.new_array.toField input)
  rintro a ⟨hc, hm⟩
  exact (Aeneas.Std.WP.spec_ok _).mpr ⟨hc, by rw [← hL]; exact hm⟩

/-- `TWO_ADIC_GENERATORS` is CompPoly's `BabyBear.twoAdicGenerators`. -/
theorem TwoAdicParams.TWO_ADIC_GENERATORS.eq_twoAdicGenerators :
    TwoAdicParams.TWO_ADIC_GENERATORS ⦃ s => (∀ y ∈ s.val, Canonical y) ∧
      s.val.map Spec.BabyBear.toField = BabyBear.twoAdicGenerators ⦄ := by
  dsimp only
  unfold baby_bear.BabyBearParameters.Insts.P3_monty_31Data_traitsTwoAdicDataSharedStaticSliceMontyField31BabyBearParameters.TWO_ADIC_GENERATORS
  exact slice_of_new_array _ (by decide)

theorem TwoAdicParams.TWO_ADIC_GENERATORS.order :
    TwoAdicParams.TWO_ADIC_GENERATORS ⦃ s => s.val.length = TWO_ADICITY.val + 1 ∧
      ∀ i (h : i < s.val.length), orderOf (Spec.BabyBear.toField s.val[i]) = 2 ^ i ⦄ := by
  refine Aeneas.Std.WP.spec_mono TwoAdicParams.TWO_ADIC_GENERATORS.eq_twoAdicGenerators ?_
  rintro s ⟨-, hs⟩
  have hlen : s.val.length = BabyBear.twoAdicGenerators.length := by
    rw [← hs, List.length_map]
  refine ⟨by rw [hlen, BabyBear.twoAdicGenerators_length,
    baby_bear.BabyBearParameters.TWO_ADICITY.eq_twoAdicity], fun i h => ?_⟩
  have hi : i < BabyBear.twoAdicity + 1 := by
    rw [hlen, BabyBear.twoAdicGenerators_length] at h; exact h
  have he : Spec.BabyBear.toField s.val[i] = BabyBear.twoAdicGenerators[i]'(by omega) := by
    simp only [← hs, List.getElem_map]
  rw [he]
  exact BabyBear.twoAdicGenerators_order ⟨i, hi⟩

theorem TwoAdicParams.TWO_ADIC_GENERATORS.sq_succ :
    TwoAdicParams.TWO_ADIC_GENERATORS ⦃ s => ∀ i (h : i + 1 < s.val.length),
      Spec.BabyBear.toField s.val[i + 1] ^ 2 = Spec.BabyBear.toField s.val[i] ⦄ := by
  refine Aeneas.Std.WP.spec_mono TwoAdicParams.TWO_ADIC_GENERATORS.eq_twoAdicGenerators ?_
  rintro s ⟨-, hs⟩ i h
  have hlen : s.val.length = BabyBear.twoAdicity + 1 := by
    rw [← BabyBear.twoAdicGenerators_length, ← hs, List.length_map]
  have e1 : Spec.BabyBear.toField s.val[i + 1] =
      BabyBear.twoAdicGenerators[i + 1]'(by rw [BabyBear.twoAdicGenerators_length]; omega) := by
    simp only [← hs, List.getElem_map]
  have e2 : Spec.BabyBear.toField s.val[i] =
      BabyBear.twoAdicGenerators[i]'(by rw [BabyBear.twoAdicGenerators_length]; omega) := by
    simp only [← hs, List.getElem_map]
  rw [e1, e2]
  exact BabyBear.twoAdicGenerators_succ_square_eq i (by omega)

/-- A list whose `i`-th entry times `ω ^ i` is `1` is the list of inverses of the
powers of `ω`. -/
theorem eq_map_inv_pow {L : List BabyBear.Field} {n : ℕ} {ω : BabyBear.Field}
    (hlen : L.length = n) (h : ∀ i (hi : i < L.length), L[i] * ω ^ i = 1) :
    L = (List.range n).map (fun j => (ω ^ j)⁻¹) := by
  apply List.ext_getElem (by simp [hlen])
  intro i h1 _
  simp only [List.getElem_map, List.getElem_range]
  exact eq_inv_of_mul_eq_one_left (h i h1)

theorem TwoAdicParams.ROOTS_8.eq :
    TwoAdicParams.ROOTS_8 ⦃ s => (∀ y ∈ s.val, Canonical y) ∧
      s.val.map Spec.BabyBear.toField =
        (List.range 4).map (fun j => BabyBear.twoAdicGenerators[3]! ^ j) ⦄ := by
  dsimp only
  unfold baby_bear.BabyBearParameters.Insts.P3_monty_31Data_traitsTwoAdicDataSharedStaticSliceMontyField31BabyBearParameters.ROOTS_8
  exact slice_of_new_array _ (by decide)

theorem TwoAdicParams.INV_ROOTS_8.eq :
    TwoAdicParams.INV_ROOTS_8 ⦃ s => (∀ y ∈ s.val, Canonical y) ∧
      s.val.map Spec.BabyBear.toField =
        (List.range 4).map (fun j => (BabyBear.twoAdicGenerators[3]! ^ j)⁻¹) ⦄ := by
  dsimp only
  unfold baby_bear.BabyBearParameters.Insts.P3_monty_31Data_traitsTwoAdicDataSharedStaticSliceMontyField31BabyBearParameters.INV_ROOTS_8
  exact slice_of_new_array _ (eq_map_inv_pow (by decide) (by decide))

theorem TwoAdicParams.ROOTS_16.eq :
    TwoAdicParams.ROOTS_16 ⦃ s => (∀ y ∈ s.val, Canonical y) ∧
      s.val.map Spec.BabyBear.toField =
        (List.range 8).map (fun j => BabyBear.twoAdicGenerators[4]! ^ j) ⦄ := by
  dsimp only
  unfold baby_bear.BabyBearParameters.Insts.P3_monty_31Data_traitsTwoAdicDataSharedStaticSliceMontyField31BabyBearParameters.ROOTS_16
  exact slice_of_new_array _ (by decide)

theorem TwoAdicParams.INV_ROOTS_16.eq :
    TwoAdicParams.INV_ROOTS_16 ⦃ s => (∀ y ∈ s.val, Canonical y) ∧
      s.val.map Spec.BabyBear.toField =
        (List.range 8).map (fun j => (BabyBear.twoAdicGenerators[4]! ^ j)⁻¹) ⦄ := by
  dsimp only
  unfold baby_bear.BabyBearParameters.Insts.P3_monty_31Data_traitsTwoAdicDataSharedStaticSliceMontyField31BabyBearParameters.INV_ROOTS_16
  exact slice_of_new_array _ (eq_map_inv_pow (by decide) (by decide))

theorem TwoAdicParams.ODD_FACTOR.spec :
    TwoAdicParams.ODD_FACTOR ⦃ r => r.val = 15 ∧
      (PRIME.val : ℤ) = r.val * 2 ^ TWO_ADICITY.val + 1 ⦄ := by
  dsimp only
  unfold baby_bear.BabyBearParameters.Insts.P3_monty_31Data_traitsMontyParameters.PRIME
    baby_bear.BabyBearParameters.Insts.P3_monty_31Data_traitsTwoAdicDataSharedStaticSliceMontyField31BabyBearParameters.TWO_ADICITY
  step*
  have h15 : (UScalar.hcast IScalarTy.I32 i2).val = 15 := by
    rw [UScalar.hcast_val_eq, i2_post1]; decide
  refine ⟨h15, ?_⟩
  rw [h15, baby_bear.BabyBearParameters.PRIME.eq_fieldSize,
    baby_bear.BabyBearParameters.TWO_ADICITY.eq_twoAdicity]
  decide

/-! ## `RelativelyPrimePower<7>` -/

/-- `x ↦ x^1725656503` inverts `x ↦ x^7` on the BabyBear field, since
`7 · 1725656503 = 6 · (p - 1) + 1`. -/
theorem exp_root_seven (x : BabyBear.Field) : (x ^ 1725656503) ^ 7 = x := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · rw [← pow_mul, show 1725656503 * 7 = 6 * (BabyBear.fieldSize - 1) + 1 by decide,
      pow_succ, pow_mul', ZMod.pow_card_sub_one_eq_one hx, one_pow, one_mul]

/-! ## The two remaining Poseidon length assertions -/

theorem poseidon1._.holds : poseidon1._ ⦃ _ => True ⦄ := by
  obtain ⟨t, ht⟩ : ∃ t, poseidon1.BABYBEAR_POSEIDON1_RC_16 = .ok t := by
    unfold poseidon1.BABYBEAR_POSEIDON1_RC_16; exact baby_bear.BabyBear.new_2d_array.never_panics _
  unfold poseidon1._
    poseidon1.BABYBEAR_POSEIDON1_HALF_FULL_ROUNDS poseidon1.BABYBEAR_POSEIDON1_PARTIAL_ROUNDS_16
  simp only [ht, bind_tc_ok, CoreModels.core.slice.Slice.len,
    CoreModels.rust_primitives.slice.slice_length]
  step*
  all_goals
    simp only [not_not]
    apply UScalar.eq_of_val_eq
    simp_all

theorem poseidon2._.holds : poseidon2._ ⦃ _ => True ⦄ := by
  obtain ⟨t, ht⟩ : ∃ t, poseidon2.BABYBEAR_POSEIDON2_RC_16_EXTERNAL_INITIAL = .ok t := by
    unfold poseidon2.BABYBEAR_POSEIDON2_RC_16_EXTERNAL_INITIAL
    exact baby_bear.BabyBear.new_2d_array.never_panics _
  unfold poseidon2._ poseidon2.BABYBEAR_POSEIDON2_HALF_FULL_ROUNDS
  simp only [ht, bind_tc_ok, CoreModels.core.slice.Slice.len,
    CoreModels.rust_primitives.slice.slice_length]
  step*
  all_goals
    simp only [not_not]
    apply UScalar.eq_of_val_eq
    simp_all

end Plonky3Lean.Proofs.BabyBear
