import Plonky3Lean.Proofs.Field.KoalaBear

/-!
# KoalaBear: the base-field constants

The constants of `koala-bear/src/koala_bear.rs` and the p3-monty-31 defaults they inherit, read as field elements through `Plonky3Lean.Spec.KoalaBear.toField`.
-/

open Aeneas Aeneas.Std CoreModels
open p3_koala_bear
open Plonky3Lean.Spec.KoalaBear
open Plonky3Lean.Lib

namespace Plonky3Lean.Proofs.KoalaBear

/-! ## `FieldParameters` -/

theorem FieldParams.MONTY_ZERO.toField :
    FieldParams.MONTY_ZERO ⦃ r => Canonical r ∧ Spec.KoalaBear.toField r = 0 ⦄ := by
  simpa using koala_bear.KoalaBear.new.toField 0#u32

theorem FieldParams.MONTY_ONE.toField :
    FieldParams.MONTY_ONE ⦃ r => Canonical r ∧ Spec.KoalaBear.toField r = 1 ⦄ := by
  simpa using koala_bear.KoalaBear.new.toField 1#u32

theorem FieldParams.MONTY_TWO.toField :
    FieldParams.MONTY_TWO ⦃ r => Canonical r ∧ Spec.KoalaBear.toField r = 2 ⦄ := by
  simpa using koala_bear.KoalaBear.new.toField 2#u32

theorem FieldParams.MONTY_NEG_ONE.toField :
    FieldParams.MONTY_NEG_ONE ⦃ r => Canonical r ∧ Spec.KoalaBear.toField r = -1 ⦄ := by
  dsimp only
  unfold koala_bear.KoalaBearParameters.Insts.P3_monty_31Data_traitsMontyParameters.PRIME
  step*
  refine WP.spec_mono (koala_bear.KoalaBear.new.toField i1) ?_
  rintro r ⟨hc, hr⟩
  refine ⟨hc, ?_⟩
  rw [hr, i1_post1]
  decide

theorem FieldParams.HALF_P_PLUS_1.spec :
    FieldParams.HALF_P_PLUS_1 ⦃ h => h.val = (KoalaBear.fieldSize + 1) / 2 ∧
      (h.val : KoalaBear.Field) * 2 = 1 ⦄ := by
  dsimp only
  unfold koala_bear.KoalaBearParameters.Insts.P3_monty_31Data_traitsMontyParameters.PRIME
  step*
  have hh : h.val = (KoalaBear.fieldSize + 1) / 2 := by
    rw [h_post1, i1_post, Nat.shiftRight_eq_div_pow]; rfl
  refine ⟨hh, ?_⟩
  rw [hh]
  decide

/-- `MONTY_GEN` is `3`, CompPoly's `KoalaBear.primitiveRoot`, of order `p - 1`. -/
theorem FieldParams.MONTY_GEN.generator :
    FieldParams.MONTY_GEN ⦃ g => Canonical g ∧
      orderOf (Spec.KoalaBear.toField g) = KoalaBear.fieldSize - 1 ⦄ := by
  dsimp only
  unfold koala_bear.KoalaBearParameters.Insts.P3_monty_31Data_traitsFieldParameters.MONTY_GEN
  refine WP.spec_mono (koala_bear.KoalaBear.new.toField 3#u32) ?_
  rintro g ⟨hc, hg⟩
  refine ⟨hc, ?_⟩
  rw [hg]
  exact_mod_cast KoalaBear.primitiveRoot_order

/-! ## `TwoAdicData` -/

/-- A table built as `&KoalaBear::new_array([..])`: its entries are canonical and stand for the literals mod `p`. -/
theorem slice_of_new_array {N : Std.Usize} (input : Array Std.U32 N) {L : List KoalaBear.Field}
    (hL : input.val.map (fun x => (x.val : KoalaBear.Field)) = L) :
    (do
      let a ← p3_monty_31.monty_31.MontyField31.new_array MontyParams input
      RustM.ok (Array.to_slice a))
      ⦃ s => (∀ y ∈ s.val, Canonical y) ∧ s.val.map Spec.KoalaBear.toField = L ⦄ := by
  apply WP.spec_bind (koala_bear.KoalaBear.new_array.toField input)
  rintro a ⟨hc, hm⟩
  exact (WP.spec_ok _).mpr ⟨hc, by rw [← hL]; exact hm⟩

/-- `TWO_ADIC_GENERATORS` is CompPoly's `KoalaBear.twoAdicGenerators`. -/
theorem TwoAdicParams.TWO_ADIC_GENERATORS.eq_twoAdicGenerators :
    TwoAdicParams.TWO_ADIC_GENERATORS ⦃ s => (∀ y ∈ s.val, Canonical y) ∧
      s.val.map Spec.KoalaBear.toField = KoalaBear.twoAdicGenerators ⦄ := by
  dsimp only
  unfold koala_bear.KoalaBearParameters.Insts.P3_monty_31Data_traitsTwoAdicDataSharedStaticSliceMontyField31KoalaBearParameters.TWO_ADIC_GENERATORS
  exact slice_of_new_array _ (by decide)

theorem TwoAdicParams.TWO_ADIC_GENERATORS.order :
    TwoAdicParams.TWO_ADIC_GENERATORS ⦃ s => s.val.length = TWO_ADICITY.val + 1 ∧
      ∀ i (h : i < s.val.length), orderOf (Spec.KoalaBear.toField s.val[i]) = 2 ^ i ⦄ := by
  refine WP.spec_mono TwoAdicParams.TWO_ADIC_GENERATORS.eq_twoAdicGenerators ?_
  rintro s ⟨-, hs⟩
  have hlen : s.val.length = KoalaBear.twoAdicGenerators.length := by
    rw [← hs, List.length_map]
  refine ⟨by rw [hlen, KoalaBear.twoAdicGenerators_length,
    koala_bear.KoalaBearParameters.TWO_ADICITY.eq_twoAdicity], fun i h => ?_⟩
  have hi : i < KoalaBear.twoAdicity + 1 := by
    rw [hlen, KoalaBear.twoAdicGenerators_length] at h; exact h
  have he : Spec.KoalaBear.toField s.val[i] = KoalaBear.twoAdicGenerators[i]'(by omega) := by
    simp only [← hs, List.getElem_map]
  rw [he]
  exact KoalaBear.twoAdicGenerators_order ⟨i, hi⟩

theorem TwoAdicParams.TWO_ADIC_GENERATORS.sq_succ :
    TwoAdicParams.TWO_ADIC_GENERATORS ⦃ s => ∀ i (h : i + 1 < s.val.length),
      Spec.KoalaBear.toField s.val[i + 1] ^ 2 = Spec.KoalaBear.toField s.val[i] ⦄ := by
  refine WP.spec_mono TwoAdicParams.TWO_ADIC_GENERATORS.eq_twoAdicGenerators ?_
  rintro s ⟨-, hs⟩ i h
  have hlen : s.val.length = KoalaBear.twoAdicity + 1 := by
    rw [← KoalaBear.twoAdicGenerators_length, ← hs, List.length_map]
  have e1 : Spec.KoalaBear.toField s.val[i + 1] =
      KoalaBear.twoAdicGenerators[i + 1]'(by rw [KoalaBear.twoAdicGenerators_length]; omega) := by
    simp only [← hs, List.getElem_map]
  have e2 : Spec.KoalaBear.toField s.val[i] =
      KoalaBear.twoAdicGenerators[i]'(by rw [KoalaBear.twoAdicGenerators_length]; omega) := by
    simp only [← hs, List.getElem_map]
  rw [e1, e2]
  exact KoalaBear.twoAdicGenerators_succ_square_eq i (by omega)

/-- A list whose `i`-th entry times `ω ^ i` is `1` is the list of inverses of the powers of `ω`. -/
theorem eq_map_inv_pow {L : List KoalaBear.Field} {n : ℕ} {ω : KoalaBear.Field}
    (hlen : L.length = n) (h : ∀ i (hi : i < L.length), L[i] * ω ^ i = 1) :
    L = (List.range n).map (fun j => (ω ^ j)⁻¹) := by
  apply List.ext_getElem (by simp [hlen])
  intro i h1 _
  simp only [List.getElem_map, List.getElem_range]
  exact eq_inv_of_mul_eq_one_left (h i h1)

theorem TwoAdicParams.ROOTS_8.eq :
    TwoAdicParams.ROOTS_8 ⦃ s => (∀ y ∈ s.val, Canonical y) ∧
      s.val.map Spec.KoalaBear.toField =
        (List.range 4).map (fun j => KoalaBear.twoAdicGenerators[3]! ^ j) ⦄ := by
  dsimp only
  unfold koala_bear.KoalaBearParameters.Insts.P3_monty_31Data_traitsTwoAdicDataSharedStaticSliceMontyField31KoalaBearParameters.ROOTS_8
  exact slice_of_new_array _ (by decide)

theorem TwoAdicParams.INV_ROOTS_8.eq :
    TwoAdicParams.INV_ROOTS_8 ⦃ s => (∀ y ∈ s.val, Canonical y) ∧
      s.val.map Spec.KoalaBear.toField =
        (List.range 4).map (fun j => (KoalaBear.twoAdicGenerators[3]! ^ j)⁻¹) ⦄ := by
  dsimp only
  unfold koala_bear.KoalaBearParameters.Insts.P3_monty_31Data_traitsTwoAdicDataSharedStaticSliceMontyField31KoalaBearParameters.INV_ROOTS_8
  exact slice_of_new_array _ (eq_map_inv_pow (by decide) (by decide))

theorem TwoAdicParams.ROOTS_16.eq :
    TwoAdicParams.ROOTS_16 ⦃ s => (∀ y ∈ s.val, Canonical y) ∧
      s.val.map Spec.KoalaBear.toField =
        (List.range 8).map (fun j => KoalaBear.twoAdicGenerators[4]! ^ j) ⦄ := by
  dsimp only
  unfold koala_bear.KoalaBearParameters.Insts.P3_monty_31Data_traitsTwoAdicDataSharedStaticSliceMontyField31KoalaBearParameters.ROOTS_16
  exact slice_of_new_array _ (by decide)

theorem TwoAdicParams.INV_ROOTS_16.eq :
    TwoAdicParams.INV_ROOTS_16 ⦃ s => (∀ y ∈ s.val, Canonical y) ∧
      s.val.map Spec.KoalaBear.toField =
        (List.range 8).map (fun j => (KoalaBear.twoAdicGenerators[4]! ^ j)⁻¹) ⦄ := by
  dsimp only
  unfold koala_bear.KoalaBearParameters.Insts.P3_monty_31Data_traitsTwoAdicDataSharedStaticSliceMontyField31KoalaBearParameters.INV_ROOTS_16
  exact slice_of_new_array _ (eq_map_inv_pow (by decide) (by decide))

theorem TwoAdicParams.ODD_FACTOR.spec :
    TwoAdicParams.ODD_FACTOR ⦃ r => r.val = 127 ∧
      (PRIME.val : ℤ) = r.val * 2 ^ TWO_ADICITY.val + 1 ⦄ := by
  dsimp only
  unfold koala_bear.KoalaBearParameters.Insts.P3_monty_31Data_traitsMontyParameters.PRIME
    koala_bear.KoalaBearParameters.Insts.P3_monty_31Data_traitsTwoAdicDataSharedStaticSliceMontyField31KoalaBearParameters.TWO_ADICITY
  step*
  have h127 : (UScalar.hcast IScalarTy.I32 i2).val = 127 := by
    rw [UScalar.hcast_val_eq, i2_post1]; decide
  refine ⟨h127, ?_⟩
  rw [h127, koala_bear.KoalaBearParameters.PRIME.eq_fieldSize,
    koala_bear.KoalaBearParameters.TWO_ADICITY.eq_twoAdicity]
  decide

end Plonky3Lean.Proofs.KoalaBear
