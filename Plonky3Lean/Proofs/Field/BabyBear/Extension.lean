module

public import Plonky3Lean.Proofs.Field.BabyBear.Constants
public import ToCompPoly.Fields.BabyBear.Extension

@[expose] public section

/-!
# BabyBear: the binomial extensions

`BinomialExtensionData<D>` for `D = 4, 5, 8`: `W`, with `X ^ D - W` irreducible;
`DTH_ROOT = W ^ ((p - 1) / D)`; `EXT_TWO_ADICITY`, the two-adicity of
`p ^ D - 1`; and `TWO_ADIC_EXTENSION_GENERATORS`, read in `F[X] / (X ^ D - W)`
through `Plonky3Lean.Spec.BabyBear.toExt`. Each is compared with CompPoly's
specification of the extension (`BabyBear.Ext4`, `Ext5`, `Ext8`), staged in
`ToCompPoly.Fields.BabyBear.Extension`.
-/

open Aeneas Aeneas.Std CoreModels Polynomial
open p3_baby_bear
open Plonky3Lean.Spec.BabyBear

namespace Plonky3Lean.Proofs.P3BabyBear

theorem Ext4Params.W.spec :
    Ext4Params.W ⦃ w => Canonical w ∧ Spec.BabyBear.toField w = 11 ∧
      Irreducible (X ^ 4 - C (Spec.BabyBear.toField w)) ⦄ := by
  dsimp only
  unfold baby_bear.BabyBearParameters.Insts.P3_monty_31Data_traitsBinomialExtensionDataArrayArrayMontyField31BabyBearParameters424.W
  refine Aeneas.Std.WP.spec_mono (baby_bear.BabyBear.new.toField 11#u32) ?_
  rintro w ⟨hc, hw⟩
  have hw' : Spec.BabyBear.toField w = 11 := by rw [hw]; rfl
  refine ⟨hc, hw', ?_⟩
  rw [hw']
  exact BabyBear.irreducible_ext4

theorem Ext4Params.EXT_TWO_ADICITY.spec :
    Ext4Params.EXT_TWO_ADICITY ⦃ e => 2 ^ e.val ∣ PRIME.val ^ 4 - 1 ∧
      ¬ 2 ^ (e.val + 1) ∣ PRIME.val ^ 4 - 1 ⦄ := by
  dsimp only
  rw [Aeneas.Std.WP.spec_ok, baby_bear.BabyBearParameters.PRIME.eq_fieldSize]
  unfold baby_bear.BabyBearParameters.Insts.P3_monty_31Data_traitsBinomialExtensionDataArrayArrayMontyField31BabyBearParameters424.EXT_TWO_ADICITY
  exact BabyBear.ext4TwoAdicity_spec

theorem Ext4Params.DTH_ROOT.spec :
    ∃ w r, Ext4Params.W = .ok w ∧ Ext4Params.DTH_ROOT = .ok r ∧ Canonical r ∧
      Spec.BabyBear.toField r = Spec.BabyBear.toField w ^ ((BabyBear.fieldSize - 1) / 4) := by
  obtain ⟨w, hw, -, hw11, -⟩ := Plonky3Lean.Lib.spec_imp_exists Ext4Params.W.spec
  have hd : Ext4Params.DTH_ROOT ⦃ r => Canonical r ∧
      Spec.BabyBear.toField r = ((1728404513 : ℕ) : BabyBear.Field) ⦄ := by
    dsimp only
    unfold baby_bear.BabyBearParameters.Insts.P3_monty_31Data_traitsBinomialExtensionDataArrayArrayMontyField31BabyBearParameters424.DTH_ROOT
    exact baby_bear.BabyBear.new.toField _
  obtain ⟨r, hr, hrc, hrv⟩ := Plonky3Lean.Lib.spec_imp_exists hd
  refine ⟨w, r, hw, hr, hrc, ?_⟩
  rw [hrv, hw11, show (11 : BabyBear.Field) = ((11 : ℕ) : BabyBear.Field) by norm_cast,
    BabyBear.natCast_pow_eq_powMod 11 _]
  decide

theorem Ext5Params.W.spec :
    Ext5Params.W ⦃ w => Canonical w ∧ Spec.BabyBear.toField w = 2 ∧
      Irreducible (X ^ 5 - C (Spec.BabyBear.toField w)) ⦄ := by
  dsimp only
  unfold baby_bear.BabyBearParameters.Insts.P3_monty_31Data_traitsBinomialExtensionDataArrayArrayMontyField31BabyBearParameters505.W
  refine Aeneas.Std.WP.spec_mono (baby_bear.BabyBear.new.toField 2#u32) ?_
  rintro w ⟨hc, hw⟩
  have hw' : Spec.BabyBear.toField w = 2 := by rw [hw]; rfl
  refine ⟨hc, hw', ?_⟩
  rw [hw']
  exact BabyBear.irreducible_ext5

theorem Ext5Params.EXT_TWO_ADICITY.spec :
    Ext5Params.EXT_TWO_ADICITY ⦃ e => 2 ^ e.val ∣ PRIME.val ^ 5 - 1 ∧
      ¬ 2 ^ (e.val + 1) ∣ PRIME.val ^ 5 - 1 ⦄ := by
  dsimp only
  rw [Aeneas.Std.WP.spec_ok, baby_bear.BabyBearParameters.PRIME.eq_fieldSize]
  unfold baby_bear.BabyBearParameters.Insts.P3_monty_31Data_traitsBinomialExtensionDataArrayArrayMontyField31BabyBearParameters505.EXT_TWO_ADICITY
  exact BabyBear.ext5TwoAdicity_spec

theorem Ext5Params.DTH_ROOT.spec :
    ∃ w r, Ext5Params.W = .ok w ∧ Ext5Params.DTH_ROOT = .ok r ∧ Canonical r ∧
      Spec.BabyBear.toField r = Spec.BabyBear.toField w ^ ((BabyBear.fieldSize - 1) / 5) := by
  obtain ⟨w, hw, -, hw11, -⟩ := Plonky3Lean.Lib.spec_imp_exists Ext5Params.W.spec
  have hd : Ext5Params.DTH_ROOT ⦃ r => Canonical r ∧
      Spec.BabyBear.toField r = ((815036133 : ℕ) : BabyBear.Field) ⦄ := by
    dsimp only
    unfold baby_bear.BabyBearParameters.Insts.P3_monty_31Data_traitsBinomialExtensionDataArrayArrayMontyField31BabyBearParameters505.DTH_ROOT
    exact baby_bear.BabyBear.new.toField _
  obtain ⟨r, hr, hrc, hrv⟩ := Plonky3Lean.Lib.spec_imp_exists hd
  refine ⟨w, r, hw, hr, hrc, ?_⟩
  rw [hrv, hw11, show (2 : BabyBear.Field) = ((2 : ℕ) : BabyBear.Field) by norm_cast,
    BabyBear.natCast_pow_eq_powMod 2 _]
  decide

theorem Ext8Params.W.spec :
    Ext8Params.W ⦃ w => Canonical w ∧ Spec.BabyBear.toField w = 11 ∧
      Irreducible (X ^ 8 - C (Spec.BabyBear.toField w)) ⦄ := by
  dsimp only
  unfold baby_bear.BabyBearParameters.Insts.P3_monty_31Data_traitsBinomialExtensionDataArrayArrayMontyField31BabyBearParameters838.W
  refine Aeneas.Std.WP.spec_mono (baby_bear.BabyBear.new.toField 11#u32) ?_
  rintro w ⟨hc, hw⟩
  have hw' : Spec.BabyBear.toField w = 11 := by rw [hw]; rfl
  refine ⟨hc, hw', ?_⟩
  rw [hw']
  exact BabyBear.irreducible_ext8

theorem Ext8Params.EXT_TWO_ADICITY.spec :
    Ext8Params.EXT_TWO_ADICITY ⦃ e => 2 ^ e.val ∣ PRIME.val ^ 8 - 1 ∧
      ¬ 2 ^ (e.val + 1) ∣ PRIME.val ^ 8 - 1 ⦄ := by
  dsimp only
  rw [Aeneas.Std.WP.spec_ok, baby_bear.BabyBearParameters.PRIME.eq_fieldSize]
  unfold baby_bear.BabyBearParameters.Insts.P3_monty_31Data_traitsBinomialExtensionDataArrayArrayMontyField31BabyBearParameters838.EXT_TWO_ADICITY
  exact BabyBear.ext8TwoAdicity_spec

theorem Ext8Params.DTH_ROOT.spec :
    ∃ w r, Ext8Params.W = .ok w ∧ Ext8Params.DTH_ROOT = .ok r ∧ Canonical r ∧
      Spec.BabyBear.toField r = Spec.BabyBear.toField w ^ ((BabyBear.fieldSize - 1) / 8) := by
  obtain ⟨w, hw, -, hw11, -⟩ := Plonky3Lean.Lib.spec_imp_exists Ext8Params.W.spec
  have hd : Ext8Params.DTH_ROOT ⦃ r => Canonical r ∧
      Spec.BabyBear.toField r = ((420899707 : ℕ) : BabyBear.Field) ⦄ := by
    dsimp only
    unfold baby_bear.BabyBearParameters.Insts.P3_monty_31Data_traitsBinomialExtensionDataArrayArrayMontyField31BabyBearParameters838.DTH_ROOT
    exact baby_bear.BabyBear.new.toField _
  obtain ⟨r, hr, hrc, hrv⟩ := Plonky3Lean.Lib.spec_imp_exists hd
  refine ⟨w, r, hw, hr, hrc, ?_⟩
  rw [hrv, hw11, show (11 : BabyBear.Field) = ((11 : ℕ) : BabyBear.Field) by norm_cast,
    BabyBear.natCast_pow_eq_powMod 11 _]
  decide

/-! ## Elements of the extensions -/

/-- A squaring chain is preserved by equality of lists. -/
theorem sq_chain_of_eq {M : Type} [Monoid M] {L L' : List M} (h : L = L')
    (hL' : ∀ i (h : i + 1 < L'.length), L'[i + 1] ^ 2 = L'[i]) :
    ∀ i (h : i + 1 < L.length), L[i + 1] ^ 2 = L[i] := by
  subst h; exact hL'

/-- The degree-4 `TWO_ADIC_EXTENSION_GENERATORS` are CompPoly's
`ext4TwoAdicGeneratorCoeffs`, entry for entry. -/
theorem Ext4Params.TWO_ADIC_EXTENSION_GENERATORS.eq :
    Ext4Params.TWO_ADIC_EXTENSION_GENERATORS ⦃ t =>
      t.val.map (fun row => row.val.map Spec.BabyBear.toField) =
        BabyBear.ext4TwoAdicGeneratorCoeffs ⦄ := by
  dsimp only
  unfold baby_bear.BabyBearParameters.Insts.P3_monty_31Data_traitsBinomialExtensionDataArrayArrayMontyField31BabyBearParameters424.TWO_ADIC_EXTENSION_GENERATORS
  refine Aeneas.Std.WP.spec_mono (baby_bear.BabyBear.new_2d_array.toField _) ?_
  rintro t ⟨-, ht⟩
  rw [ht]; decide

/-- Read in `F[X] / (X ^ 4 - 11)`, the model's table is CompPoly's
`ext4TwoAdicGenerators`. -/
theorem Ext4Params.TWO_ADIC_EXTENSION_GENERATORS.toExt_eq :
    ∃ t, Ext4Params.TWO_ADIC_EXTENSION_GENERATORS = .ok t ∧
      t.val.map (toExt 11) = BabyBear.ext4TwoAdicGenerators := by
  obtain ⟨t, ht, hc⟩ := Plonky3Lean.Lib.spec_imp_exists Ext4Params.TWO_ADIC_EXTENSION_GENERATORS.eq
  refine ⟨t, ht, ?_⟩
  unfold BabyBear.ext4TwoAdicGenerators
  rw [← hc, List.map_map]
  rfl

theorem Ext4Params.TWO_ADIC_EXTENSION_GENERATORS.sq_succ :
    ∃ w t, Ext4Params.W = .ok w ∧ Ext4Params.TWO_ADIC_EXTENSION_GENERATORS = .ok t ∧
      let chain := AdjoinRoot.of _ BabyBear.twoAdicGenerators[TWO_ADICITY.val]! ::
        t.val.map (toExt (Spec.BabyBear.toField w))
      ∀ i (h : i + 1 < chain.length), chain[i + 1] ^ 2 = chain[i] := by
  obtain ⟨w, hw, -, hw11, -⟩ := Plonky3Lean.Lib.spec_imp_exists Ext4Params.W.spec
  obtain ⟨t, ht, hm⟩ := Ext4Params.TWO_ADIC_EXTENSION_GENERATORS.toExt_eq
  refine ⟨w, t, hw, ht, ?_⟩
  have key : ∀ v : BabyBear.Field, v = 11 →
      let chain := AdjoinRoot.of (X ^ (4#usize).val - C v)
        BabyBear.twoAdicGenerators[TWO_ADICITY.val]! :: t.val.map (toExt v)
      ∀ i (h : i + 1 < chain.length), chain[i + 1] ^ 2 = chain[i] := by
    rintro v rfl chain
    refine sq_chain_of_eq (L := chain) ?_ BabyBear.ext4TwoAdicGenerators_sq_succ
    show _ :: _ = _
    rw [hm, baby_bear.BabyBearParameters.TWO_ADICITY.eq_twoAdicity]
    rfl
  exact key _ hw11

theorem Ext4Params.TWO_ADIC_EXTENSION_GENERATORS.order :
    ∃ w t e, Ext4Params.W = .ok w ∧ Ext4Params.TWO_ADIC_EXTENSION_GENERATORS = .ok t ∧
      Ext4Params.EXT_TWO_ADICITY = .ok e ∧ TWO_ADICITY.val + t.val.length = e.val ∧
      ∀ i (h : i < t.val.length),
        orderOf (toExt (Spec.BabyBear.toField w) t.val[i]) =
          2 ^ (TWO_ADICITY.val + 1 + i) := by
  obtain ⟨w, hw, -, hw11, -⟩ := Plonky3Lean.Lib.spec_imp_exists Ext4Params.W.spec
  obtain ⟨t, ht, hm⟩ := Ext4Params.TWO_ADIC_EXTENSION_GENERATORS.toExt_eq
  refine ⟨w, t, 29#usize, hw, ht, ?_, ?_, ?_⟩
  · dsimp only
    unfold baby_bear.BabyBearParameters.Insts.P3_monty_31Data_traitsBinomialExtensionDataArrayArrayMontyField31BabyBearParameters424.EXT_TWO_ADICITY
    rfl
  · rw [show t.val.length = 2 from t.property, baby_bear.BabyBearParameters.TWO_ADICITY.eq_twoAdicity]
    rfl
  have key : ∀ v : BabyBear.Field, v = 11 → ∀ i (h : i < t.val.length),
      orderOf (toExt v t.val[i]) = 2 ^ (TWO_ADICITY.val + 1 + i) := by
    rintro v rfl i hi
    have he : toExt 11 t.val[i] = BabyBear.ext4TwoAdicGenerators[i]'(by
        have : t.val.length = 2 := t.property
        rw [show BabyBear.ext4TwoAdicGenerators.length = 2 from rfl]; omega) := by
      simp only [← hm]
      exact (List.getElem_map _).symm
    rw [he, baby_bear.BabyBearParameters.TWO_ADICITY.eq_twoAdicity]
    exact BabyBear.ext4TwoAdicGenerators_order i _
  exact key _ hw11

/-- The degree-8 `TWO_ADIC_EXTENSION_GENERATORS` are CompPoly's
`ext8TwoAdicGeneratorCoeffs`, entry for entry. -/
theorem Ext8Params.TWO_ADIC_EXTENSION_GENERATORS.eq :
    Ext8Params.TWO_ADIC_EXTENSION_GENERATORS ⦃ t =>
      t.val.map (fun row => row.val.map Spec.BabyBear.toField) =
        BabyBear.ext8TwoAdicGeneratorCoeffs ⦄ := by
  dsimp only
  unfold baby_bear.BabyBearParameters.Insts.P3_monty_31Data_traitsBinomialExtensionDataArrayArrayMontyField31BabyBearParameters838.TWO_ADIC_EXTENSION_GENERATORS
  refine Aeneas.Std.WP.spec_mono (baby_bear.BabyBear.new_2d_array.toField _) ?_
  rintro t ⟨-, ht⟩
  rw [ht]; decide

/-- Read in `F[X] / (X ^ 8 - 11)`, the model's table is CompPoly's
`ext8TwoAdicGenerators`. -/
theorem Ext8Params.TWO_ADIC_EXTENSION_GENERATORS.toExt_eq :
    ∃ t, Ext8Params.TWO_ADIC_EXTENSION_GENERATORS = .ok t ∧
      t.val.map (toExt 11) = BabyBear.ext8TwoAdicGenerators := by
  obtain ⟨t, ht, hc⟩ := Plonky3Lean.Lib.spec_imp_exists Ext8Params.TWO_ADIC_EXTENSION_GENERATORS.eq
  refine ⟨t, ht, ?_⟩
  unfold BabyBear.ext8TwoAdicGenerators
  rw [← hc, List.map_map]
  rfl

theorem Ext8Params.TWO_ADIC_EXTENSION_GENERATORS.sq_succ :
    ∃ w t, Ext8Params.W = .ok w ∧ Ext8Params.TWO_ADIC_EXTENSION_GENERATORS = .ok t ∧
      let chain := AdjoinRoot.of _ BabyBear.twoAdicGenerators[TWO_ADICITY.val]! ::
        t.val.map (toExt (Spec.BabyBear.toField w))
      ∀ i (h : i + 1 < chain.length), chain[i + 1] ^ 2 = chain[i] := by
  obtain ⟨w, hw, -, hw11, -⟩ := Plonky3Lean.Lib.spec_imp_exists Ext8Params.W.spec
  obtain ⟨t, ht, hm⟩ := Ext8Params.TWO_ADIC_EXTENSION_GENERATORS.toExt_eq
  refine ⟨w, t, hw, ht, ?_⟩
  have key : ∀ v : BabyBear.Field, v = 11 →
      let chain := AdjoinRoot.of (X ^ (8#usize).val - C v)
        BabyBear.twoAdicGenerators[TWO_ADICITY.val]! :: t.val.map (toExt v)
      ∀ i (h : i + 1 < chain.length), chain[i + 1] ^ 2 = chain[i] := by
    rintro v rfl chain
    refine sq_chain_of_eq (L := chain) ?_ BabyBear.ext8TwoAdicGenerators_sq_succ
    show _ :: _ = _
    rw [hm, baby_bear.BabyBearParameters.TWO_ADICITY.eq_twoAdicity]
    rfl
  exact key _ hw11

theorem Ext8Params.TWO_ADIC_EXTENSION_GENERATORS.order :
    ∃ w t e, Ext8Params.W = .ok w ∧ Ext8Params.TWO_ADIC_EXTENSION_GENERATORS = .ok t ∧
      Ext8Params.EXT_TWO_ADICITY = .ok e ∧ TWO_ADICITY.val + t.val.length = e.val ∧
      ∀ i (h : i < t.val.length),
        orderOf (toExt (Spec.BabyBear.toField w) t.val[i]) =
          2 ^ (TWO_ADICITY.val + 1 + i) := by
  obtain ⟨w, hw, -, hw11, -⟩ := Plonky3Lean.Lib.spec_imp_exists Ext8Params.W.spec
  obtain ⟨t, ht, hm⟩ := Ext8Params.TWO_ADIC_EXTENSION_GENERATORS.toExt_eq
  refine ⟨w, t, 30#usize, hw, ht, ?_, ?_, ?_⟩
  · dsimp only
    unfold baby_bear.BabyBearParameters.Insts.P3_monty_31Data_traitsBinomialExtensionDataArrayArrayMontyField31BabyBearParameters838.EXT_TWO_ADICITY
    rfl
  · rw [show t.val.length = 3 from t.property, baby_bear.BabyBearParameters.TWO_ADICITY.eq_twoAdicity]
    rfl
  have key : ∀ v : BabyBear.Field, v = 11 → ∀ i (h : i < t.val.length),
      orderOf (toExt v t.val[i]) = 2 ^ (TWO_ADICITY.val + 1 + i) := by
    rintro v rfl i hi
    have he : toExt 11 t.val[i] = BabyBear.ext8TwoAdicGenerators[i]'(by
        have : t.val.length = 3 := t.property
        rw [show BabyBear.ext8TwoAdicGenerators.length = 3 from rfl]; omega) := by
      simp only [← hm]
      exact (List.getElem_map _).symm
    rw [he, baby_bear.BabyBearParameters.TWO_ADICITY.eq_twoAdicity]
    exact BabyBear.ext8TwoAdicGenerators_order i _
  exact key _ hw11

end Plonky3Lean.Proofs.P3BabyBear
