module

public import Plonky3Lean.Proofs.Field.BabyBear.Constants
public import ToCompPoly.Fields.BabyBear.ExtTwoAdic

@[expose] public section

/-!
# BabyBear: the binomial extensions

`BinomialExtensionData<D>` for `D = 4, 5, 8`: `W`, with `X ^ D - W` irreducible;
`DTH_ROOT = W ^ ((p - 1) / D)`; `EXT_TWO_ADICITY`, the two-adicity of
`p ^ D - 1`; and `TWO_ADIC_EXTENSION_GENERATORS`, read in `F[X] / (X ^ D - W)`
through `Plonky3Lean.Spec.BabyBear.toExt`. Each is compared with CompPoly's
extensions: `BabyBear.Ext4`, and `Ext5`/`Ext8` staged in `ToCompPoly.Fields.BabyBear`, with
the two-adic data in `ToCompPoly.Fields.BabyBear.ExtTwoAdic`.
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
  exact BabyBear.ext4Params_poly_irreducible

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
  exact BabyBear.ext5Params_poly_irreducible

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
  exact BabyBear.ext8Params_poly_irreducible

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

/-- An array that `toExt` reads with exactly the coefficients of `x` stands for `x`. -/
theorem toExt_eq_of_coeffs {P : CompPoly.Extension.BinomialParams BabyBear.Field}
    {D : Usize} {row : Array Element D} {h : D.val = P.d}
    {x : CompPoly.Extension.Ext P.toExtensionParams}
    (hrow : row.val.map Spec.BabyBear.toField = List.ofFn (CompPoly.Extension.Ext.coeff x)) :
    toExt P row h = x := by
  apply CompPoly.Extension.Ext.ext
  intro i
  simp only [toExt, CompPoly.Extension.Ext.coeff, CompPoly.Extension.Ext.ofVector,
    Vector.getElem_mk, List.getElem_toArray]
  simp only [hrow, List.getElem_ofFn]
  rfl

/-- The degree-4 `TWO_ADIC_EXTENSION_GENERATORS` are `ext4TwoAdicGeneratorCoeffs`,
entry for entry. -/
theorem Ext4Params.TWO_ADIC_EXTENSION_GENERATORS.eq :
    Ext4Params.TWO_ADIC_EXTENSION_GENERATORS ⦃ t =>
      t.val.map (fun row => row.val.map Spec.BabyBear.toField) =
        BabyBear.ext4TwoAdicGeneratorCoeffs ⦄ := by
  dsimp only
  unfold baby_bear.BabyBearParameters.Insts.P3_monty_31Data_traitsBinomialExtensionDataArrayArrayMontyField31BabyBearParameters424.TWO_ADIC_EXTENSION_GENERATORS
  refine Aeneas.Std.WP.spec_mono (baby_bear.BabyBear.new_2d_array.toField _) ?_
  rintro t ⟨-, ht⟩
  rw [ht]; decide

/-- Read in `BabyBear.Ext4`, the model's table is `ext4TwoAdicGenerators`. -/
theorem Ext4Params.TWO_ADIC_EXTENSION_GENERATORS.toExt_eq :
    ∃ t, Ext4Params.TWO_ADIC_EXTENSION_GENERATORS = .ok t ∧
      t.val.map (fun row => toExt BabyBear.ext4Params row) = BabyBear.ext4TwoAdicGenerators := by
  obtain ⟨t, ht, hc⟩ := Plonky3Lean.Lib.spec_imp_exists Ext4Params.TWO_ADIC_EXTENSION_GENERATORS.eq
  refine ⟨t, ht, ?_⟩
  have hlen : t.val.length = 2 := t.property
  have hrow : ∀ j (hj : j < t.val.length), t.val[j].val.map Spec.BabyBear.toField =
      BabyBear.ext4TwoAdicGeneratorCoeffs[j]'(by
        simp only [BabyBear.ext4TwoAdicGeneratorCoeffs, List.length_cons, List.length_nil]
        omega) := by
    intro j hj; simp only [← hc, List.getElem_map]
  apply List.ext_getElem (by simp only [List.length_map, hlen]; rfl)
  intro j h1 h2
  rw [List.getElem_map]
  apply toExt_eq_of_coeffs
  rw [hrow j (by simpa only [List.length_map] using h1)]
  simp only [BabyBear.ext4TwoAdicGeneratorCoeffs_eq, List.getElem_map]

theorem Ext4Params.TWO_ADIC_EXTENSION_GENERATORS.sq_succ :
    ∃ w t, Ext4Params.W = .ok w ∧ Spec.BabyBear.toField w = BabyBear.ext4Params.W ∧
      Ext4Params.TWO_ADIC_EXTENSION_GENERATORS = .ok t ∧
      let chain : List BabyBear.Ext4 :=
        CompPoly.Extension.Ext.ofBase BabyBear.twoAdicGenerators[TWO_ADICITY.val]! ::
          t.val.map (fun row => toExt BabyBear.ext4Params row)
      ∀ i (h : i + 1 < chain.length), chain[i + 1] ^ 2 = chain[i] := by
  obtain ⟨w, hw, -, hwW, -⟩ := Plonky3Lean.Lib.spec_imp_exists Ext4Params.W.spec
  obtain ⟨t, ht, hm⟩ := Ext4Params.TWO_ADIC_EXTENSION_GENERATORS.toExt_eq
  refine ⟨w, t, hw, hwW, ht, ?_⟩
  intro chain
  refine sq_chain_of_eq (L := chain) ?_ BabyBear.ext4TwoAdicGenerators_sq_succ
  show _ :: _ = _
  rw [hm, baby_bear.BabyBearParameters.TWO_ADICITY.eq_twoAdicity]

theorem Ext4Params.TWO_ADIC_EXTENSION_GENERATORS.order :
    ∃ w t e, Ext4Params.W = .ok w ∧ Spec.BabyBear.toField w = BabyBear.ext4Params.W ∧
      Ext4Params.TWO_ADIC_EXTENSION_GENERATORS = .ok t ∧
      Ext4Params.EXT_TWO_ADICITY = .ok e ∧ TWO_ADICITY.val + t.val.length = e.val ∧
      ∀ i (h : i < t.val.length),
        orderOf (toExt BabyBear.ext4Params t.val[i]) = 2 ^ (TWO_ADICITY.val + 1 + i) := by
  obtain ⟨w, hw, -, hwW, -⟩ := Plonky3Lean.Lib.spec_imp_exists Ext4Params.W.spec
  obtain ⟨t, ht, hm⟩ := Ext4Params.TWO_ADIC_EXTENSION_GENERATORS.toExt_eq
  refine ⟨w, t, 29#usize, hw, hwW, ht, ?_, ?_, ?_⟩
  · dsimp only
    unfold baby_bear.BabyBearParameters.Insts.P3_monty_31Data_traitsBinomialExtensionDataArrayArrayMontyField31BabyBearParameters424.EXT_TWO_ADICITY
    rfl
  · rw [show t.val.length = 2 from t.property,
      baby_bear.BabyBearParameters.TWO_ADICITY.eq_twoAdicity]
    rfl
  intro i hi
  have he : toExt BabyBear.ext4Params t.val[i] = BabyBear.ext4TwoAdicGenerators[i]'(by
      have : t.val.length = 2 := t.property
      rw [show BabyBear.ext4TwoAdicGenerators.length = 2 from rfl]; omega) := by
    simp only [← hm, List.getElem_map]
  rw [he, baby_bear.BabyBearParameters.TWO_ADICITY.eq_twoAdicity]
  exact BabyBear.ext4TwoAdicGenerators_order i _

/-- The degree-8 `TWO_ADIC_EXTENSION_GENERATORS` are `ext8TwoAdicGeneratorCoeffs`,
entry for entry. -/
theorem Ext8Params.TWO_ADIC_EXTENSION_GENERATORS.eq :
    Ext8Params.TWO_ADIC_EXTENSION_GENERATORS ⦃ t =>
      t.val.map (fun row => row.val.map Spec.BabyBear.toField) =
        BabyBear.ext8TwoAdicGeneratorCoeffs ⦄ := by
  dsimp only
  unfold baby_bear.BabyBearParameters.Insts.P3_monty_31Data_traitsBinomialExtensionDataArrayArrayMontyField31BabyBearParameters838.TWO_ADIC_EXTENSION_GENERATORS
  refine Aeneas.Std.WP.spec_mono (baby_bear.BabyBear.new_2d_array.toField _) ?_
  rintro t ⟨-, ht⟩
  rw [ht]; decide

/-- Read in `BabyBear.Ext8`, the model's table is `ext8TwoAdicGenerators`. -/
theorem Ext8Params.TWO_ADIC_EXTENSION_GENERATORS.toExt_eq :
    ∃ t, Ext8Params.TWO_ADIC_EXTENSION_GENERATORS = .ok t ∧
      t.val.map (fun row => toExt BabyBear.ext8Params row) = BabyBear.ext8TwoAdicGenerators := by
  obtain ⟨t, ht, hc⟩ := Plonky3Lean.Lib.spec_imp_exists Ext8Params.TWO_ADIC_EXTENSION_GENERATORS.eq
  refine ⟨t, ht, ?_⟩
  have hlen : t.val.length = 3 := t.property
  have hrow : ∀ j (hj : j < t.val.length), t.val[j].val.map Spec.BabyBear.toField =
      BabyBear.ext8TwoAdicGeneratorCoeffs[j]'(by
        simp only [BabyBear.ext8TwoAdicGeneratorCoeffs, List.length_cons, List.length_nil]
        omega) := by
    intro j hj; simp only [← hc, List.getElem_map]
  apply List.ext_getElem (by simp only [List.length_map, hlen]; rfl)
  intro j h1 h2
  rw [List.getElem_map]
  apply toExt_eq_of_coeffs
  rw [hrow j (by simpa only [List.length_map] using h1)]
  simp only [BabyBear.ext8TwoAdicGeneratorCoeffs_eq, List.getElem_map]

theorem Ext8Params.TWO_ADIC_EXTENSION_GENERATORS.sq_succ :
    ∃ w t, Ext8Params.W = .ok w ∧ Spec.BabyBear.toField w = BabyBear.ext8Params.W ∧
      Ext8Params.TWO_ADIC_EXTENSION_GENERATORS = .ok t ∧
      let chain : List BabyBear.Ext8 :=
        CompPoly.Extension.Ext.ofBase BabyBear.twoAdicGenerators[TWO_ADICITY.val]! ::
          t.val.map (fun row => toExt BabyBear.ext8Params row)
      ∀ i (h : i + 1 < chain.length), chain[i + 1] ^ 2 = chain[i] := by
  obtain ⟨w, hw, -, hwW, -⟩ := Plonky3Lean.Lib.spec_imp_exists Ext8Params.W.spec
  obtain ⟨t, ht, hm⟩ := Ext8Params.TWO_ADIC_EXTENSION_GENERATORS.toExt_eq
  refine ⟨w, t, hw, hwW, ht, ?_⟩
  intro chain
  refine sq_chain_of_eq (L := chain) ?_ BabyBear.ext8TwoAdicGenerators_sq_succ
  show _ :: _ = _
  rw [hm, baby_bear.BabyBearParameters.TWO_ADICITY.eq_twoAdicity]

theorem Ext8Params.TWO_ADIC_EXTENSION_GENERATORS.order :
    ∃ w t e, Ext8Params.W = .ok w ∧ Spec.BabyBear.toField w = BabyBear.ext8Params.W ∧
      Ext8Params.TWO_ADIC_EXTENSION_GENERATORS = .ok t ∧
      Ext8Params.EXT_TWO_ADICITY = .ok e ∧ TWO_ADICITY.val + t.val.length = e.val ∧
      ∀ i (h : i < t.val.length),
        orderOf (toExt BabyBear.ext8Params t.val[i]) = 2 ^ (TWO_ADICITY.val + 1 + i) := by
  obtain ⟨w, hw, -, hwW, -⟩ := Plonky3Lean.Lib.spec_imp_exists Ext8Params.W.spec
  obtain ⟨t, ht, hm⟩ := Ext8Params.TWO_ADIC_EXTENSION_GENERATORS.toExt_eq
  refine ⟨w, t, 30#usize, hw, hwW, ht, ?_, ?_, ?_⟩
  · dsimp only
    unfold baby_bear.BabyBearParameters.Insts.P3_monty_31Data_traitsBinomialExtensionDataArrayArrayMontyField31BabyBearParameters838.EXT_TWO_ADICITY
    rfl
  · rw [show t.val.length = 3 from t.property,
      baby_bear.BabyBearParameters.TWO_ADICITY.eq_twoAdicity]
    rfl
  intro i hi
  have he : toExt BabyBear.ext8Params t.val[i] = BabyBear.ext8TwoAdicGenerators[i]'(by
      have : t.val.length = 3 := t.property
      rw [show BabyBear.ext8TwoAdicGenerators.length = 3 from rfl]; omega) := by
    simp only [← hm, List.getElem_map]
  rw [he, baby_bear.BabyBearParameters.TWO_ADICITY.eq_twoAdicity]
  exact BabyBear.ext8TwoAdicGenerators_order i _

end Plonky3Lean.Proofs.P3BabyBear
