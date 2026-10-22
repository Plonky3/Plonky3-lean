module

public import Plonky3Lean.Proofs.Field.KoalaBear.Constants
public import ToCompPoly.Fields.KoalaBear.Extension
public import ToCompPoly.Fields.KoalaBear.Quintic

@[expose] public section

/-!
# KoalaBear: the binomial extensions

`BinomialExtensionData<D>` for `D = 4, 8`, both with `W = 3`:
- `W`, with `X ^ D - W` irreducible;
- `DTH_ROOT = W ^ ((p - 1) / D)`;
- `EXT_TWO_ADICITY`, the two-adicity of `p ^ D - 1`;
- `TWO_ADIC_EXTENSION_GENERATORS`, read in `F[X] / (X ^ D - W)` through `Plonky3Lean.Spec.KoalaBear.toExt`.

Each is compared with CompPoly's specification of the extension (`KoalaBear.Ext4`, `Ext8`), staged in `ToCompPoly.Fields.KoalaBear.Extension`.

Each `EXT_GENERATOR` generates its extension's multiplicative group.

For `TrinomialQuinticData`: `X ^ 5 + X ^ 2 - 1` is irreducible, and `EXT_GENERATOR`, `EXT_TWO_ADICITY` and `FROBENIUS_COEFFS` are checked.
-/

open Aeneas Aeneas.Std CoreModels Polynomial
open p3_koala_bear
open Plonky3Lean.Spec.KoalaBear

namespace Plonky3Lean.Proofs.P3KoalaBear

theorem Ext4Params.W.spec :
    Ext4Params.W ⦃ w => Canonical w ∧ Spec.KoalaBear.toField w = 3 ∧
      Irreducible (X ^ 4 - C (Spec.KoalaBear.toField w)) ⦄ := by
  dsimp only
  unfold koala_bear.KoalaBearParameters.Insts.P3_monty_31Data_traitsBinomialExtensionDataArrayArrayMontyField31KoalaBearParameters424.W
  refine Aeneas.Std.WP.spec_mono (koala_bear.KoalaBear.new.toField 3#u32) ?_
  rintro w ⟨hc, hw⟩
  have hw' : Spec.KoalaBear.toField w = 3 := by rw [hw]; rfl
  refine ⟨hc, hw', ?_⟩
  rw [hw']
  exact KoalaBear.irreducible_ext4

theorem Ext4Params.EXT_TWO_ADICITY.spec :
    Ext4Params.EXT_TWO_ADICITY ⦃ e => 2 ^ e.val ∣ PRIME.val ^ 4 - 1 ∧
      ¬ 2 ^ (e.val + 1) ∣ PRIME.val ^ 4 - 1 ⦄ := by
  dsimp only
  rw [Aeneas.Std.WP.spec_ok, koala_bear.KoalaBearParameters.PRIME.eq_fieldSize]
  unfold koala_bear.KoalaBearParameters.Insts.P3_monty_31Data_traitsBinomialExtensionDataArrayArrayMontyField31KoalaBearParameters424.EXT_TWO_ADICITY
  exact KoalaBear.ext4TwoAdicity_spec

theorem Ext4Params.DTH_ROOT.spec :
    ∃ w r, Ext4Params.W = .ok w ∧ Ext4Params.DTH_ROOT = .ok r ∧ Canonical r ∧
      Spec.KoalaBear.toField r = Spec.KoalaBear.toField w ^ ((KoalaBear.fieldSize - 1) / 4) := by
  obtain ⟨w, hw, -, hw3, -⟩ := Aeneas.Std.WP.spec_imp_exists Ext4Params.W.spec
  have hd : Ext4Params.DTH_ROOT ⦃ r => Canonical r ∧
      Spec.KoalaBear.toField r = ((2113994754 : ℕ) : KoalaBear.Field) ⦄ := by
    dsimp only
    unfold koala_bear.KoalaBearParameters.Insts.P3_monty_31Data_traitsBinomialExtensionDataArrayArrayMontyField31KoalaBearParameters424.DTH_ROOT
    exact koala_bear.KoalaBear.new.toField _
  obtain ⟨r, hr, hrc, hrv⟩ := Aeneas.Std.WP.spec_imp_exists hd
  refine ⟨w, r, hw, hr, hrc, ?_⟩
  rw [hrv, hw3, show (3 : KoalaBear.Field) = ((3 : ℕ) : KoalaBear.Field) by norm_cast,
    ZMod.natCast_pow_eq_powMod 3 _]
  decide

theorem Ext8Params.W.spec :
    Ext8Params.W ⦃ w => Canonical w ∧ Spec.KoalaBear.toField w = 3 ∧
      Irreducible (X ^ 8 - C (Spec.KoalaBear.toField w)) ⦄ := by
  dsimp only
  unfold koala_bear.KoalaBearParameters.Insts.P3_monty_31Data_traitsBinomialExtensionDataArrayArrayMontyField31KoalaBearParameters838.W
  refine Aeneas.Std.WP.spec_mono (koala_bear.KoalaBear.new.toField 3#u32) ?_
  rintro w ⟨hc, hw⟩
  have hw' : Spec.KoalaBear.toField w = 3 := by rw [hw]; rfl
  refine ⟨hc, hw', ?_⟩
  rw [hw']
  exact KoalaBear.irreducible_ext8

theorem Ext8Params.EXT_TWO_ADICITY.spec :
    Ext8Params.EXT_TWO_ADICITY ⦃ e => 2 ^ e.val ∣ PRIME.val ^ 8 - 1 ∧
      ¬ 2 ^ (e.val + 1) ∣ PRIME.val ^ 8 - 1 ⦄ := by
  dsimp only
  rw [Aeneas.Std.WP.spec_ok, koala_bear.KoalaBearParameters.PRIME.eq_fieldSize]
  unfold koala_bear.KoalaBearParameters.Insts.P3_monty_31Data_traitsBinomialExtensionDataArrayArrayMontyField31KoalaBearParameters838.EXT_TWO_ADICITY
  exact KoalaBear.ext8TwoAdicity_spec

theorem Ext8Params.DTH_ROOT.spec :
    ∃ w r, Ext8Params.W = .ok w ∧ Ext8Params.DTH_ROOT = .ok r ∧ Canonical r ∧
      Spec.KoalaBear.toField r = Spec.KoalaBear.toField w ^ ((KoalaBear.fieldSize - 1) / 8) := by
  obtain ⟨w, hw, -, hw3, -⟩ := Aeneas.Std.WP.spec_imp_exists Ext8Params.W.spec
  have hd : Ext8Params.DTH_ROOT ⦃ r => Canonical r ∧
      Spec.KoalaBear.toField r = ((1748172362 : ℕ) : KoalaBear.Field) ⦄ := by
    dsimp only
    unfold koala_bear.KoalaBearParameters.Insts.P3_monty_31Data_traitsBinomialExtensionDataArrayArrayMontyField31KoalaBearParameters838.DTH_ROOT
    exact koala_bear.KoalaBear.new.toField _
  obtain ⟨r, hr, hrc, hrv⟩ := Aeneas.Std.WP.spec_imp_exists hd
  refine ⟨w, r, hw, hr, hrc, ?_⟩
  rw [hrv, hw3, show (3 : KoalaBear.Field) = ((3 : ℕ) : KoalaBear.Field) by norm_cast,
    ZMod.natCast_pow_eq_powMod 3 _]
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
      t.val.map (fun row => row.val.map Spec.KoalaBear.toField) =
        KoalaBear.ext4TwoAdicGeneratorCoeffs ⦄ := by
  dsimp only
  unfold koala_bear.KoalaBearParameters.Insts.P3_monty_31Data_traitsBinomialExtensionDataArrayArrayMontyField31KoalaBearParameters424.TWO_ADIC_EXTENSION_GENERATORS
  refine Aeneas.Std.WP.spec_mono (koala_bear.KoalaBear.new_2d_array.toField _) ?_
  rintro t ⟨-, ht⟩
  rw [ht]; decide

/-- Read in `F[X] / (X ^ 4 - 3)`, the model's table is CompPoly's
`ext4TwoAdicGenerators`. -/
theorem Ext4Params.TWO_ADIC_EXTENSION_GENERATORS.toExt_eq :
    ∃ t, Ext4Params.TWO_ADIC_EXTENSION_GENERATORS = .ok t ∧
      t.val.map (toExt 3) = KoalaBear.ext4TwoAdicGenerators := by
  obtain ⟨t, ht, hc⟩ := Aeneas.Std.WP.spec_imp_exists Ext4Params.TWO_ADIC_EXTENSION_GENERATORS.eq
  refine ⟨t, ht, ?_⟩
  unfold KoalaBear.ext4TwoAdicGenerators
  rw [← hc, List.map_map]
  rfl

theorem Ext4Params.TWO_ADIC_EXTENSION_GENERATORS.sq_succ :
    ∃ w t, Ext4Params.W = .ok w ∧ Ext4Params.TWO_ADIC_EXTENSION_GENERATORS = .ok t ∧
      let chain := AdjoinRoot.of _ KoalaBear.twoAdicGenerators[TWO_ADICITY.val]! ::
        t.val.map (toExt (Spec.KoalaBear.toField w))
      ∀ i (h : i + 1 < chain.length), chain[i + 1] ^ 2 = chain[i] := by
  obtain ⟨w, hw, -, hw3, -⟩ := Aeneas.Std.WP.spec_imp_exists Ext4Params.W.spec
  obtain ⟨t, ht, hm⟩ := Ext4Params.TWO_ADIC_EXTENSION_GENERATORS.toExt_eq
  refine ⟨w, t, hw, ht, ?_⟩
  have key : ∀ v : KoalaBear.Field, v = 3 →
      let chain := AdjoinRoot.of (X ^ (4#usize).val - C v)
        KoalaBear.twoAdicGenerators[TWO_ADICITY.val]! :: t.val.map (toExt v)
      ∀ i (h : i + 1 < chain.length), chain[i + 1] ^ 2 = chain[i] := by
    rintro v rfl chain
    refine sq_chain_of_eq (L := chain) ?_ KoalaBear.ext4TwoAdicGenerators_sq_succ
    show _ :: _ = _
    rw [hm, koala_bear.KoalaBearParameters.TWO_ADICITY.eq_twoAdicity]
    rfl
  exact key _ hw3

theorem Ext4Params.TWO_ADIC_EXTENSION_GENERATORS.order :
    ∃ w t e, Ext4Params.W = .ok w ∧ Ext4Params.TWO_ADIC_EXTENSION_GENERATORS = .ok t ∧
      Ext4Params.EXT_TWO_ADICITY = .ok e ∧ TWO_ADICITY.val + t.val.length = e.val ∧
      ∀ i (h : i < t.val.length),
        orderOf (toExt (Spec.KoalaBear.toField w) t.val[i]) =
          2 ^ (TWO_ADICITY.val + 1 + i) := by
  obtain ⟨w, hw, -, hw3, -⟩ := Aeneas.Std.WP.spec_imp_exists Ext4Params.W.spec
  obtain ⟨t, ht, hm⟩ := Ext4Params.TWO_ADIC_EXTENSION_GENERATORS.toExt_eq
  refine ⟨w, t, 26#usize, hw, ht, ?_, ?_, ?_⟩
  · dsimp only
    unfold koala_bear.KoalaBearParameters.Insts.P3_monty_31Data_traitsBinomialExtensionDataArrayArrayMontyField31KoalaBearParameters424.EXT_TWO_ADICITY
    rfl
  · rw [show t.val.length = 2 from t.property, koala_bear.KoalaBearParameters.TWO_ADICITY.eq_twoAdicity]
    rfl
  have key : ∀ v : KoalaBear.Field, v = 3 → ∀ i (h : i < t.val.length),
      orderOf (toExt v t.val[i]) = 2 ^ (TWO_ADICITY.val + 1 + i) := by
    rintro v rfl i hi
    have he : toExt 3 t.val[i] = KoalaBear.ext4TwoAdicGenerators[i]'(by
        have : t.val.length = 2 := t.property
        rw [show KoalaBear.ext4TwoAdicGenerators.length = 2 from rfl]; omega) := by
      simp only [← hm]
      exact (List.getElem_map _).symm
    rw [he, koala_bear.KoalaBearParameters.TWO_ADICITY.eq_twoAdicity]
    exact KoalaBear.ext4TwoAdicGenerators_order i _
  exact key _ hw3

/-- The degree-8 `TWO_ADIC_EXTENSION_GENERATORS` are CompPoly's
`ext8TwoAdicGeneratorCoeffs`, entry for entry. -/
theorem Ext8Params.TWO_ADIC_EXTENSION_GENERATORS.eq :
    Ext8Params.TWO_ADIC_EXTENSION_GENERATORS ⦃ t =>
      t.val.map (fun row => row.val.map Spec.KoalaBear.toField) =
        KoalaBear.ext8TwoAdicGeneratorCoeffs ⦄ := by
  dsimp only
  unfold koala_bear.KoalaBearParameters.Insts.P3_monty_31Data_traitsBinomialExtensionDataArrayArrayMontyField31KoalaBearParameters838.TWO_ADIC_EXTENSION_GENERATORS
  refine Aeneas.Std.WP.spec_mono (koala_bear.KoalaBear.new_2d_array.toField _) ?_
  rintro t ⟨-, ht⟩
  rw [ht]; decide

/-- Read in `F[X] / (X ^ 8 - 3)`, the model's table is CompPoly's
`ext8TwoAdicGenerators`. -/
theorem Ext8Params.TWO_ADIC_EXTENSION_GENERATORS.toExt_eq :
    ∃ t, Ext8Params.TWO_ADIC_EXTENSION_GENERATORS = .ok t ∧
      t.val.map (toExt 3) = KoalaBear.ext8TwoAdicGenerators := by
  obtain ⟨t, ht, hc⟩ := Aeneas.Std.WP.spec_imp_exists Ext8Params.TWO_ADIC_EXTENSION_GENERATORS.eq
  refine ⟨t, ht, ?_⟩
  unfold KoalaBear.ext8TwoAdicGenerators
  rw [← hc, List.map_map]
  rfl

theorem Ext8Params.TWO_ADIC_EXTENSION_GENERATORS.sq_succ :
    ∃ w t, Ext8Params.W = .ok w ∧ Ext8Params.TWO_ADIC_EXTENSION_GENERATORS = .ok t ∧
      let chain := AdjoinRoot.of _ KoalaBear.twoAdicGenerators[TWO_ADICITY.val]! ::
        t.val.map (toExt (Spec.KoalaBear.toField w))
      ∀ i (h : i + 1 < chain.length), chain[i + 1] ^ 2 = chain[i] := by
  obtain ⟨w, hw, -, hw3, -⟩ := Aeneas.Std.WP.spec_imp_exists Ext8Params.W.spec
  obtain ⟨t, ht, hm⟩ := Ext8Params.TWO_ADIC_EXTENSION_GENERATORS.toExt_eq
  refine ⟨w, t, hw, ht, ?_⟩
  have key : ∀ v : KoalaBear.Field, v = 3 →
      let chain := AdjoinRoot.of (X ^ (8#usize).val - C v)
        KoalaBear.twoAdicGenerators[TWO_ADICITY.val]! :: t.val.map (toExt v)
      ∀ i (h : i + 1 < chain.length), chain[i + 1] ^ 2 = chain[i] := by
    rintro v rfl chain
    refine sq_chain_of_eq (L := chain) ?_ KoalaBear.ext8TwoAdicGenerators_sq_succ
    show _ :: _ = _
    rw [hm, koala_bear.KoalaBearParameters.TWO_ADICITY.eq_twoAdicity]
    rfl
  exact key _ hw3

theorem Ext8Params.TWO_ADIC_EXTENSION_GENERATORS.order :
    ∃ w t e, Ext8Params.W = .ok w ∧ Ext8Params.TWO_ADIC_EXTENSION_GENERATORS = .ok t ∧
      Ext8Params.EXT_TWO_ADICITY = .ok e ∧ TWO_ADICITY.val + t.val.length = e.val ∧
      ∀ i (h : i < t.val.length),
        orderOf (toExt (Spec.KoalaBear.toField w) t.val[i]) =
          2 ^ (TWO_ADICITY.val + 1 + i) := by
  obtain ⟨w, hw, -, hw3, -⟩ := Aeneas.Std.WP.spec_imp_exists Ext8Params.W.spec
  obtain ⟨t, ht, hm⟩ := Ext8Params.TWO_ADIC_EXTENSION_GENERATORS.toExt_eq
  refine ⟨w, t, 27#usize, hw, ht, ?_, ?_, ?_⟩
  · dsimp only
    unfold koala_bear.KoalaBearParameters.Insts.P3_monty_31Data_traitsBinomialExtensionDataArrayArrayMontyField31KoalaBearParameters838.EXT_TWO_ADICITY
    rfl
  · rw [show t.val.length = 3 from t.property, koala_bear.KoalaBearParameters.TWO_ADICITY.eq_twoAdicity]
    rfl
  have key : ∀ v : KoalaBear.Field, v = 3 → ∀ i (h : i < t.val.length),
      orderOf (toExt v t.val[i]) = 2 ^ (TWO_ADICITY.val + 1 + i) := by
    rintro v rfl i hi
    have he : toExt 3 t.val[i] = KoalaBear.ext8TwoAdicGenerators[i]'(by
        have : t.val.length = 3 := t.property
        rw [show KoalaBear.ext8TwoAdicGenerators.length = 3 from rfl]; omega) := by
      simp only [← hm]
      exact (List.getElem_map _).symm
    rw [he, koala_bear.KoalaBearParameters.TWO_ADICITY.eq_twoAdicity]
    exact KoalaBear.ext8TwoAdicGenerators_order i _
  exact key _ hw3

/-! ## `TrinomialQuinticData` -/

/-- The quintic extension's `EXT_TWO_ADICITY` is the two-adicity of `p ^ 5 - 1`, which is `TWO_ADICITY`. -/
theorem QuinticParams.EXT_TWO_ADICITY.spec :
    QuinticParams.EXT_TWO_ADICITY ⦃ e => e.val = TWO_ADICITY.val ∧
      2 ^ e.val ∣ PRIME.val ^ 5 - 1 ∧ ¬ 2 ^ (e.val + 1) ∣ PRIME.val ^ 5 - 1 ⦄ := by
  dsimp only
  rw [WP.spec_ok, koala_bear.KoalaBearParameters.PRIME.eq_fieldSize,
    koala_bear.KoalaBearParameters.TWO_ADICITY.eq_twoAdicity]
  unfold koala_bear.KoalaBearParameters.Insts.P3_monty_31Data_traitsTrinomialQuinticDataArrayArrayMontyField31KoalaBearParameters50.EXT_TWO_ADICITY
  exact ⟨rfl, KoalaBear.ext5TwoAdicity_spec⟩

/-! ## The multiplicative generators -/

theorem Ext4Params.EXT_GENERATOR.order :
    ∃ w g, Ext4Params.W = .ok w ∧ Ext4Params.EXT_GENERATOR = .ok g ∧
      orderOf (toExt (Spec.KoalaBear.toField w) g) = KoalaBear.fieldSize ^ 4 - 1 := by
  obtain ⟨w, hw, -, hw3, -⟩ := WP.spec_imp_exists Ext4Params.W.spec
  have hg : Ext4Params.EXT_GENERATOR ⦃ g =>
      g.val.map Spec.KoalaBear.toField = KoalaBear.ext4GeneratorCoeffs ⦄ := by
    dsimp only
    unfold koala_bear.KoalaBearParameters.Insts.P3_monty_31Data_traitsBinomialExtensionDataArrayArrayMontyField31KoalaBearParameters424.EXT_GENERATOR
    refine WP.spec_mono (koala_bear.KoalaBear.new_array.toField _) ?_
    rintro g ⟨-, hg⟩
    rw [hg]; decide
  obtain ⟨g, hg', hgv⟩ := WP.spec_imp_exists hg
  refine ⟨w, g, hw, hg', ?_⟩
  have key : ∀ v : KoalaBear.Field, v = 3 →
      orderOf (toExt v g) = KoalaBear.fieldSize ^ 4 - 1 := by
    rintro v rfl
    unfold toExt
    rw [hgv]
    exact KoalaBear.orderOf_ext4Generator
  exact key _ hw3

theorem Ext8Params.EXT_GENERATOR.order :
    ∃ w g, Ext8Params.W = .ok w ∧ Ext8Params.EXT_GENERATOR = .ok g ∧
      orderOf (toExt (Spec.KoalaBear.toField w) g) = KoalaBear.fieldSize ^ 8 - 1 := by
  obtain ⟨w, hw, -, hw3, -⟩ := WP.spec_imp_exists Ext8Params.W.spec
  have hg : Ext8Params.EXT_GENERATOR ⦃ g =>
      g.val.map Spec.KoalaBear.toField = KoalaBear.ext8GeneratorCoeffs ⦄ := by
    dsimp only
    unfold koala_bear.KoalaBearParameters.Insts.P3_monty_31Data_traitsBinomialExtensionDataArrayArrayMontyField31KoalaBearParameters838.EXT_GENERATOR
    refine WP.spec_mono (koala_bear.KoalaBear.new_array.toField _) ?_
    rintro g ⟨-, hg⟩
    rw [hg]; decide
  obtain ⟨g, hg', hgv⟩ := WP.spec_imp_exists hg
  refine ⟨w, g, hw, hg', ?_⟩
  have key : ∀ v : KoalaBear.Field, v = 3 →
      orderOf (toExt v g) = KoalaBear.fieldSize ^ 8 - 1 := by
    rintro v rfl
    unfold toExt
    rw [hgv]
    exact KoalaBear.orderOf_ext8Generator
  exact key _ hw3

theorem QuinticParams.EXT_GENERATOR.order :
    QuinticParams.EXT_GENERATOR ⦃ g => orderOf (toQuintic g) = KoalaBear.fieldSize ^ 5 - 1 ⦄ := by
  dsimp only
  unfold koala_bear.KoalaBearParameters.Insts.P3_monty_31Data_traitsTrinomialQuinticDataArrayArrayMontyField31KoalaBearParameters50.EXT_GENERATOR
  refine WP.spec_mono (koala_bear.KoalaBear.new_array.toField _) ?_
  rintro g ⟨-, hg⟩
  have hc : g.val.map Spec.KoalaBear.toField = KoalaBear.quinticGeneratorCoeffs := by
    rw [hg]; decide
  unfold toQuintic
  rw [hc]
  exact KoalaBear.orderOf_quinticGenerator

/-- `FROBENIUS_COEFFS[k]` stands for `X ^ ((k + 1) · p)` in `F[X] / (X ^ 5 + X ^ 2 - 1)`. -/
theorem QuinticParams.FROBENIUS_COEFFS.spec :
    QuinticParams.FROBENIUS_COEFFS ⦃ t => ∀ k (h : k < t.val.length),
      toQuintic t.val[k] = AdjoinRoot.root KoalaBear.quinticPoly ^ ((k + 1) * KoalaBear.fieldSize) ⦄ := by
  dsimp only
  unfold koala_bear.KoalaBearParameters.Insts.P3_monty_31Data_traitsTrinomialQuinticDataArrayArrayMontyField31KoalaBearParameters50.FROBENIUS_COEFFS
  refine WP.spec_mono (koala_bear.KoalaBear.new_2d_array.toField _) ?_
  rintro t ⟨-, ht⟩
  have hc : t.val.map (fun row => row.val.map Spec.KoalaBear.toField) =
      KoalaBear.quinticFrobeniusCoeffs := by
    rw [ht]; decide
  intro k hk
  have hk' : k < KoalaBear.quinticFrobeniusCoeffs.length := by
    rw [← hc, List.length_map]; exact hk
  rw [← KoalaBear.quinticFrobeniusCoeffs_spec k hk']
  unfold toQuintic
  congr 1
  simp only [← hc, List.getElem_map]

end Plonky3Lean.Proofs.P3KoalaBear
