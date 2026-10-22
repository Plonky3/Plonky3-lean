import Plonky3Lean.Lib.Irreducible
import Plonky3Lean.Proofs.Field.BabyBear.Constants

/-!
# BabyBear: the binomial extensions

`BinomialExtensionData<D>` for `D = 4, 5, 8`: `W`, with `X ^ D - W` irreducible;
`DTH_ROOT = W ^ ((p - 1) / D)`; `EXT_TWO_ADICITY`, the two-adicity of
`p ^ D - 1`; and `TWO_ADIC_EXTENSION_GENERATORS`, read in `F[X] / (X ^ D - W)`
through `Plonky3Lean.Spec.BabyBear.toExt`.
-/

open Aeneas Aeneas.Std CoreModels Polynomial
open p3_baby_bear
open Plonky3Lean.Spec.BabyBear
open Plonky3Lean.Lib

namespace Plonky3Lean.Proofs.BabyBear

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
  refine X_pow_sub_C_irreducible_of_gcd (ℓ := 2) (by norm_num) (by decide) ?_ ?_
  · exact_mod_cast pow_ne_one_of_powMod 11 (by unfold BabyBear.fieldSize; norm_num) (by decide)
  · unfold BabyBear.fieldSize; decide

theorem Ext4Params.EXT_TWO_ADICITY.spec :
    Ext4Params.EXT_TWO_ADICITY ⦃ e => 2 ^ e.val ∣ PRIME.val ^ 4 - 1 ∧
      ¬ 2 ^ (e.val + 1) ∣ PRIME.val ^ 4 - 1 ⦄ := by
  dsimp only
  rw [Aeneas.Std.WP.spec_ok, baby_bear.BabyBearParameters.PRIME.eq_fieldSize]
  unfold baby_bear.BabyBearParameters.Insts.P3_monty_31Data_traitsBinomialExtensionDataArrayArrayMontyField31BabyBearParameters424.EXT_TWO_ADICITY
  unfold BabyBear.fieldSize
  decide

theorem Ext4Params.DTH_ROOT.spec :
    ∃ w r, Ext4Params.W = .ok w ∧ Ext4Params.DTH_ROOT = .ok r ∧ Canonical r ∧
      Spec.BabyBear.toField r = Spec.BabyBear.toField w ^ ((BabyBear.fieldSize - 1) / 4) := by
  obtain ⟨w, hw, -, hw11, -⟩ := Aeneas.Std.WP.spec_imp_exists Ext4Params.W.spec
  have hd : Ext4Params.DTH_ROOT ⦃ r => Canonical r ∧
      Spec.BabyBear.toField r = ((1728404513 : ℕ) : BabyBear.Field) ⦄ := by
    dsimp only
    unfold baby_bear.BabyBearParameters.Insts.P3_monty_31Data_traitsBinomialExtensionDataArrayArrayMontyField31BabyBearParameters424.DTH_ROOT
    exact baby_bear.BabyBear.new.toField _
  obtain ⟨r, hr, hrc, hrv⟩ := Aeneas.Std.WP.spec_imp_exists hd
  refine ⟨w, r, hw, hr, hrc, ?_⟩
  rw [hrv, hw11, show (11 : BabyBear.Field) = ((11 : ℕ) : BabyBear.Field) by norm_cast,
    zmod_pow_eq_powMod 11 _ (by unfold BabyBear.fieldSize; norm_num)]
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
  refine X_pow_sub_C_irreducible_of_gcd (ℓ := 5) (by norm_num) (by decide) ?_ ?_
  · exact_mod_cast pow_ne_one_of_powMod 2 (by unfold BabyBear.fieldSize; norm_num) (by decide)
  · unfold BabyBear.fieldSize; decide

theorem Ext5Params.EXT_TWO_ADICITY.spec :
    Ext5Params.EXT_TWO_ADICITY ⦃ e => 2 ^ e.val ∣ PRIME.val ^ 5 - 1 ∧
      ¬ 2 ^ (e.val + 1) ∣ PRIME.val ^ 5 - 1 ⦄ := by
  dsimp only
  rw [Aeneas.Std.WP.spec_ok, baby_bear.BabyBearParameters.PRIME.eq_fieldSize]
  unfold baby_bear.BabyBearParameters.Insts.P3_monty_31Data_traitsBinomialExtensionDataArrayArrayMontyField31BabyBearParameters505.EXT_TWO_ADICITY
  unfold BabyBear.fieldSize
  decide

theorem Ext5Params.DTH_ROOT.spec :
    ∃ w r, Ext5Params.W = .ok w ∧ Ext5Params.DTH_ROOT = .ok r ∧ Canonical r ∧
      Spec.BabyBear.toField r = Spec.BabyBear.toField w ^ ((BabyBear.fieldSize - 1) / 5) := by
  obtain ⟨w, hw, -, hw11, -⟩ := Aeneas.Std.WP.spec_imp_exists Ext5Params.W.spec
  have hd : Ext5Params.DTH_ROOT ⦃ r => Canonical r ∧
      Spec.BabyBear.toField r = ((815036133 : ℕ) : BabyBear.Field) ⦄ := by
    dsimp only
    unfold baby_bear.BabyBearParameters.Insts.P3_monty_31Data_traitsBinomialExtensionDataArrayArrayMontyField31BabyBearParameters505.DTH_ROOT
    exact baby_bear.BabyBear.new.toField _
  obtain ⟨r, hr, hrc, hrv⟩ := Aeneas.Std.WP.spec_imp_exists hd
  refine ⟨w, r, hw, hr, hrc, ?_⟩
  rw [hrv, hw11, show (2 : BabyBear.Field) = ((2 : ℕ) : BabyBear.Field) by norm_cast,
    zmod_pow_eq_powMod 2 _ (by unfold BabyBear.fieldSize; norm_num)]
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
  refine X_pow_sub_C_irreducible_of_gcd (ℓ := 2) (by norm_num) (by decide) ?_ ?_
  · exact_mod_cast pow_ne_one_of_powMod 11 (by unfold BabyBear.fieldSize; norm_num) (by decide)
  · unfold BabyBear.fieldSize; decide

theorem Ext8Params.EXT_TWO_ADICITY.spec :
    Ext8Params.EXT_TWO_ADICITY ⦃ e => 2 ^ e.val ∣ PRIME.val ^ 8 - 1 ∧
      ¬ 2 ^ (e.val + 1) ∣ PRIME.val ^ 8 - 1 ⦄ := by
  dsimp only
  rw [Aeneas.Std.WP.spec_ok, baby_bear.BabyBearParameters.PRIME.eq_fieldSize]
  unfold baby_bear.BabyBearParameters.Insts.P3_monty_31Data_traitsBinomialExtensionDataArrayArrayMontyField31BabyBearParameters838.EXT_TWO_ADICITY
  unfold BabyBear.fieldSize
  decide

theorem Ext8Params.DTH_ROOT.spec :
    ∃ w r, Ext8Params.W = .ok w ∧ Ext8Params.DTH_ROOT = .ok r ∧ Canonical r ∧
      Spec.BabyBear.toField r = Spec.BabyBear.toField w ^ ((BabyBear.fieldSize - 1) / 8) := by
  obtain ⟨w, hw, -, hw11, -⟩ := Aeneas.Std.WP.spec_imp_exists Ext8Params.W.spec
  have hd : Ext8Params.DTH_ROOT ⦃ r => Canonical r ∧
      Spec.BabyBear.toField r = ((420899707 : ℕ) : BabyBear.Field) ⦄ := by
    dsimp only
    unfold baby_bear.BabyBearParameters.Insts.P3_monty_31Data_traitsBinomialExtensionDataArrayArrayMontyField31BabyBearParameters838.DTH_ROOT
    exact baby_bear.BabyBear.new.toField _
  obtain ⟨r, hr, hrc, hrv⟩ := Aeneas.Std.WP.spec_imp_exists hd
  refine ⟨w, r, hw, hr, hrc, ?_⟩
  rw [hrv, hw11, show (11 : BabyBear.Field) = ((11 : ℕ) : BabyBear.Field) by norm_cast,
    zmod_pow_eq_powMod 11 _ (by unfold BabyBear.fieldSize; norm_num)]
  decide

/-! ## Elements of the extensions -/

theorem root_pow_eq (D : ℕ) (w : BabyBear.Field) :
    AdjoinRoot.root (X ^ D - C w) ^ D = AdjoinRoot.of _ w := by
  have h := AdjoinRoot.eval₂_root (X ^ D - C w)
  simp only [eval₂_sub, eval₂_X_pow, eval₂_C] at h
  exact sub_eq_zero.mp h

theorem toExt_eq_of_map {D : Usize} {w : BabyBear.Field} {row : Array Element D}
    {L : List BabyBear.Field} (h : row.val.map Spec.BabyBear.toField = L) :
    toExt w row = AdjoinRoot.mk _ ((L.mapIdx fun j a => C a * X ^ j).sum) := by
  unfold toExt; rw [h]

/-- `TWO_ADIC_GENERATORS[27]`, mapped into an extension, keeps its order `2 ^ 27`. -/
theorem orderOf_of_twoAdicGenerator_27 {D : ℕ} (hD : 0 < D) (w : BabyBear.Field) :
    orderOf (AdjoinRoot.of (X ^ D - C w) (0x1A427A41 : BabyBear.Field)) = 2 ^ 27 := by
  have hinj : Function.Injective (AdjoinRoot.of (X ^ D - C w)) :=
    AdjoinRoot.of.injective_of_degree_ne_zero
      (by rw [degree_X_pow_sub_C hD]; exact_mod_cast hD.ne')
  have h1 := orderOf_injective (AdjoinRoot.of (X ^ D - C w)).toMonoidHom hinj
    (0x1A427A41 : BabyBear.Field)
  simp only [RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe] at h1
  rw [h1]
  have := BabyBear.twoAdicGenerators_order ⟨27, by decide⟩
  simpa [BabyBear.twoAdicGenerators] using this

/-- The last entry of CompPoly's two-adic generator table, `TWO_ADIC_GENERATORS[27]`. -/
theorem twoAdicGenerators_twoAdicity :
    BabyBear.twoAdicGenerators[TWO_ADICITY.val]! = 0x1A427A41 := by
  rw [baby_bear.BabyBearParameters.TWO_ADICITY.eq_twoAdicity]
  rfl

/-- The degree-4 `TWO_ADIC_EXTENSION_GENERATORS`, read in `F[X] / (X ^ 4 - 11)`,
form the squaring chain above `TWO_ADIC_GENERATORS[27]`. -/
theorem Ext4Params.TWO_ADIC_EXTENSION_GENERATORS.chain :
    ∃ t, Ext4Params.TWO_ADIC_EXTENSION_GENERATORS = .ok t ∧ ∃ h : t.val.length = 2,
      ∀ w : BabyBear.Field, w = 11 →
        toExt w (t.val[0]'(by omega)) ^ 2 = AdjoinRoot.of _ 0x1A427A41 ∧
        toExt w (t.val[1]'(by omega)) ^ 2 = toExt w (t.val[0]'(by omega)) := by
  have hg : Ext4Params.TWO_ADIC_EXTENSION_GENERATORS ⦃ t =>
      t.val.map (fun row => row.val.map Spec.BabyBear.toField) =
        [[0, 0, 1996171314, 0], [0, 0, 0, 124907976]] ⦄ := by
    dsimp only
    unfold baby_bear.BabyBearParameters.Insts.P3_monty_31Data_traitsBinomialExtensionDataArrayArrayMontyField31BabyBearParameters424.TWO_ADIC_EXTENSION_GENERATORS
    refine Aeneas.Std.WP.spec_mono (baby_bear.BabyBear.new_2d_array.toField _) ?_
    rintro t ⟨-, ht⟩
    rw [ht]; decide
  obtain ⟨t, ht, htv⟩ := Aeneas.Std.WP.spec_imp_exists hg
  have hlen : t.val.length = 2 := t.property
  have hrow : ∀ j (hj : j < t.val.length), t.val[j].val.map Spec.BabyBear.toField =
      [[0, 0, 1996171314, 0], [0, 0, 0, 124907976]][j]'(by simp; omega) := by
    intro j hj; simp only [← htv, List.getElem_map]
  have hx0 : toExt 11 (t.val[0]'(by omega)) =
      AdjoinRoot.of _ 1996171314 * AdjoinRoot.root _ ^ 2 := by
    rw [toExt_eq_of_map (hrow 0 (by omega))]
    simp [List.mapIdx_cons, AdjoinRoot.mk_C, AdjoinRoot.mk_X]
  have hx1 : toExt 11 (t.val[1]'(by omega)) =
      AdjoinRoot.of _ 124907976 * AdjoinRoot.root _ ^ 3 := by
    rw [toExt_eq_of_map (hrow 1 (by omega))]
    simp [List.mapIdx_cons, AdjoinRoot.mk_C, AdjoinRoot.mk_X]
  have hr := root_pow_eq (4#usize).val (11 : BabyBear.Field)
  refine ⟨t, ht, hlen, ?_⟩
  rintro w rfl
  refine ⟨?_, ?_⟩
  · rw [hx0, mul_pow, ← pow_mul, show 2 * 2 = (4#usize).val by simp, hr, ← map_pow, ← map_mul]
    congr 1
  · rw [hx1, hx0, mul_pow, ← pow_mul, show 3 * 2 = (4#usize).val + 2 by simp, pow_add, hr, ← mul_assoc,
      ← map_pow, ← map_mul]
    congr 2

theorem Ext4Params.TWO_ADIC_EXTENSION_GENERATORS.sq_succ :
    ∃ w t, Ext4Params.W = .ok w ∧ Ext4Params.TWO_ADIC_EXTENSION_GENERATORS = .ok t ∧
      let chain := AdjoinRoot.of _ BabyBear.twoAdicGenerators[TWO_ADICITY.val]! ::
        t.val.map (toExt (Spec.BabyBear.toField w))
      ∀ i (h : i + 1 < chain.length), chain[i + 1] ^ 2 = chain[i] := by
  obtain ⟨w, hw, -, hw11, -⟩ := Aeneas.Std.WP.spec_imp_exists Ext4Params.W.spec
  obtain ⟨t, ht, hlen, hc⟩ := Ext4Params.TWO_ADIC_EXTENSION_GENERATORS.chain
  obtain ⟨h0, h1⟩ := hc _ hw11
  refine ⟨w, t, hw, ht, ?_⟩
  intro chain i hi
  have hi' : i < 2 := by simp only [chain, List.length_cons, List.length_map, hlen] at hi; omega
  interval_cases i <;>
    simp only [chain, List.getElem_cons_succ, List.getElem_cons_zero, List.getElem_map]
  · rw [twoAdicGenerators_twoAdicity]; exact h0
  · exact h1

theorem Ext4Params.TWO_ADIC_EXTENSION_GENERATORS.order :
    ∃ w t e, Ext4Params.W = .ok w ∧ Ext4Params.TWO_ADIC_EXTENSION_GENERATORS = .ok t ∧
      Ext4Params.EXT_TWO_ADICITY = .ok e ∧ TWO_ADICITY.val + t.val.length = e.val ∧
      ∀ i (h : i < t.val.length),
        orderOf (toExt (Spec.BabyBear.toField w) t.val[i]) =
          2 ^ (TWO_ADICITY.val + 1 + i) := by
  obtain ⟨w, hw, -, hw11, -⟩ := Aeneas.Std.WP.spec_imp_exists Ext4Params.W.spec
  obtain ⟨t, ht, hlen, hc⟩ := Ext4Params.TWO_ADIC_EXTENSION_GENERATORS.chain
  obtain ⟨hs0, hs1⟩ := hc _ hw11
  refine ⟨w, t, 29#usize, hw, ht, ?_, ?_, ?_⟩
  · dsimp only
    unfold baby_bear.BabyBearParameters.Insts.P3_monty_31Data_traitsBinomialExtensionDataArrayArrayMontyField31BabyBearParameters424.EXT_TWO_ADICITY
    rfl
  · rw [hlen, baby_bear.BabyBearParameters.TWO_ADICITY.eq_twoAdicity]; rfl
  intro i hi
  rw [baby_bear.BabyBearParameters.TWO_ADICITY.eq_twoAdicity]
  have h0 := orderOf_eq_two_pow_succ_of_sq (k := 26) hs0
    (orderOf_of_twoAdicGenerator_27 (by simp) _)
  have h1 := orderOf_eq_two_pow_succ_of_sq (k := 27) hs1 h0
  rw [hlen] at hi
  interval_cases i
  · exact h0
  · exact h1

/-- The degree-8 `TWO_ADIC_EXTENSION_GENERATORS`, read in `F[X] / (X ^ 8 - 11)`,
form the squaring chain above `TWO_ADIC_GENERATORS[27]`. -/
theorem Ext8Params.TWO_ADIC_EXTENSION_GENERATORS.chain :
    ∃ t, Ext8Params.TWO_ADIC_EXTENSION_GENERATORS = .ok t ∧ ∃ h : t.val.length = 3,
      ∀ w : BabyBear.Field, w = 11 →
        toExt w (t.val[0]'(by omega)) ^ 2 = AdjoinRoot.of _ 0x1A427A41 ∧
        toExt w (t.val[1]'(by omega)) ^ 2 = toExt w (t.val[0]'(by omega)) ∧
        toExt w (t.val[2]'(by omega)) ^ 2 = toExt w (t.val[1]'(by omega)) := by
  have hg : Ext8Params.TWO_ADIC_EXTENSION_GENERATORS ⦃ t =>
      t.val.map (fun row => row.val.map Spec.BabyBear.toField) =
        [[0, 0, 0, 0, 1996171314, 0, 0, 0], [0, 0, 0, 0, 0, 0, 124907976, 0],
          [0, 0, 0, 518392818, 0, 0, 0, 0]] ⦄ := by
    dsimp only
    unfold baby_bear.BabyBearParameters.Insts.P3_monty_31Data_traitsBinomialExtensionDataArrayArrayMontyField31BabyBearParameters838.TWO_ADIC_EXTENSION_GENERATORS
    refine Aeneas.Std.WP.spec_mono (baby_bear.BabyBear.new_2d_array.toField _) ?_
    rintro t ⟨-, ht⟩
    rw [ht]; decide
  obtain ⟨t, ht, htv⟩ := Aeneas.Std.WP.spec_imp_exists hg
  have hlen : t.val.length = 3 := t.property
  have hrow : ∀ j (hj : j < t.val.length), t.val[j].val.map Spec.BabyBear.toField =
      [[0, 0, 0, 0, 1996171314, 0, 0, 0], [0, 0, 0, 0, 0, 0, 124907976, 0],
        [0, 0, 0, 518392818, 0, 0, 0, 0]][j]'(by simp; omega) := by
    intro j hj; simp only [← htv, List.getElem_map]
  have hx0 : toExt 11 (t.val[0]'(by omega)) =
      AdjoinRoot.of _ 1996171314 * AdjoinRoot.root _ ^ 4 := by
    rw [toExt_eq_of_map (hrow 0 (by omega))]
    simp [List.mapIdx_cons, AdjoinRoot.mk_C, AdjoinRoot.mk_X]
  have hx1 : toExt 11 (t.val[1]'(by omega)) =
      AdjoinRoot.of _ 124907976 * AdjoinRoot.root _ ^ 6 := by
    rw [toExt_eq_of_map (hrow 1 (by omega))]
    simp [List.mapIdx_cons, AdjoinRoot.mk_C, AdjoinRoot.mk_X]
  have hx2 : toExt 11 (t.val[2]'(by omega)) =
      AdjoinRoot.of _ 518392818 * AdjoinRoot.root _ ^ 3 := by
    rw [toExt_eq_of_map (hrow 2 (by omega))]
    simp [List.mapIdx_cons, AdjoinRoot.mk_C, AdjoinRoot.mk_X]
  have hr := root_pow_eq (8#usize).val (11 : BabyBear.Field)
  refine ⟨t, ht, hlen, ?_⟩
  rintro w rfl
  refine ⟨?_, ?_, ?_⟩
  · rw [hx0, mul_pow, ← pow_mul, show 4 * 2 = (8#usize).val by simp, hr, ← map_pow, ← map_mul]
    congr 1
  · rw [hx1, hx0, mul_pow, ← pow_mul, show 6 * 2 = (8#usize).val + 4 by simp, pow_add, hr, ← mul_assoc,
      ← map_pow, ← map_mul]
    congr 2
  · rw [hx2, hx1, mul_pow, ← pow_mul, ← map_pow]
    congr 2

theorem Ext8Params.TWO_ADIC_EXTENSION_GENERATORS.sq_succ :
    ∃ w t, Ext8Params.W = .ok w ∧ Ext8Params.TWO_ADIC_EXTENSION_GENERATORS = .ok t ∧
      let chain := AdjoinRoot.of _ BabyBear.twoAdicGenerators[TWO_ADICITY.val]! ::
        t.val.map (toExt (Spec.BabyBear.toField w))
      ∀ i (h : i + 1 < chain.length), chain[i + 1] ^ 2 = chain[i] := by
  obtain ⟨w, hw, -, hw11, -⟩ := Aeneas.Std.WP.spec_imp_exists Ext8Params.W.spec
  obtain ⟨t, ht, hlen, hc⟩ := Ext8Params.TWO_ADIC_EXTENSION_GENERATORS.chain
  obtain ⟨h0, h1, h2⟩ := hc _ hw11
  refine ⟨w, t, hw, ht, ?_⟩
  intro chain i hi
  have hi' : i < 3 := by simp only [chain, List.length_cons, List.length_map, hlen] at hi; omega
  interval_cases i <;>
    simp only [chain, List.getElem_cons_succ, List.getElem_cons_zero, List.getElem_map]
  · rw [twoAdicGenerators_twoAdicity]; exact h0
  · exact h1
  · exact h2

theorem Ext8Params.TWO_ADIC_EXTENSION_GENERATORS.order :
    ∃ w t e, Ext8Params.W = .ok w ∧ Ext8Params.TWO_ADIC_EXTENSION_GENERATORS = .ok t ∧
      Ext8Params.EXT_TWO_ADICITY = .ok e ∧ TWO_ADICITY.val + t.val.length = e.val ∧
      ∀ i (h : i < t.val.length),
        orderOf (toExt (Spec.BabyBear.toField w) t.val[i]) =
          2 ^ (TWO_ADICITY.val + 1 + i) := by
  obtain ⟨w, hw, -, hw11, -⟩ := Aeneas.Std.WP.spec_imp_exists Ext8Params.W.spec
  obtain ⟨t, ht, hlen, hc⟩ := Ext8Params.TWO_ADIC_EXTENSION_GENERATORS.chain
  obtain ⟨hs0, hs1, hs2⟩ := hc _ hw11
  refine ⟨w, t, 30#usize, hw, ht, ?_, ?_, ?_⟩
  · dsimp only
    unfold baby_bear.BabyBearParameters.Insts.P3_monty_31Data_traitsBinomialExtensionDataArrayArrayMontyField31BabyBearParameters838.EXT_TWO_ADICITY
    rfl
  · rw [hlen, baby_bear.BabyBearParameters.TWO_ADICITY.eq_twoAdicity]; rfl
  intro i hi
  rw [baby_bear.BabyBearParameters.TWO_ADICITY.eq_twoAdicity]
  have h0 := orderOf_eq_two_pow_succ_of_sq (k := 26) hs0
    (orderOf_of_twoAdicGenerator_27 (by simp) _)
  have h1 := orderOf_eq_two_pow_succ_of_sq (k := 27) hs1 h0
  have h2 := orderOf_eq_two_pow_succ_of_sq (k := 28) hs2 h1
  rw [hlen] at hi
  interval_cases i
  · exact h0
  · exact h1
  · exact h2

end Plonky3Lean.Proofs.BabyBear
