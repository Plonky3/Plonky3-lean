module

public import Plonky3Lean.Proofs.Field.Binary.BasisConvert
public import Plonky3Lean.Proofs.Field.Binary.PolyField

@[expose] public section

/-!
# GHASH arithmetic that goes through the tower

`Ghash128` inverts by converting to the tower, inverting there and converting back
(`ghash_invert_or_zero_spec`). Its division and the operators that take a tower operand are
built on that and on the conversions `N` and `N⁻¹`.
-/

open Aeneas Aeneas.Std CoreModels Polynomial
open ConcreteBinaryTower ConcreteBinaryTower.Coordinates
open p3_binary_field BinaryField BF128Ghash
open Plonky3Lean.Lib Plonky3Lean.Spec.BinaryField

namespace Plonky3Lean.Proofs.Binary

/-! ## The tower inside CompPoly's GHASH field -/

/-- `GF(2)[x] / (x^128 + x^7 + x^2 + x + 1)` is CompPoly's GHASH quotient. -/
noncomputable def ghashIso : AdjoinRoot (modPoly 128 135) ≃ₐ[ZMod 2] AdjoinRoot ghashPoly :=
  AdjoinRoot.algEquivOfEq (ZMod 2) _ _ modPoly_128_ghash

theorem ghashIso_mk (p : (ZMod 2)[X]) :
    ghashIso (AdjoinRoot.mk (modPoly 128 135) p) = AdjoinRoot.mk ghashPoly p := by
  simp only [ghashIso, AdjoinRoot.coe_algEquivOfEq, AdjoinRoot.algHomOfDvd,
    AdjoinRoot.mapAlgHom, AlgHom.coe_mk]
  have h : (AdjoinRoot.map (RingHom.id (ZMod 2)) (modPoly 128 135) ghashPoly (by
      rw [Polynomial.map_id, modPoly_128_ghash])).comp (AdjoinRoot.mk (modPoly 128 135)) =
      AdjoinRoot.mk ghashPoly := by
    apply Polynomial.ringHom_ext
    · intro r
      simp [AdjoinRoot.mk_C]
    · simp [AdjoinRoot.mk_X]
  exact congrArg (fun φ => φ p) h

/-- The basis change `N`, as a field embedding of the tower's `GF(2^128)` into CompPoly's GHASH
field. -/
noncomputable def towerToGhash : ConcreteBTField 7 →+* PolyQuot :=
  ghashIso.toRingEquiv.toRingHom.comp N128

theorem towerToGhash_apply (x : ConcreteBTField 7) : towerToGhash x = ghashIso (N128 x) := rfl

theorem towerToGhash_injective : Function.Injective towerToGhash :=
  ghashIso.injective.comp N128_injective

/-- `From<BinaryField128> for Ghash128` is `towerToGhash`. -/
theorem ghash128_from_bf128_toQuot (t : tower.BinaryField128) :
    ghash.Ghash128.Insts.CoreConvertFromBinaryField128.from t ⦃ x =>
      toQuot (ghash x) = towerToGhash (towerOf 7 t) ⦄ := by
  apply WP.spec_mono (ghash_from_bf128_spec t)
  intro x hx
  rw [towerToGhash_apply, ← hx, ghashIso_mk, toQuot_eq_mk]

/-- `From<Ghash128> for BinaryField128` is the inverse of `towerToGhash`. -/
theorem bf128_from_ghash_toQuot (x : ghash.Ghash128) :
    tower.BinaryField128.Insts.CoreConvertFromGhash128.from x ⦃ t =>
      towerToGhash (towerOf 7 t) = toQuot (ghash x) ⦄ := by
  apply WP.spec_mono (bf128_from_ghash_spec x)
  intro t ht
  rw [towerToGhash_apply, ht, ghashIso_mk, toQuot_eq_mk]

theorem ghash_eq_zero_iff (a : Std.U128) : ghash a = 0 ↔ a = 0#u128 := by
  constructor
  · intro h
    have hq := congrArg toQuot h
    rw [toQuot_eq_mk, toQuot_zero] at hq
    have h0 : a.val = 0 := by
      apply mk_natPoly_eq_zero (n := 128) (tail := 135) (by norm_num) (u128_val_lt a)
      rw [modPoly_128_ghash]; exact hq
    exact UScalar.eq_of_val_eq h0
  · rintro rfl; rfl

theorem ghash128_invert_or_zero_ghash (a : ghash.Ghash128) :
    ghash.Ghash128.invert_or_zero a ⦃ r => ghash r = (ghash a)⁻¹ ⦄ := by
  unfold ghash.Ghash128.invert_or_zero
  exact ghash_invert_or_zero_spec a

theorem ghash128_try_inverse_spec (a : ghash.Ghash128) :
    ghash.Ghash128.Insts.P3_fieldFieldField.try_inverse a ⦃ r =>
      (ghash a = 0 → r = .None) ∧ (ghash a ≠ 0 → ∃ c, r = .Some c ∧ ghash c = (ghash a)⁻¹) ⦄ := by
  unfold ghash.Ghash128.Insts.P3_fieldFieldField.try_inverse core.bool.Bool.then_some
  refine WP.spec_bind (ghash128_invert_or_zero_ghash a) fun c hc => ?_
  by_cases h : a = 0#u128
  · have h' : ¬ (a != 0#u128) = true := by simp [h]
    simp only [h', WP.spec_ok]
    exact ⟨fun _ => rfl, fun hn => absurd ((ghash_eq_zero_iff a).mpr h) hn⟩
  · have h' : (a != 0#u128) = true := by simp [h]
    simp only [h', WP.spec_ok]
    exact ⟨fun hz => absurd ((ghash_eq_zero_iff a).mp hz) h, fun _ => ⟨c, rfl, hc⟩⟩

theorem ghash128_inverse_ghash (a : ghash.Ghash128) (ha : ghash a ≠ 0) :
    field_defaults.Ghash128.inverse a ⦃ c => ghash c = (ghash a)⁻¹ ⦄ := by
  unfold field_defaults.Ghash128.inverse field_defaults.Ghash128.raw_inverse
  refine WP.spec_bind (ghash128_try_inverse_spec a) fun o ho => ?_
  obtain ⟨c, rfl, hc⟩ := ho.2 ha
  simp only [CoreModels.core.option.Option.expect, WP.spec_ok]
  exact hc

theorem ghash128_inverse_zero (a : ghash.Ghash128) (ha : ghash a = 0) :
    field_defaults.Ghash128.inverse a = .fail .panic := by
  obtain ⟨o, ho, hspec⟩ := WP.spec_imp_exists (ghash128_try_inverse_spec a)
  unfold field_defaults.Ghash128.inverse field_defaults.Ghash128.raw_inverse
  rw [ho, hspec.1 ha]
  simp [CoreModels.core.option.Option.expect, CoreModels.core.panicking.internal.panic]

theorem ghash128_div_ghash (a b : ghash.Ghash128) (hb : ghash b ≠ 0) :
    ghash.Ghash128.Insts.CoreOpsArithDivGhash128Ghash128.div a b ⦃ r =>
      ghash r = ghash a / ghash b ⦄ := by
  unfold ghash.Ghash128.Insts.CoreOpsArithDivGhash128Ghash128.div
  refine WP.spec_bind (ghash128_inverse_ghash b hb) fun c hc => ?_
  simp only [CoreModels.core.convert.From.Blanket.from, Aeneas.Std.bind_ok]
  refine WP.spec_mono (ghash128_mul_ghash a c) fun r hr => ?_
  rw [hr, hc, div_eq_mul_inv]

theorem ghash128_div_zero (a b : ghash.Ghash128) (hb : ghash b = 0) :
    ghash.Ghash128.Insts.CoreOpsArithDivGhash128Ghash128.div a b = .fail .panic := by
  unfold ghash.Ghash128.Insts.CoreOpsArithDivGhash128Ghash128.div
  rw [ghash128_inverse_zero b hb]
  simp

theorem ghash128_div_assign_ghash (a b : ghash.Ghash128) (hb : ghash b ≠ 0) :
    ghash.Ghash128.Insts.CoreOpsArithDivAssignGhash128.div_assign a b ⦃ r =>
      ghash r = ghash a / ghash b ⦄ := by
  unfold ghash.Ghash128.Insts.CoreOpsArithDivAssignGhash128.div_assign
  refine WP.spec_bind (ghash128_inverse_ghash b hb) fun c hc => ?_
  simp only [CoreModels.core.convert.From.Blanket.from, Aeneas.Std.bind_ok]
  refine WP.spec_mono (ghash128_mul_assign_ghash a c) fun r hr => ?_
  rw [hr, hc, div_eq_mul_inv]

theorem ghash128_div_assign_zero (a b : ghash.Ghash128) (hb : ghash b = 0) :
    ghash.Ghash128.Insts.CoreOpsArithDivAssignGhash128.div_assign a b = .fail .panic := by
  unfold ghash.Ghash128.Insts.CoreOpsArithDivAssignGhash128.div_assign
  rw [ghash128_inverse_zero b hb]
  simp

/-! ## Operators with a tower operand -/

theorem ghash128_add_bf128 (a : ghash.Ghash128) (b : tower.BinaryField128) :
    ghash.Ghash128.Insts.CoreOpsArithAddBinaryField128Ghash128.add a b ⦃ r =>
      toQuot (ghash r) = toQuot (ghash a) + towerToGhash (towerOf 7 b) ⦄ := by
  unfold ghash.Ghash128.Insts.CoreOpsArithAddBinaryField128Ghash128.add
  refine WP.spec_bind (ghash128_from_bf128_toQuot b) fun g hg => ?_
  refine WP.spec_mono (ghash128_add_ghash a g) fun r hr => ?_
  rw [hr, toQuot_add, hg]

theorem ghash128_sub_bf128 (a : ghash.Ghash128) (b : tower.BinaryField128) :
    ghash.Ghash128.Insts.CoreOpsArithSubBinaryField128Ghash128.sub a b ⦃ r =>
      toQuot (ghash r) = toQuot (ghash a) - towerToGhash (towerOf 7 b) ⦄ := by
  unfold ghash.Ghash128.Insts.CoreOpsArithSubBinaryField128Ghash128.sub
  refine WP.spec_bind (ghash128_from_bf128_toQuot b) fun g hg => ?_
  refine WP.spec_mono (ghash128_sub_ghash a g) fun r hr => ?_
  rw [hr, CharTwo.sub_eq_add, CharTwo.sub_eq_add, toQuot_add, hg]

theorem ghash128_mul_bf128 (a : ghash.Ghash128) (b : tower.BinaryField128) :
    ghash.Ghash128.Insts.CoreOpsArithMulBinaryField128Ghash128.mul a b ⦃ r =>
      toQuot (ghash r) = toQuot (ghash a) * towerToGhash (towerOf 7 b) ⦄ := by
  unfold ghash.Ghash128.Insts.CoreOpsArithMulBinaryField128Ghash128.mul
  refine WP.spec_bind (ghash128_from_bf128_toQuot b) fun g hg => ?_
  refine WP.spec_mono (ghash128_mul_ghash a g) fun r hr => ?_
  rw [hr, toQuot_mul, hg]

end Plonky3Lean.Proofs.Binary
