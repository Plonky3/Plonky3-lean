module

public import Plonky3Lean.Proofs.Field.Neon.Packing
public import Plonky3Lean.Proofs.Field.BabyBear.Generic
public import Plonky3Lean.Proofs.Field.BabyBear.Constants

@[expose] public section

/-!
# BabyBear: the NEON packed arithmetic, at BabyBear's parameters

The generic results of `Plonky3Lean.Proofs.Neon`, at the dictionaries the baby-bear variant
(`P3BabyBearNeon`) extracts for `BabyBearParameters`: the variant's `MontyParameters`
dictionary is P3BabyBear's `MontyParams` (`BabyBearMontyParamsNeon.toPortable`, the bridge),
and `PACKED_P` and `PACKED_MU` hold `PRIME` and `MONTY_MU` in every lane (`packedValid`).

Composed with the scalar results of `Plonky3Lean.Proofs.P3BabyBear`, lane `i` of each packed
result stands for the field operation on lane `i` of the inputs, in CompPoly's `BabyBear.Field`.
-/

open Aeneas Aeneas.Std CoreModels
open Plonky3Lean.Lib Plonky3Lean.Spec.Packed.Neon
open Plonky3Lean.Spec.BabyBear (MontyParams FieldParams Element Canonical toField)

namespace Plonky3Lean.Proofs.P3BabyBear.Neon

/-- The bridge: the variant's `MontyParameters` dictionary for `BabyBearParameters`, read as
P3Monty31's record, is P3BabyBear's `MontyParams`. The constants are bound to P3BabyBear's,
the derived impls are P3BabyBear's, and `MONTY_MASK` is the trait default in both. -/
theorem BabyBearMontyParamsNeon.toPortable : toPortable BabyBearMontyParamsNeon = MontyParams := by
  unfold Spec.Packed.Neon.toPortable BabyBearMontyParamsNeon MontyParams
  rw [p3_baby_bear_neon.baby_bear.BabyBearParameters.Insts.P3_monty_31Data_traitsMontyParameters,
    p3_baby_bear.baby_bear.BabyBearParameters.Insts.P3_monty_31Data_traitsMontyParameters]
  rfl

theorem lanes_of_repeat (x : Std.U32) (d : U32x4) (hdx : ∀ y ∈ d.val, y = x) (i : Fin 4) :
    lane d i = x := by
  have hi : i.val < d.val.length := by rw [Neon.A.len]; exact i.isLt
  simp only [lane, List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
  exact hdx _ (List.getElem_mem hi)

/-- BabyBear's NEON parameters are valid: `PACKED_P` is `PRIME` in every lane, and `PACKED_MU`
is `MONTY_MU` in every lane, read as a `u32` (the `i32` `-0x77ffffff`). -/
theorem packedValid : Valid BabyBearPackedParams 2013265921#u32 2281701377#u32 where
  monty := by
    show Spec.Monty31.Valid (toPortable BabyBearMontyParamsNeon) _ _
    rw [BabyBearMontyParamsNeon.toPortable]; exact valid
  packed_p := by
    obtain ⟨d, hd, hdx⟩ := array_repeat_eq 4#usize core.U32.Insts.CoreCloneClone (fun _ => rfl)
      2013265921#u32
    refine ⟨d, ?_, lanes_of_repeat _ d hdx⟩
    show p3_baby_bear_neon.baby_bear.BabyBearParameters.Insts.P3_monty_31Aarch64_neonPackingMontyParametersNeon.PACKED_P = _
    unfold p3_baby_bear_neon.baby_bear.BabyBearParameters.Insts.P3_monty_31Aarch64_neonPackingMontyParametersNeon.PACKED_P
    rw [hd, bind_ok]; rfl
  packed_mu := by
    obtain ⟨d, hd, hdx⟩ := array_repeat_eq 4#usize core.I32.Insts.CoreCloneClone (fun _ => rfl)
      (-2013265919)#i32
    refine ⟨d, ?_, fun i => ?_⟩
    · show p3_baby_bear_neon.baby_bear.BabyBearParameters.Insts.P3_monty_31Aarch64_neonPackingMontyParametersNeon.PACKED_MU = _
      unfold p3_baby_bear_neon.baby_bear.BabyBearParameters.Insts.P3_monty_31Aarch64_neonPackingMontyParametersNeon.PACKED_MU
      rw [hd, bind_ok]; rfl
    · have hi : i.val < d.val.length := by rw [Neon.A.len]; exact i.isLt
      have hx : slane d i = (-2013265919)#i32 := by
        simp only [slane, List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hi,
          Option.getD_some]
        exact hdx _ (List.getElem_mem hi)
      rw [hx]
      rfl

theorem fieldValid' : Spec.Monty31.FieldValid FieldParams 2013265921#u32 2281701377#u32 :=
  fieldValid

theorem monty_zero :
    FieldParams.MONTY_ZERO ⦃ z => Spec.Monty31.Canonical (2013265921#u32).val z ∧
      Spec.Monty31.toField (2013265921#u32).val z = 0 ⦄ :=
  FieldParams.MONTY_ZERO.toField

/-! ## Lane `i` is the scalar operator on lane `i` -/

open p3_monty_31_neon.aarch64_neon.packing.PackedMontyField31Neon.Insts

theorem add.lanewise (x y : PackedBabyBearNeon) (hx : ∀ i : Fin 4, Canonical (toVector x)[i])
    (hy : ∀ i : Fin 4, Canonical (toVector y)[i]) :
    CoreOpsArithAddPackedMontyField31NeonPackedMontyField31Neon.add BabyBearPackedParams x y
      ⦃ z => (∀ i : Fin 4, Canonical (toVector z)[i]) ∧ ∀ i : Fin 4,
        p3_monty_31.monty_31.MontyField31.Insts.CoreOpsArithAddMontyField31MontyField31.add
          MontyParams (toVector x)[i] (toVector y)[i] = .ok (toVector z)[i] ⦄ := by
  have h := _root_.Plonky3Lean.Proofs.Neon.add.lanewise packedValid x y hx hy
  rw [BabyBearMontyParamsNeon.toPortable] at h
  exact h

theorem sub.lanewise (x y : PackedBabyBearNeon) (hx : ∀ i : Fin 4, Canonical (toVector x)[i])
    (hy : ∀ i : Fin 4, Canonical (toVector y)[i]) :
    CoreOpsArithSubPackedMontyField31NeonPackedMontyField31Neon.sub BabyBearPackedParams x y
      ⦃ z => (∀ i : Fin 4, Canonical (toVector z)[i]) ∧ ∀ i : Fin 4,
        p3_monty_31.monty_31.MontyField31.Insts.CoreOpsArithSubMontyField31MontyField31.sub
          MontyParams (toVector x)[i] (toVector y)[i] = .ok (toVector z)[i] ⦄ := by
  have h := _root_.Plonky3Lean.Proofs.Neon.sub.lanewise packedValid x y hx hy
  rw [BabyBearMontyParamsNeon.toPortable] at h
  exact h

theorem mul.lanewise (x y : PackedBabyBearNeon) (hx : ∀ i : Fin 4, Canonical (toVector x)[i])
    (hy : ∀ i : Fin 4, Canonical (toVector y)[i]) :
    CoreOpsArithMulPackedMontyField31NeonPackedMontyField31Neon.mul BabyBearPackedParams x y
      ⦃ z => (∀ i : Fin 4, Canonical (toVector z)[i]) ∧ ∀ i : Fin 4,
        p3_monty_31.monty_31.MontyField31.Insts.CoreOpsArithMulMontyField31MontyField31.mul
          MontyParams (toVector x)[i] (toVector y)[i] = .ok (toVector z)[i] ⦄ := by
  have h := _root_.Plonky3Lean.Proofs.Neon.mul.lanewise packedValid x y hx hy
  rw [BabyBearMontyParamsNeon.toPortable] at h
  exact h

theorem neg.lanewise (x : PackedBabyBearNeon) (hx : ∀ i : Fin 4, Canonical (toVector x)[i]) :
    CoreOpsArithNegPackedMontyField31Neon.neg BabyBearPackedParams x
      ⦃ z => (∀ i : Fin 4, Canonical (toVector z)[i]) ∧ ∀ i : Fin 4,
        p3_monty_31.monty_31.MontyField31.Insts.CoreOpsArithNegMontyField31.neg
          FieldParams (toVector x)[i] = .ok (toVector z)[i] ⦄ :=
  _root_.Plonky3Lean.Proofs.Neon.neg.lanewise packedValid FieldParams fieldValid' monty_zero x hx

/-- `halve_neon(v)`, the vector `PackedMontyField31Neon::halve` passes to `from_vector`, for `v`
with canonical lanes: its lanes are canonical, and lane `i` is the scalar `halve` of lane `i`. -/
theorem halve_neon.lanewise (v : U32x4) (hv : FromVectorSafe BabyBear.fieldSize v) :
    p3_monty_31_neon.aarch64_neon.utils.halve_neon BabyBearPackedParams v
      ⦃ r => FromVectorSafe BabyBear.fieldSize r ∧ ∀ i : Fin 4,
        p3_monty_31.monty_31.MontyField31.Insts.P3_fieldFieldPrimeCharacteristicRing.halve
          FieldParams ⟨lane v i, ()⟩ = .ok ⟨lane r i, ()⟩ ⦄ :=
  _root_.Plonky3Lean.Proofs.Neon.halve_neon.lanewise packedValid FieldParams fieldValid' v hv

/-! ## As field elements -/

/-- A lane-wise statement about the scalar operator gives the scalar operator's field-element
claim, lane by lane. -/
theorem lanes_toField {m : RustM PackedBabyBearNeon} {R : Fin 4 → Element → Prop}
    {op : Fin 4 → RustM Element}
    (hm : m ⦃ z => (∀ i : Fin 4, Canonical (toVector z)[i]) ∧ ∀ i, op i = .ok (toVector z)[i] ⦄)
    (hop : ∀ i, op i ⦃ c => Canonical c ∧ R i c ⦄) :
    m ⦃ z => ∀ i : Fin 4, Canonical (toVector z)[i] ∧ R i (toVector z)[i] ⦄ := by
  refine WP.spec_mono hm fun z hz i => ?_
  have h := hop i
  rw [hz.2 i] at h
  simp only [WP.spec_ok] at h
  exact h

theorem add.toField (x y : PackedBabyBearNeon) (hx : ∀ i : Fin 4, Canonical (toVector x)[i])
    (hy : ∀ i : Fin 4, Canonical (toVector y)[i]) :
    CoreOpsArithAddPackedMontyField31NeonPackedMontyField31Neon.add BabyBearPackedParams x y
      ⦃ z => ∀ i : Fin 4, Canonical (toVector z)[i] ∧
        toField (toVector z)[i] = toField (toVector x)[i] + toField (toVector y)[i] ⦄ :=
  lanes_toField (add.lanewise x y hx hy)
    (fun i => baby_bear.BabyBear.add.toField _ _ (hx i) (hy i))

theorem sub.toField (x y : PackedBabyBearNeon) (hx : ∀ i : Fin 4, Canonical (toVector x)[i])
    (hy : ∀ i : Fin 4, Canonical (toVector y)[i]) :
    CoreOpsArithSubPackedMontyField31NeonPackedMontyField31Neon.sub BabyBearPackedParams x y
      ⦃ z => ∀ i : Fin 4, Canonical (toVector z)[i] ∧
        toField (toVector z)[i] = toField (toVector x)[i] - toField (toVector y)[i] ⦄ :=
  lanes_toField (sub.lanewise x y hx hy)
    (fun i => baby_bear.BabyBear.sub.toField _ _ (hx i) (hy i))

theorem mul.toField (x y : PackedBabyBearNeon) (hx : ∀ i : Fin 4, Canonical (toVector x)[i])
    (hy : ∀ i : Fin 4, Canonical (toVector y)[i]) :
    CoreOpsArithMulPackedMontyField31NeonPackedMontyField31Neon.mul BabyBearPackedParams x y
      ⦃ z => ∀ i : Fin 4, Canonical (toVector z)[i] ∧
        toField (toVector z)[i] = toField (toVector x)[i] * toField (toVector y)[i] ⦄ :=
  lanes_toField (mul.lanewise x y hx hy)
    (fun i => baby_bear.BabyBear.mul.toField _ _ (hx i) (hy i))

theorem neg.toField (x : PackedBabyBearNeon) (hx : ∀ i : Fin 4, Canonical (toVector x)[i]) :
    CoreOpsArithNegPackedMontyField31Neon.neg BabyBearPackedParams x
      ⦃ z => ∀ i : Fin 4, Canonical (toVector z)[i] ∧
        toField (toVector z)[i] = -toField (toVector x)[i] ⦄ :=
  lanes_toField (neg.lanewise x hx) (fun i => baby_bear.BabyBear.neg.toField _ (hx i))

theorem halve_neon.toField (v : U32x4) (hv : FromVectorSafe BabyBear.fieldSize v) :
    p3_monty_31_neon.aarch64_neon.utils.halve_neon BabyBearPackedParams v
      ⦃ r => FromVectorSafe BabyBear.fieldSize r ∧ ∀ i : Fin 4,
        toField ⟨lane r i, ()⟩ * 2 = toField ⟨lane v i, ()⟩ ⦄ := by
  refine WP.spec_mono (halve_neon.lanewise v hv) fun r hr => ⟨hr.1, fun i => ?_⟩
  have h := baby_bear.BabyBear.halve.toField ⟨lane v i, ()⟩ (hv i)
  rw [hr.2 i] at h
  simp only [WP.spec_ok] at h
  exact h.2

/-! ## `from_vector`'s safety condition -/

theorem add.from_vector_arg (x y : PackedBabyBearNeon)
    (hx : ∀ i : Fin 4, Canonical (toVector x)[i]) (hy : ∀ i : Fin 4, Canonical (toVector y)[i]) :
    ∃ v, FromVectorSafe BabyBear.fieldSize v ∧
      CoreOpsArithAddPackedMontyField31NeonPackedMontyField31Neon.add BabyBearPackedParams x y =
        p3_monty_31_neon.aarch64_neon.packing.PackedMontyField31Neon.from_vector
          BabyBearPackedParams v :=
  let ⟨v, hs, _, he⟩ := _root_.Plonky3Lean.Proofs.Neon.add.from_vector_arg packedValid x y hx hy
  ⟨v, hs, he⟩

theorem sub.from_vector_arg (x y : PackedBabyBearNeon)
    (hx : ∀ i : Fin 4, Canonical (toVector x)[i]) (hy : ∀ i : Fin 4, Canonical (toVector y)[i]) :
    ∃ v, FromVectorSafe BabyBear.fieldSize v ∧
      CoreOpsArithSubPackedMontyField31NeonPackedMontyField31Neon.sub BabyBearPackedParams x y =
        p3_monty_31_neon.aarch64_neon.packing.PackedMontyField31Neon.from_vector
          BabyBearPackedParams v :=
  let ⟨v, hs, _, he⟩ := _root_.Plonky3Lean.Proofs.Neon.sub.from_vector_arg packedValid x y hx hy
  ⟨v, hs, he⟩

theorem mul.from_vector_arg (x y : PackedBabyBearNeon)
    (hx : ∀ i : Fin 4, Canonical (toVector x)[i]) (hy : ∀ i : Fin 4, Canonical (toVector y)[i]) :
    ∃ v, FromVectorSafe BabyBear.fieldSize v ∧
      CoreOpsArithMulPackedMontyField31NeonPackedMontyField31Neon.mul BabyBearPackedParams x y =
        p3_monty_31_neon.aarch64_neon.packing.PackedMontyField31Neon.from_vector
          BabyBearPackedParams v :=
  let ⟨v, hs, _, he⟩ := _root_.Plonky3Lean.Proofs.Neon.mul.from_vector_arg packedValid x y hx hy
  ⟨v, hs, he⟩

theorem neg.from_vector_arg (x : PackedBabyBearNeon)
    (hx : ∀ i : Fin 4, Canonical (toVector x)[i]) :
    ∃ v, FromVectorSafe BabyBear.fieldSize v ∧
      CoreOpsArithNegPackedMontyField31Neon.neg BabyBearPackedParams x =
        p3_monty_31_neon.aarch64_neon.packing.PackedMontyField31Neon.from_vector
          BabyBearPackedParams v :=
  let ⟨v, hs, _, he⟩ := _root_.Plonky3Lean.Proofs.Neon.neg.from_vector_arg packedValid x hx
  ⟨v, hs, he⟩

end Plonky3Lean.Proofs.P3BabyBear.Neon
