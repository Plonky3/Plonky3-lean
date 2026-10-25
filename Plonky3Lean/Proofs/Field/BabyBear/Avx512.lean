module

public import Plonky3Lean.Proofs.Field.Avx512.Packing
public import Plonky3Lean.Proofs.Field.BabyBear.Generic
public import Plonky3Lean.Proofs.Field.BabyBear.Constants

@[expose] public section

/-!
# BabyBear: the AVX-512 packed arithmetic, at BabyBear's parameters

The generic results of `Plonky3Lean.Proofs.Avx512`, at the dictionaries the baby-bear variant
(`P3BabyBearAvx512`) extracts for `BabyBearParameters`: the variant's `MontyParameters`
dictionary is P3BabyBear's `MontyParams` (`BabyBearMontyParamsAvx512.toPortable`, the bridge),
and `PACKED_P` and `PACKED_MU` hold `PRIME` and `MONTY_MU` in every lane (`packedValid`).

Composed with the scalar results of `Plonky3Lean.Proofs.P3BabyBear`, lane `i` of each packed
result stands for the field operation on lane `i` of the inputs, in CompPoly's `BabyBear.Field`.
-/

open Aeneas Aeneas.Std CoreModels
open Plonky3Lean.Lib Plonky3Lean.Spec.Packed.Avx512
open Plonky3Lean.Spec.BabyBear (MontyParams FieldParams Element Canonical toField)

namespace Plonky3Lean.Proofs.P3BabyBear.Avx512

/-- The bridge: the variant's `MontyParameters` dictionary for `BabyBearParameters`, read as
P3Monty31's record, is P3BabyBear's `MontyParams`. The constants are bound to P3BabyBear's,
the derived impls are P3BabyBear's, and `MONTY_MASK` is the trait default in both. -/
theorem BabyBearMontyParamsAvx512.toPortable :
    toPortable BabyBearMontyParamsAvx512 = MontyParams := by
  unfold Spec.Packed.Avx512.toPortable BabyBearMontyParamsAvx512 MontyParams
  rw [p3_baby_bear_avx512.baby_bear.BabyBearParameters.Insts.P3_monty_31Data_traitsMontyParameters,
    p3_baby_bear.baby_bear.BabyBearParameters.Insts.P3_monty_31Data_traitsMontyParameters]
  rfl

theorem lanes_of_repeat (x : Std.U32) (d : M512i) (hdx : ∀ y ∈ d.val, y = x) (i : Fin 16) :
    lane d i = x := by
  have hi : i.val < d.val.length := by rw [Avx512.V.len]; exact i.isLt
  simp only [lane, List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
  exact hdx _ (List.getElem_mem hi)

/-- BabyBear's AVX-512 parameters are valid: `PACKED_P` and `PACKED_MU` are `PRIME` and `MONTY_MU`
in every lane. -/
theorem packedValid : Valid BabyBearPackedParams 2013265921#u32 2281701377#u32 where
  monty := by
    show Spec.Monty31.Valid (toPortable BabyBearMontyParamsAvx512) _ _
    rw [BabyBearMontyParamsAvx512.toPortable]; exact valid
  packed_p := by
    obtain ⟨d, hd, hdx⟩ := array_repeat_eq 16#usize core.U32.Insts.CoreCloneClone (fun _ => rfl)
      2013265921#u32
    refine ⟨d, ?_, lanes_of_repeat _ d hdx⟩
    show p3_baby_bear_avx512.baby_bear.BabyBearParameters.Insts.P3_monty_31X86_64_avx512PackingMontyParametersAVX512.PACKED_P = _
    unfold p3_baby_bear_avx512.baby_bear.BabyBearParameters.Insts.P3_monty_31X86_64_avx512PackingMontyParametersAVX512.PACKED_P
    rw [hd, bind_ok]; rfl
  packed_mu := by
    obtain ⟨d, hd, hdx⟩ := array_repeat_eq 16#usize core.U32.Insts.CoreCloneClone (fun _ => rfl)
      2281701377#u32
    refine ⟨d, ?_, lanes_of_repeat _ d hdx⟩
    show p3_baby_bear_avx512.baby_bear.BabyBearParameters.Insts.P3_monty_31X86_64_avx512PackingMontyParametersAVX512.PACKED_MU = _
    unfold p3_baby_bear_avx512.baby_bear.BabyBearParameters.Insts.P3_monty_31X86_64_avx512PackingMontyParametersAVX512.PACKED_MU
    rw [hd, bind_ok]; rfl

theorem fieldValid' : Spec.Monty31.FieldValid FieldParams 2013265921#u32 2281701377#u32 :=
  fieldValid

theorem monty_zero :
    FieldParams.MONTY_ZERO ⦃ z => Spec.Monty31.Canonical (2013265921#u32).val z ∧
      Spec.Monty31.toField (2013265921#u32).val z = 0 ⦄ :=
  FieldParams.MONTY_ZERO.toField

/-! ## Lane `i` is the scalar operator on lane `i` -/

open p3_monty_31_avx512.x86_64_avx512.packing.PackedMontyField31AVX512.Insts

theorem add.lanewise (x y : PackedBabyBearAVX512) (hx : ∀ i : Fin 16, Canonical (toVector x)[i])
    (hy : ∀ i : Fin 16, Canonical (toVector y)[i]) :
    CoreOpsArithAddPackedMontyField31AVX512PackedMontyField31AVX512.add BabyBearPackedParams x y
      ⦃ z => (∀ i : Fin 16, Canonical (toVector z)[i]) ∧ ∀ i : Fin 16,
        p3_monty_31.monty_31.MontyField31.Insts.CoreOpsArithAddMontyField31MontyField31.add
          MontyParams (toVector x)[i] (toVector y)[i] = .ok (toVector z)[i] ⦄ := by
  have h := _root_.Plonky3Lean.Proofs.Avx512.add.lanewise packedValid x y hx hy
  rw [BabyBearMontyParamsAvx512.toPortable] at h
  exact h

theorem sub.lanewise (x y : PackedBabyBearAVX512) (hx : ∀ i : Fin 16, Canonical (toVector x)[i])
    (hy : ∀ i : Fin 16, Canonical (toVector y)[i]) :
    CoreOpsArithSubPackedMontyField31AVX512PackedMontyField31AVX512.sub BabyBearPackedParams x y
      ⦃ z => (∀ i : Fin 16, Canonical (toVector z)[i]) ∧ ∀ i : Fin 16,
        p3_monty_31.monty_31.MontyField31.Insts.CoreOpsArithSubMontyField31MontyField31.sub
          MontyParams (toVector x)[i] (toVector y)[i] = .ok (toVector z)[i] ⦄ := by
  have h := _root_.Plonky3Lean.Proofs.Avx512.sub.lanewise packedValid x y hx hy
  rw [BabyBearMontyParamsAvx512.toPortable] at h
  exact h

theorem mul.lanewise (x y : PackedBabyBearAVX512) (hx : ∀ i : Fin 16, Canonical (toVector x)[i])
    (hy : ∀ i : Fin 16, Canonical (toVector y)[i]) :
    CoreOpsArithMulPackedMontyField31AVX512PackedMontyField31AVX512.mul BabyBearPackedParams x y
      ⦃ z => (∀ i : Fin 16, Canonical (toVector z)[i]) ∧ ∀ i : Fin 16,
        p3_monty_31.monty_31.MontyField31.Insts.CoreOpsArithMulMontyField31MontyField31.mul
          MontyParams (toVector x)[i] (toVector y)[i] = .ok (toVector z)[i] ⦄ := by
  have h := _root_.Plonky3Lean.Proofs.Avx512.mul.lanewise packedValid x y hx hy
  rw [BabyBearMontyParamsAvx512.toPortable] at h
  exact h

theorem neg.lanewise (x : PackedBabyBearAVX512) (hx : ∀ i : Fin 16, Canonical (toVector x)[i]) :
    CoreOpsArithNegPackedMontyField31AVX512.neg BabyBearPackedParams x
      ⦃ z => (∀ i : Fin 16, Canonical (toVector z)[i]) ∧ ∀ i : Fin 16,
        p3_monty_31.monty_31.MontyField31.Insts.CoreOpsArithNegMontyField31.neg
          FieldParams (toVector x)[i] = .ok (toVector z)[i] ⦄ :=
  _root_.Plonky3Lean.Proofs.Avx512.neg.lanewise packedValid FieldParams fieldValid' monty_zero x hx

/-- `halve_avx512(v)`, the vector `PackedMontyField31AVX512::halve` passes to `from_vector`, for `v`
with canonical lanes: its lanes are canonical, and lane `i` is the scalar `halve` of lane `i`. -/
theorem halve_avx512.lanewise (v : M512i) (hv : FromVectorSafe BabyBear.fieldSize v) :
    p3_monty_31_avx512.x86_64_avx512.utils.halve_avx512 BabyBearMontyParamsAvx512 v
      ⦃ r => FromVectorSafe BabyBear.fieldSize r ∧ ∀ i : Fin 16,
        p3_monty_31.monty_31.MontyField31.Insts.P3_fieldFieldPrimeCharacteristicRing.halve
          FieldParams ⟨lane v i, ()⟩ = .ok ⟨lane r i, ()⟩ ⦄ :=
  _root_.Plonky3Lean.Proofs.Avx512.halve_avx512.lanewise BabyBearMontyParamsAvx512
    (by rw [BabyBearMontyParamsAvx512.toPortable]; exact valid) (by decide) FieldParams fieldValid'
    v hv

/-! ## As field elements -/

/-- A lane-wise statement about the scalar operator gives the scalar operator's field-element
claim, lane by lane. -/
theorem lanes_toField {m : RustM PackedBabyBearAVX512} {R : Fin 16 → Element → Prop}
    {op : Fin 16 → RustM Element}
    (hm : m ⦃ z => (∀ i : Fin 16, Canonical (toVector z)[i]) ∧ ∀ i, op i = .ok (toVector z)[i] ⦄)
    (hop : ∀ i, op i ⦃ c => Canonical c ∧ R i c ⦄) :
    m ⦃ z => ∀ i : Fin 16, Canonical (toVector z)[i] ∧ R i (toVector z)[i] ⦄ := by
  refine WP.spec_mono hm fun z hz i => ?_
  have h := hop i
  rw [hz.2 i] at h
  simp only [WP.spec_ok] at h
  exact h

theorem add.toField (x y : PackedBabyBearAVX512) (hx : ∀ i : Fin 16, Canonical (toVector x)[i])
    (hy : ∀ i : Fin 16, Canonical (toVector y)[i]) :
    CoreOpsArithAddPackedMontyField31AVX512PackedMontyField31AVX512.add BabyBearPackedParams x y
      ⦃ z => ∀ i : Fin 16, Canonical (toVector z)[i] ∧
        toField (toVector z)[i] = toField (toVector x)[i] + toField (toVector y)[i] ⦄ :=
  lanes_toField (add.lanewise x y hx hy)
    (fun i => baby_bear.BabyBear.add.toField _ _ (hx i) (hy i))

theorem sub.toField (x y : PackedBabyBearAVX512) (hx : ∀ i : Fin 16, Canonical (toVector x)[i])
    (hy : ∀ i : Fin 16, Canonical (toVector y)[i]) :
    CoreOpsArithSubPackedMontyField31AVX512PackedMontyField31AVX512.sub BabyBearPackedParams x y
      ⦃ z => ∀ i : Fin 16, Canonical (toVector z)[i] ∧
        toField (toVector z)[i] = toField (toVector x)[i] - toField (toVector y)[i] ⦄ :=
  lanes_toField (sub.lanewise x y hx hy)
    (fun i => baby_bear.BabyBear.sub.toField _ _ (hx i) (hy i))

theorem mul.toField (x y : PackedBabyBearAVX512) (hx : ∀ i : Fin 16, Canonical (toVector x)[i])
    (hy : ∀ i : Fin 16, Canonical (toVector y)[i]) :
    CoreOpsArithMulPackedMontyField31AVX512PackedMontyField31AVX512.mul BabyBearPackedParams x y
      ⦃ z => ∀ i : Fin 16, Canonical (toVector z)[i] ∧
        toField (toVector z)[i] = toField (toVector x)[i] * toField (toVector y)[i] ⦄ :=
  lanes_toField (mul.lanewise x y hx hy)
    (fun i => baby_bear.BabyBear.mul.toField _ _ (hx i) (hy i))

theorem neg.toField (x : PackedBabyBearAVX512) (hx : ∀ i : Fin 16, Canonical (toVector x)[i]) :
    CoreOpsArithNegPackedMontyField31AVX512.neg BabyBearPackedParams x
      ⦃ z => ∀ i : Fin 16, Canonical (toVector z)[i] ∧
        toField (toVector z)[i] = -toField (toVector x)[i] ⦄ :=
  lanes_toField (neg.lanewise x hx) (fun i => baby_bear.BabyBear.neg.toField _ (hx i))

theorem halve_avx512.toField (v : M512i) (hv : FromVectorSafe BabyBear.fieldSize v) :
    p3_monty_31_avx512.x86_64_avx512.utils.halve_avx512 BabyBearMontyParamsAvx512 v
      ⦃ r => FromVectorSafe BabyBear.fieldSize r ∧ ∀ i : Fin 16,
        toField ⟨lane r i, ()⟩ * 2 = toField ⟨lane v i, ()⟩ ⦄ := by
  refine WP.spec_mono (halve_avx512.lanewise v hv) fun r hr => ⟨hr.1, fun i => ?_⟩
  have h := baby_bear.BabyBear.halve.toField ⟨lane v i, ()⟩ (hv i)
  rw [hr.2 i] at h
  simp only [WP.spec_ok] at h
  exact h.2

/-! ## `from_vector`'s safety condition -/

theorem add.from_vector_arg (x y : PackedBabyBearAVX512)
    (hx : ∀ i : Fin 16, Canonical (toVector x)[i]) (hy : ∀ i : Fin 16, Canonical (toVector y)[i]) :
    ∃ v, FromVectorSafe BabyBear.fieldSize v ∧
      CoreOpsArithAddPackedMontyField31AVX512PackedMontyField31AVX512.add BabyBearPackedParams x y =
        p3_monty_31_avx512.x86_64_avx512.packing.PackedMontyField31AVX512.from_vector
          BabyBearPackedParams v :=
  let ⟨v, hs, _, he⟩ := _root_.Plonky3Lean.Proofs.Avx512.add.from_vector_arg packedValid x y hx hy
  ⟨v, hs, he⟩

theorem sub.from_vector_arg (x y : PackedBabyBearAVX512)
    (hx : ∀ i : Fin 16, Canonical (toVector x)[i]) (hy : ∀ i : Fin 16, Canonical (toVector y)[i]) :
    ∃ v, FromVectorSafe BabyBear.fieldSize v ∧
      CoreOpsArithSubPackedMontyField31AVX512PackedMontyField31AVX512.sub BabyBearPackedParams x y =
        p3_monty_31_avx512.x86_64_avx512.packing.PackedMontyField31AVX512.from_vector
          BabyBearPackedParams v :=
  let ⟨v, hs, _, he⟩ := _root_.Plonky3Lean.Proofs.Avx512.sub.from_vector_arg packedValid x y hx hy
  ⟨v, hs, he⟩

theorem mul.from_vector_arg (x y : PackedBabyBearAVX512)
    (hx : ∀ i : Fin 16, Canonical (toVector x)[i]) (hy : ∀ i : Fin 16, Canonical (toVector y)[i]) :
    ∃ v, FromVectorSafe BabyBear.fieldSize v ∧
      CoreOpsArithMulPackedMontyField31AVX512PackedMontyField31AVX512.mul BabyBearPackedParams x y =
        p3_monty_31_avx512.x86_64_avx512.packing.PackedMontyField31AVX512.from_vector
          BabyBearPackedParams v :=
  let ⟨v, hs, _, he⟩ := _root_.Plonky3Lean.Proofs.Avx512.mul.from_vector_arg packedValid x y hx hy
  ⟨v, hs, he⟩

theorem neg.from_vector_arg (x : PackedBabyBearAVX512)
    (hx : ∀ i : Fin 16, Canonical (toVector x)[i]) :
    ∃ v, FromVectorSafe BabyBear.fieldSize v ∧
      CoreOpsArithNegPackedMontyField31AVX512.neg BabyBearPackedParams x =
        p3_monty_31_avx512.x86_64_avx512.packing.PackedMontyField31AVX512.from_vector
          BabyBearPackedParams v :=
  let ⟨v, hs, _, he⟩ := _root_.Plonky3Lean.Proofs.Avx512.neg.from_vector_arg packedValid x hx
  ⟨v, hs, he⟩

end Plonky3Lean.Proofs.P3BabyBear.Avx512
