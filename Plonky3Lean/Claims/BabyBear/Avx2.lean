module

public import Plonky3Lean.Proofs.Field.BabyBear.Avx2

@[expose] public section

/-!
# BabyBear on x86_64 with AVX2: claims

What this repository asserts about `PackedBabyBearAVX2`, p3-monty-31's
`PackedMontyField31AVX2<BabyBearParameters>`, at the Plonky3 commit pinned in `plonky3/`.
The model is the x86_64-avx2 variants of p3-monty-31 (`crates/monty-31/variants/x86_64-avx2`,
namespace `p3_monty_31_avx2`) and p3-baby-bear (`crates/baby-bear/variants/x86_64-avx2`,
`p3_baby_bear_avx2`), extracted against the intrinsic models of `arch/` (`P3ArchShims`).
`toVector`, `lane`, `FromVectorSafe` and the dictionary names are
`Plonky3Lean.Spec.Packed`'s; `Canonical`, `toField` and the scalar dictionaries
`MontyParams` and `FieldParams` are `Plonky3Lean.Spec.BabyBear`'s, so a lane is read exactly as
a scalar `BabyBear` is, and `BabyBear.Field` is CompPoly's specification of the field.

For packed inputs whose lanes are canonical, `Add`, `Sub`, `Mul` and `Neg`:

* never fail, and end in a call `from_vector(v)` whose `v` has canonical lanes, which is the
  safety condition `from_vector` documents (`*.from_vector_arg`);
* give a result whose lanes are canonical, lane `i` being what the portable scalar operator
  returns on lane `i` of the inputs (`*.lanewise`);
* and so, by the scalar claims, stand lane by lane for the field operation (`*.toField`).

`PackedMontyField31AVX2::halve` is not in the model; `halve_avx2`, the vector it passes to
`from_vector`, is, and is claimed on the lanes of an `__m256i`.

Not claimed: the impls whose right operand is a scalar `MontyField31` (they `broadcast` it
first), the assigning operators, `halve` itself and the rest of `PrimeCharacteristicRing` and
`PackedField` (`dot_product`'s dispatch, as opposed to its kernels, `mixed_dot_product`,
`exp_const`, interleaving, the packed Poseidon layers), the intrinsic models themselves
(trusted, and tested against the hardware in `arch/tests/`), and the `transmute` layout
assumptions `to_vector` and `from_vector` rest on (`STATUS.md`).
-/

open Aeneas Aeneas.Std CoreModels
open Plonky3Lean.Spec.Packed
open Plonky3Lean.Spec.BabyBear (MontyParams FieldParams Canonical toField)
open p3_monty_31_avx2.x86_64_avx2.packing.PackedMontyField31AVX2.Insts

namespace Plonky3Lean.Claims.P3BabyBear

/-! ## BabyBear's AVX2 parameters

The baby-bear variant re-extracts `BabyBearParameters`' `MontyParameters` dictionary into the
monty-31 variant's record; read as P3Monty31's record it is the scalar `MontyParams`. Its
`MontyParametersAVX2` constants hold `PRIME` and `MONTY_MU` in every lane. -/

/-- The bridge: the AVX2 build's `MontyParameters` dictionary for `BabyBearParameters` is the
scalar one, member for member. -/
theorem x86_64_avx2.BabyBearParameters.MontyParameters.toPortable :
    toPortable BabyBearMontyParamsAvx2 = MontyParams :=
  Proofs.P3BabyBear.Avx2.BabyBearMontyParamsAvx2.toPortable

/-- `PACKED_P` and `PACKED_MU` are `PRIME = 2013265921` and `MONTY_MU = 2281701377` in every
lane, and BabyBear's `MontyParameters` are valid. -/
theorem x86_64_avx2.BabyBearParameters.valid :
    Valid BabyBearPackedParams 2013265921#u32 2281701377#u32 :=
  Proofs.P3BabyBear.Avx2.packedValid

/-! ## Lane `i` is the scalar operator on lane `i` -/

/-- Packed `x + y` on canonical lanes has canonical lanes, lane `i` being the scalar
`x[i] + y[i]`. -/
theorem x86_64_avx2.PackedBabyBearAVX2.add.lanewise (x y : PackedBabyBearAVX2)
    (hx : ∀ i : Fin 8, Canonical (toVector x)[i]) (hy : ∀ i : Fin 8, Canonical (toVector y)[i]) :
    CoreOpsArithAddPackedMontyField31AVX2PackedMontyField31AVX2.add BabyBearPackedParams x y
      ⦃ z => (∀ i : Fin 8, Canonical (toVector z)[i]) ∧ ∀ i : Fin 8,
        p3_monty_31.monty_31.MontyField31.Insts.CoreOpsArithAddMontyField31MontyField31.add
          MontyParams (toVector x)[i] (toVector y)[i] = .ok (toVector z)[i] ⦄ :=
  Proofs.P3BabyBear.Avx2.add.lanewise x y hx hy

/-- Packed `x - y` on canonical lanes has canonical lanes, lane `i` being the scalar
`x[i] - y[i]`. -/
theorem x86_64_avx2.PackedBabyBearAVX2.sub.lanewise (x y : PackedBabyBearAVX2)
    (hx : ∀ i : Fin 8, Canonical (toVector x)[i]) (hy : ∀ i : Fin 8, Canonical (toVector y)[i]) :
    CoreOpsArithSubPackedMontyField31AVX2PackedMontyField31AVX2.sub BabyBearPackedParams x y
      ⦃ z => (∀ i : Fin 8, Canonical (toVector z)[i]) ∧ ∀ i : Fin 8,
        p3_monty_31.monty_31.MontyField31.Insts.CoreOpsArithSubMontyField31MontyField31.sub
          MontyParams (toVector x)[i] (toVector y)[i] = .ok (toVector z)[i] ⦄ :=
  Proofs.P3BabyBear.Avx2.sub.lanewise x y hx hy

/-- Packed `x * y` on canonical lanes has canonical lanes, lane `i` being the scalar
`x[i] * y[i]`: the vector Montgomery multiplication, with its signed intermediate, agrees with
the scalar one. -/
theorem x86_64_avx2.PackedBabyBearAVX2.mul.lanewise (x y : PackedBabyBearAVX2)
    (hx : ∀ i : Fin 8, Canonical (toVector x)[i]) (hy : ∀ i : Fin 8, Canonical (toVector y)[i]) :
    CoreOpsArithMulPackedMontyField31AVX2PackedMontyField31AVX2.mul BabyBearPackedParams x y
      ⦃ z => (∀ i : Fin 8, Canonical (toVector z)[i]) ∧ ∀ i : Fin 8,
        p3_monty_31.monty_31.MontyField31.Insts.CoreOpsArithMulMontyField31MontyField31.mul
          MontyParams (toVector x)[i] (toVector y)[i] = .ok (toVector z)[i] ⦄ :=
  Proofs.P3BabyBear.Avx2.mul.lanewise x y hx hy

/-- Packed `-x` on canonical lanes has canonical lanes, lane `i` being the scalar `-x[i]`. -/
theorem x86_64_avx2.PackedBabyBearAVX2.neg.lanewise (x : PackedBabyBearAVX2)
    (hx : ∀ i : Fin 8, Canonical (toVector x)[i]) :
    CoreOpsArithNegPackedMontyField31AVX2.neg BabyBearPackedParams x
      ⦃ z => (∀ i : Fin 8, Canonical (toVector z)[i]) ∧ ∀ i : Fin 8,
        p3_monty_31.monty_31.MontyField31.Insts.CoreOpsArithNegMontyField31.neg
          FieldParams (toVector x)[i] = .ok (toVector z)[i] ⦄ :=
  Proofs.P3BabyBear.Avx2.neg.lanewise x hx

/-- `halve_avx2(v)`, which `PackedBabyBearAVX2::halve` passes to `from_vector`, on a vector with
canonical lanes: its lanes are canonical, and lane `i` is the scalar `halve` of lane `i`. -/
theorem x86_64_avx2.halve_avx2.lanewise (v : M256i) (hv : FromVectorSafe BabyBear.fieldSize v) :
    p3_monty_31_avx2.x86_64_avx2.utils.halve_avx2 BabyBearMontyParamsAvx2 v
      ⦃ r => FromVectorSafe BabyBear.fieldSize r ∧ ∀ i : Fin 8,
        p3_monty_31.monty_31.MontyField31.Insts.P3_fieldFieldPrimeCharacteristicRing.halve
          FieldParams ⟨lane v i, ()⟩ = .ok ⟨lane r i, ()⟩ ⦄ :=
  Proofs.P3BabyBear.Avx2.halve_avx2.lanewise v hv

/-! ## As field elements -/

/-- Packed `x + y` is lane-wise addition in `BabyBear.Field`. -/
theorem x86_64_avx2.PackedBabyBearAVX2.add.toField (x y : PackedBabyBearAVX2)
    (hx : ∀ i : Fin 8, Canonical (toVector x)[i]) (hy : ∀ i : Fin 8, Canonical (toVector y)[i]) :
    CoreOpsArithAddPackedMontyField31AVX2PackedMontyField31AVX2.add BabyBearPackedParams x y
      ⦃ z => ∀ i : Fin 8, Canonical (toVector z)[i] ∧
        toField (toVector z)[i] = toField (toVector x)[i] + toField (toVector y)[i] ⦄ :=
  Proofs.P3BabyBear.Avx2.add.toField x y hx hy

/-- Packed `x - y` is lane-wise subtraction in `BabyBear.Field`. -/
theorem x86_64_avx2.PackedBabyBearAVX2.sub.toField (x y : PackedBabyBearAVX2)
    (hx : ∀ i : Fin 8, Canonical (toVector x)[i]) (hy : ∀ i : Fin 8, Canonical (toVector y)[i]) :
    CoreOpsArithSubPackedMontyField31AVX2PackedMontyField31AVX2.sub BabyBearPackedParams x y
      ⦃ z => ∀ i : Fin 8, Canonical (toVector z)[i] ∧
        toField (toVector z)[i] = toField (toVector x)[i] - toField (toVector y)[i] ⦄ :=
  Proofs.P3BabyBear.Avx2.sub.toField x y hx hy

/-- Packed `x * y` is lane-wise multiplication in `BabyBear.Field`. -/
theorem x86_64_avx2.PackedBabyBearAVX2.mul.toField (x y : PackedBabyBearAVX2)
    (hx : ∀ i : Fin 8, Canonical (toVector x)[i]) (hy : ∀ i : Fin 8, Canonical (toVector y)[i]) :
    CoreOpsArithMulPackedMontyField31AVX2PackedMontyField31AVX2.mul BabyBearPackedParams x y
      ⦃ z => ∀ i : Fin 8, Canonical (toVector z)[i] ∧
        toField (toVector z)[i] = toField (toVector x)[i] * toField (toVector y)[i] ⦄ :=
  Proofs.P3BabyBear.Avx2.mul.toField x y hx hy

/-- Packed `-x` is lane-wise negation in `BabyBear.Field`. -/
theorem x86_64_avx2.PackedBabyBearAVX2.neg.toField (x : PackedBabyBearAVX2)
    (hx : ∀ i : Fin 8, Canonical (toVector x)[i]) :
    CoreOpsArithNegPackedMontyField31AVX2.neg BabyBearPackedParams x
      ⦃ z => ∀ i : Fin 8, Canonical (toVector z)[i] ∧
        toField (toVector z)[i] = -toField (toVector x)[i] ⦄ :=
  Proofs.P3BabyBear.Avx2.neg.toField x hx

/-- `halve_avx2(v)` is lane-wise halving in `BabyBear.Field`. -/
theorem x86_64_avx2.halve_avx2.toField (v : M256i) (hv : FromVectorSafe BabyBear.fieldSize v) :
    p3_monty_31_avx2.x86_64_avx2.utils.halve_avx2 BabyBearMontyParamsAvx2 v
      ⦃ r => FromVectorSafe BabyBear.fieldSize r ∧ ∀ i : Fin 8,
        toField ⟨lane r i, ()⟩ * 2 = toField ⟨lane v i, ()⟩ ⦄ :=
  Proofs.P3BabyBear.Avx2.halve_avx2.toField v hv

/-! ## `from_vector`'s safety condition

`from_vector` is `unsafe`: "each element of vector must be in `0..P`". Each operator's last
call is `from_vector(v)`; on canonical inputs that `v` meets the condition. (`from_vector`
transmutes, so the vector is determined by the result.) For `halve`, the vector is
`halve_avx2`'s result, which `x86_64_avx2.halve_avx2.lanewise` covers. -/

theorem x86_64_avx2.PackedBabyBearAVX2.add.from_vector_arg (x y : PackedBabyBearAVX2)
    (hx : ∀ i : Fin 8, Canonical (toVector x)[i]) (hy : ∀ i : Fin 8, Canonical (toVector y)[i]) :
    ∃ v, FromVectorSafe BabyBear.fieldSize v ∧
      CoreOpsArithAddPackedMontyField31AVX2PackedMontyField31AVX2.add BabyBearPackedParams x y =
        p3_monty_31_avx2.x86_64_avx2.packing.PackedMontyField31AVX2.from_vector
          BabyBearPackedParams v :=
  Proofs.P3BabyBear.Avx2.add.from_vector_arg x y hx hy

theorem x86_64_avx2.PackedBabyBearAVX2.sub.from_vector_arg (x y : PackedBabyBearAVX2)
    (hx : ∀ i : Fin 8, Canonical (toVector x)[i]) (hy : ∀ i : Fin 8, Canonical (toVector y)[i]) :
    ∃ v, FromVectorSafe BabyBear.fieldSize v ∧
      CoreOpsArithSubPackedMontyField31AVX2PackedMontyField31AVX2.sub BabyBearPackedParams x y =
        p3_monty_31_avx2.x86_64_avx2.packing.PackedMontyField31AVX2.from_vector
          BabyBearPackedParams v :=
  Proofs.P3BabyBear.Avx2.sub.from_vector_arg x y hx hy

theorem x86_64_avx2.PackedBabyBearAVX2.mul.from_vector_arg (x y : PackedBabyBearAVX2)
    (hx : ∀ i : Fin 8, Canonical (toVector x)[i]) (hy : ∀ i : Fin 8, Canonical (toVector y)[i]) :
    ∃ v, FromVectorSafe BabyBear.fieldSize v ∧
      CoreOpsArithMulPackedMontyField31AVX2PackedMontyField31AVX2.mul BabyBearPackedParams x y =
        p3_monty_31_avx2.x86_64_avx2.packing.PackedMontyField31AVX2.from_vector
          BabyBearPackedParams v :=
  Proofs.P3BabyBear.Avx2.mul.from_vector_arg x y hx hy

theorem x86_64_avx2.PackedBabyBearAVX2.neg.from_vector_arg (x : PackedBabyBearAVX2)
    (hx : ∀ i : Fin 8, Canonical (toVector x)[i]) :
    ∃ v, FromVectorSafe BabyBear.fieldSize v ∧
      CoreOpsArithNegPackedMontyField31AVX2.neg BabyBearPackedParams x =
        p3_monty_31_avx2.x86_64_avx2.packing.PackedMontyField31AVX2.from_vector
          BabyBearPackedParams v :=
  Proofs.P3BabyBear.Avx2.neg.from_vector_arg x hx

/-! ## Dot products

`PackedField::dot_product::<N>` dispatches to the kernels `dot_product_2` and `dot_product_4` to
`dot_product_8`, each followed by `from_vector`. On packed inputs whose lanes are canonical, each
kernel never fails, returns a vector with canonical lanes (`from_vector`'s safety condition), and
lane `i` stands for `Σ_k lhs[k]_i · rhs[k]_i` in `BabyBear.Field`. Each sums 64-bit products and
reduces once; the proofs check the sums' bounds for any `p < 2^31`. The `IntoM256` dictionary is
the one of `PackedMontyField31AVX2`'s impl (`IsPackedInto`). -/

/-- `dot_product_2(lhs, rhs)` on packed inputs with canonical lanes: lane `i` is
`Σ_k lhs[k]_i · rhs[k]_i`. -/
theorem x86_64_avx2.dot_product_2.toField
    (iI : p3_monty_31_avx2.x86_64_avx2.packing.IntoM256 PackedBabyBearAVX2
      p3_baby_bear.baby_bear.BabyBearParameters)
    (hI : IsPackedInto iI BabyBearPackedParams) (lhs rhs : Std.Array PackedBabyBearAVX2 2#usize)
    (hl : ∀ k : Fin 2, ∀ i : Fin 8, Canonical (toVector (lhs.val[k.val]'(by simp; omega)))[i])
    (hr : ∀ k : Fin 2, ∀ i : Fin 8, Canonical (toVector (rhs.val[k.val]'(by simp; omega)))[i]) :
    p3_monty_31_avx2.x86_64_avx2.packing.dot_product_2 BabyBearPackedParams iI iI lhs rhs
      ⦃ v => FromVectorSafe BabyBear.fieldSize v ∧ ∀ i : Fin 8,
        toField ⟨lane v i, ()⟩ = ∑ k : Fin 2,
          toField (toVector (lhs.val[k.val]'(by simp; omega)))[i] *
            toField (toVector (rhs.val[k.val]'(by simp; omega)))[i] ⦄ :=
  Proofs.P3BabyBear.Avx2.dot_product_2.toField iI hI lhs rhs hl hr

/-- `dot_product_4(lhs, rhs)` on packed inputs with canonical lanes: lane `i` is
`Σ_k lhs[k]_i · rhs[k]_i`. -/
theorem x86_64_avx2.dot_product_4.toField
    (iI : p3_monty_31_avx2.x86_64_avx2.packing.IntoM256 PackedBabyBearAVX2
      p3_baby_bear.baby_bear.BabyBearParameters)
    (hI : IsPackedInto iI BabyBearPackedParams) (lhs rhs : Std.Array PackedBabyBearAVX2 4#usize)
    (hl : ∀ k : Fin 4, ∀ i : Fin 8, Canonical (toVector (lhs.val[k.val]'(by simp)))[i])
    (hr : ∀ k : Fin 4, ∀ i : Fin 8, Canonical (toVector (rhs.val[k.val]'(by simp)))[i]) :
    p3_monty_31_avx2.x86_64_avx2.packing.dot_product_4 BabyBearPackedParams iI iI lhs rhs
      ⦃ v => FromVectorSafe BabyBear.fieldSize v ∧ ∀ i : Fin 8,
        toField ⟨lane v i, ()⟩ = ∑ k : Fin 4,
          toField (toVector (lhs.val[k.val]'(by simp)))[i] *
            toField (toVector (rhs.val[k.val]'(by simp)))[i] ⦄ :=
  Proofs.P3BabyBear.Avx2.dot_product_4.toField iI hI lhs rhs hl hr

/-- `dot_product_5(lhs, rhs)` on packed inputs with canonical lanes: lane `i` is
`Σ_k lhs[k]_i · rhs[k]_i`. -/
theorem x86_64_avx2.dot_product_5.toField
    (iI : p3_monty_31_avx2.x86_64_avx2.packing.IntoM256 PackedBabyBearAVX2
      p3_baby_bear.baby_bear.BabyBearParameters)
    (hI : IsPackedInto iI BabyBearPackedParams) (lhs rhs : Std.Array PackedBabyBearAVX2 5#usize)
    (hl : ∀ k : Fin 5, ∀ i : Fin 8, Canonical (toVector (lhs.val[k.val]'(by simp)))[i])
    (hr : ∀ k : Fin 5, ∀ i : Fin 8, Canonical (toVector (rhs.val[k.val]'(by simp)))[i]) :
    p3_monty_31_avx2.x86_64_avx2.packing.dot_product_5 BabyBearPackedParams iI iI lhs rhs
      ⦃ v => FromVectorSafe BabyBear.fieldSize v ∧ ∀ i : Fin 8,
        toField ⟨lane v i, ()⟩ = ∑ k : Fin 5,
          toField (toVector (lhs.val[k.val]'(by simp)))[i] *
            toField (toVector (rhs.val[k.val]'(by simp)))[i] ⦄ :=
  Proofs.P3BabyBear.Avx2.dot_product_5.toField iI hI lhs rhs hl hr

/-- `dot_product_6(lhs, rhs)` on packed inputs with canonical lanes: lane `i` is
`Σ_k lhs[k]_i · rhs[k]_i`. -/
theorem x86_64_avx2.dot_product_6.toField
    (iI : p3_monty_31_avx2.x86_64_avx2.packing.IntoM256 PackedBabyBearAVX2
      p3_baby_bear.baby_bear.BabyBearParameters)
    (hI : IsPackedInto iI BabyBearPackedParams) (lhs rhs : Std.Array PackedBabyBearAVX2 6#usize)
    (hl : ∀ k : Fin 6, ∀ i : Fin 8, Canonical (toVector (lhs.val[k.val]'(by simp)))[i])
    (hr : ∀ k : Fin 6, ∀ i : Fin 8, Canonical (toVector (rhs.val[k.val]'(by simp)))[i]) :
    p3_monty_31_avx2.x86_64_avx2.packing.dot_product_6 BabyBearPackedParams iI iI lhs rhs
      ⦃ v => FromVectorSafe BabyBear.fieldSize v ∧ ∀ i : Fin 8,
        toField ⟨lane v i, ()⟩ = ∑ k : Fin 6,
          toField (toVector (lhs.val[k.val]'(by simp)))[i] *
            toField (toVector (rhs.val[k.val]'(by simp)))[i] ⦄ :=
  Proofs.P3BabyBear.Avx2.dot_product_6.toField iI hI lhs rhs hl hr

/-- `dot_product_7(lhs, rhs)` on packed inputs with canonical lanes: lane `i` is
`Σ_k lhs[k]_i · rhs[k]_i`. -/
theorem x86_64_avx2.dot_product_7.toField
    (iI : p3_monty_31_avx2.x86_64_avx2.packing.IntoM256 PackedBabyBearAVX2
      p3_baby_bear.baby_bear.BabyBearParameters)
    (hI : IsPackedInto iI BabyBearPackedParams) (lhs rhs : Std.Array PackedBabyBearAVX2 7#usize)
    (hl : ∀ k : Fin 7, ∀ i : Fin 8, Canonical (toVector (lhs.val[k.val]'(by simp)))[i])
    (hr : ∀ k : Fin 7, ∀ i : Fin 8, Canonical (toVector (rhs.val[k.val]'(by simp)))[i]) :
    p3_monty_31_avx2.x86_64_avx2.packing.dot_product_7 BabyBearPackedParams iI iI lhs rhs
      ⦃ v => FromVectorSafe BabyBear.fieldSize v ∧ ∀ i : Fin 8,
        toField ⟨lane v i, ()⟩ = ∑ k : Fin 7,
          toField (toVector (lhs.val[k.val]'(by simp)))[i] *
            toField (toVector (rhs.val[k.val]'(by simp)))[i] ⦄ :=
  Proofs.P3BabyBear.Avx2.dot_product_7.toField iI hI lhs rhs hl hr

/-- `dot_product_8(lhs, rhs)` on packed inputs with canonical lanes: lane `i` is
`Σ_k lhs[k]_i · rhs[k]_i`. -/
theorem x86_64_avx2.dot_product_8.toField
    (iI : p3_monty_31_avx2.x86_64_avx2.packing.IntoM256 PackedBabyBearAVX2
      p3_baby_bear.baby_bear.BabyBearParameters)
    (hI : IsPackedInto iI BabyBearPackedParams) (lhs rhs : Std.Array PackedBabyBearAVX2 8#usize)
    (hl : ∀ k : Fin 8, ∀ i : Fin 8, Canonical (toVector (lhs.val[k.val]'(by simp)))[i])
    (hr : ∀ k : Fin 8, ∀ i : Fin 8, Canonical (toVector (rhs.val[k.val]'(by simp)))[i]) :
    p3_monty_31_avx2.x86_64_avx2.packing.dot_product_8 BabyBearPackedParams iI iI lhs rhs
      ⦃ v => FromVectorSafe BabyBear.fieldSize v ∧ ∀ i : Fin 8,
        toField ⟨lane v i, ()⟩ = ∑ k : Fin 8,
          toField (toVector (lhs.val[k.val]'(by simp)))[i] *
            toField (toVector (rhs.val[k.val]'(by simp)))[i] ⦄ :=
  Proofs.P3BabyBear.Avx2.dot_product_8.toField iI hI lhs rhs hl hr

end Plonky3Lean.Claims.P3BabyBear
