module

public import Plonky3Lean.Proofs.Field.BabyBear.Neon

@[expose] public section

/-!
# BabyBear on AArch64 with NEON: claims

What this repository asserts about `PackedBabyBearNeon`, p3-monty-31's
`PackedMontyField31Neon<BabyBearParameters>`, at the Plonky3 commit pinned in `plonky3/`.
The model is the aarch64-neon variants of p3-monty-31 (`crates/monty-31/variants/aarch64-neon`,
namespace `p3_monty_31_neon`) and p3-baby-bear (`crates/baby-bear/variants/aarch64-neon`,
`p3_baby_bear_neon`), extracted against the intrinsic models of `arch/` (`P3ArchShims`), with
`confuse_compiler` the identity (pre-patch `monty-31/030`). `toVector`, `lane`,
`FromVectorSafe` and the dictionary names are `Plonky3Lean.Spec.Packed.Neon`'s; `Canonical`,
`toField` and the scalar dictionaries `MontyParams` and `FieldParams` are
`Plonky3Lean.Spec.BabyBear`'s, so a lane is read exactly as a scalar `BabyBear` is, and
`BabyBear.Field` is CompPoly's specification of the field.

For packed inputs whose lanes are canonical, `Add`, `Sub`, `Mul` and `Neg`:

* never fail, and end in a call `from_vector(v)` whose `v` has canonical lanes, which is the
  safety condition `from_vector` documents (`*.from_vector_arg`);
* give a result whose lanes are canonical, lane `i` being what the portable scalar operator
  returns on lane `i` of the inputs (`*.lanewise`);
* and so, by the scalar claims, stand lane by lane for the field operation (`*.toField`).

`Mul` is NEON's signed Montgomery multiplication (`vqdmulhq_s32`); its arithmetic is proved for
any valid parameters in `Plonky3Lean.Proofs.Neon.monty_signed`.

`PackedMontyField31Neon::halve` is not in the model; `halve_neon`, the vector it passes to
`from_vector`, is, and is claimed on the lanes of a `uint32x4_t`.

Not claimed: the impls whose right operand is a scalar `MontyField31` (they `broadcast` it
first), the assigning operators, `halve` itself and the rest of `PrimeCharacteristicRing` and
`PackedField` (`cube`, `exp_const`, `dot_product`, interleaving, the packed Poseidon layers),
the intrinsic models themselves (trusted, and tested against the hardware in `arch/tests/`),
`confuse_compiler`'s stand-in, and the `transmute` layout assumptions `to_vector`,
`to_signed_vector` and `from_vector` rest on (`STATUS.md`).
-/

open Aeneas Aeneas.Std CoreModels
open Plonky3Lean.Spec.Packed.Neon
open Plonky3Lean.Spec.BabyBear (MontyParams FieldParams Canonical toField)
open p3_monty_31_neon.aarch64_neon.packing.PackedMontyField31Neon.Insts

namespace Plonky3Lean.Claims.P3BabyBear

/-! ## BabyBear's NEON parameters

The baby-bear variant re-extracts `BabyBearParameters`' `MontyParameters` dictionary into the
monty-31 variant's record; read as P3Monty31's record it is the scalar `MontyParams`. Its
`MontyParametersNeon` constants hold `PRIME` and `MONTY_MU` in every lane. -/

/-- The bridge: the NEON build's `MontyParameters` dictionary for `BabyBearParameters` is the
scalar one, member for member. -/
theorem aarch64_neon.BabyBearParameters.MontyParameters.toPortable :
    toPortable BabyBearMontyParamsNeon = MontyParams :=
  Proofs.P3BabyBear.Neon.BabyBearMontyParamsNeon.toPortable

/-- `PACKED_P` is `PRIME = 2013265921` in every lane, `PACKED_MU` is `MONTY_MU = 2281701377` in
every lane read as a `u32`, and BabyBear's `MontyParameters` are valid. -/
theorem aarch64_neon.BabyBearParameters.valid :
    Valid BabyBearPackedParams 2013265921#u32 2281701377#u32 :=
  Proofs.P3BabyBear.Neon.packedValid

/-! ## Lane `i` is the scalar operator on lane `i` -/

/-- Packed `x + y` on canonical lanes has canonical lanes, lane `i` being the scalar
`x[i] + y[i]`. -/
theorem aarch64_neon.PackedBabyBearNeon.add.lanewise (x y : PackedBabyBearNeon)
    (hx : ∀ i : Fin 4, Canonical (toVector x)[i]) (hy : ∀ i : Fin 4, Canonical (toVector y)[i]) :
    CoreOpsArithAddPackedMontyField31NeonPackedMontyField31Neon.add BabyBearPackedParams x y
      ⦃ z => (∀ i : Fin 4, Canonical (toVector z)[i]) ∧ ∀ i : Fin 4,
        p3_monty_31.monty_31.MontyField31.Insts.CoreOpsArithAddMontyField31MontyField31.add
          MontyParams (toVector x)[i] (toVector y)[i] = .ok (toVector z)[i] ⦄ :=
  Proofs.P3BabyBear.Neon.add.lanewise x y hx hy

/-- Packed `x - y` on canonical lanes has canonical lanes, lane `i` being the scalar
`x[i] - y[i]`. -/
theorem aarch64_neon.PackedBabyBearNeon.sub.lanewise (x y : PackedBabyBearNeon)
    (hx : ∀ i : Fin 4, Canonical (toVector x)[i]) (hy : ∀ i : Fin 4, Canonical (toVector y)[i]) :
    CoreOpsArithSubPackedMontyField31NeonPackedMontyField31Neon.sub BabyBearPackedParams x y
      ⦃ z => (∀ i : Fin 4, Canonical (toVector z)[i]) ∧ ∀ i : Fin 4,
        p3_monty_31.monty_31.MontyField31.Insts.CoreOpsArithSubMontyField31MontyField31.sub
          MontyParams (toVector x)[i] (toVector y)[i] = .ok (toVector z)[i] ⦄ :=
  Proofs.P3BabyBear.Neon.sub.lanewise x y hx hy

/-- Packed `x * y` on canonical lanes has canonical lanes, lane `i` being the scalar
`x[i] * y[i]`: the vector Montgomery multiplication, with its signed intermediate, agrees with
the scalar one. -/
theorem aarch64_neon.PackedBabyBearNeon.mul.lanewise (x y : PackedBabyBearNeon)
    (hx : ∀ i : Fin 4, Canonical (toVector x)[i]) (hy : ∀ i : Fin 4, Canonical (toVector y)[i]) :
    CoreOpsArithMulPackedMontyField31NeonPackedMontyField31Neon.mul BabyBearPackedParams x y
      ⦃ z => (∀ i : Fin 4, Canonical (toVector z)[i]) ∧ ∀ i : Fin 4,
        p3_monty_31.monty_31.MontyField31.Insts.CoreOpsArithMulMontyField31MontyField31.mul
          MontyParams (toVector x)[i] (toVector y)[i] = .ok (toVector z)[i] ⦄ :=
  Proofs.P3BabyBear.Neon.mul.lanewise x y hx hy

/-- Packed `-x` on canonical lanes has canonical lanes, lane `i` being the scalar `-x[i]`. -/
theorem aarch64_neon.PackedBabyBearNeon.neg.lanewise (x : PackedBabyBearNeon)
    (hx : ∀ i : Fin 4, Canonical (toVector x)[i]) :
    CoreOpsArithNegPackedMontyField31Neon.neg BabyBearPackedParams x
      ⦃ z => (∀ i : Fin 4, Canonical (toVector z)[i]) ∧ ∀ i : Fin 4,
        p3_monty_31.monty_31.MontyField31.Insts.CoreOpsArithNegMontyField31.neg
          FieldParams (toVector x)[i] = .ok (toVector z)[i] ⦄ :=
  Proofs.P3BabyBear.Neon.neg.lanewise x hx

/-- `halve_neon(v)`, which `PackedBabyBearNeon::halve` passes to `from_vector`, on a vector with
canonical lanes: its lanes are canonical, and lane `i` is the scalar `halve` of lane `i`. -/
theorem aarch64_neon.halve_neon.lanewise (v : U32x4) (hv : FromVectorSafe BabyBear.fieldSize v) :
    p3_monty_31_neon.aarch64_neon.utils.halve_neon BabyBearPackedParams v
      ⦃ r => FromVectorSafe BabyBear.fieldSize r ∧ ∀ i : Fin 4,
        p3_monty_31.monty_31.MontyField31.Insts.P3_fieldFieldPrimeCharacteristicRing.halve
          FieldParams ⟨lane v i, ()⟩ = .ok ⟨lane r i, ()⟩ ⦄ :=
  Proofs.P3BabyBear.Neon.halve_neon.lanewise v hv

/-! ## As field elements -/

/-- Packed `x + y` is lane-wise addition in `BabyBear.Field`. -/
theorem aarch64_neon.PackedBabyBearNeon.add.toField (x y : PackedBabyBearNeon)
    (hx : ∀ i : Fin 4, Canonical (toVector x)[i]) (hy : ∀ i : Fin 4, Canonical (toVector y)[i]) :
    CoreOpsArithAddPackedMontyField31NeonPackedMontyField31Neon.add BabyBearPackedParams x y
      ⦃ z => ∀ i : Fin 4, Canonical (toVector z)[i] ∧
        toField (toVector z)[i] = toField (toVector x)[i] + toField (toVector y)[i] ⦄ :=
  Proofs.P3BabyBear.Neon.add.toField x y hx hy

/-- Packed `x - y` is lane-wise subtraction in `BabyBear.Field`. -/
theorem aarch64_neon.PackedBabyBearNeon.sub.toField (x y : PackedBabyBearNeon)
    (hx : ∀ i : Fin 4, Canonical (toVector x)[i]) (hy : ∀ i : Fin 4, Canonical (toVector y)[i]) :
    CoreOpsArithSubPackedMontyField31NeonPackedMontyField31Neon.sub BabyBearPackedParams x y
      ⦃ z => ∀ i : Fin 4, Canonical (toVector z)[i] ∧
        toField (toVector z)[i] = toField (toVector x)[i] - toField (toVector y)[i] ⦄ :=
  Proofs.P3BabyBear.Neon.sub.toField x y hx hy

/-- Packed `x * y` is lane-wise multiplication in `BabyBear.Field`. -/
theorem aarch64_neon.PackedBabyBearNeon.mul.toField (x y : PackedBabyBearNeon)
    (hx : ∀ i : Fin 4, Canonical (toVector x)[i]) (hy : ∀ i : Fin 4, Canonical (toVector y)[i]) :
    CoreOpsArithMulPackedMontyField31NeonPackedMontyField31Neon.mul BabyBearPackedParams x y
      ⦃ z => ∀ i : Fin 4, Canonical (toVector z)[i] ∧
        toField (toVector z)[i] = toField (toVector x)[i] * toField (toVector y)[i] ⦄ :=
  Proofs.P3BabyBear.Neon.mul.toField x y hx hy

/-- Packed `-x` is lane-wise negation in `BabyBear.Field`. -/
theorem aarch64_neon.PackedBabyBearNeon.neg.toField (x : PackedBabyBearNeon)
    (hx : ∀ i : Fin 4, Canonical (toVector x)[i]) :
    CoreOpsArithNegPackedMontyField31Neon.neg BabyBearPackedParams x
      ⦃ z => ∀ i : Fin 4, Canonical (toVector z)[i] ∧
        toField (toVector z)[i] = -toField (toVector x)[i] ⦄ :=
  Proofs.P3BabyBear.Neon.neg.toField x hx

/-- `halve_neon(v)` is lane-wise halving in `BabyBear.Field`. -/
theorem aarch64_neon.halve_neon.toField (v : U32x4) (hv : FromVectorSafe BabyBear.fieldSize v) :
    p3_monty_31_neon.aarch64_neon.utils.halve_neon BabyBearPackedParams v
      ⦃ r => FromVectorSafe BabyBear.fieldSize r ∧ ∀ i : Fin 4,
        toField ⟨lane r i, ()⟩ * 2 = toField ⟨lane v i, ()⟩ ⦄ :=
  Proofs.P3BabyBear.Neon.halve_neon.toField v hv

/-! ## `from_vector`'s safety condition

`from_vector` is `unsafe`: "each element of vector must be in `0..P`". Each operator's last
call is `from_vector(v)`; on canonical inputs that `v` meets the condition. (`from_vector`
transmutes, so the vector is determined by the result.) For `halve`, the vector is
`halve_neon`'s result, which `aarch64_neon.halve_neon.lanewise` covers. -/

theorem aarch64_neon.PackedBabyBearNeon.add.from_vector_arg (x y : PackedBabyBearNeon)
    (hx : ∀ i : Fin 4, Canonical (toVector x)[i]) (hy : ∀ i : Fin 4, Canonical (toVector y)[i]) :
    ∃ v, FromVectorSafe BabyBear.fieldSize v ∧
      CoreOpsArithAddPackedMontyField31NeonPackedMontyField31Neon.add BabyBearPackedParams x y =
        p3_monty_31_neon.aarch64_neon.packing.PackedMontyField31Neon.from_vector
          BabyBearPackedParams v :=
  Proofs.P3BabyBear.Neon.add.from_vector_arg x y hx hy

theorem aarch64_neon.PackedBabyBearNeon.sub.from_vector_arg (x y : PackedBabyBearNeon)
    (hx : ∀ i : Fin 4, Canonical (toVector x)[i]) (hy : ∀ i : Fin 4, Canonical (toVector y)[i]) :
    ∃ v, FromVectorSafe BabyBear.fieldSize v ∧
      CoreOpsArithSubPackedMontyField31NeonPackedMontyField31Neon.sub BabyBearPackedParams x y =
        p3_monty_31_neon.aarch64_neon.packing.PackedMontyField31Neon.from_vector
          BabyBearPackedParams v :=
  Proofs.P3BabyBear.Neon.sub.from_vector_arg x y hx hy

theorem aarch64_neon.PackedBabyBearNeon.mul.from_vector_arg (x y : PackedBabyBearNeon)
    (hx : ∀ i : Fin 4, Canonical (toVector x)[i]) (hy : ∀ i : Fin 4, Canonical (toVector y)[i]) :
    ∃ v, FromVectorSafe BabyBear.fieldSize v ∧
      CoreOpsArithMulPackedMontyField31NeonPackedMontyField31Neon.mul BabyBearPackedParams x y =
        p3_monty_31_neon.aarch64_neon.packing.PackedMontyField31Neon.from_vector
          BabyBearPackedParams v :=
  Proofs.P3BabyBear.Neon.mul.from_vector_arg x y hx hy

theorem aarch64_neon.PackedBabyBearNeon.neg.from_vector_arg (x : PackedBabyBearNeon)
    (hx : ∀ i : Fin 4, Canonical (toVector x)[i]) :
    ∃ v, FromVectorSafe BabyBear.fieldSize v ∧
      CoreOpsArithNegPackedMontyField31Neon.neg BabyBearPackedParams x =
        p3_monty_31_neon.aarch64_neon.packing.PackedMontyField31Neon.from_vector
          BabyBearPackedParams v :=
  Proofs.P3BabyBear.Neon.neg.from_vector_arg x hx

end Plonky3Lean.Claims.P3BabyBear
