module

public import Plonky3Lean.Spec.Monty31
public import Plonky3Lean.Spec.BabyBear
public import P3Monty31Avx2
public import P3BabyBearAvx2

@[expose] public section

/-!
# Packed Monty31: what a `PackedMontyField31AVX2` means

p3-monty-31's AVX2 backend packs eight `MontyField31` into one `__m256i`. Its model is
the `P3Monty31Avx2` variant (`crates/monty-31/variants/x86_64-avx2`), in the namespace
`p3_monty_31_avx2`; its `MontyField31` is P3Monty31's, so a lane is an element exactly as
`Plonky3Lean.Spec.Monty31` reads one.

* **A packed value.** `toVector` reads a `PackedMontyField31AVX2<MP>` as the `Vector` of its
  eight elements, lane `i` at index `i`. `Canonical` says every lane is canonical.
* **A vector.** `lane v i` is lane `i` of an `__m256i` (p3-arch-shims' eight `u32`s).
  `FromVectorSafe p v` is the safety condition of `PackedMontyField31AVX2::from_vector`: every
  lane is in `0..p`.
* **The parameters.** The variant re-declares p3-monty-31's parameter traits (on x86_64
  `PackedMontyParameters` has the supertrait `MontyParametersAVX2`), so its `MontyParameters`
  dictionary is a different record from P3Monty31's, with the same members. `toPortable` reads
  it as the portable one. `Valid` is `Monty31.Valid` of that reading, plus `PACKED_P` and
  `PACKED_MU` being `PRIME` and `MONTY_MU` in every lane.
* **BabyBear's names.** `PackedBabyBearAVX2` is the packed BabyBear type, and
  `BabyBearPackedParams` and `BabyBearMontyParamsAvx2` the dictionaries the baby-bear variant
  (`P3BabyBearAvx2`, `crates/baby-bear/variants/x86_64-avx2`) extracts for
  `BabyBearParameters`. Each is an alias of a generated name and adds nothing to it.
-/

open Aeneas Aeneas.Std CoreModels

namespace Plonky3Lean.Spec.Packed

/-- Rust's `PackedMontyField31AVX2<MP>`: eight `MontyField31<MP>`. -/
abbrev PackedAvx2 (MP : Type) := p3_monty_31_avx2.x86_64_avx2.packing.PackedMontyField31AVX2 MP

/-- An `__m256i`, as p3-arch-shims models it: eight `u32` lanes. -/
abbrev M256i := p3_arch_shims.x86_64.types.M256i

/-- A packed value as the vector of its lanes. -/
def toVector {MP : Type} (x : PackedAvx2 MP) : Vector (Monty31.Element MP) 8 :=
  ⟨x.val.toArray, by simp⟩

/-- Every lane of a packed value is canonical, `< p`. -/
def Canonical {MP : Type} (p : ℕ) (x : PackedAvx2 MP) : Prop :=
  ∀ i : Fin 8, Monty31.Canonical p (toVector x)[i]

/-- Lane `i` of an `__m256i`. -/
def lane (v : M256i) (i : Fin 8) : Std.U32 :=
  v.val[i.val]!

/-- The safety condition of `PackedMontyField31AVX2::from_vector`: "each element of vector
must be in `0..P` (canonical form)". -/
def FromVectorSafe (p : ℕ) (v : M256i) : Prop :=
  ∀ i : Fin 8, (lane v i).val < p

/-- The variant's `MontyParameters` dictionary, read as P3Monty31's: the same members. -/
def toPortable {MP : Type} (inst : p3_monty_31_avx2.data_traits.MontyParameters MP) :
    p3_monty_31.data_traits.MontyParameters MP where
  PRIME := inst.PRIME
  MONTY_BITS := inst.MONTY_BITS
  MONTY_MU := inst.MONTY_MU
  MONTY_MASK := inst.MONTY_MASK
  coremarkerCopyInst := inst.coremarkerCopyInst
  coredefaultDefaultInst := inst.coredefaultDefaultInst
  corefmtDebugInst := inst.corefmtDebugInst
  corecmpEqInst := inst.corecmpEqInst
  corecmpPartialEqInst := inst.corecmpPartialEqInst
  corehashHashInst := inst.corehashHashInst

/-- The parameters of a `PackedMontyParameters` impl on x86_64 with AVX2: valid
`MontyParameters` (`Monty31.Valid`, through `toPortable`), and `PACKED_P` and `PACKED_MU`
holding `p = PRIME` and `mu = MONTY_MU` in every lane, which `MontyParametersAVX2` documents
and nothing checks. -/
structure Valid {MP : Type} (inst : p3_monty_31_avx2.data_traits.PackedMontyParameters MP)
    (p mu : Std.U32) : Prop where
  monty : Monty31.Valid (toPortable inst.MontyParametersInst) p mu
  packed_p : ∃ v, inst.x86_64_avx2packingMontyParametersAVX2Inst.PACKED_P = .ok v ∧
    ∀ i, lane v i = p
  packed_mu : ∃ v, inst.x86_64_avx2packingMontyParametersAVX2Inst.PACKED_MU = .ok v ∧
    ∀ i, lane v i = mu

/-! ## BabyBear -/

/-- Rust's `PackedBabyBearAVX2 = PackedMontyField31AVX2<BabyBearParameters>`. -/
abbrev PackedBabyBearAVX2 := PackedAvx2 p3_baby_bear.baby_bear.BabyBearParameters

/-- The `PackedMontyParameters` dictionary the baby-bear variant extracts for
`BabyBearParameters` on x86_64 with AVX2: its `MontyParameters` and its `MontyParametersAVX2`
(`PACKED_P`, `PACKED_MU`, `baby-bear/src/x86_64_avx2/packing.rs`). -/
noncomputable abbrev BabyBearPackedParams :=
  p3_baby_bear_avx2.baby_bear.BabyBearParameters.Insts.P3_monty_31Data_traitsPackedMontyParameters

/-- Its `MontyParameters` dictionary, in the monty-31 variant's record. -/
noncomputable abbrev BabyBearMontyParamsAvx2 :=
  p3_baby_bear_avx2.baby_bear.BabyBearParameters.Insts.P3_monty_31Data_traitsMontyParameters

end Plonky3Lean.Spec.Packed
