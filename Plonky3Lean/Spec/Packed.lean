module

public import Plonky3Lean.Spec.Monty31
public import Plonky3Lean.Spec.BabyBear
public import P3Monty31Avx2
public import P3BabyBearAvx2
public import P3Monty31Neon
public import P3BabyBearNeon
public import P3Monty31Avx512
public import P3BabyBearAvx512

@[expose] public section

/-!
# Packed Monty31: what an AVX2, NEON or AVX-512 `PackedMontyField31` means

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

The NEON backend's readings, at width 4, are in `Neon`, and the AVX-512 backend's, at width
16, in `Avx512` (below).
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

/-! ## NEON

p3-monty-31's NEON backend packs four `MontyField31` into one `uint32x4_t`, and its
multiplication reads them as an `int32x4_t`. Its model is the `P3Monty31Neon` variant
(`crates/monty-31/variants/aarch64-neon`), in the namespace `p3_monty_31_neon`; its
`MontyField31` is P3Monty31's. The readings are those above at width 4, in the namespace
`Plonky3Lean.Spec.Packed.Neon`. `Valid` differs in `PACKED_MU`, which is an `int32x4_t`
holding `MONTY_MU`'s bits: its lanes, read as `u32`, are `MONTY_MU`. -/

namespace Neon

/-- Rust's `PackedMontyField31Neon<MP>`: four `MontyField31<MP>`. -/
abbrev PackedNeon (MP : Type) := p3_monty_31_neon.aarch64_neon.packing.PackedMontyField31Neon MP

/-- A `uint32x4_t`, as p3-arch-shims models it: four `u32` lanes. -/
abbrev U32x4 := p3_arch_shims.aarch64.types.U32x4

/-- An `int32x4_t`, as p3-arch-shims models it: four `i32` lanes. -/
abbrev I32x4 := p3_arch_shims.aarch64.types.I32x4

/-- A packed value as the vector of its lanes. -/
def toVector {MP : Type} (x : PackedNeon MP) : Vector (Monty31.Element MP) 4 :=
  ⟨x.val.toArray, by simp⟩

/-- Every lane of a packed value is canonical, `< p`. -/
def Canonical {MP : Type} (p : ℕ) (x : PackedNeon MP) : Prop :=
  ∀ i : Fin 4, Monty31.Canonical p (toVector x)[i]

/-- Lane `i` of a `uint32x4_t`. -/
def lane (v : U32x4) (i : Fin 4) : Std.U32 :=
  v.val[i.val]!

/-- Lane `i` of an `int32x4_t`. -/
def slane (v : I32x4) (i : Fin 4) : Std.I32 :=
  v.val[i.val]!

/-- The safety condition of `PackedMontyField31Neon::from_vector`: "each element of vector
must be in `0..P` (canonical form)". -/
def FromVectorSafe (p : ℕ) (v : U32x4) : Prop :=
  ∀ i : Fin 4, (lane v i).val < p

/-- The variant's `MontyParameters` dictionary, read as P3Monty31's: the same members. -/
def toPortable {MP : Type} (inst : p3_monty_31_neon.data_traits.MontyParameters MP) :
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

/-- The parameters of a `PackedMontyParameters` impl on AArch64: valid `MontyParameters`
(`Monty31.Valid`, through `toPortable`), `PACKED_P` holding `p = PRIME` in every lane, and
`PACKED_MU` holding `mu = MONTY_MU` in every lane, read as a `u32`, which `MontyParametersNeon`
documents and nothing checks. -/
structure Valid {MP : Type} (inst : p3_monty_31_neon.data_traits.PackedMontyParameters MP)
    (p mu : Std.U32) : Prop where
  monty : Monty31.Valid (toPortable inst.MontyParametersInst) p mu
  packed_p : ∃ v, inst.aarch64_neonpackingMontyParametersNeonInst.PACKED_P = .ok v ∧
    ∀ i, lane v i = p
  packed_mu : ∃ v, inst.aarch64_neonpackingMontyParametersNeonInst.PACKED_MU = .ok v ∧
    ∀ i, IScalar.hcast .U32 (slane v i) = mu

/-! ### BabyBear -/

/-- Rust's `PackedBabyBearNeon = PackedMontyField31Neon<BabyBearParameters>`. -/
abbrev PackedBabyBearNeon := PackedNeon p3_baby_bear.baby_bear.BabyBearParameters

/-- The `PackedMontyParameters` dictionary the baby-bear variant extracts for
`BabyBearParameters` on AArch64: its `MontyParameters` and its `MontyParametersNeon`
(`PACKED_P`, `PACKED_MU`, `baby-bear/src/aarch64_neon/packing.rs`). -/
noncomputable abbrev BabyBearPackedParams :=
  p3_baby_bear_neon.baby_bear.BabyBearParameters.Insts.P3_monty_31Data_traitsPackedMontyParameters

/-- Its `MontyParameters` dictionary, in the monty-31 variant's record. -/
noncomputable abbrev BabyBearMontyParamsNeon :=
  p3_baby_bear_neon.baby_bear.BabyBearParameters.Insts.P3_monty_31Data_traitsMontyParameters

end Neon

/-! ## AVX-512

p3-monty-31's AVX-512 backend packs sixteen `MontyField31` into one `__m512i`. Its model is the
`P3Monty31Avx512` variant (`crates/monty-31/variants/x86_64-avx512`), in the namespace
`p3_monty_31_avx512`; its `MontyField31` is P3Monty31's. The readings are AVX2's at width 16,
in the namespace `Plonky3Lean.Spec.Packed.Avx512`. -/

namespace Avx512

/-- Rust's `PackedMontyField31AVX512<MP>`: sixteen `MontyField31<MP>`. -/
abbrev PackedAvx512 (MP : Type) :=
  p3_monty_31_avx512.x86_64_avx512.packing.PackedMontyField31AVX512 MP

/-- An `__m512i`, as p3-arch-shims models it: sixteen `u32` lanes. -/
abbrev M512i := p3_arch_shims.x86_64.types.M512i

/-- A packed value as the vector of its lanes. -/
def toVector {MP : Type} (x : PackedAvx512 MP) : Vector (Monty31.Element MP) 16 :=
  ⟨x.val.toArray, by simp⟩

/-- Every lane of a packed value is canonical, `< p`. -/
def Canonical {MP : Type} (p : ℕ) (x : PackedAvx512 MP) : Prop :=
  ∀ i : Fin 16, Monty31.Canonical p (toVector x)[i]

/-- Lane `i` of an `__m512i`. -/
def lane (v : M512i) (i : Fin 16) : Std.U32 :=
  v.val[i.val]!

/-- Every lane of the vector is canonical, in `0..p`. This implies the safety condition of
`PackedMontyField31AVX512::from_vector`, which documents the weaker "each element of vector must
be in `0..=P`". -/
def FromVectorSafe (p : ℕ) (v : M512i) : Prop :=
  ∀ i : Fin 16, (lane v i).val < p

/-- The variant's `MontyParameters` dictionary, read as P3Monty31's: the same members. -/
def toPortable {MP : Type} (inst : p3_monty_31_avx512.data_traits.MontyParameters MP) :
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

/-- The parameters of a `PackedMontyParameters` impl on x86_64 with AVX-512F: valid
`MontyParameters` (`Monty31.Valid`, through `toPortable`), and `PACKED_P` and `PACKED_MU`
holding `p = PRIME` and `mu = MONTY_MU` in every lane, which `MontyParametersAVX512` documents
and nothing checks. -/
structure Valid {MP : Type} (inst : p3_monty_31_avx512.data_traits.PackedMontyParameters MP)
    (p mu : Std.U32) : Prop where
  monty : Monty31.Valid (toPortable inst.MontyParametersInst) p mu
  packed_p : ∃ v, inst.x86_64_avx512packingMontyParametersAVX512Inst.PACKED_P = .ok v ∧
    ∀ i, lane v i = p
  packed_mu : ∃ v, inst.x86_64_avx512packingMontyParametersAVX512Inst.PACKED_MU = .ok v ∧
    ∀ i, lane v i = mu

/-! ### BabyBear -/

/-- Rust's `PackedBabyBearAVX512 = PackedMontyField31AVX512<BabyBearParameters>`. -/
abbrev PackedBabyBearAVX512 := PackedAvx512 p3_baby_bear.baby_bear.BabyBearParameters

/-- The `PackedMontyParameters` dictionary the baby-bear variant extracts for
`BabyBearParameters` on x86_64 with AVX-512F: its `MontyParameters` and its
`MontyParametersAVX512` (`PACKED_P`, `PACKED_MU`, `baby-bear/src/x86_64_avx512/packing.rs`). -/
noncomputable abbrev BabyBearPackedParams :=
  p3_baby_bear_avx512.baby_bear.BabyBearParameters.Insts.P3_monty_31Data_traitsPackedMontyParameters

/-- Its `MontyParameters` dictionary, in the monty-31 variant's record. -/
noncomputable abbrev BabyBearMontyParamsAvx512 :=
  p3_baby_bear_avx512.baby_bear.BabyBearParameters.Insts.P3_monty_31Data_traitsMontyParameters

end Avx512

end Plonky3Lean.Spec.Packed
