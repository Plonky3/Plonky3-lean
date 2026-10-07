/-
# `p3-monty-31`: what p3-baby-bear uses from it that aeneas does not supply

Most of p3-monty-31 comes from its scoped extraction, `P3Monty31/Extraction/`
(the `data_traits`, `mds`, `poseidon1`/`poseidon2` parameter traits,
`MontyField31` itself, `MontyField31::new`, `utils::to_monty`, the `Clone`
impl). This file holds what that extraction does not produce:

* `MontyField31::new_array`, `MontyField31::new_2d_array`. They are in the LLBC
  with bodies, but aeneas drops them without a diagnostic
  (docs/extractor-issues.md, 4). They are transcribed below: an elementwise
  `new`, left to right, as the Rust `while` loops are.
* `MontyField31::new_monty` and the scalar arithmetic impls that wrap the
  extracted `utils` functions: `Add`, `Sub`, `Mul`, `Neg` and `Field::halve`.
  Like `new_array`, charon translates them (with bodies) but leaves them out
  of the declaration order aeneas reads, so they are not emitted
  (docs/extractor-issues.md, 4). Each body is one line and is transcribed
  below; the arithmetic itself (`utils::add`, `sub`, `monty_reduce`,
  `halve_u32`) is extracted.
* the `no_packing` Poseidon layer types and their constructor impls. On a
  target with no SIMD these are the layers baby-bear's Poseidon instances use.
  The constructor bodies are one struct literal each and are transcribed.
* memberless `Field` and `PrimeField` witnesses for `MontyField31`. Both
  traits are memberless in `P3Monty31.Assumptions.P3Field`, so the witnesses carry no
  content.
-/
import P3Monty31.Extraction
import P3Poseidon1
import P3Poseidon2
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM ControlFlow Error

namespace p3_monty_31

/-- [p3_monty_31::monty_31::MontyField31::new_array]. Upstream:
`monty-31/src/monty_31.rs:88`, `while i < N { output[i] = Self::new(input[i]) }`.
The `else` branch is unreachable (`mapM` preserves length); it is a `panic`
rather than a proof only to keep this a plain transcription. -/
def monty_31.MontyField31.new_array {MP : Type}
    (data_traitsMontyParametersInst : data_traits.MontyParameters MP)
    {N : Std.Usize} (input : Array Std.U32 N) :
    RustM (Array (monty_31.MontyField31 MP) N) :=
  input.val.mapM (monty_31.MontyField31.new data_traitsMontyParametersInst) >>=
    fun l => if h : l.length = N.val then ok ⟨l, h⟩ else fail .panic

/-- [p3_monty_31::monty_31::MontyField31::new_2d_array]. Upstream:
`monty-31/src/monty_31.rs:101`, `new_array` on each row, left to right. -/
def monty_31.MontyField31.new_2d_array {MP : Type}
    (data_traitsMontyParametersInst : data_traits.MontyParameters MP)
    {N M : Std.Usize} (input : Array (Array Std.U32 N) M) :
    RustM (Array (Array (monty_31.MontyField31 MP) N) M) :=
  input.val.mapM (monty_31.MontyField31.new_array data_traitsMontyParametersInst) >>=
    fun l => if h : l.length = M.val then ok ⟨l, h⟩ else fail .panic

/-! ## Scalar arithmetic (`monty-31/src/monty_31.rs`) -/

/-- [p3_monty_31::monty_31::MontyField31::new_monty]. Upstream line 71:
`Self { value, _phantom: PhantomData }`, with no reduction. -/
def monty_31.MontyField31.new_monty {MP : Type}
    (_data_traitsMontyParametersInst : data_traits.MontyParameters MP) (value : Std.U32) :
    RustM (monty_31.MontyField31 MP) :=
  ok { value := value, _phantom := () }

/-- `<MontyField31<FP> as Add>::add`. Upstream line 733:
`Self::new_monty(add::<FP>(self.value, rhs.value))`. -/
def monty_31.MontyField31.add {MP : Type}
    (data_traitsMontyParametersInst : data_traits.MontyParameters MP)
    (self rhs : monty_31.MontyField31 MP) : RustM (monty_31.MontyField31 MP) := do
  let v ← utils.add data_traitsMontyParametersInst self.value rhs.value
  monty_31.MontyField31.new_monty data_traitsMontyParametersInst v

/-- `<MontyField31<FP> as Sub>::sub`. Upstream line 742:
`Self::new_monty(sub::<FP>(self.value, rhs.value))`. -/
def monty_31.MontyField31.sub {MP : Type}
    (data_traitsMontyParametersInst : data_traits.MontyParameters MP)
    (self rhs : monty_31.MontyField31 MP) : RustM (monty_31.MontyField31 MP) := do
  let v ← utils.sub data_traitsMontyParametersInst self.value rhs.value
  monty_31.MontyField31.new_monty data_traitsMontyParametersInst v

/-- `<MontyField31<FP> as Mul>::mul`. Upstream line 760:
`let long_prod = self.value as u64 * rhs.value as u64;`
`Self::new_monty(monty_reduce::<FP>(long_prod))`. The `*` is Rust's checked
`u64` multiplication, as aeneas renders it. -/
def monty_31.MontyField31.mul {MP : Type}
    (data_traitsMontyParametersInst : data_traits.MontyParameters MP)
    (self rhs : monty_31.MontyField31 MP) : RustM (monty_31.MontyField31 MP) := do
  let i ← lift (UScalar.cast .U64 self.value)
  let i1 ← lift (UScalar.cast .U64 rhs.value)
  let long_prod ← i * i1
  let v ← utils.monty_reduce data_traitsMontyParametersInst long_prod
  monty_31.MontyField31.new_monty data_traitsMontyParametersInst v

/-- `<MontyField31<FP> as Neg>::neg`. Upstream line 751: `Self::ZERO - self`,
where `ZERO` is `FP::MONTY_ZERO` (line 214). -/
def monty_31.MontyField31.neg {FP : Type}
    (data_traitsFieldParametersInst : data_traits.FieldParameters FP)
    (self : monty_31.MontyField31 FP) : RustM (monty_31.MontyField31 FP) := do
  let zero ← data_traitsFieldParametersInst.MONTY_ZERO
  monty_31.MontyField31.sub
    data_traitsFieldParametersInst.PackedMontyParametersInst.MontyParametersInst zero self

/-- `<MontyField31<FP> as Field>::halve`. Upstream line 225:
`Self::new_monty(halve_u32::<FP>(self.value))`. -/
def monty_31.MontyField31.halve {FP : Type}
    (data_traitsFieldParametersInst : data_traits.FieldParameters FP)
    (self : monty_31.MontyField31 FP) : RustM (monty_31.MontyField31 FP) := do
  let v ← utils.halve_u32 data_traitsFieldParametersInst self.value
  monty_31.MontyField31.new_monty
    data_traitsFieldParametersInst.PackedMontyParametersInst.MontyParametersInst v

/-- `impl<FP: FieldParameters> PrimeField for MontyField31<FP>`
(`monty-31/src/monty_31.rs:671`). `PrimeField` has no members here. -/
def monty_31.MontyField31.Insts.P3_fieldFieldPrimeField {FP : Type}
    (_data_traitsFieldParametersInst : data_traits.FieldParameters FP) :
    p3_field.field.PrimeField (monty_31.MontyField31 FP) := {}

/-- `impl<FP: FieldParameters> Field for MontyField31<FP>`
(`monty-31/src/monty_31.rs:432`). `Field` has no members here. -/
def monty_31.MontyField31.Insts.P3_fieldFieldField {FP : Type}
    (_data_traitsFieldParametersInst : data_traits.FieldParameters FP) :
    p3_field.field.Field (monty_31.MontyField31 FP) := {}

/-! ## `no_packing::poseidon1` (`monty-31/src/no_packing/poseidon1.rs`) -/

/-- Upstream line 14. aeneas orders type parameters before const generics. -/
structure no_packing.poseidon1.Poseidon1InternalLayerMonty31 (MP : Type)
    (ILP : Type) (WIDTH : Std.Usize) where
  internal_constants :
    p3_poseidon1.internal.PartialRoundConstants (monty_31.MontyField31 MP) WIDTH
  _phantom : core.marker.PhantomData ILP

/-- Upstream line 25. -/
structure no_packing.poseidon1.Poseidon1ExternalLayerMonty31 (MP : Type)
    (MU : Type) (WIDTH : Std.Usize) where
  external_constants :
    p3_poseidon1.external.FullRoundConstants (monty_31.MontyField31 MP) WIDTH
  _mds : core.marker.PhantomData MU

/-- Upstream line 30: `Self { internal_constants, _phantom: PhantomData }`. -/
def no_packing.poseidon1.Poseidon1InternalLayerMonty31.Insts.P3_poseidon1InternalPartialRoundLayerConstructorMontyField31WIDTH
    {FP ILP : Type} {WIDTH : Std.Usize}
    (data_traitsFieldParametersInst : data_traits.FieldParameters FP)
    (_PartialRoundBaseParametersInst :
      poseidon1.PartialRoundBaseParameters ILP FP WIDTH) :
    p3_poseidon1.internal.PartialRoundLayerConstructor
      (no_packing.poseidon1.Poseidon1InternalLayerMonty31 FP ILP WIDTH)
      (monty_31.MontyField31 FP) WIDTH := {
  p3_fieldfieldFieldInst :=
    monty_31.MontyField31.Insts.P3_fieldFieldField data_traitsFieldParametersInst
  new_from_constants := fun internal_constants =>
    ok { internal_constants, _phantom := () }
}

/-- Upstream line 44: `Self { external_constants, _mds: PhantomData }`. -/
def no_packing.poseidon1.Poseidon1ExternalLayerMonty31.Insts.P3_poseidon1ExternalFullRoundLayerConstructorMontyField31WIDTH
    {FP MU : Type} (WIDTH : Std.Usize)
    (data_traitsFieldParametersInst : data_traits.FieldParameters FP)
    (_mdsMDSUtilsInst : mds.MDSUtils MU) :
    p3_poseidon1.external.FullRoundLayerConstructor
      (no_packing.poseidon1.Poseidon1ExternalLayerMonty31 FP MU WIDTH)
      (monty_31.MontyField31 FP) WIDTH := {
  p3_fieldfieldFieldInst :=
    monty_31.MontyField31.Insts.P3_fieldFieldField data_traitsFieldParametersInst
  new_from_constants := fun external_constants =>
    ok { external_constants, _mds := () }
}

/-! ## `no_packing::poseidon2` (`monty-31/src/no_packing/poseidon2.rs`) -/

/-- Upstream line 14. -/
structure no_packing.poseidon2.Poseidon2InternalLayerMonty31 (MP : Type)
    (ILP : Type) (WIDTH : Std.Usize) where
  internal_constants : alloc.vec.Vec (monty_31.MontyField31 MP)
  _phantom : core.marker.PhantomData ILP

/-- Upstream line 25. -/
structure no_packing.poseidon2.Poseidon2ExternalLayerMonty31 (MP : Type)
    (WIDTH : Std.Usize) where
  external_constants :
    p3_poseidon2.external.ExternalLayerConstants (monty_31.MontyField31 MP) WIDTH

/-- Upstream line 28: `Self { internal_constants, _phantom: PhantomData }`. -/
def no_packing.poseidon2.Poseidon2InternalLayerMonty31.Insts.P3_poseidon2InternalInternalLayerConstructorMontyField31
    {FP ILP : Type} {WIDTH : Std.Usize}
    (data_traitsFieldParametersInst : data_traits.FieldParameters FP)
    (_InternalLayerBaseParametersInst :
      poseidon2.InternalLayerBaseParameters ILP FP WIDTH) :
    p3_poseidon2.internal.InternalLayerConstructor
      (no_packing.poseidon2.Poseidon2InternalLayerMonty31 FP ILP WIDTH)
      (monty_31.MontyField31 FP) := {
  p3_fieldfieldFieldInst :=
    monty_31.MontyField31.Insts.P3_fieldFieldField data_traitsFieldParametersInst
  new_from_constants := fun internal_constants =>
    ok { internal_constants, _phantom := () }
}

/-- Upstream line 41: `Self { external_constants }`. -/
def no_packing.poseidon2.Poseidon2ExternalLayerMonty31.Insts.P3_poseidon2ExternalExternalLayerConstructorMontyField31WIDTH
    {FP : Type} (WIDTH : Std.Usize)
    (data_traitsFieldParametersInst : data_traits.FieldParameters FP) :
    p3_poseidon2.external.ExternalLayerConstructor
      (no_packing.poseidon2.Poseidon2ExternalLayerMonty31 FP WIDTH)
      (monty_31.MontyField31 FP) WIDTH := {
  p3_fieldfieldFieldInst :=
    monty_31.MontyField31.Insts.P3_fieldFieldField data_traitsFieldParametersInst
  new_from_constants := fun external_constants =>
    ok { external_constants }
}

end p3_monty_31
