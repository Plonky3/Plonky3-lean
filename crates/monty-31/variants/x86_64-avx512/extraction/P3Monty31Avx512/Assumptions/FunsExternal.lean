-- [p3_monty_31], variant x86_64-avx512: external functions.
--
-- Hand-written from hax's seed, `Extraction/FunsExternal_Template.lean`.
-- The generated code imports this module by name.
-- extract.sh fails if the regenerated template declares different names.
--
-- As in TypesExternal.lean, each external is bound to the portable model. The
-- generated code also calls p3-field's AVX-512 helpers (`P3FieldAvx512`), the
-- intrinsics' models (`P3ArchShims`) and `transmute` (`HaxExt`), at the layout
-- instances below.
module

public import Aeneas
public import CoreModels
public import HaxExt
public import P3ArchShims
public import P3FieldAvx512
public import P3Monty31
public import P3Monty31Avx512.Extraction.Types

@[expose] public section
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM ControlFlow Error

namespace p3_monty_31_avx512

/-- [p3_monty_31::monty_31::{impl core::clone::Clone for p3_monty_31::monty_31::MontyField31<MP>}::clone]:
the portable model, given the variant's `MontyParameters` dictionary as the
portable one (the trait has the same members on every target). -/
def monty_31.MontyField31.Insts.CoreCloneClone.clone
    {MP : Type _} (corecloneCloneInst : core.clone.Clone MP)
    (data_traitsMontyParametersInst : data_traits.MontyParameters MP) :
    monty_31.MontyField31 MP → RustM (monty_31.MontyField31 MP) :=
  p3_monty_31.monty_31.MontyField31.Insts.CoreCloneClone.clone corecloneCloneInst
    { PRIME := data_traitsMontyParametersInst.PRIME
      MONTY_BITS := data_traitsMontyParametersInst.MONTY_BITS
      MONTY_MU := data_traitsMontyParametersInst.MONTY_MU
      MONTY_MASK := data_traitsMontyParametersInst.MONTY_MASK
      coremarkerCopyInst := data_traitsMontyParametersInst.coremarkerCopyInst
      coredefaultDefaultInst := data_traitsMontyParametersInst.coredefaultDefaultInst
      corefmtDebugInst := data_traitsMontyParametersInst.corefmtDebugInst
      corecmpEqInst := data_traitsMontyParametersInst.corecmpEqInst
      corecmpPartialEqInst := data_traitsMontyParametersInst.corecmpPartialEqInst
      corehashHashInst := data_traitsMontyParametersInst.corehashHashInst }

end p3_monty_31_avx512

/-! ## Layouts

`PackedMontyField31AVX512::to_vector` and `from_vector` transmute between
`[MontyField31<PMP>; 16]` and `__m512i`. -/

/-- `[MontyField31<MP>; 16]` read as an `__m512i`: lane `i` is element `i`'s `value`.

Assumed: `MontyField31` is `repr(transparent)` over its `value: u32` (its other
field is a `PhantomData`), so the array is sixteen `u32`s, element `i` at byte
`4 i`; and `__m512i`'s lane `i` is bytes `4 i` to `4 i + 3`, as in p3-arch-shims'
`repr(transparent)` lane array. -/
instance p3_monty_31_avx512.Transmute.montyArrayToM512i (MP : Type _) :
    core.intrinsics.Transmute (Array (p3_monty_31.monty_31.MontyField31 MP) 16#usize)
      p3_arch_shims.x86_64.types.M512i where
  transmute a := Array.make 16#usize (a.val.map (·.value)) (by simp)

/-- An `__m512i` read as `[MontyField31<MP>; 16]`: element `i`'s `value` is lane `i`.

Assumed: the layout of `montyArrayToM512i`, read the other way. Every `u32` is a
`MontyField31` as far as layout goes; the value need not be canonical. -/
instance p3_monty_31_avx512.Transmute.m512iToMontyArray (MP : Type _) :
    core.intrinsics.Transmute p3_arch_shims.x86_64.types.M512i
      (Array (p3_monty_31.monty_31.MontyField31 MP) 16#usize) where
  transmute v := Array.make 16#usize (v.val.map fun x => { value := x, _phantom := () }) (by simp)
