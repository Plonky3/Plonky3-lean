-- [p3_monty_31], variant aarch64-neon: external functions.
-- HAND-WRITTEN, from hax's seed of Extraction/FunsExternal_Template.lean.
-- The generated code imports it by this module name. extract.sh fails if the
-- regenerated template declares different names than this file does.
--
-- As in TypesExternal.lean, each external is bound to the portable model. The
-- generated code also calls p3-field's NEON helpers (`P3FieldNeon`), the
-- intrinsics' models (`P3ArchShims`) and `transmute` (`HaxExt`), at the layout
-- instances below.
module

public import Aeneas
public import CoreModels
public import HaxExt
public import P3ArchShims
public import P3FieldNeon
public import P3Monty31
public import P3Monty31Neon.Extraction.Types

@[expose] public section
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM ControlFlow Error

namespace p3_monty_31_neon

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

end p3_monty_31_neon

/-! ## Layouts

`PackedMontyField31Neon::to_vector` and `from_vector` transmute between
`[MontyField31<PMP>; 4]` and `uint32x4_t`, and `to_signed_vector` from
`[MontyField31<PMP>; 4]` to `int32x4_t`. -/

/-- `[MontyField31<MP>; 4]` read as a `uint32x4_t`: lane `i` is element `i`'s `value`.

Assumed: `MontyField31` is `repr(transparent)` over its `value: u32` (its other
field is a `PhantomData`), so the array is four `u32`s, element `i` at byte
`4 i`; and `uint32x4_t`'s lane `i` is bytes `4 i` to `4 i + 3`, as in
p3-arch-shims' `repr(transparent)` lane array. -/
instance p3_monty_31_neon.Transmute.montyArrayToU32x4 (MP : Type _) :
    core.intrinsics.Transmute (Array (p3_monty_31.monty_31.MontyField31 MP) 4#usize)
      p3_arch_shims.aarch64.types.U32x4 where
  transmute a := Array.make 4#usize (a.val.map (·.value)) (by simp)

/-- A `uint32x4_t` read as `[MontyField31<MP>; 4]`: element `i`'s `value` is lane `i`.

Assumed: the layout of `montyArrayToU32x4`, read the other way. Every `u32` is a
`MontyField31` as far as layout goes; the value need not be canonical. -/
instance p3_monty_31_neon.Transmute.u32x4ToMontyArray (MP : Type _) :
    core.intrinsics.Transmute p3_arch_shims.aarch64.types.U32x4
      (Array (p3_monty_31.monty_31.MontyField31 MP) 4#usize) where
  transmute v := Array.make 4#usize (v.val.map fun x => { value := x, _phantom := () }) (by simp)

/-- `[MontyField31<MP>; 4]` read as an `int32x4_t`: lane `i` has the bits of element `i`'s
`value`, read as a two's-complement `i32`.

Assumed: the layout of `montyArrayToU32x4`, with `int32x4_t`'s lane `i` at the same bytes
as `uint32x4_t`'s, as in p3-arch-shims' `repr(transparent)` lane array of `i32`s. -/
instance p3_monty_31_neon.Transmute.montyArrayToI32x4 (MP : Type _) :
    core.intrinsics.Transmute (Array (p3_monty_31.monty_31.MontyField31 MP) 4#usize)
      p3_arch_shims.aarch64.types.I32x4 where
  transmute a := Array.make 4#usize (a.val.map fun x => ⟨x.value.bv⟩) (by simp)
