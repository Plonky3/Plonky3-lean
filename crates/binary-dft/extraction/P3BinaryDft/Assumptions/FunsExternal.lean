-- [p3_binary_dft]: external functions.
-- HAND-WRITTEN, from hax's seed of Extraction/FunsExternal_Template.lean.
-- The generated code imports it by this module name.
-- extract.sh fails if the regenerated template declares other names than this file.
module

public import Aeneas
public import CoreModels
public import P3Field
public import P3BinaryField
public import P3Util
public import HaxExt
public import P3BinaryDft.Extraction.Types
public import P3BinaryDft.Mirror.MaybeRayon
public import P3BinaryDft.Assumptions.Layout

@[expose] public section
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc

namespace p3_binary_dft

/-- A staged group of stages, which gathers several stages into one pass through staging buffers.

Assumed: charon is told to leave it opaque, since aeneas rejects the rayon iterator its body drives.

Only a pool of 16 workers or more schedules a staged group, and the serial pool has one. -/
opaque lch.schedule.fused_group {F : Type _} {Clause0_Clause0_Repr : Type _} (INVERSE : Bool)
    (butterflyButterflyFieldInst : butterfly.ButterflyField F Clause0_Clause0_Repr) :
    Slice F → Std.Usize → Std.Usize → Std.Usize → Std.Usize → lch.twiddles.Twiddles F →
      RustM (Slice F) :=
  fun _ _ _ _ _ _ => .fail .panic

end p3_binary_dft
