-- [p3_binary_dft]: external functions.
--
-- Hand-written from hax's seed, `Extraction/FunsExternal_Template.lean`.
-- The generated code imports this module by name.
-- extract.sh fails if the regenerated template declares different names.
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
