-- [p3_mersenne_31]: external types.
-- HAND-WRITTEN, from hax's seed of Extraction/TypesExternal_Template.lean.
-- The generated code imports it by this module name. extract.sh fails if the
-- regenerated template declares different names than this file does.
module

public import Aeneas
public import CoreModels

@[expose] public section
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM ControlFlow Error
open Std.Do

/- You can set the `maxHeartbeats` value with the `-max-heartbeats` CLI option -/

/- You can set the `maxRecDepth` value with the `-max-recdepth` CLI option -/

