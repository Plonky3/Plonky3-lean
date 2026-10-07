-- [p3_baby_bear]: external types.
-- HAND-WRITTEN, from hax's seed of Extraction/TypesExternal_Template.lean.
-- The generated code imports it by this module name. extract.sh fails if the
-- regenerated template declares different names than this file does.
import Aeneas
import CoreModels
-- The dependency interface: the libraries of crates/mds and crates/monty-31,
-- the scoped extractions of p3-mds and p3-monty-31 plus what they do not supply
-- (`P3Monty31.Assumptions.Mirror`, which imports the p3-field and
-- p3-poseidon{1,2} stubs).
import P3Mds
import P3Monty31
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM ControlFlow Error
open Std.Do
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option linter.style.whitespace false
set_option linter.style.setOption false
set_option linter.style.longLine false

/- You can set the `maxHeartbeats` value with the `-max-heartbeats` CLI option -/
set_option maxHeartbeats 1000000

/- You can set the `maxRecDepth` value with the `-max-recdepth` CLI option -/
set_option maxRecDepth 2048

