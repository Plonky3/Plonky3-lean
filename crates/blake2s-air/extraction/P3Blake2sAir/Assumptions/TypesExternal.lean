-- [p3_blake2s_air]: external types.
--
-- Hand-written from hax's seed, `Extraction/TypesExternal_Template.lean`.
-- The generated code imports this module by name.
-- extract.sh fails if the regenerated template declares different names.
--
-- The template declares nothing.
module

public import Aeneas
public import CoreModels

@[expose] public section
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
