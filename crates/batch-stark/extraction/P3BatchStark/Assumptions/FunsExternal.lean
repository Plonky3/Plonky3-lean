-- [p3_batch_stark]: external functions.
--
-- Hand-written from hax's seed, `Extraction/FunsExternal_Template.lean`.
-- The generated code imports this module by name.
-- extract.sh fails if the regenerated template declares different names.
--
-- The template declares nothing.
-- The opening count of one instance comes from p3-uni-stark's extraction.
module

public import Aeneas
public import CoreModels
public import P3BatchStark.Extraction.Types
public import P3UniStark
-- The `core` models that hax-lean's CoreModels lacks live in `HaxExt.lean`.
public import HaxExt

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
