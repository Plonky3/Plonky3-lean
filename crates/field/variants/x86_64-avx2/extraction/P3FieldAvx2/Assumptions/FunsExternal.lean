-- [p3_field], variant x86_64-avx2: external functions.
-- HAND-WRITTEN, from hax's seed of Extraction/FunsExternal_Template.lean.
-- The generated code imports it by this module name. extract.sh fails if the
-- regenerated template declares different names than this file does.
--
-- The variant declares no external function. The intrinsics the generated code
-- calls are p3-arch-shims' models, by their absolute names (`P3ArchShims`).
module

public import Aeneas
public import CoreModels
public import P3ArchShims
public import P3FieldAvx2.Extraction.Types

@[expose] public section
