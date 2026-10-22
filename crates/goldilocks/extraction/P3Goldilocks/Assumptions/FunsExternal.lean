-- [p3_goldilocks]: external functions.
-- HAND-WRITTEN, from hax's seed of Extraction/FunsExternal_Template.lean.
-- The generated code imports it by this module name. extract.sh fails if the
-- regenerated template declares different names than this file does.
-- The template declares nothing. The imports supply what the generated code
-- names from other crates: p3-util's `gcd_inner` and `branch_hint`, and the
-- `core` models in `HaxExt`.
import Aeneas
import CoreModels
import P3Goldilocks.Extraction.Types
import P3Util
import HaxExt
