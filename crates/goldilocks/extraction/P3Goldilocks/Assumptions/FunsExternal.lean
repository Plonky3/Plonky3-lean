-- [p3_goldilocks]: external functions.
--
-- Hand-written from hax's seed, `Extraction/FunsExternal_Template.lean`.
-- The generated code imports this module by name.
-- extract.sh fails if the regenerated template declares different names.
--
-- The template declares nothing.
--
-- The imports supply what the generated code names from other crates:
--
-- - p3-util's `gcd_inner` and `branch_hint`
-- - the `core` models in `HaxExt`
module

public import Aeneas
public import CoreModels
public import P3Goldilocks.Extraction.Types
public import P3Util
public import HaxExt

@[expose] public section
