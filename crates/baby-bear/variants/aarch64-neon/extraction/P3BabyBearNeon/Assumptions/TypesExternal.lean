-- [p3_baby_bear], variant aarch64-neon: external types.
-- HAND-WRITTEN, from hax's seed of Extraction/TypesExternal_Template.lean.
-- The generated code imports it by this module name. extract.sh fails if the
-- regenerated template declares different names than this file does.
--
-- The variant's run makes `baby_bear` opaque (`opaque` in crate.toml), so that
-- `BabyBearParameters` is the type P3BabyBear already models: the external is
-- bound to its portable counterpart here, not assumed. The binding is in the
-- variant's namespace, where the generated code looks first. The generated code
-- refers to the monty-31 variant's traits (`renames` in crate.toml), so this
-- module also brings P3Monty31Neon in.
module

public import Aeneas
public import CoreModels
public import P3BabyBear
public import P3Monty31Neon

@[expose] public section
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc

namespace p3_baby_bear_neon

/-- [p3_baby_bear::baby_bear::BabyBearParameters]: the portable type. The struct
has the same definition on every target. -/
abbrev baby_bear.BabyBearParameters : Type :=
  p3_baby_bear.baby_bear.BabyBearParameters

end p3_baby_bear_neon
