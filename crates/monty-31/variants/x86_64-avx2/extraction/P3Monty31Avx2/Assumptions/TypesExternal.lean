-- [p3_monty_31], variant x86_64-avx2: external types.
-- HAND-WRITTEN, from hax's seed of Extraction/TypesExternal_Template.lean.
-- The generated code imports it by this module name. extract.sh fails if the
-- regenerated template declares different names than this file does.
--
-- The variant's run makes the scalar modules opaque (`opaque` in crate.toml), so
-- that the scalar types and functions are the ones P3Monty31 already models:
-- each external is bound to its portable counterpart here, not assumed. The
-- bindings are in the variant's namespace, where the generated code looks first.
module

public import Aeneas
public import CoreModels
public import P3ArchShims
public import P3Monty31

@[expose] public section
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc

namespace p3_monty_31_avx2

/-- [p3_monty_31::monty_31::MontyField31]: the portable type. The struct has
the same definition on every target. -/
abbrev monty_31.MontyField31 (MP : Type _) : Type :=
  p3_monty_31.monty_31.MontyField31 MP

end p3_monty_31_avx2
