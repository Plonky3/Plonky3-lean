-- [p3_baby_bear], variant aarch64-neon: external functions.
--
-- Hand-written from hax's seed, `Extraction/FunsExternal_Template.lean`.
-- The generated code imports this module by name.
-- extract.sh fails if the regenerated template declares different names.
--
-- As in TypesExternal.lean, each external is bound to the portable model: the
-- derived impls of `BabyBearParameters` and its `MontyParameters` constants are
-- P3BabyBear's. The constants are `RustM` values here, since an opaque
-- associated constant is a computation in the generated code; each is `ok` of
-- the portable constant.
module

public import Aeneas
public import CoreModels
public import P3BabyBear
public import P3BabyBearNeon.Extraction.Types

@[expose] public section
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM ControlFlow Error

namespace p3_baby_bear_neon

/-- [p3_baby_bear::baby_bear::{impl core::clone::Clone for p3_baby_bear::baby_bear::BabyBearParameters}::clone]:
the portable model. -/
def baby_bear.BabyBearParameters.Insts.CoreCloneClone.clone :
    baby_bear.BabyBearParameters → RustM baby_bear.BabyBearParameters :=
  p3_baby_bear.baby_bear.BabyBearParameters.Insts.CoreCloneClone.clone

/-- [p3_baby_bear::baby_bear::{impl core::default::Default for p3_baby_bear::baby_bear::BabyBearParameters}::default]:
the portable model. -/
def baby_bear.BabyBearParameters.Insts.CoreDefaultDefault.default :
    RustM baby_bear.BabyBearParameters :=
  p3_baby_bear.baby_bear.BabyBearParameters.Insts.CoreDefaultDefault.default

/-- [p3_baby_bear::baby_bear::{impl core::fmt::Debug for p3_baby_bear::baby_bear::BabyBearParameters}::fmt]:
the portable model (itself opaque, P3BabyBear's `Assumptions/FunsExternal.lean`). As there,
the signature is CoreModels' `Debug::fmt`, without the template's back-function. -/
def baby_bear.BabyBearParameters.Insts.CoreFmtDebug.fmt :
    baby_bear.BabyBearParameters → core.fmt.Formatter →
      RustM ((core.result.Result Unit core.fmt.Error) × core.fmt.Formatter) :=
  p3_baby_bear.baby_bear.BabyBearParameters.Insts.CoreFmtDebug.fmt

/-- [p3_baby_bear::baby_bear::{impl core::cmp::PartialEq<p3_baby_bear::baby_bear::BabyBearParameters> for p3_baby_bear::baby_bear::BabyBearParameters}::eq]:
the portable model. -/
def baby_bear.BabyBearParameters.Insts.CoreCmpPartialEqBabyBearParameters.eq :
    baby_bear.BabyBearParameters → baby_bear.BabyBearParameters → RustM Bool :=
  p3_baby_bear.baby_bear.BabyBearParameters.Insts.CoreCmpPartialEqBabyBearParameters.eq

/-- [p3_baby_bear::baby_bear::{impl core::hash::Hash for p3_baby_bear::baby_bear::BabyBearParameters}::hash]:
the portable model. -/
def baby_bear.BabyBearParameters.Insts.CoreHashHash.hash
    {__H : Type} (corehashHasherInst : core.hash.Hasher __H) :
    baby_bear.BabyBearParameters → __H → RustM __H :=
  p3_baby_bear.baby_bear.BabyBearParameters.Insts.CoreHashHash.hash corehashHasherInst

/-- [p3_baby_bear::baby_bear::{impl p3_monty_31::data_traits::MontyParameters for p3_baby_bear::baby_bear::BabyBearParameters}::MONTY_MU]:
the portable constant. -/
def baby_bear.BabyBearParameters.Insts.P3_monty_31Data_traitsMontyParameters.MONTY_MU :
    RustM Std.U32 :=
  ok p3_baby_bear.baby_bear.BabyBearParameters.Insts.P3_monty_31Data_traitsMontyParameters.MONTY_MU

/-- [p3_baby_bear::baby_bear::{impl p3_monty_31::data_traits::MontyParameters for p3_baby_bear::baby_bear::BabyBearParameters}::MONTY_BITS]:
the portable constant. -/
def baby_bear.BabyBearParameters.Insts.P3_monty_31Data_traitsMontyParameters.MONTY_BITS :
    RustM Std.U32 :=
  ok p3_baby_bear.baby_bear.BabyBearParameters.Insts.P3_monty_31Data_traitsMontyParameters.MONTY_BITS

/-- [p3_baby_bear::baby_bear::{impl p3_monty_31::data_traits::MontyParameters for p3_baby_bear::baby_bear::BabyBearParameters}::PRIME]:
the portable constant. -/
def baby_bear.BabyBearParameters.Insts.P3_monty_31Data_traitsMontyParameters.PRIME :
    RustM Std.U32 :=
  ok p3_baby_bear.baby_bear.BabyBearParameters.Insts.P3_monty_31Data_traitsMontyParameters.PRIME

end p3_baby_bear_neon
