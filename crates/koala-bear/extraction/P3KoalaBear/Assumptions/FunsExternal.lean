-- [p3_koala_bear]: external functions.
-- HAND-WRITTEN, from hax's seed of Extraction/FunsExternal_Template.lean.
-- The generated code imports it by this module name. extract.sh fails if the
-- regenerated template declares different names than this file does.
--
-- EDITED: aeneas's template gives `fmt` a `&mut Formatter` back-function in
-- its result, but `CoreModels`' `core.fmt.Debug.fmt` returns only the updated
-- `Formatter`. The four signatures below are adjusted to CoreModels' shape.
-- `axiom` -> `opaque`: an opaque constant asserts only that
-- some inhabitant exists, so it adds nothing to a theorem's axiom footprint.
-- These are the bodies of four derived `Debug` impls, which extract.sh
-- makes opaque on purpose.
module

public import Aeneas
public import CoreModels
public import P3KoalaBear.Extraction.Types

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

/- You can set the `maxHeartbeats` value with the `-max-heartbeats` CLI option -/
set_option maxHeartbeats 1000000

/- You can set the `maxRecDepth` value with the `-max-recdepth` CLI option -/
set_option maxRecDepth 2048
open p3_koala_bear

/-- [p3_koala_bear::koala_bear::{impl core::fmt::Debug for p3_koala_bear::koala_bear::KoalaBearParameters}::fmt]:
    Source: 'koala-bear/src/koala_bear.rs', lines 11:31-11:36
    Visibility: public
    Assumed: `Debug` bodies are opaque by `charon_args` (toolchain.toml). -/
opaque koala_bear.KoalaBearParameters.Insts.CoreFmtDebug.fmt
  :
  koala_bear.KoalaBearParameters → core.fmt.Formatter → RustM
    ((core.result.Result Unit core.fmt.Error) × core.fmt.Formatter)

/-- [p3_koala_bear::mds::{impl core::fmt::Debug for p3_koala_bear::mds::MDSKoalaBearData}::fmt]:
    Source: 'koala-bear/src/mds.rs', lines 12:25-12:30
    Visibility: public
    Assumed: `Debug` bodies are opaque by `charon_args` (toolchain.toml). -/
opaque mds.MDSKoalaBearData.Insts.CoreFmtDebug.fmt
  :
  mds.MDSKoalaBearData → core.fmt.Formatter → RustM ((core.result.Result
    Unit core.fmt.Error) × core.fmt.Formatter)

/-- [p3_koala_bear::poseidon1::{impl core::fmt::Debug for p3_koala_bear::poseidon1::KoalaBearPoseidonParameters}::fmt]:
    Source: 'koala-bear/src/poseidon1.rs', lines 92:9-92:14
    Visibility: public
    Assumed: `Debug` bodies are opaque by `charon_args` (toolchain.toml). -/
opaque poseidon1.KoalaBearPoseidonParameters.Insts.CoreFmtDebug.fmt
  :
  poseidon1.KoalaBearPoseidonParameters → core.fmt.Formatter → RustM
    ((core.result.Result Unit core.fmt.Error) × core.fmt.Formatter)

/-- [p3_koala_bear::poseidon2::{impl core::fmt::Debug for p3_koala_bear::poseidon2::KoalaBearInternalLayerParameters}::fmt]:
    Source: 'koala-bear/src/poseidon2.rs', lines 404:9-404:14
    Visibility: public
    Assumed: `Debug` bodies are opaque by `charon_args` (toolchain.toml). -/
opaque poseidon2.KoalaBearInternalLayerParameters.Insts.CoreFmtDebug.fmt
  :
  poseidon2.KoalaBearInternalLayerParameters → core.fmt.Formatter → RustM
    ((core.result.Result Unit core.fmt.Error) × core.fmt.Formatter)

