-- [p3_security]: external functions.
-- HAND-WRITTEN, from hax's seed of Extraction/FunsExternal_Template.lean.
-- The generated code imports it by this module name. extract.sh fails if the
-- regenerated template declares different names than this file does.
--
-- EDITED: aeneas's template gives `fmt` a `&mut Formatter` back-function in
-- its result, but `CoreModels`' `core.fmt.Debug.fmt` returns only the updated
-- `Formatter`. The signatures below are adjusted to CoreModels' shape.
-- `axiom` -> `opaque`: these are the bodies of derived `Debug` impls, which
-- extract.sh makes opaque on purpose.
module

public import Aeneas
public import CoreModels
public import P3Security.Extraction.Types
-- `core` models missing from hax-lean's CoreModels (`HaxExt.lean`).
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

/- You can set the `maxHeartbeats` value with the `-max-heartbeats` CLI option -/
set_option maxHeartbeats 1000000

/- You can set the `maxRecDepth` value with the `-max-recdepth` CLI option -/
set_option maxRecDepth 2048
open p3_security

/-- [p3_security::budget::report::{impl core::fmt::Debug for p3_security::budget::report::SecurityTerm}::fmt]:
    Source: 'security/src/budget/report.rs', lines 27:22-27:27
    Visibility: public
    Assumed: `Debug` bodies are opaque by `charon_args` (toolchain.toml). -/
opaque budget.report.SecurityTerm.Insts.CoreFmtDebug.fmt
  :
  budget.report.SecurityTerm → core.fmt.Formatter → RustM
    ((core.result.Result Unit core.fmt.Error) × core.fmt.Formatter)

/-- [p3_security::budget::report::{impl core::fmt::Debug for p3_security::budget::report::SecurityReport}::fmt]:
    Source: 'security/src/budget/report.rs', lines 43:22-43:27
    Visibility: public
    Assumed: `Debug` bodies are opaque by `charon_args` (toolchain.toml). -/
opaque budget.report.SecurityReport.Insts.CoreFmtDebug.fmt
  :
  budget.report.SecurityReport → core.fmt.Formatter → RustM
    ((core.result.Result Unit core.fmt.Error) × core.fmt.Formatter)

/-- [p3_security::budget::shape::{impl core::fmt::Debug for p3_security::budget::shape::ProtocolParams}::fmt]:
    Source: 'security/src/budget/shape.rs', lines 11:22-11:27
    Visibility: public
    Assumed: `Debug` bodies are opaque by `charon_args` (toolchain.toml). -/
opaque budget.shape.ProtocolParams.Insts.CoreFmtDebug.fmt
  :
  budget.shape.ProtocolParams → core.fmt.Formatter → RustM
    ((core.result.Result Unit core.fmt.Error) × core.fmt.Formatter)

/-- [p3_security::budget::shape::{impl core::fmt::Debug for p3_security::budget::shape::InstanceShape}::fmt]:
    Source: 'security/src/budget/shape.rs', lines 41:22-41:27
    Visibility: public
    Assumed: `Debug` bodies are opaque by `charon_args` (toolchain.toml). -/
opaque budget.shape.InstanceShape.Insts.CoreFmtDebug.fmt
  :
  budget.shape.InstanceShape → core.fmt.Formatter → RustM
    ((core.result.Result Unit core.fmt.Error) × core.fmt.Formatter)

/-- [p3_security::budget::shape::{impl core::fmt::Debug for p3_security::budget::shape::LookupShape}::fmt]:
    Source: 'security/src/budget/shape.rs', lines 76:22-76:27
    Visibility: public
    Assumed: `Debug` bodies are opaque by `charon_args` (toolchain.toml). -/
opaque budget.shape.LookupShape.Insts.CoreFmtDebug.fmt
  :
  budget.shape.LookupShape → core.fmt.Formatter → RustM
    ((core.result.Result Unit core.fmt.Error) × core.fmt.Formatter)

/-- [p3_security::budget::shape::{impl core::fmt::Debug for p3_security::budget::shape::AirShape}::fmt]:
    Source: 'security/src/budget/shape.rs', lines 89:22-89:27
    Visibility: public
    Assumed: `Debug` bodies are opaque by `charon_args` (toolchain.toml). -/
opaque budget.shape.AirShape.Insts.CoreFmtDebug.fmt
  :
  budget.shape.AirShape → core.fmt.Formatter → RustM
    ((core.result.Result Unit core.fmt.Error) × core.fmt.Formatter)
