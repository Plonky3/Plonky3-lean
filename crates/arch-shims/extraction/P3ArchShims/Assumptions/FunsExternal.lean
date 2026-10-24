-- [p3_arch_shims]: external functions.
-- HAND-WRITTEN, from hax's seed of Extraction/FunsExternal_Template.lean.
-- The generated code imports it by this module name. extract.sh fails if the
-- regenerated template declares different names than this file does.
--
-- EDITED: aeneas's template gives `fmt` a `&mut Formatter` back-function in
-- its result, but `CoreModels`' `core.fmt.Debug.fmt` returns only the updated
-- `Formatter`; the signatures are adjusted to CoreModels' shape
-- (docs/extractor-issues.md 6). `axiom` -> `opaque`. These are the bodies of
-- the vector types' `Debug` impls, which extract.sh makes opaque on purpose.
module

public import Aeneas
public import CoreModels
public import P3ArchShims.Extraction.Types

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
open p3_arch_shims

/-- [p3_arch_shims::x86_64::types::{impl core::fmt::Debug for p3_arch_shims::x86_64::types::M256i}::fmt]:
    Source: 'src/x86_64/types.rs', lines 29:12-31:13
    Visibility: public
    Assumed: `Debug` bodies are opaque by `charon_args` (toolchain.toml). -/
opaque x86_64.types.M256i.Insts.CoreFmtDebug.fmt
  :
  x86_64.types.M256i → core.fmt.Formatter → RustM ((core.result.Result
    Unit core.fmt.Error) × core.fmt.Formatter)

/-- [p3_arch_shims::x86_64::types::{impl core::fmt::Debug for p3_arch_shims::x86_64::types::M128i}::fmt]:
    Source: 'src/x86_64/types.rs', lines 29:12-31:13
    Visibility: public
    Assumed: `Debug` bodies are opaque by `charon_args` (toolchain.toml). -/
opaque x86_64.types.M128i.Insts.CoreFmtDebug.fmt
  :
  x86_64.types.M128i → core.fmt.Formatter → RustM ((core.result.Result
    Unit core.fmt.Error) × core.fmt.Formatter)

/-- [p3_arch_shims::x86_64::types::{impl core::fmt::Debug for p3_arch_shims::x86_64::types::M256}::fmt]:
    Source: 'src/x86_64/types.rs', lines 29:12-31:13
    Visibility: public
    Assumed: `Debug` bodies are opaque by `charon_args` (toolchain.toml). -/
opaque x86_64.types.M256.Insts.CoreFmtDebug.fmt
  :
  x86_64.types.M256 → core.fmt.Formatter → RustM ((core.result.Result
    Unit core.fmt.Error) × core.fmt.Formatter)

/-- [p3_arch_shims::aarch64::types::{impl core::fmt::Debug for p3_arch_shims::aarch64::types::U32x4}::fmt]:
    Source: 'src/aarch64/types.rs', lines 37:12-39:13
    Visibility: public
    Assumed: `Debug` bodies are opaque by `charon_args` (toolchain.toml). -/
opaque aarch64.types.U32x4.Insts.CoreFmtDebug.fmt
  :
  aarch64.types.U32x4 → core.fmt.Formatter → RustM ((core.result.Result
    Unit core.fmt.Error) × core.fmt.Formatter)

/-- [p3_arch_shims::aarch64::types::{impl core::fmt::Debug for p3_arch_shims::aarch64::types::I32x4}::fmt]:
    Source: 'src/aarch64/types.rs', lines 37:12-39:13
    Visibility: public
    Assumed: `Debug` bodies are opaque by `charon_args` (toolchain.toml). -/
opaque aarch64.types.I32x4.Insts.CoreFmtDebug.fmt
  :
  aarch64.types.I32x4 → core.fmt.Formatter → RustM ((core.result.Result
    Unit core.fmt.Error) × core.fmt.Formatter)

/-- [p3_arch_shims::aarch64::types::{impl core::fmt::Debug for p3_arch_shims::aarch64::types::U64x2}::fmt]:
    Source: 'src/aarch64/types.rs', lines 37:12-39:13
    Visibility: public
    Assumed: `Debug` bodies are opaque by `charon_args` (toolchain.toml). -/
opaque aarch64.types.U64x2.Insts.CoreFmtDebug.fmt
  :
  aarch64.types.U64x2 → core.fmt.Formatter → RustM ((core.result.Result
    Unit core.fmt.Error) × core.fmt.Formatter)

/-- [p3_arch_shims::aarch64::types::{impl core::fmt::Debug for p3_arch_shims::aarch64::types::U32x2}::fmt]:
    Source: 'src/aarch64/types.rs', lines 37:12-39:13
    Visibility: public
    Assumed: `Debug` bodies are opaque by `charon_args` (toolchain.toml). -/
opaque aarch64.types.U32x2.Insts.CoreFmtDebug.fmt
  :
  aarch64.types.U32x2 → core.fmt.Formatter → RustM ((core.result.Result
    Unit core.fmt.Error) × core.fmt.Formatter)
