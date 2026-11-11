-- [p3_word]: external functions.
--
-- Hand-written from hax's seed, `Extraction/FunsExternal_Template.lean`.
-- The generated code imports this module by name.
-- extract.sh fails if the regenerated template declares different names.
--
-- EDITED: the `fmt` signatures below follow CoreModels' shape.
-- aeneas's template gives `fmt` a `&mut Formatter` back-function in its result.
-- CoreModels' `core.fmt.Debug.fmt` returns only the updated `Formatter`.
--
-- EDITED: `axiom` -> `opaque`.
-- These are the bodies of derived `Debug` impls.
-- extract.sh makes them opaque on purpose.
module

public import Aeneas
public import CoreModels
public import P3Word.Extraction.Types
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

/- You can set the `maxHeartbeats` value with the `-max-heartbeats` CLI option -/
set_option maxHeartbeats 1000000

/- You can set the `maxRecDepth` value with the `-max-recdepth` CLI option -/
set_option maxRecDepth 2048
open p3_word

/-- [p3_word::index::{impl core::fmt::Debug for p3_word::index::IndexError}::fmt]:
    Source: 'word/src/index.rs', lines 13:22-13:27
    Visibility: public
    Assumed: `Debug` bodies are opaque by `charon_args` (toolchain.toml). -/
opaque index.IndexError.Insts.CoreFmtDebug.fmt
  :
  index.IndexError → core.fmt.Formatter → RustM
    ((core.result.Result Unit core.fmt.Error) × core.fmt.Formatter)

/-- [p3_word::word::{impl core::fmt::Debug for p3_word::word::Word32}::fmt]:
    Source: 'word/src/word.rs', lines 39:22-39:27
    Visibility: public
    Assumed: `Debug` bodies are opaque by `charon_args` (toolchain.toml). -/
opaque word.Word32.Insts.CoreFmtDebug.fmt
  :
  word.Word32 → core.fmt.Formatter → RustM
    ((core.result.Result Unit core.fmt.Error) × core.fmt.Formatter)

/-- [p3_word::word::{impl core::fmt::Debug for p3_word::word::Word64}::fmt]:
    Source: 'word/src/word.rs', lines 135:22-135:27
    Visibility: public
    Assumed: `Debug` bodies are opaque by `charon_args` (toolchain.toml). -/
opaque word.Word64.Insts.CoreFmtDebug.fmt
  :
  word.Word64 → core.fmt.Formatter → RustM
    ((core.result.Result Unit core.fmt.Error) × core.fmt.Formatter)
