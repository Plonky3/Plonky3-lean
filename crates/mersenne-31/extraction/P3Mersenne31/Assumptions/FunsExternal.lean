-- [p3_mersenne_31]: external functions.
-- HAND-WRITTEN, from hax's seed of Extraction/FunsExternal_Template.lean.
-- The generated code imports it by this module name. extract.sh fails if the
-- regenerated template declares different names than this file does.
module

public import Aeneas
public import CoreModels
public import P3Mersenne31.Extraction.Types
-- `core` models missing from hax-lean's CoreModels (`HaxExt.lean`).
public import HaxExt
-- The functions of other crates the extraction calls:
-- `p3_field::halve_u32` (crates/field/stub/P3Field.lean) and
-- `p3_util::gcd_inversion_prime_field_32` (crates/util, extracted).
public import P3Field
public import P3Util

@[expose] public section
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM ControlFlow Error
open Std.Do

/- You can set the `maxHeartbeats` value with the `-max-heartbeats` CLI option -/

/- You can set the `maxRecDepth` value with the `-max-recdepth` CLI option -/
open p3_mersenne_31

