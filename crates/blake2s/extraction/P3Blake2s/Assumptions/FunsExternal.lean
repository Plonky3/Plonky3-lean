-- [p3_blake2s]: external functions.
-- HAND-WRITTEN, from hax's seed of Extraction/FunsExternal_Template.lean.
-- The generated code imports it by this module name. extract.sh fails if the
-- regenerated template declares different names than this file does.
-- `axiom` -> `opaque`: an opaque constant asserts only that some inhabitant
-- exists, so it adds nothing to a theorem's axiom footprint.
module

public import Aeneas
public import CoreModels
public import HaxExt
public import P3Blake2s.Extraction.Types

@[expose] public section
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc

namespace p3_blake2s

/-- [p3_blake2s::{p3_blake2s::Blake2s256}::hash]: `blake2`'s `Blake2s::<U32>::digest`.

Assumed: its body goes through `blake2`'s incremental `Digest`, whose buffer type
aeneas rejects (docs/extractor-issues.md 16). -/
opaque Blake2s256.hash : Slice Std.U8 → RustM (Std.Array Std.U8 32#usize)

end p3_blake2s
