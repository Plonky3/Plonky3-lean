-- [p3_symmetric]: external functions.
-- HAND-WRITTEN, from hax's seed of Extraction/FunsExternal_Template.lean.
-- The generated code imports it by this module name. extract.sh fails if the
-- regenerated template declares different names than this file does.
-- The template declares nothing.
module

public import Aeneas
public import CoreModels
public import P3Symmetric.Extraction.Types
public import P3Util

@[expose] public section

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc

namespace p3_symmetric

/-- [p3_symmetric::hasher::CryptographicHasher::hash_iter_slices]: the provided body, which hashes the slices' items in order.

Assumed: the body is opaque by `charon_args` (crate.toml), because aeneas stops on the iterator adapters it calls (docs/extractor-issues.md 30).

No claim reads it: a theorem about a hasher takes its `hash_iter_slices` as given. -/
@[trait_default]
opaque hasher.CryptographicHasher.hash_iter_slices.default
  {Self : Type _} {Item : Type _} {Out : Type _} {I : Type _} {Clause1_IntoIter : Type _}
  (CryptographicHasherInst : hasher.CryptographicHasher Self Item Out)
  (coreitertraitscollectIntoIteratorISharedASliceClause1_IntoIterInst :
    core.iter.traits.collect.IntoIterator I (Slice Item) Clause1_IntoIter) :
  Self → I → RustM Out

end p3_symmetric
