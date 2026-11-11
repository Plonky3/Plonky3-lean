-- [p3_symmetric]: external functions.
--
-- Hand-written from hax's seed, `Extraction/FunsExternal_Template.lean`.
-- The generated code imports this module by name.
-- extract.sh fails if the regenerated template declares different names.
--
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

/-- [p3_symmetric::hasher::CryptographicHasher::hash_iter_slices]: the provided body.

It hashes the slices' items in order.

Assumed: aeneas stops on its iterator adapters, so crate.toml makes it opaque (docs/extractor-issues.md 30).

No claim reads it.

A theorem about a hasher takes its slice-hashing method as given. -/
@[trait_default]
opaque hasher.CryptographicHasher.hash_iter_slices.default
  {Self : Type _} {Item : Type _} {Out : Type _} {I : Type _} {Clause1_IntoIter : Type _}
  (CryptographicHasherInst : hasher.CryptographicHasher Self Item Out)
  (coreitertraitscollectIntoIteratorISharedASliceClause1_IntoIterInst :
    core.iter.traits.collect.IntoIterator I (Slice Item) Clause1_IntoIter) :
  Self → I → RustM Out

end p3_symmetric
