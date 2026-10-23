/-
The constants of the `blake3` crate that p3-blake3 references, transcribed.

Each is a `[[mirror]]` in crates/blake3-crate/crate.toml.
-/
module

public import Aeneas
public import CoreModels

@[expose] public section

open Aeneas Aeneas.Std

namespace blake3

/-- `blake3::BLOCK_LEN`: the bytes of a block, `64`. -/
def BLOCK_LEN : RustM Std.Usize := .ok 64#usize

/-- `blake3::CHUNK_LEN`: the bytes of a chunk, `1024`. -/
def CHUNK_LEN : RustM Std.Usize := .ok 1024#usize

/-- `blake3::OUT_LEN`: the bytes of a digest, `32`. -/
def OUT_LEN : RustM Std.Usize := .ok 32#usize

end blake3
