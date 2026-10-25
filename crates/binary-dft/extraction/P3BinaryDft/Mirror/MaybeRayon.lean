/-
The serial pool of p3-maybe-rayon, which the transforms read their worker count from.

maybe-rayon has no Lean library, so the one item the transforms call is transcribed here.
-/
module

public import Aeneas
public import CoreModels

@[expose] public section
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc

namespace p3_maybe_rayon

/-- The worker count of the serial pool, which is one. -/
def serial.current_num_threads : RustM Std.Usize := .ok 1#usize

end p3_maybe_rayon
