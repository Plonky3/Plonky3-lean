/-
# `p3-util`: what the field crates use from it that aeneas does not supply

* `branch_hint`, which p3-goldilocks calls on rare branches of its arithmetic.
  Its body is an empty inline `asm!` on the architectures that support one,
  and nothing elsewhere.
  aeneas rejects inline assembly, so it is transcribed below.
-/
module

public import P3Util.Extraction

@[expose] public section
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM ControlFlow Error

namespace p3_util

/-- [p3_util::branch_hint]. Upstream: `util/src/lib.rs:396`.

The body is `asm!("", options(nomem, nostack, preserves_flags))`, or nothing.

The empty template touches no memory, stack or flags, and returns. -/
def branch_hint : RustM Unit :=
  ok ()

end p3_util
