/-
The binary PCS's query count, which p3-security computes in floating point.

aeneas has no floating-point operations (docs/extractor-issues.md 19).

The count is an opaque function of the target, the rate and the grinding bits.

The computation never panics: its saturating operations and its cast from f64 to usize all saturate.
-/
module

public import Aeneas
public import CoreModels

@[expose] public section
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM

namespace p3_security

/-- The query count for a target, a log inverse rate and grinding bits.

Assumed: p3-security derives it from a floating-point bound, which aeneas cannot translate. -/
opaque binary.BinaryPcsRegime.queriesForTargetCount : Std.Usize → Std.Usize → Std.Usize → Std.Usize

/-- The query count, which never panics. -/
def binary.BinaryPcsRegime.queries_for_target (security_level log_inv_rate query_pow_bits : Std.Usize) :
    RustM Std.Usize :=
  ok (binary.BinaryPcsRegime.queriesForTargetCount security_level log_inv_rate query_pow_bits)

end p3_security
