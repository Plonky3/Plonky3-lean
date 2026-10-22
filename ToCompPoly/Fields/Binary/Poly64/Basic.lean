/-
Copyright (c) 2026 CompPoly. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Coratger
-/
import CompPoly.Fields.Binary.Common

/-!
# `GF(2^64)` modulo `X^64 + X^4 + X^3 + X + 1`

The modulus, its tail, and the quotient ring.
-/

namespace Poly64

open Polynomial

/-- The modulus `X^64 + X^4 + X^3 + X + 1` over `GF(2)`. -/
noncomputable def modulus : (ZMod 2)[X] := X ^ 64 + X ^ 4 + X ^ 3 + X + 1

/-- The tail `X^4 + X^3 + X + 1`, which `X^64` reduces to. -/
noncomputable def tail : (ZMod 2)[X] := X ^ 4 + X ^ 3 + X + 1

theorem modulus_eq_X_pow_add_tail : modulus = X ^ 64 + tail := by
  unfold modulus tail
  ring

/-- `GF(2)[X] / (X^64 + X^4 + X^3 + X + 1)`. -/
abbrev Quot := AdjoinRoot modulus

end Poly64
