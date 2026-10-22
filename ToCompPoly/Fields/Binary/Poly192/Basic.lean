/-
Copyright (c) 2026 CompPoly. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Coratger
-/
import ToCompPoly.Fields.Binary.Poly64.Basic

/-!
# `GF(2^192)` as a cubic extension of `GF(2^64)`

The extension is `GF(2^64)[Y] / (Y^3 + Y + 1)`.

An element is given by three coefficients `c_0 + c_1 Y + c_2 Y^2`.
-/

namespace Poly192

open Polynomial

/-- The modulus `Y^3 + Y + 1` over `GF(2^64)`. -/
noncomputable def modulus : Poly64.Quot[X] := X ^ 3 + X + 1

/-- `GF(2^64)[Y] / (Y^3 + Y + 1)`. -/
abbrev Quot := AdjoinRoot modulus

/-- The element `c_0 + c_1 Y + c_2 Y^2`. -/
noncomputable def ofCoeffs (c₀ c₁ c₂ : Poly64.Quot) : Quot :=
  AdjoinRoot.mk modulus (C c₀ + C c₁ * X + C c₂ * X ^ 2)

end Poly192
