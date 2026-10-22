import CompPoly.Fields.Goldilocks
import P3Goldilocks

/-!
# Goldilocks: what the model's values mean

A Rust `Goldilocks` is one `u64`, not necessarily reduced.

* `toField` reads it as an element of CompPoly's `Goldilocks.Field`, `ZMod p` with `p = 2^64 - 2^32 + 1`.
* Every `u64` stands for its residue, so `x` and `x + p` stand for the same element.
* `Canonical` says the stored `u64` is below `p`.
* No claim assumes `Canonical` of an input.
-/

open Aeneas Aeneas.Std

namespace Plonky3Lean.Spec.Goldilocks

/-- A Goldilocks field element as the model has it: Rust's `Goldilocks`. -/
abbrev Element := p3_goldilocks.goldilocks.Goldilocks

/-- The field element a stored `u64` stands for: its residue mod `p`. -/
def toField (x : Element) : Goldilocks.Field :=
  (x.value.val : Goldilocks.Field)

/-- The stored `u64` is fully reduced, `< p`. -/
def Canonical (x : Element) : Prop :=
  x.value.val < Goldilocks.fieldSize

end Plonky3Lean.Spec.Goldilocks
