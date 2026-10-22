import CompPoly.Fields.Mersenne
import P3Mersenne31

/-!
# Mersenne31: what the model's values mean

A Rust `Mersenne31` is a `u32` that holds the element itself, not a Montgomery form.

* **The invariant.** The stored value fits in 31 bits, `value < 2^31`, as the field's doc comment requires (`mersenne-31/src/mersenne_31.rs:37`).

  So `value` is in `[0, p]` for `p = 2^31 - 1`, and zero has two representations, `0` and `p`.

  `Valid` is this invariant, and nothing more.

* **An element.** `toField` reads the stored value in CompPoly's `Mersenne31.Field` (`ZMod p`), where `p` and `0` are both zero.

  `Canonical` says the stored value is in `[0, p)`, the stricter form that `as_canonical_u32` returns.
-/

open Aeneas Aeneas.Std CoreModels
open p3_mersenne_31

namespace Plonky3Lean.Spec.Mersenne31

/-- A Mersenne31 field element as the model has it: Rust's `Mersenne31`, one `u32`. -/
abbrev Element := mersenne_31.Mersenne31

/-- The representation invariant: the stored value fits in 31 bits. -/
def Valid (x : Element) : Prop :=
  x.value.val < 2 ^ 31

/-- The stored value is fully reduced, in `[0, p)`. -/
def Canonical (x : Element) : Prop :=
  x.value.val < Mersenne31.fieldSize

/-- The field element a stored value stands for. -/
def toField (x : Element) : Mersenne31.Field :=
  (x.value.val : Mersenne31.Field)

end Plonky3Lean.Spec.Mersenne31
