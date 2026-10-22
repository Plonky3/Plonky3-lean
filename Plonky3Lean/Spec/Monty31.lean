import Mathlib.Data.ZMod.Basic
import P3Monty31

/-!
# Monty31: what a `MontyField31` means, for any parameters

p3-monty-31 implements one field per `MontyParameters` impl.

That covers BabyBear, KoalaBear, and any 31-bit prime a downstream crate picks.

The code is generic, so its specification is too.

* **The parameters.** `Valid` is exactly what `MontyField31::new` asserts, in a `const` block:

  - `PRIME` is odd,
  - `PRIME < 2^31`,
  - `MONTY_BITS = 32`,
  - `PRIME · MONTY_MU ≡ 1 (mod 2^32)`.

  It also records that `MONTY_MASK` keeps its default, `2^32 - 1`.

  A proof that needs more than this has found a property the Rust relies on and does not check.

* **An element.** The stored `u32` holds the element `a` in Montgomery form, `a · 2^32 mod p`.

  `toField` decodes it into `ZMod p`.

  `Canonical` says it is fully reduced, `< p`, which equality and hashing rely on.
-/

open Aeneas Aeneas.Std CoreModels
open p3_monty_31

namespace Plonky3Lean.Spec.Monty31

/-- The parameters of a `MontyParameters` impl, as `MontyField31::new` checks them.

`p` is `PRIME` and `mu` is `MONTY_MU`. -/
structure Valid {MP : Type} (inst : data_traits.MontyParameters MP) (p mu : Std.U32) : Prop where
  prime : inst.PRIME = .ok p
  bits : inst.MONTY_BITS = .ok 32#u32
  monty_mu : inst.MONTY_MU = .ok mu
  mask : inst.MONTY_MASK = .ok 4294967295#u32
  odd : p.val % 2 = 1
  lt : p.val < 2 ^ 31
  inv : p.val * mu.val % 2 ^ 32 = 1

/-- The parameters of a `FieldParameters` impl: valid `MontyParameters`.

`HALF_P_PLUS_1` keeps its default `(p + 1) / 2`, which halving relies on. -/
structure FieldValid {FP : Type} (inst : data_traits.FieldParameters FP) (p mu : Std.U32) : Prop where
  monty : Valid inst.PackedMontyParametersInst.MontyParametersInst p mu
  half : ∃ h : Std.U32, inst.HALF_P_PLUS_1 = .ok h ∧ h.val = (p.val + 1) / 2

/-- The named elements of a `FieldParameters` impl keep their defaults.

`MONTY_ZERO`, `MONTY_ONE` and `MONTY_TWO` are `new(0)`, `new(1)` and `new(2)`.

An impl may override them, and nothing checks an override. -/
structure FieldDefaults {FP : Type} (inst : data_traits.FieldParameters FP) : Prop where
  zero : inst.MONTY_ZERO =
    monty_31.MontyField31.new inst.PackedMontyParametersInst.MontyParametersInst 0#u32
  one : inst.MONTY_ONE =
    monty_31.MontyField31.new inst.PackedMontyParametersInst.MontyParametersInst 1#u32
  two : inst.MONTY_TWO =
    monty_31.MontyField31.new inst.PackedMontyParametersInst.MontyParametersInst 2#u32

/-- A field element as the model has it: Rust's `MontyField31<MP>`. -/
abbrev Element (MP : Type) := monty_31.MontyField31 MP

/-- The element of `ZMod p` that a stored value stands for: the stored `u32` times `2^(-32)`. -/
def toField {MP : Type} (p : ℕ) (x : Element MP) : ZMod p :=
  (x.value.val : ZMod p) * (2 ^ 32 : ZMod p)⁻¹

/-- The representation invariant: the stored value is fully reduced. -/
def Canonical {MP : Type} (p : ℕ) (x : Element MP) : Prop :=
  x.value.val < p

end Plonky3Lean.Spec.Monty31
