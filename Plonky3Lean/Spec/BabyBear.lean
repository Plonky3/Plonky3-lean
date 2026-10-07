import CompPoly.Fields.BabyBear
import P3BabyBear

/-!
# BabyBear: what the model's values mean

Two things the BabyBear claims are stated in.

* **What an element means.** A Rust `BabyBear` is a `MontyField31` whose `u32`
  holds the element in Montgomery form: the element `a` is stored as
  `a · 2^32 mod p`. `toField` decodes a stored value into CompPoly's
  `BabyBear.Field` (`ZMod p`), the specification every claim compares against,
  and `Canonical` is the invariant the Rust relies on, that the stored value is
  fully reduced. These two definitions are the whole of the interpretation: a
  claim about field arithmetic or a field constant says something about
  `toField` of the model's values.
* **Names for the model's constants.** `abbrev`s naming the trait constants and
  instances that aeneas generated for `BabyBearParameters`, so that claims
  about them read in Rust's terms. Each is an alias of a generated definition
  and adds nothing to it.

Each constant is read *through the trait instance* the extracted code builds,
so a statement about it is about the value the code sees, not a free-standing
literal.
-/

open Aeneas Aeneas.Std CoreModels
open p3_baby_bear

namespace Plonky3Lean.Spec.BabyBear

/-- The `MontyParameters` instance aeneas generated for `BabyBearParameters`. -/
noncomputable abbrev MontyParams :=
  baby_bear.BabyBearParameters.Insts.P3_monty_31Data_traitsMontyParameters

/-- The `TwoAdicData` instance aeneas generated for `BabyBearParameters`. -/
noncomputable abbrev TwoAdicParams :=
  baby_bear.BabyBearParameters.Insts.P3_monty_31Data_traitsTwoAdicDataSharedStaticSliceMontyField31BabyBearParameters

/-- `BabyBearParameters::PRIME` (`baby-bear/src/baby_bear.rs`). -/
abbrev PRIME : Std.U32 :=
  baby_bear.BabyBearParameters.Insts.P3_monty_31Data_traitsMontyParameters.PRIME

/-- `BabyBearParameters::MONTY_MU`. -/
abbrev MONTY_MU : Std.U32 :=
  baby_bear.BabyBearParameters.Insts.P3_monty_31Data_traitsMontyParameters.MONTY_MU

/-- `BabyBearParameters::MONTY_BITS`. -/
abbrev MONTY_BITS : Std.U32 :=
  baby_bear.BabyBearParameters.Insts.P3_monty_31Data_traitsMontyParameters.MONTY_BITS

/-- `BabyBearParameters::TWO_ADICITY`. -/
abbrev TWO_ADICITY : Std.Usize :=
  baby_bear.BabyBearParameters.Insts.P3_monty_31Data_traitsTwoAdicDataSharedStaticSliceMontyField31BabyBearParameters.TWO_ADICITY

/-! ## What an element means -/

/-- A BabyBear field element as the model has it: Rust's
`BabyBear = MontyField31<BabyBearParameters>`, a `u32` in Montgomery form. -/
abbrev Element := p3_monty_31.monty_31.MontyField31 baby_bear.BabyBearParameters

/-- The field element an `Element` stands for. Its stored `u32` is `a · 2^32 mod p`
for the element `a`, so `a` is the stored value times `2^-32`, in CompPoly's
`BabyBear.Field` (`ZMod p`, `p = 2^31 - 2^27 + 1`). -/
def toField (x : Element) : BabyBear.Field :=
  (x.value.val : BabyBear.Field) * (2 ^ 32 : BabyBear.Field)⁻¹

/-- The representation invariant: the stored value is fully reduced, `< p`. With
it, each field element has exactly one stored value, which the Rust relies on
(for example, `PartialEq` compares stored values). -/
def Canonical (x : Element) : Prop :=
  x.value.val < BabyBear.fieldSize

end Plonky3Lean.Spec.BabyBear
