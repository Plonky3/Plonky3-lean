import P3BabyBear

/-!
# BabyBear: names for the model's constants

`abbrev`s naming the trait constants and instances that aeneas generated for
`BabyBearParameters`, so that claims about them read in Rust's terms. Each is
an alias of a generated definition and adds nothing to it. The specification
the claims compare these constants against is CompPoly's
`CompPoly.Fields.BabyBear`, not anything here.

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

end Plonky3Lean.Spec.BabyBear
