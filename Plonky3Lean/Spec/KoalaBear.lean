import CompPoly.Fields.KoalaBear
import P3KoalaBear
import Plonky3Lean.Spec.Monty31
import ToCompPoly.Fields.KoalaBear.Extension
import ToCompPoly.Fields.KoalaBear.Quintic

/-!
# KoalaBear: what the model's values mean

KoalaBear is p3-monty-31 at `p = 2^31 - 2^24 + 1`, so its elements mean what any `MontyField31` element means.

* **What an element means.**
  `toField` and `Canonical` are the generic `Plonky3Lean.Spec.Monty31` ones at `p`, landing in CompPoly's `KoalaBear.Field`.
  `toExt` reads an array of coefficients as an element of a binomial extension `F[X] / (X ^ D - w)`.
  `toQuintic` reads one as an element of the quintic extension `F[X] / (X ^ 5 + X ^ 2 - 1)`.
* **Names for the model's constants.**
  `abbrev`s for the trait constants and instances that aeneas generated for `KoalaBearParameters`.
  Each is an alias of a generated definition and adds nothing to it.

Each constant is read through the trait instance the extracted code builds.
A statement about it is about the value the code sees.
-/

open Aeneas Aeneas.Std CoreModels
open p3_koala_bear

namespace Plonky3Lean.Spec.KoalaBear

/-- The `MontyParameters` instance aeneas generated for `KoalaBearParameters`. -/
noncomputable abbrev MontyParams :=
  koala_bear.KoalaBearParameters.Insts.P3_monty_31Data_traitsMontyParameters

/-- The `TwoAdicData` instance aeneas generated for `KoalaBearParameters`. -/
noncomputable abbrev TwoAdicParams :=
  koala_bear.KoalaBearParameters.Insts.P3_monty_31Data_traitsTwoAdicDataSharedStaticSliceMontyField31KoalaBearParameters

/-- The `FieldParameters` instance aeneas generated for `KoalaBearParameters`.

It sets `MONTY_GEN` and keeps p3-monty-31's defaults for `MONTY_ZERO`, `MONTY_ONE`, `MONTY_TWO`, `MONTY_NEG_ONE` and `HALF_P_PLUS_1`. -/
noncomputable abbrev FieldParams :=
  koala_bear.KoalaBearParameters.Insts.P3_monty_31Data_traitsFieldParameters

/-- The `BinomialExtensionData<4>` instance aeneas generated for `KoalaBearParameters`. -/
noncomputable abbrev Ext4Params :=
  koala_bear.KoalaBearParameters.Insts.P3_monty_31Data_traitsBinomialExtensionDataArrayArrayMontyField31KoalaBearParameters424

/-- The `BinomialExtensionData<8>` instance aeneas generated for `KoalaBearParameters`. -/
noncomputable abbrev Ext8Params :=
  koala_bear.KoalaBearParameters.Insts.P3_monty_31Data_traitsBinomialExtensionDataArrayArrayMontyField31KoalaBearParameters838

/-- The `TrinomialQuinticData` instance aeneas generated for `KoalaBearParameters`. -/
noncomputable abbrev QuinticParams :=
  koala_bear.KoalaBearParameters.Insts.P3_monty_31Data_traitsTrinomialQuinticDataArrayArrayMontyField31KoalaBearParameters50

/-- `KoalaBearParameters::PRIME` (`koala-bear/src/koala_bear.rs`). -/
abbrev PRIME : Std.U32 :=
  koala_bear.KoalaBearParameters.Insts.P3_monty_31Data_traitsMontyParameters.PRIME

/-- `KoalaBearParameters::MONTY_MU`. -/
abbrev MONTY_MU : Std.U32 :=
  koala_bear.KoalaBearParameters.Insts.P3_monty_31Data_traitsMontyParameters.MONTY_MU

/-- `KoalaBearParameters::MONTY_BITS`. -/
abbrev MONTY_BITS : Std.U32 :=
  koala_bear.KoalaBearParameters.Insts.P3_monty_31Data_traitsMontyParameters.MONTY_BITS

/-- `KoalaBearParameters::TWO_ADICITY`. -/
abbrev TWO_ADICITY : Std.Usize :=
  koala_bear.KoalaBearParameters.Insts.P3_monty_31Data_traitsTwoAdicDataSharedStaticSliceMontyField31KoalaBearParameters.TWO_ADICITY

/-! ## What an element means -/

/-- A KoalaBear field element as the model has it: Rust's `KoalaBear = MontyField31<KoalaBearParameters>`. -/
abbrev Element := Monty31.Element koala_bear.KoalaBearParameters

/-- The field element an `Element` stands for, in CompPoly's `KoalaBear.Field`.

It is the generic Montgomery decoding at `p = 2^31 - 2^24 + 1`: the stored `u32` times `2^(-32)`. -/
abbrev toField (x : Element) : KoalaBear.Field :=
  Monty31.toField KoalaBear.fieldSize x

/-- The representation invariant: the stored value is fully reduced, `< p`. -/
abbrev Canonical (x : Element) : Prop :=
  Monty31.Canonical KoalaBear.fieldSize x

/-! ## What an extension-field element means -/

open Polynomial in
/-- The element `Σ j, c_j · X ^ j` of `F[X] / (X ^ D - w)` that a coefficient array stands for.

Each coefficient is read through `toField`.
This is how `BinomialExtensionField<KoalaBear, D>` stores an element, with `X ^ D = W`. -/
noncomputable def toExt {D : Usize} (w : KoalaBear.Field) (coeffs : Array Element D) :
    AdjoinRoot (X ^ D.val - C w) :=
  KoalaBear.ofCoeffs D.val w (coeffs.val.map toField)

/-- The element `Σ j, c_j · X ^ j` of `F[X] / (X ^ 5 + X ^ 2 - 1)` that a coefficient array stands for.

This is how `QuinticTrinomialExtensionField<KoalaBear>` stores an element, with `X ^ 5 = 1 - X ^ 2`. -/
noncomputable def toQuintic (coeffs : Array Element 5#usize) : KoalaBear.Ext5 :=
  KoalaBear.ofQuinticCoeffs (coeffs.val.map toField)

end Plonky3Lean.Spec.KoalaBear
