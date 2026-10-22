import P3BabyBear
import Plonky3Lean.Proofs.Field.BabyBear.Arith
import Plonky3Lean.Proofs.Field.Monty31.Reduce

/-!
# Monty31: a valid prime below `2^30`

The prime `2^29 - 3` passes every check `MontyField31::new` makes.

For it, the 96-bit reduction leaves its low limb out of range.
-/

open Aeneas Aeneas.Std CoreModels
open p3_monty_31 p3_baby_bear
open Plonky3Lean.Spec.Monty31

namespace Plonky3Lean.Proofs.Monty31.Findings

/-- `MontyParameters` at the prime `2^29 - 3`, otherwise BabyBear's. -/
@[reducible]
def thirtyBit : data_traits.MontyParameters baby_bear.BabyBearParameters :=
  { baby_bear.BabyBearParameters.Insts.P3_monty_31Data_traitsMontyParameters with
    PRIME := .ok 536870909#u32
    MONTY_MU := .ok 894784853#u32 }

/-- The prime `2^29 - 3` is odd, below `2^31`, with `MONTY_MU` its inverse modulo `2^32`. -/
theorem thirtyBit_valid : Valid thirtyBit 536870909#u32 894784853#u32 where
  prime := rfl
  bits := by
    show RustM.ok baby_bear.BabyBearParameters.Insts.P3_monty_31Data_traitsMontyParameters.MONTY_BITS = _
    unfold baby_bear.BabyBearParameters.Insts.P3_monty_31Data_traitsMontyParameters.MONTY_BITS
    rfl
  monty_mu := rfl
  mask := Proofs.BabyBear.MontyParams.MONTY_MASK.eq
  odd := by decide
  lt := by decide
  inv := by decide

/-- For `x = 2^64 - 1` and `p = 2^29 - 3`, one subtraction leaves the low limb too large.

```text
  lo                  = 2^64 - 1
  lo - 2 · 2^32 · p  >= 2 · 2^32 · p    (outside the inner reduction's domain)
```
-/
theorem thirtyBit_low_limb_out_of_range :
    let p := 536870909
    let lo := 2 ^ 64 - 1
    2 * 2 ^ 32 * p ≤ lo ∧ 2 * 2 ^ 32 * p ≤ lo - 2 * 2 ^ 32 * p := by
  decide

end Plonky3Lean.Proofs.Monty31.Findings
