import CompPoly.Fields.BabyBear
import Plonky3Lean.Proofs.Field.BabyBear

/-!
# BabyBear: claims

What this repository asserts about p3-baby-bear, at the Plonky3 commit pinned
in `plonky3/`. The model is the extraction in `crates/baby-bear` and the scoped
extraction in `crates/monty-31`; `PRIME`, `MontyParams` and the other names are
`Plonky3Lean.Spec.BabyBear`'s aliases for its constants, and `BabyBear.*` is
CompPoly's specification of the field.

Not claimed: anything about field arithmetic (addition, multiplication,
Montgomery reduction, inversion), the Poseidon1 and Poseidon2 permutations or
the MDS layer, and the two round-constant length assertions that aeneas names
`poseidon1._` and `poseidon2._`.
-/

open Aeneas Aeneas.Std CoreModels
open p3_baby_bear
open Plonky3Lean.Spec.BabyBear

namespace Plonky3Lean.Claims.BabyBear

/-! ## `BabyBearParameters`: the trait instances return these constants -/

theorem baby_bear.BabyBearParameters.PRIME.from_instance :
    MontyParams.PRIME = .ok PRIME :=
  Proofs.BabyBear.baby_bear.BabyBearParameters.PRIME.from_instance

theorem baby_bear.BabyBearParameters.MONTY_MU.from_instance :
    MontyParams.MONTY_MU = .ok MONTY_MU :=
  Proofs.BabyBear.baby_bear.BabyBearParameters.MONTY_MU.from_instance

theorem baby_bear.BabyBearParameters.MONTY_BITS.from_instance :
    MontyParams.MONTY_BITS = .ok MONTY_BITS :=
  Proofs.BabyBear.baby_bear.BabyBearParameters.MONTY_BITS.from_instance

theorem baby_bear.BabyBearParameters.TWO_ADICITY.from_instance :
    TwoAdicParams.TWO_ADICITY = .ok TWO_ADICITY :=
  Proofs.BabyBear.baby_bear.BabyBearParameters.TWO_ADICITY.from_instance

/-! ## `BabyBearParameters`: the constants against the specification -/

/-- `PRIME` is CompPoly's `BabyBear.fieldSize`, `2^31 - 2^27 + 1`. -/
theorem baby_bear.BabyBearParameters.PRIME.eq_fieldSize :
    PRIME.val = BabyBear.fieldSize :=
  Proofs.BabyBear.baby_bear.BabyBearParameters.PRIME.eq_fieldSize

/-- The modulus is prime. -/
theorem baby_bear.BabyBearParameters.PRIME.is_prime :
    Nat.Prime PRIME.val :=
  Proofs.BabyBear.baby_bear.BabyBearParameters.PRIME.is_prime

/-- `gcd(7, p - 1) = 1`, so `x ↦ x^7` permutes the field. -/
theorem baby_bear.BabyBearParameters.PRIME.coprime_seven_pred :
    Nat.Coprime 7 (PRIME.val - 1) :=
  Proofs.BabyBear.baby_bear.BabyBearParameters.PRIME.coprime_seven_pred

/-- `MONTY_BITS` is `32`. -/
theorem baby_bear.BabyBearParameters.MONTY_BITS.val_eq_32 :
    MONTY_BITS.val = 32 :=
  Proofs.BabyBear.baby_bear.BabyBearParameters.MONTY_BITS.val_eq_32

/-- `PRIME · MONTY_MU ≡ 1 (mod 2^32)`. -/
theorem baby_bear.BabyBearParameters.MONTY_MU.inverse :
    (PRIME.val * MONTY_MU.val) % (2 ^ 32) = 1 :=
  Proofs.BabyBear.baby_bear.BabyBearParameters.MONTY_MU.inverse

/-- `TWO_ADICITY` is CompPoly's `BabyBear.twoAdicity`, 27. -/
theorem baby_bear.BabyBearParameters.TWO_ADICITY.eq_twoAdicity :
    TWO_ADICITY.val = BabyBear.twoAdicity :=
  Proofs.BabyBear.baby_bear.BabyBearParameters.TWO_ADICITY.eq_twoAdicity

/-- `p - 1 = 2^TWO_ADICITY · 15`. -/
theorem baby_bear.BabyBearParameters.TWO_ADICITY.factorization :
    PRIME.val - 1 = 2 ^ TWO_ADICITY.val * 15 :=
  Proofs.BabyBear.baby_bear.BabyBearParameters.TWO_ADICITY.factorization

/-- `2^TWO_ADICITY` is the largest power of two dividing `p - 1`. -/
theorem baby_bear.BabyBearParameters.TWO_ADICITY.maximal :
    ¬ 2 ^ (TWO_ADICITY.val + 1) ∣ PRIME.val - 1 :=
  Proofs.BabyBear.baby_bear.BabyBearParameters.TWO_ADICITY.maximal

/-! ## The `BabyBear` constructors -/

/-- `BabyBear::new x` never panics and returns the Montgomery form
`x · 2^32 mod p`. This includes that the four compile-time assertions on the
parameters in `MontyField31::new` pass. -/
theorem baby_bear.BabyBear.new.montgomery_form (x : Std.U32) :
    p3_monty_31.monty_31.MontyField31.new MontyParams x
      ⦃ r => r.value.val = x.val * 2 ^ 32 % BabyBear.fieldSize ⦄ :=
  Proofs.BabyBear.baby_bear.BabyBear.new.montgomery_form x

/-- `BabyBear::new_array` never panics. About the hand-written transcription
of the Rust function (`crates/monty-31`, `Assumptions/Mirror.lean`). -/
theorem baby_bear.BabyBear.new_array.never_panics {N : Std.Usize} (input : Array Std.U32 N) :
    ∃ r, p3_monty_31.monty_31.MontyField31.new_array MontyParams input = .ok r :=
  Proofs.BabyBear.baby_bear.BabyBear.new_array.never_panics input

/-- `BabyBear::new_2d_array` never panics. About the hand-written
transcription, like `new_array`. -/
theorem baby_bear.BabyBear.new_2d_array.never_panics {N M : Std.Usize}
    (input : Array (Array Std.U32 N) M) :
    ∃ r, p3_monty_31.monty_31.MontyField31.new_2d_array MontyParams input = .ok r :=
  Proofs.BabyBear.baby_bear.BabyBear.new_2d_array.never_panics input

/-! ## The Poseidon round-constant length assertions

Nine of the eleven `const _: () = assert!(..)` in `baby-bear/src/poseidon{1,2}.rs`
hold. -/

/-- `baby-bear/src/poseidon1.rs:70`, on `BABYBEAR_POSEIDON1_RC_24`. -/
theorem poseidon1.const_check_1.holds : poseidon1.const_check_1 ⦃ _ => True ⦄ :=
  Proofs.BabyBear.poseidon1.const_check_1.holds

/-- `baby-bear/src/poseidon2.rs:66`, on `BABYBEAR_POSEIDON2_RC_16_EXTERNAL_FINAL`. -/
theorem poseidon2.const_check_1.holds : poseidon2.const_check_1 ⦃ _ => True ⦄ :=
  Proofs.BabyBear.poseidon2.const_check_1.holds

/-- `baby-bear/src/poseidon2.rs:68`, on `BABYBEAR_POSEIDON2_RC_16_INTERNAL`. -/
theorem poseidon2.const_check_2.holds : poseidon2.const_check_2 ⦃ _ => True ⦄ :=
  Proofs.BabyBear.poseidon2.const_check_2.holds

/-- `baby-bear/src/poseidon2.rs:70`, on `BABYBEAR_POSEIDON2_RC_24_EXTERNAL_INITIAL`. -/
theorem poseidon2.const_check_3.holds : poseidon2.const_check_3 ⦃ _ => True ⦄ :=
  Proofs.BabyBear.poseidon2.const_check_3.holds

/-- `baby-bear/src/poseidon2.rs:72`, on `BABYBEAR_POSEIDON2_RC_24_EXTERNAL_FINAL`. -/
theorem poseidon2.const_check_4.holds : poseidon2.const_check_4 ⦃ _ => True ⦄ :=
  Proofs.BabyBear.poseidon2.const_check_4.holds

/-- `baby-bear/src/poseidon2.rs:74`, on `BABYBEAR_POSEIDON2_RC_24_INTERNAL`. -/
theorem poseidon2.const_check_5.holds : poseidon2.const_check_5 ⦃ _ => True ⦄ :=
  Proofs.BabyBear.poseidon2.const_check_5.holds

/-- `baby-bear/src/poseidon2.rs:76`, on `BABYBEAR_POSEIDON2_RC_32_EXTERNAL_INITIAL`. -/
theorem poseidon2.const_check_6.holds : poseidon2.const_check_6 ⦃ _ => True ⦄ :=
  Proofs.BabyBear.poseidon2.const_check_6.holds

/-- `baby-bear/src/poseidon2.rs:78`, on `BABYBEAR_POSEIDON2_RC_32_EXTERNAL_FINAL`. -/
theorem poseidon2.const_check_7.holds : poseidon2.const_check_7 ⦃ _ => True ⦄ :=
  Proofs.BabyBear.poseidon2.const_check_7.holds

/-- `baby-bear/src/poseidon2.rs:80`, on `BABYBEAR_POSEIDON2_RC_32_INTERNAL`. -/
theorem poseidon2.const_check_8.holds : poseidon2.const_check_8 ⦃ _ => True ⦄ :=
  Proofs.BabyBear.poseidon2.const_check_8.holds

end Plonky3Lean.Claims.BabyBear
