import CompPoly.Fields.BabyBear
import Plonky3Lean.Proofs.Field.BabyBear
import Plonky3Lean.Proofs.Field.BabyBear.Element

/-!
# BabyBear: claims

What this repository asserts about p3-baby-bear, at the Plonky3 commit pinned
in `plonky3/`. The model is the extraction in `crates/baby-bear` and the scoped
extraction in `crates/monty-31`; `PRIME`, `MontyParams` and the other names are
`Plonky3Lean.Spec.BabyBear`'s aliases for its constants, and `BabyBear.*` is
CompPoly's specification of the field.

Not claimed: anything about field arithmetic (addition, multiplication,
Montgomery reduction, inversion), the Poseidon1 and Poseidon2 permutations or
the MDS layer, the values of the round constants, and the two round-constant
length assertions that aeneas names `poseidon1._` and `poseidon2._`.
-/

open Aeneas Aeneas.Std CoreModels
open p3_baby_bear
open Plonky3Lean.Spec.BabyBear

namespace Plonky3Lean.Claims.BabyBear

/-! ## `BabyBearParameters`: the trait instances return these constants

aeneas turns each associated constant of a trait impl into a field of the
generated instance, of type `RustM _`. These four claims say that reading a
constant through the instance, as generic code such as `MontyField31::new`
does, returns the named constant without failing. The claims below about
`PRIME`, `MONTY_MU`, `MONTY_BITS` and `TWO_ADICITY` therefore apply to the
values that generic code sees. -/

/-- Reading `<BabyBearParameters as MontyParameters>::PRIME` through the
generated `MontyParameters` instance returns `PRIME`, without failing. -/
theorem baby_bear.BabyBearParameters.PRIME.from_instance :
    MontyParams.PRIME = .ok PRIME :=
  Proofs.BabyBear.baby_bear.BabyBearParameters.PRIME.from_instance

/-- Reading `<BabyBearParameters as MontyParameters>::MONTY_MU` through the
generated `MontyParameters` instance returns `MONTY_MU`, without failing. -/
theorem baby_bear.BabyBearParameters.MONTY_MU.from_instance :
    MontyParams.MONTY_MU = .ok MONTY_MU :=
  Proofs.BabyBear.baby_bear.BabyBearParameters.MONTY_MU.from_instance

/-- Reading `<BabyBearParameters as MontyParameters>::MONTY_BITS` through the
generated `MontyParameters` instance returns `MONTY_BITS`, without failing. -/
theorem baby_bear.BabyBearParameters.MONTY_BITS.from_instance :
    MontyParams.MONTY_BITS = .ok MONTY_BITS :=
  Proofs.BabyBear.baby_bear.BabyBearParameters.MONTY_BITS.from_instance

/-- Reading `TWO_ADICITY` through the generated `TwoAdicData` instance of
`BabyBearParameters` returns `TWO_ADICITY`, without failing. -/
theorem baby_bear.BabyBearParameters.TWO_ADICITY.from_instance :
    TwoAdicParams.TWO_ADICITY = .ok TWO_ADICITY :=
  Proofs.BabyBear.baby_bear.BabyBearParameters.TWO_ADICITY.from_instance

/-! ## `BabyBearParameters`: the constants against the specification

Each claim reads a constant as a natural number (`.val` of the `u32` or
`usize`) and compares it with CompPoly's independent specification of the
BabyBear field, or with a number-theoretic property the Rust relies on. -/

/-- The modulus `PRIME` (`0x78000001` in `baby-bear/src/baby_bear.rs`) is
CompPoly's `BabyBear.fieldSize`, `2^31 - 2^27 + 1 = 2013265921`: the extracted
field and the specified one have the same order. -/
theorem baby_bear.BabyBearParameters.PRIME.eq_fieldSize :
    PRIME.val = BabyBear.fieldSize :=
  Proofs.BabyBear.baby_bear.BabyBearParameters.PRIME.eq_fieldSize

/-- The modulus `PRIME` is a prime number, so the integers modulo it form a
field. The proof uses CompPoly's Pratt certificate for `BabyBear.fieldSize`. -/
theorem baby_bear.BabyBearParameters.PRIME.is_prime :
    Nat.Prime PRIME.val :=
  Proofs.BabyBear.baby_bear.BabyBearParameters.PRIME.is_prime

/-- `gcd(7, p - 1) = 1` for the modulus `p = PRIME`. This is the fact behind
BabyBear's `RelativelyPrimePower<7>` impl, which Poseidon's S-box relies on:
it makes `x ↦ x^7` a permutation of the field. (`3` does not work for
BabyBear, since `p - 1 = 2^27 · 3 · 5`.) -/
theorem baby_bear.BabyBearParameters.PRIME.coprime_seven_pred :
    Nat.Coprime 7 (PRIME.val - 1) :=
  Proofs.BabyBear.baby_bear.BabyBearParameters.PRIME.coprime_seven_pred

/-- `MONTY_BITS` is `32`: Montgomery form uses the radix `R = 2^32`, which is
what `MontyField31::new` asserts. Both sides come from the extraction, so this
checks that the constant was extracted correctly, not anything about the
field. -/
theorem baby_bear.BabyBearParameters.MONTY_BITS.val_eq_32 :
    MONTY_BITS.val = 32 :=
  Proofs.BabyBear.baby_bear.BabyBearParameters.MONTY_BITS.val_eq_32

/-- `MONTY_MU` (`0x88000001`) is the inverse of `PRIME` modulo `2^32`:
`PRIME · MONTY_MU ≡ 1 (mod 2^32)`. This is the precondition of Montgomery
reduction, and one of the four assertions in `MontyField31::new`. -/
theorem baby_bear.BabyBearParameters.MONTY_MU.inverse :
    (PRIME.val * MONTY_MU.val) % (2 ^ 32) = 1 :=
  Proofs.BabyBear.baby_bear.BabyBearParameters.MONTY_MU.inverse

/-- `TWO_ADICITY` is CompPoly's `BabyBear.twoAdicity`, `27`: the extracted and
the specified two-adicity agree. -/
theorem baby_bear.BabyBearParameters.TWO_ADICITY.eq_twoAdicity :
    TWO_ADICITY.val = BabyBear.twoAdicity :=
  Proofs.BabyBear.baby_bear.BabyBearParameters.TWO_ADICITY.eq_twoAdicity

/-- `p - 1 = 2^TWO_ADICITY · 15` for the modulus `p = PRIME`. So the field's
multiplicative group has a subgroup of order `2^TWO_ADICITY`, which is the
largest two-adic FFT domain. The odd part `15` is fixed in the statement, so
this on its own does not say that `TWO_ADICITY` is the largest such exponent;
`TWO_ADICITY.maximal` does. -/
theorem baby_bear.BabyBearParameters.TWO_ADICITY.factorization :
    PRIME.val - 1 = 2 ^ TWO_ADICITY.val * 15 :=
  Proofs.BabyBear.baby_bear.BabyBearParameters.TWO_ADICITY.factorization

/-- `2^(TWO_ADICITY + 1)` does not divide `p - 1`, so `2^TWO_ADICITY` is the
largest power of two that divides `p - 1`: `TWO_ADICITY` is exactly the field's
two-adicity, not merely a lower bound for it. -/
theorem baby_bear.BabyBearParameters.TWO_ADICITY.maximal :
    ¬ 2 ^ (TWO_ADICITY.val + 1) ∣ PRIME.val - 1 :=
  Proofs.BabyBear.baby_bear.BabyBearParameters.TWO_ADICITY.maximal

/-! ## The `BabyBear` constructors

`BabyBear` is `MontyField31<BabyBearParameters>`, and its constructors are
`MontyField31`'s at `BabyBearParameters` (`MontyParams`). In Aeneas,
`m ⦃ r => P r ⦄` states that `m` returns a value `r` (it does not panic) and
that `P r` holds. -/

/-- For every `u32` input `x`, `BabyBear::new x` does not panic, and the field
element it returns stores `x · 2^32 mod p` (with `p = BabyBear.fieldSize`):
`x` in Montgomery form, reduced into `[0, p)`. This covers inputs `x ≥ p` too.
`MontyField31::new` first checks four facts about the parameters: `PRIME` is
odd, `PRIME < 2^31`, `MONTY_BITS = 32`, and
`PRIME · MONTY_MU ≡ 1 (mod 2^32)`. In Rust they are compile-time assertions;
Aeneas keeps them as runtime checks, so this claim includes that all four pass
for BabyBear. -/
theorem baby_bear.BabyBear.new.montgomery_form (x : Std.U32) :
    p3_monty_31.monty_31.MontyField31.new MontyParams x
      ⦃ r => r.value.val = x.val * 2 ^ 32 % BabyBear.fieldSize ⦄ :=
  Proofs.BabyBear.baby_bear.BabyBear.new.montgomery_form x

/-- For every array of `N` `u32`s, `BabyBear::new_array` does not panic: it
returns an array of `N` field elements. It says nothing about the values.
Aeneas drops this Rust function, so the claim is about its hand-written
transcription, an elementwise `new` (`crates/monty-31`,
`Assumptions/Mirror.lean`). -/
theorem baby_bear.BabyBear.new_array.never_panics {N : Std.Usize} (input : Array Std.U32 N) :
    ∃ r, p3_monty_31.monty_31.MontyField31.new_array MontyParams input = .ok r :=
  Proofs.BabyBear.baby_bear.BabyBear.new_array.never_panics input

/-- For every `M × N` array of `u32`s, `BabyBear::new_2d_array` does not panic:
it returns an `M × N` array of field elements. It says nothing about the
values. Like `new_array`, the claim is about the hand-written transcription,
`new_array` applied to each row. -/
theorem baby_bear.BabyBear.new_2d_array.never_panics {N M : Std.Usize}
    (input : Array (Array Std.U32 N) M) :
    ∃ r, p3_monty_31.monty_31.MontyField31.new_2d_array MontyParams input = .ok r :=
  Proofs.BabyBear.baby_bear.BabyBear.new_2d_array.never_panics input

/-! ## The constructors, as field elements

`Plonky3Lean.Spec.BabyBear.toField` reads a stored value as the field element it
stands for, in CompPoly's `BabyBear.Field` (`ZMod p`), and `Canonical` says the
stored value is fully reduced. Every constant in `baby-bear/src/baby_bear.rs`
is built by one of these three constructors from literal `u32`s, so these
claims are what the constant claims below rest on. -/

/-- For every `u32` input `x`, `BabyBear::new x` returns the field element
`x mod p`, stored canonically (`< p`). This is `new.montgomery_form` read
through `toField`: the stored `x · 2^32 mod p` decodes to `x`. -/
theorem baby_bear.BabyBear.new.toField (x : Std.U32) :
    p3_monty_31.monty_31.MontyField31.new MontyParams x
      ⦃ r => Canonical r ∧ toField r = (x.val : BabyBear.Field) ⦄ :=
  Proofs.BabyBear.baby_bear.BabyBear.new.toField x

/-- `BabyBear::new_array` returns, for each input `x`, the field element
`x mod p`, in order and stored canonically. About the hand-written
transcription of the Rust function (`crates/monty-31`,
`Assumptions/Mirror.lean`). -/
theorem baby_bear.BabyBear.new_array.toField {N : Std.Usize} (input : Array Std.U32 N) :
    p3_monty_31.monty_31.MontyField31.new_array MontyParams input
      ⦃ r => (∀ y ∈ r.val, Canonical y) ∧
        r.val.map Spec.BabyBear.toField = input.val.map (fun x => (x.val : BabyBear.Field)) ⦄ :=
  Proofs.BabyBear.baby_bear.BabyBear.new_array.toField input

/-- `BabyBear::new_2d_array` returns, for each input `x`, the field element
`x mod p`, row by row and stored canonically. About the hand-written
transcription, like `new_array`. -/
theorem baby_bear.BabyBear.new_2d_array.toField {N M : Std.Usize}
    (input : Array (Array Std.U32 N) M) :
    p3_monty_31.monty_31.MontyField31.new_2d_array MontyParams input
      ⦃ r => (∀ row ∈ r.val, ∀ y ∈ row.val, Canonical y) ∧
        r.val.map (fun row => row.val.map Spec.BabyBear.toField) =
          input.val.map (fun row => row.val.map (fun x => (x.val : BabyBear.Field))) ⦄ :=
  Proofs.BabyBear.baby_bear.BabyBear.new_2d_array.toField input

/-! ## The Poseidon round-constant length assertions

`baby-bear/src/poseidon{1,2}.rs` check the length of each round-constant table
with an anonymous `const _: () = assert!(..)`. Aeneas extracts each one as a
`RustM Unit` computation: it builds the table (through `new_array` or
`new_2d_array`), takes its length, and asserts the comparison. Each claim
`… ⦃ _ => True ⦄` states that the computation does not panic. That is, the
table builds and the assertion holds. Nothing is said about the constants'
values.

Nine of the eleven assertions are claimed. The other two, which Aeneas names
`poseidon1._` (on `BABYBEAR_POSEIDON1_RC_16`) and `poseidon2._` (on
`BABYBEAR_POSEIDON2_RC_16_EXTERNAL_INITIAL`), are not. -/

/-- The Poseidon1 assertion at `baby-bear/src/poseidon1.rs:70` holds: the
width-24 round-constant table `BABYBEAR_POSEIDON1_RC_24` has
`2 · HALF_FULL_ROUNDS + PARTIAL_ROUNDS_24 = 2 · 4 + 21 = 29` rows. -/
theorem poseidon1.const_check_1.holds : poseidon1.const_check_1 ⦃ _ => True ⦄ :=
  Proofs.BabyBear.poseidon1.const_check_1.holds

/-- The Poseidon2 assertion at `baby-bear/src/poseidon2.rs:66` holds: the
width-16 final external round constants,
`BABYBEAR_POSEIDON2_RC_16_EXTERNAL_FINAL`, have `HALF_FULL_ROUNDS = 4` rows. -/
theorem poseidon2.const_check_1.holds : poseidon2.const_check_1 ⦃ _ => True ⦄ :=
  Proofs.BabyBear.poseidon2.const_check_1.holds

/-- The Poseidon2 assertion at `baby-bear/src/poseidon2.rs:68` holds: the
width-16 internal round constants, `BABYBEAR_POSEIDON2_RC_16_INTERNAL`, number
`PARTIAL_ROUNDS_16 = 13`, one per partial round. -/
theorem poseidon2.const_check_2.holds : poseidon2.const_check_2 ⦃ _ => True ⦄ :=
  Proofs.BabyBear.poseidon2.const_check_2.holds

/-- The Poseidon2 assertion at `baby-bear/src/poseidon2.rs:70` holds: the
width-24 initial external round constants,
`BABYBEAR_POSEIDON2_RC_24_EXTERNAL_INITIAL`, have `HALF_FULL_ROUNDS = 4`
rows. -/
theorem poseidon2.const_check_3.holds : poseidon2.const_check_3 ⦃ _ => True ⦄ :=
  Proofs.BabyBear.poseidon2.const_check_3.holds

/-- The Poseidon2 assertion at `baby-bear/src/poseidon2.rs:72` holds: the
width-24 final external round constants,
`BABYBEAR_POSEIDON2_RC_24_EXTERNAL_FINAL`, have `HALF_FULL_ROUNDS = 4` rows. -/
theorem poseidon2.const_check_4.holds : poseidon2.const_check_4 ⦃ _ => True ⦄ :=
  Proofs.BabyBear.poseidon2.const_check_4.holds

/-- The Poseidon2 assertion at `baby-bear/src/poseidon2.rs:74` holds: the
width-24 internal round constants, `BABYBEAR_POSEIDON2_RC_24_INTERNAL`, number
`PARTIAL_ROUNDS_24 = 21`, one per partial round. -/
theorem poseidon2.const_check_5.holds : poseidon2.const_check_5 ⦃ _ => True ⦄ :=
  Proofs.BabyBear.poseidon2.const_check_5.holds

/-- The Poseidon2 assertion at `baby-bear/src/poseidon2.rs:76` holds: the
width-32 initial external round constants,
`BABYBEAR_POSEIDON2_RC_32_EXTERNAL_INITIAL`, have `HALF_FULL_ROUNDS = 4`
rows. -/
theorem poseidon2.const_check_6.holds : poseidon2.const_check_6 ⦃ _ => True ⦄ :=
  Proofs.BabyBear.poseidon2.const_check_6.holds

/-- The Poseidon2 assertion at `baby-bear/src/poseidon2.rs:78` holds: the
width-32 final external round constants,
`BABYBEAR_POSEIDON2_RC_32_EXTERNAL_FINAL`, have `HALF_FULL_ROUNDS = 4` rows. -/
theorem poseidon2.const_check_7.holds : poseidon2.const_check_7 ⦃ _ => True ⦄ :=
  Proofs.BabyBear.poseidon2.const_check_7.holds

/-- The Poseidon2 assertion at `baby-bear/src/poseidon2.rs:80` holds: the
width-32 internal round constants, `BABYBEAR_POSEIDON2_RC_32_INTERNAL`, number
`PARTIAL_ROUNDS_32 = 30`, one per partial round. -/
theorem poseidon2.const_check_8.holds : poseidon2.const_check_8 ⦃ _ => True ⦄ :=
  Proofs.BabyBear.poseidon2.const_check_8.holds

end Plonky3Lean.Claims.BabyBear
