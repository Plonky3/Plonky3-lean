import CompPoly.Fields.KoalaBear
import Plonky3Lean.Proofs.Field.KoalaBear
import Plonky3Lean.Proofs.Field.KoalaBear.Arith
import Plonky3Lean.Proofs.Field.KoalaBear.Constants
import Plonky3Lean.Proofs.Field.KoalaBear.Extension
import Plonky3Lean.Proofs.Field.KoalaBear.Poseidon
import ToCompPoly.Fields.KoalaBear.Extension

/-!
# KoalaBear: claims

What this repository asserts about p3-koala-bear, at the Plonky3 commit pinned in `plonky3/`.

- The model is the extraction in `crates/koala-bear` and the scoped extraction in `crates/monty-31`.
- `PRIME`, `MontyParams` and the other names are `Plonky3Lean.Spec.KoalaBear`'s aliases for its constants.
- `KoalaBear.*` is CompPoly's specification of the field, extended by `ToCompPoly` (the binomial extensions, cube roots).
- `toField` and `Canonical` are the generic Monty31 ones at `p = KoalaBear.fieldSize`.

KoalaBear's parameters pass the checks of `MontyField31::new`, so the generic Monty31 theorems apply at them.
Most claims below are those theorems at KoalaBear's parameters.

Not claimed:
- inversion, exponentiation, and the other `PrimeCharacteristicRing` methods KoalaBear overrides;
- the integer conversions and deserialization;
- the packed (SIMD) and extension-field arithmetic, and `mul_w`, which the extraction does not produce;
- the body of `exp_1420470955`, which the model leaves opaque;
- the extension fields' `EXT_GENERATOR`s, and `TrinomialQuinticData`'s `EXT_GENERATOR` and `FROBENIUS_COEFFS`;
- `UniformSamplingField`'s `SAMPLING_BITS_M`;
- the Poseidon1 and Poseidon2 permutations, the MDS layer, and the values of the round constants.
-/

open Aeneas Aeneas.Std CoreModels
open p3_koala_bear
open Plonky3Lean.Spec.KoalaBear

namespace Plonky3Lean.Claims.KoalaBear

/-! ## `KoalaBearParameters`: the trait instances return these constants

Reading a constant through the generated instance, as generic code does, returns the named constant without failing.
The claims about `PRIME`, `MONTY_MU`, `MONTY_BITS` and `TWO_ADICITY` therefore apply to the values generic code sees. -/

/-- Reading `<KoalaBearParameters as MontyParameters>::PRIME` through the instance returns `PRIME`. -/
theorem koala_bear.KoalaBearParameters.PRIME.from_instance :
    MontyParams.PRIME = .ok PRIME :=
  Proofs.KoalaBear.koala_bear.KoalaBearParameters.PRIME.from_instance

/-- Reading `<KoalaBearParameters as MontyParameters>::MONTY_MU` through the instance returns `MONTY_MU`. -/
theorem koala_bear.KoalaBearParameters.MONTY_MU.from_instance :
    MontyParams.MONTY_MU = .ok MONTY_MU :=
  Proofs.KoalaBear.koala_bear.KoalaBearParameters.MONTY_MU.from_instance

/-- Reading `<KoalaBearParameters as MontyParameters>::MONTY_BITS` through the instance returns `MONTY_BITS`. -/
theorem koala_bear.KoalaBearParameters.MONTY_BITS.from_instance :
    MontyParams.MONTY_BITS = .ok MONTY_BITS :=
  Proofs.KoalaBear.koala_bear.KoalaBearParameters.MONTY_BITS.from_instance

/-- Reading `TWO_ADICITY` through the `TwoAdicData` instance returns `TWO_ADICITY`. -/
theorem koala_bear.KoalaBearParameters.TWO_ADICITY.from_instance :
    TwoAdicParams.TWO_ADICITY = .ok TWO_ADICITY :=
  Proofs.KoalaBear.koala_bear.KoalaBearParameters.TWO_ADICITY.from_instance

/-! ## `KoalaBearParameters`: the constants against the specification -/

/-- `PRIME` (`0x7f000001`) is CompPoly's `KoalaBear.fieldSize`, `2^31 - 2^24 + 1 = 2130706433`. -/
theorem koala_bear.KoalaBearParameters.PRIME.eq_fieldSize :
    PRIME.val = KoalaBear.fieldSize :=
  Proofs.KoalaBear.koala_bear.KoalaBearParameters.PRIME.eq_fieldSize

/-- `PRIME` is a prime number, by CompPoly's Pratt certificate for `KoalaBear.fieldSize`. -/
theorem koala_bear.KoalaBearParameters.PRIME.is_prime :
    Nat.Prime PRIME.val :=
  Proofs.KoalaBear.koala_bear.KoalaBearParameters.PRIME.is_prime

/-- `gcd(3, p - 1) = 1`, so `x ↦ x^3` permutes the field.

This is the fact behind `RelativelyPrimePower<3>`, the Poseidon S-box.
It holds since `p - 1 = 2^24 · 127`. -/
theorem koala_bear.KoalaBearParameters.PRIME.coprime_three_pred :
    Nat.Coprime 3 (PRIME.val - 1) :=
  Proofs.KoalaBear.koala_bear.KoalaBearParameters.PRIME.coprime_three_pred

/-- `MONTY_BITS` is `32`, the radix `R = 2^32` that `MontyField31::new` asserts.

Both sides come from the extraction, so this checks the extraction, not the field. -/
theorem koala_bear.KoalaBearParameters.MONTY_BITS.val_eq_32 :
    MONTY_BITS.val = 32 :=
  Proofs.KoalaBear.koala_bear.KoalaBearParameters.MONTY_BITS.val_eq_32

/-- `MONTY_MU` (`0x81000001`) is the inverse of `PRIME` modulo `2^32`.

This is the precondition of Montgomery reduction, and one of the assertions of `MontyField31::new`. -/
theorem koala_bear.KoalaBearParameters.MONTY_MU.inverse :
    (PRIME.val * MONTY_MU.val) % (2 ^ 32) = 1 :=
  Proofs.KoalaBear.koala_bear.KoalaBearParameters.MONTY_MU.inverse

/-- `TWO_ADICITY` is CompPoly's `KoalaBear.twoAdicity`, `24`. -/
theorem koala_bear.KoalaBearParameters.TWO_ADICITY.eq_twoAdicity :
    TWO_ADICITY.val = KoalaBear.twoAdicity :=
  Proofs.KoalaBear.koala_bear.KoalaBearParameters.TWO_ADICITY.eq_twoAdicity

/-- `p - 1 = 2^TWO_ADICITY · 127`: the multiplicative group has a subgroup of order `2^TWO_ADICITY`. -/
theorem koala_bear.KoalaBearParameters.TWO_ADICITY.factorization :
    PRIME.val - 1 = 2 ^ TWO_ADICITY.val * 127 :=
  Proofs.KoalaBear.koala_bear.KoalaBearParameters.TWO_ADICITY.factorization

/-- `2^(TWO_ADICITY + 1)` does not divide `p - 1`: `TWO_ADICITY` is exactly the two-adicity, not a lower bound. -/
theorem koala_bear.KoalaBearParameters.TWO_ADICITY.maximal :
    ¬ 2 ^ (TWO_ADICITY.val + 1) ∣ PRIME.val - 1 :=
  Proofs.KoalaBear.koala_bear.KoalaBearParameters.TWO_ADICITY.maximal

/-- KoalaBear's `MontyParameters` pass every check of `MontyField31::new`, and `MONTY_MASK` is `2^32 - 1`.

So every generic Monty31 theorem holds at KoalaBear's parameters. -/
theorem koala_bear.KoalaBearParameters.valid :
    Spec.Monty31.Valid MontyParams PRIME MONTY_MU :=
  Proofs.KoalaBear.MontyParams.valid

/-- KoalaBear's `FieldParameters` are valid: its `MontyParameters` are, and `HALF_P_PLUS_1` is `(p + 1) / 2`. -/
theorem koala_bear.KoalaBearParameters.field_valid :
    Spec.Monty31.FieldValid FieldParams PRIME MONTY_MU :=
  Proofs.KoalaBear.FieldParams.valid

/-! ## The `KoalaBear` constructors

`KoalaBear` is `MontyField31<KoalaBearParameters>`.
In Aeneas, `m ⦃ r => P r ⦄` states that `m` returns a value `r` (it does not panic) and that `P r` holds. -/

/-- For every `u32` input `x`, `KoalaBear::new x` does not panic and stores `x · 2^32 mod p`.

The four assertions of `MontyField31::new` are runtime checks in the model, so this includes that they pass. -/
theorem koala_bear.KoalaBear.new.montgomery_form (x : Std.U32) :
    p3_monty_31.monty_31.MontyField31.new MontyParams x
      ⦃ r => r.value.val = x.val * 2 ^ 32 % KoalaBear.fieldSize ⦄ :=
  Proofs.KoalaBear.koala_bear.KoalaBear.new.montgomery_form x

/-- `KoalaBear::new_array` does not panic.

The claim is about the hand-written transcription in `crates/monty-31`, `Assumptions/Mirror.lean`. -/
theorem koala_bear.KoalaBear.new_array.never_panics {N : Std.Usize} (input : Array Std.U32 N) :
    ∃ r, p3_monty_31.monty_31.MontyField31.new_array MontyParams input = .ok r :=
  Proofs.KoalaBear.koala_bear.KoalaBear.new_array.never_panics input

/-- `KoalaBear::new_2d_array` does not panic, about the transcription like `new_array`. -/
theorem koala_bear.KoalaBear.new_2d_array.never_panics {N M : Std.Usize}
    (input : Array (Array Std.U32 N) M) :
    ∃ r, p3_monty_31.monty_31.MontyField31.new_2d_array MontyParams input = .ok r :=
  Proofs.KoalaBear.koala_bear.KoalaBear.new_2d_array.never_panics input

/-- For every `u32` input `x`, `KoalaBear::new x` is the field element `x mod p`, stored canonically. -/
theorem koala_bear.KoalaBear.new.toField (x : Std.U32) :
    p3_monty_31.monty_31.MontyField31.new MontyParams x
      ⦃ r => Canonical r ∧ toField r = (x.val : KoalaBear.Field) ⦄ :=
  Proofs.KoalaBear.koala_bear.KoalaBear.new.toField x

/-- `KoalaBear::new_array` returns, for each input `x`, the field element `x mod p`, in order and stored canonically. -/
theorem koala_bear.KoalaBear.new_array.toField {N : Std.Usize} (input : Array Std.U32 N) :
    p3_monty_31.monty_31.MontyField31.new_array MontyParams input
      ⦃ r => (∀ y ∈ r.val, Canonical y) ∧
        r.val.map toField = input.val.map (fun x => (x.val : KoalaBear.Field)) ⦄ :=
  Proofs.KoalaBear.koala_bear.KoalaBear.new_array.toField input

/-- `KoalaBear::new_2d_array` returns, for each input `x`, the field element `x mod p`, row by row and stored canonically. -/
theorem koala_bear.KoalaBear.new_2d_array.toField {N M : Std.Usize}
    (input : Array (Array Std.U32 N) M) :
    p3_monty_31.monty_31.MontyField31.new_2d_array MontyParams input
      ⦃ r => (∀ row ∈ r.val, ∀ y ∈ row.val, Canonical y) ∧
        r.val.map (fun row => row.val.map toField) =
          input.val.map (fun row => row.val.map (fun x => (x.val : KoalaBear.Field))) ⦄ :=
  Proofs.KoalaBear.koala_bear.KoalaBear.new_2d_array.toField input

/-! ## `FieldParameters`: the named field elements

`MONTY_ZERO`, `MONTY_ONE`, `MONTY_TWO`, `MONTY_NEG_ONE` and `HALF_P_PLUS_1` are p3-monty-31's defaults.
`MONTY_GEN` is KoalaBear's own. -/

/-- `MONTY_ZERO` is the field element `0`, stored canonically. -/
theorem koala_bear.KoalaBearParameters.MONTY_ZERO.toField :
    FieldParams.MONTY_ZERO ⦃ r => Canonical r ∧ toField r = 0 ⦄ :=
  Proofs.KoalaBear.FieldParams.MONTY_ZERO.toField

/-- `MONTY_ONE` is the field element `1`, stored canonically. -/
theorem koala_bear.KoalaBearParameters.MONTY_ONE.toField :
    FieldParams.MONTY_ONE ⦃ r => Canonical r ∧ toField r = 1 ⦄ :=
  Proofs.KoalaBear.FieldParams.MONTY_ONE.toField

/-- `MONTY_TWO` is the field element `2`, stored canonically. -/
theorem koala_bear.KoalaBearParameters.MONTY_TWO.toField :
    FieldParams.MONTY_TWO ⦃ r => Canonical r ∧ toField r = 2 ⦄ :=
  Proofs.KoalaBear.FieldParams.MONTY_TWO.toField

/-- `MONTY_NEG_ONE`, built as `new(PRIME - 1)`, is the field element `-1`, stored canonically. -/
theorem koala_bear.KoalaBearParameters.MONTY_NEG_ONE.toField :
    FieldParams.MONTY_NEG_ONE ⦃ r => Canonical r ∧ toField r = -1 ⦄ :=
  Proofs.KoalaBear.FieldParams.MONTY_NEG_ONE.toField

/-- `HALF_P_PLUS_1` is the plain integer `(p + 1) / 2`, the inverse of `2` modulo `p`. -/
theorem koala_bear.KoalaBearParameters.HALF_P_PLUS_1.spec :
    FieldParams.HALF_P_PLUS_1 ⦃ h => h.val = (KoalaBear.fieldSize + 1) / 2 ∧
      (h.val : KoalaBear.Field) * 2 = 1 ⦄ :=
  Proofs.KoalaBear.FieldParams.HALF_P_PLUS_1.spec

/-- `MONTY_GEN` (`KoalaBear::new(3)`) generates the multiplicative group: its order is `p - 1`. -/
theorem koala_bear.KoalaBearParameters.MONTY_GEN.generator :
    FieldParams.MONTY_GEN ⦃ g => Canonical g ∧
      orderOf (toField g) = KoalaBear.fieldSize - 1 ⦄ :=
  Proofs.KoalaBear.FieldParams.MONTY_GEN.generator

/-! ## `TwoAdicData`: the roots of unity

The tables are compared with CompPoly's independently stated `KoalaBear.twoAdicGenerators`. -/

/-- `TWO_ADIC_GENERATORS` is, entry for entry, CompPoly's table, and every entry is stored canonically. -/
theorem koala_bear.KoalaBearParameters.TWO_ADIC_GENERATORS.eq_twoAdicGenerators :
    TwoAdicParams.TWO_ADIC_GENERATORS ⦃ s => (∀ y ∈ s.val, Canonical y) ∧
      s.val.map toField = KoalaBear.twoAdicGenerators ⦄ :=
  Proofs.KoalaBear.TwoAdicParams.TWO_ADIC_GENERATORS.eq_twoAdicGenerators

/-- `TWO_ADIC_GENERATORS` has `TWO_ADICITY + 1 = 25` entries, and entry `i` has order exactly `2^i`. -/
theorem koala_bear.KoalaBearParameters.TWO_ADIC_GENERATORS.order :
    TwoAdicParams.TWO_ADIC_GENERATORS ⦃ s => s.val.length = TWO_ADICITY.val + 1 ∧
      ∀ i (h : i < s.val.length), orderOf (toField s.val[i]) = 2 ^ i ⦄ :=
  Proofs.KoalaBear.TwoAdicParams.TWO_ADIC_GENERATORS.order

/-- Each entry of `TWO_ADIC_GENERATORS` squares to the one before it. -/
theorem koala_bear.KoalaBearParameters.TWO_ADIC_GENERATORS.sq_succ :
    TwoAdicParams.TWO_ADIC_GENERATORS ⦃ s => ∀ i (h : i + 1 < s.val.length),
      toField s.val[i + 1] ^ 2 = toField s.val[i] ⦄ :=
  Proofs.KoalaBear.TwoAdicParams.TWO_ADIC_GENERATORS.sq_succ

/-- `ROOTS_8` is `[1, ω, ω^2, ω^3]` for `ω = TWO_ADIC_GENERATORS[3]`, stored canonically. -/
theorem koala_bear.KoalaBearParameters.ROOTS_8.eq :
    TwoAdicParams.ROOTS_8 ⦃ s => (∀ y ∈ s.val, Canonical y) ∧
      s.val.map toField = (List.range 4).map (fun j => KoalaBear.twoAdicGenerators[3]! ^ j) ⦄ :=
  Proofs.KoalaBear.TwoAdicParams.ROOTS_8.eq

/-- `INV_ROOTS_8` holds the inverses of `ROOTS_8`, in the same order, stored canonically. -/
theorem koala_bear.KoalaBearParameters.INV_ROOTS_8.eq :
    TwoAdicParams.INV_ROOTS_8 ⦃ s => (∀ y ∈ s.val, Canonical y) ∧
      s.val.map toField =
        (List.range 4).map (fun j => (KoalaBear.twoAdicGenerators[3]! ^ j)⁻¹) ⦄ :=
  Proofs.KoalaBear.TwoAdicParams.INV_ROOTS_8.eq

/-- `ROOTS_16` is `[1, ω, …, ω^7]` for `ω = TWO_ADIC_GENERATORS[4]`, stored canonically. -/
theorem koala_bear.KoalaBearParameters.ROOTS_16.eq :
    TwoAdicParams.ROOTS_16 ⦃ s => (∀ y ∈ s.val, Canonical y) ∧
      s.val.map toField = (List.range 8).map (fun j => KoalaBear.twoAdicGenerators[4]! ^ j) ⦄ :=
  Proofs.KoalaBear.TwoAdicParams.ROOTS_16.eq

/-- `INV_ROOTS_16` holds the inverses of `ROOTS_16`, in the same order, stored canonically. -/
theorem koala_bear.KoalaBearParameters.INV_ROOTS_16.eq :
    TwoAdicParams.INV_ROOTS_16 ⦃ s => (∀ y ∈ s.val, Canonical y) ∧
      s.val.map toField =
        (List.range 8).map (fun j => (KoalaBear.twoAdicGenerators[4]! ^ j)⁻¹) ⦄ :=
  Proofs.KoalaBear.TwoAdicParams.INV_ROOTS_16.eq

/-- `ODD_FACTOR`, computed as `PRIME >> TWO_ADICITY`, is `127`, the odd `r` with `p = r · 2^TWO_ADICITY + 1`. -/
theorem koala_bear.KoalaBearParameters.ODD_FACTOR.spec :
    TwoAdicParams.ODD_FACTOR ⦃ r => r.val = 127 ∧
      (PRIME.val : ℤ) = r.val * 2 ^ TWO_ADICITY.val + 1 ⦄ :=
  Proofs.KoalaBear.TwoAdicParams.ODD_FACTOR.spec

/-! ## `RelativelyPrimePower<3>` -/

/-- `exp_root_d` computes `x^(1/3)` as `exp_1420470955(x)`, and `x ↦ x^1420470955` inverts `x ↦ x^3`.

The first half is read off the model, so a change of exponent upstream breaks this claim.
The body of `exp_1420470955` is opaque in the model, so the second half is about the exponent, not the addition chain. -/
theorem koala_bear.KoalaBearParameters.exp_root_d.exponent :
    (∀ {R : Type} (inst : p3_field.field.PrimeCharacteristicRing R) (x : R),
      koala_bear.KoalaBearParameters.Insts.P3_monty_31Data_traitsRelativelyPrimePower3.exp_root_d
          inst x =
        p3_field.exponentiation.exp_1420470955 inst x) ∧
    ∀ x : KoalaBear.Field, (x ^ 1420470955) ^ 3 = x :=
  Proofs.KoalaBear.koala_bear.KoalaBearParameters.exp_root_d.exponent

/-! ## Scalar arithmetic

The `u32` helpers of p3-monty-31's `utils`, which are extracted, at KoalaBear's parameters.
Then the `MontyField31` operators that wrap them, read as field operations.
The operators' one-line bodies are transcribed in `crates/monty-31/extraction/P3Monty31/Assumptions/Mirror.lean`.
Every operator claim assumes canonical inputs, as the Rust does, and gives a canonical output. -/

/-- Montgomery reduction: for `x < 2^32 p`, `monty_reduce(x)` is the canonical `r` with `r · 2^32 ≡ x (mod p)`. -/
theorem p3_monty_31.utils.monty_reduce.spec (x : Std.U64)
    (hx : x.val < 2 ^ 32 * KoalaBear.fieldSize) :
    p3_monty_31.utils.monty_reduce MontyParams x ⦃ r => r.val < KoalaBear.fieldSize ∧
      (r.val * 2 ^ 32) % KoalaBear.fieldSize = x.val % KoalaBear.fieldSize ⦄ :=
  Proofs.KoalaBear.utils.monty_reduce.spec x hx

/-- `from_monty(x)` is the canonical `r` with `r · 2^32 ≡ x (mod p)`, for every `u32`. -/
theorem p3_monty_31.utils.from_monty.spec (x : Std.U32) :
    p3_monty_31.utils.from_monty MontyParams x ⦃ r => r.val < KoalaBear.fieldSize ∧
      (r.val * 2 ^ 32) % KoalaBear.fieldSize = x.val % KoalaBear.fieldSize ⦄ :=
  Proofs.KoalaBear.utils.from_monty.spec x

/-- For canonical `a` and `b`, `add(a, b)` is `(a + b) mod p`. -/
theorem p3_monty_31.utils.add.spec (a b : Std.U32) (ha : a.val < KoalaBear.fieldSize)
    (hb : b.val < KoalaBear.fieldSize) :
    p3_monty_31.utils.add MontyParams a b ⦃ r => r.val = (a.val + b.val) % KoalaBear.fieldSize ⦄ :=
  Proofs.KoalaBear.utils.add.spec a b ha hb

/-- For canonical `a` and `b`, `sub(a, b)` is `(a - b) mod p`, computed as `(a + p - b) mod p`. -/
theorem p3_monty_31.utils.sub.spec (a b : Std.U32) (ha : a.val < KoalaBear.fieldSize)
    (hb : b.val < KoalaBear.fieldSize) :
    p3_monty_31.utils.sub MontyParams a b
      ⦃ r => r.val = (a.val + KoalaBear.fieldSize - b.val) % KoalaBear.fieldSize ⦄ :=
  Proofs.KoalaBear.utils.sub.spec a b ha hb

/-- For canonical `a`, `halve_u32(a)` is the canonical `r` with `2r ≡ a (mod p)`. -/
theorem p3_monty_31.utils.halve_u32.spec (a : Std.U32) (ha : a.val < KoalaBear.fieldSize) :
    p3_monty_31.utils.halve_u32 FieldParams a ⦃ r => r.val < KoalaBear.fieldSize ∧
      (r.val * 2) % KoalaBear.fieldSize = a.val ⦄ :=
  Proofs.KoalaBear.utils.halve_u32.spec a ha

/-- `to_monty(x)` is `x · 2^32 mod p`, for every `u32`. -/
theorem p3_monty_31.utils.to_monty.spec (x : Std.U32) :
    p3_monty_31.utils.to_monty MontyParams x ⦃ r => r.val = x.val * 2 ^ 32 % KoalaBear.fieldSize ⦄ :=
  Proofs.KoalaBear.utils.to_monty.spec x

/-- `a + b` on canonical KoalaBear elements is canonical, and is the sum of the field elements. -/
theorem koala_bear.KoalaBear.add.toField (a b : Element) (ha : Canonical a) (hb : Canonical b) :
    p3_monty_31.monty_31.MontyField31.add MontyParams a b
      ⦃ c => Canonical c ∧ toField c = toField a + toField b ⦄ :=
  Proofs.KoalaBear.koala_bear.KoalaBear.add.toField a b ha hb

/-- `a - b` on canonical KoalaBear elements is canonical, and is the difference of the field elements. -/
theorem koala_bear.KoalaBear.sub.toField (a b : Element) (ha : Canonical a) (hb : Canonical b) :
    p3_monty_31.monty_31.MontyField31.sub MontyParams a b
      ⦃ c => Canonical c ∧ toField c = toField a - toField b ⦄ :=
  Proofs.KoalaBear.koala_bear.KoalaBear.sub.toField a b ha hb

/-- `a * b` on canonical KoalaBear elements is canonical, and is the product of the field elements. -/
theorem koala_bear.KoalaBear.mul.toField (a b : Element) (ha : Canonical a) (hb : Canonical b) :
    p3_monty_31.monty_31.MontyField31.mul MontyParams a b
      ⦃ c => Canonical c ∧ toField c = toField a * toField b ⦄ :=
  Proofs.KoalaBear.koala_bear.KoalaBear.mul.toField a b ha hb

/-- `-a` on a canonical KoalaBear element is canonical, and is the negation of the field element. -/
theorem koala_bear.KoalaBear.neg.toField (a : Element) (ha : Canonical a) :
    p3_monty_31.monty_31.MontyField31.neg FieldParams a
      ⦃ c => Canonical c ∧ toField c = -toField a ⦄ :=
  Proofs.KoalaBear.koala_bear.KoalaBear.neg.toField a ha

/-- `a.halve()` on a canonical KoalaBear element is canonical, and is half the field element. -/
theorem koala_bear.KoalaBear.halve.toField (a : Element) (ha : Canonical a) :
    p3_monty_31.monty_31.MontyField31.halve FieldParams a
      ⦃ c => Canonical c ∧ toField c * 2 = toField a ⦄ :=
  Proofs.KoalaBear.koala_bear.KoalaBear.halve.toField a ha

/-- `from_monty(a.value)`, the body of `as_canonical_u32`, is the canonical `u32` for the field element `a` stands for, for any `a`. -/
theorem koala_bear.KoalaBear.from_monty.toField (a : Element) :
    p3_monty_31.utils.from_monty MontyParams a.value
      ⦃ r => r.val < KoalaBear.fieldSize ∧ (r.val : KoalaBear.Field) = toField a ⦄ :=
  Proofs.KoalaBear.koala_bear.KoalaBear.from_monty.toField a

/-! ## `BinomialExtensionData<D>`: the binomial extensions

KoalaBear's binomial extensions of degree `D = 4, 8` are `F[X] / (X ^ D - 3)`.
- `X ^ D - W` must be irreducible, so that the quotient is a field.
- `DTH_ROOT` must be `W ^ ((p - 1) / D)`.
- `EXT_TWO_ADICITY` must be the two-adicity of `p ^ D - 1`.
- `TWO_ADIC_EXTENSION_GENERATORS` must continue the base field's chain of square roots, with `EXT_TWO_ADICITY - TWO_ADICITY` entries.

Each extension element is read through `Plonky3Lean.Spec.KoalaBear.toExt`. -/

/-- `W = 3` for the degree-4 extension, stored canonically, and `X ^ 4 - W` is irreducible. -/
theorem koala_bear.KoalaBearParameters.BinomialExtensionData4.W.irreducible :
    Ext4Params.W ⦃ w => Canonical w ∧ toField w = 3 ∧
      Irreducible (Polynomial.X ^ 4 - Polynomial.C (toField w)) ⦄ :=
  Proofs.KoalaBear.Ext4Params.W.spec

/-- `DTH_ROOT` for the degree-4 extension is `W ^ ((p - 1) / 4)`, stored canonically. -/
theorem koala_bear.KoalaBearParameters.BinomialExtensionData4.DTH_ROOT.spec :
    ∃ w r, Ext4Params.W = .ok w ∧ Ext4Params.DTH_ROOT = .ok r ∧ Canonical r ∧
      toField r = toField w ^ ((KoalaBear.fieldSize - 1) / 4) :=
  Proofs.KoalaBear.Ext4Params.DTH_ROOT.spec

/-- `EXT_TWO_ADICITY` for the degree-4 extension is the two-adicity of `p ^ 4 - 1`. -/
theorem koala_bear.KoalaBearParameters.BinomialExtensionData4.EXT_TWO_ADICITY.spec :
    Ext4Params.EXT_TWO_ADICITY ⦃ e => 2 ^ e.val ∣ PRIME.val ^ 4 - 1 ∧
      ¬ 2 ^ (e.val + 1) ∣ PRIME.val ^ 4 - 1 ⦄ :=
  Proofs.KoalaBear.Ext4Params.EXT_TWO_ADICITY.spec

/-- The degree-4 `TWO_ADIC_EXTENSION_GENERATORS` has `EXT_TWO_ADICITY - TWO_ADICITY` entries, and entry `i` has order `2 ^ (TWO_ADICITY + 1 + i)`. -/
theorem koala_bear.KoalaBearParameters.BinomialExtensionData4.TWO_ADIC_EXTENSION_GENERATORS.order :
    ∃ w t e, Ext4Params.W = .ok w ∧ Ext4Params.TWO_ADIC_EXTENSION_GENERATORS = .ok t ∧
      Ext4Params.EXT_TWO_ADICITY = .ok e ∧ TWO_ADICITY.val + t.val.length = e.val ∧
      ∀ i (h : i < t.val.length),
        orderOf (toExt (toField w) t.val[i]) = 2 ^ (TWO_ADICITY.val + 1 + i) :=
  Proofs.KoalaBear.Ext4Params.TWO_ADIC_EXTENSION_GENERATORS.order

/-- The degree-4 `TWO_ADIC_EXTENSION_GENERATORS` is, coefficient for coefficient, `KoalaBear.ext4TwoAdicGeneratorCoeffs`. -/
theorem koala_bear.KoalaBearParameters.BinomialExtensionData4.TWO_ADIC_EXTENSION_GENERATORS.eq_ext4TwoAdicGenerators :
    Ext4Params.TWO_ADIC_EXTENSION_GENERATORS ⦃ t =>
      t.val.map (fun row => row.val.map toField) = KoalaBear.ext4TwoAdicGeneratorCoeffs ⦄ :=
  Proofs.KoalaBear.Ext4Params.TWO_ADIC_EXTENSION_GENERATORS.eq

/-- The degree-4 `TWO_ADIC_EXTENSION_GENERATORS` continues the base field's chain.

Entry `0` squares to `TWO_ADIC_GENERATORS[TWO_ADICITY]`, and each later entry to the one before. -/
theorem koala_bear.KoalaBearParameters.BinomialExtensionData4.TWO_ADIC_EXTENSION_GENERATORS.sq_succ :
    ∃ w t, Ext4Params.W = .ok w ∧ Ext4Params.TWO_ADIC_EXTENSION_GENERATORS = .ok t ∧
      let chain := AdjoinRoot.of _ KoalaBear.twoAdicGenerators[TWO_ADICITY.val]! ::
        t.val.map (toExt (toField w))
      ∀ i (h : i + 1 < chain.length), chain[i + 1] ^ 2 = chain[i] :=
  Proofs.KoalaBear.Ext4Params.TWO_ADIC_EXTENSION_GENERATORS.sq_succ

/-- `W = 3` for the degree-8 extension, stored canonically, and `X ^ 8 - W` is irreducible. -/
theorem koala_bear.KoalaBearParameters.BinomialExtensionData8.W.irreducible :
    Ext8Params.W ⦃ w => Canonical w ∧ toField w = 3 ∧
      Irreducible (Polynomial.X ^ 8 - Polynomial.C (toField w)) ⦄ :=
  Proofs.KoalaBear.Ext8Params.W.spec

/-- `DTH_ROOT` for the degree-8 extension is `W ^ ((p - 1) / 8)`, stored canonically. -/
theorem koala_bear.KoalaBearParameters.BinomialExtensionData8.DTH_ROOT.spec :
    ∃ w r, Ext8Params.W = .ok w ∧ Ext8Params.DTH_ROOT = .ok r ∧ Canonical r ∧
      toField r = toField w ^ ((KoalaBear.fieldSize - 1) / 8) :=
  Proofs.KoalaBear.Ext8Params.DTH_ROOT.spec

/-- `EXT_TWO_ADICITY` for the degree-8 extension is the two-adicity of `p ^ 8 - 1`. -/
theorem koala_bear.KoalaBearParameters.BinomialExtensionData8.EXT_TWO_ADICITY.spec :
    Ext8Params.EXT_TWO_ADICITY ⦃ e => 2 ^ e.val ∣ PRIME.val ^ 8 - 1 ∧
      ¬ 2 ^ (e.val + 1) ∣ PRIME.val ^ 8 - 1 ⦄ :=
  Proofs.KoalaBear.Ext8Params.EXT_TWO_ADICITY.spec

/-- The degree-8 `TWO_ADIC_EXTENSION_GENERATORS` has `EXT_TWO_ADICITY - TWO_ADICITY` entries, and entry `i` has order `2 ^ (TWO_ADICITY + 1 + i)`. -/
theorem koala_bear.KoalaBearParameters.BinomialExtensionData8.TWO_ADIC_EXTENSION_GENERATORS.order :
    ∃ w t e, Ext8Params.W = .ok w ∧ Ext8Params.TWO_ADIC_EXTENSION_GENERATORS = .ok t ∧
      Ext8Params.EXT_TWO_ADICITY = .ok e ∧ TWO_ADICITY.val + t.val.length = e.val ∧
      ∀ i (h : i < t.val.length),
        orderOf (toExt (toField w) t.val[i]) = 2 ^ (TWO_ADICITY.val + 1 + i) :=
  Proofs.KoalaBear.Ext8Params.TWO_ADIC_EXTENSION_GENERATORS.order

/-- The degree-8 `TWO_ADIC_EXTENSION_GENERATORS` is, coefficient for coefficient, `KoalaBear.ext8TwoAdicGeneratorCoeffs`. -/
theorem koala_bear.KoalaBearParameters.BinomialExtensionData8.TWO_ADIC_EXTENSION_GENERATORS.eq_ext8TwoAdicGenerators :
    Ext8Params.TWO_ADIC_EXTENSION_GENERATORS ⦃ t =>
      t.val.map (fun row => row.val.map toField) = KoalaBear.ext8TwoAdicGeneratorCoeffs ⦄ :=
  Proofs.KoalaBear.Ext8Params.TWO_ADIC_EXTENSION_GENERATORS.eq

/-- The degree-8 `TWO_ADIC_EXTENSION_GENERATORS` continues the base field's chain.

Entry `0` squares to `TWO_ADIC_GENERATORS[TWO_ADICITY]`, and each later entry to the one before. -/
theorem koala_bear.KoalaBearParameters.BinomialExtensionData8.TWO_ADIC_EXTENSION_GENERATORS.sq_succ :
    ∃ w t, Ext8Params.W = .ok w ∧ Ext8Params.TWO_ADIC_EXTENSION_GENERATORS = .ok t ∧
      let chain := AdjoinRoot.of _ KoalaBear.twoAdicGenerators[TWO_ADICITY.val]! ::
        t.val.map (toExt (toField w))
      ∀ i (h : i + 1 < chain.length), chain[i + 1] ^ 2 = chain[i] :=
  Proofs.KoalaBear.Ext8Params.TWO_ADIC_EXTENSION_GENERATORS.sq_succ

/-! ## `TrinomialQuinticData` -/

/-- The quintic extension's `EXT_TWO_ADICITY` is the two-adicity of `p ^ 5 - 1`, equal to `TWO_ADICITY`.

So its empty `TWO_ADIC_EXTENSION_GENERATORS` is the right length. -/
theorem koala_bear.KoalaBearParameters.TrinomialQuinticData.EXT_TWO_ADICITY.spec :
    QuinticParams.EXT_TWO_ADICITY ⦃ e => e.val = TWO_ADICITY.val ∧
      2 ^ e.val ∣ PRIME.val ^ 5 - 1 ∧ ¬ 2 ^ (e.val + 1) ∣ PRIME.val ^ 5 - 1 ⦄ :=
  Proofs.KoalaBear.QuinticParams.EXT_TWO_ADICITY.spec

/-! ## The Poseidon round-constant length assertions

`koala-bear/src/poseidon{1,2}.rs` check the length of each round-constant table with an anonymous `const _: () = assert!(..)`.
Each claim `… ⦃ _ => True ⦄` states that the table builds and the assertion holds.
Nothing is said about the constants' values. -/

/-- `koala-bear/src/poseidon1.rs:65`, on `KOALABEAR_POSEIDON1_RC_16`. -/
theorem poseidon1._.holds : poseidon1._ ⦃ _ => True ⦄ :=
  Proofs.KoalaBear.poseidon1._.holds

/-- `koala-bear/src/poseidon1.rs:69`, on `KOALABEAR_POSEIDON1_RC_24`. -/
theorem poseidon1.const_check_1.holds : poseidon1.const_check_1 ⦃ _ => True ⦄ :=
  Proofs.KoalaBear.poseidon1.const_check_1.holds

/-- `koala-bear/src/poseidon2.rs:69`, on `KOALABEAR_POSEIDON2_RC_16_EXTERNAL_INITIAL`. -/
theorem poseidon2._.holds : poseidon2._ ⦃ _ => True ⦄ :=
  Proofs.KoalaBear.poseidon2._.holds

/-- `koala-bear/src/poseidon2.rs:72`, on `KOALABEAR_POSEIDON2_RC_16_EXTERNAL_FINAL`. -/
theorem poseidon2.const_check_1.holds : poseidon2.const_check_1 ⦃ _ => True ⦄ :=
  Proofs.KoalaBear.poseidon2.const_check_1.holds

/-- `koala-bear/src/poseidon2.rs:74`, on `KOALABEAR_POSEIDON2_RC_16_INTERNAL`. -/
theorem poseidon2.const_check_2.holds : poseidon2.const_check_2 ⦃ _ => True ⦄ :=
  Proofs.KoalaBear.poseidon2.const_check_2.holds

/-- `koala-bear/src/poseidon2.rs:76`, on `KOALABEAR_POSEIDON2_RC_24_EXTERNAL_INITIAL`. -/
theorem poseidon2.const_check_3.holds : poseidon2.const_check_3 ⦃ _ => True ⦄ :=
  Proofs.KoalaBear.poseidon2.const_check_3.holds

/-- `koala-bear/src/poseidon2.rs:79`, on `KOALABEAR_POSEIDON2_RC_24_EXTERNAL_FINAL`. -/
theorem poseidon2.const_check_4.holds : poseidon2.const_check_4 ⦃ _ => True ⦄ :=
  Proofs.KoalaBear.poseidon2.const_check_4.holds

/-- `koala-bear/src/poseidon2.rs:81`, on `KOALABEAR_POSEIDON2_RC_24_INTERNAL`. -/
theorem poseidon2.const_check_5.holds : poseidon2.const_check_5 ⦃ _ => True ⦄ :=
  Proofs.KoalaBear.poseidon2.const_check_5.holds

/-- `koala-bear/src/poseidon2.rs:83`, on `KOALABEAR_POSEIDON2_RC_32_EXTERNAL_INITIAL`. -/
theorem poseidon2.const_check_6.holds : poseidon2.const_check_6 ⦃ _ => True ⦄ :=
  Proofs.KoalaBear.poseidon2.const_check_6.holds

/-- `koala-bear/src/poseidon2.rs:86`, on `KOALABEAR_POSEIDON2_RC_32_EXTERNAL_FINAL`. -/
theorem poseidon2.const_check_7.holds : poseidon2.const_check_7 ⦃ _ => True ⦄ :=
  Proofs.KoalaBear.poseidon2.const_check_7.holds

/-- `koala-bear/src/poseidon2.rs:88`, on `KOALABEAR_POSEIDON2_RC_32_INTERNAL`. -/
theorem poseidon2.const_check_8.holds : poseidon2.const_check_8 ⦃ _ => True ⦄ :=
  Proofs.KoalaBear.poseidon2.const_check_8.holds

end Plonky3Lean.Claims.KoalaBear
