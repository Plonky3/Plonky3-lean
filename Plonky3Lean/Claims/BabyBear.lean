import CompPoly.Fields.BabyBear
import Plonky3Lean.Proofs.Field.BabyBear
import Plonky3Lean.Proofs.Field.BabyBear.Constants
import Plonky3Lean.Proofs.Field.BabyBear.Element
import Plonky3Lean.Proofs.Field.BabyBear.Extension

/-!
# BabyBear: claims

What this repository asserts about p3-baby-bear, at the Plonky3 commit pinned
in `plonky3/`. The model is the extraction in `crates/baby-bear` and the scoped
extraction in `crates/monty-31`; `PRIME`, `MontyParams` and the other names are
`Plonky3Lean.Spec.BabyBear`'s aliases for its constants, and `BabyBear.*` is
CompPoly's specification of the field.

Not claimed: anything about field arithmetic (addition, multiplication,
Montgomery reduction, inversion), the extension fields' `EXT_GENERATOR`s, the
Poseidon1 and Poseidon2 permutations or the MDS layer, and the values of the
round constants.
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

/-! ## `FieldParameters`: the named field elements

`MONTY_ZERO`, `MONTY_ONE`, `MONTY_TWO`, `MONTY_NEG_ONE` and `HALF_P_PLUS_1` are
p3-monty-31's defaults, which BabyBear inherits; `MONTY_GEN` is BabyBear's own.
Each is a `RustM` value, read through the `FieldParameters` instance as generic
code sees it. -/

/-- `MONTY_ZERO` is the field element `0`, stored canonically. -/
theorem baby_bear.BabyBearParameters.MONTY_ZERO.toField :
    FieldParams.MONTY_ZERO ⦃ r => Canonical r ∧ Spec.BabyBear.toField r = 0 ⦄ :=
  Proofs.BabyBear.FieldParams.MONTY_ZERO.toField

/-- `MONTY_ONE` is the field element `1`, stored canonically. -/
theorem baby_bear.BabyBearParameters.MONTY_ONE.toField :
    FieldParams.MONTY_ONE ⦃ r => Canonical r ∧ Spec.BabyBear.toField r = 1 ⦄ :=
  Proofs.BabyBear.FieldParams.MONTY_ONE.toField

/-- `MONTY_TWO` is the field element `2`, stored canonically. -/
theorem baby_bear.BabyBearParameters.MONTY_TWO.toField :
    FieldParams.MONTY_TWO ⦃ r => Canonical r ∧ Spec.BabyBear.toField r = 2 ⦄ :=
  Proofs.BabyBear.FieldParams.MONTY_TWO.toField

/-- `MONTY_NEG_ONE`, built as `new(PRIME - 1)`, is the field element `-1`,
stored canonically; computing `PRIME - 1` does not underflow. -/
theorem baby_bear.BabyBearParameters.MONTY_NEG_ONE.toField :
    FieldParams.MONTY_NEG_ONE ⦃ r => Canonical r ∧ Spec.BabyBear.toField r = -1 ⦄ :=
  Proofs.BabyBear.FieldParams.MONTY_NEG_ONE.toField

/-- `HALF_P_PLUS_1` is the plain integer `(p + 1) / 2`, not a Montgomery form,
computed without overflow. As an integer modulo `p` it is the inverse of `2`,
which is what halving relies on. -/
theorem baby_bear.BabyBearParameters.HALF_P_PLUS_1.spec :
    FieldParams.HALF_P_PLUS_1 ⦃ h => h.val = (BabyBear.fieldSize + 1) / 2 ∧
      (h.val : BabyBear.Field) * 2 = 1 ⦄ :=
  Proofs.BabyBear.FieldParams.HALF_P_PLUS_1.spec

/-- `MONTY_GEN` (`BabyBear::new(31)`) generates the multiplicative group of the
field: it is stored canonically, and its order is `p - 1`. -/
theorem baby_bear.BabyBearParameters.MONTY_GEN.generator :
    FieldParams.MONTY_GEN ⦃ g => Canonical g ∧
      orderOf (Spec.BabyBear.toField g) = BabyBear.fieldSize - 1 ⦄ :=
  Proofs.BabyBear.FieldParams.MONTY_GEN.generator

/-! ## `TwoAdicData`: the roots of unity

The trait requires the `i`-th entry of `TWO_ADIC_GENERATORS` to be a `2^i`-th
root of unity whose square is the `(i - 1)`-th entry, `ROOTS_8` and `ROOTS_16`
to agree with it, and the `INV_` tables to hold the inverses. The table is
compared with CompPoly's independently stated `BabyBear.twoAdicGenerators`. -/

/-- `TWO_ADIC_GENERATORS` is, entry for entry, CompPoly's table of BabyBear
two-adic generators, and every entry is stored canonically. -/
theorem baby_bear.BabyBearParameters.TWO_ADIC_GENERATORS.eq_twoAdicGenerators :
    TwoAdicParams.TWO_ADIC_GENERATORS ⦃ s => (∀ y ∈ s.val, Canonical y) ∧
      s.val.map Spec.BabyBear.toField = BabyBear.twoAdicGenerators ⦄ :=
  Proofs.BabyBear.TwoAdicParams.TWO_ADIC_GENERATORS.eq_twoAdicGenerators

/-- `TWO_ADIC_GENERATORS` has `TWO_ADICITY + 1 = 28` entries, and entry `i` has
order exactly `2^i`: it is a primitive `2^i`-th root of unity. -/
theorem baby_bear.BabyBearParameters.TWO_ADIC_GENERATORS.order :
    TwoAdicParams.TWO_ADIC_GENERATORS ⦃ s => s.val.length = TWO_ADICITY.val + 1 ∧
      ∀ i (h : i < s.val.length), orderOf (Spec.BabyBear.toField s.val[i]) = 2 ^ i ⦄ :=
  Proofs.BabyBear.TwoAdicParams.TWO_ADIC_GENERATORS.order

/-- Each entry of `TWO_ADIC_GENERATORS` squares to the one before it. -/
theorem baby_bear.BabyBearParameters.TWO_ADIC_GENERATORS.sq_succ :
    TwoAdicParams.TWO_ADIC_GENERATORS ⦃ s => ∀ i (h : i + 1 < s.val.length),
      Spec.BabyBear.toField s.val[i + 1] ^ 2 = Spec.BabyBear.toField s.val[i] ⦄ :=
  Proofs.BabyBear.TwoAdicParams.TWO_ADIC_GENERATORS.sq_succ

/-- `ROOTS_8` is `[1, ω, ω², ω³]` for `ω = TWO_ADIC_GENERATORS[3]`, the
primitive 8th root of unity, stored canonically. -/
theorem baby_bear.BabyBearParameters.ROOTS_8.eq :
    TwoAdicParams.ROOTS_8 ⦃ s => (∀ y ∈ s.val, Canonical y) ∧
      s.val.map Spec.BabyBear.toField =
        (List.range 4).map (fun j => BabyBear.twoAdicGenerators[3]! ^ j) ⦄ :=
  Proofs.BabyBear.TwoAdicParams.ROOTS_8.eq

/-- `INV_ROOTS_8` holds the inverses of `ROOTS_8`, in the same order, stored
canonically. -/
theorem baby_bear.BabyBearParameters.INV_ROOTS_8.eq :
    TwoAdicParams.INV_ROOTS_8 ⦃ s => (∀ y ∈ s.val, Canonical y) ∧
      s.val.map Spec.BabyBear.toField =
        (List.range 4).map (fun j => (BabyBear.twoAdicGenerators[3]! ^ j)⁻¹) ⦄ :=
  Proofs.BabyBear.TwoAdicParams.INV_ROOTS_8.eq

/-- `ROOTS_16` is `[1, ω, …, ω⁷]` for `ω = TWO_ADIC_GENERATORS[4]`, the
primitive 16th root of unity, stored canonically. -/
theorem baby_bear.BabyBearParameters.ROOTS_16.eq :
    TwoAdicParams.ROOTS_16 ⦃ s => (∀ y ∈ s.val, Canonical y) ∧
      s.val.map Spec.BabyBear.toField =
        (List.range 8).map (fun j => BabyBear.twoAdicGenerators[4]! ^ j) ⦄ :=
  Proofs.BabyBear.TwoAdicParams.ROOTS_16.eq

/-- `INV_ROOTS_16` holds the inverses of `ROOTS_16`, in the same order, stored
canonically. -/
theorem baby_bear.BabyBearParameters.INV_ROOTS_16.eq :
    TwoAdicParams.INV_ROOTS_16 ⦃ s => (∀ y ∈ s.val, Canonical y) ∧
      s.val.map Spec.BabyBear.toField =
        (List.range 8).map (fun j => (BabyBear.twoAdicGenerators[4]! ^ j)⁻¹) ⦄ :=
  Proofs.BabyBear.TwoAdicParams.INV_ROOTS_16.eq

/-- `ODD_FACTOR`, computed as `PRIME >> TWO_ADICITY`, is `15`, the odd `r` with
`p = r · 2^TWO_ADICITY + 1`. -/
theorem baby_bear.BabyBearParameters.ODD_FACTOR.spec :
    TwoAdicParams.ODD_FACTOR ⦃ r => r.val = 15 ∧
      (PRIME.val : ℤ) = r.val * 2 ^ TWO_ADICITY.val + 1 ⦄ :=
  Proofs.BabyBear.TwoAdicParams.ODD_FACTOR.spec

/-! ## `RelativelyPrimePower<7>` -/

/-- Raising to the power `1725656503` inverts `x ↦ x^7` on the BabyBear field.
`exp_root_d` computes `x^(1/7)` as `exp_1725656503(x)`; this is the
number-theoretic fact it relies on (`7 · 1725656503 ≡ 1 mod p - 1`). The body of
`exp_1725656503` is opaque in the model, so the claim is about the exponent, not
the function. -/
theorem baby_bear.BabyBearParameters.exp_root_d.exponent (x : BabyBear.Field) :
    (x ^ 1725656503) ^ 7 = x :=
  Proofs.BabyBear.exp_root_seven x

/-! ## `BinomialExtensionData<D>`: the binomial extensions

BabyBear's extension fields of degree `D = 4, 5, 8` are `F[X] / (X ^ D - W)`.
The trait requires `X ^ D - W` to be irreducible (otherwise the quotient is not a
field), `DTH_ROOT` to be `W ^ ((p - 1) / D)`, `EXT_TWO_ADICITY` to be the
two-adicity of `p ^ D - 1`, and the `i`-th entry of
`TWO_ADIC_EXTENSION_GENERATORS` to be a primitive `2 ^ (TWO_ADICITY + 1 + i)`-th
root of unity. Each extension element is read through
`Plonky3Lean.Spec.BabyBear.toExt`.

The degree-5 field has no two-adic extension generators: `p ^ 5 - 1` has the
same two-adicity as `p - 1`, and its `TWO_ADIC_EXTENSION_GENERATORS` is empty.

Not claimed: `EXT_GENERATOR`, a generator of each extension's multiplicative
group. Proving that needs the factorisation of `p ^ D - 1`, which is a much
larger computation than anything else here. -/

/-- `W = 11` for the degree-4 extension, stored canonically, and `X ^ 4 - W` is
irreducible over the BabyBear field, so `F[X] / (X ^ 4 - W)` is a field of order
`p ^ 4`. -/
theorem baby_bear.BabyBearParameters.BinomialExtensionData4.W.irreducible :
    Ext4Params.W ⦃ w => Canonical w ∧ Spec.BabyBear.toField w = 11 ∧
      Irreducible (Polynomial.X ^ 4 - Polynomial.C (Spec.BabyBear.toField w)) ⦄ :=
  Proofs.BabyBear.Ext4Params.W.spec

/-- `DTH_ROOT` for the degree-4 extension is `W ^ ((p - 1) / 4)`, stored
canonically: the image of `X` under one application of Frobenius is
`DTH_ROOT · X`. -/
theorem baby_bear.BabyBearParameters.BinomialExtensionData4.DTH_ROOT.spec :
    ∃ w r, Ext4Params.W = .ok w ∧ Ext4Params.DTH_ROOT = .ok r ∧ Canonical r ∧
      Spec.BabyBear.toField r = Spec.BabyBear.toField w ^ ((BabyBear.fieldSize - 1) / 4) :=
  Proofs.BabyBear.Ext4Params.DTH_ROOT.spec

/-- `EXT_TWO_ADICITY` for the degree-4 extension is the two-adicity of
`p ^ 4 - 1`: `2 ^ EXT_TWO_ADICITY` divides it and no higher power of `2` does. -/
theorem baby_bear.BabyBearParameters.BinomialExtensionData4.EXT_TWO_ADICITY.spec :
    Ext4Params.EXT_TWO_ADICITY ⦃ e => 2 ^ e.val ∣ PRIME.val ^ 4 - 1 ∧
      ¬ 2 ^ (e.val + 1) ∣ PRIME.val ^ 4 - 1 ⦄ :=
  Proofs.BabyBear.Ext4Params.EXT_TWO_ADICITY.spec

/-- Entry `i` of `TWO_ADIC_EXTENSION_GENERATORS` for the degree-4 extension, read
as an element of `F[X] / (X ^ 4 - W)`, has order exactly
`2 ^ (TWO_ADICITY + 1 + i)`: it extends the base field's two-adic generators. -/
theorem baby_bear.BabyBearParameters.BinomialExtensionData4.TWO_ADIC_EXTENSION_GENERATORS.order :
    ∃ w t, Ext4Params.W = .ok w ∧ Ext4Params.TWO_ADIC_EXTENSION_GENERATORS = .ok t ∧
      ∀ i (h : i < t.val.length),
        orderOf (toExt 4 (Spec.BabyBear.toField w) t.val[i].val) =
          2 ^ (TWO_ADICITY.val + 1 + i) :=
  Proofs.BabyBear.Ext4Params.TWO_ADIC_EXTENSION_GENERATORS.order

/-- `W = 2` for the degree-5 extension, stored canonically, and `X ^ 5 - W` is
irreducible over the BabyBear field, so `F[X] / (X ^ 5 - W)` is a field of order
`p ^ 5`. -/
theorem baby_bear.BabyBearParameters.BinomialExtensionData5.W.irreducible :
    Ext5Params.W ⦃ w => Canonical w ∧ Spec.BabyBear.toField w = 2 ∧
      Irreducible (Polynomial.X ^ 5 - Polynomial.C (Spec.BabyBear.toField w)) ⦄ :=
  Proofs.BabyBear.Ext5Params.W.spec

/-- `DTH_ROOT` for the degree-5 extension is `W ^ ((p - 1) / 5)`, stored
canonically: the image of `X` under one application of Frobenius is
`DTH_ROOT · X`. -/
theorem baby_bear.BabyBearParameters.BinomialExtensionData5.DTH_ROOT.spec :
    ∃ w r, Ext5Params.W = .ok w ∧ Ext5Params.DTH_ROOT = .ok r ∧ Canonical r ∧
      Spec.BabyBear.toField r = Spec.BabyBear.toField w ^ ((BabyBear.fieldSize - 1) / 5) :=
  Proofs.BabyBear.Ext5Params.DTH_ROOT.spec

/-- `EXT_TWO_ADICITY` for the degree-5 extension is the two-adicity of
`p ^ 5 - 1`: `2 ^ EXT_TWO_ADICITY` divides it and no higher power of `2` does. -/
theorem baby_bear.BabyBearParameters.BinomialExtensionData5.EXT_TWO_ADICITY.spec :
    Ext5Params.EXT_TWO_ADICITY ⦃ e => 2 ^ e.val ∣ PRIME.val ^ 5 - 1 ∧
      ¬ 2 ^ (e.val + 1) ∣ PRIME.val ^ 5 - 1 ⦄ :=
  Proofs.BabyBear.Ext5Params.EXT_TWO_ADICITY.spec

/-- `W = 11` for the degree-8 extension, stored canonically, and `X ^ 8 - W` is
irreducible over the BabyBear field, so `F[X] / (X ^ 8 - W)` is a field of order
`p ^ 8`. -/
theorem baby_bear.BabyBearParameters.BinomialExtensionData8.W.irreducible :
    Ext8Params.W ⦃ w => Canonical w ∧ Spec.BabyBear.toField w = 11 ∧
      Irreducible (Polynomial.X ^ 8 - Polynomial.C (Spec.BabyBear.toField w)) ⦄ :=
  Proofs.BabyBear.Ext8Params.W.spec

/-- `DTH_ROOT` for the degree-8 extension is `W ^ ((p - 1) / 8)`, stored
canonically: the image of `X` under one application of Frobenius is
`DTH_ROOT · X`. -/
theorem baby_bear.BabyBearParameters.BinomialExtensionData8.DTH_ROOT.spec :
    ∃ w r, Ext8Params.W = .ok w ∧ Ext8Params.DTH_ROOT = .ok r ∧ Canonical r ∧
      Spec.BabyBear.toField r = Spec.BabyBear.toField w ^ ((BabyBear.fieldSize - 1) / 8) :=
  Proofs.BabyBear.Ext8Params.DTH_ROOT.spec

/-- `EXT_TWO_ADICITY` for the degree-8 extension is the two-adicity of
`p ^ 8 - 1`: `2 ^ EXT_TWO_ADICITY` divides it and no higher power of `2` does. -/
theorem baby_bear.BabyBearParameters.BinomialExtensionData8.EXT_TWO_ADICITY.spec :
    Ext8Params.EXT_TWO_ADICITY ⦃ e => 2 ^ e.val ∣ PRIME.val ^ 8 - 1 ∧
      ¬ 2 ^ (e.val + 1) ∣ PRIME.val ^ 8 - 1 ⦄ :=
  Proofs.BabyBear.Ext8Params.EXT_TWO_ADICITY.spec

/-- Entry `i` of `TWO_ADIC_EXTENSION_GENERATORS` for the degree-8 extension, read
as an element of `F[X] / (X ^ 8 - W)`, has order exactly
`2 ^ (TWO_ADICITY + 1 + i)`: it extends the base field's two-adic generators. -/
theorem baby_bear.BabyBearParameters.BinomialExtensionData8.TWO_ADIC_EXTENSION_GENERATORS.order :
    ∃ w t, Ext8Params.W = .ok w ∧ Ext8Params.TWO_ADIC_EXTENSION_GENERATORS = .ok t ∧
      ∀ i (h : i < t.val.length),
        orderOf (toExt 8 (Spec.BabyBear.toField w) t.val[i].val) =
          2 ^ (TWO_ADICITY.val + 1 + i) :=
  Proofs.BabyBear.Ext8Params.TWO_ADIC_EXTENSION_GENERATORS.order

/-! ## The Poseidon round-constant length assertions

`baby-bear/src/poseidon{1,2}.rs` check the length of each round-constant table
with an anonymous `const _: () = assert!(..)`. Aeneas extracts each one as a
`RustM Unit` computation: it builds the table (through `new_array` or
`new_2d_array`), takes its length, and asserts the comparison. Each claim
`… ⦃ _ => True ⦄` states that the computation does not panic. That is, the
table builds and the assertion holds. Nothing is said about the constants'
values.

All eleven assertions are claimed. Aeneas names the first in each module `_`
and the others `__N`, which post-patch 030 renames to `const_check_N`. -/

/-- The Poseidon1 assertion at `baby-bear/src/poseidon1.rs:66` holds: the
width-16 round-constant table `BABYBEAR_POSEIDON1_RC_16` has
`2 · HALF_FULL_ROUNDS + PARTIAL_ROUNDS_16 = 2 · 4 + 13 = 21` rows. -/
theorem poseidon1._.holds : poseidon1._ ⦃ _ => True ⦄ :=
  Proofs.BabyBear.poseidon1._.holds

/-- The Poseidon2 assertion at `baby-bear/src/poseidon2.rs:64` holds: the
width-16 initial external round constants,
`BABYBEAR_POSEIDON2_RC_16_EXTERNAL_INITIAL`, have `HALF_FULL_ROUNDS = 4` rows. -/
theorem poseidon2._.holds : poseidon2._ ⦃ _ => True ⦄ :=
  Proofs.BabyBear.poseidon2._.holds

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
