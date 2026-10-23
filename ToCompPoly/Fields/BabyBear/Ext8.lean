/-
Copyright (c) 2026 CompPoly. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Derek Sorensen
-/
module

public import CompPoly.Fields.Extension
public import CompPoly.Fields.BabyBear.Basic
public import Mathlib.Tactic.ReduceModChar

/-!
# The degree-8 extension of BabyBear

`BabyBear[X] / (X^8 - 11)`, the octic extension Plonky3 uses alongside the BabyBear base field.

Irreducibility of `X^8 - 11` is discharged by `Polynomial.irreducible_X_pow_sub_C`, whose two
hypotheses are single exponentiations in the base field: `11^((p^8-1)/8) = 1` and
`11^((p^4-1)/8) ≠ 1`.

## Main definitions

* `BabyBear.ext8Params`: the `BinomialParams` for `X^8 - 11`.
* `BabyBear.Ext8`: the extension field itself.
-/

@[expose] public section

namespace BabyBear

open CompPoly.Extension Polynomial

/-- The base-field cardinality as a bare numeral, for `reduce_mod_char`; `qNum_eq` pins it to
`fieldSize`. -/
private abbrev qNum : ℕ := 2013265921

private theorem qNum_eq : qNum = fieldSize := by norm_num

/-- The parameters of the octic extension `BabyBear[X] / (X^8 - 11)`. -/
def ext8Params : BinomialParams Field where
  d := 8
  W := 11
  two_le := by norm_num
  q := fieldSize

instance : Fact (Nat.card Field = ext8Params.q) :=
  ⟨by rw [Nat.card_eq_fintype_card]; exact ZMod.card _⟩

@[simp] theorem ext8Params_d : ext8Params.d = 8 := rfl
@[simp] theorem ext8Params_W : ext8Params.W = 11 := rfl
@[simp] theorem ext8Params_q : ext8Params.q = fieldSize := rfl

/-- `X^8 - 11` is irreducible over BabyBear, by Rabin's criterion. -/
theorem ext8Params_poly_irreducible : Irreducible ext8Params.poly := by
  have h8 : (8 : ℕ).primeFactors = {2} := by
    rw [show (8 : ℕ) = 2 ^ 3 from by norm_num,
      Nat.primeFactors_prime_pow (by norm_num) Nat.prime_two]
  rw [BinomialParams.poly, ext8Params_d, ext8Params_W]
  refine irreducible_X_pow_sub_C (q := qNum) (ZMod.card _) (by norm_num) (by decide)
    (by norm_num) (by simp only [h8, Finset.mem_singleton, forall_eq]; norm_num) ?_ ?_
  · show (11 : ZMod qNum) ^ ((qNum ^ 8 - 1) / 8) = 1
    reduce_mod_char
  · simp only [h8, Finset.mem_singleton, forall_eq]
    show (11 : ZMod qNum) ^ ((qNum ^ 4 - 1) / 8) ≠ 1
    reduce_mod_char
    decide

instance : Fact (Irreducible ext8Params.poly) := ⟨ext8Params_poly_irreducible⟩

/-- The irreducibility fact in the form the general framework's `Field` instance consumes. -/
instance : Fact (Irreducible ext8Params.toExtensionParams.poly) :=
  ⟨ext8Params.toExtensionParams_poly ▸ ext8Params_poly_irreducible⟩

/-- The degree-8 extension field of BabyBear. -/
abbrev Ext8 : Type := CompPoly.Extension.Ext ext8Params.toExtensionParams

@[simp] theorem card_ext8 : Fintype.card Ext8 = fieldSize ^ 8 := Ext.card_ext

end BabyBear
