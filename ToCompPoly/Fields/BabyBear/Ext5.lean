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
# The degree-5 extension of BabyBear

`BabyBear[X] / (X^5 - 2)`, the quintic extension Plonky3 uses alongside the BabyBear base field.

Irreducibility of `X^5 - 2` is discharged by `Polynomial.irreducible_X_pow_sub_C`, whose two
hypotheses are single exponentiations in the base field: `2^((p^5-1)/5) = 1` and
`2^((p-1)/5) ≠ 1`.

## Main definitions

* `BabyBear.ext5Params`: the `BinomialParams` for `X^5 - 2`.
* `BabyBear.Ext5`: the extension field itself.
-/

@[expose] public section

namespace BabyBear

open CompPoly.Extension Polynomial

/-- The base-field cardinality as a bare numeral, for `reduce_mod_char`; `qNum_eq` pins it to
`fieldSize`. -/
private abbrev qNum : ℕ := 2013265921

private theorem qNum_eq : qNum = fieldSize := by norm_num

/-- The parameters of the quintic extension `BabyBear[X] / (X^5 - 2)`. -/
def ext5Params : BinomialParams Field where
  d := 5
  W := 2
  two_le := by norm_num
  q := fieldSize

instance : Fact (Nat.card Field = ext5Params.q) :=
  ⟨by rw [Nat.card_eq_fintype_card]; exact ZMod.card _⟩

@[simp] theorem ext5Params_d : ext5Params.d = 5 := rfl
@[simp] theorem ext5Params_W : ext5Params.W = 2 := rfl
@[simp] theorem ext5Params_q : ext5Params.q = fieldSize := rfl

/-- `X^5 - 2` is irreducible over BabyBear, by Rabin's criterion. -/
theorem ext5Params_poly_irreducible : Irreducible ext5Params.poly := by
  have h5 : (5 : ℕ).primeFactors = {5} := Nat.prime_five.primeFactors
  rw [BinomialParams.poly, ext5Params_d, ext5Params_W]
  refine irreducible_X_pow_sub_C (q := qNum) (ZMod.card _) (by norm_num) (by decide)
    (by norm_num) (by simp only [h5, Finset.mem_singleton, forall_eq]; norm_num) ?_ ?_
  · show (2 : ZMod qNum) ^ ((qNum ^ 5 - 1) / 5) = 1
    reduce_mod_char
  · simp only [h5, Finset.mem_singleton, forall_eq, Nat.div_self (by norm_num : 0 < 5), pow_one]
    show (2 : ZMod qNum) ^ ((qNum - 1) / 5) ≠ 1
    reduce_mod_char
    decide

instance : Fact (Irreducible ext5Params.poly) := ⟨ext5Params_poly_irreducible⟩

/-- The irreducibility fact in the form the general framework's `Field` instance consumes. -/
instance : Fact (Irreducible ext5Params.toExtensionParams.poly) :=
  ⟨ext5Params.toExtensionParams_poly ▸ ext5Params_poly_irreducible⟩

/-- The degree-5 extension field of BabyBear. -/
abbrev Ext5 : Type := CompPoly.Extension.Ext ext5Params.toExtensionParams

@[simp] theorem card_ext5 : Fintype.card Ext5 = fieldSize ^ 5 := Ext.card_ext

end BabyBear
