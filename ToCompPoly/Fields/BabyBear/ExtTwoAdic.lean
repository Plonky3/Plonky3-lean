/-
Copyright (c) 2026 CompPoly. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Derek Sorensen
-/
module

public import CompPoly.Fields.BabyBear
public import CompPoly.Fields.BabyBear.Ext4
public import ToCompPoly.Fields.BabyBear.Ext5
public import ToCompPoly.Fields.BabyBear.Ext8
public import ToCompPoly.Fields.Extension.Monomial
public import ToCompPoly.ToMathlib.Order.OrderOfSq

/-!
# BabyBear: two-adic data of the binomial extensions

For the extensions `Ext4`, `Ext5` and `Ext8` (`X ^ D - W` for `(D, W) = (4, 11), (5, 2), (8, 11)`):

- `ext*TwoAdicity` is the two-adicity of `p ^ D - 1`.
- For `D = 4, 8`, `ext*TwoAdicGenerators` extends `twoAdicGenerators` past `twoAdicity`:
  - entry `i` has order `2 ^ (twoAdicity + 1 + i)`;
  - entry `0` squares to `twoAdicGenerators[twoAdicity]`, and each later entry to the one
    before;
  - `ext*TwoAdicGeneratorCoeffs` gives the coefficients of each entry.
- For `D = 5`, `p ^ 5 - 1` has the two-adicity of `p - 1`, so there is no such table.

Each generator is a monomial `c · X ^ k`, so the squaring chain is computed with
`Ext.monomial_mul_monomial` and `Ext.monomial_mul_monomial_of_le`. Everything is kernel-checked,
without `native_decide`.
-/

@[expose] public section

namespace BabyBear

open CompPoly.Extension

/-- The last entry of `twoAdicGenerators`. -/
theorem twoAdicGenerators_twoAdicity : twoAdicGenerators[twoAdicity]! = 0x1A427A41 := rfl

/-- `twoAdicGenerators[27]` has order `2 ^ 27`. -/
theorem orderOf_twoAdicGenerator_27 : orderOf (0x1A427A41 : Field) = 2 ^ 27 := by
  have := twoAdicGenerators_order ⟨27, by decide⟩
  simpa [twoAdicGenerators] using this

/-! ## Two-adicity of `p ^ D - 1` -/

/-- The two-adicity of `p ^ 4 - 1`. -/
@[reducible]
def ext4TwoAdicity : ℕ := 29

theorem ext4TwoAdicity_spec :
    2 ^ ext4TwoAdicity ∣ fieldSize ^ 4 - 1 ∧ ¬ 2 ^ (ext4TwoAdicity + 1) ∣ fieldSize ^ 4 - 1 := by
  unfold fieldSize; decide

/-- The two-adicity of `p ^ 5 - 1`, the same as that of `p - 1`. -/
@[reducible]
def ext5TwoAdicity : ℕ := 27

theorem ext5TwoAdicity_spec :
    2 ^ ext5TwoAdicity ∣ fieldSize ^ 5 - 1 ∧ ¬ 2 ^ (ext5TwoAdicity + 1) ∣ fieldSize ^ 5 - 1 := by
  unfold fieldSize; decide

/-- The two-adicity of `p ^ 8 - 1`. -/
@[reducible]
def ext8TwoAdicity : ℕ := 30

theorem ext8TwoAdicity_spec :
    2 ^ ext8TwoAdicity ∣ fieldSize ^ 8 - 1 ∧ ¬ 2 ^ (ext8TwoAdicity + 1) ∣ fieldSize ^ 8 - 1 := by
  unfold fieldSize; decide

/-! ## Degree 4 -/

/-- The coefficients of the two-adic generators of `Ext4` past `twoAdicity`. -/
def ext4TwoAdicGeneratorCoeffs : List (List Field) :=
  [[0, 0, 1996171314, 0], [0, 0, 0, 124907976]]

/-- The two-adic generators of `Ext4` past `twoAdicity`: `1996171314 · X ^ 2` and
`124907976 · X ^ 3`. -/
def ext4TwoAdicGenerators : List Ext4 :=
  [Ext.monomial 2 1996171314, Ext.monomial 3 124907976]

/-- `ext4TwoAdicGeneratorCoeffs` lists the coefficients of `ext4TwoAdicGenerators`. -/
theorem ext4TwoAdicGeneratorCoeffs_eq :
    ext4TwoAdicGeneratorCoeffs = ext4TwoAdicGenerators.map fun x => List.ofFn (Ext.coeff x) := by
  decide

theorem ext4TwoAdicGenerators_length :
    twoAdicity + ext4TwoAdicGenerators.length = ext4TwoAdicity := rfl

/-- Entry `0` squares to `twoAdicGenerators[twoAdicity]`, and each later entry to the one
before. -/
theorem ext4TwoAdicGenerators_sq_succ :
    let chain : List Ext4 := Ext.ofBase twoAdicGenerators[twoAdicity]! :: ext4TwoAdicGenerators
    ∀ i (h : i + 1 < chain.length), chain[i + 1] ^ 2 = chain[i] := by
  intro chain i hi
  have hi' : i < 2 := by simp [chain, ext4TwoAdicGenerators] at hi; omega
  interval_cases i
  · show (Ext.monomial 2 1996171314 : Ext4) ^ 2 = Ext.ofBase twoAdicGenerators[twoAdicity]!
    rw [sq, Ext.monomial_mul_monomial_of_le ext4Params 2 2 (by decide) (by decide) (by decide),
      show 2 + 2 - ext4Params.d = 0 from rfl, Ext.monomial_zero, twoAdicGenerators_twoAdicity]
    congr 1
  · show (Ext.monomial 3 124907976 : Ext4) ^ 2 = Ext.monomial 2 1996171314
    rw [sq, Ext.monomial_mul_monomial_of_le ext4Params 3 3 (by decide) (by decide) (by decide)]
    congr 1

theorem ext4TwoAdicGenerators_order :
    ∀ i (h : i < ext4TwoAdicGenerators.length),
      orderOf ext4TwoAdicGenerators[i] = 2 ^ (twoAdicity + 1 + i) := by
  have hlen : ext4TwoAdicGenerators.length = 2 := rfl
  have hs := ext4TwoAdicGenerators_sq_succ
  simp only [twoAdicGenerators_twoAdicity] at hs
  have s0 : ext4TwoAdicGenerators[0] ^ 2 = Ext.ofBase (0x1A427A41 : Field) := by
    simpa only [List.getElem_cons_succ, List.getElem_cons_zero] using hs 0 (by simp [hlen])
  have s1 : ext4TwoAdicGenerators[1] ^ 2 = ext4TwoAdicGenerators[0] := by
    simpa only [List.getElem_cons_succ] using hs 1 (by simp [hlen])
  have hbase : orderOf (Ext.ofBase (0x1A427A41 : Field) : Ext4) = 2 ^ 27 := by
    rw [Ext.orderOf_ofBase, orderOf_twoAdicGenerator_27]
  have h0 := orderOf_eq_two_pow_succ_of_sq (k := 26) s0 hbase
  have h1 := orderOf_eq_two_pow_succ_of_sq (k := 27) s1 h0
  intro i hi
  rw [hlen] at hi
  interval_cases i
  · exact h0
  · exact h1

/-! ## Degree 8 -/

/-- The coefficients of the two-adic generators of `Ext8` past `twoAdicity`. -/
def ext8TwoAdicGeneratorCoeffs : List (List Field) :=
  [[0, 0, 0, 0, 1996171314, 0, 0, 0], [0, 0, 0, 0, 0, 0, 124907976, 0],
    [0, 0, 0, 518392818, 0, 0, 0, 0]]

/-- The two-adic generators of `Ext8` past `twoAdicity`: `1996171314 · X ^ 4`,
`124907976 · X ^ 6` and `518392818 · X ^ 3`. -/
def ext8TwoAdicGenerators : List Ext8 :=
  [Ext.monomial 4 1996171314, Ext.monomial 6 124907976, Ext.monomial 3 518392818]

/-- `ext8TwoAdicGeneratorCoeffs` lists the coefficients of `ext8TwoAdicGenerators`. -/
theorem ext8TwoAdicGeneratorCoeffs_eq :
    ext8TwoAdicGeneratorCoeffs = ext8TwoAdicGenerators.map fun x => List.ofFn (Ext.coeff x) := by
  decide

theorem ext8TwoAdicGenerators_length :
    twoAdicity + ext8TwoAdicGenerators.length = ext8TwoAdicity := rfl

/-- Entry `0` squares to `twoAdicGenerators[twoAdicity]`, and each later entry to the one
before. -/
theorem ext8TwoAdicGenerators_sq_succ :
    let chain : List Ext8 := Ext.ofBase twoAdicGenerators[twoAdicity]! :: ext8TwoAdicGenerators
    ∀ i (h : i + 1 < chain.length), chain[i + 1] ^ 2 = chain[i] := by
  intro chain i hi
  have hi' : i < 3 := by simp [chain, ext8TwoAdicGenerators] at hi; omega
  interval_cases i
  · show (Ext.monomial 4 1996171314 : Ext8) ^ 2 = Ext.ofBase twoAdicGenerators[twoAdicity]!
    rw [sq, Ext.monomial_mul_monomial_of_le ext8Params 4 4 (by decide) (by decide) (by decide),
      show 4 + 4 - ext8Params.d = 0 from rfl, Ext.monomial_zero, twoAdicGenerators_twoAdicity]
    congr 1
  · show (Ext.monomial 6 124907976 : Ext8) ^ 2 = Ext.monomial 4 1996171314
    rw [sq, Ext.monomial_mul_monomial_of_le ext8Params 6 6 (by decide) (by decide) (by decide)]
    congr 1
  · show (Ext.monomial 3 518392818 : Ext8) ^ 2 = Ext.monomial 6 124907976
    rw [sq, Ext.monomial_mul_monomial 3 3 (by decide)]
    congr 1

theorem ext8TwoAdicGenerators_order :
    ∀ i (h : i < ext8TwoAdicGenerators.length),
      orderOf ext8TwoAdicGenerators[i] = 2 ^ (twoAdicity + 1 + i) := by
  have hlen : ext8TwoAdicGenerators.length = 3 := rfl
  have hs := ext8TwoAdicGenerators_sq_succ
  simp only [twoAdicGenerators_twoAdicity] at hs
  have s0 : ext8TwoAdicGenerators[0] ^ 2 = Ext.ofBase (0x1A427A41 : Field) := by
    simpa only [List.getElem_cons_succ, List.getElem_cons_zero] using hs 0 (by simp [hlen])
  have s1 : ext8TwoAdicGenerators[1] ^ 2 = ext8TwoAdicGenerators[0] := by
    simpa only [List.getElem_cons_succ] using hs 1 (by simp [hlen])
  have s2 : ext8TwoAdicGenerators[2] ^ 2 = ext8TwoAdicGenerators[1] := by
    simpa only [List.getElem_cons_succ] using hs 2 (by simp [hlen])
  have hbase : orderOf (Ext.ofBase (0x1A427A41 : Field) : Ext8) = 2 ^ 27 := by
    rw [Ext.orderOf_ofBase, orderOf_twoAdicGenerator_27]
  have h0 := orderOf_eq_two_pow_succ_of_sq (k := 26) s0 hbase
  have h1 := orderOf_eq_two_pow_succ_of_sq (k := 27) s1 h0
  have h2 := orderOf_eq_two_pow_succ_of_sq (k := 28) s2 h1
  intro i hi
  rw [hlen] at hi
  interval_cases i
  · exact h0
  · exact h1
  · exact h2

end BabyBear
