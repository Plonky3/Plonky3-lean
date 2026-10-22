/-
Copyright (c) 2026 CompPoly. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Derek Sorensen
-/
module

public import CompPoly.Fields.BabyBear
public import Mathlib.RingTheory.AdjoinRoot
public import ToCompPoly.Fields.BabyBear
public import ToCompPoly.ToMathlib.Order.OrderOfSq
public import ToCompPoly.ToMathlib.Polynomial.XPowSubC
/-!
  # BabyBear: binomial extension fields

  The extensions of the BabyBear field that Plonky3 uses, `F[X] / (X ^ D - W)` for
  `(D, W) = (4, 11), (5, 2), (8, 11)`:
  - `ofCoeffs D W cs` is the element `Σ j, cs[j] · X ^ j`, the coefficient form in
    which an element is stored;
  - `X ^ D - W` is irreducible, so each quotient is a field (`Ext4`, `Ext5`, `Ext8`);
  - `ext*TwoAdicity` is the two-adicity of `p ^ D - 1`;
  - for `D = 4, 8`, `ext*TwoAdicGenerators` extends `twoAdicGenerators` past
    `twoAdicity`: entry `i` has order `2 ^ (twoAdicity + 1 + i)`, entry `0` squares to
    `twoAdicGenerators[twoAdicity]`, and each later entry to the one before.
    For `D = 5`, `p ^ 5 - 1` has the two-adicity of `p - 1`, so there is no such table.

  Everything is kernel-checked, without `native_decide`.
-/

@[expose] public section

open Polynomial

namespace BabyBear

/-! ## Elements in coefficient form -/

/-- The element `Σ j, cs[j] · X ^ j` of `F[X] / (X ^ D - W)`, in the basis
`1, X, …, X ^ (D - 1)`. -/
noncomputable def ofCoeffs (D : ℕ) (W : Field) (cs : List Field) : AdjoinRoot (X ^ D - C W) :=
  AdjoinRoot.mk _ ((cs.mapIdx fun j a => C a * X ^ j).sum)

/-- In `F[X] / (X ^ D - W)`, the root `X` satisfies `X ^ D = W`. -/
theorem root_pow_eq (D : ℕ) (W : Field) :
    AdjoinRoot.root (X ^ D - C W) ^ D = AdjoinRoot.of _ W := by
  have h := AdjoinRoot.eval₂_root (X ^ D - C W)
  simp only [eval₂_sub, eval₂_X_pow, eval₂_C] at h
  exact sub_eq_zero.mp h

/-- `twoAdicGenerators[27]`, mapped into an extension, keeps its order `2 ^ 27`. -/
theorem orderOf_of_twoAdicGenerator_27 {D : ℕ} (hD : 0 < D) (W : Field) :
    orderOf (AdjoinRoot.of (X ^ D - C W) (0x1A427A41 : Field)) = 2 ^ 27 := by
  have hinj : Function.Injective (AdjoinRoot.of (X ^ D - C W)) :=
    AdjoinRoot.of.injective_of_degree_ne_zero
      (by rw [degree_X_pow_sub_C hD]; exact_mod_cast hD.ne')
  have h1 := orderOf_injective (AdjoinRoot.of (X ^ D - C W)).toMonoidHom hinj
    (0x1A427A41 : Field)
  simp only [RingHom.toMonoidHom_eq_coe, MonoidHom.coe_ofClass] at h1
  rw [h1]
  have := twoAdicGenerators_order ⟨27, by decide⟩
  simpa [twoAdicGenerators] using this

/-- The last entry of `twoAdicGenerators`. -/
theorem twoAdicGenerators_twoAdicity : twoAdicGenerators[twoAdicity]! = 0x1A427A41 := rfl

/-! ## Degree 4: `X ^ 4 - 11` -/

/-- `W` of the degree-4 extension. -/
@[reducible]
def ext4W : Field := 11

theorem irreducible_ext4 : Irreducible (X ^ 4 - C ext4W) := by
  show Irreducible (X ^ 4 - C (11 : Field))
  refine X_pow_sub_C_irreducible_of_gcd (ℓ := 2) (by norm_num) (by decide) ?_ ?_
  · exact_mod_cast natCast_pow_ne_one 11 (by decide)
  · unfold fieldSize; decide

instance : Fact (Irreducible (X ^ 4 - C ext4W)) := ⟨irreducible_ext4⟩

/-- The degree-4 extension `F[X] / (X ^ 4 - 11)`, a field of order `p ^ 4`. -/
abbrev Ext4 := AdjoinRoot (X ^ 4 - C ext4W)

/-- The two-adicity of `p ^ 4 - 1`. -/
@[reducible]
def ext4TwoAdicity : ℕ := 29

theorem ext4TwoAdicity_spec :
    2 ^ ext4TwoAdicity ∣ fieldSize ^ 4 - 1 ∧ ¬ 2 ^ (ext4TwoAdicity + 1) ∣ fieldSize ^ 4 - 1 := by
  unfold fieldSize; decide

/-- The coefficients of the two-adic generators of `Ext4` past `twoAdicity`. -/
def ext4TwoAdicGeneratorCoeffs : List (List Field) :=
  [[0, 0, 1996171314, 0], [0, 0, 0, 124907976]]

/-- The two-adic generators of `Ext4` past `twoAdicity`. -/
noncomputable def ext4TwoAdicGenerators : List Ext4 :=
  ext4TwoAdicGeneratorCoeffs.map (ofCoeffs 4 ext4W)

theorem ext4TwoAdicGenerators_length :
    twoAdicity + ext4TwoAdicGenerators.length = ext4TwoAdicity := rfl

/-- Entry `0` squares to `twoAdicGenerators[twoAdicity]`, and each later entry to the
one before. -/
theorem ext4TwoAdicGenerators_sq_succ :
    let chain : List Ext4 :=
      AdjoinRoot.of _ twoAdicGenerators[twoAdicity]! :: ext4TwoAdicGenerators
    ∀ i (h : i + 1 < chain.length), chain[i + 1] ^ 2 = chain[i] := by
  intro chain i hi
  have hi' : i < 2 := by
    simp [chain, ext4TwoAdicGenerators, ext4TwoAdicGeneratorCoeffs] at hi; omega
  have hr := root_pow_eq 4 ext4W
  interval_cases i
  · simp only [chain, twoAdicGenerators_twoAdicity, List.getElem_cons_succ,
      List.getElem_cons_zero, ext4TwoAdicGenerators, ext4TwoAdicGeneratorCoeffs,
      List.getElem_map, List.getElem_cons_zero]
    simp only [ofCoeffs, List.mapIdx_cons, List.mapIdx_nil, List.sum_cons, List.sum_nil,
      map_mul, map_pow, AdjoinRoot.mk_C, AdjoinRoot.mk_X, map_zero, zero_mul,
      zero_add, add_zero, Nat.reduceAdd]
    rw [mul_pow, ← pow_mul, hr, ← map_pow, ← map_mul]
    congr 1
  · simp only [chain, List.getElem_cons_succ, ext4TwoAdicGenerators,
      ext4TwoAdicGeneratorCoeffs, List.getElem_map, List.getElem_cons_zero]
    simp only [ofCoeffs, List.mapIdx_cons, List.mapIdx_nil, List.sum_cons, List.sum_nil,
      map_mul, map_pow, AdjoinRoot.mk_C, AdjoinRoot.mk_X, map_zero, zero_mul,
      zero_add, add_zero, Nat.reduceAdd]
    rw [mul_pow, ← pow_mul, show 3 * 2 = 4 + 2 by rfl, pow_add, hr, ← mul_assoc,
      ← map_pow, ← map_mul]
    congr 2

theorem ext4TwoAdicGenerators_order :
    ∀ i (h : i < ext4TwoAdicGenerators.length),
      orderOf ext4TwoAdicGenerators[i] = 2 ^ (twoAdicity + 1 + i) := by
  have hlen : ext4TwoAdicGenerators.length = 2 := rfl
  have hs := ext4TwoAdicGenerators_sq_succ
  simp only [twoAdicGenerators_twoAdicity] at hs
  have s0 : ext4TwoAdicGenerators[0] ^ 2 = AdjoinRoot.of _ (0x1A427A41 : Field) := by
    simpa only [List.getElem_cons_succ, List.getElem_cons_zero] using hs 0 (by simp [hlen])
  have s1 : ext4TwoAdicGenerators[1] ^ 2 = ext4TwoAdicGenerators[0] := by
    simpa only [List.getElem_cons_succ] using hs 1 (by simp [hlen])
  have h0 := orderOf_eq_two_pow_succ_of_sq (k := 26) s0
    (orderOf_of_twoAdicGenerator_27 (by norm_num) _)
  have h1 := orderOf_eq_two_pow_succ_of_sq (k := 27) s1 h0
  intro i hi
  rw [hlen] at hi
  interval_cases i
  · exact h0
  · exact h1

/-! ## Degree 5: `X ^ 5 - 2` -/

/-- `W` of the degree-5 extension. -/
@[reducible]
def ext5W : Field := 2

theorem irreducible_ext5 : Irreducible (X ^ 5 - C ext5W) := by
  show Irreducible (X ^ 5 - C (2 : Field))
  refine X_pow_sub_C_irreducible_of_gcd (ℓ := 5) (by norm_num) (by decide) ?_ ?_
  · exact_mod_cast natCast_pow_ne_one 2 (by decide)
  · unfold fieldSize; decide

instance : Fact (Irreducible (X ^ 5 - C ext5W)) := ⟨irreducible_ext5⟩

/-- The degree-5 extension `F[X] / (X ^ 5 - 2)`, a field of order `p ^ 5`. -/
abbrev Ext5 := AdjoinRoot (X ^ 5 - C ext5W)

/-- The two-adicity of `p ^ 5 - 1`, the same as that of `p - 1`. -/
@[reducible]
def ext5TwoAdicity : ℕ := 27

theorem ext5TwoAdicity_spec :
    2 ^ ext5TwoAdicity ∣ fieldSize ^ 5 - 1 ∧ ¬ 2 ^ (ext5TwoAdicity + 1) ∣ fieldSize ^ 5 - 1 := by
  unfold fieldSize; decide

/-! ## Degree 8: `X ^ 8 - 11` -/

/-- `W` of the degree-8 extension. -/
@[reducible]
def ext8W : Field := 11

theorem irreducible_ext8 : Irreducible (X ^ 8 - C ext8W) := by
  show Irreducible (X ^ 8 - C (11 : Field))
  refine X_pow_sub_C_irreducible_of_gcd (ℓ := 2) (by norm_num) (by decide) ?_ ?_
  · exact_mod_cast natCast_pow_ne_one 11 (by decide)
  · unfold fieldSize; decide

instance : Fact (Irreducible (X ^ 8 - C ext8W)) := ⟨irreducible_ext8⟩

/-- The degree-8 extension `F[X] / (X ^ 8 - 11)`, a field of order `p ^ 8`. -/
abbrev Ext8 := AdjoinRoot (X ^ 8 - C ext8W)

/-- The two-adicity of `p ^ 8 - 1`. -/
@[reducible]
def ext8TwoAdicity : ℕ := 30

theorem ext8TwoAdicity_spec :
    2 ^ ext8TwoAdicity ∣ fieldSize ^ 8 - 1 ∧ ¬ 2 ^ (ext8TwoAdicity + 1) ∣ fieldSize ^ 8 - 1 := by
  unfold fieldSize; decide

/-- The coefficients of the two-adic generators of `Ext8` past `twoAdicity`. -/
def ext8TwoAdicGeneratorCoeffs : List (List Field) :=
  [[0, 0, 0, 0, 1996171314, 0, 0, 0], [0, 0, 0, 0, 0, 0, 124907976, 0],
    [0, 0, 0, 518392818, 0, 0, 0, 0]]

/-- The two-adic generators of `Ext8` past `twoAdicity`. -/
noncomputable def ext8TwoAdicGenerators : List Ext8 :=
  ext8TwoAdicGeneratorCoeffs.map (ofCoeffs 8 ext8W)

theorem ext8TwoAdicGenerators_length :
    twoAdicity + ext8TwoAdicGenerators.length = ext8TwoAdicity := rfl

/-- Entry `0` squares to `twoAdicGenerators[twoAdicity]`, and each later entry to the
one before. -/
theorem ext8TwoAdicGenerators_sq_succ :
    let chain : List Ext8 :=
      AdjoinRoot.of _ twoAdicGenerators[twoAdicity]! :: ext8TwoAdicGenerators
    ∀ i (h : i + 1 < chain.length), chain[i + 1] ^ 2 = chain[i] := by
  intro chain i hi
  have hi' : i < 3 := by
    simp [chain, ext8TwoAdicGenerators, ext8TwoAdicGeneratorCoeffs] at hi; omega
  have hr := root_pow_eq 8 ext8W
  interval_cases i
  · simp only [chain, twoAdicGenerators_twoAdicity, List.getElem_cons_succ,
      List.getElem_cons_zero, ext8TwoAdicGenerators, ext8TwoAdicGeneratorCoeffs,
      List.getElem_map, List.getElem_cons_zero]
    simp only [ofCoeffs, List.mapIdx_cons, List.mapIdx_nil, List.sum_cons, List.sum_nil,
      map_mul, map_pow, AdjoinRoot.mk_C, AdjoinRoot.mk_X, map_zero, zero_mul,
      zero_add, add_zero, Nat.reduceAdd]
    rw [mul_pow, ← pow_mul, hr, ← map_pow, ← map_mul]
    congr 1
  · simp only [chain, List.getElem_cons_succ, ext8TwoAdicGenerators,
      ext8TwoAdicGeneratorCoeffs, List.getElem_map, List.getElem_cons_zero]
    simp only [ofCoeffs, List.mapIdx_cons, List.mapIdx_nil, List.sum_cons, List.sum_nil,
      map_mul, map_pow, AdjoinRoot.mk_C, AdjoinRoot.mk_X, map_zero, zero_mul,
      zero_add, add_zero, Nat.reduceAdd]
    rw [mul_pow, ← pow_mul, show 6 * 2 = 8 + 4 by rfl, pow_add, hr, ← mul_assoc,
      ← map_pow, ← map_mul]
    congr 2
  · simp only [chain, List.getElem_cons_succ, ext8TwoAdicGenerators,
      ext8TwoAdicGeneratorCoeffs, List.getElem_map, List.getElem_cons_zero]
    simp only [ofCoeffs, List.mapIdx_cons, List.mapIdx_nil, List.sum_cons, List.sum_nil,
      map_mul, map_pow, AdjoinRoot.mk_C, AdjoinRoot.mk_X, map_zero, zero_mul,
      zero_add, add_zero, Nat.reduceAdd]
    rw [mul_pow, ← pow_mul, ← map_pow]
    congr 2

theorem ext8TwoAdicGenerators_order :
    ∀ i (h : i < ext8TwoAdicGenerators.length),
      orderOf ext8TwoAdicGenerators[i] = 2 ^ (twoAdicity + 1 + i) := by
  have hlen : ext8TwoAdicGenerators.length = 3 := rfl
  have hs := ext8TwoAdicGenerators_sq_succ
  simp only [twoAdicGenerators_twoAdicity] at hs
  have s0 : ext8TwoAdicGenerators[0] ^ 2 = AdjoinRoot.of _ (0x1A427A41 : Field) := by
    simpa only [List.getElem_cons_succ, List.getElem_cons_zero] using hs 0 (by simp [hlen])
  have s1 : ext8TwoAdicGenerators[1] ^ 2 = ext8TwoAdicGenerators[0] := by
    simpa only [List.getElem_cons_succ] using hs 1 (by simp [hlen])
  have s2 : ext8TwoAdicGenerators[2] ^ 2 = ext8TwoAdicGenerators[1] := by
    simpa only [List.getElem_cons_succ] using hs 2 (by simp [hlen])
  have h0 := orderOf_eq_two_pow_succ_of_sq (k := 26) s0
    (orderOf_of_twoAdicGenerator_27 (by norm_num) _)
  have h1 := orderOf_eq_two_pow_succ_of_sq (k := 27) s1 h0
  have h2 := orderOf_eq_two_pow_succ_of_sq (k := 28) s2 h1
  intro i hi
  rw [hlen] at hi
  interval_cases i
  · exact h0
  · exact h1
  · exact h2

end BabyBear
