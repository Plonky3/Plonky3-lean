/-
Copyright (c) 2026 CompPoly. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Coratger
-/
import Mathlib.RingTheory.AdjoinRoot
import ToCompPoly.Fields.Mersenne
import ToCompPoly.ToMathlib.Order.OrderOfSq

/-!
  # Mersenne31: the complex extension `F[i] = F[X] / (X ^ 2 + 1)`

  Since `p ≡ 3 (mod 4)`, `-1` is not a square and `X ^ 2 + 1` is irreducible, so
  `Complex = F[i]` is a field with `p ^ 2` elements.
  - `Complex.mk a b` is `a + b · i`;
  - the Frobenius map is complex conjugation, so `z ^ (p + 1)` is the norm `a ^ 2 + b ^ 2`;
  - `twoAdicGenerators` lists an element of order `2 ^ k` for each `k ≤ 32`, each the square
    root of the one before; entries `0` to `31` lie on the circle `a ^ 2 + b ^ 2 = 1`.

  Everything is kernel-checked, without `native_decide`.
-/

open Polynomial

namespace Mersenne31

/-- `X ^ 2 + 1`, written as `X ^ 2 - (-1)`. -/
noncomputable abbrev complexPoly : Field[X] := X ^ 2 - C (-1)

theorem irreducible_complexPoly : Irreducible complexPoly :=
  X_pow_sub_C_irreducible_of_prime Nat.prime_two neg_one_ne_sq

instance : Fact (Irreducible complexPoly) := ⟨irreducible_complexPoly⟩

/-- The complex extension `F[X] / (X ^ 2 + 1)`, a field of order `p ^ 2`. -/
abbrev Complex := AdjoinRoot complexPoly

namespace Complex

/-- The square root of `-1`. -/
noncomputable def i : Complex := AdjoinRoot.root complexPoly

theorem i_sq : i ^ 2 = -1 := by
  have h := AdjoinRoot.eval₂_root complexPoly
  simp only [eval₂_sub, eval₂_X_pow, eval₂_C] at h
  simp only [map_neg, map_one] at h
  rw [i]; linear_combination h

/-- The element `a + b · i`. -/
noncomputable def mk (a b : Field) : Complex :=
  AdjoinRoot.of complexPoly a + AdjoinRoot.of complexPoly b * i

theorem mk_mul (a b c d : Field) :
    mk a b * mk c d = mk (a * c - b * d) (a * d + b * c) := by
  simp only [mk, map_sub, map_add, map_mul]
  linear_combination (AdjoinRoot.of complexPoly b * AdjoinRoot.of complexPoly d) * i_sq

theorem mk_sq (a b : Field) : mk a b ^ 2 = mk (a * a - b * b) (a * b + b * a) := by
  rw [sq, mk_mul]

theorem mk_one : mk 1 0 = 1 := by simp [mk]

theorem mk_neg_one : mk (-1) 0 = -1 := by simp [mk]

theorem of_eq_mk (a : Field) : AdjoinRoot.of complexPoly a = mk a 0 := by simp [mk]

theorem mk_injective {a b c d : Field} (h : mk a b = mk c d) : a = c ∧ b = d := by
  have h0 : AdjoinRoot.mk complexPoly (C (a - c) + C (b - d) * X) = 0 := by
    simp only [map_add, map_mul, AdjoinRoot.mk_C, AdjoinRoot.mk_X, map_sub]
    simp only [mk] at h
    rw [← i]
    linear_combination h
  have hdvd := AdjoinRoot.mk_eq_zero.mp h0
  have hdeg : (C (a - c) + C (b - d) * X).degree < complexPoly.degree := by
    rw [degree_X_pow_sub_C (by norm_num)]
    calc (C (a - c) + C (b - d) * X).degree ≤ ((1 : ℕ) : WithBot ℕ) := by
          rw [add_comm]; exact degree_linear_le
      _ < ((2 : ℕ) : WithBot ℕ) := by norm_num
  have hz := eq_zero_of_dvd_of_degree_lt hdvd hdeg
  have h1 := congrArg (coeff · 0) hz
  have h2 := congrArg (coeff · 1) hz
  simp at h1 h2
  exact ⟨sub_eq_zero.mp h1, sub_eq_zero.mp h2⟩

/-- Every element is `a + b · i`. -/
theorem exists_mk (z : Complex) : ∃ a b, z = mk a b := by
  obtain ⟨f, rfl⟩ := AdjoinRoot.mk_surjective z
  have hm : complexPoly.Monic := monic_X_pow_sub_C _ (by norm_num)
  have hdeg : (f %ₘ complexPoly).degree ≤ 1 := by
    have := degree_modByMonic_lt f hm
    rw [degree_X_pow_sub_C (by norm_num)] at this
    exact Order.le_of_lt_succ this
  refine ⟨(f %ₘ complexPoly).coeff 0, (f %ₘ complexPoly).coeff 1, ?_⟩
  have hmod : AdjoinRoot.mk complexPoly f = AdjoinRoot.mk complexPoly (f %ₘ complexPoly) := by
    rw [AdjoinRoot.mk_eq_mk]
    exact ⟨f /ₘ complexPoly, sub_eq_iff_eq_add'.mpr (modByMonic_add_div f complexPoly).symm⟩
  rw [hmod]
  conv_lhs => rw [eq_X_add_C_of_degree_le_one hdeg]
  simp only [map_add, map_mul, AdjoinRoot.mk_C, AdjoinRoot.mk_X, mk, i]
  ring

instance : CharP Complex fieldSize :=
  charP_of_injective_algebraMap (algebraMap Field Complex).injective fieldSize

/-- The Frobenius map `z ↦ z ^ p` is complex conjugation, since `i ^ p = -i` for `p ≡ 3 (mod 4)`. -/
theorem mk_pow_fieldSize (a b : Field) : mk a b ^ fieldSize = mk a (-b) := by
  have hi : i ^ fieldSize = -i := by
    rw [show fieldSize = 2 * 1073741823 + 1 by decide, pow_succ, pow_mul, i_sq,
      Odd.neg_one_pow (by decide)]
    ring
  simp only [mk]
  rw [add_pow_char, mul_pow, ← map_pow, ← map_pow, ZMod.pow_card, ZMod.pow_card, hi, map_neg]
  ring

/-- `z ^ (p + 1)` is the norm `a ^ 2 + b ^ 2`, an element of the base field. -/
theorem mk_pow_fieldSize_succ (a b : Field) :
    mk a b ^ (fieldSize + 1) = AdjoinRoot.of complexPoly (a * a + b * b) := by
  rw [pow_succ, mk_pow_fieldSize, mk_mul, of_eq_mk]
  congr 1 <;> ring

end Complex

open Complex

/-! ## Two-adic generators -/

/-- The two-adicity of `p ^ 2 - 1 = (p - 1)(p + 1) = 2 · (2 ^ 30 - 1) · 2 ^ 31`. -/
@[reducible]
def complexTwoAdicity : ℕ := 32

theorem complexTwoAdicity_spec :
    2 ^ complexTwoAdicity ∣ fieldSize ^ 2 - 1 ∧ ¬ 2 ^ (complexTwoAdicity + 1) ∣ fieldSize ^ 2 - 1 := by
  unfold fieldSize; decide

/-- The coefficients `(a, b)` of `a + b · i` for the generators of the two-adic subgroups. -/
def twoAdicGeneratorCoeffs : List (Field × Field) :=
  [(1, 0), (2147483646, 0), (0, 2147483646), (32768, 2147450879), (590768354, 978592373),
    (1179735656, 1241207368), (1567857810, 456695729), (1774253895, 1309288441),
    (736262640, 1553669210), (1819216575, 1662816114), (1323191254, 1936974060),
    (605622498, 1964232216), (343674985, 501786993), (1995316534, 149306621),
    (2107600913, 1378821388), (541476169, 2101081972), (2135874973, 483411332),
    (2097144245, 1684033590), (1662322247, 670236780), (1172215635, 595888646),
    (241940101, 323856519), (1957194259, 2139647100), (1957419629, 1541039442),
    (1062045235, 1824580421), (1929382196, 1664698822), (1889294251, 331248939),
    (1214231414, 1646302518), (1765392370, 461136547), (1629751483, 66485474),
    (1501355827, 1439063420), (509778402, 800467507), (311014874, 1584694829),
    (1166849849, 1117296306)]

/-- Entry `k` generates the subgroup of order `2 ^ k` of `Complexˣ`. -/
noncomputable def twoAdicGenerators : List Complex :=
  twoAdicGeneratorCoeffs.map fun c => mk c.1 c.2

theorem twoAdicGenerators_length : twoAdicGenerators.length = complexTwoAdicity + 1 := rfl

/-- Each entry after the first squares to the one before, as a check on coefficients. -/
def twoAdicGeneratorCoeffs_chain : Bool :=
  (twoAdicGeneratorCoeffs.zip twoAdicGeneratorCoeffs.tail).all fun (x, y) =>
    decide (y.1 * y.1 - y.2 * y.2 = x.1) && decide (y.1 * y.2 + y.2 * y.1 = x.2)

theorem twoAdicGeneratorCoeffs_chain_eq : twoAdicGeneratorCoeffs_chain = true := by decide

/-- Entry `k + 1` squares to entry `k`. -/
theorem twoAdicGenerators_sq_succ (k : ℕ) (hk : k + 1 < twoAdicGenerators.length) :
    twoAdicGenerators[k + 1] ^ 2 = twoAdicGenerators[k] := by
  have h := twoAdicGeneratorCoeffs_chain_eq
  simp only [twoAdicGeneratorCoeffs_chain, List.all_eq_true, Bool.and_eq_true,
    decide_eq_true_eq] at h
  have hk' : k < (twoAdicGeneratorCoeffs.zip twoAdicGeneratorCoeffs.tail).length := by
    simp [twoAdicGenerators] at hk ⊢; omega
  obtain ⟨h1, h2⟩ := h _ (List.getElem_mem hk')
  simp only [List.getElem_zip, List.getElem_tail] at h1 h2
  simp only [twoAdicGenerators, List.getElem_map, mk_sq, h1, h2]

theorem twoAdicGenerators_one : twoAdicGenerators[1] = -1 := by
  rw [← mk_neg_one]; simp [twoAdicGenerators, twoAdicGeneratorCoeffs]; rfl

theorem ringChar_complex : ringChar Complex = fieldSize := ringChar.eq Complex fieldSize

/-- Entry `k` has order `2 ^ k`. -/
theorem twoAdicGenerators_order (k : ℕ) (hk : k < twoAdicGenerators.length) :
    orderOf twoAdicGenerators[k] = 2 ^ k := by
  rcases k with _ | k
  · simp [twoAdicGenerators, twoAdicGeneratorCoeffs, mk_one]
  · induction k with
    | zero =>
      rw [twoAdicGenerators_one, orderOf_neg_one, ringChar_complex, if_neg (by decide)]; rfl
    | succ k ih =>
      exact orderOf_eq_two_pow_succ_of_sq (twoAdicGenerators_sq_succ (k + 1) hk) (ih (by omega))

/-- Entries `0` to `31` lie on the circle `a ^ 2 + b ^ 2 = 1`, of order `p + 1 = 2 ^ 31`. -/
theorem twoAdicGeneratorCoeffs_norm :
    ∀ c ∈ twoAdicGeneratorCoeffs.take complexTwoAdicity, c.1 * c.1 + c.2 * c.2 = 1 := by
  have : (twoAdicGeneratorCoeffs.take complexTwoAdicity).all
      (fun c => decide (c.1 * c.1 + c.2 * c.2 = 1)) = true := by decide
  simpa using this

/-- The last entry, of order `2 ^ 32`, has norm `-1`, so it is off the circle. -/
theorem twoAdicGeneratorCoeffs_norm_last :
    ∀ c ∈ twoAdicGeneratorCoeffs.drop complexTwoAdicity, c.1 * c.1 + c.2 * c.2 = -1 := by
  have : (twoAdicGeneratorCoeffs.drop complexTwoAdicity).all
      (fun c => decide (c.1 * c.1 + c.2 * c.2 = -1)) = true := by decide
  simpa using this

end Mersenne31
