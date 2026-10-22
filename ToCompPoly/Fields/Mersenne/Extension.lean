/-
Copyright (c) 2026 CompPoly. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Coratger
-/
import CompPoly.Fields.PrattCertificate
import ToCompPoly.Fields.Mersenne.Complex
import ToCompPoly.ToMathlib.Polynomial.CoeffList

/-!
  # Mersenne31: the binomial extensions of `F` and of `F[i]`

  - `F[X] / (X ^ 3 - 5)`: `5` is not a cube, and `5 ^ ((p - 1) / 3)` is a primitive cube root of unity.
  - `F[i][Y] / (Y ^ 2 - (2 + i))`, the field QM31: `2 + i` is not a square.
  - `F[i][Y] / (Y ^ 3 - 5i)`: `5i` is not a cube.
  - `12 + i` generates the multiplicative group of `F[i]`.
  - QM31 has an element of order `2 ^ 33` whose square is the order-`2 ^ 32` generator of `F[i]`.

  Powers in `F[i]` reduce to powers in `F` through the norm `z ^ (p + 1)`.

  Everything is kernel-checked, without `native_decide`.
-/

open Polynomial

namespace Mersenne31

open Complex

/-! ## The cubic extension of `F` -/

theorem irreducible_ext3 : Irreducible (X ^ 3 - C (5 : Field)) :=
  X_pow_sub_C_irreducible_of_prime Nat.prime_three five_ne_cube

/-- `5 ^ ((p - 1) / 3)`, the value of `DTH_ROOT` for `X ^ 3 - 5`. -/
theorem five_pow_div_three : (5 : Field) ^ ((fieldSize - 1) / 3) = 1513477735 := by
  rw [show (5 : Field) = ((5 : ℕ) : Field) by norm_num,
    natCast_pow_eq 5 1513477735 (by decide) (by decide)]
  rfl

/-- `1513477735` is a primitive cube root of unity. -/
theorem dthRoot3_cube : (1513477735 : Field) ^ 3 = 1 ∧ (1513477735 : Field) ≠ 1 := by
  constructor <;> decide

theorem ext3Poly_monic : (X ^ 3 - C (5 : Field)).Monic := monic_X_pow_sub_C _ (by norm_num)

theorem mk_X_pow_three : AdjoinRoot.mk (X ^ 3 - C (5 : Field)) (X ^ 3) =
    AdjoinRoot.mk (X ^ 3 - C (5 : Field)) (CoeffList.toPoly [5]) := by
  rw [← sub_eq_zero, ← map_sub, show CoeffList.toPoly [(5 : Field)] = C 5 by simp [CoeffList.toPoly],
    AdjoinRoot.mk_self]

/-- `10 + X`, the value of `EXT_GENERATOR` for `X ^ 3 - 5`, has order `p ^ 3 - 1`.

The primes of `p ^ 3 - 1` are `2, 3, 7, 11, 31, 151, 331, 529510939, 2903110321`. -/
theorem orderOf_ext3Generator :
    orderOf (AdjoinRoot.mk (X ^ 3 - C (5 : Field)) (CoeffList.toPoly [10, 1, 0])) =
      fieldSize ^ 3 - 1 := by
  refine CoeffList.orderOf_mk_toPoly ext3Poly_monic (natDegree_X_pow_sub_C) (by norm_num)
    mk_X_pow_three _
    [(2, 1), (3, 3), (7, 1), (11, 1), (31, 1), (151, 1), (331, 1), (529510939, 1),
      (2903110321, 1)]
    ?_ (by unfold fieldSize; norm_num) (by unfold fieldSize; norm_num)
    (by unfold fieldSize; norm_num) (by decide +kernel) (by decide +kernel)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num

/-! ## Non-residues of `F[i]` -/

/-- `2 + i` is not a square: its norm `5` is not a square in `F`. -/
theorem mk_two_one_ne_sq (z : Complex) : z ^ 2 ≠ mk 2 1 := by
  obtain ⟨a, b, rfl⟩ := exists_mk z
  intro h
  rw [mk_sq] at h
  obtain ⟨h1, h2⟩ := mk_injective h
  apply five_ne_sq (a * a + b * b)
  linear_combination (a * a - b * b + 2) * h1 + (a * b + b * a + 1) * h2

/-- `5i` is not a cube: its norm `25` would be a cube, and so would `5 = 125 / 25`. -/
theorem mk_zero_five_ne_cube (z : Complex) : z ^ 3 ≠ mk 0 5 := by
  obtain ⟨a, b, rfl⟩ := exists_mk z
  intro h
  rw [pow_succ, mk_sq, mk_mul] at h
  obtain ⟨h1, h2⟩ := mk_injective h
  set n := a * a + b * b with hn
  have hn3 : n ^ 3 = 25 := by
    rw [hn]; linear_combination (a * (a * a - 3 * b * b)) * h1 + (5 + (3 * a * a * b - b * b * b)) * h2
  have hn0 : n ≠ 0 := by rintro h0; rw [h0] at hn3; revert hn3; decide
  apply five_ne_cube (5 / n)
  rw [div_pow, hn3, div_eq_iff (by decide)]; norm_num

/-! ## QM31 and the cubic extension of `F[i]` -/

theorem irreducible_qm31 : Irreducible (X ^ 2 - C (mk 2 1)) :=
  X_pow_sub_C_irreducible_of_prime Nat.prime_two mk_two_one_ne_sq

instance : Fact (Irreducible (X ^ 2 - C (mk 2 1))) := ⟨irreducible_qm31⟩

/-- QM31, `F[i][Y] / (Y ^ 2 - (2 + i))`, a field of order `p ^ 4`. -/
abbrev QM31 := AdjoinRoot (X ^ 2 - C (mk 2 1))

theorem irreducible_complexExt3 : Irreducible (X ^ 3 - C (mk 0 5)) :=
  X_pow_sub_C_irreducible_of_prime Nat.prime_three mk_zero_five_ne_cube

/-- The two-adicity of `p ^ 4 - 1`. -/
theorem qm31TwoAdicity_spec : 2 ^ 33 ∣ fieldSize ^ 4 - 1 ∧ ¬ 2 ^ 34 ∣ fieldSize ^ 4 - 1 := by
  unfold fieldSize; decide

/-- The two-adicity of `p ^ 6 - 1`. -/
theorem complexExt3TwoAdicity_spec : 2 ^ 32 ∣ fieldSize ^ 6 - 1 ∧ ¬ 2 ^ 33 ∣ fieldSize ^ 6 - 1 := by
  unfold fieldSize; decide

/-- The two-adicity of `p + 1`, the order of the circle group. -/
theorem circleTwoAdicity_spec : fieldSize + 1 = 2 ^ 31 := by
  unfold fieldSize; decide

/-! ## Powers through the norm -/

/-- For `e = (p + 1) · k`, a power of `a + b · i` is the power of its norm. -/
theorem mk_pow_norm (a b : Field) (k : ℕ) :
    mk a b ^ ((fieldSize + 1) * k) = AdjoinRoot.of complexPoly ((a * a + b * b) ^ k) := by
  rw [pow_mul, mk_pow_fieldSize_succ, map_pow]

/-- `(2 + i) ^ ((p ^ 2 - 1) / 2) = -1`, the value of `DTH_ROOT` for QM31. -/
theorem mk_two_one_pow_dth : mk 2 1 ^ ((fieldSize ^ 2 - 1) / 2) = -1 := by
  rw [show (fieldSize ^ 2 - 1) / 2 = (fieldSize + 1) * ((fieldSize - 1) / 2) by unfold fieldSize; norm_num,
    mk_pow_norm, show (2 : Field) * 2 + 1 * 1 = ((5 : ℕ) : Field) by norm_num,
    natCast_pow_eq 5 2147483646 (by decide) (by decide)]
  rw [show ((2147483646 : ℕ) : Field) = -1 by decide, map_neg, map_one]

/-- `(5i) ^ ((p ^ 2 - 1) / 3) = 634005911`, the value of `DTH_ROOT` for `Y ^ 3 - 5i`. -/
theorem mk_zero_five_pow_dth :
    mk 0 5 ^ ((fieldSize ^ 2 - 1) / 3) = AdjoinRoot.of complexPoly 634005911 := by
  rw [show (fieldSize ^ 2 - 1) / 3 = (fieldSize + 1) * ((fieldSize - 1) / 3) by unfold fieldSize; norm_num,
    mk_pow_norm, show (0 : Field) * 0 + 5 * 5 = ((25 : ℕ) : Field) by norm_num,
    natCast_pow_eq 25 634005911 (by decide) (by decide)]
  rfl

/-! ## A generator of `F[i]` -/

theorem prime_dvd_complex_card_sub_one {q : ℕ} (hq : q.Prime) (h : q ∣ fieldSize ^ 2 - 1) :
    q ∣ fieldSize - 1 := by
  rw [show fieldSize ^ 2 - 1 = (fieldSize - 1) * 2 ^ 31 by unfold fieldSize; norm_num] at h
  rcases (Nat.Prime.dvd_mul hq).mp h with h | h
  · exact h
  · rw [(Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp (hq.dvd_of_dvd_pow h)]; decide

/-- `12 + i`, the value of `COMPLEX_GENERATOR`, generates the multiplicative group of `F[i]`: its norm `145` generates that of `F`. -/
theorem orderOf_mk_twelve_one : orderOf (mk 12 1) = fieldSize ^ 2 - 1 := by
  have hnorm : (12 : Field) * 12 + 1 * 1 = ((145 : ℕ) : Field) := by norm_num
  have hof : Function.Injective (AdjoinRoot.of complexPoly) := (AdjoinRoot.of complexPoly).injective
  apply orderOf_eq_of_pow_and_pow_div_prime (by unfold fieldSize; norm_num)
  · rw [show fieldSize ^ 2 - 1 = (fieldSize + 1) * (fieldSize - 1) by unfold fieldSize; norm_num,
      mk_pow_norm, hnorm, ZMod.pow_card_sub_one_eq_one (by decide), map_one]
  · intro q hq hdvd
    have hq1 := prime_dvd_complex_card_sub_one hq hdvd
    rw [show (fieldSize ^ 2 - 1) / q = (fieldSize + 1) * ((fieldSize - 1) / q) by
      rw [show fieldSize ^ 2 - 1 = (fieldSize + 1) * (fieldSize - 1) by unfold fieldSize; norm_num,
        Nat.mul_div_assoc _ hq1], mk_pow_norm, hnorm, ← map_one (AdjoinRoot.of complexPoly)]
    intro h
    have h' := hof h
    revert h'
    have he : (fieldSize - 1) / q < 2 ^ 64 := lt_of_le_of_lt (Nat.div_le_self _ _) (by decide)
    refine natCast_pow_ne_one 145 he ?_
    rcases prime_dvd_fieldSize_sub_one hq hq1 with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-! ## The order-`2 ^ 33` element of QM31 -/

/-- The value of `complex_ext_two_adic_generator(33)`: `(1437746044 + 946469285 i) · Y`. -/
noncomputable def qm31TwoAdicGenerator : QM31 :=
  AdjoinRoot.of _ (mk 1437746044 946469285) * AdjoinRoot.root _

theorem qm31TwoAdicGenerator_sq :
    qm31TwoAdicGenerator ^ 2 =
      AdjoinRoot.of (X ^ 2 - C (mk 2 1)) twoAdicGenerators[complexTwoAdicity] := by
  have hr : AdjoinRoot.root (X ^ 2 - C (mk 2 1)) ^ 2 = AdjoinRoot.of _ (mk 2 1) := by
    have h := AdjoinRoot.eval₂_root (X ^ 2 - C (mk 2 1))
    simp only [eval₂_sub, eval₂_X_pow, eval₂_C] at h
    exact sub_eq_zero.mp h
  rw [qm31TwoAdicGenerator, mul_pow, hr, ← map_pow, ← map_mul, mk_sq, mk_mul]
  congr 1

/-- `qm31TwoAdicGenerator` has order `2 ^ 33`, the full two-adic part of `p ^ 4 - 1`. -/
theorem orderOf_qm31TwoAdicGenerator : orderOf qm31TwoAdicGenerator = 2 ^ 33 := by
  have hinj : Function.Injective (AdjoinRoot.of (X ^ 2 - C (mk 2 1))) :=
    AdjoinRoot.of.injective_of_degree_ne_zero (by rw [degree_X_pow_sub_C (by norm_num)]; decide)
  have h32 := orderOf_injective (AdjoinRoot.of (X ^ 2 - C (mk 2 1))).toMonoidHom hinj
    (twoAdicGenerators[complexTwoAdicity])
  simp only [RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe] at h32
  rw [twoAdicGenerators_order _ (by decide)] at h32
  exact orderOf_eq_two_pow_succ_of_sq (k := 31) qm31TwoAdicGenerator_sq h32

end Mersenne31
