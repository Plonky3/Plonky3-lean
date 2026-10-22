/-
Copyright (c) 2026 CompPoly. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Coratger
-/
import CompPoly.Fields.KoalaBear
import CompPoly.Fields.PrattCertificate
import Mathlib.Tactic.NormNum.Prime
import ToCompPoly.ToMathlib.Polynomial.CoeffList
import ToCompPoly.ToMathlib.Polynomial.IrreducibleOfOrder

/-!
  # KoalaBear: the quintic extension `F[X] / (X ^ 5 + X ^ 2 - 1)`

  - `ofQuinticCoeffs cs` is the element `Σ j, cs[j] · X ^ j`, with `X ^ 5 = 1 - X ^ 2`.
  - `X + 2` has order `p ^ 5 - 1`, checked from the factorisation of `p ^ 5 - 1`.
  - So `X ^ 5 + X ^ 2 - 1` is irreducible, and `X + 2` generates the multiplicative group.
  - `quinticFrobeniusCoeffs[k]` are the coefficients of `X ^ ((k + 1) · p)`.

  Every power is computed on coefficient lists by the kernel, without `native_decide`.
-/

open Polynomial

namespace KoalaBear

/-- The trinomial `X ^ 5 + X ^ 2 - 1`. -/
noncomputable def quinticPoly : Polynomial Field := X ^ 5 + X ^ 2 - 1

/-- `X ^ 5` modulo the trinomial, as low coefficients: `1 - X ^ 2`. -/
def quinticReduction : List Field := [1, 0, -1]

theorem quinticPoly_eq : quinticPoly = X ^ 5 - CoeffList.toPoly quinticReduction := by
  simp [quinticPoly, quinticReduction]
  ring

theorem degree_quinticReduction_lt : (CoeffList.toPoly quinticReduction).degree < 5 :=
  lt_of_lt_of_le (CoeffList.degree_toPoly_lt _) (by norm_num [quinticReduction])

theorem quinticPoly_monic : quinticPoly.Monic := by
  rw [quinticPoly_eq]
  exact monic_X_pow_sub (by exact_mod_cast degree_quinticReduction_lt)

theorem quinticPoly_natDegree : quinticPoly.natDegree = 5 := by
  rw [quinticPoly_eq]
  refine natDegree_eq_of_degree_eq_some ?_
  rw [degree_sub_eq_left_of_degree_lt] <;> rw [degree_X_pow]
  all_goals first | rfl | exact_mod_cast degree_quinticReduction_lt

theorem mk_X_pow_five :
    AdjoinRoot.mk quinticPoly (X ^ 5) = AdjoinRoot.mk quinticPoly (CoeffList.toPoly quinticReduction) := by
  rw [← sub_eq_zero, ← map_sub, ← quinticPoly_eq, AdjoinRoot.mk_self]

/-- The element `Σ j, cs[j] · X ^ j` of `F[X] / (X ^ 5 + X ^ 2 - 1)`. -/
noncomputable def ofQuinticCoeffs (cs : List Field) : AdjoinRoot quinticPoly :=
  AdjoinRoot.mk _ (CoeffList.toPoly cs)

/-- The coefficients of the multiplicative generator: `X + 2`. -/
def quinticGeneratorCoeffs : List Field := [2, 1, 0, 0, 0]

/-- `X + 2` has order `p ^ 5 - 1`.

The primes of `p ^ 5 - 1` are `2, 11, 71, 127, 181, 344859791, 38435241482589294665521`. -/
theorem orderOf_quinticGenerator :
    orderOf (ofQuinticCoeffs quinticGeneratorCoeffs) = fieldSize ^ 5 - 1 := by
  refine CoeffList.orderOf_mk_toPoly quinticPoly_monic quinticPoly_natDegree (by norm_num)
    mk_X_pow_five _
    [(2, 24), (11, 2), (71, 1), (127, 1), (181, 1), (344859791, 1),
      (38435241482589294665521, 1)]
    ?_ (by unfold fieldSize; norm_num) (by unfold fieldSize; norm_num)
    (by unfold fieldSize; norm_num) (by decide +kernel) (by decide +kernel)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  iterate 6 (on_goal 1 => norm_num)
  pratt

/-- `X ^ 5 + X ^ 2 - 1` is irreducible, since `F[X] / (X ^ 5 + X ^ 2 - 1)` has an element of order `p ^ 5 - 1`. -/
theorem irreducible_quinticPoly : Irreducible quinticPoly := by
  refine irreducible_of_orderOf quinticPoly_monic (by rw [quinticPoly_natDegree]; norm_num)
    (g := ofQuinticCoeffs quinticGeneratorCoeffs) ?_
  rw [orderOf_quinticGenerator, ZMod.card, quinticPoly_natDegree]

instance : Fact (Irreducible quinticPoly) := ⟨irreducible_quinticPoly⟩

/-- The quintic extension, a field of order `p ^ 5`. -/
abbrev Ext5 := AdjoinRoot quinticPoly

/-- The coefficients of `X ^ ((k + 1) · p)`, for `k = 0, 1, 2, 3`. -/
def quinticFrobeniusCoeffs : List (List Field) :=
  [[1576402667, 1173144480, 1567662457, 1206866823, 2428146],
    [1680345488, 1381986, 615237464, 1380104858, 295431824],
    [441230756, 323126830, 704986542, 1445620072, 503505220],
    [1364444097, 1144738982, 2008416047, 143367062, 1027410849]]

/-- Entry `k` of `quinticFrobeniusCoeffs` is `X ^ ((k + 1) · p)`, the image of `X ^ (k + 1)` under Frobenius. -/
theorem quinticFrobeniusCoeffs_spec :
    ∀ k (h : k < quinticFrobeniusCoeffs.length),
      ofQuinticCoeffs quinticFrobeniusCoeffs[k] = AdjoinRoot.root quinticPoly ^ ((k + 1) * fieldSize) := by
  have hroot : AdjoinRoot.root quinticPoly = AdjoinRoot.mk quinticPoly (CoeffList.toPoly [0, 1]) := by
    simp [AdjoinRoot.mk_X]
  have key : ∀ k < 4, (∀ i < 5, (CoeffList.powMod 5 quinticReduction [0, 1] ((k + 1) * fieldSize)).getD i 0 =
      (quinticFrobeniusCoeffs.getD k []).getD i 0) ∧
      (CoeffList.powMod 5 quinticReduction [0, 1] ((k + 1) * fieldSize)).length ≤ 5 := by
    unfold fieldSize; decide +kernel
  intro k hk
  have hk4 : k < 4 := hk
  obtain ⟨hc, hl⟩ := key k hk4
  rw [hroot, ← CoeffList.mk_toPoly_powMod mk_X_pow_five _ _ (by unfold fieldSize; omega),
    ofQuinticCoeffs]
  congr 1
  refine CoeffList.toPoly_eq_of_getD 5 ?_ hl ?_
  · interval_cases k <;> simp [quinticFrobeniusCoeffs]
  · intro i hi
    rw [hc i hi]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk, Option.getD_some]

end KoalaBear
