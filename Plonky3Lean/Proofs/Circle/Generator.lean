module

public import Plonky3Lean.Proofs.Circle.Point
public import Plonky3Lean.Proofs.Field.Mersenne31.Constants
public import Mathlib.Algebra.Polynomial.Roots

@[expose] public section

/-!
# p3-circle: the circle generators

The crate takes its subgroup generators from a table of points.

Entry k must lie on the circle, and entry k + 1 must square to entry k.

Then entry k has order exactly 2^k, in any field where 2 is not zero.

Mersenne31's table satisfies this up to k = 31, where 2^31 = p + 1 is the order of the whole circle group.
-/

namespace Plonky3Lean.Proofs.Circle

open Plonky3Lean.Spec.Circle p3_circle.point.mirror p3_dft.mirror

set_option linter.unusedSectionVars false

variable {K : Type _} [Field K] [DecidableEq K]

/-- The point of the circle with coordinates q, and the neutral element when q is off the circle. -/
noncomputable def toC (q : K × K) : C K := if h : q.1 ^ 2 + q.2 ^ 2 = 1 then C.mk q.1 q.2 h else 0

theorem toC_of_on {q : K × K} (h : q.1 ^ 2 + q.2 ^ 2 = 1) : toC q = C.mk q.1 q.2 h := by
  simp [toC, h]

/-- What the crate relies on about its table of circle generators. -/
structure CircleGenValid (G : Gen (K × K)) : Prop where
  on_circle : ∀ k ≤ G.adicity, (G.gen k).1 ^ 2 + (G.gen k).2 ^ 2 = 1
  gen_zero : G.gen 0 = (1, 0)
  gen_one : 1 ≤ G.adicity → G.gen 1 = (-1, 0)
  nested : ∀ k < G.adicity, 2 • toC (G.gen (k + 1)) = toC (G.gen k)

/-- Entry k of the table, as a point of the circle. -/
noncomputable def genPt (G : Gen (K × K)) (k : ℕ) : C K := toC (G.gen k)

variable {G : Gen (K × K)}

theorem ofC_genPt (hV : CircleGenValid G) {k : ℕ} (hk : k ≤ G.adicity) :
    ofC (genPt G k) = Point.new (G.gen k).1 (G.gen k).2 := by
  rw [genPt, toC_of_on (hV.on_circle k hk)]; rfl

/-- The generator of order 2^log_n is entry log_n of the table, and panics past its adicity. -/
theorem generator_eq (hV : CircleGenValid G) (k : ℕ) :
    Point.generator G k = if k ≤ G.adicity then some (ofC (genPt G k)) else none := by
  unfold Point.generator Gen.get
  split_ifs with hk
  · rw [ofC_genPt hV hk]; rfl
  · rfl

theorem genPt_zero (hV : CircleGenValid G) : genPt G 0 = 0 := by
  rw [genPt, toC_of_on (hV.on_circle 0 (Nat.zero_le _))]
  ext <;> simp [C.x, C.y, hV.gen_zero] <;> rfl

/-- Doubling entry k, k - j times, gives entry j. -/
theorem genPt_nsmul (hV : CircleGenValid G) {j k : ℕ} (hjk : j ≤ k) (hk : k ≤ G.adicity) :
    2 ^ (k - j) • genPt G k = genPt G j := by
  induction k, hjk using Nat.le_induction with
  | base => simp
  | succ k hjk ih =>
    rw [show k + 1 - j = (k - j) + 1 by omega, pow_succ, mul_comm, mul_nsmul, genPt,
      hV.nested k (by omega), ← genPt, ih (by omega)]

/-- Entry k has order exactly 2^k, in a field where 2 is not zero. -/
theorem addOrderOf_genPt (hV : CircleGenValid G) (h2 : (2 : K) ≠ 0) {k : ℕ}
    (hk : k ≤ G.adicity) : addOrderOf (genPt G k) = 2 ^ k := by
  rcases k with _ | k
  · rw [genPt_zero hV, addOrderOf_zero, pow_zero]
  · have h1 : genPt G 1 ≠ 0 := by
      rw [genPt, toC_of_on (hV.on_circle 1 (by omega))]
      intro h
      have := congrArg C.x h
      simp only [C.x, hV.gen_one (by omega)] at this
      change (-1 : K) = 1 at this
      exact h2 (by linear_combination -this)
    have := Fact.mk Nat.prime_two
    have e1 := genPt_nsmul hV (j := 1) (k := k + 1) (by omega) hk
    have e0 := genPt_nsmul hV (j := 0) (k := k + 1) (by omega) hk
    rw [Nat.add_sub_cancel] at e1
    rw [Nat.sub_zero, genPt_zero hV] at e0
    exact addOrderOf_eq_prime_pow (by rw [e1]; exact h1) e0

/-! ## Mersenne31 -/

/-- Mersenne31's table of circle generators: entry k is the coordinate pair of an element of order 2^k of F[i]. -/
def m31CircleGen : Gen (Mersenne31.Field × Mersenne31.Field) :=
  ⟨31, fun k => Mersenne31.twoAdicGeneratorCoeffs.getD k (0, 0)⟩

theorem m31CircleGen_gen (k : ℕ) (hk : k < 33) :
    m31CircleGen.gen k = Mersenne31.twoAdicGeneratorCoeffs[k]'(by
      rw [Plonky3Lean.Proofs.P3Mersenne31.coeffs_length]; exact hk) := by
  simp only [m31CircleGen, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by
    rw [Plonky3Lean.Proofs.P3Mersenne31.coeffs_length]; exact hk), Option.getD_some]

theorem m31CircleGen_on (k : ℕ) (hk : k ≤ 31) :
    (m31CircleGen.gen k).1 ^ 2 + (m31CircleGen.gen k).2 ^ 2 = 1 := by
  have hk' : k < (Mersenne31.twoAdicGeneratorCoeffs.take 32).length := by
    rw [List.length_take, Plonky3Lean.Proofs.P3Mersenne31.coeffs_length]; omega
  have h := Mersenne31.twoAdicGeneratorCoeffs_norm _ (List.getElem_mem hk')
  simp only [List.getElem_take] at h
  rw [m31CircleGen_gen k (by omega)]
  simpa [sq] using h

theorem m31CircleGen_valid : CircleGenValid m31CircleGen where
  on_circle := m31CircleGen_on
  gen_zero := rfl
  gen_one _ := by simp [m31CircleGen, Mersenne31.twoAdicGeneratorCoeffs]; rfl
  nested k hk := by
    change k < 31 at hk
    have h := Mersenne31.twoAdicGeneratorCoeffs_chain_eq
    simp only [Mersenne31.twoAdicGeneratorCoeffs_chain, List.all_eq_true, Bool.and_eq_true,
      decide_eq_true_eq] at h
    have hk' : k < (Mersenne31.twoAdicGeneratorCoeffs.zip Mersenne31.twoAdicGeneratorCoeffs.tail).length := by
      simp [Mersenne31.twoAdicGeneratorCoeffs]; omega
    obtain ⟨h1, h2⟩ := h _ (List.getElem_mem hk')
    simp only [List.getElem_zip, List.getElem_tail] at h1 h2
    rw [toC_of_on (m31CircleGen_on (k + 1) hk), toC_of_on (m31CircleGen_on k hk.le)]
    rw [two_nsmul]
    refine C.ext ?_ ?_
    · rw [C.add_x]
      simp only [C.mk_x, C.mk_y, m31CircleGen_gen (k + 1) (by omega), m31CircleGen_gen k (by omega)]
      exact h1
    · rw [C.add_y]
      simp only [C.mk_x, C.mk_y, m31CircleGen_gen (k + 1) (by omega), m31CircleGen_gen k (by omega)]
      exact h2

/-! ## The circle group of Mersenne31 has order p + 1 = 2^31 -/

noncomputable instance : Fintype (C Mersenne31.Field) := by
  unfold C; classical exact inferInstance

/-- The map (x, y) -> x + i y, a group embedding of the circle into F[i]. -/
noncomputable def toComplexC (P : C Mersenne31.Field) : Mersenne31.Complex :=
  Mersenne31.Complex.mk P.x P.y

theorem toComplexC_injective : Function.Injective toComplexC := by
  intro P Q h
  obtain ⟨hx, hy⟩ := Mersenne31.Complex.mk_injective h
  exact C.ext hx hy

theorem toComplexC_add (P Q : C Mersenne31.Field) :
    toComplexC (P + Q) = toComplexC P * toComplexC Q := by
  rw [toComplexC, toComplexC, toComplexC, Mersenne31.Complex.mk_mul]; rfl

/-- Every point of the circle has norm one: (x + i y)^(p + 1) = x^2 + y^2 = 1. -/
theorem toComplexC_pow (P : C Mersenne31.Field) :
    toComplexC P ^ (Mersenne31.fieldSize + 1) = 1 := by
  rw [toComplexC, Mersenne31.Complex.mk_pow_fieldSize_succ, show P.x * P.x + P.y * P.y = 1 by
    linear_combination P.eq, map_one]

theorem card_le : Fintype.card (C Mersenne31.Field) ≤ 2 ^ 31 := by
  classical
  let S := (Polynomial.nthRoots (Mersenne31.fieldSize + 1) (1 : Mersenne31.Complex)).toFinset
  have hmem : ∀ P, toComplexC P ∈ S := fun P => by
    simp only [S, Multiset.mem_toFinset]
    rw [Polynomial.mem_nthRoots (by omega)]
    exact toComplexC_pow P
  calc Fintype.card (C Mersenne31.Field) ≤ Fintype.card S :=
        Fintype.card_le_of_injective (fun P => ⟨toComplexC P, hmem P⟩)
          (fun P Q h => toComplexC_injective (congrArg Subtype.val h))
    _ = S.card := Fintype.card_coe S
    _ ≤ (Polynomial.nthRoots (Mersenne31.fieldSize + 1) (1 : Mersenne31.Complex)).card :=
        Multiset.toFinset_card_le _
    _ ≤ Mersenne31.fieldSize + 1 := Polynomial.card_nthRoots _ _
    _ = 2 ^ 31 := Mersenne31.circleTwoAdicity_spec

/-- The circle group of Mersenne31 has exactly p + 1 = 2^31 points. -/
theorem card_circle : Fintype.card (C Mersenne31.Field) = 2 ^ 31 := by
  refine le_antisymm card_le ?_
  have h := addOrderOf_genPt m31CircleGen_valid (by decide) (k := 31) le_rfl
  rw [← h]
  exact addOrderOf_le_card_univ

/-- Every point of the Mersenne31 circle is a multiple of entry 31: the group is cyclic of order 2^31. -/
theorem m31_zmultiples_eq_top :
    AddSubgroup.zmultiples (genPt m31CircleGen 31) = ⊤ := by
  apply AddSubgroup.eq_top_of_card_eq
  rw [Nat.card_zmultiples, addOrderOf_genPt m31CircleGen_valid (by decide) (k := 31) le_rfl, Nat.card_eq_fintype_card,
    card_circle]

/-- No point of the Mersenne31 circle has order 2^32: every order divides 2^31. -/
theorem m31_addOrderOf_dvd (P : C Mersenne31.Field) : addOrderOf P ∣ 2 ^ 31 := by
  rw [← card_circle]; exact addOrderOf_dvd_card

open Aeneas Aeneas.Std p3_mersenne_31 Plonky3Lean.Spec.Mersenne31 Plonky3Lean.Proofs.P3Mersenne31 in
/-- The Rust circle generator of order 2^bits is entry bits of the table, and panics past 31. -/
theorem circle_two_adic_generator_eq (bits : Std.Usize) :
    complex.Mersenne31.circle_two_adic_generator bits ⦃ c => bits.val ≤ 31 ∧
      toComplex c = Mersenne31.Complex.mk (m31CircleGen.gen bits.val).1 (m31CircleGen.gen bits.val).2 ⦄ ∨
    (31 < bits.val ∧ complex.Mersenne31.circle_two_adic_generator bits = .fail .panic) := by
  unfold complex.Mersenne31.circle_two_adic_generator
  rw [CIRCLE_TWO_ADIC_GENERATORS.eq]
  by_cases h : bits.val ≤ 31
  · left
    have hb : bits ≤ 31#usize := by scalar_tac
    simp only [hb, massert, ite_true, bind_ok]
    step*
    refine ⟨h, ?_⟩
    have hk' : bits.val < (Mersenne31.twoAdicGeneratorCoeffs.take 32).length := by
      rw [List.length_take, coeffs_length]; omega
    rw [c_post1, toComplex_of_vals circleTable _ circleTable_vals bits.val (by scalar_tac) hk',
      m31CircleGen_gen _ (by omega)]
    simp
  · right
    refine ⟨by omega, ?_⟩
    have hb : ¬ bits ≤ 31#usize := by scalar_tac
    simp [hb, massert]

end Plonky3Lean.Proofs.Circle
