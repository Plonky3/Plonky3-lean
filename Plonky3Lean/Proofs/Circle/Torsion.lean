module

public import Plonky3Lean.Proofs.Circle.Domain
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

@[expose] public section

/-!
# p3-circle: torsion points, and where the vanishing polynomial vanishes

Over any field K with 2 nonzero, the circle embeds in the multiplicative group of the algebraic closure, by (x, y) -> x + i y.

So it has at most m points P with m P = 0.

A point of order m therefore generates all of them.

Consequence: the vanishing polynomial of a standard domain vanishes exactly on the domain, at every point of the circle over K, the extensions included.

This is the property Lemma 4 states for the base field.
-/

namespace Plonky3Lean.Proofs.Circle

open Plonky3Lean.Spec.Circle p3_dft.mirror

set_option linter.unusedSectionVars false

variable {K : Type _} [Field K]

/-- A square root of -1 in the algebraic closure. -/
noncomputable def iC (K : Type _) [Field K] : AlgebraicClosure K :=
  (IsAlgClosed.exists_pow_nat_eq (-1 : AlgebraicClosure K) (by norm_num : 0 < 2)).choose

theorem iC_sq : iC K ^ 2 = -1 :=
  (IsAlgClosed.exists_pow_nat_eq (-1 : AlgebraicClosure K) (by norm_num : 0 < 2)).choose_spec

/-- The embedding (x, y) -> x + i y of the circle into the algebraic closure. -/
noncomputable def psi (P : C K) : AlgebraicClosure K :=
  algebraMap K _ P.x + iC K * algebraMap K _ P.y

theorem psi_add (P Q : C K) : psi (P + Q) = psi P * psi Q := by
  simp only [psi, C.add_x, C.add_y, map_sub, map_add, map_mul]
  linear_combination -(algebraMap K _ P.y * algebraMap K _ Q.y) * iC_sq (K := K)

theorem psi_zero : psi (0 : C K) = 1 := by simp [psi]

theorem psi_nsmul (P : C K) (m : ℕ) : psi (m • P) = psi P ^ m := by
  induction m with
  | zero => simp [psi_zero]
  | succ m ih => rw [succ_nsmul, psi_add, ih, pow_succ]

theorem psi_mul_psi_neg (P : C K) : psi P * psi (-P) = 1 := by
  rw [← psi_add, add_neg_cancel, psi_zero]

theorem psi_injective (h2 : (2 : K) ≠ 0) : Function.Injective (psi : C K → AlgebraicClosure K) := by
  intro P Q h
  have hn : psi (-P) = psi (-Q) := by
    have h1 := psi_mul_psi_neg P
    have h2' := psi_mul_psi_neg Q
    rw [h] at h1
    exact (mul_left_cancel₀ (left_ne_zero_of_mul_eq_one h2') (h1.trans h2'.symm))
  have hx : algebraMap K (AlgebraicClosure K) (2 * P.x) = algebraMap K _ (2 * Q.x) := by
    have := congrArg₂ (· + ·) h hn
    simp only [psi, C.neg_x, C.neg_y, map_neg] at this
    simp only [map_mul, map_ofNat]
    linear_combination this
  have hi : iC K ≠ 0 := fun h0 => by have := iC_sq (K := K); rw [h0] at this; norm_num at this
  have hy : algebraMap K (AlgebraicClosure K) (2 * P.y) = algebraMap K _ (2 * Q.y) := by
    have := congrArg₂ (· - ·) h hn
    simp only [psi, C.neg_x, C.neg_y, map_neg] at this
    simp only [map_mul, map_ofNat]
    apply mul_left_cancel₀ hi
    linear_combination this
  have hx' := (mul_right_inj' h2).mp ((algebraMap K _).injective hx)
  have hy' := (mul_right_inj' h2).mp ((algebraMap K _).injective hy)
  exact C.ext hx' hy'

/-- At most m points of the circle satisfy m P = 0. -/
theorem card_torsion_le (h2 : (2 : K) ≠ 0) {m : ℕ} (hm : 0 < m) (T : Finset (C K))
    (hT : ∀ P ∈ T, m • P = 0) : T.card ≤ m := by
  classical
  have hsub : T.image psi ⊆ (Polynomial.nthRoots m (1 : AlgebraicClosure K)).toFinset := by
    intro z hz
    obtain ⟨P, hP, rfl⟩ := Finset.mem_image.mp hz
    rw [Multiset.mem_toFinset, Polynomial.mem_nthRoots hm, ← psi_nsmul, hT P hP, psi_zero]
  calc T.card = (T.image psi).card := (Finset.card_image_of_injective _ (psi_injective h2)).symm
    _ ≤ _ := Finset.card_le_card hsub
    _ ≤ _ := Multiset.toFinset_card_le _
    _ ≤ m := Polynomial.card_nthRoots _ _

/-- A point of order m generates every point P with m P = 0. -/
theorem torsion_mem (h2 : (2 : K) ≠ 0) {g : C K} {m : ℕ} (hg : addOrderOf g = m) (hm : 0 < m)
    (P : C K) (hP : m • P = 0) : ∃ i < m, P = i • g := by
  classical
  by_contra hne
  simp only [not_exists, not_and] at hne
  let T := insert P ((Finset.range m).image fun i => i • g)
  have hinj : Set.InjOn (fun i => i • g) (Finset.range m : Set ℕ) := by
    intro i hi j hj h
    simp only [Finset.coe_range, Set.mem_Iio] at hi hj
    exact nsmul_injOn_Iio_addOrderOf (by rwa [hg]) (by rwa [hg]) h
  have hcard : T.card = m + 1 := by
    rw [Finset.card_insert_of_notMem, Finset.card_image_of_injOn hinj, Finset.card_range]
    simp only [Finset.mem_image, Finset.mem_range, not_exists, not_and]
    exact fun i hi h => hne i hi h.symm
  have := card_torsion_le h2 hm T (by
    intro Q hQ
    rcases Finset.mem_insert.mp hQ with rfl | hQ
    · exact hP
    · obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hQ
      rw [smul_comm, ← hg, addOrderOf_nsmul_eq_zero, smul_zero])
  omega

variable [DecidableEq K] {G : Gen (K × K)}

/-- The vanishing polynomial of a standard domain is v_n itself: v_n(Q) = 0 for its shift Q. -/
theorem vn_genPt_succ (hV : CircleGenValid G) (h2 : (2 : K) ≠ 0) {n : ℕ} (hn : 1 ≤ n)
    (hG : n + 1 ≤ G.adicity) : vn n (genPt G (n + 1)) = 0 := by
  have h4 : 2 • genPt G 2 = genPt G 1 := by
    rw [← genPt_nsmul hV (show 1 ≤ 2 by omega) (by omega)]; rfl
  have hx := congrArg C.x h4
  rw [C.two_nsmul_x] at hx
  have h1 : (genPt G 1).x = -1 := by
    rw [genPt, toC_of_on (hV.on_circle 1 (by omega)), C.mk_x, hV.gen_one (by omega)]
  rw [vn, show n - 1 = n + 1 - 2 by omega, genPt_nsmul hV (by omega) hG]
  rw [h1] at hx
  have : 2 * (genPt G 2).x ^ 2 = 0 := by linear_combination hx
  exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp ((mul_eq_zero.mp this).resolve_left h2)

/-- Over any field with 2 nonzero, v_n vanishes at a point of the circle exactly when the point is in the standard domain of size 2^n. -/
theorem vn_eq_zero_iff (hV : CircleGenValid G) (h2 : (2 : K) ≠ 0) {n : ℕ} (hn : 1 ≤ n)
    (hG : n + 1 ≤ G.adicity) (P : C K) :
    vn n P = 0 ↔ ∃ j, P = (2 * j + 1) • genPt G (n + 1) := by
  constructor
  · intro hP
    set R := 2 ^ (n - 1) • P with hR
    have h2R : 2 • R = genPt G 1 := by
      rw [genPt, toC_of_on (hV.on_circle 1 (by omega))]
      refine C.ext ?_ ?_
      · rw [C.two_nsmul_x, C.mk_x, hV.gen_one (by omega), show R.x = 0 from hP]; ring
      · rw [C.two_nsmul_y, C.mk_y, hV.gen_one (by omega), show R.x = 0 from hP]; ring
    have hQ : 2 ^ n • genPt G (n + 1) = genPt G 1 := by
      rw [← genPt_nsmul hV (show 1 ≤ n + 1 by omega) hG]; congr 2
    have htor : 2 ^ n • (P - genPt G (n + 1)) = 0 := by
      rw [smul_sub, hQ, ← h2R, hR, smul_smul, ← pow_succ', show n - 1 + 1 = n by omega, sub_self]
    have hord : addOrderOf (genPt G n) = 2 ^ n := addOrderOf_genPt hV h2 (by omega)
    obtain ⟨i, -, hi⟩ := torsion_mem h2 hord (by positivity) _ htor
    refine ⟨i, ?_⟩
    have hg : genPt G n = 2 • genPt G (n + 1) := by
      rw [← genPt_nsmul hV (show n ≤ n + 1 by omega) hG, Nat.add_sub_cancel_left, pow_one]
    rw [hg, smul_smul] at hi
    rw [sub_eq_iff_eq_add] at hi
    rw [hi, ← succ_nsmul, mul_comm]
  · rintro ⟨j, rfl⟩
    have := vD_twinPoint hV (n := n) (by omega) (genPt G (n + 1)) j
    rw [twinPoint_standard hV hn hG, vD, sub_eq_zero, vn_genPt_succ hV h2 hn hG] at this
    exact this

end Plonky3Lean.Proofs.Circle
