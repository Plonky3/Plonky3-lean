module

public import Plonky3Lean.Proofs.Circle.Torsion

@[expose] public section

/-!
# p3-circle: the single-point selectors

The selector of Lemma 11 at a point P of the trace domain H is s_P = v_n / (v_0 . T_P^(-1)).

The crate evaluates it as v_n(Q) ((Q - P).x + 1) / (Q - P).y.

With D = Q - P and R = 2^(n-1) P, the doubling formulas turn it into a polynomial in D:

```text
    s_P(Q) = -R.y 2^(n-1) v_1(D) v_2(D) ... v_(n-1)(D) (D.x + 1)
```

On H this polynomial is zero except at P, where it is -2^n R.y, the value of Remark 16.

So the crate's first-row and last-row selectors are not 0/1 on the trace domain:

```text
    first row:   s_shift(shift)   = -2^n (2^(n-1) shift).y
    last row:    s_(-shift)(-shift) = 2^n (2^(n-1) shift).y = -s_shift(shift)
```

The transition selector 1 - s_(-shift) / s_(-shift)(-shift) is 1 off the last row and 0 on it.
-/

namespace Plonky3Lean.Proofs.Circle

open Plonky3Lean.Spec.Circle p3_dft.mirror Finset

set_option linter.unusedSectionVars false

variable {K : Type _} [Field K]

/-- The y-coordinate of 2^m D is D.y 2^m (D.x)(2 D).x ... (2^(m-1) D).x. -/
theorem two_pow_nsmul_y (D : C K) (m : ℕ) :
    (2 ^ m • D).y = D.y * 2 ^ m * ∏ k ∈ range m, (2 ^ k • D).x := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ, mul_nsmul, C.two_nsmul_y, ih, prod_range_succ, pow_succ]
    ring

/-- The selector of Lemma 11, as a polynomial in D = Q - P. -/
def selReg (n : ℕ) (P Q : C K) : K :=
  -(2 ^ (n - 1) • P).y * 2 ^ (n - 1) * (∏ k ∈ range (n - 1), (2 ^ k • (Q - P)).x) * ((Q - P).x + 1)

/-- When v_n(P) = 0, v_n(Q) = -R.y (2^(n-1) (Q - P)).y for R = 2^(n-1) P. -/
theorem vn_of_vn_zero {n : ℕ} {P : C K} (hP : vn n P = 0) (Q : C K) :
    vn n Q = -(2 ^ (n - 1) • P).y * (2 ^ (n - 1) • (Q - P)).y := by
  have hQ : Q = P + (Q - P) := by abel
  rw [vn] at hP ⊢
  conv_lhs => rw [hQ, smul_add, C.add_x, hP]
  ring

/-- Off the pole, the crate's quotient v_n(Q) ((Q - P).x + 1) / (Q - P).y is the selector polynomial. -/
theorem quotient_eq_selReg {n : ℕ} {P : C K} (hP : vn n P = 0) (Q : C K) (hy : (Q - P).y ≠ 0) :
    vn n Q * ((Q - P).x + 1) * ((Q - P).y)⁻¹ = selReg n P Q := by
  rw [vn_of_vn_zero hP, two_pow_nsmul_y (Q - P), selReg]
  field_simp

/-- The selector polynomial at P itself: -2^n (2^(n-1) P).y. -/
theorem selReg_self (n : ℕ) (hn : 1 ≤ n) (P : C K) : selReg n P P = -2 ^ n * (2 ^ (n - 1) • P).y := by
  simp only [selReg, sub_self, smul_zero, C.zero_x, prod_const_one, mul_one]
  rw [show (2 : K) ^ n = 2 ^ (n - 1) * 2 by rw [← pow_succ]; congr 1; omega]
  ring

/-- A point of order two of the circle is (-1, 0). -/
theorem eq_of_two_nsmul_eq_zero (h2 : (2 : K) ≠ 0) {D : C K} (hD : 2 • D = 0) (hne : D ≠ 0) :
    D.x + 1 = 0 := by
  have hx := congrArg C.x hD
  have hy := congrArg C.y hD
  rw [C.two_nsmul_x, C.zero_x] at hx
  rw [C.two_nsmul_y, C.zero_y] at hy
  have h1 : (D.x - 1) * (D.x + 1) = 0 := by
    have : 2 * ((D.x - 1) * (D.x + 1)) = 0 := by linear_combination hx
    exact (mul_eq_zero.mp this).resolve_left h2
  rcases mul_eq_zero.mp h1 with h | h
  · exfalso; apply hne
    have hDx : D.x = 1 := by linear_combination h
    have : D.y ^ 2 = 0 := by linear_combination D.eq - (D.x + 1) * h
    exact C.ext hDx (by simpa using pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this)
  · exact h


/-- For D nonzero with 2^n D = 0, a factor of the selector polynomial vanishes. -/
theorem selFactor_eq_zero (h2 : (2 : K) ≠ 0) {n : ℕ} {D : C K} (hD : 2 ^ n • D = 0) (hne : D ≠ 0) :
    (∏ k ∈ range (n - 1), (2 ^ k • D).x) * (D.x + 1) = 0 := by
  have hdvd : addOrderOf D ∣ 2 ^ n := addOrderOf_dvd_of_nsmul_eq_zero hD
  obtain ⟨j, hj, hjo⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  have hj0 : j ≠ 0 := by rintro rfl; exact hne (AddMonoid.addOrderOf_eq_one_iff.mp (by simpa using hjo))
  rcases Nat.lt_or_ge j 2 with h | h
  · have hj1 : j = 1 := by omega
    subst hj1
    rw [eq_of_two_nsmul_eq_zero h2 (by rw [← pow_one 2, ← hjo]; exact addOrderOf_nsmul_eq_zero D) hne,
      mul_zero]
  · apply mul_eq_zero_of_left
    apply prod_eq_zero (i := j - 2) (by simp; omega)
    set E := 2 ^ (j - 2) • D
    have h2E : 2 • (2 • E) = 0 := by
      rw [smul_smul, smul_smul, show 2 * 2 * 2 ^ (j - 2) = 2 ^ j by
        rw [← pow_two, ← pow_add]; congr 1; omega, ← hjo, addOrderOf_nsmul_eq_zero]
    have hE : 2 • E ≠ 0 := by
      rw [smul_smul, show 2 * 2 ^ (j - 2) = 2 ^ (j - 1) by rw [← pow_succ']; congr 1; omega]
      intro h0
      have := Nat.le_of_dvd (by positivity) (addOrderOf_dvd_of_nsmul_eq_zero h0)
      rw [hjo] at this
      exact absurd this (not_le.mpr (Nat.pow_lt_pow_right (by norm_num) (by omega)))
    have := eq_of_two_nsmul_eq_zero h2 h2E hE
    rw [C.two_nsmul_x] at this
    have : 2 * E.x ^ 2 = 0 := by linear_combination this
    exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp ((mul_eq_zero.mp this).resolve_left h2)

variable [DecidableEq K] {G : Gen (K × K)}

/-- An odd multiple of the generator Q of order 2^(n + 1), doubled n times, is the point (-1, 0). -/
theorem two_pow_nsmul_odd (hV : CircleGenValid G) {n : ℕ} (hG : n + 1 ≤ G.adicity) (a : ℕ) :
    2 ^ n • ((2 * a + 1) • genPt G (n + 1)) = genPt G 1 := by
  have h1 : 2 ^ n • genPt G (n + 1) = genPt G 1 := by
    rw [← genPt_nsmul hV (show 1 ≤ n + 1 by omega) hG]; congr 2
  have h0 : 2 • genPt G 1 = 0 := by
    rw [← genPt_zero hV, ← genPt_nsmul hV (show 0 ≤ 1 by omega) (by omega)]; rfl
  rw [smul_comm, h1, add_nsmul, one_nsmul, mul_nsmul, h0, smul_zero, zero_add]

/-- On the standard domain H of size 2^n, the selector polynomial of P is zero at every other point. -/
theorem selReg_on_domain (hV : CircleGenValid G) (h2 : (2 : K) ≠ 0) {n : ℕ}
    (hG : n + 1 ≤ G.adicity) (a b : ℕ)
    (hne : (2 * b + 1) • genPt G (n + 1) ≠ (2 * a + 1) • genPt G (n + 1)) :
    selReg n ((2 * a + 1) • genPt G (n + 1)) ((2 * b + 1) • genPt G (n + 1)) = 0 := by
  rw [selReg, mul_assoc, selFactor_eq_zero h2 _ (sub_ne_zero.mpr hne), mul_zero]
  rw [smul_sub, two_pow_nsmul_odd hV hG, two_pow_nsmul_odd hV hG, sub_self]

open p3_circle.point.mirror in
/-- s_p_at_p is the selector polynomial at its own point. -/
theorem s_p_at_p_eq_selReg (P : C K) {n : ℕ} (hn : 1 ≤ n) :
    Point.s_p_at_p (ofC P) n = some (selReg n P P) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  simp only [Point.s_p_at_p, ge_iff_le, hn, ↓reduceIte, v_n_prod_ofC, selReg_self _ hn,
    two_pow_nsmul_y, Nat.add_sub_cancel, ofC_y, Option.some.injEq]
  simp only [vn, Nat.add_sub_cancel]
  rw [show 2 * (m + 1) - 1 = (m + 1) + m by omega, pow_add]
  ring


/-- At a point Q of the line through P on the y-axis direction, (Q - P).y = 0, v_n takes the value it takes at P, when that value is zero. -/
theorem vn_eq_zero_of_y {n : ℕ} {P Q : C K} (hP : vn n P = 0) (hy : (Q - P).y = 0) : vn n Q = 0 := by
  rw [vn_of_vn_zero hP, two_pow_nsmul_y (Q - P), hy]; ring

theorem vn_neg (n : ℕ) (P : C K) : vn n (-P) = vn n P := by
  simp only [vn, smul_neg, C.neg_x]

open p3_circle.point.mirror p3_circle.domain.mirror p3_commit.domain.mirror in
/-- Off the trace domain, selectors_at_point returns the selector polynomials of the first and last points, the normalized transition selector, and 1 / v_n.

With S the shift and k = s_(-S)(-S):

```text
    is_first_row  = s_S(Q)
    is_last_row   = s_(-S)(Q)
    is_transition = 1 - s_(-S)(Q) / k
    inv_vanishing = 1 / v_n(Q)
```
-/
theorem selectors_at_point_eq (hV : CircleGenValid G) (h2 : (2 : K) ≠ 0) {n : ℕ} (hn : 1 ≤ n)
    (hG : n + 1 ≤ G.adicity) (t : K) (ht : 1 + t * t ≠ 0) (hz : vn n (stereo t ht) ≠ 0) :
    CircleDomain.selectors_at_point ⟨n, ofC (genPt G (n + 1))⟩ t = some
      ⟨selReg n (genPt G (n + 1)) (stereo t ht), selReg n (-genPt G (n + 1)) (stereo t ht),
        1 - selReg n (-genPt G (n + 1)) (stereo t ht) / selReg n (-genPt G (n + 1)) (-genPt G (n + 1)),
        (vn n (stereo t ht))⁻¹⟩ := by
  have hfrom : Point.from_projective_line t = some (ofC (stereo t ht)) := by
    rw [from_projective_line_eq]; simp [ht]
  rw [CircleDomain.selectors_at_point, hfrom]
  simp only [Option.bind_eq_bind, Option.bind_some]
  generalize stereo t ht = Q at hz ⊢
  set S := genPt G (n + 1)
  have hS : vn n S = 0 := vn_genPt_succ hV h2 hn hG
  have hnS : vn n (-S) = 0 := by rw [vn_neg, hS]
  have hd1 : (Q - S).y ≠ 0 := fun h => hz (vn_eq_zero_of_y hS h)
  have hd2 : (Q - -S).y ≠ 0 := fun h => hz (vn_eq_zero_of_y hnS h)
  have hk : selReg n (-S) (-S) ≠ 0 := by
    rw [selReg_self n hn, smul_neg, C.neg_y]
    have hR : (2 ^ (n - 1) • S).x = 0 := hS
    have hy : (2 ^ (n - 1) • S).y ≠ 0 := by
      intro h0; have := (2 ^ (n - 1) • S).eq; rw [hR, h0] at this; norm_num at this
    exact mul_ne_zero (neg_ne_zero.mpr (pow_ne_zero n h2)) (neg_ne_zero.mpr hy)
  simp only [neg_ofC, s_p_at_p_eq_selReg (-S) hn, Option.bind_some,
    vanishing_poly_eq n S Q hn, vD, hS, sub_zero, recip_v_tilde_p_num_den_ofC, batchInv]
  have hall : ∀ x ∈ [(Q - S).y, (Q - -S).y * selReg n (-S) (-S), vn n Q], x ≠ 0 := by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl
    exacts [hd1, mul_ne_zero hd2 hk, hz]
  rw [ite_eq_left hall]
  simp only [List.map_cons, List.map_nil, List.getD_cons_zero, List.getD_cons_succ,
    Option.bind_some, Option.some.injEq, LagrangeSelectors.mk.injEq]
  have e1 := quotient_eq_selReg hS Q hd1
  have e2 := quotient_eq_selReg hnS Q hd2
  refine ⟨e1, ?_, ?_, trivial⟩
  · rw [← e2]; field_simp
  · rw [← e2]; field_simp


open p3_circle.point.mirror p3_circle.domain.mirror p3_commit.domain.mirror in
/-- selectors_at_point panics on the trace domain itself, where v_n vanishes. -/
theorem selectors_at_point_none (hV : CircleGenValid G) (h2 : (2 : K) ≠ 0) {n : ℕ} (hn : 1 ≤ n)
    (hG : n + 1 ≤ G.adicity) (t : K) (ht : 1 + t * t ≠ 0) (hz : vn n (stereo t ht) = 0) :
    CircleDomain.selectors_at_point ⟨n, ofC (genPt G (n + 1))⟩ t = none := by
  have hfrom : Point.from_projective_line t = some (ofC (stereo t ht)) := by
    rw [from_projective_line_eq]; simp [ht]
  rw [CircleDomain.selectors_at_point, hfrom]
  simp only [Option.bind_eq_bind, Option.bind_some]
  generalize stereo t ht = Q at hz ⊢
  simp only [neg_ofC, s_p_at_p_eq_selReg _ hn, Option.bind_some, vanishing_poly_eq n _ Q hn, vD,
    vn_genPt_succ hV h2 hn hG, sub_zero, hz, batchInv, recip_v_tilde_p_num_den_ofC]
  simp

open p3_circle.point.mirror p3_circle.domain.mirror in
/-- selectors_at_point panics at the points t^2 = -1 of the line, which have no point on the circle. -/
theorem selectors_at_point_none_of_sq (n : ℕ) (S : C K) (t : K) (ht : 1 + t * t = 0) :
    CircleDomain.selectors_at_point ⟨n, ofC S⟩ t = none := by
  have hfrom : Point.from_projective_line t = none := by
    rw [from_projective_line_eq]; simp [ht]
  simp [CircleDomain.selectors_at_point, hfrom]

open p3_circle.point.mirror p3_circle.domain.mirror p3_commit.domain.mirror in
/-- On a domain whose points all lie off the trace domain, selectors_on_coset lists, at each point, the values of selectors_at_point. -/
theorem selectors_on_coset_eq (hV : CircleGenValid G) (h2 : (2 : K) ≠ 0) {n : ℕ} (hn : 1 ≤ n)
    (hG : n + 1 ≤ G.adicity) (coset : CircleDomain K) (pts : List (C K))
    (hpts : CircleDomain.points G coset = some (pts.map ofC)) (hoff : ∀ Q ∈ pts, vn n Q ≠ 0) :
    CircleDomain.selectors_on_coset G ⟨n, ofC (genPt G (n + 1))⟩ coset = some
      ⟨pts.map (selReg n (genPt G (n + 1))), pts.map (selReg n (-genPt G (n + 1))),
        pts.map fun Q => 1 - selReg n (-genPt G (n + 1)) Q /
          selReg n (-genPt G (n + 1)) (-genPt G (n + 1)),
        pts.map fun Q => (vn n Q)⁻¹⟩ := by
  set S := genPt G (n + 1)
  have hS : vn n S = 0 := vn_genPt_succ hV h2 hn hG
  have hnS : vn n (-S) = 0 := by rw [vn_neg, hS]
  have hk : selReg n (-S) (-S) ≠ 0 := by
    rw [selReg_self n hn, smul_neg, C.neg_y]
    have hR : (2 ^ (n - 1) • S).x = 0 := hS
    have hy : (2 ^ (n - 1) • S).y ≠ 0 := by
      intro h0; have := (2 ^ (n - 1) • S).eq; rw [hR, h0] at this; norm_num at this
    exact mul_ne_zero (neg_ne_zero.mpr (pow_ne_zero n h2)) (neg_ne_zero.mpr hy)
  have hd1 : ∀ Q ∈ pts, (Q - S).y ≠ 0 := fun Q hQ h => hoff Q hQ (vn_eq_zero_of_y hS h)
  have hd2 : ∀ Q ∈ pts, (Q - -S).y ≠ 0 := fun Q hQ h => hoff Q hQ (vn_eq_zero_of_y hnS h)
  have hz : (pts.map ofC).mapM (fun at_ => (Point.v_n at_ n).map (· - 0)) =
      some (pts.map fun Q => vn n Q) := by
    rw [List.mapM_map]
    exact mapM_eq_some_map _ _ _ fun Q _ => by simp [v_n_ofC, hn]
  have hb : ∀ l : List K, (∀ x ∈ l, x ≠ 0) → batchInv l = some (l.map (·⁻¹)) := fun l hl => by
    unfold batchInv; rw [ite_eq_left hl]
  simp only [CircleDomain.selectors_on_coset, hpts, Option.bind_eq_bind, Option.bind_some, neg_ofC,
    s_p_at_p_eq_selReg (-S) hn, v_n_ofC, hn, ↓reduceIte, hS]
  rw [hz]
  simp only [Option.bind_some, List.map_map, Function.comp_def, recip_v_tilde_p_num_den_ofC]
  rw [hb _ (by simpa using hoff), hb _ (by simpa using hd1),
    hb _ (by simpa using fun Q hQ => mul_ne_zero (hd2 Q hQ) hk)]
  simp only [Option.bind_some, Option.some.injEq, LagrangeSelectors.mk.injEq, List.length_map]
  refine ⟨?_, ?_, ?_, by simp [Function.comp_def]⟩ <;>
  · apply List.ext_getElem (by simp)
    intro i h1 h2'
    simp only [List.length_map, List.length_range] at h1
    simp only [List.getElem_map, List.getElem_range, List.getD_eq_getElem?_getD,
      List.getElem?_map, List.getElem?_eq_getElem h1, Option.map_some, Option.getD_some,
      recip_v_tilde_p_num_den_ofC]
    have hQ := List.getElem_mem h1
    have e1 := quotient_eq_selReg hS _ (hd1 _ hQ)
    have e2 := quotient_eq_selReg hnS _ (hd2 _ hQ)
    first
      | exact e1
      | (rw [← e2]; field_simp)

/-! ## Mersenne31: the values on the trace domain -/

/-- The point of order 4 in Mersenne31's table is (0, -1). -/
theorem m31_genPt_two : genPt m31CircleGen 2 = C.mk 0 (-1) (by norm_num) := by
  rw [genPt, toC_of_on (m31CircleGen_on 2 (by decide))]
  refine C.ext ?_ ?_ <;> simp only [C.mk_x, C.mk_y, m31CircleGen_gen 2 (by decide)] <;> decide

/-- On the Mersenne31 trace domain of size 2^n, the first-row selector is 2^n at the first row. -/
theorem m31_first_row_value {n : ℕ} (hn : 1 ≤ n) (hG : n + 1 ≤ 31) :
    selReg n (genPt m31CircleGen (n + 1)) (genPt m31CircleGen (n + 1)) = 2 ^ n := by
  rw [selReg_self n hn, show n - 1 = n + 1 - 2 by omega,
    genPt_nsmul m31CircleGen_valid (by omega) hG, m31_genPt_two, C.mk_y]
  ring

/-- On the Mersenne31 trace domain of size 2^n, the last-row selector is -2^n at the last row. -/
theorem m31_last_row_value {n : ℕ} (hn : 1 ≤ n) (hG : n + 1 ≤ 31) :
    selReg n (-genPt m31CircleGen (n + 1)) (-genPt m31CircleGen (n + 1)) = -2 ^ n := by
  rw [selReg_self n hn, smul_neg, C.neg_y, show n - 1 = n + 1 - 2 by omega,
    genPt_nsmul m31CircleGen_valid (by omega) hG, m31_genPt_two, C.mk_y]
  ring

end Plonky3Lean.Proofs.Circle
