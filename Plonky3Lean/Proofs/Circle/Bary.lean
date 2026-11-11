module

public import Plonky3Lean.Proofs.Circle.Poly
public import P3Circle.Prover

@[expose] public section

/-!
# p3-circle: barycentric evaluation on a twin coset

Take a twin coset D of size N = 2^(m+1), and a function f of the FFT space:

```text
    f(x, y) = p(x) + y q(x),     deg p < N / 2,  deg q < N / 2
```

The crate evaluates f at a point Z off D as

```text
    f(Z) = v_D(Z) sum_(P in D) f(P) ((Z - P).x + 1) / ((Z - P).y s_P)
```

Here v_D is the vanishing polynomial of D, and s_P = -2 P.y v_(m+1)'(P.x) is the selector normalizer.

This is the Lagrange interpolation of the paper (Haböck, Levit, Papini, eprint 2024/278, Section 3.3).

The Lagrange function of P is L_P(Q) = -(P.y + Q.y) W_P(Q.x).

Here W_P is the quotient of v_(m+1)(X) - v_(m+1)(P.x) by X - P.x.

It lies in the FFT space, it is s_P at P and zero on the rest of D.

Off the poles of P it is the crate's term v_D(Q) ((Q - P).x + 1) / (Q - P).y.

So the sum is an FFT-space function that agrees with f on D.

Two such functions agree everywhere, because:

- the N points of D have N / 2 distinct x-coordinates, the roots of v_D
- each x-coordinate is shared by two points of D.
-/

namespace Plonky3Lean.Proofs.Circle

open Polynomial Plonky3Lean.Spec.Circle Finset

set_option linter.unusedSectionVars false

variable {K : Type _} [Field K] [DecidableEq K]

/-- The functions p(x) + y q(x) with p and q of degree below D.

For D = 2^m this is the FFT space of order m + 1. -/
def IsFftPoly (D : ℕ) (f : C K → K) : Prop :=
  ∃ p q : K[X], p.degree < D ∧ q.degree < D ∧ ∀ P, f P = p.eval P.x + P.y * q.eval P.x

namespace IsFftPoly

theorem toCirclePoly {D : ℕ} {f : C K → K} (hf : IsFftPoly D f) : IsCirclePoly D f := by
  obtain ⟨p, q, hp, hq, hf⟩ := hf
  exact ⟨p, q, hp.le, hq, hf⟩

theorem const {D : ℕ} (hD : 1 ≤ D) (a : K) : IsFftPoly D fun _ => a :=
  ⟨C a, 0, degree_C_le.trans_lt (by exact_mod_cast hD), by simp, fun P => by simp⟩

theorem add {D : ℕ} {f g : C K → K} (hf : IsFftPoly D f) (hg : IsFftPoly D g) :
    IsFftPoly D fun P => f P + g P := by
  obtain ⟨p, q, hp, hq, hf⟩ := hf
  obtain ⟨p', q', hp', hq', hg⟩ := hg
  exact ⟨p + p', q + q', (degree_add_le _ _).trans_lt (max_lt hp hp'),
    (degree_add_le _ _).trans_lt (max_lt hq hq'), fun P => by simp only [hf, hg]; simp; ring⟩

theorem smul {D : ℕ} {f : C K → K} (a : K) (hf : IsFftPoly D f) : IsFftPoly D fun P => a * f P := by
  obtain ⟨p, q, hp, hq, hf⟩ := hf
  exact ⟨a • p, a • q, (degree_smul_le _ _).trans_lt hp,
    (degree_smul_le _ _).trans_lt hq, fun P => by simp only [hf]; simp; ring⟩

theorem sub {D : ℕ} {f g : C K → K} (hf : IsFftPoly D f) (hg : IsFftPoly D g) :
    IsFftPoly D fun P => f P - g P := by
  simpa [sub_eq_add_neg] using add hf (smul (-1) hg)

theorem sum {D : ℕ} (hD : 1 ≤ D) {ι : Type _} (s : Finset ι) {f : ι → C K → K}
    (hf : ∀ i ∈ s, IsFftPoly D (f i)) : IsFftPoly D fun P => ∑ i ∈ s, f i P := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using const hD 0
  | insert i s hi ih =>
    simp only [sum_insert hi]
    exact add (hf i (mem_insert_self i s)) (ih fun j hj => hf j (mem_insert_of_mem hj))

/-- The FFT-basis functions of order m + 1. -/
theorem fftEval (m : ℕ) (c : ℕ → K) : IsFftPoly (2 ^ m) (fftEval (m + 1) c) := by
  obtain ⟨p, hp, he⟩ := exists_poly_xEval m fun k => c (2 * k)
  obtain ⟨q, hq, ho⟩ := exists_poly_xEval m fun k => c (2 * k + 1)
  exact ⟨p, q, degree_lt_of_natDegree_lt hp, degree_lt_of_natDegree_lt hq,
    fun P => by rw [fftEval_split, he, ho]⟩

end IsFftPoly

/-! ## The Lagrange functions -/

/-- The quotient of v_(m+1)(X) - v_(m+1)(a) by X - a.

It is the product of 2 (v_(k+1)(X) + v_(k+1)(a)) over k < m. -/
noncomputable def lagW (m : ℕ) (a : K) : K[X] :=
  ∏ k ∈ range m, (2 * (vnPoly k + C ((vnPoly k).eval a)))

theorem X_sub_C_mul_lagW (m : ℕ) (a : K) :
    (X - C a) * lagW m a = vnPoly m - C ((vnPoly m).eval a) := by
  induction m with
  | zero => simp [lagW, vnPoly]
  | succ m ih =>
    rw [lagW, prod_range_succ, ← lagW, ← mul_assoc, ih, vnPoly]
    simp only [eval_sub, eval_mul, eval_pow, eval_one, eval_ofNat, map_sub, map_mul, map_pow, map_one,
      map_ofNat]
    ring

theorem lagW_ne_zero (h2 : (2 : K) ≠ 0) (m : ℕ) (a : K) : lagW m a ≠ 0 := by
  intro h
  have := congrArg natDegree (X_sub_C_mul_lagW m a)
  rw [h, mul_zero, natDegree_zero, natDegree_sub_C, natDegree_vnPoly h2] at this
  exact (Nat.two_pow_pos m).ne this

theorem natDegree_lagW_lt (h2 : (2 : K) ≠ 0) (m : ℕ) (a : K) : (lagW m a).natDegree < 2 ^ m := by
  have := congrArg natDegree (X_sub_C_mul_lagW m a)
  rw [natDegree_mul (X_sub_C_ne_zero a) (lagW_ne_zero h2 m a), natDegree_X_sub_C, natDegree_sub_C,
    natDegree_vnPoly h2] at this
  omega

/-- The quotient at a is the derivative of v_(m+1) there. -/
theorem eval_lagW_self (m : ℕ) (a : K) : (lagW m a).eval a = (derivative (vnPoly m)).eval a := by
  have := congrArg (fun p => (derivative p).eval a) (X_sub_C_mul_lagW m a)
  simpa [derivative_mul] using this

/-- (Q.x - a) W(Q.x) = v_(m+1)(Q) - v_(m+1)(a). -/
theorem sub_mul_eval_lagW (m : ℕ) (a : K) (Q : C K) :
    (Q.x - a) * (lagW m a).eval Q.x = vn (m + 1) Q - (vnPoly m).eval a := by
  have := congrArg (eval Q.x) (X_sub_C_mul_lagW m a)
  simpa [vn_eq_eval] using this

/-- The Lagrange function of P on a twin coset of size 2^(m+1): L_P(Q) = -(P.y + Q.y) W_P(Q.x). -/
noncomputable def lagF (m : ℕ) (P Q : C K) : K := -(P.y + Q.y) * (lagW m P.x).eval Q.x

/-- The Lagrange function lies in the FFT space of order m + 1. -/
theorem isFftPoly_lagF (h2 : (2 : K) ≠ 0) (m : ℕ) (P : C K) : IsFftPoly (2 ^ m) (lagF m P) :=
  ⟨-(P.y • lagW m P.x), -lagW m P.x,
    (degree_neg _).trans_lt ((degree_smul_le _ _).trans_lt (degree_lt_of_natDegree_lt (natDegree_lagW_lt h2 m _))),
    (degree_neg _).trans_lt (degree_lt_of_natDegree_lt (natDegree_lagW_lt h2 m _)),
    fun Q => by simp [lagF]; ring⟩

/-- Off the pole, the crate's Lagrange term is the Lagrange function:

v_(m+1)(Q) - v_(m+1)(P), times (Q - P).x + 1, is L_P(Q) (Q - P).y. -/
theorem lagF_mul_sub_y (m : ℕ) (P Q : C K) :
    lagF m P Q * (Q - P).y = (vn (m + 1) Q - vn (m + 1) P) * ((Q - P).x + 1) := by
  rw [vn_eq_eval P, ← sub_mul_eval_lagW, lagF, C.sub_x, C.sub_y]
  linear_combination (lagW m P.x).eval Q.x * (Q.x * P.eq - P.x * Q.eq)

/-- The selector normalizer of a point is its own Lagrange function there. -/
theorem s_p_at_p_eq_lagF (m : ℕ) (P : C K) :
    p3_circle.point.mirror.Point.s_p_at_p (ofC P) (m + 1) = some (lagF m P P) := by
  rw [s_p_at_p_ofC, lagF, eval_lagW_self]
  congr 1; ring

/-- The Lagrange function of P vanishes at every other point with the same v_(m+1). -/
theorem lagF_eq_zero {m : ℕ} {P Q : C K} (hPQ : vn (m + 1) Q = vn (m + 1) P) (hne : Q ≠ P) :
    lagF m P Q = 0 := by
  have h := sub_mul_eval_lagW m P.x Q
  rw [← vn_eq_eval, hPQ, sub_self] at h
  rcases mul_eq_zero.mp h with h | h
  · have hy : (Q.y - P.y) * (Q.y + P.y) = 0 := by
      linear_combination Q.eq - P.eq - (Q.x + P.x) * h
    rcases mul_eq_zero.mp hy with hy | hy
    · exact absurd (C.ext (by linear_combination h) (by linear_combination hy)) hne
    · rw [lagF, show P.y + Q.y = 0 by linear_combination hy, neg_zero, zero_mul]
  · rw [lagF, h, mul_zero]

/-! ## The fibres of a twin coset over the x-axis -/

/-- At most two points of the circle share an x-coordinate. -/
theorem card_filter_x_le_two (s : Finset (C K)) (x : K) : (s.filter (·.x = x)).card ≤ 2 := by
  have hinj : Set.InjOn C.y (s.filter (·.x = x) : Set (C K)) := fun P hP Q hQ h =>
    C.ext ((mem_filter.mp (mem_coe.mp hP)).2.trans (mem_filter.mp (mem_coe.mp hQ)).2.symm) h
  set r : K[X] := X ^ 2 - Polynomial.C (1 - x ^ 2)
  have hne : r ≠ 0 := X_pow_sub_C_ne_zero (by norm_num) _
  rw [← card_image_of_injOn hinj]
  refine (card_le_card (t := r.roots.toFinset) fun y hy => ?_).trans ((Multiset.toFinset_card_le _).trans
    ((card_roots' _).trans natDegree_X_pow_sub_C.le))
  obtain ⟨P, hP, rfl⟩ := mem_image.mp hy
  simp only [mem_filter] at hP
  rw [Multiset.mem_toFinset, mem_roots hne, IsRoot, eval_sub, eval_pow, eval_X, eval_C, ← hP.2]
  linear_combination P.eq

variable {m : ℕ} {pts : Finset (C K)} {c : K}

theorem roots_vn_ne_zero (h2 : (2 : K) ≠ 0) (m : ℕ) (c : K) : (vnPoly m - C c : K[X]) ≠ 0 := by
  intro h
  have := congrArg natDegree h
  rw [natDegree_sub_C, natDegree_vnPoly h2, natDegree_zero] at this
  exact (Nat.two_pow_pos m).ne' this

theorem image_x_subset (hc : ∀ P ∈ pts, vn (m + 1) P = c) (h2 : (2 : K) ≠ 0) :
    pts.image C.x ⊆ (vnPoly m - C c).roots.toFinset := fun x hx => by
  obtain ⟨P, hP, rfl⟩ := mem_image.mp hx
  rw [Multiset.mem_toFinset, mem_roots (roots_vn_ne_zero h2 m c), IsRoot, eval_sub, eval_C, ← vn_eq_eval,
    hc P hP, sub_self]

theorem card_roots_vn_le (h2 : (2 : K) ≠ 0) (m : ℕ) (c : K) :
    (vnPoly m - C c : K[X]).roots.toFinset.card ≤ 2 ^ m :=
  (Multiset.toFinset_card_le _).trans ((card_roots' _).trans (by rw [natDegree_sub_C, natDegree_vnPoly h2]))

/-- Take 2^(m+1) distinct points with the same v_(m+1).

- They have 2^m distinct x-coordinates.
- Each point shares its x-coordinate with another one. -/
theorem twin_fibers (h2 : (2 : K) ≠ 0) (hcard : pts.card = 2 ^ (m + 1)) (hc : ∀ P ∈ pts, vn (m + 1) P = c) :
    (pts.image C.x).card = 2 ^ m ∧ ∀ P ∈ pts, ∃ Q ∈ pts, Q ≠ P ∧ Q.x = P.x := by
  have hle : (pts.image C.x).card ≤ 2 ^ m :=
    (card_le_card (image_x_subset hc h2)).trans (card_roots_vn_le h2 m c)
  have hsum := card_eq_sum_card_image C.x pts
  have hbound : ∑ x ∈ pts.image C.x, (pts.filter (·.x = x)).card ≤ ∑ _x ∈ pts.image C.x, 2 :=
    sum_le_sum fun x _ => card_filter_x_le_two pts x
  rw [sum_const, smul_eq_mul, ← hsum, hcard, pow_succ] at hbound
  have hX : (pts.image C.x).card = 2 ^ m := by omega
  refine ⟨hX, fun P hP => ?_⟩
  have heq : ∑ x ∈ pts.image C.x, (pts.filter (·.x = x)).card = ∑ _x ∈ pts.image C.x, 2 := by
    rw [← hsum, sum_const, smul_eq_mul, hX, hcard, pow_succ]
  have hfib := (sum_eq_sum_iff_of_le fun x _ => card_filter_x_le_two pts x).mp heq P.x
    (mem_image_of_mem _ hP)
  obtain ⟨Q, hQ, hne⟩ := exists_mem_ne (by omega : 1 < (pts.filter (·.x = P.x)).card) P
  exact ⟨Q, (mem_filter.mp hQ).1, hne, (mem_filter.mp hQ).2⟩

/-- Two points with the same x-coordinate are equal or conjugate. -/
theorem y_eq_or_neg {P Q : C K} (h : Q.x = P.x) : Q.y = P.y ∨ Q.y = -P.y := by
  have : (Q.y - P.y) * (Q.y + P.y) = 0 := by linear_combination Q.eq - P.eq - (Q.x + P.x) * h
  rcases mul_eq_zero.mp this with h | h
  · exact Or.inl (by linear_combination h)
  · exact Or.inr (by linear_combination h)

/-- An FFT-space function of order m + 1 that vanishes on the twin coset vanishes everywhere. -/
theorem IsFftPoly.eq_zero (h2 : (2 : K) ≠ 0) (hcard : pts.card = 2 ^ (m + 1))
    (hc : ∀ P ∈ pts, vn (m + 1) P = c) {f : C K → K} (hf : IsFftPoly (2 ^ m) f) (hz : ∀ P ∈ pts, f P = 0)
    (Z : C K) : f Z = 0 := by
  obtain ⟨p, q, hp, hq, hf⟩ := hf
  obtain ⟨hX, hpair⟩ := twin_fibers h2 hcard hc
  have hroot : ∀ x ∈ pts.image C.x, p.eval x = 0 ∧ q.eval x = 0 := fun x hx => by
    obtain ⟨P, hP, rfl⟩ := mem_image.mp hx
    obtain ⟨Q, hQ, hne, hQx⟩ := hpair P hP
    have hy : Q.y ≠ P.y := fun h => hne (C.ext hQx h)
    have e1 := hz P hP
    have e2 := hz Q hQ
    rw [hf] at e1 e2
    rw [hQx] at e2
    have hq0 : q.eval P.x = 0 :=
      (mul_eq_zero.mp (by linear_combination e2 - e1 : (Q.y - P.y) * q.eval P.x = 0)).resolve_left
        (sub_ne_zero.mpr hy)
    exact ⟨by linear_combination e1 - P.y * hq0, hq0⟩
  have hp0 := eq_zero_of_natDegree_lt_card_of_eval_eq_zero' p _ (fun x hx => (hroot x hx).1)
    (hX ▸ natDegree_lt_of_degree_lt (by positivity) hp)
  have hq0 := eq_zero_of_natDegree_lt_card_of_eval_eq_zero' q _ (fun x hx => (hroot x hx).2)
    (hX ▸ natDegree_lt_of_degree_lt (by positivity) hq)
  simp [hf, hp0, hq0]

/-- The twin coset is the whole fibre of v_(m+1) over c. -/
theorem mem_of_vn_eq (h2 : (2 : K) ≠ 0) (hcard : pts.card = 2 ^ (m + 1)) (hc : ∀ P ∈ pts, vn (m + 1) P = c)
    {Q : C K} (hQ : vn (m + 1) Q = c) : Q ∈ pts := by
  obtain ⟨hX, hpair⟩ := twin_fibers h2 hcard hc
  have hsub := image_x_subset hc h2
  have heq := eq_of_subset_of_card_le hsub (hX ▸ card_roots_vn_le h2 m c)
  have hx : Q.x ∈ pts.image C.x := by
    rw [heq, Multiset.mem_toFinset, mem_roots (roots_vn_ne_zero h2 m c), IsRoot, eval_sub, eval_C,
      ← vn_eq_eval, hQ, sub_self]
  obtain ⟨P, hP, hPx⟩ := mem_image.mp hx
  obtain ⟨P', hP', hne, hP'x⟩ := hpair P hP
  rcases y_eq_or_neg hPx.symm with h | h
  · rwa [C.ext hPx.symm h]
  · rcases y_eq_or_neg hP'x with h' | h'
    · exact absurd (C.ext hP'x h') hne
    · rwa [C.ext (hPx.symm.trans hP'x.symm) (h.trans h'.symm)]

/-- The selector normalizer of a point of the twin coset is not zero. -/
theorem lagF_self_ne_zero (h2 : (2 : K) ≠ 0) (hcard : pts.card = 2 ^ (m + 1))
    (hc : ∀ P ∈ pts, vn (m + 1) P = c) {P : C K} (hP : P ∈ pts) : lagF m P P ≠ 0 := by
  obtain ⟨hX, hpair⟩ := twin_fibers h2 hcard hc
  obtain ⟨Q, hQ, hne, hQx⟩ := hpair P hP
  have hy : P.y ≠ 0 := fun h0 => by
    rcases y_eq_or_neg hQx with h | h
    · exact hne (C.ext hQx h)
    · exact hne (C.ext hQx (by rw [h, h0, neg_zero]))
  have hW : (lagW m P.x).eval P.x ≠ 0 := fun h0 => by
    refine lagW_ne_zero h2 m P.x (eq_zero_of_natDegree_lt_card_of_eval_eq_zero' _ (pts.image C.x)
      (fun x hx => ?_) (hX ▸ natDegree_lagW_lt h2 m P.x))
    obtain ⟨R, hR, rfl⟩ := mem_image.mp hx
    by_cases hRx : R.x = P.x
    · rwa [hRx]
    · have := sub_mul_eval_lagW m P.x R
      rw [← vn_eq_eval, hc R hR, hc P hP, sub_self] at this
      exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hRx)
  rw [lagF]
  exact mul_ne_zero (neg_ne_zero.mpr (by rw [← two_mul]; exact mul_ne_zero h2 hy)) hW

/-- On a twin coset of size at least 4, a point Z off the coset is off every pole: (Z - P).y is nonzero.

The pole of P is its antipode, and the antipode lies on the coset. -/
theorem sub_y_ne_zero (h2 : (2 : K) ≠ 0) (hm : 1 ≤ m) (hcard : pts.card = 2 ^ (m + 1))
    (hc : ∀ P ∈ pts, vn (m + 1) P = c) {Z : C K} (hZ : Z ∉ pts) {P : C K} (hP : P ∈ pts) : (Z - P).y ≠ 0 := by
  intro hy
  set D := Z - P with hDdef
  have hZD : Z = P + D := by rw [hDdef]; abel
  have hx : (D.x - 1) * (D.x + 1) = 0 := by linear_combination D.eq - D.y * hy
  rcases mul_eq_zero.mp hx with h | h
  · exact hZ (by rwa [hZD, show D = 0 from C.ext (by simp; linear_combination h) hy, add_zero])
  · refine hZ (mem_of_vn_eq h2 hcard hc ?_)
    have hD2 : 2 • D = 0 := C.ext (by rw [C.two_nsmul_x, show D.x = -1 by linear_combination h]; simp; norm_num)
      (by rw [C.two_nsmul_y, hy]; simp)
    have hDm : 2 ^ m • D = 0 := by
      rw [show 2 ^ m = 2 ^ (m - 1) * 2 by rw [← pow_succ]; congr 1; omega, mul_comm, mul_nsmul, hD2, smul_zero]
    rw [← hc P hP, vn, vn, Nat.add_sub_cancel, hZD, smul_add, hDm, add_zero]

/-! ## The barycentric formula -/

/-- The circle barycentric formula.

Take 2^(m+1) distinct points with the same v_(m+1), equal to c, and f in the FFT space of order m + 1.

Take a point Z with (Z - P).y nonzero for every point P.

Then sum_P f(P) ((Z - P).x + 1) / ((Z - P).y s_P), times v_(m+1)(Z) - c, is f(Z). -/
theorem bary (h2 : (2 : K) ≠ 0) (hcard : pts.card = 2 ^ (m + 1)) (hc : ∀ P ∈ pts, vn (m + 1) P = c)
    {f : C K → K} (hf : IsFftPoly (2 ^ m) f) {Z : C K} (hZ : ∀ P ∈ pts, (Z - P).y ≠ 0) :
    (∑ P ∈ pts, f P * (((Z - P).x + 1) * ((Z - P).y * lagF m P P)⁻¹)) * (vn (m + 1) Z - c) = f Z := by
  set g : C K → K := fun Q => ∑ P ∈ pts, f P * (lagF m P P)⁻¹ * lagF m P Q
  have hg : IsFftPoly (2 ^ m) g := IsFftPoly.sum Nat.one_le_two_pow _ fun P _ =>
    IsFftPoly.smul _ (isFftPoly_lagF h2 m P)
  have hgD : ∀ Q ∈ pts, f Q - g Q = 0 := fun Q hQ => by
    rw [sub_eq_zero]
    change f Q = ∑ P ∈ pts, f P * (lagF m P P)⁻¹ * lagF m P Q
    rw [sum_eq_single Q (fun P hP hne => by rw [lagF_eq_zero (by rw [hc Q hQ, hc P hP]) hne.symm,
      mul_zero]) (fun h => absurd hQ h), mul_assoc, inv_mul_cancel₀ (lagF_self_ne_zero h2 hcard hc hQ),
      mul_one]
  have := IsFftPoly.eq_zero h2 hcard hc (hf.sub hg) hgD Z
  rw [sum_mul, (sub_eq_zero.mp this : f Z = g Z)]
  refine sum_congr rfl fun P hP => ?_
  have hs := lagF_self_ne_zero h2 hcard hc hP
  have hy := hZ P hP
  have hl := lagF_mul_sub_y m P Z
  rw [hc P hP] at hl
  field_simp
  linear_combination (-f P) * hl

/-- Take f of degree 2^m with a v_(m+1) component mu, the line the FFT space misses.

Then the formula returns f(Z) - mu v_D(Z), not f(Z).

For f = v_(m+1) itself it returns the constant c. -/
theorem bary_circlePoly (h2 : (2 : K) ≠ 0) (hcard : pts.card = 2 ^ (m + 1)) (hc : ∀ P ∈ pts, vn (m + 1) P = c)
    {f : C K → K} (hf : IsCirclePoly (2 ^ m) f) :
    ∃ μ : K, (∀ P, f P = (f P - μ * vn (m + 1) P) + μ * vn (m + 1) P) ∧
      IsFftPoly (2 ^ m) (fun P => f P - μ * vn (m + 1) P) ∧
      ∀ {Z : C K}, (∀ P ∈ pts, (Z - P).y ≠ 0) →
        (∑ P ∈ pts, f P * (((Z - P).x + 1) * ((Z - P).y * lagF m P P)⁻¹)) * (vn (m + 1) Z - c) =
          f Z - μ * (vn (m + 1) Z - c) := by
  obtain ⟨c', μ, hF⟩ := IsCirclePoly.split_vn h2 hf
  have hfft : IsFftPoly (2 ^ m) (fun P => f P - μ * vn (m + 1) P) := by
    simpa [hF] using IsFftPoly.fftEval m c'
  refine ⟨μ, fun P => by ring, hfft, fun {Z} hZ => ?_⟩
  have := bary h2 hcard hc (hfft.add (IsFftPoly.const Nat.one_le_two_pow (μ * c))) hZ
  rw [show f Z - μ * (vn (m + 1) Z - c) = f Z - μ * vn (m + 1) Z + μ * c by ring, ← this]
  congr 1
  refine sum_congr rfl fun P hP => ?_
  rw [hc P hP]; ring

/-! ## The crate's evaluation -/

section crate

open p3_circle.point.mirror p3_circle.domain.mirror p3_circle.prover.mirror p3_commit.domain.mirror
open p3_commit.pcs.univariate.mirror

/-- The selector normalizer of P is -2^n (2^(n-1) P).y. -/
theorem lagF_self_eq {n : ℕ} (hn : 1 ≤ n) (P : C K) : lagF (n - 1) P P = -2 ^ n * (2 ^ (n - 1) • P).y := by
  have h1 := s_p_at_p_eq_lagF (n - 1) P
  rw [Nat.sub_add_cancel hn, s_p_at_p_eq_selReg P hn, selReg_self n hn] at h1
  exact (Option.some.inj h1).symm

theorem allM_eq_some_true {α : Type _} (f : α → Option Bool) :
    ∀ l : List α, (∀ a ∈ l, f a = some true) → l.allM f = some true
  | [], _ => List.allM_nil
  | a :: l, h => by
    simp [List.allM_cons, h a List.mem_cons_self, allM_eq_some_true f l fun b hb => h b (List.mem_cons_of_mem a hb)]

theorem zipIdx_map_range {α : Type _} (g : ℕ → α) (N : ℕ) :
    ((List.range N).map g).zipIdx = (List.range N).map fun i => (g i, i) :=
  List.ext_getElem (by simp) fun i _ _ => by simp [List.getElem_zipIdx]

variable {s : ℕ} {S : C K} {P : ℕ → C K}

/-- The points of a twin coset of size 2^s with shift S, listed so that:

- they are distinct
- doubling s - 1 times sends a point of even index to 2^(s-1) S, and one of odd index to its conjugate.

The circle FFT order of a twin coset, and its prefixes, list their points this way. -/
structure TwinList (s : ℕ) (S : C K) (P : ℕ → C K) : Prop where
  inj : ∀ i < 2 ^ s, ∀ j < 2 ^ s, P i = P j → i = j
  par : ∀ i < 2 ^ s, 2 ^ (s - 1) • P i = if i % 2 = 0 then 2 ^ (s - 1) • S else -(2 ^ (s - 1) • S)

theorem TwinList.vn_eq (hP : TwinList s S P) {i : ℕ} (hi : i < 2 ^ s) : vn s (P i) = vn s S := by
  rw [vn, vn, hP.par i hi]; split_ifs <;> simp

theorem TwinList.card (hP : TwinList s S P) :
    ((List.range (2 ^ s)).map P).toFinset.card = 2 ^ s := by
  rw [List.toFinset_card_of_nodup (List.Nodup.map_on (fun i hi j hj h => hP.inj i (List.mem_range.mp hi) j
    (List.mem_range.mp hj) h) List.nodup_range), List.length_map, List.length_range]

theorem TwinList.mem {Q : C K} :
    Q ∈ ((List.range (2 ^ s)).map P).toFinset ↔ ∃ i < 2 ^ s, P i = Q := by
  simp

theorem TwinList.lagF_ne_zero (h2 : (2 : K) ≠ 0) (hs : 1 ≤ s) (hP : TwinList s S P) {i : ℕ} (hi : i < 2 ^ s) :
    lagF (s - 1) (P i) (P i) ≠ 0 := by
  obtain ⟨m, rfl⟩ : ∃ m, s = m + 1 := ⟨s - 1, by omega⟩
  exact lagF_self_ne_zero h2 hP.card (fun Q hQ => by
    obtain ⟨j, hj, rfl⟩ := TwinList.mem.mp hQ; exact hP.vn_eq hj) (TwinList.mem.mpr ⟨i, hi, rfl⟩)

/-- The crate's Lagrange denominators of a twin coset of size 2^s >= 2 pass the debug assertions.

They are the batch inversion of (Z - P_i).y s_i, times (Z - P_i).x + 1, with s_i the normalizer of P_i. -/
theorem compute_lagrange_den_eq_map (hs : 1 ≤ s) (hP : TwinList s S P) (Z : C K) :
    compute_lagrange_den_on_domain ((List.range (2 ^ s)).map fun i => ofC (P i)) (ofC Z) ⟨s, ofC S⟩ =
      (batchInv ((List.range (2 ^ s)).map fun i => (Z - P i).y * lagF (s - 1) (P i) (P i))).map
        fun inv => List.zipWith (· * ·) ((List.range (2 ^ s)).map fun i => (Z - P i).x + 1) inv := by
  have hsp : ∀ Q : C K, Point.s_p_at_p (ofC Q) s = some (lagF (s - 1) Q Q) := fun Q => by
    have := s_p_at_p_eq_lagF (s - 1) Q; rwa [Nat.sub_add_cancel hs] at this
  have hidx : ∀ i < 2 ^ s, (if i % 2 = 0 then lagF (s - 1) S S else -lagF (s - 1) S S) =
      lagF (s - 1) (P i) (P i) := fun i hi => by
    rw [lagF_self_eq hs, lagF_self_eq hs, hP.par i hi]; split_ifs <;> simp
  have h2s : 2 ≤ 2 ^ s := by
    calc 2 = 2 ^ 1 := rfl
      _ ≤ 2 ^ s := Nat.pow_le_pow_right two_pos hs
  unfold compute_lagrange_den_on_domain
  simp only [List.length_map, List.length_range, ne_eq, not_true_eq_false, ↓reduceIte, hsp,
    Option.bind_eq_bind, Option.bind_some, show ¬ 2 ^ s < 2 by omega]
  rw [allM_eq_some_true _ _ fun i hi => ?_]
  · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, Option.bind_some, zipIdx_map_range, List.map_map]
    refine (show ∀ A A' B B' : List K, A = A' → B = B' →
        ((batchInv A).bind fun a => pure (List.zipWith (· * ·) B a)) =
          (batchInv A').map fun inv => List.zipWith (· * ·) B' inv from by
      rintro A _ _ _ rfl rfl; cases batchInv A <;> rfl) _ _ _ _
      (List.map_congr_left fun i hi => ?_) (List.map_congr_left fun i hi => ?_)
    · simp only [Function.comp_apply, sub_ofC, ofC_y]
      rw [hidx i (List.mem_range.mp hi)]
    · simp [sub_ofC]
  · have hi' : i < 2 ^ s := by simp at hi; omega
    simp [List.getElem?_map, List.getElem?_range hi', hsp, hidx i hi']

/-- The crate's Lagrange denominators of a twin coset of size 2^s >= 2, toward a point off every pole. -/
theorem compute_lagrange_den_eq (h2 : (2 : K) ≠ 0) (hs : 1 ≤ s) (hP : TwinList s S P) (Z : C K)
    (hZ : ∀ i < 2 ^ s, (Z - P i).y ≠ 0) :
    compute_lagrange_den_on_domain ((List.range (2 ^ s)).map fun i => ofC (P i)) (ofC Z) ⟨s, ofC S⟩ =
      some ((List.range (2 ^ s)).map fun i => ((Z - P i).x + 1) * ((Z - P i).y * lagF (s - 1) (P i) (P i))⁻¹) := by
  rw [compute_lagrange_den_eq_map hs hP, batchInv_eq fun x hx => ?_]
  · simp only [Option.map_some, List.map_map, List.zipWith_map, List.zipWith_self, Option.some.injEq]
    rfl
  · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
    exact mul_ne_zero (hZ i (List.mem_range.mp hi)) (hP.lagF_ne_zero h2 hs (List.mem_range.mp hi))

/-- The crate's Lagrange denominators panic at a pole of a point: where (Z - P_i).y = 0.

This holds on the domain itself, where Z = P_i. -/
theorem compute_lagrange_den_none (hs : 1 ≤ s) (hP : TwinList s S P) {Z : C K} {i : ℕ} (hi : i < 2 ^ s)
    (hZ : (Z - P i).y = 0) :
    compute_lagrange_den_on_domain ((List.range (2 ^ s)).map fun i => ofC (P i)) (ofC Z) ⟨s, ofC S⟩ = none := by
  rw [compute_lagrange_den_eq_map hs hP, batchInv, ite_eq_right fun h => h _ (List.mem_map.mpr ⟨i,
    List.mem_range.mpr hi, rfl⟩) (by rw [hZ, zero_mul])]
  rfl

/-- On a twin coset of size at least 4, the crate's Lagrange denominators panic exactly on the coset. -/
theorem compute_lagrange_den_none_iff (h2 : (2 : K) ≠ 0) (hs : 2 ≤ s) (hP : TwinList s S P) (Z : C K) :
    compute_lagrange_den_on_domain ((List.range (2 ^ s)).map fun i => ofC (P i)) (ofC Z) ⟨s, ofC S⟩ = none ↔
      ∃ i < 2 ^ s, Z = P i := by
  constructor
  · intro hnone
    by_contra hoff
    push Not at hoff
    have hs1 : s - 1 + 1 = s := by omega
    rw [compute_lagrange_den_eq h2 (by omega) hP Z fun i hi => sub_y_ne_zero (m := s - 1) (c := vn s S) h2
      (by omega) (by rw [hP.card, hs1]) (fun Q hQ => by
        obtain ⟨j, hj, rfl⟩ := TwinList.mem.mp hQ; rw [hs1]; exact hP.vn_eq hj)
      (fun hZ => by obtain ⟨j, hj, hjZ⟩ := TwinList.mem.mp hZ; exact hoff j hj hjZ.symm)
      (TwinList.mem.mpr ⟨i, hi, rfl⟩)] at hnone
    exact Option.some_ne_none _ hnone
  · rintro ⟨i, hi, rfl⟩
    exact compute_lagrange_den_none (by omega) hP hi (by simp)

/-- On a twin coset of size 2 whose points have a nonzero x-coordinate, the crate panics off the coset.

The antipode of the first point is off the coset, and it is the pole of that point's Lagrange term. -/
theorem compute_lagrange_den_size_two (h2 : (2 : K) ≠ 0) (hP : TwinList 1 S P) (hx : (P 0).x ≠ 0) :
    (P 0).antipode ≠ P 0 ∧ (P 0).antipode ≠ P 1 ∧
      compute_lagrange_den_on_domain ((List.range (2 ^ 1)).map fun i => ofC (P i)) (ofC (P 0).antipode)
        ⟨1, ofC S⟩ = none := by
  have hv : vn 1 (P 1) = vn 1 (P 0) := by rw [hP.vn_eq (by norm_num), hP.vn_eq (by norm_num)]
  simp only [vn, Nat.sub_self, pow_zero, one_nsmul] at hv
  have hne : -(P 0).x ≠ (P 0).x := fun h => hx (by
    have : 2 * (P 0).x = 0 := by linear_combination -h
    exact (mul_eq_zero.mp this).resolve_left h2)
  refine ⟨fun h => hne (by rw [← C.antipode_x, h]), fun h => hne (by rw [← C.antipode_x, h, hv]),
    compute_lagrange_den_none le_rfl hP (i := 0) (by norm_num) ?_⟩
  simp [C.antipode]

/-- A domain of one point has no twin coset: the crate's Lagrange denominators panic on it. -/
theorem compute_lagrange_den_log_zero (pts : List (Point K)) (at_ : Point K) (shift : Point K) :
    compute_lagrange_den_on_domain pts at_ ⟨0, shift⟩ = none := by
  unfold compute_lagrange_den_on_domain
  by_cases h : pts.length = 2 ^ 0 <;> simp [h, Point.s_p_at_p]

theorem TwinList.nodup (hP : TwinList s S P) : ((List.range (2 ^ s)).map P).Nodup :=
  List.Nodup.map_on (fun i hi j hj h => hP.inj i (List.mem_range.mp hi) j (List.mem_range.mp hj) h)
    List.nodup_range

/-- The crate's evaluation of the columns at a point, from the Lagrange denominators.

Take a matrix whose 2^s rows hold columns of the FFT space of order s at the points of a twin coset.

At a point off every pole it returns the columns' values. -/
theorem evaluate_at_point_with_den_eq (h2 : (2 : K) ≠ 0) (hs : 1 ≤ s) (hP : TwinList s S P) (M : Mat K)
    (hM : M.height = 2 ^ s) (fs : Fin M.width → C K → K) (hf : ∀ c, IsFftPoly (2 ^ (s - 1)) (fs c))
    (hent : ∀ r < 2 ^ s, ∀ c, M.entry r c = fs c (P r)) (Z : C K) (hZ : ∀ i < 2 ^ s, (Z - P i).y ≠ 0) :
    evaluate_at_point_with_den ⟨s, ofC S⟩ M (ofC Z)
        ((List.range (2 ^ s)).map fun i => ((Z - P i).x + 1) * ((Z - P i).y * lagF (s - 1) (P i) (P i))⁻¹) =
      some ((List.finRange M.width).map fun c => fs c Z) := by
  obtain ⟨m, rfl⟩ : ∃ m, s = m + 1 := ⟨s - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at hf ⊢
  unfold evaluate_at_point_with_den
  simp only [vanishing_poly_eq _ _ _ hs, Option.bind_eq_bind, Option.bind_some, List.length_map,
    List.length_range, hM, ne_eq, not_true_eq_false, ↓reduceIte, Option.pure_def, Option.some.injEq]
  refine List.map_congr_left fun c _ => ?_
  have hc : ∀ Q ∈ ((List.range (2 ^ (m + 1))).map P).toFinset, vn (m + 1) Q = vn (m + 1) S := fun Q hQ => by
    obtain ⟨j, hj, rfl⟩ := TwinList.mem.mp hQ; exact hP.vn_eq hj
  have hZ' : ∀ Q ∈ ((List.range (2 ^ (m + 1))).map P).toFinset, (Z - Q).y ≠ 0 := fun Q hQ => by
    obtain ⟨j, hj, rfl⟩ := TwinList.mem.mp hQ; exact hZ j hj
  rw [← bary h2 hP.card hc (hf c) hZ', List.sum_toFinset _ hP.nodup, List.map_map, vD]
  congr 2
  refine List.map_congr_left fun r hr => ?_
  have hr' := List.mem_range.mp hr
  rw [hent r hr', List.getD_eq_getElem _ _ (by simpa using hr'), List.getElem_map, List.getElem_range]
  simp only [Function.comp_apply]
  ring

end crate

end Plonky3Lean.Proofs.Circle
