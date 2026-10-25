module

public import Mathlib.Algebra.Polynomial.Div
public import Mathlib.Algebra.Polynomial.Eval.Degree
public import Plonky3Lean.Proofs.Circle.Deep

@[expose] public section

/-!
# Polynomials on the circle and the DEEP quotient

A polynomial of degree at most D on the circle is reduced modulo x^2 + y^2 = 1:

```text
    f(x, y) = p(x) + y q(x),     deg p <= D,  deg q < D
```

This is the space L_N of the paper, with N = 2 D.
-/

namespace Plonky3Lean.Proofs.Circle

open Polynomial Plonky3Lean.Spec.Circle Plonky3Lean.Proofs.Dft Finset

set_option linter.unusedSectionVars false

variable {K : Type _} [Field K]

/-- The functions on the circle that a polynomial of degree at most D gives. -/
def IsCirclePoly (D : ℕ) (f : C K → K) : Prop :=
  ∃ p q : K[X], p.degree ≤ D ∧ q.degree < D ∧ ∀ P, f P = p.eval P.x + P.y * q.eval P.x

namespace IsCirclePoly

theorem degree_lt_iff {q : K[X]} {D : ℕ} : q.degree < D ↔ q.degree + 1 ≤ D := by
  induction q.degree using WithBot.recBotCoe with
  | bot => simp
  | coe n =>
    simp only [Nat.cast_withBot, ← WithBot.coe_one, ← WithBot.coe_add, WithBot.coe_lt_coe, WithBot.coe_le_coe]
    omega

theorem mono {D D' : ℕ} {f : C K → K} (h : D ≤ D') (hf : IsCirclePoly D f) : IsCirclePoly D' f := by
  obtain ⟨p, q, hp, hq, hf⟩ := hf
  exact ⟨p, q, hp.trans (by exact_mod_cast h), hq.trans_le (by exact_mod_cast h), hf⟩

theorem const (D : ℕ) (a : K) : IsCirclePoly D fun _ => a :=
  ⟨C a, 0, degree_C_le.trans (by exact_mod_cast Nat.zero_le D), by simp, fun P => by simp⟩

theorem x : IsCirclePoly 1 fun P : C K => P.x :=
  ⟨X, 0, by simp, by simp, fun P => by simp⟩

theorem y : IsCirclePoly 1 fun P : C K => P.y :=
  ⟨0, 1, by simp, by simp, fun P => by simp⟩

theorem add {D : ℕ} {f g : C K → K} (hf : IsCirclePoly D f) (hg : IsCirclePoly D g) :
    IsCirclePoly D fun P => f P + g P := by
  obtain ⟨p, q, hp, hq, hf⟩ := hf
  obtain ⟨p', q', hp', hq', hg⟩ := hg
  exact ⟨p + p', q + q', (degree_add_le _ _).trans (max_le hp hp'),
    (degree_add_le _ _).trans_lt (max_lt hq hq'), fun P => by simp only [hf, hg]; simp; ring⟩

theorem smul {D : ℕ} {f : C K → K} (a : K) (hf : IsCirclePoly D f) : IsCirclePoly D fun P => a * f P := by
  obtain ⟨p, q, hp, hq, hf⟩ := hf
  exact ⟨a • p, a • q, (degree_smul_le _ _).trans hp,
    (degree_smul_le _ _).trans_lt hq, fun P => by simp only [hf]; simp; ring⟩

theorem sum {D : ℕ} {ι : Type _} (s : Finset ι) {f : ι → C K → K} (hf : ∀ i ∈ s, IsCirclePoly D (f i)) :
    IsCirclePoly D fun P => ∑ i ∈ s, f i P := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using const D 0
  | insert i s hi ih =>
    simp only [sum_insert hi]
    exact add (hf i (mem_insert_self i s)) (ih fun j hj => hf j (mem_insert_of_mem hj))

theorem mul {D D' : ℕ} {f g : C K → K} (hf : IsCirclePoly D f) (hg : IsCirclePoly D' g) :
    IsCirclePoly (D + D') fun P => f P * g P := by
  obtain ⟨p, q, hp, hq, hf⟩ := hf
  obtain ⟨p', q', hp', hq', hg⟩ := hg
  rw [degree_lt_iff] at hq hq'
  refine ⟨p * p' + (1 - X ^ 2) * (q * q'), p * q' + q * p', ?_, ?_, fun P => ?_⟩
  · refine (degree_add_le _ _).trans (max_le ((degree_mul_le _ _).trans ?_) ((degree_mul_le _ _).trans ?_))
    · push_cast; exact add_le_add hp hp'
    · have h1 : (1 - X ^ 2 : K[X]).degree ≤ 2 := by
        refine (degree_sub_le _ _).trans (max_le (by simp) ?_); rw [degree_X_pow]; rfl
      refine (add_le_add h1 (degree_mul_le _ _)).trans ?_
      push_cast
      calc (2 : WithBot ℕ) + (q.degree + q'.degree) = (q.degree + 1) + (q'.degree + 1) := by
            rw [show (2 : WithBot ℕ) = 1 + 1 from rfl]; ac_rfl
        _ ≤ D + D' := add_le_add hq hq'
  · rw [degree_lt_iff]
    refine (add_le_add_left (degree_add_le (p * q') (q * p')) 1).trans ?_
    rw [← max_add_add_right]
    refine max_le ((add_le_add_left (degree_mul_le _ _) 1).trans ?_)
      ((add_le_add_left (degree_mul_le _ _) 1).trans ?_)
    · push_cast; rw [add_assoc]; exact add_le_add hp hq'
    · push_cast; rw [add_right_comm]; exact add_le_add hq hp'
  · simp only [hf, hg, eval_add, eval_mul, eval_sub, eval_one, eval_pow, eval_X]
    linear_combination (q.eval P.x * q'.eval P.x) * P.eq

theorem pow {f : C K → K} (hf : IsCirclePoly 1 f) (i : ℕ) : IsCirclePoly i fun P => f P ^ i := by
  induction i with
  | zero => simpa using const 0 (1 : K)
  | succ i ih => simpa [pow_succ] using mul ih hf

/-- A polynomial of degree at most D in a degree-one function has degree at most D. -/
theorem eval {D : ℕ} {f : C K → K} (hf : IsCirclePoly 1 f) {p : K[X]} (hp : p.degree ≤ D) :
    IsCirclePoly D fun P => p.eval (f P) := by
  simp only [eval_eq_sum_range]
  refine sum _ fun i hi => smul _ ((pow hf i).mono ?_)
  rcases eq_or_ne p 0 with rfl | h0
  · simp at hi; omega
  · rw [degree_eq_natDegree h0] at hp
    have := Finset.mem_range.mp hi
    exact_mod_cast (Nat.lt_succ_iff.mp this).trans (by exact_mod_cast hp)

/-- A translate of a polynomial on the circle has the same degree. -/
theorem translate {D : ℕ} {f : C K → K} (hf : IsCirclePoly D f) (Z : C K) :
    IsCirclePoly D fun P => f (P + Z) := by
  obtain ⟨p, q, hp, hq, hf⟩ := hf
  have hx : IsCirclePoly 1 fun P : C K => (P + Z).x := by
    simpa [sub_eq_add_neg, mul_comm] using add (smul Z.x x) (smul (-Z.y) y)
  have hy : IsCirclePoly 1 fun P : C K => (P + Z).y := by
    simpa [mul_comm] using add (smul Z.y x) (smul Z.x y)
  simp only [hf]
  refine add (eval hx hp) ?_
  rcases Nat.eq_zero_or_pos D with rfl | hD
  · have : q = 0 := by simpa using hq
    simpa [this] using const 0 (0 : K)
  · have hq' : q.degree ≤ (D - 1 : ℕ) := by
      rw [degree_lt_iff] at hq
      revert hq
      induction q.degree using WithBot.recBotCoe with
      | bot => exact fun _ => bot_le
      | coe n =>
        simp only [Nat.cast_withBot, ← WithBot.coe_one, ← WithBot.coe_add, WithBot.coe_le_coe]
        omega
    simpa [show 1 + (D - 1) = D by omega] using mul hy (eval hx hq')

end IsCirclePoly

/-! ## The DEEP quotient -/

/-- At the neutral point (1, 0), the quotient by the tangent 1 - x of (f - f(1, 0)) y has the degree of f. -/
theorem IsCirclePoly.deep_zero {D : ℕ} {f : C K → K} (hf : IsCirclePoly D f) :
    ∃ g, IsCirclePoly D g ∧ ∀ P : C K, (1 - P.x) * g P = (f P - f 0) * P.y := by
  obtain ⟨p, q, hp, hq, hf⟩ := hf
  set r := p - C (p.eval 1)
  set s := r /ₘ (X - C 1)
  have hs : (X - C 1) * s = r := mul_divByMonic_eq_iff_isRoot.mpr (by simp [r])
  have hr : r.degree ≤ D := (degree_sub_le _ _).trans (max_le hp (degree_C_le.trans (by exact_mod_cast Nat.zero_le D)))
  have hsd : s.degree < D := by
    rcases eq_or_ne r 0 with h | h
    · simp [s, h]
    · exact (degree_divByMonic_lt _ _ h (by rw [degree_X_sub_C]; exact zero_lt_one)).trans_le hr
  refine ⟨fun P => P.y * (-s).eval P.x + ((1 + X) * q).eval P.x, ⟨(1 + X) * q, -s, ?_, by rwa [degree_neg],
    fun P => by ring⟩, fun P => ?_⟩
  · rw [IsCirclePoly.degree_lt_iff] at hq
    have h1 : (1 + X : K[X]).degree ≤ 1 := (degree_add_le _ _).trans (max_le (by simp) degree_X_le)
    calc ((1 + X) * q).degree ≤ (1 + X : K[X]).degree + q.degree := degree_mul_le _ _
      _ ≤ 1 + q.degree := by gcongr
      _ ≤ D := by rwa [add_comm]
  · have hsx := congrArg (Polynomial.eval P.x) hs
    simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, r] at hsx
    simp only [hf, Polynomial.eval_neg, Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_one,
      Polynomial.eval_X, C.zero_x, C.zero_y]
    linear_combination (-q.eval P.x) * P.eq + P.y * hsx

/-- The DEEP quotient lemma.

Take f of degree at most D and a point Z of the circle.

The quotient of (f - f(Z)) (P - Z)_y by the tangent 1 - (P - Z)_x at Z also has degree at most D. -/
theorem IsCirclePoly.deep {D : ℕ} {f : C K → K} (hf : IsCirclePoly D f) (Z : C K) :
    ∃ g, IsCirclePoly D g ∧ ∀ P : C K, (1 - (P - Z).x) * g P = (f P - f Z) * (P - Z).y := by
  obtain ⟨g, hg, hgP⟩ := (hf.translate Z).deep_zero
  refine ⟨fun P => g (P - Z), by simpa [sub_eq_add_neg] using hg.translate (-Z), fun P => ?_⟩
  simpa using hgP (P - Z)

/-! ## The FFT basis spans the polynomials below the domain size -/

theorem degree_lt_of_natDegree_lt {r : K[X]} {n : ℕ} (h : r.natDegree < n) : r.degree < n :=
  degree_le_natDegree.trans_lt (by exact_mod_cast h)

theorem natDegree_lt_of_degree_lt {r : K[X]} {n : ℕ} (hn : 0 < n) (h : r.degree < n) : r.natDegree < n := by
  rcases eq_or_ne r 0 with rfl | h0
  · simpa
  · exact (natDegree_lt_iff_degree_lt h0).mpr h

/-- The squaring map pi(x) = 2 x^2 - 1 as a polynomial. -/
noncomputable def piPoly : K[X] := C 2 * X ^ 2 - 1

theorem natDegree_piPoly_le : (piPoly : K[X]).natDegree ≤ 2 := by
  unfold piPoly
  refine (natDegree_sub_le _ _).trans (max_le ((natDegree_C_mul_le _ _).trans ?_) (by simp))
  simp

theorem eval_piPoly (x : K) : (piPoly : K[X]).eval x = piX x := by simp [piPoly, piX]

/-- An x-basis function of order m is a polynomial of degree below 2^m. -/
theorem exists_poly_xEval (m : ℕ) (d : ℕ → K) :
    ∃ r : K[X], r.natDegree < 2 ^ m ∧ ∀ x, xEval m d x = r.eval x := by
  induction m generalizing d with
  | zero => exact ⟨C (d 0), by simp, fun x => by simp [xEval, xBasis]⟩
  | succ m ih =>
    obtain ⟨re, hre, he⟩ := ih fun k => d (2 * k)
    obtain ⟨ro, hro, ho⟩ := ih fun k => d (2 * k + 1)
    refine ⟨re.comp piPoly + X * ro.comp piPoly, ?_, fun x => ?_⟩
    · have hc : ∀ r : K[X], r.natDegree < 2 ^ m → (r.comp piPoly).natDegree ≤ (2 ^ m - 1) * 2 := fun r hr =>
        natDegree_comp_le.trans (Nat.mul_le_mul (by omega) natDegree_piPoly_le)
      have hp : 1 ≤ 2 ^ m := Nat.one_le_two_pow
      refine (natDegree_add_le _ _).trans_lt (max_lt ((hc re hre).trans_lt ?_)
        ((natDegree_mul_le.trans (add_le_add natDegree_X_le (hc ro hro))).trans_lt ?_)) <;>
      · rw [pow_succ]; omega
    · rw [xEval_split, he, ho]; simp [eval_comp, eval_piPoly]

/-- Every polynomial of degree below 2^m is an x-basis function of order m. -/
theorem exists_xEval (h2 : (2 : K) ≠ 0) (m : ℕ) (r : K[X]) (hr : r.natDegree < 2 ^ m) :
    ∃ d : ℕ → K, ∀ x, r.eval x = xEval m d x := by
  induction m generalizing r with
  | zero =>
    refine ⟨fun _ => r.coeff 0, fun x => ?_⟩
    rw [eq_C_of_natDegree_eq_zero (p := r) (by simpa using hr)]
    simp [xEval, xBasis]
  | succ m ih =>
    set N := 2 ^ m
    have hN : 1 ≤ N := Nat.one_le_two_pow
    -- The even and odd coefficients, as polynomials in (u + 1) / 2 = x^2 at u = pi(x).
    let half : ℕ → K[X] := fun e => ∑ i ∈ range N, C (r.coeff (2 * i + e)) * (C 2⁻¹ * (X + 1)) ^ i
    have hdeg : ∀ e, (half e).natDegree < N := fun e => by
      refine (natDegree_sum_le_of_forall_le _ _ (n := N - 1) fun i hi => ?_).trans_lt (by omega)
      refine (natDegree_C_mul_le _ _).trans (natDegree_pow_le.trans ?_)
      have : (C 2⁻¹ * (X + 1) : K[X]).natDegree ≤ 1 :=
        (natDegree_C_mul_le _ _).trans ((natDegree_add_le _ _).trans (max_le natDegree_X_le (by simp)))
      have hi := Finset.mem_range.mp hi
      calc i * _ ≤ i * 1 := Nat.mul_le_mul_left _ this
        _ ≤ N - 1 := by omega
    have heval : ∀ e x, (half e).eval (piX x) = ∑ i ∈ range N, r.coeff (2 * i + e) * (x ^ 2) ^ i := by
      intro e x
      simp only [half, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_add, eval_X, eval_one]
      refine sum_congr rfl fun i _ => ?_
      congr 2
      unfold piX; field_simp; ring
    obtain ⟨dA, hA⟩ := ih (half 0) (hdeg 0)
    obtain ⟨dB, hB⟩ := ih (half 1) (hdeg 1)
    refine ⟨fun k => if k % 2 = 0 then dA (k / 2) else dB (k / 2), fun x => ?_⟩
    rw [xEval_split]
    simp only [show ∀ k, (2 * k) % 2 = 0 by omega, show ∀ k, (2 * k + 1) % 2 ≠ 0 by omega, ↓reduceIte,
      show ∀ k, 2 * k / 2 = k by omega, show ∀ k, (2 * k + 1) / 2 = k by omega, ← hA, ← hB, heval]
    rw [eval_eq_sum_range' (n := 2 * N) (by rw [pow_succ] at hr; omega), sum_range_two_mul, mul_sum]
    congr 1 <;> refine sum_congr rfl fun i _ => ?_
    · simp [pow_mul]
    · rw [pow_succ, pow_mul]; ring

/-- An FFT-basis function of order m + 1 has degree at most 2^m on the circle. -/
theorem isCirclePoly_fftEval (m : ℕ) (c : ℕ → K) : IsCirclePoly (2 ^ m) (fftEval (m + 1) c) := by
  obtain ⟨p, hp, he⟩ := exists_poly_xEval m fun k => c (2 * k)
  obtain ⟨q, hq, ho⟩ := exists_poly_xEval m fun k => c (2 * k + 1)
  exact ⟨p, q, (degree_lt_of_natDegree_lt hp).le, degree_lt_of_natDegree_lt hq,
    fun P => by rw [fftEval_split, he, ho]⟩

/-- Every pair p + y q with p and q of degree below 2^m is an FFT-basis function of order m + 1. -/
theorem exists_fftEval (h2 : (2 : K) ≠ 0) (m : ℕ) (p q : K[X]) (hp : p.natDegree < 2 ^ m)
    (hq : q.natDegree < 2 ^ m) : ∃ c : ℕ → K, ∀ P : C K, p.eval P.x + P.y * q.eval P.x = fftEval (m + 1) c P := by
  obtain ⟨dp, hdp⟩ := exists_xEval h2 m p hp
  obtain ⟨dq, hdq⟩ := exists_xEval h2 m q hq
  refine ⟨fun k => if k % 2 = 0 then dp (k / 2) else dq (k / 2), fun P => ?_⟩
  rw [fftEval_split]
  simp only [show ∀ k, (2 * k) % 2 = 0 by omega, show ∀ k, (2 * k + 1) % 2 ≠ 0 by omega, ↓reduceIte,
    show ∀ k, 2 * k / 2 = k by omega, show ∀ k, (2 * k + 1) / 2 = k by omega, ← hdp, ← hdq]

theorem natDegree_vnPoly (h2 : (2 : K) ≠ 0) (m : ℕ) : (vnPoly m : K[X]).natDegree = 2 ^ m := by
  induction m with
  | zero => simp [vnPoly]
  | succ m ih =>
    rw [vnPoly, ← C_1, ← C_ofNat, natDegree_sub_C,
      natDegree_C_mul h2, natDegree_pow, ih, pow_succ]
    ring

/-- The space of degree 2^m is the FFT space of order m + 1 plus the line of v_(m+1). -/
theorem IsCirclePoly.split_vn (h2 : (2 : K) ≠ 0) {m : ℕ} {F : C K → K} (hF : IsCirclePoly (2 ^ m) F) :
    ∃ (c : ℕ → K) (μ : K), ∀ P, F P = fftEval (m + 1) c P + μ * vn (m + 1) P := by
  classical
  obtain ⟨p, q, hp, hq, hF⟩ := hF
  have hv := natDegree_vnPoly h2 m
  have hv0 : (vnPoly m : K[X]) ≠ 0 := fun h => by simp [h] at hv
  set μ := p.coeff (2 ^ m) / (vnPoly m).leadingCoeff
  set p' := p - C μ * vnPoly m
  have hp' : p'.degree < (2 ^ m : ℕ) := by
    rw [degree_lt_iff_coeff_zero]
    intro k hk
    simp only [p', coeff_sub, coeff_C_mul]
    rcases eq_or_lt_of_le hk with rfl | hk
    · have hlc : (vnPoly m : K[X]).coeff (2 ^ m) = (vnPoly m).leadingCoeff := by rw [leadingCoeff, hv]
      rw [hlc, div_mul_cancel₀ _ (leadingCoeff_ne_zero.mpr hv0), sub_self]
    · rw [coeff_eq_zero_of_degree_lt (hp.trans_lt (by exact_mod_cast hk)),
        coeff_eq_zero_of_natDegree_lt (by rw [hv]; exact hk), mul_zero, sub_zero]
  obtain ⟨c, hc⟩ := exists_fftEval h2 m p' q (natDegree_lt_of_degree_lt (by positivity) hp')
    (natDegree_lt_of_degree_lt (by positivity) hq)
  refine ⟨c, μ, fun P => ?_⟩
  rw [hF, ← hc, vn_eq_eval]
  simp only [p', eval_sub, eval_mul, eval_C]
  ring

/-! ## The FFT space is orthogonal to v_n on a larger standard domain -/

section domain

variable [DecidableEq K] {G : p3_dft.mirror.Gen (K × K)}

theorem bit_add_two_pow_of_lt {j n k : ℕ} (hk : k < n) : bit (j + 2 ^ n) k = bit j k := by
  unfold bit
  rw [show 2 ^ n = 2 * 2 ^ (n - k - 1) * 2 ^ k by rw [← pow_succ', ← pow_add]; congr 1; omega,
    Nat.add_mul_div_right _ _ (by positivity)]
  omega

theorem bit_add_two_pow_self {j n : ℕ} (hj : j < 2 ^ n) : bit (j + 2 ^ n) n = 1 := by
  unfold bit
  rw [Nat.add_div_right _ (by positivity), Nat.div_eq_of_lt hj]

theorem bit_eq_zero_of_lt {m k : ℕ} (h : m < 2 ^ k) : bit m k = 0 := by
  unfold bit; rw [Nat.div_eq_of_lt h]

/-- Multiplying basis function j of order n by v_n gives basis function j + 2^n of a larger order. -/
theorem basis_add_two_pow {n L j : ℕ} (hn : 1 ≤ n) (hnL : n < L) (hj : j < 2 ^ n) (P : C K) :
    basis L (j + 2 ^ n) P = basis n j P * vn n P := by
  unfold basis
  rw [bit_add_two_pow_of_lt (by omega), ← prod_Ico_consecutive _ hn hnL.le,
    prod_eq_prod_Ico_succ_bot hnL, bit_add_two_pow_self hj,
    prod_eq_one (s := Ico (n + 1) L) fun k hk => by
      rw [bit_eq_zero_of_lt (lt_of_lt_of_le (by rw [pow_succ]; omega)
        (Nat.pow_le_pow_right (by norm_num) (mem_Ico.mp hk).1)), pow_zero],
    prod_congr rfl fun k hk => by rw [bit_add_two_pow_of_lt (mem_Ico.mp hk).2]]
  ring

theorem basis_neg {L m : ℕ} (hm : bit m 0 = 1) (P : C K) : basis L m (-P) = -basis L m P := by
  simp only [basis, hm, pow_one, C.neg_y, vn_neg, neg_mul]

theorem bit_log (m : ℕ) (hm : m ≠ 0) : bit m (Nat.log 2 m) = 1 := by
  have h1 := Nat.pow_log_le_self 2 hm
  have h2 := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) m
  unfold bit
  rw [show m / 2 ^ Nat.log 2 m = 1 from le_antisymm
    (Nat.lt_succ_iff.mp ((Nat.div_lt_iff_lt_mul (by positivity)).mpr (by rw [pow_succ] at h2; omega)))
    ((Nat.le_div_iff_mul_le (by positivity)).mpr (by omega))]

/-- Over the standard domain of size 2^L, every FFT basis function but the constant one sums to zero. -/
theorem sum_basis_eq_zero (hV : CircleGenValid G) (h2 : (2 : K) ≠ 0) {L m : ℕ} (hm0 : m ≠ 0) (hm : m < 2 ^ L)
    (hG : L + 1 ≤ G.adicity) :
    ∑ k ∈ range (2 ^ L), basis L m ((2 * k + 1) • genPt G (L + 1)) = 0 := by
  set Q := genPt G (L + 1)
  have hQ : 2 ^ (L + 1) • Q = 0 := genPt_order_zero hV hG
  rcases Nat.mod_two_eq_zero_or_one m with he | ho
  · -- The lowest set bit s >= 1: translating by a point of order 2^s negates the basis function.
    have hex : ∃ s, bit m s = 1 := ⟨_, bit_log m hm0⟩
    set s := Nat.find hex
    have hs : bit m s = 1 := Nat.find_spec hex
    have hlow : ∀ k < s, bit m k = 0 := fun k hk => by
      have := Nat.find_min hex hk
      have : bit m k < 2 := Nat.mod_lt _ (by norm_num)
      omega
    have hs1 : 1 ≤ s := by
      by_contra h
      have : bit m 0 = 0 := by unfold bit; simpa using he
      rw [show s = 0 by omega] at hs; omega
    have hsL : s < L := by
      by_contra h
      rw [bit_eq_zero_of_lt (hm.trans_le (Nat.pow_le_pow_right (by norm_num) (by omega)))] at hs
      omega
    set T := 2 ^ (L + 1 - s) • Q
    have htr : ∀ k, (2 * (k + 2 ^ (L - s)) + 1) • Q = (2 * k + 1) • Q + T := fun k => by
      rw [← add_nsmul, show L + 1 - s = (L - s) + 1 by omega, pow_succ]; congr 1; ring
    have hvn : ∀ k ∈ Ico 1 L, ∀ P : C K, vn k (P + T) ^ bit m k =
        (if k = s then -1 else 1) * vn k P ^ bit m k := fun k hk P => by
      have hk := mem_Ico.mp hk
      have hT : 2 ^ (k - 1) • T = 2 ^ (k - 1 + (L + 1 - s)) • Q := by rw [smul_smul, ← pow_add]
      rcases lt_trichotomy k s with hlt | hks | hgt
      · simp [hlow k hlt, hlt.ne]
      · rw [hks] at hT ⊢
        rw [hs, vn, vn, smul_add, hT, show s - 1 + (L + 1 - s) = L + 1 - 1 by omega,
          genPt_nsmul hV (by omega) hG, add_genPt_one_x hV (by omega)]
        simp
      · rw [vn, vn, smul_add, hT, show k - 1 + (L + 1 - s) = (L + 1) + (k - 1 - s) by omega, pow_add,
          mul_nsmul, hQ, smul_zero, add_zero]
        simp [hgt.ne']
    have hb : ∀ P : C K, basis L m (P + T) = -basis L m P := fun P => by
      have h0 : bit m 0 = 0 := hlow 0 (by omega)
      simp only [basis, h0, pow_zero, one_mul]
      rw [prod_congr rfl fun k hk => hvn k hk P, prod_mul_distrib, prod_ite_eq' (Ico 1 L) s]
      simp [mem_Ico.mpr ⟨hs1, hsL⟩]
    rw [show 2 ^ L = 2 * 2 ^ (L - s) * 2 ^ (s - 1) by
      rw [mul_assoc, ← pow_add, ← pow_succ']; congr 1; omega]
    exact sum_antiperiodic _ _ (fun j => by rw [htr, hb]) _
  · -- An odd index: the basis function is odd under P -> -P, which maps the domain to itself.
    have hbit : bit m 0 = 1 := by unfold bit; simpa using ho
    have hneg : ∀ k ∈ range (2 ^ L), (2 * (2 ^ L - 1 - k) + 1) • Q = -((2 * k + 1) • Q) := fun k hk => by
      have := mem_range.mp hk
      rw [eq_neg_iff_add_eq_zero, ← add_nsmul, show 2 * (2 ^ L - 1 - k) + 1 + (2 * k + 1) = 2 ^ (L + 1) by
        rw [pow_succ]; omega, hQ]
    have hS := sum_range_reflect (fun k => basis L m ((2 * k + 1) • Q)) (2 ^ L)
    rw [sum_congr rfl fun k hk => by rw [hneg k hk, basis_neg hbit], sum_neg_distrib] at hS
    have : (2 : K) * ∑ k ∈ range (2 ^ L), basis L m ((2 * k + 1) • Q) = 0 := by linear_combination -hS
    exact (mul_eq_zero.mp this).resolve_left h2

/-- Over the standard domain of size 2^L, an FFT-basis function of order n < L is orthogonal to v_n. -/
theorem sum_fftEval_mul_vn (hV : CircleGenValid G) (h2 : (2 : K) ≠ 0) {n L : ℕ} (hn : 1 ≤ n) (hnL : n < L)
    (hG : L + 1 ≤ G.adicity) (c : ℕ → K) :
    ∑ k ∈ range (2 ^ L), fftEval n c ((2 * k + 1) • genPt G (L + 1)) * vn n ((2 * k + 1) • genPt G (L + 1)) = 0 := by
  simp only [fftEval, smul_eq_mul, sum_mul]
  rw [sum_comm]
  refine sum_eq_zero fun j hj => ?_
  have hj := mem_range.mp hj
  simp only [mul_right_comm _ (c j), ← basis_add_two_pow hn hnL hj, ← sum_mul]
  rw [sum_basis_eq_zero hV h2 (by positivity) (lt_of_lt_of_le (by rw [pow_succ]; omega)
    (Nat.pow_le_pow_right (by norm_num) hnL)) hG, zero_mul]

/-- A sum over the rows of the circle FFT order is the sum over the natural points. -/
theorem sum_cfft_permute {M : Type _} [AddCommMonoid M] (L : ℕ) (f : ℕ → M) :
    ∑ i ∈ range (2 ^ L), f (p3_circle.ordering.mirror.cfft_permute_index i L) = ∑ k ∈ range (2 ^ L), f k :=
  sum_nbij' (p3_circle.ordering.mirror.cfft_permute_index · L) (p3_circle.ordering.mirror.cfft_permute_index · L)
    (fun i _ => by simpa using cfft_permute_index_lt L i) (fun i _ => by simpa using cfft_permute_index_lt L i)
    (fun i hi => cfft_permute_index_involutive (by simpa using hi))
    (fun i hi => cfft_permute_index_involutive (by simpa using hi)) (fun i _ => rfl)

open p3_circle.ordering.mirror p3_circle.deep_quotient.mirror in
/-- The lambda extraction on a function of degree 2^(n - 1), n = L - lb, read in circle FFT order on the LDE domain.

The function splits as an FFT-basis function of order n plus mu v_n.

The extraction returns that mu, and the FFT-basis function. -/
theorem extract_lambda_circlePoly (hV : CircleGenValid G) (h2 : (2 : K) ≠ 0) {L lb : ℕ} (hlb : 1 ≤ lb)
    (hn : lb + 1 ≤ L) (hG : L + 1 ≤ G.adicity) {F : C K → K} (hF : IsCirclePoly (2 ^ (L - lb - 1)) F) :
    ∃ (c : ℕ → K) (μ : K), (∀ P, F P = fftEval (L - lb) c P + μ * vn (L - lb) P) ∧
      extract_lambda G ((List.range (2 ^ L)).map fun i => F ((2 * cfft_permute_index i L + 1) • genPt G (L + 1))) lb =
        some (μ, (List.range (2 ^ L)).map fun i =>
          fftEval (L - lb) c ((2 * cfft_permute_index i L + 1) • genPt G (L + 1))) := by
  obtain ⟨c, μ, hc⟩ := hF.split_vn h2
  rw [show L - lb - 1 + 1 = L - lb by omega] at hc
  refine ⟨c, μ, hc, ?_⟩
  set pt : ℕ → C K := fun k => (2 * k + 1) • genPt G (L + 1)
  have hlen : ((List.range (2 ^ L)).map fun i => F (pt (cfft_permute_index i L))).length = 2 ^ L := by simp
  have hget : ∀ i ∈ range (2 ^ L), ((List.range (2 ^ L)).map fun i => F (pt (cfft_permute_index i L))).getD i 0 =
      F (pt (cfft_permute_index i L)) := fun i hi => by
    rw [List.getD_eq_getElem _ _ (by simpa using hi)]; simp
  have hlam : (∑ i ∈ range (2 ^ L), ((List.range (2 ^ L)).map fun i => F (pt (cfft_permute_index i L))).getD i 0 *
      vdAt G L lb i) * ((2 : K) ^ (L - 1))⁻¹ = μ := by
    rw [sum_congr rfl fun i hi => by rw [hget i hi]]
    simp only [vdAt]
    rw [sum_cfft_permute L fun k => F (pt k) * vn (L - lb) (pt k)]
    simp only [hc, add_mul, sum_add_distrib, pt, sum_fftEval_mul_vn hV h2 (by omega : 1 ≤ L - lb)
      (by omega : L - lb < L) hG, zero_add, mul_assoc, ← mul_sum, ← pow_two, sum_vn_sq hV h2 hlb hn hG]
    field_simp
  rw [extract_lambda_eq hV hlb hn hG h2 _ hlen, hlam]
  congr 2
  refine List.map_congr_left fun i hi => ?_
  rw [hget i (by simpa using hi), vdAt, hc]
  ring

end domain

end Plonky3Lean.Proofs.Circle
