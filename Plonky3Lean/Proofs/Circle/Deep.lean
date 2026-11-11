module

public import P3Circle.DeepQuotient
public import Plonky3Lean.Proofs.Circle.Folding
public import Plonky3Lean.Proofs.Circle.Selectors

@[expose] public section

/-!
# p3-circle: the DEEP quotient on the circle

The crate's single-point vanishing function is v(x) = re + i im, where

```text
    re = 1 - (x - zeta).x,     im = (x - zeta).y
```

It is the complex conjugate of the paper's v_P of equation (11), with the same single zero at zeta.

On the circle, re^2 + im^2 = 2 re.

So 1 / v = (re - i im) / (2 re) = 1/2 - i im / (2 re).

For g = f(x) - f(zeta), the quotient q = g / v of Proposition 4 then has

```text
    Re(q) = g / 2,     Im(q) = -g im / (2 re),     q v = g
```

The row reduction is sum_j alpha^j Re(q_j) + alpha^(W + j) Im(q_j).

It uses two powers of alpha per column.

The prover's accumulated reduction and the verifier's row reduction agree at every query point.
-/

namespace Plonky3Lean.Proofs.Circle

open Plonky3Lean.Spec.Circle p3_circle.point.mirror p3_circle.deep_quotient.mirror Finset

set_option linter.unusedSectionVars false

variable {K : Type _} [Field K] [DecidableEq K]

/-- The crate's v_p at x, toward zeta: (1 - (zeta - x).x, (zeta - x).y). -/
theorem v_p_eq (P Q : C K) : Point.v_p (ofC P) (ofC Q) = (1 - (Q - P).x, (Q - P).y) := by
  simp only [Point.v_p, neg_ofC, add_ofC, ofC_x, ofC_y, C.add_x, C.add_y, C.neg_x, C.neg_y, C.sub_x,
    C.sub_y, Prod.mk.injEq]
  constructor <;> ring

/-- The circle identity: |v|^2 = re^2 + im^2 = 2 re. -/
theorem v_p_norm (P Q : C K) :
    (Point.v_p (ofC P) (ofC Q)).1 ^ 2 + (Point.v_p (ofC P) (ofC Q)).2 ^ 2 =
      2 * (Point.v_p (ofC P) (ofC Q)).1 := by
  rw [v_p_eq]; linear_combination (Q - P).eq

/-- The denominator 2 re vanishes exactly when the query point is the opening point. -/
theorem v_p_denom_eq_zero (h2 : (2 : K) ≠ 0) (P Q : C K) :
    (Point.v_p (ofC P) (ofC Q)).1 + (Point.v_p (ofC P) (ofC Q)).1 = 0 ↔ P = Q := by
  rw [v_p_eq, ← two_mul, mul_eq_zero, or_iff_right h2, sub_eq_zero]
  constructor
  · intro h
    have hy : (Q - P).y ^ 2 = 0 := by linear_combination (Q - P).eq + (1 + (Q - P).x) * h
    have hd : Q - P = 0 := C.ext h.symm (by simpa using pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hy)
    exact (sub_eq_zero.mp hd).symm
  · rintro rfl; simp


/-! ## The row reduction -/

/-- The quotient g / v as a formal complex number: g (re - i im) / (re^2 + im^2). -/
def cquot (g : K) (v : K × K) : K × K :=
  (g * v.1 / (v.1 ^ 2 + v.2 ^ 2), -(g * v.2) / (v.1 ^ 2 + v.2 ^ 2))

/-- Proposition 4: the quotient times v is g, when v is nonzero. -/
theorem cquot_mul (g : K) (v : K × K) (hv : v.1 ^ 2 + v.2 ^ 2 ≠ 0) :
    ((cquot g v).1 * v.1 - (cquot g v).2 * v.2, (cquot g v).1 * v.2 + (cquot g v).2 * v.1) = (g, 0) := by
  simp only [cquot, Prod.mk.injEq]
  constructor <;> field_simp <;> ring

theorem dot_product_sub (xs ps qs : List K) (hpq : ps.length = qs.length) (has : ps.length ≤ xs.length) :
    dot_product xs ((ps.zip qs).map fun p => -p.2 + p.1) = dot_product xs ps - dot_product xs qs := by
  induction ps generalizing xs qs with
  | nil => cases qs <;> simp_all [dot_product]
  | cons p ps ih =>
    cases qs with
    | nil => simp at hpq
    | cons q qs =>
      cases xs with
      | nil => simp at has
      | cons a xs =>
        simp only [dot_product, List.zip_cons_cons, List.map_cons, List.sum_cons] at ih ⊢
        rw [ih xs qs (by simpa using hpq) (by simpa using has)]
        ring

theorem dot_product_range (f : ℕ → K) (ps : List K) :
    dot_product ((List.range ps.length).map f) ps = ∑ j ∈ range ps.length, f j * ps.getD j 0 := by
  induction ps generalizing f with
  | nil => simp [dot_product]
  | cons p ps ih =>
    rw [List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_map, sum_range_succ']
    have := ih (f ∘ Nat.succ)
    simp only [dot_product, List.zip_cons_cons, List.map_cons, List.sum_cons] at this ⊢
    rw [this]
    simp [add_comm]

/-- The verifier's row reduction.

It is none exactly when the query point is the opening point.

Otherwise it is (re - alpha^W im) / (2 re) times sum_j alpha_j (p_j(x) - p_j(zeta)). -/
theorem deep_quotient_reduce_row_eq (h2 : (2 : K) ≠ 0) (αW : K) (αs : List K) (P Q : C K)
    (ps qs : List K) :
    deep_quotient_reduce_row αW αs (ofC P) (ofC Q) ps qs =
      if P = Q then none else some
        (((Point.v_p (ofC P) (ofC Q)).1 - αW * (Point.v_p (ofC P) (ofC Q)).2) *
          ((Point.v_p (ofC P) (ofC Q)).1 + (Point.v_p (ofC P) (ofC Q)).1)⁻¹ *
          dot_product αs ((ps.zip qs).map fun p => -p.2 + p.1)) := by
  unfold deep_quotient_reduce_row deep_quotient_vanishing_part tryInverse
  by_cases h : P = Q
  · simp [h, (v_p_denom_eq_zero h2 Q Q).mpr rfl]
  · simp [h, mt (v_p_denom_eq_zero h2 P Q).mp h]

/-- The row reduction is sum_j alpha^j Re(q_j) + alpha^(W + j) Im(q_j).

Here q_j is the quotient (p_j(x) - p_j(zeta)) / v. -/
theorem reduce_row_eq_re_im (h2 : (2 : K) ≠ 0) (α : K) (P Q : C K) (hPQ : P ≠ Q) (ps qs : List K)
    (hpq : ps.length = qs.length) :
    deep_quotient_reduce_row (α ^ ps.length) ((List.range ps.length).map (α ^ ·)) (ofC P) (ofC Q) ps qs =
      some (∑ j ∈ range ps.length, (α ^ j * (cquot (ps.getD j 0 - qs.getD j 0) (Point.v_p (ofC P) (ofC Q))).1 +
        α ^ (ps.length + j) * (cquot (ps.getD j 0 - qs.getD j 0) (Point.v_p (ofC P) (ofC Q))).2)) := by
  rw [deep_quotient_reduce_row_eq h2, ite_eq_right hPQ, Option.some.injEq]
  set v := Point.v_p (ofC P) (ofC Q)
  have hn : v.1 ^ 2 + v.2 ^ 2 = 2 * v.1 := v_p_norm P Q
  have hre : v.1 + v.1 ≠ 0 := mt (v_p_denom_eq_zero h2 P Q).mp hPQ
  have hdot : dot_product ((List.range ps.length).map (α ^ ·)) ((ps.zip qs).map fun p => -p.2 + p.1) =
      ∑ j ∈ range ps.length, α ^ j * (ps.getD j 0 - qs.getD j 0) := by
    rw [dot_product_sub _ _ _ hpq (by simp), dot_product_range]
    have e := dot_product_range (fun j => α ^ j) qs
    rw [← hpq] at e
    rw [e, ← sum_sub_distrib]
    exact sum_congr rfl fun j _ => by ring
  rw [hdot, mul_sum]
  refine sum_congr rfl fun j _ => ?_
  simp only [cquot, hn, pow_add, show v.1 + v.1 = 2 * v.1 by ring]
  ring


/-! ## The prover's accumulation -/

/-- The prover's vanishing parts are im / (2 re) at every domain point.

They panic exactly when the opening point is a domain point. -/
theorem compute_vanishing_parts_eq (h2 : (2 : K) ≠ 0) (pts : List (C K)) (Q : C K) :
    compute_vanishing_parts (pts.map ofC) (ofC Q) =
      if Q ∈ pts then none else some (pts.map fun P =>
        (Point.v_p (ofC P) (ofC Q)).2 * ((Point.v_p (ofC P) (ofC Q)).1 + (Point.v_p (ofC P) (ofC Q)).1)⁻¹) := by
  unfold compute_vanishing_parts p3_commit.domain.mirror.batchInv
  simp only [List.map_map, Function.comp_def]
  by_cases hQ : Q ∈ pts
  · have hz : ¬ ∀ x ∈ pts.map (fun P => (Point.v_p (ofC P) (ofC Q)).1 + (Point.v_p (ofC P) (ofC Q)).1),
        x ≠ 0 :=
      fun h => h _ (List.mem_map_of_mem hQ) ((v_p_denom_eq_zero h2 Q Q).mpr rfl)
    simp only [hz, hQ, ↓reduceIte]
    rfl
  · have hnz : ∀ x ∈ pts.map (fun P => (Point.v_p (ofC P) (ofC Q)).1 + (Point.v_p (ofC P) (ofC Q)).1),
        x ≠ 0 := by
      intro d hd
      obtain ⟨P, hP, rfl⟩ := List.mem_map.mp hd
      exact mt (v_p_denom_eq_zero h2 P Q).mp (fun h => hQ (h ▸ hP))
    rw [ite_eq_left hnz, ite_eq_right hQ]
    simp only [Option.bind_eq_bind, Option.bind_some]
    rw [zip_map_map, List.map_map]
    rfl

/-- At a query point, the prover's accumulated DEEP quotient adds an offset times the row reduction. -/
theorem accumulate_eq_reduce_row (αoff αW : K) (αs ps qs : List K) (P Q : C K) (hPQ : P ≠ Q)
    (h2 : (2 : K) ≠ 0) (hpq : ps.length = qs.length) (has : ps.length ≤ αs.length) :
    (αoff / 2 - αoff * αW * ((Point.v_p (ofC P) (ofC Q)).2 *
        ((Point.v_p (ofC P) (ofC Q)).1 + (Point.v_p (ofC P) (ofC Q)).1)⁻¹)) *
      (dot_product αs ps - dot_product αs qs) =
    αoff * ((deep_quotient_reduce_row αW αs (ofC P) (ofC Q) ps qs).getD 0) := by
  rw [deep_quotient_reduce_row_eq h2, ite_eq_right hPQ, Option.getD_some, dot_product_sub _ _ _ hpq has]
  have hre := mt (v_p_denom_eq_zero h2 P Q).mp hPQ
  set v := Point.v_p (ofC P) (ofC Q)
  have hv1 : v.1 ≠ 0 := fun h => hre (by rw [h, add_zero])
  rw [show v.1 + v.1 = 2 * v.1 by ring]
  field_simp


/-! ## The lambda extraction -/

section lambda

/-- A sum of 2 h m terms is zero when shifting by h negates every term. -/
theorem sum_antiperiodic {M : Type _} [AddCommGroup M] (f : ℕ → M) (h : ℕ) (hf : ∀ j, f (j + h) = -f j)
    (m : ℕ) : ∑ j ∈ range (2 * h * m), f j = 0 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show 2 * h * (m + 1) = 2 * h * m + (h + h) by ring, sum_range_add, ih, zero_add, sum_range_add]
    rw [← sum_add_distrib]
    exact sum_eq_zero fun j _ => by rw [show 2 * h * m + (h + j) = (2 * h * m + j) + h by ring, hf,
      add_neg_cancel]

variable {G : p3_dft.mirror.Gen (K × K)}

theorem vn_succ_eq (n : ℕ) (hn : 1 ≤ n) (P : C K) : vn (n + 1) P = 2 * vn n P ^ 2 - 1 := by
  rw [vn, vn, Nat.add_sub_cancel, ← C.two_nsmul_x, smul_smul, ← pow_succ']
  congr 3; omega

theorem vn_sq (h2 : (2 : K) ≠ 0) (n : ℕ) (hn : 1 ≤ n) (P : C K) :
    vn n P ^ 2 = (2 : K)⁻¹ * (1 + vn (n + 1) P) := by
  rw [vn_succ_eq n hn]; field_simp; ring

/-- Take a point of order 2^(lb + 1), with lb >= 1, and L >= lb.

The x-coordinates of its odd multiples sum to zero over 2^L terms. -/
theorem sum_odd_x_eq_zero (hV : CircleGenValid G) {lb L : ℕ} (hlb : 1 ≤ lb) (hL : lb ≤ L)
    (hG : lb + 1 ≤ G.adicity) :
    ∑ j ∈ range (2 ^ L), ((2 * j + 1) • genPt G (lb + 1)).x = 0 := by
  have h1 : 2 ^ lb • genPt G (lb + 1) = genPt G 1 := by
    have := genPt_nsmul hV (j := 1) (k := lb + 1) (by omega) hG; rwa [Nat.add_sub_cancel] at this
  have hsplit : 2 ^ L = 2 * 2 ^ (lb - 1) * 2 ^ (L - lb) := by
    rw [← pow_succ', ← pow_add]; congr 1; omega
  rw [hsplit]
  refine sum_antiperiodic _ _ (fun j => ?_) _
  rw [show 2 * (j + 2 ^ (lb - 1)) + 1 = (2 * j + 1) + 2 ^ lb by
      rw [show 2 ^ lb = 2 * 2 ^ (lb - 1) by rw [← pow_succ']; congr 1; omega]; ring,
    add_nsmul, h1, add_genPt_one_x hV (by omega)]

theorem genPt_order_zero (hV : CircleGenValid G) {k : ℕ} (hk : k ≤ G.adicity) : 2 ^ k • genPt G k = 0 := by
  have := genPt_nsmul hV (j := 0) (k := k) (by omega) hk
  rwa [Nat.sub_zero, genPt_zero hV] at this

/-- Take n = L - lb with lb >= 1 and n >= 1.

Over the standard domain of size 2^L, the squares of v_n at the points sum to 2^(L - 1). -/
theorem sum_vn_sq (hV : CircleGenValid G) (h2 : (2 : K) ≠ 0) {L lb : ℕ} (hlb : 1 ≤ lb) (hn : lb + 1 ≤ L)
    (hG : L + 1 ≤ G.adicity) :
    ∑ j ∈ range (2 ^ L), vn (L - lb) ((2 * j + 1) • genPt G (L + 1)) ^ 2 = 2 ^ (L - 1) := by
  have hQ : 2 ^ (L - lb) • genPt G (L + 1) = genPt G (lb + 1) := by
    have := genPt_nsmul hV (j := lb + 1) (k := L + 1) (by omega) hG
    rwa [show L + 1 - (lb + 1) = L - lb by omega] at this
  simp only [vn_sq h2 (L - lb) (by omega), ← mul_sum, sum_add_distrib, sum_const, card_range,
    nsmul_eq_mul, mul_one]
  have hs : ∑ j ∈ range (2 ^ L), vn (L - lb + 1) ((2 * j + 1) • genPt G (L + 1)) = 0 := by
    rw [← sum_odd_x_eq_zero hV hlb (by omega) (by omega) (L := L)]
    refine sum_congr rfl fun j _ => ?_
    rw [vn, Nat.add_sub_cancel, smul_comm, hQ]
  rw [hs, add_zero, show L = (L - 1) + 1 by omega, pow_succ]
  push_cast
  field_simp

/-- Take the vanishing polynomial v_n at the natural point k of the LDE domain.

It only depends on the zigzag of k mod 2 2^lb. -/
theorem vn_zigzag (hV : CircleGenValid G) {L lb : ℕ} (hn : lb + 1 ≤ L) (hG : L + 1 ≤ G.adicity) (k : ℕ) :
    vn (L - lb) ((2 * (if k % (2 * 2 ^ lb) < 2 ^ lb then k % (2 * 2 ^ lb)
      else 2 * 2 ^ lb - 1 - k % (2 * 2 ^ lb)) + 1) • genPt G (L + 1)) =
      vn (L - lb) ((2 * k + 1) • genPt G (L + 1)) := by
  set Q := genPt G (L + 1)
  have hQ : 2 ^ (L - lb - 1) • Q = genPt G (lb + 2) := by
    have := genPt_nsmul hV (j := lb + 2) (k := L + 1) (by omega) hG
    rwa [show L + 1 - (lb + 2) = L - lb - 1 by omega] at this
  have h0 : (4 * 2 ^ lb) • genPt G (lb + 2) = 0 := by
    rw [show 4 * 2 ^ lb = 2 ^ (lb + 2) by ring]; exact genPt_order_zero hV (by omega)
  have hb := Nat.div_add_mod k (2 * 2 ^ lb)
  have hm := Nat.mod_lt k (show 2 * 2 ^ lb > 0 by positivity)
  set m := k % (2 * 2 ^ lb)
  have hk : (2 * k + 1) • genPt G (lb + 2) = (2 * m + 1) • genPt G (lb + 2) := by
    have e : 2 * k + 1 = (2 * m + 1) + (4 * 2 ^ lb) * (k / (2 * 2 ^ lb)) := by
      nth_rewrite 1 [← hb]; ring
    rw [e, add_nsmul, mul_nsmul, h0, smul_zero, add_zero]
  simp only [vn, smul_comm (2 ^ (L - lb - 1)) _ Q, hQ, hk]
  split_ifs with h
  · rfl
  · have hneg : (2 * (2 * 2 ^ lb - 1 - m) + 1) • genPt G (lb + 2) = -((2 * m + 1) • genPt G (lb + 2)) := by
      rw [eq_neg_iff_add_eq_zero, ← add_nsmul, show 2 * (2 * 2 ^ lb - 1 - m) + 1 + (2 * m + 1) = 4 * 2 ^ lb by
        omega, h0]
    rw [hneg, C.neg_x]

theorem list_sum_map_range (f : ℕ → K) (n : ℕ) : ((List.range n).map f).sum = ∑ i ∈ range n, f i := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.range_succ, List.map_append, List.sum_append, ih, sum_range_succ]; simp

/-- The value of the vanishing polynomial the lambda extraction reads at row i.

It is v_n at the natural point sigma(i). -/
noncomputable def vdAt (G : p3_dft.mirror.Gen (K × K)) (L lb i : ℕ) : K :=
  vn (L - lb) ((2 * p3_circle.ordering.mirror.cfft_permute_index i L + 1) • genPt G (L + 1))

/-- Run the lambda extraction on an LDE of 2^L values, 2^lb times the trace size.

It returns lambda = <lde, v_d> / 2^(L - 1) and lde - lambda v_d.

Here v_d is v_n on the LDE domain in circle FFT order. -/
theorem extract_lambda_eq (hV : CircleGenValid G) {L lb : ℕ} (hlb : 1 ≤ lb) (hn : lb + 1 ≤ L)
    (hG : L + 1 ≤ G.adicity) (h2 : (2 : K) ≠ 0) (lde : List K) (hlen : lde.length = 2 ^ L) :
    extract_lambda G lde lb = some
      ((∑ i ∈ range (2 ^ L), lde.getD i 0 * vdAt G L lb i) * ((2 : K) ^ (L - 1))⁻¹,
        (List.range (2 ^ L)).map fun i => lde.getD i 0 -
          (∑ i ∈ range (2 ^ L), lde.getD i 0 * vdAt G L lb i) * ((2 : K) ^ (L - 1))⁻¹ * vdAt G L lb i) := by
  have hpts := standard_points hV (n := L) (by omega) hG
  have htake : ((List.range (2 ^ L)).map fun k => ofC ((2 * k + 1) • genPt G (L + 1))).take (2 ^ lb) =
      (List.range (2 ^ lb)).map fun k => ofC ((2 * k + 1) • genPt G (L + 1)) := by
    rw [← List.map_take, List.take_range, min_eq_left (Nat.pow_le_pow_right (by norm_num) (by omega))]
  have hinit : ((List.range (2 ^ lb)).map fun k => ofC ((2 * k + 1) • genPt G (L + 1))).mapM
      (fun p => Point.v_n p (L - lb)) =
      some ((List.range (2 ^ lb)).map fun k => vn (L - lb) ((2 * k + 1) • genPt G (L + 1))) := by
    rw [List.mapM_map]
    exact mapM_eq_some_map _ _ _ fun k _ => by simp [v_n_ofC, show 1 ≤ L - lb by omega]
  have hat : ∀ i, ((List.range (2 ^ lb)).map fun k => vn (L - lb) ((2 * k + 1) • genPt G (L + 1))).getD
      (if p3_circle.ordering.mirror.cfft_permute_index i L % (2 * 2 ^ lb) < 2 ^ lb then
        p3_circle.ordering.mirror.cfft_permute_index i L % (2 * 2 ^ lb)
      else 2 * 2 ^ lb - 1 - p3_circle.ordering.mirror.cfft_permute_index i L % (2 * 2 ^ lb)) 0 =
      vdAt G L lb i := by
    intro i
    have hm := Nat.mod_lt (p3_circle.ordering.mirror.cfft_permute_index i L)
      (show 2 * 2 ^ lb > 0 by positivity)
    rw [List.getD_eq_getElem _ _ (by simp; split_ifs <;> omega), List.getElem_map, List.getElem_range,
      vn_zigzag hV hn hG, vdAt]
  have hinv : p3_commit.domain.mirror.inv ((2 : K) ^ (L - 1)) = some ((2 : K) ^ (L - 1))⁻¹ := by
    simp [p3_commit.domain.mirror.inv, h2]
  unfold extract_lambda
  simp only [hlen, Plonky3Lean.Proofs.Dft.log2Strict_pow, Option.bind_eq_bind, Option.bind_some,
    show ¬ L < lb by omega, ↓reduceIte, standard_eq hV L hG, hpts, htake, hinit,
    show ¬ L < 1 by omega, hinv, hat, list_sum_map_range]

/-- After the extraction, the LDE is orthogonal to v_d on the LDE domain. -/
theorem extract_lambda_orthogonal (hV : CircleGenValid G) {L lb : ℕ} (hlb : 1 ≤ lb) (hn : lb + 1 ≤ L)
    (hG : L + 1 ≤ G.adicity) (h2 : (2 : K) ≠ 0) (lde : List K) :
    ∑ i ∈ range (2 ^ L), (lde.getD i 0 -
      (∑ i ∈ range (2 ^ L), lde.getD i 0 * vdAt G L lb i) * ((2 : K) ^ (L - 1))⁻¹ * vdAt G L lb i) *
        vdAt G L lb i = 0 := by
  have hsq : ∑ i ∈ range (2 ^ L), vdAt G L lb i ^ 2 = 2 ^ (L - 1) := by
    rw [← sum_vn_sq hV h2 hlb hn hG]
    refine sum_nbij' (p3_circle.ordering.mirror.cfft_permute_index · L)
      (p3_circle.ordering.mirror.cfft_permute_index · L) (fun i _ => by simpa using cfft_permute_index_lt L i)
      (fun i _ => by simpa using cfft_permute_index_lt L i)
      (fun i hi => cfft_permute_index_involutive (by simpa using hi))
      (fun i hi => cfft_permute_index_involutive (by simpa using hi)) (fun i _ => rfl)
  simp only [sub_mul, sum_sub_distrib, mul_assoc, ← mul_sum]
  rw [show ∑ i ∈ range (2 ^ L), vdAt G L lb i * vdAt G L lb i = 2 ^ (L - 1) by
    rw [← hsq]; exact sum_congr rfl fun i _ => by ring]
  rw [inv_mul_cancel₀ (pow_ne_zero _ h2), mul_one, sub_self]

end lambda

end Plonky3Lean.Proofs.Circle
