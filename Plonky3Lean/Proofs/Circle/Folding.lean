module

public import P3Circle.Folding
public import Plonky3Lean.Proofs.Circle.CfftStd

@[expose] public section

/-!
# p3-circle: circle FRI folding

The first layer folds along the involution J, with y as the odd reference function.

This follows equations (14) and (15):

```text
    f(P) = f_0(x) + y f_1(x),     fold(f) = f_0 + beta f_1
```

The later layers fold along x -> -x, with x as the odd reference function.

This follows equations (17) and (18):

```text
    g(x) = g_0(pi(x)) + x g_1(pi(x)),     fold(g) = g_0 + beta g_1
```

In coefficients, both folds keep the even coefficients plus beta times the odd ones.

This is the arity-2 fold of FRI, with the squaring map pi(x) = 2 x^2 - 1 in place of x^2.
-/

namespace Plonky3Lean.Proofs.Circle

open Plonky3Lean.Spec.Circle Plonky3Lean.Proofs.Dft Finset

set_option linter.unusedSectionVars false

local notation "rev" => Plonky3Lean.Spec.Matrix.bitRev

variable {K : Type _} [Field K]

/-! ## The x-only basis -/

theorem piX_iterate_succ (t : ℕ) (x : K) : piX^[t + 1] x = piX^[t] (piX x) :=
  Function.iterate_succ_apply piX t x

theorem bit_two_mul_add (k e t : ℕ) (he : e < 2) : bit (2 * k + e) (t + 1) = bit k t := by
  unfold bit
  rw [pow_succ', ← Nat.div_div_eq_div_mul, show (2 * k + e) / 2 = k by omega]

theorem bit_two_mul_add_zero (k e : ℕ) (he : e < 2) : bit (2 * k + e) 0 = e := by
  unfold bit; simp; omega

theorem xBasis_split (m k e : ℕ) (he : e < 2) (x : K) :
    xBasis (m + 1) (2 * k + e) x = x ^ e * xBasis m k (piX x) := by
  unfold xBasis
  rw [prod_range_succ']
  simp only [Function.iterate_zero, id_eq, bit_two_mul_add_zero k e he, piX_iterate_succ,
    bit_two_mul_add k e _ he]
  ring

theorem xEval_split (m : ℕ) (d : ℕ → K) (x : K) :
    xEval (m + 1) d x = xEval m (fun k => d (2 * k)) (piX x) + x * xEval m (fun k => d (2 * k + 1)) (piX x) := by
  unfold xEval
  rw [pow_succ', sum_range_two_mul, mul_sum]
  congr 1
  · refine sum_congr rfl fun k _ => ?_
    rw [show 2 * k = 2 * k + 0 from rfl, xBasis_split m k 0 (by norm_num)]; simp
  · refine sum_congr rfl fun k _ => ?_
    rw [xBasis_split m k 1 (by norm_num)]; simp only [smul_eq_mul]; ring

theorem piX_neg (x : K) : piX (-x) = piX x := by simp [piX]

/-- The x-fold, equations (17) to (19).

The fold of the values at x and -x is the even part plus beta times the odd part, at pi(x). -/
theorem foldPair_xEval (h2 : (2 : K) ≠ 0) {x : K} (hx : x ≠ 0) (m : ℕ) (d : ℕ → K) (β : K) :
    foldPair x β (xEval (m + 1) d x) (xEval (m + 1) d (-x)) =
      xEval m (fun k => d (2 * k) + β * d (2 * k + 1)) (piX x) := by
  rw [xEval_split, xEval_split, piX_neg, foldPair]
  have : xEval m (fun k => d (2 * k) + β * d (2 * k + 1)) (piX x) =
      xEval m (fun k => d (2 * k)) (piX x) + β * xEval m (fun k => d (2 * k + 1)) (piX x) := by
    unfold xEval; rw [mul_sum, ← sum_add_distrib]
    exact sum_congr rfl fun k _ => by simp only [smul_eq_mul]; ring
  rw [this, smul_eq_mul, smul_eq_mul]
  field_simp
  ring

/-! ## The first layer -/

theorem two_pow_nsmul_x (P : C K) (t : ℕ) : (2 ^ t • P).x = piX^[t] P.x := by
  induction t generalizing P with
  | zero => simp
  | succ t ih =>
    rw [pow_succ', mul_nsmul, ih, piX_iterate_succ, C.two_nsmul_x]
    rfl


theorem basis_split (m k e : ℕ) (he : e < 2) (P : C K) :
    basis (m + 1) (2 * k + e) P = P.y ^ e * xBasis m k P.x := by
  unfold basis xBasis
  rw [prod_Ico_eq_prod_range, Nat.add_sub_cancel, bit_two_mul_add_zero k e he]
  congr 1
  refine prod_congr rfl fun t _ => ?_
  rw [add_comm 1 t, bit_two_mul_add k e t he, vn, Nat.add_sub_cancel, two_pow_nsmul_x]

/-- f = f_0(x) + y f_1(x), equation (16), in coefficients: the even and the odd coefficients. -/
theorem fftEval_split (m : ℕ) (c : ℕ → K) (P : C K) :
    fftEval (m + 1) c P = xEval m (fun k => c (2 * k)) P.x + P.y * xEval m (fun k => c (2 * k + 1)) P.x := by
  unfold fftEval xEval
  rw [pow_succ', sum_range_two_mul, mul_sum]
  congr 1
  · refine sum_congr rfl fun k _ => ?_
    rw [show 2 * k = 2 * k + 0 from rfl, basis_split m k 0 (by norm_num)]; simp
  · refine sum_congr rfl fun k _ => ?_
    rw [basis_split m k 1 (by norm_num)]; simp only [smul_eq_mul]; ring

/-- The first-layer fold, equations (14) to (16).

The fold of the values at P and J(P) is the even part plus beta times the odd part, at P.x. -/
theorem foldPair_fftEval (h2 : (2 : K) ≠ 0) {P : C K} (hy : P.y ≠ 0) (m : ℕ) (c : ℕ → K) (β : K) :
    foldPair P.y β (fftEval (m + 1) c P) (fftEval (m + 1) c (-P)) =
      xEval m (fun k => c (2 * k) + β * c (2 * k + 1)) P.x := by
  rw [fftEval_split, fftEval_split, C.neg_x, C.neg_y, foldPair]
  have : xEval m (fun k => c (2 * k) + β * c (2 * k + 1)) P.x =
      xEval m (fun k => c (2 * k)) P.x + β * xEval m (fun k => c (2 * k + 1)) P.x := by
    unfold xEval; rw [mul_sum, ← sum_add_distrib]
    exact sum_congr rfl fun k _ => by simp only [smul_eq_mul]; ring
  rw [this, smul_eq_mul, smul_eq_mul]
  field_simp
  ring


/-! ## The code -/

section code

variable [DecidableEq K] {G : p3_dft.mirror.Gen (K × K)}

open p3_circle.point.mirror p3_circle.domain.mirror p3_circle.cfft.mirror p3_circle.folding.mirror
  p3_commit.domain.mirror

theorem batchInv_eq {l : List K} (h : ∀ x ∈ l, x ≠ 0) : batchInv l = some (l.map (·⁻¹)) := by
  unfold batchInv; rw [ite_eq_left h]

/-- The y-twiddles of a twin coset: the y-coordinates of its half coset, in bit-reversed order. -/
theorem y_twiddles_eq (hV : CircleGenValid G) {n : ℕ} (S : C K) (hn : 1 ≤ n) (hG : n - 1 ≤ G.adicity) :
    y_twiddles G ⟨n, ofC S⟩ =
      some ((List.range (2 ^ (n - 1))).map fun b => (S + rev (n - 1) b • genPt G (n - 1)).y) := by
  simp only [y_twiddles, CircleDomain.coset0, subgroup_generator_eq hV ⟨n, ofC S⟩ hn hG,
    Option.bind_eq_bind, Option.bind_some, chain_ofC, List.map_map]
  exact congrArg some (revList_map_range 0 (fun i => (S + i • genPt G (n - 1)).y) (n - 1))

/-- The x-twiddles of layer 0 of a twin coset.

They are the x-coordinates of its first 2^(n-2) half-coset points, in bit-reversed order. -/
theorem x_twiddles_zero_eq (hV : CircleGenValid G) {n : ℕ} (S : C K) (hn : 2 ≤ n)
    (hG : n - 1 ≤ G.adicity) :
    x_twiddles G ⟨n, ofC S⟩ 0 =
      some ((List.range (2 ^ (n - 2))).map fun c => (S + rev (n - 2) c • genPt G (n - 1)).x) := by
  simp only [x_twiddles, subgroup_generator_eq hV ⟨n, ofC S⟩ (show 1 ≤ n by omega) hG, Option.bind_eq_bind,
    Option.bind_some, pow_zero, mul_ofC, one_nsmul, show ¬ n < 0 + 2 by omega, ↓reduceIte,
    Nat.sub_zero, chain_ofC, List.map_map]
  exact congrArg some (revList_map_range 0 (fun i => (S + i • genPt G (n - 1)).x) (n - 2))

theorem nth_x_twiddle_eq (hV : CircleGenValid G) {n : ℕ} (S : C K) (hn : 1 ≤ n)
    (hG : n - 1 ≤ G.adicity) (idx : ℕ) :
    nth_x_twiddle G ⟨n, ofC S⟩ idx = some ((S + idx • genPt G (n - 1)).x) := by
  simp [nth_x_twiddle, subgroup_generator_eq hV ⟨n, ofC S⟩ hn hG, mul_ofC, add_ofC]

/-- The code's fold of a pair with an inverted twiddle is the paper's fold. -/
theorem fold_formula (lo hi t β : K) :
    (lo + hi + β * ((lo - hi) * t⁻¹)) / 2 = foldPair t β lo hi := by
  simp only [foldPair, smul_eq_mul]
  by_cases ht : t = 0
  · simp [ht, div_eq_inv_mul]
  · field_simp

theorem fold_eq (rows : List (K × K)) (β : K) (ts : List K) (hlen : rows.length = ts.length) :
    p3_circle.folding.mirror.fold rows β (ts.map (·⁻¹)) =
      some ((rows.zip ts).map fun r => foldPair r.2 β r.1.1 r.1.2) := by
  rw [p3_circle.folding.mirror.fold, ite_eq_right (by simpa using hlen), List.zip_map_right, List.map_map]
  congr 1
  exact List.map_congr_left fun r _ => fold_formula _ _ _ _

theorem two_nsmul_genPt (hV : CircleGenValid G) {k : ℕ} (hk : k + 1 ≤ G.adicity) :
    2 • genPt G (k + 1) = genPt G k := by
  have := genPt_nsmul hV (show k ≤ k + 1 by omega) hk; rwa [Nat.add_sub_cancel_left, pow_one] at this

theorem add_genPt_one_x (hV : CircleGenValid G) (h1 : 1 ≤ G.adicity) (P : C K) :
    (P + genPt G 1).x = -P.x := by
  rw [genPt, toC_of_on (hV.on_circle 1 h1), C.add_x]
  simp [hV.gen_one h1]

/-- The x-coordinate X(m, b) of point b of the bit-reversed half coset of the standard domain of size 2^m. -/
noncomputable def Xp (G : p3_dft.mirror.Gen (K × K)) (m b : ℕ) : K :=
  (genPt G (m + 1) + rev (m - 1) b • genPt G (m - 1)).x

theorem zip_map_map {α β γ : Type _} (f : α → β) (g : α → γ) (l : List α) :
    (l.map f).zip (l.map g) = l.map fun a => (f a, g a) := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [ih]

/-- Take the codeword of f on the standard domain of size 2^n, n >= 1, with rows (f(P_b), f(J(P_b))).

Its first-layer fold is the codeword of f_0 + beta f_1 at the x-coordinates P_b.x. -/
theorem fold_y_spec (hV : CircleGenValid G) (h2 : (2 : K) ≠ 0) {n : ℕ} (hn : 1 ≤ n)
    (hG : n + 1 ≤ G.adicity) (c : ℕ → K) (β : K) :
    fold_y G β ((List.range (2 ^ (n - 1))).map fun b =>
        (fftEval n c (genPt G (n + 1) + rev (n - 1) b • genPt G (n - 1)),
          fftEval n c (-(genPt G (n + 1) + rev (n - 1) b • genPt G (n - 1))))) =
      some ((List.range (2 ^ (n - 1))).map fun b =>
        xEval (n - 1) (fun k => c (2 * k) + β * c (2 * k + 1)) (Xp G n b)) := by
  have hys := y_twiddles_eq hV (genPt G (n + 1)) hn (by omega)
  have hnz : ∀ y ∈ (List.range (2 ^ (n - 1))).map
      (fun b => (genPt G (n + 1) + rev (n - 1) b • genPt G (n - 1)).y), y ≠ 0 := by
    intro y hy
    obtain ⟨b, -, rfl⟩ := List.mem_map.mp hy
    have := twC_standard_ne_zero hV h2 hn hG (j := 0) (b := b) (by omega)
    simpa [twC] using this
  simp only [fold_y, List.length_map, List.length_range, log2Strict_pow, Option.map_some,
    Option.bind_eq_bind, Option.bind_some, show n - 1 + 1 = n by omega, standard_eq hV n hG, hys,
    batchInv_eq hnz]
  rw [fold_eq _ _ _ (by simp), zip_map_map, List.map_map]
  congr 1
  refine List.map_congr_left fun b hb => ?_
  simp only [Function.comp_apply]
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hy0 := hnz _ (List.mem_map_of_mem hb)
  simp only [Nat.add_sub_cancel] at hy0 ⊢
  rw [foldPair_fftEval h2 hy0, Xp, Nat.add_sub_cancel]

/-- Take a codeword of 2^(r+1) values at the points X(r + 2, b).

Its x-fold is the codeword of g_0 + beta g_1 at the points X(r + 1, c). -/
theorem fold_x_spec (hV : CircleGenValid G) (h2 : (2 : K) ≠ 0) {r : ℕ} (hG : r + 3 ≤ G.adicity)
    (d : ℕ → K) (β : K) :
    fold_x G β 1 ((List.range (2 ^ r)).map fun c =>
        (xEval (r + 1) d (Xp G (r + 2) (2 * c)), xEval (r + 1) d (Xp G (r + 2) (2 * c + 1)))) =
      some ((List.range (2 ^ r)).map fun c =>
        xEval r (fun k => d (2 * k) + β * d (2 * k + 1)) (Xp G (r + 1) c)) := by
  have hxs := x_twiddles_zero_eq hV (genPt G (r + 2 + 1)) (show 2 ≤ r + 2 by omega) (by omega)
  have hpt : ∀ c, Xp G (r + 2) (2 * c) = (genPt G (r + 2 + 1) + rev r c • genPt G (r + 2 - 1)).x :=
    fun c => by rw [Xp, show r + 2 - 1 = r + 1 by omega, rev_double]
  have hnz : ∀ x ∈ (List.range (2 ^ (r + 2 - 2))).map
      (fun c => (genPt G (r + 2 + 1) + rev (r + 2 - 2) c • genPt G (r + 2 - 1)).x), x ≠ 0 := by
    intro x hx
    obtain ⟨c, -, rfl⟩ := List.mem_map.mp hx
    have := twC_standard_ne_zero hV h2 (n := r + 2) (by omega) (by omega) (j := 1) (b := c) (by omega)
    simpa [twC] using this
  have hodd : ∀ c, Xp G (r + 2) (2 * c + 1) = -Xp G (r + 2) (2 * c) := fun c => by
    have h1 : 2 ^ r • genPt G (r + 1) = genPt G 1 := by
      have := genPt_nsmul hV (j := 1) (k := r + 1) (by omega) (by omega)
      rwa [Nat.add_sub_cancel] at this
    rw [Xp, Xp, show r + 2 - 1 = r + 1 by omega, rev_double_add_one, rev_double, add_nsmul, h1,
      ← add_assoc, add_right_comm, add_genPt_one_x hV (by omega)]
  have hpi : ∀ c, piX (Xp G (r + 2) (2 * c)) = Xp G (r + 1) c := fun c => by
    rw [Xp, Xp, show r + 2 - 1 = r + 1 by omega, rev_double, show r + 1 - 1 = r by omega, piX,
      ← C.two_nsmul_x, smul_add, two_nsmul_genPt hV (by omega), smul_comm,
      two_nsmul_genPt hV (by omega)]
  simp only [fold_x, ne_eq, not_true_eq_false, ↓reduceIte, List.length_map, List.length_range,
    ← pow_succ', log2Strict_pow, Option.bind_eq_bind, Option.bind_some,
    standard_eq hV (r + 1 + 1) (by omega), show r + 1 + 1 = r + 2 by omega, hxs, batchInv_eq hnz]
  simp only [show r + 2 - 2 = r by omega] at hnz ⊢
  rw [fold_eq _ _ _ (by simp), zip_map_map, List.map_map]
  congr 1
  refine List.map_congr_left fun c hc => ?_
  simp only [Function.comp_apply]
  rw [← hpt, hodd, foldPair_xEval h2 (by rw [hpt]; exact hnz _ (List.mem_map_of_mem hc)), hpi]

/-- A query's x-fold of one row uses the twiddle of the matrix fold at that row.

It panics exactly on an arity other than 2 or a row of another length. -/
theorem fold_x_row_spec (hV : CircleGenValid G) {lfh : ℕ} (hG : lfh + 3 ≤ G.adicity) (index : ℕ)
    (β e0 e1 : K) (hx : Xp G (lfh + 2) (2 * index) ≠ 0) :
    fold_x_row G index lfh 1 β [e0, e1] = some (foldPair (Xp G (lfh + 2) (2 * index)) β e0 e1) := by
  simp only [fold_x_row, ne_eq, not_true_eq_false, ↓reduceIte, List.length_cons, List.length_nil,
    zero_add, Nat.reduceAdd, Option.bind_eq_bind, standard_eq hV (lfh + 1 + 1) (by omega),
    Option.bind_some, bitRev_eq]
  rw [nth_x_twiddle_eq hV _ (by omega) (by omega)]
  have hX : Xp G (lfh + 2) (2 * index) = (genPt G (lfh + 1 + 1 + 1) + rev lfh index • genPt G (lfh + 1 + 1 - 1)).x := by
    rw [Xp, show lfh + 2 - 1 = lfh + 1 by omega, rev_double]
  rw [← hX, Option.bind_some, p3_commit.domain.mirror.inv, ite_eq_right hx]
  simp [fold_formula]

/-- The x-twiddle of round r of the query at top-level index t, in a FRI instance of log height L. -/
noncomputable def Xq (G : p3_dft.mirror.Gen (K × K)) (L t r : ℕ) : K :=
  (genPt G (L + 2 - r) + rev (L - 1 - r) (t / 2 ^ (r + 1)) • genPt G (L - r)).x

/-- Round r's twiddle is the one the row x-fold uses for the index t / 2^(r + 1).

The folded log height there is L - 1 - r. -/
theorem Xq_eq_Xp {L t r : ℕ} (hr : r + 1 ≤ L) : Xq G L t r = Xp G (L - 1 - r + 2) (2 * (t / 2 ^ (r + 1))) := by
  rw [Xq, Xp, show L - 1 - r + 2 - 1 = (L - 1 - r) + 1 by omega, rev_double,
    show L - 1 - r + 2 + 1 = L + 2 - r by omega, show L - 1 - r + 1 = L - r by omega]

/-- One step of the chain gives round k + 1's twiddle from round k's.

Square it, and negate it when the next index bit is set. -/
theorem Xq_succ (hV : CircleGenValid G) {L t k : ℕ} (hk : k + 2 ≤ L - 1) (hG : L + 2 ≤ G.adicity) :
    (if (t / 2 ^ (k + 1)) % 2 = 1 then -Point.vnStep (Xq G L t k) else Point.vnStep (Xq G L t k)) =
      Xq G L t (k + 1) := by
  have hdiv : t / 2 ^ (k + 1) = 2 * (t / 2 ^ (k + 1 + 1)) + (t / 2 ^ (k + 1)) % 2 := by
    have := Nat.div_add_mod (t / 2 ^ (k + 1)) 2
    rw [show t / 2 ^ (k + 1 + 1) = t / 2 ^ (k + 1) / 2 by rw [pow_succ, ← Nat.div_div_eq_div_mul]]
    omega
  have h2pt : 2 • genPt G (L + 2 - k) = genPt G (L + 2 - (k + 1)) := by
    rw [show L + 2 - k = (L + 2 - (k + 1)) + 1 by omega]; exact two_nsmul_genPt hV (by omega)
  have h2g : 2 • genPt G (L - k) = genPt G (L - (k + 1)) := by
    rw [show L - k = (L - (k + 1)) + 1 by omega]; exact two_nsmul_genPt hV (by omega)
  have hmid : 2 ^ (L - 1 - (k + 1)) • genPt G (L - (k + 1)) = genPt G 1 := by
    have := genPt_nsmul hV (j := 1) (k := L - (k + 1)) (by omega) (by omega)
    rwa [show L - (k + 1) - 1 = L - 1 - (k + 1) by omega] at this
  have hrev : L - 1 - k = (L - 1 - (k + 1)) + 1 := by omega
  rcases Nat.mod_two_eq_zero_or_one (t / 2 ^ (k + 1)) with he | he
  · rw [ite_eq_right (by omega), Xq, Xq, vnStep_x, smul_add, h2pt, smul_comm, h2g, hrev, hdiv, he,
      add_zero, rev_double]
  · rw [ite_eq_left he, Xq, Xq, vnStep_x, smul_add, h2pt, smul_comm, h2g, hrev, hdiv, he,
      rev_double_add_one, add_nsmul, hmid, add_comm (genPt G 1), ← add_assoc,
      add_genPt_one_x hV (by omega), neg_neg]

/-- Take an instance of log height L with L + 2 <= adicity, and at most L - 1 rounds.

The query's inverted x-twiddles are then those of every round, and computing them never panics. -/
theorem query_x_twiddles_inv_eq (hV : CircleGenValid G) (h2 : (2 : K) ≠ 0) {L R : ℕ} (t : ℕ)
    (hR : 1 ≤ R) (hRL : R + 1 ≤ L) (hG : L + 2 ≤ G.adicity) :
    query_x_twiddles_inv G t L R = some ((List.range R).map fun r => (Xq G L t r)⁻¹) := by
  have loop : ∀ k, k + 1 ≤ R → (List.range k).foldl (twiddleChainLoop t) ([Xq G L t 0], Xq G L t 0) =
      ((List.range (k + 1)).map (Xq G L t), Xq G L t k) := by
    intro k
    induction k with
    | zero => intro _; simp
    | succ k ih =>
      intro hk
      rw [List.range_succ, List.foldl_append, ih (by omega), List.foldl_cons, List.foldl_nil,
        twiddleChainLoop]
      simp only
      rw [Xq_succ hV (by omega) hG, List.range_succ (n := k + 1), List.map_append, List.map_singleton]
  have hseed : nth_x_twiddle G ⟨L + 1, ofC (genPt G (L + 1 + 1))⟩ (p3_dft.mirror.bitRev (L - 1) (t / 2)) =
      some (Xq G L t 0) := by
    rw [nth_x_twiddle_eq hV _ (by omega) (by omega), bitRev_eq, Xq, show L + 2 - 0 = L + 1 + 1 by omega,
      show L - 1 - 0 = L - 1 by omega, show L - 0 = L + 1 - 1 by omega, zero_add, pow_one]
  unfold query_x_twiddles_inv
  rw [ite_eq_right (by omega), ite_eq_right (by omega)]
  simp only [Option.bind_eq_bind, standard_eq hV (L + 1) (by omega), Option.bind_some, hseed]
  rw [loop (R - 1) (by omega), show R - 1 + 1 = R by omega]
  rw [batchInv_eq (fun x hx => ?_)]
  · simp [Function.comp_def]
  obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hx
  have hr' : r < R := by simpa using hr
  have := twC_standard_ne_zero hV h2 (n := L + 1 - r) (by omega) (by omega) (j := 1)
    (b := t / 2 ^ (r + 1)) (by omega)
  simp only [twC, one_ne_zero, ↓reduceIte, Nat.sub_self, pow_zero, one_nsmul] at this
  rwa [Xq, show L + 2 - r = L + 1 - r + 1 by omega, show L - 1 - r = L + 1 - r - 1 - 1 by omega,
    show L - r = L + 1 - r - 1 by omega]

end code

end Plonky3Lean.Proofs.Circle
