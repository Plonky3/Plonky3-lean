module

public import P3Circle.Prover
public import Plonky3Lean.Proofs.Circle.Honest
public import Plonky3Lean.Proofs.Circle.Bary

@[expose] public section

/-!
# p3-circle: the honest prover's open path

Take honest matrices: each committed matrix holds its columns on the LDE domain, in circle FFT order.

The prover's reduced column of a height is then the DEEP function of that height on the LDE domain.

Its lambda and corrected column are the ones the verifier's completeness reads.
-/

namespace Plonky3Lean.Proofs.Circle

open Plonky3Lean.Spec.Circle Plonky3Lean.Proofs.Dft Finset
open p3_dft.mirror p3_fri.mirror p3_commit.pcs.univariate.mirror p3_circle.point.mirror p3_circle.domain.mirror
open p3_circle.ordering.mirror p3_circle.deep_quotient.mirror p3_circle.pcs.mirror p3_circle.prover.mirror
open p3_circle.folding.mirror p3_fri.config.mirror p3_circle.verifier.mirror

set_option linter.unusedSectionVars false

variable {K : Type} [Field K] [DecidableEq K] {G : Gen (K × K)}

/-! ## Honest committed matrices -/

/-- The committed LDE of an honest matrix: row r holds the columns at the natural point sigma(r). -/
noncomputable def ldeMat (G : Gen (K × K)) (lb : ℕ) (m : HMat K) : Mat K :=
  ⟨2 ^ hgt lb m, m.2.length, fun r c => m.2.get c (ptD G (hgt lb m) (cfft_permute_index r (hgt lb m)))⟩

theorem finRange_map_get_apply {α : Type _} (l : List (α → K)) (a : α) :
    (List.finRange l.length).map (fun c => l.get c a) = l.map (· a) := by
  rw [show (fun c => l.get c a) = (· a) ∘ l.get from rfl, ← List.map_map, List.map_get_finRange]

theorem rowsOf_ldeMat (lb : ℕ) (m : HMat K) :
    rowsOf (ldeMat G lb m) = (List.range (2 ^ hgt lb m)).map fun r =>
      m.2.map (· (ptD G (hgt lb m) (cfft_permute_index r (hgt lb m)))) := by
  simp only [rowsOf, ldeMat]
  exact List.map_congr_left fun r _ => finRange_map_get_apply _ _

/-- The domain points of height h in circle FFT order. -/
theorem permutedPoints_eq (hV : CircleGenValid G) {h : ℕ} (hh : 1 ≤ h) (hG : h + 1 ≤ G.adicity) :
    permutedPoints G h = some ((List.range (2 ^ h)).map fun i => ofC (ptD G h (cfft_permute_index i h))) := by
  unfold permutedPoints
  simp only [standard_eq hV h hG, standard_points hV hh hG, Option.bind_eq_bind, Option.bind_some,
    cfft_permute_slice, List.length_map, List.length_range, log2Strict_pow]
  refine mapM_eq_some_map _ _ _ fun i hi => ?_
  rw [List.getElem?_map, List.getElem?_range (by simpa using cfft_permute_index_lt h i)]
  rfl

theorem foldl_fst {β : Type _} (w : K) (g : β → K × K → K) :
    ∀ (ps : List β) (e : K × K), (ps.foldl (fun e p => (e.1 * w, g p e)) e).1 = e.1 * w ^ ps.length
  | [], e => by simp
  | p :: ps, e => by rw [List.foldl_cons, foldl_fst w g ps, List.length_cons, pow_succ]; ring

theorem matStep_fst (α : K) (m : HMat K) (Q : C K) (e : K × K) :
    (matStep α m Q e).1 = e.1 * ((α ^ m.2.length) ^ 2) ^ m.1.points.length := by
  have := foldl_fst ((α ^ (m.2.map (· Q)).length) ^ 2)
    (fun p e => e.2 + e.1 * deepTerm α Q (ptOf p.point) (m.2.map (· Q)) p.values) m.1.points e
  exact this.trans (by rw [List.length_map])

/-- The running power of alpha does not depend on the query point. -/
theorem deepAcc_fst (α : K) :
    ∀ (ms : List (HMat K)) (Q Q' : C K) (e e' : K × K), e.1 = e'.1 → (deepAcc α ms Q e).1 = (deepAcc α ms Q' e').1
  | [], _, _, _, _, h => h
  | m :: ms, Q, Q', e, e', h => by
    simp only [deepAcc, List.foldl_cons]
    exact deepAcc_fst α ms Q Q' _ _ (by rw [matStep_fst, matStep_fst, h])

/-! ## The prover's DEEP quotients of one matrix -/

/-- One opening point's step of the verifier's honest reduction at the query point Q. -/
noncomputable def honestStep (α : K) (fs : List (C K → K)) (Q : C K) (e : K × K) (p : PointOpening K) : K × K :=
  (e.1 * (α ^ fs.length) ^ 2, e.2 + e.1 * deepTerm α Q (ptOf p.point) (fs.map (· Q)) p.values)

theorem matStep_eq (α : K) (m : HMat K) (Q : C K) (e : K × K) :
    matStep α m Q e = m.1.points.foldl (honestStep α m.2 Q) e := by
  simp only [matStep, List.length_map]; rfl

/-- One opening point's step of the prover's accumulation, over the whole column. -/
def proverStep (pts : List (Point K)) (α αW : K) (rr : List K) (e : K × List K) (p : PointOpening K) :
    Option (K × List K) := do
  let zeta ← Point.from_projective_line p.point
  let vp ← compute_vanishing_parts pts zeta
  pure (e.1 * αW ^ 2, accumulate_deep_quotient e.2 e.1 αW rr vp
    (dot_product ((List.range p.values.length).map (α ^ ·)) p.values))

theorem ofC_ptOf {t : K} (ht : 1 + t * t ≠ 0) : Point.from_projective_line t = some (ofC (ptOf t)) := by
  rw [from_projective_line_eq, dite_eq_right ht, ptOf, dite_eq_right ht]

/-! ## The lifted reduction of a wide matrix -/

local notation "rev" => Plonky3Lean.Spec.Matrix.bitRev

/-- Rows 2 j and 2 j + 1 of the circle FFT order hold a point of the half coset and its conjugate. -/
theorem ptD_pair (hV : CircleGenValid G) {n : ℕ} (hG : n + 2 ≤ G.adicity) {j : ℕ} (hj : j < 2 ^ n) :
    ptD G (n + 1) (cfft_permute_index (2 * j) (n + 1)) = genPt G (n + 2) + rev n j • genPt G n ∧
      ptD G (n + 1) (cfft_permute_index (2 * j + 1) (n + 1)) = -(genPt G (n + 2) + rev n j • genPt G n) := by
  set Q := genPt G (n + 2)
  have h4 : genPt G n = 4 • Q := by
    have := genPt_nsmul hV (j := n) (k := n + 2) (by omega) hG
    rw [show n + 2 - n = 2 by omega] at this
    rw [← this]; norm_num [Q]
  have hzero : 2 ^ (n + 2) • Q = 0 := genPt_order_zero hV hG
  have hr := Plonky3Lean.Proofs.Matrix.bitRev_lt n j
  have hev : Q + rev n j • genPt G n = (2 * (2 * rev n j) + 1) • Q := by
    rw [h4, smul_smul, show 2 * (2 * rev n j) + 1 = 1 + rev n j * 4 by ring, add_nsmul, one_nsmul]
  refine ⟨?_, ?_⟩
  · rw [ptD, cfft_permute_index_even hj, hev]
  · rw [ptD, cfft_permute_index_odd hj, rev_complement n hj, hev, eq_neg_iff_add_eq_zero, ← add_nsmul,
      show 2 * (2 * (2 ^ n - 1 - rev n j) + 1) + 1 + (2 * (2 * rev n j) + 1) = 2 ^ (n + 2) by rw [pow_add]; omega,
      show n + 1 + 1 = n + 2 by omega, hzero]

/-- The first 2^s points of the LDE domain of height h, in circle FFT order, are a twin coset of size 2^s.

Its shift is the LDE's shift, the generator of order 2^(h + 1). -/
theorem twinList_prefix (hV : CircleGenValid G) (h2 : (2 : K) ≠ 0) {h s : ℕ} (hs : 1 ≤ s) (hsh : s ≤ h)
    (hG : h + 1 ≤ G.adicity) : TwinList s (genPt G (h + 1)) fun r => ptD G h (cfft_permute_index r h) := by
  have hsh' : 2 ^ s ≤ 2 ^ h := Nat.pow_le_pow_right two_pos hsh
  refine ⟨fun i hi j hj hij => ?_, fun r hr => ?_⟩
  · have hk := List.inj_on_of_nodup_map (standard_nodup hV h2 hG)
      (List.mem_range.mpr (cfft_permute_index_lt h i)) (List.mem_range.mpr (cfft_permute_index_lt h j)) hij
    rw [← cfft_permute_index_involutive (show i < 2 ^ h by omega), hk,
      cfft_permute_index_involutive (show j < 2 ^ h by omega)]
  obtain ⟨n, rfl⟩ : ∃ n, h = n + 1 := ⟨h - 1, by omega⟩
  have hj : r / 2 < 2 ^ (s - 1) := by
    rw [show 2 ^ s = 2 ^ (s - 1) * 2 by rw [← pow_succ]; congr 1; omega] at hr; omega
  have hjn : r / 2 < 2 ^ n := lt_of_lt_of_le hj (Nat.pow_le_pow_right two_pos (by omega))
  obtain ⟨he, ho⟩ := ptD_pair hV (show n + 2 ≤ G.adicity by omega) hjn
  have hz : 2 ^ (s - 1) • rev n (r / 2) • genPt G n = 0 := by
    have hrev : rev n (r / 2) = rev (s - 1) (r / 2) * 2 ^ (n - (s - 1)) := by
      have := Plonky3Lean.Proofs.Matrix.bitRev_add_of_lt (k := n - (s - 1)) hj
      rwa [show s - 1 + (n - (s - 1)) = n by omega] at this
    rw [hrev, smul_smul, show 2 ^ (s - 1) * (rev (s - 1) (r / 2) * 2 ^ (n - (s - 1))) = 2 ^ n * rev (s - 1) (r / 2) by
      rw [mul_left_comm, ← pow_add, show s - 1 + (n - (s - 1)) = n by omega, mul_comm], mul_nsmul,
      genPt_order_zero hV (by omega), smul_zero]
  rcases Nat.even_or_odd' r with ⟨j, rfl | rfl⟩
  · rw [show 2 * j / 2 = j by omega] at he hz
    simp [he, smul_add, hz]
  · rw [show (2 * j + 1) / 2 = j by omega] at ho hz
    simp [ho, smul_add, hz, show (2 * j + 1) % 2 = 1 by omega]

/-- The twiddles of the twin coset of size 2^s shifted as the standard domain of size 2^h are nonzero.

Every twiddle is one of:

- a coordinate of a point of order at least 8
- a y-coordinate of a point of order at least 4. -/
theorem twC_prefix_ne_zero (hV : CircleGenValid G) (h2 : (2 : K) ≠ 0) {h s : ℕ} (hs : 1 ≤ s) (hsh : s ≤ h)
    (hG : h + 1 ≤ G.adicity) {j b : ℕ} (hj : j < s) :
    twC (genPt G (h + 1)) (genPt G (s - 1)) s j b ≠ 0 := by
  set S := genPt G (h + 1)
  have hS : addOrderOf S = 2 ^ (h + 1) := addOrderOf_genPt hV h2 hG
  have hg : genPt G (s - 1) = (2 ^ (h - s) * 2 ^ 2) • S := by
    have := genPt_nsmul hV (show s - 1 ≤ h + 1 by omega) hG
    rw [show h + 1 - (s - 1) = (h - s) + 2 by omega] at this
    rw [← this, pow_add]
  have hpt : ∀ r, S + r • genPt G (s - 1) = (2 * (2 * (2 ^ (h - s) * r)) + 1) • S := fun r => by
    rw [hg, smul_smul, add_comm, ← succ_nsmul]; ring_nf
  unfold twC
  split_ifs with h0
  · rw [hpt]
    apply y_ne_zero_of_order
    intro hd
    have := addOrderOf_dvd_iff_nsmul_eq_zero.mp hd
    rw [smul_smul, ← addOrderOf_dvd_iff_nsmul_eq_zero, hS, show 2 * (2 * (2 * (2 ^ (h - s) * rev (s - 1) b)) + 1) =
      2 ^ 1 * (2 * (2 * (2 ^ (h - s) * rev (s - 1) b)) + 1) by ring] at this
    have := le_of_two_pow_dvd this
    omega
  · rw [hpt, smul_smul]
    apply x_ne_zero_of_order
    intro hd
    have := addOrderOf_dvd_iff_nsmul_eq_zero.mp hd
    rw [smul_smul, ← addOrderOf_dvd_iff_nsmul_eq_zero, hS, show 4 * (2 ^ (j - 1) *
      (2 * (2 * (2 ^ (h - s) * rev (s - 1 - j) b)) + 1)) =
        2 ^ (j + 1) * (2 * (2 * (2 ^ (h - s) * rev (s - 1 - j) b)) + 1) by
        rw [show j + 1 = (j - 1) + 2 by omega, pow_add]; ring] at this
    have := le_of_two_pow_dvd this
    omega

/-- Row i of the transforms on the twin coset of size 2^s is row i of the LDE domain of size 2^h. -/
theorem ptAt_prefix (hV : CircleGenValid G) {h s : ℕ} (hs : 1 ≤ s) (hsh : s ≤ h) (hG : h + 1 ≤ G.adicity)
    {i : ℕ} (hi : i < 2 ^ s) :
    ptAt (genPt G (h + 1)) (genPt G (s - 1)) s i = ptD G h (cfft_permute_index i h) := by
  obtain ⟨n, rfl⟩ : ∃ n, h = n + 1 := ⟨h - 1, by omega⟩
  have hj : i / 2 < 2 ^ (s - 1) := by
    rw [show 2 ^ s = 2 ^ (s - 1) * 2 by rw [← pow_succ]; congr 1; omega] at hi; omega
  obtain ⟨he, ho⟩ := ptD_pair hV (show n + 2 ≤ G.adicity by omega)
    (lt_of_lt_of_le hj (Nat.pow_le_pow_right two_pos (by omega)))
  have hr : rev n (i / 2) • genPt G n = rev (s - 1) (i / 2) • genPt G (s - 1) := by
    have := Plonky3Lean.Proofs.Matrix.bitRev_add_of_lt (k := n - (s - 1)) hj
    rw [show s - 1 + (n - (s - 1)) = n by omega] at this
    rw [this, mul_comm, mul_nsmul, genPt_nsmul hV (by omega) (by omega)]
  rcases Nat.even_or_odd' i with ⟨j, rfl | rfl⟩
  · rw [show 2 * j / 2 = j by omega] at he hr
    simp [ptAt, he, hr]
  · rw [show (2 * j + 1) / 2 = j by omega] at ho hr
    simp [ptAt, ho, hr, show (2 * j + 1) % 2 = 1 by omega, show (2 * j + 1) / 2 = j by omega]

/-- The row reduction of the columns at a point: sum_j alpha^j f_j(Q). -/
noncomputable def redF (α : K) (fs : List (C K → K)) (Q : C K) : K :=
  dot_product ((List.range fs.length).map (α ^ ·)) (fs.map (· Q))

theorem rowsOf_prefix (lb : ℕ) (m : HMat K) (s : ℕ) :
    rowsOf (⟨2 ^ s, m.2.length, (ldeMat G lb m).entry⟩ : Mat K) = (List.range (2 ^ s)).map fun r =>
      m.2.map (· (ptD G (hgt lb m) (cfft_permute_index r (hgt lb m)))) := by
  simp only [rowsOf, ldeMat]
  exact List.map_congr_left fun r _ => finRange_map_get_apply _ _

theorem rowwise_alpha_reduce_map (α : K) (fs : List (C K → K)) (N : ℕ) (P : ℕ → C K) :
    rowwise_alpha_reduce ((List.range N).map fun r => fs.map (· (P r))) α =
      (List.range N).map fun r => redF α fs (P r) := by
  simp [rowwise_alpha_reduce, redF]

/-- The row reduction of columns of the FFT space lies in the FFT space. -/
theorem isFftPoly_redF {D : ℕ} (hD : 1 ≤ D) (α : K) {fs : List (C K → K)} (hfs : ∀ f ∈ fs, IsFftPoly D f) :
    IsFftPoly D (redF α fs) := by
  have h : redF α fs = fun Q => ∑ j ∈ Finset.range fs.length, α ^ j * fs.getD j 0 Q := by
    funext Q
    rw [redF, show fs.length = (fs.map (· Q)).length by simp, dot_product_range]
    simp only [List.length_map]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [show (0 : K) = (fun f : C K → K => f Q) 0 from rfl, List.getD_map]
  rw [h]
  refine IsFftPoly.sum hD _ fun j hj => IsFftPoly.smul _ (hfs _ ?_)
  rw [List.getD_eq_getElem _ _ (Finset.mem_range.mp hj)]
  exact List.getElem_mem _

/-- The lifted reduction of an honest matrix is its row-by-row reduction.

The columns lie in the FFT space of the trace size 2^s, so their reduction does too.

Its values on the twin coset of the first 2^s rows determine it. -/
theorem rowwise_alpha_reduce_lifted_honest (hV : CircleGenValid G) (h2 : (2 : K) ≠ 0) {lb : ℕ} (α : K)
    (m : HMat K) (hs : 1 ≤ m.1.domain.log_n) (hG : hgt lb m + 1 ≤ G.adicity)
    (hfft : ∀ f ∈ m.2, IsFftPoly (2 ^ (m.1.domain.log_n - 1)) f) :
    rowwise_alpha_reduce_lifted G ⟨m.1.domain.log_n, ofC (genPt G (hgt lb m + 1))⟩
        ⟨2 ^ m.1.domain.log_n, m.2.length, (ldeMat G lb m).entry⟩ α ⟨hgt lb m, ofC (genPt G (hgt lb m + 1))⟩ =
      some (rowwise_alpha_reduce (rowsOf (ldeMat G lb m)) α) := by
  set s := m.1.domain.log_n
  set h := hgt lb m
  have hsh : s ≤ h := by unfold s h hgt; omega
  set P : ℕ → C K := fun r => ptD G h (cfft_permute_index r h)
  have hP := twinList_prefix hV h2 hs hsh hG
  have hred : rowwise_alpha_reduce (rowsOf (⟨2 ^ s, m.2.length, (ldeMat G lb m).entry⟩ : Mat K)) α =
      (List.range (2 ^ s)).map fun r => redF α m.2 (P r) := by
    rw [rowsOf_prefix, rowwise_alpha_reduce_map]
  obtain ⟨cs, hcs, hcsv⟩ := interpolate_spec hV h2 hs (show s - 1 ≤ G.adicity by omega) (genPt G (h + 1))
    (fun j hj b _ => twC_prefix_ne_zero hV h2 hs hsh hG hj)
    (fun i => ((List.range (2 ^ s)).map fun r => redF α m.2 (P r)).getD i 0)
  -- The interpolant agrees with the reduction on the twin coset, so everywhere.
  have hagree : ∀ Q, fftEval s cs Q = redF α m.2 Q := by
    obtain ⟨k, hk⟩ : ∃ k, s = k + 1 := ⟨s - 1, by omega⟩
    have hk' : s - 1 = k := by omega
    intro Q
    have hfe : IsFftPoly (2 ^ k) (fftEval s cs) := hk ▸ IsFftPoly.fftEval k cs
    have hrf : IsFftPoly (2 ^ k) (redF α m.2) := isFftPoly_redF Nat.one_le_two_pow α (hk' ▸ hfft)
    refine sub_eq_zero.mp (IsFftPoly.eq_zero (m := k) (c := vn s (genPt G (h + 1))) h2
      (by rw [hP.card, hk]) (fun R hR => ?_) (hfe.sub hrf) (fun R hR => ?_) Q)
    · obtain ⟨j, hj, rfl⟩ := TwinList.mem.mp hR; rw [← hk]; exact hP.vn_eq hj
    · obtain ⟨j, hj, rfl⟩ := TwinList.mem.mp hR
      have := hcsv j hj
      rw [ptAt_prefix hV hs hsh hG hj, List.getD_eq_getElem _ _ (by simpa using hj), List.getElem_map,
        List.getElem_range] at this
      rw [sub_eq_zero]; exact this
  obtain ⟨y, hy, hyv⟩ := evaluate_standard hV hs hsh hG cs
  unfold rowwise_alpha_reduce_lifted
  simp only [hred, List.length_map, List.length_range, ne_eq, not_true_eq_false, ↓reduceIte,
    show ¬ h < s by omega, Option.bind_eq_bind]
  rw [hcs, Option.bind_some, hy, Option.bind_some, rowsOf_ldeMat, rowwise_alpha_reduce_map]
  refine congrArg some (List.map_congr_left fun i hi => ?_)
  rw [hyv i (List.mem_range.mp hi), hagree]
  rfl

/-- What one matrix needs for the prover's accumulation to be the honest reduction:

- a domain of at least 2 rows, with room in the generator table
- columns of the FFT space of the trace size
- honest values at opening points on the circle and off the LDE domain. -/
structure ProverMatOK (G : Gen (K × K)) (lb : ℕ) (m : HMat K) : Prop where
  log_n : 1 ≤ m.1.domain.log_n
  fft : ∀ f ∈ m.2, IsFftPoly (2 ^ (m.1.domain.log_n - 1)) f
  adicity : hgt lb m + 1 ≤ G.adicity
  values : ∀ p ∈ m.1.points, p.values = m.2.map (· (ptOf p.point))
  on_circle : ∀ p ∈ m.1.points, 1 + p.point * p.point ≠ 0
  off_domain : ∀ p ∈ m.1.points, ∀ k < 2 ^ hgt lb m, ptOf p.point ≠ ptD G (hgt lb m) k

/-- The prover's reduced rows of an honest matrix are its row-by-row reduction, whatever its width. -/
theorem reducedRows_honest (hV : CircleGenValid G) (h2 : (2 : K) ≠ 0) {lb : ℕ} (α : K) (m : HMat K)
    (hm : ProverMatOK G lb m) :
    reducedRows G lb (hgt lb m) (ldeMat G lb m) α = some (rowwise_alpha_reduce (rowsOf (ldeMat G lb m)) α) := by
  unfold reducedRows
  simp only [show ¬ hgt lb m < lb by unfold hgt; omega, ↓reduceIte,
    show hgt lb m - lb = m.1.domain.log_n by unfold hgt; omega]
  split_ifs
  · simp only [standard_eq hV _ hm.adicity, Option.bind_eq_bind, Option.bind_some, CircleDomain.new]
    exact rowwise_alpha_reduce_lifted_honest hV h2 α m hm.log_n hm.adicity hm.fft
  · rfl

/-- The prover's step at one point adds, at every row, the DEEP term at that row's point. -/
theorem proverStep_eq (h2 : (2 : K) ≠ 0) {lb : ℕ} (α : K) (m : HMat K) (hm : ProverMatOK G lb m)
    {p : PointOpening K} (hp : p ∈ m.1.points) (a : K) (bs : ℕ → K) :
    proverStep ((List.range (2 ^ hgt lb m)).map fun i => ofC (ptD G (hgt lb m) (cfft_permute_index i (hgt lb m))))
        α (α ^ m.2.length) (rowwise_alpha_reduce (rowsOf (ldeMat G lb m)) α)
        (a, (List.range (2 ^ hgt lb m)).map bs) p =
      some (a * (α ^ m.2.length) ^ 2, (List.range (2 ^ hgt lb m)).map fun i =>
        bs i + a * deepTerm α (ptD G (hgt lb m) (cfft_permute_index i (hgt lb m))) (ptOf p.point)
          (m.2.map (· (ptD G (hgt lb m) (cfft_permute_index i (hgt lb m))))) p.values) := by
  set h := hgt lb m
  set P : ℕ → C K := fun i => ptD G h (cfft_permute_index i h)
  have hoff : ptOf p.point ∉ (List.range (2 ^ h)).map P := by
    intro hmem
    obtain ⟨i, -, hi⟩ := List.mem_map.mp hmem
    exact hm.off_domain p hp _ (cfft_permute_index_lt h i) hi.symm
  unfold proverStep
  rw [ofC_ptOf (hm.on_circle p hp), Option.bind_eq_bind, Option.bind_some,
    show (List.range (2 ^ h)).map (fun i => ofC (P i)) = ((List.range (2 ^ h)).map P).map ofC by
      rw [List.map_map]; rfl,
    compute_vanishing_parts_eq h2 _ _]
  simp only [hoff, ↓reduceIte, Option.bind_eq_bind, Option.bind_some, Option.pure_def]
  have hvals := hm.values p hp
  unfold accumulate_deep_quotient rowwise_alpha_reduce
  simp only [rowsOf_ldeMat, List.map_map, Function.comp_def]
  rw [show hgt lb m = h from rfl, zip_map_map, zip_map_map, List.map_map]
  congr 2
  refine List.map_congr_left fun i hi => ?_
  have hPQ : P i ≠ ptOf p.point := fun hc => hoff (hc ▸ List.mem_map_of_mem hi)
  have hlen : (m.2.map (· (P i))).length = p.values.length := by rw [hvals]; simp
  have hacc := accumulate_eq_reduce_row a (α ^ m.2.length) ((List.range m.2.length).map (α ^ ·))
    (m.2.map (· (P i))) p.values (P i) (ptOf p.point) hPQ h2 hlen (by simp)
  have hred := reduce_row_eq_re_im h2 α (P i) (ptOf p.point) hPQ (m.2.map (· (P i))) p.values hlen
  simp only [List.length_map] at hred
  rw [hred, Option.getD_some] at hacc
  have hd : deepTerm α (P i) (ptOf p.point) (m.2.map (· (P i))) p.values =
      ∑ x ∈ range m.2.length, (α ^ x * (cquot ((m.2.map (· (P i))).getD x 0 - p.values.getD x 0)
        (Point.v_p (ofC (P i)) (ofC (ptOf p.point)))).1 + α ^ (m.2.length + x) *
        (cquot ((m.2.map (· (P i))).getD x 0 - p.values.getD x 0) (Point.v_p (ofC (P i)) (ofC (ptOf p.point)))).2) := by
    unfold deepTerm; simp only [List.length_map]
  simp only [Function.comp_apply, List.length_map, ← hlen]
  show _ = bs i + a * deepTerm α (P i) (ptOf p.point) (m.2.map (· (P i))) p.values
  rw [hd]
  exact congrArg (bs i + ·) hacc

/-- The prover's steps over a matrix's points: every row accumulates its point's honest reduction. -/
theorem foldlM_proverStep (h2 : (2 : K) ≠ 0) {lb : ℕ} (α : K) (m : HMat K) (hm : ProverMatOK G lb m) :
    ∀ (ps : List (PointOpening K)), (∀ p ∈ ps, p ∈ m.1.points) → ∀ (a : K) (bs : ℕ → K),
      ps.foldlM (proverStep ((List.range (2 ^ hgt lb m)).map fun i =>
          ofC (ptD G (hgt lb m) (cfft_permute_index i (hgt lb m))))
        α (α ^ m.2.length) (rowwise_alpha_reduce (rowsOf (ldeMat G lb m)) α)) (a, (List.range (2 ^ hgt lb m)).map bs) =
      some (a * ((α ^ m.2.length) ^ 2) ^ ps.length, (List.range (2 ^ hgt lb m)).map fun i =>
        (ps.foldl (honestStep α m.2 (ptD G (hgt lb m) (cfft_permute_index i (hgt lb m)))) (a, bs i)).2)
  | [], _, a, bs => by simp
  | p :: ps, hps, a, bs => by
    rw [List.foldlM_cons, proverStep_eq h2 α m hm (hps p List.mem_cons_self), Option.bind_eq_bind, Option.bind_some,
      foldlM_proverStep h2 α m hm ps (fun q hq => hps q (List.mem_cons_of_mem _ hq))]
    simp only [List.length_cons, List.foldl_cons]
    congr 2
    · rw [pow_succ]; ring

/-- The reduced columns the prover holds after some honest matrices: at each height, the DEEP function of the
matrices of that height on the LDE domain, with its running power of alpha. -/
noncomputable def honestRO (G : Gen (K × K)) (lb : ℕ) (α : K) (L : List (HMat K)) (h : ℕ) : K × List K :=
  ((deepAcc α (L.filter fun m => hgt lb m = h) (ptD G h 0) (1, 0)).1,
    (List.range (2 ^ h)).map fun i => deepFnAt lb α L h (ptD G h (cfft_permute_index i h)))

/-- The prover's reduction state after the honest matrices L. -/
def ROInv (G : Gen (K × K)) (lb : ℕ) (α : K) (L : List (HMat K)) (st : (ℕ → K × List K) × List ℕ) : Prop :=
  st.2 = Plonky3Lean.Proofs.Fri.keysAfter [] (L.map (hgt lb)) ∧ ∀ h ∈ st.2, st.1 h = honestRO G lb α L h

theorem mem_keysAfter_nil {lb : ℕ} {L : List (HMat K)} {h : ℕ} :
    h ∈ Plonky3Lean.Proofs.Fri.keysAfter [] (L.map (hgt lb)) ↔ ∃ m ∈ L, hgt lb m = h := by
  rw [(Plonky3Lean.Proofs.Fri.keysAfter_spec _ [] List.nodup_nil).2]
  simp

theorem honestRO_snoc (α : K) {lb : ℕ} {L : List (HMat K)} {m : HMat K} {h : ℕ} (hm : hgt lb m = h) :
    honestRO G lb α (L ++ [m]) h = ((honestRO G lb α L h).1 * ((α ^ m.2.length) ^ 2) ^ m.1.points.length,
      (List.range (2 ^ h)).map fun i => (m.1.points.foldl (honestStep α m.2 (ptD G h (cfft_permute_index i h)))
        ((honestRO G lb α L h).1, deepFnAt lb α L h (ptD G h (cfft_permute_index i h)))).2) := by
  have hfil : (L ++ [m]).filter (fun m' => hgt lb m' = h) = L.filter (fun m' => hgt lb m' = h) ++ [m] := by
    simp [List.filter_append, hm]
  unfold honestRO deepFnAt
  simp only [hfil, deepAcc, List.foldl_append, List.foldl_cons, List.foldl_nil]
  refine Prod.ext (matStep_fst _ _ _ _) (List.map_congr_left fun i _ => ?_)
  rw [matStep_eq]
  congr 2
  exact Prod.ext (deepAcc_fst α _ _ _ _ _ rfl) rfl

theorem honestRO_snoc_ne (α : K) {lb : ℕ} {L : List (HMat K)} {m : HMat K} {h : ℕ} (hm : hgt lb m ≠ h) :
    honestRO G lb α (L ++ [m]) h = honestRO G lb α L h := by
  have hfil : (L ++ [m]).filter (fun m' => hgt lb m' = h) = L.filter (fun m' => hgt lb m' = h) := by
    simp [List.filter_append, hm]
  unfold honestRO deepFnAt
  rw [hfil]

/-- The prover's accumulation of one honest matrix keeps its state the honest one. -/
theorem accumulateMatrix_honest (hV : CircleGenValid G) (h2 : (2 : K) ≠ 0) {lb : ℕ} (α : K) {L : List (HMat K)}
    {st : (ℕ → K × List K) × List ℕ} (hst : ROInv G lb α L st) (m : HMat K) (hm : ProverMatOK G lb m) :
    ∃ st', accumulateMatrix G lb α st (ldeMat G lb m, m.1.points.map (·.point), m.1.points.map (·.values)) = some st' ∧
      ROInv G lb α (L ++ [m]) st' := by
  obtain ⟨acc, keys⟩ := st
  obtain ⟨hkeys, hacc⟩ := hst
  dsimp only at hkeys hacc
  set h := hgt lb m
  have hh1 : 1 ≤ h := by have := hm.log_n; unfold h hgt; omega
  have hentry : (if h ∈ keys then acc h else (1, List.replicate (2 ^ h) 0)) = honestRO G lb α L h := by
    split_ifs with hk
    · exact hacc h hk
    · have hnil : (L.filter fun m' => hgt lb m' = h) = [] := by
        rw [List.filter_eq_nil_iff]
        intro m' hm' hc
        exact hk (hkeys ▸ mem_keysAfter_nil.mpr ⟨m', hm', by simpa using hc⟩)
      simp only [honestRO, deepFnAt, hnil]
      congr 1
      simp [deepAcc]
  have hfold := foldlM_proverStep h2 α m hm m.1.points (fun p hp => hp) (honestRO G lb α L h).1
    (fun i => deepFnAt lb α L h (ptD G h (cfft_permute_index i h)))
  refine ⟨(Function.update acc h ((honestRO G lb α L h).1 * ((α ^ m.2.length) ^ 2) ^ m.1.points.length,
      (List.range (2 ^ h)).map fun i => (m.1.points.foldl (honestStep α m.2 (ptD G h (cfft_permute_index i h)))
        ((honestRO G lb α L h).1, deepFnAt lb α L h (ptD G h (cfft_permute_index i h)))).2),
      if h ∈ keys then keys else keys ++ [h]), ?_, ?_⟩
  · unfold accumulateMatrix
    simp only [show (ldeMat G lb m).height = 2 ^ hgt lb m from rfl, log2Strict_pow, Option.bind_eq_bind,
      Option.bind_some]
    simp only [reducedRows_honest hV h2 α m hm, Option.bind_some]
    simp only [ldeMat]
    rw [show 2 ^ hgt lb m = 2 ^ h from rfl, hentry, permutedPoints_eq hV hh1 hm.adicity, Option.bind_some,
      zip_map_map, List.foldlM_map]
    erw [hfold]
    rfl
  · refine ⟨?_, fun h' hh' => ?_⟩
    · simp only [Plonky3Lean.Proofs.Fri.keysAfter, List.map_append, List.map_cons, List.map_nil,
        List.foldl_append, List.foldl_cons, List.foldl_nil] at hkeys ⊢
      rw [hkeys]
    · dsimp only
      by_cases he : h' = h
      · subst he
        rw [Function.update_self]
        exact (honestRO_snoc α (rfl : hgt lb m = h)).symm
      · have hk : h' ∈ keys := by split_ifs at hh' <;> simp_all
        rw [Function.update_of_ne he, hacc h' hk, honestRO_snoc_ne α (Ne.symm he)]

/-- The prover's input to the accumulation for one honest matrix: its LDE, its opening points, and its values. -/
noncomputable def accInput (G : Gen (K × K)) (lb : ℕ) (m : HMat K) : Mat K × List K × List (List K) :=
  (ldeMat G lb m, m.1.points.map (·.point), m.1.points.map (·.values))

theorem foldlM_accumulate (hV : CircleGenValid G) (h2 : (2 : K) ≠ 0) {lb : ℕ} (α : K) :
    ∀ (L : List (HMat K)), (∀ m ∈ L, ProverMatOK G lb m) → ∀ (L0 : List (HMat K)) (st : (ℕ → K × List K) × List ℕ),
      ROInv G lb α L0 st → ∃ st', (L.map (accInput G lb)).foldlM (accumulateMatrix G lb α) st = some st' ∧
        ROInv G lb α (L0 ++ L) st'
  | [], _, L0, st, hst => ⟨st, rfl, by simpa using hst⟩
  | m :: L, hL, L0, st, hst => by
    obtain ⟨st1, h1, hinv1⟩ := accumulateMatrix_honest hV h2 α hst m (hL m List.mem_cons_self)
    obtain ⟨st2, h2', hinv2⟩ := foldlM_accumulate hV h2 α L (fun m' hm' => hL m' (List.mem_cons_of_mem _ hm'))
      (L0 ++ [m]) st1 hinv1
    refine ⟨st2, ?_, by simpa using hinv2⟩
    rw [List.map_cons, List.foldlM_cons]
    erw [h1]
    exact h2'

/-- The prover's reduction of honest batches holds, at every height, the DEEP function on the LDE domain. -/
theorem reducedOpenings_honest (hV : CircleGenValid G) (h2 : (2 : K) ≠ 0) {lb : ℕ} (α : K)
    (hb : List (List (HMat K))) (hok : ∀ m ∈ hb.flatten, ProverMatOK G lb m) :
    ∃ st, reducedOpenings G lb α (hb.map fun ms => (ms.map (ldeMat G lb), ms.map fun m => m.1.points.map (·.point)))
        (hb.map fun ms => ms.map fun m => m.1.points.map (·.values)) = some st ∧ ROInv G lb α hb.flatten st := by
  have hflat : ((hb.map fun ms => (ms.map (ldeMat G lb), ms.map fun m => m.1.points.map (·.point))).zip
      (hb.map fun ms => ms.map fun m => m.1.points.map (·.values))).flatMap
        (fun rv => (rv.1.1.zip (rv.1.2.zip rv.2)).map fun m => (m.1, m.2.1, m.2.2)) =
      hb.flatten.map (accInput G lb) := by
    rw [zip_map_map, List.flatMap_map, List.map_flatten]
    clear hok
    induction hb with
    | nil => rfl
    | cons ms hb ih =>
      rw [List.flatMap_cons, List.map_cons, List.flatten_cons, ih]
      simp only [zip_map_map, List.map_map]
      rfl
  obtain ⟨st, hst, hinv⟩ := foldlM_accumulate hV h2 α hb.flatten hok [] (fun _ => (1, []), [])
    ⟨rfl, fun h hh => by simp at hh⟩
  exact ⟨st, by rw [reducedOpenings, hflat]; exact hst, by simpa using hinv⟩

/-! ## The lambdas and the corrected columns -/

/-- The corrected DEEP function of height h on its LDE domain, in circle FFT order. -/
noncomputable def corrCol (G : Gen (K × K)) (lb : ℕ) (α : K) (L : List (HMat K)) (h : ℕ) : List K :=
  (List.range (2 ^ h)).map fun i => corr G lb α L h (ptD G h (cfft_permute_index i h))

/-- The prover's extraction on the honest LDE returns the lambda and the corrected column. -/
theorem extract_ldeVec (hV : CircleGenValid G) (h2 : (2 : K) ≠ 0) {lb : ℕ} (α : K) {L : List (HMat K)} {h : ℕ}
    (hlb : 1 ≤ lb) (hh : lb + 1 ≤ h) (hG : h + 1 ≤ G.adicity) (hon : HonestAt G lb L h) :
    extract_lambda G (ldeVec G lb α L h) lb = some (lamAt G lb α L h, corrCol G lb α L h) := by
  obtain ⟨μ, hμ⟩ := deep_splits h2 α hh hon
  have hext := extract_lambda_split hV h2 hlb hh hG (fun k => deepFnAt lb α L h (ptD G h k)) _ μ hμ
  have hlam : lamAt G lb α L h = μ := by rw [lamAt, ldeVec]; simp only [ptD] at hext ⊢; rw [hext]; rfl
  rw [ldeVec]
  simp only [ptD] at hext ⊢
  rw [hext, hlam, corrCol]
  congr 2
  exact List.map_congr_left fun i _ =>
    (corr_ptD hV h2 α hlb hh hG hon (cfft_permute_index_lt h i)).symm

/-- The prover's lambdas, increasing in height, with the corrected columns. -/
theorem extractLambdas_honest (hV : CircleGenValid G) (h2 : (2 : K) ≠ 0) {lb H : ℕ} (α : K) {L : List (HMat K)}
    (hlb : 1 ≤ lb) (hG : H + 1 ≤ G.adicity) (hbd : ∀ h ∈ heightsOf lb L, lb + 2 ≤ h ∧ h ≤ H)
    (hon : ∀ h, HonestAt G lb L h) {st : (ℕ → K × List K) × List ℕ} (hst : ROInv G lb α L st) :
    extractLambdas G lb st.1 (st.2.mergeSort fun a b => decide (a ≤ b)) =
      some ((heightsOf lb L).map fun h => (h, lamAt G lb α L h, corrCol G lb α L h)) := by
  rw [show st.2.mergeSort (fun a b => decide (a ≤ b)) = heightsOf lb L by rw [hst.1]; rfl]
  refine mapM_eq_some_map _ _ _ fun h hh => ?_
  have hk : h ∈ st.2 := by
    rw [hst.1]; exact (List.mergeSort_perm _ _).mem_iff.mp hh
  have hb := hbd h hh
  simp only [show h ≠ 0 by omega, ↓reduceIte, hst.2 h hk, honestRO]
  rw [show ((List.range (2 ^ h)).map fun i => deepFnAt lb α L h (ptD G h (cfft_permute_index i h))) =
    ldeVec G lb α L h from rfl, extract_ldeVec hV h2 α hlb (by omega) (by omega) (hon h)]
  rfl

/-! ## Coefficients padded with zeros -/


/-- The first 2^m coefficients, then zeros. -/
def trunc (m : ℕ) (d : ℕ → K) : ℕ → K := fun k => if k < 2 ^ m then d k else 0

theorem bit_eq_zero_of_lt' {j k : ℕ} (h : j < 2 ^ k) : bit j k = 0 := by
  unfold bit; rw [Nat.div_eq_of_lt h]

theorem basis_mono {m n j : ℕ} (hmn : m ≤ n) (hj : j < 2 ^ m) (P : C K) : basis n j P = basis m j P := by
  unfold basis
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · obtain rfl : j = 0 := by simpa using hj
    simp [bit]
  · rw [← prod_Ico_consecutive _ (show 1 ≤ m by omega) hmn, prod_eq_one (s := Ico m n) fun k hk => by
      rw [bit_eq_zero_of_lt' (hj.trans_le (Nat.pow_le_pow_right (by norm_num) (mem_Ico.mp hk).1)), pow_zero],
      mul_one]

theorem xBasis_mono {m n k : ℕ} (hmn : m ≤ n) (hk : k < 2 ^ m) (x : K) : xBasis n k x = xBasis m k x := by
  unfold xBasis
  rw [← prod_range_mul_prod_Ico _ hmn, prod_eq_one (s := Ico m n) fun t ht => by
    rw [bit_eq_zero_of_lt' (hk.trans_le (Nat.pow_le_pow_right (by norm_num) (mem_Ico.mp ht).1)), pow_zero],
    mul_one]

/-- Padding the coefficients with zeros does not change the function. -/
theorem fftEval_trunc {m n : ℕ} (hmn : m ≤ n) (c : ℕ → K) (P : C K) :
    fftEval n (trunc m c) P = fftEval m c P := by
  unfold fftEval
  rw [← sum_range_add_sum_Ico _ (Nat.pow_le_pow_right (by norm_num) hmn), sum_eq_zero (s := Ico _ _) fun j hj => by
    simp [trunc, show ¬ j < 2 ^ m by have := (mem_Ico.mp hj).1; omega], add_zero]
  exact sum_congr rfl fun j hj => by
    have hj := mem_range.mp hj
    rw [basis_mono hmn hj]; simp [trunc, hj]

theorem xEval_trunc {m n : ℕ} (hmn : m ≤ n) (d : ℕ → K) (x : K) :
    xEval n (trunc m d) x = xEval m d x := by
  unfold xEval
  rw [← sum_range_add_sum_Ico _ (Nat.pow_le_pow_right (by norm_num) hmn), sum_eq_zero (s := Ico _ _) fun j hj => by
    simp [trunc, show ¬ j < 2 ^ m by have := (mem_Ico.mp hj).1; omega], add_zero]
  exact sum_congr rfl fun j hj => by
    have hj := mem_range.mp hj
    rw [xBasis_mono hmn hj]; simp [trunc, hj]

theorem foldCoeffs_trunc (m : ℕ) (d : ℕ → K) (β : K) :
    foldCoeffs (trunc (m + 1) d) β = trunc m (foldCoeffs d β) := by
  funext k
  simp only [foldCoeffs, trunc, pow_succ]
  split_ifs <;> first | ring1 | (exfalso; omega)

theorem trunc_add (m : ℕ) (d e : ℕ → K) : (fun k => trunc m d k + trunc m e k) = trunc m (fun k => d k + e k) := by
  funext k; simp only [trunc]; split_ifs <;> ring

/-! ## The first layer -/

theorem pairsOf_matOfPairs (v : List K) :
    pairsOf (matOfPairs v) = (List.range (v.length / 2)).map fun j => (v.getD (2 * j) 0, v.getD (2 * j + 1) 0) := by
  simp [pairsOf, matOfPairs]

/-- The first-layer fold of an honest corrected column is the codeword circle FRI starts from at that height. -/
theorem fold_y_honest (hV : CircleGenValid G) (h2 : (2 : K) ≠ 0) {lb : ℕ} (α β : K) {L : List (HMat K)} {h : ℕ}
    (hlb : 1 ≤ lb) (hh : lb + 2 ≤ h) (hG : h + 1 ≤ G.adicity) (hon : HonestAt G lb L h) :
    fold_y G β (pairsOf (matOfPairs (corrCol G lb α L h))) = some ((List.range (2 ^ (h - 1))).map fun b =>
      xEval (h - 1) (trunc (h - lb - 1) (foldCoeffs (deepCoeffs G lb α L h) β)) (Xp G h b)) := by
  obtain ⟨n, rfl⟩ : ∃ n, h = n + 1 := ⟨h - 1, by omega⟩
  set c := deepCoeffs G lb α L (n + 1)
  have hcol : ∀ k < 2 ^ (n + 1), (corrCol G lb α L (n + 1)).getD k 0 =
      fftEval (n + 1) (trunc (n + 1 - lb) c) (ptD G (n + 1) (cfft_permute_index k (n + 1))) := fun k hk => by
    rw [corrCol, List.getD_eq_getElem _ _ (by simpa using hk), List.getElem_map, List.getElem_range,
      corr_ptD hV h2 α hlb (by omega) hG hon (cfft_permute_index_lt _ _), fftEval_trunc (by omega)]
  have hpairs : pairsOf (matOfPairs (corrCol G lb α L (n + 1))) = (List.range (2 ^ (n + 1 - 1))).map fun b =>
      (fftEval (n + 1) (trunc (n + 1 - lb) c) (genPt G (n + 1 + 1) + rev (n + 1 - 1) b • genPt G (n + 1 - 1)),
        fftEval (n + 1) (trunc (n + 1 - lb) c) (-(genPt G (n + 1 + 1) + rev (n + 1 - 1) b • genPt G (n + 1 - 1)))) := by
    rw [pairsOf_matOfPairs, show (corrCol G lb α L (n + 1)).length / 2 = 2 ^ (n + 1 - 1) by
      simp [corrCol, pow_succ]]
    refine List.map_congr_left fun b hb => ?_
    have hb' : b < 2 ^ n := by simpa using hb
    obtain ⟨he, ho⟩ := ptD_pair hV (n := n) (by omega) hb'
    rw [hcol _ (by rw [pow_succ]; omega), hcol _ (by rw [pow_succ]; omega), he, ho]
    simp only [Nat.add_sub_cancel]
  rw [hpairs, fold_y_spec hV h2 (by omega) hG]
  congr 2
  funext b
  rw [show (fun k => trunc (n + 1 - lb) c (2 * k) + β * trunc (n + 1 - lb) c (2 * k + 1)) =
    foldCoeffs (trunc (n + 1 - lb - 1 + 1) c) β by rw [show n + 1 - lb - 1 + 1 = n + 1 - lb by omega]; rfl,
    foldCoeffs_trunc]

/-! ## The circle FRI commit phase -/

/-- The log height of the tallest of a batch of matrices. -/
def topLog (mats : List (Mat K)) : ℕ := (mats.map fun m => Nat.log 2 m.height).foldl max 0

/-- The methods of an honest commitment scheme:

- it returns the matrices it committed
- an opening holds, at each index, the row of every matrix at that index shifted down to its height
- the commitment accepts an opening of nonempty matrices of power-of-two heights at indices below the tallest. -/
structure MmcsHonest (mmcs : MmcsOps K) : Prop where
  get : ∀ mats, mmcs.get_matrices (mmcs.commit mats).2 = mats
  rows : ∀ mats idxs, (mmcs.open_multi_batch idxs (mmcs.commit mats).2).1 = idxs.map fun I => mats.map fun m =>
    (rowsOf m).getD (I / 2 ^ (topLog mats - Nat.log 2 m.height)) []
  accepts : ∀ mats idxs, mats ≠ [] → (∀ m ∈ mats, 2 ^ Nat.log 2 m.height = m.height) →
    (∀ I ∈ idxs, I < 2 ^ topLog mats) →
    mmcs.verify_multi_batch (mmcs.commit mats).1 (mats.map fun m => (m.width, m.height)) idxs
      (mmcs.open_multi_batch idxs (mmcs.commit mats).2).1 (mmcs.open_multi_batch idxs (mmcs.commit mats).2).2 = .ok ()

theorem layer_congr (E : ℕ → ℕ → K) {β β' : ℕ → K} : ∀ r, (∀ i < r, β i = β' i) → layer E β r = layer E β' r
  | 0, _ => rfl
  | r + 1, h => by
    simp only [layer]
    rw [layer_congr E r fun i hi => h i (by omega), h r (by omega)]

/-- The honest codeword of round r: the layer at the round's points, padded to the round's height. -/
noncomputable def cwAt (G : Gen (K × K)) (lb H : ℕ) (E : ℕ → ℕ → K) (β : ℕ → K) (r : ℕ) : List K :=
  (List.range (2 ^ (H - 1 - r))).map fun b =>
    xEval (H - 1 - r) (trunc (H - (lb + 1) - r) (layer E β r)) (Xp G (H - r) b)

/-- The first-layer codeword of height h: the folded DEEP function at the points of the height. -/
noncomputable def fiCW (G : Gen (K × K)) (lb : ℕ) (α β : K) (L : List (HMat K)) (h : ℕ) : List K :=
  (List.range (2 ^ (h - 1))).map fun b =>
    xEval (h - 1) (trunc (h - lb - 1) (foldCoeffs (deepCoeffs G lb α L h) β)) (Xp G h b)

theorem zipWith_add_map {α : Type _} (f g : α → K) (l : List α) :
    List.zipWith (· + ·) (l.map f) (l.map g) = l.map fun a => f a + g a := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [ih]

theorem length_fiCW (lb : ℕ) (α β : K) (L : List (HMat K)) (h : ℕ) :
    (fiCW G lb α β L h).length = 2 ^ (h - 1) := by simp [fiCW]

/-- The inputs still to be rolled in after round r: the first-layer codewords below height H - r, tallest first. -/
noncomputable def restAt (G : Gen (K × K)) (lb H : ℕ) (α β : K) (L : List (HMat K)) (r : ℕ) : List (List K) :=
  ((heightsOf lb L).reverse.filter (· < H - r)).map (fiCW G lb α β L)

theorem filter_lt_succ : ∀ {l : List ℕ}, l.Pairwise (· > ·) → ∀ k,
    l.filter (· < k + 1) = if k ∈ l then k :: l.filter (· < k) else l.filter (· < k)
  | [], _, k => by simp
  | a :: t, hl, k => by
    have ht := List.pairwise_cons.mp hl
    have ih := filter_lt_succ ht.2 k
    rcases lt_trichotomy a k with hak | rfl | hak
    · have hall : ∀ x ∈ t, x < a := fun x hx => ht.1 x hx
      have hk : k ∉ a :: t := by
        intro hk; rcases List.mem_cons.mp hk with h | h
        · omega
        · have := hall k h; omega
      have e1 : t.filter (· < k + 1) = t := List.filter_eq_self.mpr fun x hx => by
        have := hall x hx; simp; omega
      have e2 : t.filter (· < k) = t := List.filter_eq_self.mpr fun x hx => by
        have := hall x hx; simp; omega
      rw [List.filter_cons_of_pos (by simp; omega), List.filter_cons_of_pos (by simp; omega), e1, e2]
      simp only [hk, ↓reduceIte]
    · have hall : ∀ x ∈ t, x < a := fun x hx => ht.1 x hx
      have e1 : t.filter (· < a + 1) = t := List.filter_eq_self.mpr fun x hx => by
        have := hall x hx; simp; omega
      have e2 : t.filter (· < a) = t := List.filter_eq_self.mpr fun x hx => by
        have := hall x hx; simp; omega
      rw [List.filter_cons_of_pos (by simp), List.filter_cons_of_neg (by simp), e1, e2]
      simp
    · have hka : k ≠ a := by omega
      simp only [List.filter_cons, show ¬ a < k + 1 by omega, show ¬ a < k by omega, decide_false,
        Bool.false_eq_true, ↓reduceIte, List.mem_cons, hka, false_or]
      exact ih

theorem restAt_succ {lb H : ℕ} (α β : K) (L : List (HMat K)) {r : ℕ} (hr : r + 1 ≤ H) :
    restAt G lb H α β L r = if H - (r + 1) ∈ heightsOf lb L then
      fiCW G lb α β L (H - (r + 1)) :: restAt G lb H α β L (r + 1) else restAt G lb H α β L (r + 1) := by
  have hp : (heightsOf lb L).reverse.Pairwise (· > ·) :=
    List.pairwise_reverse.mpr ((heightsOf_pairwise lb L).imp id)
  unfold restAt
  rw [show H - r = H - (r + 1) + 1 by omega, filter_lt_succ hp]
  by_cases hm : H - (r + 1) ∈ heightsOf lb L <;> simp [hm]

theorem length_cwAt (lb H : ℕ) (E : ℕ → ℕ → K) (β : ℕ → K) (r : ℕ) :
    (cwAt G lb H E β r).length = 2 ^ (H - 1 - r) := by simp [cwAt]

/-- One commit round on the honest codeword: the fold of round r, with the input of height H - (r + 1) rolled in. -/
theorem commitRound_honest (hV : CircleGenValid G) (h2 : (2 : K) ≠ 0) {lb H : ℕ} (α bβ : K) {L : List (HMat K)}
    (hlb : 1 ≤ lb) (hG : H + 1 ≤ G.adicity) (fmmcs : MmcsOps K) (hmm : MmcsHonest fmmcs) {S : Type _}
    (tx : CircleProverTx K fmmcs.Commitment S) {r : ℕ} (hr : r + 1 ≤ H - (lb + 1)) (bl : List K) (hbl : bl.length = r)
    (cs : List fmmcs.Commitment) (ds : List fmmcs.ProverData) (ws : List K) (s : S) :
    commitRound G fmmcs tx (cwAt G lb H (friCoeffs G lb H α bβ L) (bl.getD · 0) r, restAt G lb H α bβ L r,
        cs, ds, ws, s) =
      some (cwAt G lb H (friCoeffs G lb H α bβ L)
          ((bl ++ [(tx.commit_round s (fmmcs.commit [matOfPairs (cwAt G lb H (friCoeffs G lb H α bβ L)
            (bl.getD · 0) r)]).1).1]).getD · 0) (r + 1),
        restAt G lb H α bβ L (r + 1),
        cs ++ [(fmmcs.commit [matOfPairs (cwAt G lb H (friCoeffs G lb H α bβ L) (bl.getD · 0) r)]).1],
        ds ++ [(fmmcs.commit [matOfPairs (cwAt G lb H (friCoeffs G lb H α bβ L) (bl.getD · 0) r)]).2],
        ws ++ [((tx.commit_round s (fmmcs.commit [matOfPairs (cwAt G lb H (friCoeffs G lb H α bβ L)
          (bl.getD · 0) r)]).1).2.1).getD 0],
        (tx.commit_round s (fmmcs.commit [matOfPairs (cwAt G lb H (friCoeffs G lb H α bβ L)
          (bl.getD · 0) r)]).1).2.2) := by
  set E := friCoeffs G lb H α bβ L
  set cw := cwAt G lb H E (bl.getD · 0) r
  set c := (fmmcs.commit [matOfPairs cw]).1
  set β := (tx.commit_round s c).1
  set bl' := bl ++ [β]
  have hβr : bl'.getD r 0 = β := by simp [bl', List.getD_eq_getElem?_getD, hbl]
  have hlay : layer E (bl.getD · 0) r = layer E (bl'.getD · 0) r :=
    layer_congr E r fun i hi => by simp [bl', List.getD_eq_getElem?_getD, List.getElem?_append_left (hbl ▸ hi)]
  obtain ⟨n, hn⟩ : ∃ n, H - 1 - r = n + 1 := ⟨H - 2 - r, by omega⟩
  -- The fold of the round.
  have hfold : fold_x G β 1 (pairsOf (matOfPairs cw)) = some ((List.range (2 ^ n)).map fun b =>
      xEval n (trunc (H - (lb + 1) - (r + 1)) (foldCoeffs (layer E (bl'.getD · 0) r) β)) (Xp G (n + 1) b)) := by
    have hpairs : pairsOf (matOfPairs cw) = (List.range (2 ^ n)).map fun b =>
        (xEval (n + 1) (trunc (H - (lb + 1) - (r + 1) + 1) (layer E (bl'.getD · 0) r)) (Xp G (n + 2) (2 * b)),
          xEval (n + 1) (trunc (H - (lb + 1) - (r + 1) + 1) (layer E (bl'.getD · 0) r)) (Xp G (n + 2) (2 * b + 1))) := by
      rw [pairsOf_matOfPairs, length_cwAt, hn, pow_succ, Nat.mul_div_cancel _ (by norm_num)]
      refine List.map_congr_left fun b hb => ?_
      have hb' := List.mem_range.mp hb
      simp only [cw, cwAt, hn, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range
        (show 2 * b < 2 ^ (n + 1) by rw [pow_succ]; omega), List.getElem?_range
        (show 2 * b + 1 < 2 ^ (n + 1) by rw [pow_succ]; omega), Option.map_some, Option.getD_some,
        show H - r = n + 2 by omega, show H - (lb + 1) - (r + 1) + 1 = H - (lb + 1) - r by omega]
      have hlay' := hlay
      simp only [List.getD_eq_getElem?_getD] at hlay'
      rw [hlay']
    rw [hpairs, fold_x_spec hV h2 (by omega)]
    congr 2
    funext b
    rw [show (fun k => trunc (H - (lb + 1) - (r + 1) + 1) (layer E (bl'.getD · 0) r) (2 * k) +
        β * trunc (H - (lb + 1) - (r + 1) + 1) (layer E (bl'.getD · 0) r) (2 * k + 1)) =
      foldCoeffs (trunc (H - (lb + 1) - (r + 1) + 1) (layer E (bl'.getD · 0) r)) β from rfl, foldCoeffs_trunc]
  have hnext : cwAt G lb H E (bl'.getD · 0) (r + 1) = (List.range (2 ^ n)).map fun b =>
      xEval n (trunc (H - (lb + 1) - (r + 1)) (fun k => foldCoeffs (layer E (bl'.getD · 0) r) β k + E (r + 1) k))
        (Xp G (n + 1) b) := by
    simp only [cwAt, layer, hβr, show H - 1 - (r + 1) = n by omega, show H - (r + 1) = n + 1 by omega]
  unfold commitRound
  simp only [hmm.get, List.getLast?_singleton, Option.bind_eq_bind, Option.bind_some]
  rw [hfold, Option.bind_some, hnext, restAt_succ α bβ L (by omega)]
  by_cases hm : H - (r + 1) ∈ heightsOf lb L
  · simp only [hm, ↓reduceIte, length_fiCW, List.length_map, List.length_range,
      show H - (r + 1) - 1 = n by omega]
    refine congrArg some (Prod.ext ?_ (Prod.ext rfl rfl))
    rw [fiCW, show H - (r + 1) - 1 = n by omega, show H - (r + 1) = n + 1 by omega, zipWith_add_map]
    refine List.map_congr_left fun b _ => ?_
    rw [← xEval_add, show n + 1 - lb - 1 = H - (lb + 1) - (r + 1) by omega, trunc_add]
    congr 3
    funext k
    simp only [E, friCoeffs, show H - (r + 1) = n + 1 by omega] at hm ⊢
    simp only [hm, ↓reduceIte]
  · have hE : E (r + 1) = fun _ => 0 := by simp [E, friCoeffs, hm]
    simp only [hm, ↓reduceIte, hE, add_zero]
    rcases hrest : restAt G lb H α bβ L (r + 1) with _ | ⟨v, rest'⟩
    · exact congrArg some (Prod.ext rfl (Prod.ext rfl rfl))
    · have hv : v ∈ restAt G lb H α bβ L (r + 1) := by rw [hrest]; exact List.mem_cons_self
      obtain ⟨h', hh', rfl⟩ := List.mem_map.mp hv
      have hh'' := List.mem_filter.mp hh'
      have hlt : h' < H - (r + 1) := by simpa using hh''.2
      have hlen : (fiCW G lb α bβ L h').length ≠ (List.map (fun b => xEval n (trunc (H - (lb + 1) - (r + 1))
          (foldCoeffs (layer E (bl'.getD · 0) r) β)) (Xp G (n + 1) b)) (List.range (2 ^ n))).length := by
        rw [length_fiCW, List.length_map, List.length_range]
        intro heq
        have := Nat.pow_right_injective (le_refl 2) heq
        omega
      simp only [hlen, ↓reduceIte]
      exact congrArg some (Prod.ext rfl (Prod.ext rfl rfl))

/-- The honest commit phase's first k rounds: the betas, commitments, prover data, witnesses, and state. -/
noncomputable def honestRun (G : Gen (K × K)) (lb H : ℕ) (E : ℕ → ℕ → K) (fmmcs : MmcsOps K) {S : Type _}
    (tx : CircleProverTx K fmmcs.Commitment S) (s : S) :
    ℕ → List K × List fmmcs.Commitment × List fmmcs.ProverData × List K × S
  | 0 => ([], [], [], [], s)
  | k + 1 =>
    let (bl, cs, ds, ws, s1) := honestRun G lb H E fmmcs tx s k
    let cd := fmmcs.commit [matOfPairs (cwAt G lb H E (bl.getD · 0) k)]
    let bws := tx.commit_round s1 cd.1
    (bl ++ [bws.1], cs ++ [cd.1], ds ++ [cd.2], ws ++ [bws.2.1.getD 0], bws.2.2)

theorem honestRun_length (lb H : ℕ) (E : ℕ → ℕ → K) (fmmcs : MmcsOps K) {S : Type _}
    (tx : CircleProverTx K fmmcs.Commitment S) (s : S) :
    ∀ k, (honestRun G lb H E fmmcs tx s k).1.length = k ∧ (honestRun G lb H E fmmcs tx s k).2.1.length = k ∧
      (honestRun G lb H E fmmcs tx s k).2.2.1.length = k ∧ (honestRun G lb H E fmmcs tx s k).2.2.2.1.length = k
  | 0 => by simp [honestRun]
  | k + 1 => by
    obtain ⟨h1, h2, h3, h4⟩ := honestRun_length lb H E fmmcs tx s k
    simp [honestRun, h1, h2, h3, h4]

/-- The commit rounds of the honest run: after k rounds the prover holds round k's codeword and inputs. -/
theorem foldlM_commitRound_honest (hV : CircleGenValid G) (h2 : (2 : K) ≠ 0) {lb H : ℕ} (α bβ : K)
    {L : List (HMat K)} (hlb : 1 ≤ lb) (hG : H + 1 ≤ G.adicity) (fmmcs : MmcsOps K) (hmm : MmcsHonest fmmcs)
    {S : Type _} (tx : CircleProverTx K fmmcs.Commitment S) (s : S) :
    ∀ k ≤ H - (lb + 1), (List.range k).foldlM (fun st _ => commitRound G fmmcs tx st)
        (cwAt G lb H (friCoeffs G lb H α bβ L) (fun _ => 0) 0, restAt G lb H α bβ L 0, [], [], [], s) =
      some (cwAt G lb H (friCoeffs G lb H α bβ L)
          ((honestRun G lb H (friCoeffs G lb H α bβ L) fmmcs tx s k).1.getD · 0) k,
        restAt G lb H α bβ L k, (honestRun G lb H (friCoeffs G lb H α bβ L) fmmcs tx s k).2.1,
        (honestRun G lb H (friCoeffs G lb H α bβ L) fmmcs tx s k).2.2.1,
        (honestRun G lb H (friCoeffs G lb H α bβ L) fmmcs tx s k).2.2.2.1,
        (honestRun G lb H (friCoeffs G lb H α bβ L) fmmcs tx s k).2.2.2.2)
  | 0, _ => by simp [honestRun, cwAt, layer]
  | k + 1, hk => by
    rw [List.range_succ, List.foldlM_append, foldlM_commitRound_honest hV h2 α bβ hlb hG fmmcs hmm tx s k (by omega),
      Option.bind_eq_bind, Option.bind_some, List.foldlM_cons]
    rw [commitRound_honest hV h2 α bβ hlb hG fmmcs hmm tx (by omega) _
      (honestRun_length lb H _ fmmcs tx s k).1]
    rfl

theorem xEval_trunc_zero (n : ℕ) (d : ℕ → K) (x : K) : xEval n (trunc 0 d) x = d 0 := by
  rw [xEval_trunc (Nat.zero_le n)]; simp [xEval, xBasis]

/-- The honest commit phase: the run's commitments, data and witnesses, and the folded constant. -/
theorem commitPhase_honest (hV : CircleGenValid G) (h2 : (2 : K) ≠ 0) {lb H : ℕ} (α bβ : K) {L : List (HMat K)}
    (hlb : 1 ≤ lb) (hG : H + 1 ≤ G.adicity) (hbd : ∀ h ∈ heightsOf lb L, lb + 2 ≤ h ∧ h ≤ H)
    (hH : H ∈ heightsOf lb L) (fmmcs : MmcsOps K) (hmm : MmcsHonest fmmcs) {S : Type _}
    (tx : CircleProverTx K fmmcs.Commitment S) (s : S) :
    commitPhase G fmmcs tx lb ((heightsOf lb L).reverse.map (fiCW G lb α bβ L)) s =
      some ((honestRun G lb H (friCoeffs G lb H α bβ L) fmmcs tx s (H - (lb + 1))).2.1,
        (honestRun G lb H (friCoeffs G lb H α bβ L) fmmcs tx s (H - (lb + 1))).2.2.1,
        (honestRun G lb H (friCoeffs G lb H α bβ L) fmmcs tx s (H - (lb + 1))).2.2.2.1,
        layer (friCoeffs G lb H α bβ L)
          ((honestRun G lb H (friCoeffs G lb H α bβ L) fmmcs tx s (H - (lb + 1))).1.getD · 0) (H - (lb + 1)) 0,
        (honestRun G lb H (friCoeffs G lb H α bβ L) fmmcs tx s (H - (lb + 1))).2.2.2.2) := by
  set E := friCoeffs G lb H α bβ L
  set R := H - (lb + 1)
  have hHb := hbd H hH
  have hp : (heightsOf lb L).reverse.Pairwise (· > ·) :=
    List.pairwise_reverse.mpr ((heightsOf_pairwise lb L).imp id)
  have hinputs : (heightsOf lb L).reverse.map (fiCW G lb α bβ L) =
      cwAt G lb H E (fun _ => 0) 0 :: restAt G lb H α bβ L 0 := by
    have hall : (heightsOf lb L).reverse.filter (· < H + 1) = (heightsOf lb L).reverse :=
      List.filter_eq_self.mpr fun x hx => by
        have := hbd x (List.mem_reverse.mp hx); simp; omega
    rw [← hall, filter_lt_succ hp]
    simp only [List.mem_reverse, hH, ↓reduceIte]
    rw [List.map_cons, restAt, Nat.sub_zero]
    congr 1
    simp only [fiCW, cwAt, layer, E, friCoeffs, Nat.sub_zero, hH, ↓reduceIte, show H - 1 - 0 = H - 1 from rfl,
      show H - (lb + 1) = H - lb - 1 by omega]
  rw [hinputs, commitPhase]
  simp only [length_cwAt, Nat.sub_zero, log2Strict_pow, Option.bind_eq_bind, Option.bind_some]
  rw [show H - 1 - lb = R by omega, foldlM_commitRound_honest hV h2 α bβ hlb hG fmmcs hmm tx s R le_rfl,
    Option.bind_some]
  have hcw : cwAt G lb H E ((honestRun G lb H E fmmcs tx s R).1.getD · 0) R =
      List.replicate (2 ^ lb) (layer E ((honestRun G lb H E fmmcs tx s R).1.getD · 0) R 0) := by
    rw [cwAt, show H - (lb + 1) - R = 0 by omega, show H - 1 - R = lb by omega]
    simp only [xEval_trunc_zero]
    simp
  rw [hcw]
  simp [List.length_replicate, List.head?_replicate, E, R]

/-! ## The query answers -/

theorem topLog_singleton (m : Mat K) : topLog [m] = Nat.log 2 m.height := by simp [topLog]

theorem rowsOf_matOfPairs_getD (v : List K) {j : ℕ} (hj : j < v.length / 2) :
    (rowsOf (matOfPairs v)).getD j [] = [v.getD (2 * j) 0, v.getD (2 * j + 1) 0] := by
  simp [rowsOf, matOfPairs, List.getD_eq_getElem?_getD, hj, List.finRange_succ]

/-- The answers of one round on a committed codeword: at each query, the other member of its pair. -/
noncomputable def roundAnswer (fmmcs : MmcsOps K) (cw : List K) (cur : List ℕ) :
    CommitPhaseMultiStep K fmmcs.MultiProof :=
  ⟨cur.map fun t => [cw.getD (2 * (t / 2) + (1 - t % 2)) 0],
    (fmmcs.open_multi_batch (cur.map (· / 2)) (fmmcs.commit [matOfPairs cw]).2).2⟩

/-- The answers of every round, the indices halving each round. -/
noncomputable def answersOf (fmmcs : MmcsOps K) : List (List K) → List ℕ → List (CommitPhaseMultiStep K fmmcs.MultiProof)
  | [], _ => []
  | cw :: cws, cur => roundAnswer fmmcs cw cur :: answersOf fmmcs cws (cur.map (· / 2))

theorem pair_sibling (a b : K) (t : ℕ) :
    (([a, b].zipIdx.filter fun p => p.2 ≠ t % 2).map Prod.fst) = [[a, b].getD (1 - t % 2) 0] := by
  rcases Nat.mod_two_eq_zero_or_one t with h | h <;> simp [h, List.zipIdx]

/-- One round of the query answers. -/
def aqStep (fmmcs : MmcsOps K) (st : List ℕ × List (CommitPhaseMultiStep K fmmcs.MultiProof))
    (pd : fmmcs.ProverData) : Option (List ℕ × List (CommitPhaseMultiStep K fmmcs.MultiProof)) := do
  let (current, acc) := st
  let group_indices := current.map (· / 2)
  let (opened_rows, opening_proof) := fmmcs.open_multi_batch group_indices pd
  let siblings ← (current.zip opened_rows).mapM fun (index, rows) =>
    match rows with
    | [row] => if row.length ≠ 2 then none else some ((row.zipIdx.filter fun p => p.2 ≠ index % 2).map Prod.fst)
    | _ => none
  pure (group_indices, acc ++ [⟨siblings, opening_proof⟩])

theorem answerQueries_eq (fmmcs : MmcsOps K) (data : List fmmcs.ProverData) (start : List ℕ) :
    answerQueries fmmcs data start = (data.foldlM (aqStep fmmcs) (start, [])).map (·.2) := by
  unfold answerQueries
  show (data.foldlM (aqStep fmmcs) (start, []) >>= fun x => match x with | (_, out) => pure out) = _
  rcases data.foldlM (aqStep fmmcs) (start, []) with _ | ⟨a, b⟩ <;> rfl

theorem zip_map_self' {α β : Type _} (g : α → β) : ∀ (l : List α), l.zip (l.map g) = l.map fun a => (a, g a)
  | [] => rfl
  | a :: l => by simp [zip_map_self' g l]

/-- One round of answers on a committed codeword whose pairs the indices reach. -/
theorem aqStep_honest (fmmcs : MmcsOps K) (hmm : MmcsHonest fmmcs) (cw : List K) (cur : List ℕ)
    (hb : ∀ t ∈ cur, t / 2 < cw.length / 2) (acc : List (CommitPhaseMultiStep K fmmcs.MultiProof)) :
    aqStep fmmcs (cur, acc) (fmmcs.commit [matOfPairs cw]).2 =
      some (cur.map (· / 2), acc ++ [roundAnswer fmmcs cw cur]) := by
  unfold aqStep
  simp only [hmm.rows, topLog_singleton, List.map_cons, List.map_nil, Nat.sub_self, pow_zero, Nat.div_one,
    List.map_map]
  rw [zip_map_self']
  rw [List.mapM_map, mapM_eq_some_map _ _ (fun t => [cw.getD (2 * (t / 2) + (1 - t % 2)) 0]) fun t ht => by
    simp only [Function.comp_apply, rowsOf_matOfPairs_getD cw (hb t ht), List.length_cons, List.length_nil,
      ne_eq, not_true_eq_false, ↓reduceIte, pair_sibling]
    rcases Nat.mod_two_eq_zero_or_one t with h | h <;> simp [h]]
  rfl

/-- The query answers on committed codewords whose pairs the indices reach. -/
theorem foldlM_aqStep_honest (fmmcs : MmcsOps K) (hmm : MmcsHonest fmmcs) :
    ∀ (cws : List (List K)) (cur : List ℕ),
      (∀ k (hk : k < cws.length), ∀ t ∈ cur, t / 2 ^ k / 2 < cws[k].length / 2) →
      ∀ acc, (cws.map fun cw => (fmmcs.commit [matOfPairs cw]).2).foldlM (aqStep fmmcs) (cur, acc) =
        some (cur.map (· / 2 ^ cws.length), acc ++ answersOf fmmcs cws cur)
  | [], cur, _, acc => by simp [answersOf]
  | cw :: cws, cur, hb, acc => by
    rw [List.map_cons, List.foldlM_cons, aqStep_honest fmmcs hmm cw cur (fun t ht => by
        have := hb 0 (by simp) t ht; simpa only [List.getElem_cons_zero, pow_zero, Nat.div_one] using this),
      Option.bind_eq_bind, Option.bind_some, foldlM_aqStep_honest fmmcs hmm cws (cur.map (· / 2)) (fun k hk t ht => by
        obtain ⟨t0, ht0, rfl⟩ := List.mem_map.mp ht
        have := hb (k + 1) (by simpa using hk) t0 ht0
        simp only [List.getElem_cons_succ] at this
        rwa [Nat.div_div_eq_div_mul t0 2 (2 ^ k), ← pow_succ'])]
    simp only [List.map_map, List.length_cons, answersOf, List.append_assoc, List.singleton_append]
    refine congrArg some (Prod.ext (List.map_congr_left fun t _ => ?_) rfl)
    simp [Nat.div_div_eq_div_mul, pow_succ']

/-! ## The input openings -/

theorem le_foldl_max_init : ∀ (l : List ℕ) (a : ℕ), a ≤ l.foldl max a
  | [], _ => le_rfl
  | b :: l, a => (le_max_left a b).trans (le_foldl_max_init l _)

theorem le_foldl_max_mem : ∀ (l : List ℕ) (a x : ℕ), x ∈ l → x ≤ l.foldl max a
  | [], _, _, h => by simp at h
  | b :: l, a, x, h => by
    rcases List.mem_cons.mp h with rfl | h
    · exact (le_max_right a x).trans (le_foldl_max_init l _)
    · exact le_foldl_max_mem l _ x h

theorem foldl_max_mem : ∀ (l : List ℕ) (a : ℕ), l.foldl max a ∈ a :: l
  | [], a => by simp
  | b :: l, a => by
    rcases List.mem_cons.mp (foldl_max_mem l (max a b)) with h | h
    · rw [List.foldl_cons, h]; rcases max_choice a b with h' | h' <;> simp [h']
    · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h)

/-- The tallest height of a nonempty batch of powers of two is 2 to the tallest log. -/
theorem max?_pow (ks : List ℕ) (hks : ks ≠ []) : (ks.map (2 ^ ·)).max? = some (2 ^ ks.foldl max 0) := by
  rw [List.max?_eq_some_iff]
  refine ⟨?_, fun b hb => ?_⟩
  · rcases List.mem_cons.mp (foldl_max_mem ks 0) with h | h
    · obtain ⟨k, hk⟩ := List.exists_mem_of_ne_nil ks hks
      have := le_foldl_max_mem ks 0 k hk
      rw [h] at this ⊢
      exact List.mem_map.mpr ⟨k, hk, by rw [show k = 0 by omega]⟩
    · exact List.mem_map_of_mem h
  · obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hb
    exact Nat.pow_le_pow_right (by norm_num) (le_foldl_max_mem ks 0 k hk)

theorem topLog_ldeMat (lb : ℕ) (ms : List (HMat K)) : topLog (ms.map (ldeMat G lb)) = (ms.map (hgt lb)).foldl max 0 := by
  simp [topLog, ldeMat, Nat.log_pow (by norm_num : 1 < 2), Function.comp_def]

theorem rowsOf_ldeMat_getD (lb : ℕ) (m : HMat K) {r : ℕ} (hr : r < 2 ^ hgt lb m) :
    (rowsOf (ldeMat G lb m)).getD r [] = m.2.map (· (ptD G (hgt lb m) (cfft_permute_index r (hgt lb m)))) := by
  rw [rowsOf_ldeMat, List.getD_eq_getElem _ _ (by simpa using hr)]
  simp

theorem foldl_max_hgt_le {lb H : ℕ} {ms : List (HMat K)} (hH : ∀ m ∈ ms, hgt lb m ≤ H) :
    (ms.map (hgt lb)).foldl max 0 ≤ H := by
  rcases List.mem_cons.mp (foldl_max_mem (ms.map (hgt lb)) 0) with h | h
  · rw [h]; omega
  · obtain ⟨m, hm, he⟩ := List.mem_map.mp h; rw [← he]; exact hH m hm

/-- The rows of an honest batch's opening: at each query, the columns at the point of each matrix's height. -/
theorem inputRows_honest (hV : CircleGenValid G) (immcs : MmcsOps K) (hmm : MmcsHonest immcs) {lb H : ℕ}
    (ms : List (HMat K)) (hH : ∀ m ∈ ms, hgt lb m ≤ H) (hn : ∀ m ∈ ms, 1 ≤ m.1.domain.log_n)
    (hG : H + 1 ≤ G.adicity) (indices : List ℕ) (hidx : ∀ i ∈ indices, i < 2 ^ H) :
    (immcs.open_multi_batch (indices.map (· / 2 ^ (H - (ms.map (hgt lb)).foldl max 0)))
        (immcs.commit (ms.map (ldeMat G lb))).2).1 =
      indices.map fun i => ms.map fun m => m.2.map (· (qPt G H i (hgt lb m))) := by
  have htopH := foldl_max_hgt_le hH
  set top := (ms.map (hgt lb)).foldl max 0
  rw [hmm.rows, topLog_ldeMat, List.map_map]
  refine List.map_congr_left fun i hi => ?_
  rw [Function.comp_apply, List.map_map]
  refine List.map_congr_left fun m hm => ?_
  have hmH := hH m hm
  have hmt : hgt lb m ≤ top := le_foldl_max_mem _ 0 _ (List.mem_map_of_mem hm)
  have hidx' := hidx i hi
  have hdiv : i / 2 ^ (H - top) / 2 ^ (top - Nat.log 2 (ldeMat G lb m).height) = i / 2 ^ (H - hgt lb m) := by
    rw [show (ldeMat G lb m).height = 2 ^ hgt lb m from rfl, Nat.log_pow (by norm_num), Nat.div_div_eq_div_mul,
      ← pow_add, show H - top + (top - hgt lb m) = H - hgt lb m by omega]
  rw [Function.comp_apply, show (ms.map (hgt lb)).foldl max 0 = top from rfl, hdiv, rowsOf_ldeMat_getD lb m (by
    rw [Nat.div_lt_iff_lt_mul (by positivity), ← pow_add, show hgt lb m + (H - hgt lb m) = H by omega]; exact hidx'),
    qPt_eq hV i (by have := hn m hm; unfold hgt; omega) (by omega)]

/-- The input openings of honest batches: each batch opens once, at the indices shifted to its tallest height. -/
theorem openInputs_honest (immcs : MmcsOps K) (hmm : MmcsHonest immcs) {lb H : ℕ}
    (hb : List (List (HMat K))) (hne : ∀ ms ∈ hb, ms ≠ []) (hH : ∀ m ∈ hb.flatten, hgt lb m ≤ H)
    (indices : List ℕ) :
    openInputs immcs H indices (hb.map fun ms => (immcs.commit (ms.map (ldeMat G lb))).2) =
      some (hb.map fun ms => ⟨(immcs.open_multi_batch (indices.map (· / 2 ^ (H - (ms.map (hgt lb)).foldl max 0)))
          (immcs.commit (ms.map (ldeMat G lb))).2).1,
        (immcs.open_multi_batch (indices.map (· / 2 ^ (H - (ms.map (hgt lb)).foldl max 0)))
          (immcs.commit (ms.map (ldeMat G lb))).2).2⟩) := by
  unfold openInputs
  rw [List.mapM_map]
  refine mapM_eq_some_map _ _ _ fun ms hms => ?_
  have htopH := foldl_max_hgt_le (lb := lb) fun m hm => hH m (List.mem_flatten.mpr ⟨ms, hms, hm⟩)
  have hmax : ((ms.map (ldeMat G lb)).map Mat.height).max? = some (2 ^ (ms.map (hgt lb)).foldl max 0) := by
    rw [List.map_map, show (Mat.height ∘ ldeMat G lb) = (2 ^ ·) ∘ hgt lb from rfl, ← List.map_map,
      max?_pow _ (by simpa using hne ms hms)]
  simp only [Function.comp_apply, hmm.get, hmax, log2Strict_pow, Option.bind_eq_bind, Option.bind_some,
    show ¬ H < (ms.map (hgt lb)).foldl max 0 by omega, ↓reduceIte, Option.pure_def]

/-! ## The first-layer openings -/

theorem length_corrCol (lb : ℕ) (α : K) (L : List (HMat K)) (h : ℕ) : (corrCol G lb α L h).length = 2 ^ h := by
  simp [corrCol]

theorem corrCol_getD (lb : ℕ) (α : K) (L : List (HMat K)) {h k : ℕ} (hk : k < 2 ^ h) :
    (corrCol G lb α L h).getD k 0 = corr G lb α L h (ptD G h (cfft_permute_index k h)) := by
  rw [corrCol, List.getD_eq_getElem _ _ (by simpa using hk)]; simp

/-- The first-layer row of height h at a query is the committed pair its index reaches. -/
theorem flVals_eq_row (hV : CircleGenValid G) {lb H : ℕ} (α : K) (L : List (HMat K)) {h i : ℕ} (hh : 1 ≤ h)
    (hhH : h ≤ H) (hG : H + 1 ≤ G.adicity) (hi : i < 2 ^ H) :
    flVals G lb H α L h i = [(corrCol G lb α L h).getD (2 * (i / 2 ^ (H - h) / 2)) 0,
      (corrCol G lb α L h).getD (2 * (i / 2 ^ (H - h) / 2) + 1) 0] := by
  obtain ⟨n, rfl⟩ : ∃ n, h = n + 1 := ⟨h - 1, by omega⟩
  have hri : i / 2 ^ (H - (n + 1)) < 2 ^ (n + 1) := by
    rw [Nat.div_lt_iff_lt_mul (by positivity), ← pow_add, show n + 1 + (H - (n + 1)) = H by omega]; exact hi
  have hP := qPt_eq hV (H := H) i (by omega : 1 ≤ n + 1) (by omega)
  unfold flVals qBit
  rw [hP]
  rcases Nat.even_or_odd' (i / 2 ^ (H - (n + 1))) with ⟨j, hj | hj⟩ <;> rw [hj] <;>
    have hj' : j < 2 ^ n := by rw [pow_succ] at hri; omega
  · obtain ⟨he, ho⟩ := ptD_pair hV (n := n) (by omega) hj'
    simp only [Nat.mul_mod_right, ↓reduceIte, show 2 * j / 2 = j by omega]
    rw [corrCol_getD lb α L (by rw [pow_succ]; omega), corrCol_getD lb α L (by rw [pow_succ]; omega), he, ho]
  · obtain ⟨he, ho⟩ := ptD_pair hV (n := n) (by omega) hj'
    simp only [show (2 * j + 1) % 2 = 1 by omega, one_ne_zero, ↓reduceIte, show (2 * j + 1) / 2 = j by omega]
    rw [corrCol_getD lb α L (by rw [pow_succ]; omega), corrCol_getD lb α L (by rw [pow_succ]; omega), he, ho,
      neg_neg]

theorem height_matOfPairs_corrCol (lb : ℕ) (α : K) (L : List (HMat K)) {h : ℕ} (hh : 1 ≤ h) :
    (matOfPairs (corrCol G lb α L h)).height = 2 ^ (h - 1) := by
  simp only [matOfPairs, length_corrCol]
  obtain ⟨n, rfl⟩ : ∃ n, h = n + 1 := ⟨h - 1, by omega⟩
  simp [pow_succ]

theorem topLog_firstLayer {lb H : ℕ} (α : K) (L : List (HMat K)) (hH : H ∈ heightsOf lb L)
    (hbd : ∀ h ∈ heightsOf lb L, lb + 2 ≤ h ∧ h ≤ H) :
    topLog ((heightsOf lb L).map fun h => matOfPairs (corrCol G lb α L h)) = H - 1 := by
  have hlogs : ((heightsOf lb L).map fun h => matOfPairs (corrCol G lb α L h)).map (fun m => Nat.log 2 m.height) =
      (heightsOf lb L).map (· - 1) := by
    simp only [List.map_map]
    refine List.map_congr_left fun h hh => ?_
    have := hbd h hh
    simp [height_matOfPairs_corrCol lb α L (show 1 ≤ h by omega), Nat.log_pow (by norm_num : 1 < 2)]
  rw [topLog, hlogs]
  refine le_antisymm ?_ (le_foldl_max_mem _ 0 _ (List.mem_map_of_mem hH))
  rcases List.mem_cons.mp (foldl_max_mem ((heightsOf lb L).map (· - 1)) 0) with h | h
  · rw [h]; omega
  · obtain ⟨h', hh', he⟩ := List.mem_map.mp h; rw [← he]; have := hbd h' hh'; omega

/-- The first-layer openings: at each query, the rows of every height that the index reaches. -/
theorem firstLayer_open_honest (hV : CircleGenValid G) (fmmcs : MmcsOps K) (hmm : MmcsHonest fmmcs) {lb H : ℕ}
    (α : K) (L : List (HMat K)) (hH : H ∈ heightsOf lb L) (hbd : ∀ h ∈ heightsOf lb L, lb + 2 ≤ h ∧ h ≤ H)
    (hG : H + 1 ≤ G.adicity) (indices : List ℕ) (hidx : ∀ i ∈ indices, i < 2 ^ H) :
    (fmmcs.open_multi_batch (indices.map (· / 2))
        (fmmcs.commit ((heightsOf lb L).map fun h => matOfPairs (corrCol G lb α L h))).2).1 =
      indices.map fun i => (heightsOf lb L).map fun h => flVals G lb H α L h i := by
  have hlogs : ((heightsOf lb L).map fun h => matOfPairs (corrCol G lb α L h)).map (fun m => Nat.log 2 m.height) =
      (heightsOf lb L).map (· - 1) := by
    simp only [List.map_map]
    refine List.map_congr_left fun h hh => ?_
    have := hbd h hh
    simp [height_matOfPairs_corrCol lb α L (show 1 ≤ h by omega), Nat.log_pow (by norm_num : 1 < 2)]
  have htop : topLog ((heightsOf lb L).map fun h => matOfPairs (corrCol G lb α L h)) = H - 1 := by
    rw [topLog, hlogs]
    refine le_antisymm ?_ (le_foldl_max_mem _ 0 _ (List.mem_map_of_mem hH))
    rcases List.mem_cons.mp (foldl_max_mem ((heightsOf lb L).map (· - 1)) 0) with h | h
    · rw [h]; omega
    · obtain ⟨h', hh', he⟩ := List.mem_map.mp h; rw [← he]; have := hbd h' hh'; omega
  rw [hmm.rows, htop, List.map_map]
  refine List.map_congr_left fun i hi => ?_
  rw [Function.comp_apply, List.map_map]
  refine List.map_congr_left fun h hh => ?_
  have hb := hbd h hh
  have hi' := hidx i hi
  rw [Function.comp_apply, height_matOfPairs_corrCol lb α L (show 1 ≤ h by omega), Nat.log_pow (by norm_num),
    show i / 2 / 2 ^ (H - 1 - (h - 1)) = i / 2 ^ (H - h) / 2 by
      rw [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul, mul_comm, show H - 1 - (h - 1) = H - h by omega],
    rowsOf_matOfPairs_getD _ (by
      rw [length_corrCol, Nat.div_lt_iff_lt_mul (by norm_num), Nat.div_lt_iff_lt_mul (by positivity)]
      calc i < 2 ^ H := hi'
        _ = 2 ^ h * 2 ^ (H - h) := by rw [← pow_add]; congr 1; omega
        _ ≤ 2 ^ h / 2 * 2 * 2 ^ (H - h) := by
          rw [Nat.div_mul_cancel (dvd_pow_self 2 (by omega))]),
    flVals_eq_row hV α L (by omega) hb.2 hG hi']

theorem zip_map_left' {α β : Type _} (f : α → β) : ∀ (l : List α), (l.map f).zip l = l.map fun a => (f a, a)
  | [] => rfl
  | a :: l => by simp [zip_map_left' f l]

/-- The first-layer siblings the prover reads off the openings: the corrected function at the conjugate points. -/
theorem firstLayerSiblings_honest {lb H : ℕ} (α : K) (L : List (HMat K)) (indices : List ℕ) :
    firstLayerSiblings H (heightsOf lb L) indices
        (indices.map fun i => (heightsOf lb L).map fun h => flVals G lb H α L h i) =
      indices.map fun i => (heightsOf lb L).map fun h => corr G lb α L h (-qPt G H i h) := by
  rw [firstLayerSiblings, zip_map_self', List.map_map]
  refine List.map_congr_left fun i hi => ?_
  rw [Function.comp_apply, zip_map_left']
  simp only [List.map_map]
  refine List.map_congr_left fun h _ => ?_
  simp only [Function.comp_apply, flVals, qBit]
  rcases Nat.mod_two_eq_zero_or_one (i / 2 ^ (H - h)) with hb | hb <;> simp [hb]

/-! ## The transcript -/

/-- The prover's and the verifier's transcripts agree on a run.

Related states give the same challenges, the verifier accepting the prover's grinding witnesses:

- the batch phase returns alpha
- the first layer returns the bivariate beta
- each commit round returns its beta
- the query phase returns the indices.

A grind at difficulty zero returns no witness.

The query phase draws one index per query, of H bits. -/
structure TxAgree {Com Sp Sv : Type _} (params : FriParameters) (H : ℕ) (tp : CircleProverTx K Com Sp)
    (tv : CircleVerifierTx K Com Sv) (Rel : Sp → Sv → Prop) : Prop where
  batch : ∀ sp sv cl, Rel sp sv → ∃ sv', tv.batch_phase sv cl ((tp.batch_phase sp cl).2.1.getD 0) =
    .ok ((tp.batch_phase sp cl).1, sv') ∧ Rel (tp.batch_phase sp cl).2.2 sv'
  first : ∀ sp sv c, Rel sp sv → ∃ sv', tv.first_layer sv c = ((tp.first_layer sp c).1, sv') ∧
    Rel (tp.first_layer sp c).2 sv'
  commit : ∀ sp sv c, Rel sp sv → ∃ sv', tv.commit_round sv c ((tp.commit_round sp c).2.1.getD 0) =
    .ok ((tp.commit_round sp c).1, sv') ∧ Rel (tp.commit_round sp c).2.2 sv'
  query : ∀ sp sv f, Rel sp sv → ∃ sv', tv.query_phase sv f ((tp.query_phase sp f).2.1.getD 0) =
    .ok ((tp.query_phase sp f).1, sv')
  batch_none : params.batch_proof_of_work_bits = 0 → ∀ sp cl, (tp.batch_phase sp cl).2.1 = none
  commit_none : params.commit_proof_of_work_bits = 0 → ∀ sp c, (tp.commit_round sp c).2.1 = none
  query_none : params.query_proof_of_work_bits = 0 → ∀ sp f, (tp.query_phase sp f).2.1 = none
  queries : ∀ sp f, (tp.query_phase sp f).1.length = params.num_queries ∧
    ∀ i ∈ (tp.query_phase sp f).1, i < 2 ^ H

theorem cwAt_congr (lb H : ℕ) (E : ℕ → ℕ → K) {β β' : ℕ → K} {i : ℕ} (h : ∀ j < i, β j = β' j) :
    cwAt G lb H E β i = cwAt G lb H E β' i := by
  rw [cwAt, cwAt, layer_congr E i h]

/-- The run's commitments and data are those of the round codewords, under the run's final betas. -/
theorem honestRun_commits (lb H : ℕ) (E : ℕ → ℕ → K) (fmmcs : MmcsOps K) {S : Type _}
    (tx : CircleProverTx K fmmcs.Commitment S) (s : S) :
    ∀ k, (honestRun G lb H E fmmcs tx s k).2.1 = (List.range k).map (fun i =>
        (fmmcs.commit [matOfPairs (cwAt G lb H E ((honestRun G lb H E fmmcs tx s k).1.getD · 0) i)]).1) ∧
      (honestRun G lb H E fmmcs tx s k).2.2.1 = (List.range k).map (fun i =>
        (fmmcs.commit [matOfPairs (cwAt G lb H E ((honestRun G lb H E fmmcs tx s k).1.getD · 0) i)]).2)
  | 0 => by simp [honestRun]
  | k + 1 => by
    obtain ⟨hc, hd⟩ := honestRun_commits lb H E fmmcs tx s k
    have hlen := (honestRun_length (G := G) lb H E fmmcs tx s k).1
    have hcw : ∀ i ≤ k, cwAt G lb H E ((honestRun G lb H E fmmcs tx s (k + 1)).1.getD · 0) i =
        cwAt G lb H E ((honestRun G lb H E fmmcs tx s k).1.getD · 0) i := fun i hi =>
      cwAt_congr lb H E fun j hj => by
        simp only [honestRun, List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_left (by omega)]
    simp only [List.range_succ, List.map_append, List.map_cons, List.map_nil]
    refine ⟨?_, ?_⟩
    · rw [show (honestRun G lb H E fmmcs tx s (k + 1)).2.1 = (honestRun G lb H E fmmcs tx s k).2.1 ++
        [(fmmcs.commit [matOfPairs (cwAt G lb H E ((honestRun G lb H E fmmcs tx s k).1.getD · 0) k)]).1] from rfl,
        hc, hcw k le_rfl]
      congr 1
      exact List.map_congr_left fun i hi => by rw [hcw i (by simp at hi; omega)]
    · rw [show (honestRun G lb H E fmmcs tx s (k + 1)).2.2.1 = (honestRun G lb H E fmmcs tx s k).2.2.1 ++
        [(fmmcs.commit [matOfPairs (cwAt G lb H E ((honestRun G lb H E fmmcs tx s k).1.getD · 0) k)]).2] from rfl,
        hd, hcw k le_rfl]
      congr 1
      exact List.map_congr_left fun i hi => by rw [hcw i (by simp at hi; omega)]

theorem Xp_odd (hV : CircleGenValid G) {r : ℕ} (hG : r + 3 ≤ G.adicity) (c : ℕ) :
    Xp G (r + 2) (2 * c + 1) = -Xp G (r + 2) (2 * c) := by
  have h1 : 2 ^ r • genPt G (r + 1) = genPt G 1 := by
    have := genPt_nsmul hV (j := 1) (k := r + 1) (by omega) (by omega)
    rwa [Nat.add_sub_cancel] at this
  rw [Xp, Xp, show r + 2 - 1 = r + 1 by omega, Plonky3Lean.Proofs.Dft.rev_double_add_one,
    Plonky3Lean.Proofs.Dft.rev_double, add_nsmul, h1, ← add_assoc, add_right_comm, add_genPt_one_x hV (by omega)]

/-- The verifier's commit-phase replay on the honest run returns the run's betas. -/
theorem replay_commits {Sp Sv : Type _} {params : FriParameters} {H : ℕ} (lb : ℕ) (E : ℕ → ℕ → K)
    (fmmcs : MmcsOps K) {tp : CircleProverTx K fmmcs.Commitment Sp} {tv : CircleVerifierTx K fmmcs.Commitment Sv}
    {Rel : Sp → Sv → Prop} (agree : TxAgree params H tp tv Rel) {ME IE : Type} (sp : Sp) :
    ∀ k (sv : Sv), Rel sp sv → ∃ sv', ((honestRun G lb H E fmmcs tp sp k).2.1.zip
        (honestRun G lb H E fmmcs tp sp k).2.2.2.1).foldlM
        (fun (acc : List K × Sv) cw => do
          let r ← txResult (ME := ME) (IE := IE) (tv.commit_round acc.2 cw.1 cw.2)
          pure (acc.1 ++ [r.1], r.2)) ([], sv) =
        pure ((honestRun G lb H E fmmcs tp sp k).1, sv') ∧ Rel (honestRun G lb H E fmmcs tp sp k).2.2.2.2 sv'
  | 0, sv, h => ⟨sv, rfl, h⟩
  | k + 1, sv, h => by
    obtain ⟨sv1, h1, hr1⟩ := replay_commits lb E fmmcs agree sp k sv h
    have hl := honestRun_length (G := G) lb H E fmmcs tp sp k
    set run := honestRun G lb H E fmmcs tp sp k
    set c := (fmmcs.commit [matOfPairs (cwAt G lb H E (run.1.getD · 0) k)]).1
    obtain ⟨sv2, h2, hr2⟩ := agree.commit run.2.2.2.2 sv1 c hr1
    refine ⟨sv2, ?_, hr2⟩
    show ((run.2.1 ++ [c]).zip (run.2.2.2.1 ++ [((tp.commit_round run.2.2.2.2 c).2.1).getD 0])).foldlM _ ([], sv) =
      pure (run.1 ++ [(tp.commit_round run.2.2.2.2 c).1], sv2)
    rw [List.zip_append (by rw [hl.2.1, hl.2.2.2]), List.foldlM_append, h1, pure_bind, List.zip_cons_cons,
      List.zip_nil_left, List.foldlM_cons, h2]
    rfl

/-! ## The prover's run on honest batches -/

/-- The verifier's claims about honest batches: the commitments of their LDEs, and the matrices' claims. -/
noncomputable def claimsOf (G : Gen (K × K)) (immcs : MmcsOps K) (lb : ℕ) (hb : List (List (HMat K))) :
    List (Claim K immcs.Commitment) :=
  hb.map fun ms => ⟨(immcs.commit (ms.map (ldeMat G lb))).1, ms.map Prod.fst⟩

/-- The prover's opening requests for honest batches: the committed data and each matrix's points. -/
noncomputable def requestsOf (G : Gen (K × K)) (immcs : MmcsOps K) (lb : ℕ) (hb : List (List (HMat K))) :
    List (immcs.ProverData × List (List K)) :=
  hb.map fun ms => ((immcs.commit (ms.map (ldeMat G lb))).2, ms.map fun m => m.1.points.map (·.point))

/-- The claimed values of honest batches. -/
def valuesOf (hb : List (List (HMat K))) : List (List (List (List K))) :=
  hb.map fun ms => ms.map fun m => m.1.points.map (·.values)

theorem claimHeights_claimsOf (immcs : MmcsOps K) (lb : ℕ) (hb : List (List (HMat K))) :
    claimHeights lb (claimsOf G immcs lb hb) = hb.flatten.map (hgt lb) := by
  simp only [claimHeights, claimsOf, List.flatMap_map, List.map_flatten, List.map_map]
  rfl

/-! ## The opened values: the circle Lagrange evaluation -/

/-- The prover opens an honest matrix at its points to the columns' values there.

Take a matrix whose columns lie in the FFT space of the trace size 2^n, n >= 2.

Take opening points on the circle and off the LDE domain. -/
theorem openMatrix_honest (hV : CircleGenValid G) (h2 : (2 : K) ≠ 0) {lb : ℕ} (m : HMat K)
    (hn : 2 ≤ m.1.domain.log_n) (hG : hgt lb m + 1 ≤ G.adicity)
    (hfft : ∀ f ∈ m.2, IsFftPoly (2 ^ (m.1.domain.log_n - 1)) f)
    (hvals : ∀ p ∈ m.1.points, p.values = m.2.map (· (ptOf p.point)))
    (hcirc : ∀ p ∈ m.1.points, 1 + p.point * p.point ≠ 0)
    (hoff : ∀ p ∈ m.1.points, ∀ k < 2 ^ hgt lb m, ptOf p.point ≠ ptD G (hgt lb m) k) :
    openMatrix G lb (ldeMat G lb m) (m.1.points.map (·.point)) = some (m.1.points.map (·.values)) := by
  unfold openMatrix
  simp only [ldeMat, log2Strict_pow, Option.bind_eq_bind, Option.bind_some]
  set s := m.1.domain.log_n
  set h := hgt lb m
  have hsh : s ≤ h := by unfold h hgt; omega
  have hP := twinList_prefix hV h2 (show 1 ≤ s by omega) hsh hG
  have htake : ((List.range (2 ^ h)).map fun i => ofC (ptD G h (cfft_permute_index i h))).take (2 ^ s) =
      (List.range (2 ^ s)).map fun i => ofC (ptD G h (cfft_permute_index i h)) := by
    rw [← List.map_take, List.take_range, min_eq_left (Nat.pow_le_pow_right two_pos hsh)]
  simp only [permutedPoints_eq hV (show 1 ≤ h by omega) hG, standard_eq hV h hG, show ¬ h < lb by unfold h hgt; omega,
    ↓reduceIte, show h - lb = s by unfold h hgt; omega, CircleDomain.new, Option.bind_some, htake]
  rw [List.mapM_map]
  refine mapM_eq_some_map _ _ _ fun p hp => ?_
  have hs1 : s - 1 + 1 = s := by omega
  have hZ : ∀ i < 2 ^ s, (ptOf p.point - ptD G h (cfft_permute_index i h)).y ≠ 0 := fun i hi => by
    refine sub_y_ne_zero (m := s - 1) (c := vn s (genPt G (h + 1))) h2 (by omega) (by rw [hP.card, hs1]) (fun Q hQ => ?_) (fun hZ => ?_)
      (TwinList.mem.mpr ⟨i, hi, rfl⟩)
    · obtain ⟨j, hj, rfl⟩ := TwinList.mem.mp hQ; rw [hs1]; exact hP.vn_eq hj
    · obtain ⟨j, -, hj⟩ := TwinList.mem.mp hZ
      exact hoff p hp _ (cfft_permute_index_lt h j) hj.symm
  simp only [Function.comp_apply, ofC_ptOf (hcirc p hp), Option.bind_some,
    compute_lagrange_den_eq h2 (show 1 ≤ s by omega) hP _ hZ]
  rw [evaluate_at_point_with_den_eq h2 (show 1 ≤ s by omega) hP ⟨2 ^ s, m.2.length, _⟩ rfl (fun c => m.2.get c)
    (fun c => hfft _ (List.get_mem _ _)) (fun r _ c => rfl) _ hZ, hvals p hp]
  exact congrArg some (finRange_map_get_apply m.2 _)

/-- The prover's opened values of honest batches are the claimed values. -/
theorem openedValues_honest (hV : CircleGenValid G) (h2 : (2 : K) ≠ 0) {lb H : ℕ} (hb : List (List (HMat K)))
    (hc : ∀ m ∈ hb.flatten, 2 ≤ m.1.domain.log_n ∧ hgt lb m ≤ H) (hG : H + 1 ≤ G.adicity)
    (hfft : ∀ m ∈ hb.flatten, ∀ f ∈ m.2, IsFftPoly (2 ^ (m.1.domain.log_n - 1)) f)
    (hvals : ∀ m ∈ hb.flatten, ∀ p ∈ m.1.points, p.values = m.2.map (· (ptOf p.point)))
    (hcirc : ∀ m ∈ hb.flatten, ∀ p ∈ m.1.points, 1 + p.point * p.point ≠ 0)
    (hoff : ∀ m ∈ hb.flatten, ∀ p ∈ m.1.points, ∀ k < 2 ^ hgt lb m, ptOf p.point ≠ ptD G (hgt lb m) k) :
    openedValues G lb (hb.map fun ms => (ms.map (ldeMat G lb), ms.map fun m => m.1.points.map (·.point))) =
      some (valuesOf hb) := by
  unfold openedValues valuesOf
  rw [List.mapM_map]
  refine mapM_eq_some_map _ _ _ fun ms hms => ?_
  have hms' : ∀ m ∈ ms, m ∈ hb.flatten := fun m hm => List.mem_flatten.mpr ⟨ms, hms, hm⟩
  simp only [Function.comp_apply, List.length_map, ne_eq, not_true_eq_false, ↓reduceIte]
  rw [zip_map_map, List.mapM_map]
  refine mapM_eq_some_map _ _ _ fun m hm => ?_
  have hm' := hms' m hm
  exact openMatrix_honest hV h2 m (hc m hm').1 (by have := (hc m hm').2; omega) (hfft m hm') (hvals m hm')
    (hcirc m hm') (hoff m hm')

theorem max?_eq_foldl {l : List ℕ} {H : ℕ} (h : l.max? = some H) : l.foldl max 0 = H := by
  obtain ⟨hmem, hle⟩ := List.max?_eq_some_iff.mp h
  refine le_antisymm ?_ (le_foldl_max_mem l 0 H hmem)
  rcases List.mem_cons.mp (foldl_max_mem l 0) with h' | h'
  · rw [h']; omega
  · exact hle _ h'

/-- The claims the prover binds: every opening point of every matrix, mapped to the circle, with its values. -/
noncomputable def claimsZOf (hb : List (List (HMat K))) : List (Point K × List K) :=
  hb.flatten.flatMap fun m => m.1.points.map fun p => (ofC (ptOf p.point), p.values)

theorem proverClaims_honest {lb : ℕ} (hb : List (List (HMat K)))
    (hcirc : ∀ m ∈ hb.flatten, ∀ p ∈ m.1.points, 1 + p.point * p.point ≠ 0) :
    (((hb.map fun ms => (ms.map (ldeMat G lb), ms.map fun m => m.1.points.map (·.point))).zip (valuesOf hb)).flatMap
        (fun rv => (rv.1.2.zip rv.2).flatMap fun pv => pv.1.zip pv.2)).mapM
        (fun tv => (Point.from_projective_line tv.1).map fun z => (z, tv.2)) = some (claimsZOf hb) := by
  have hl : ((hb.map fun ms => (ms.map (ldeMat G lb), ms.map fun m => m.1.points.map (·.point))).zip
      (valuesOf hb)).flatMap (fun rv => (rv.1.2.zip rv.2).flatMap fun pv => pv.1.zip pv.2) =
      hb.flatten.flatMap fun m => m.1.points.map fun p => (p.point, p.values) := by
    clear hcirc
    induction hb with
    | nil => rfl
    | cons ms hb ih =>
      simp only [List.map_cons, valuesOf, List.zip_cons_cons, List.flatMap_cons, List.flatten_cons,
        List.flatMap_append] at ih ⊢
      rw [ih, zip_map_map]
      simp only [List.flatMap_map, zip_map_map]
  rw [hl, show claimsZOf hb = (hb.flatten.flatMap fun m => m.1.points.map fun p => (p.point, p.values)).map
    (fun tv => (ofC (ptOf tv.1), tv.2)) by simp [claimsZOf, List.map_flatMap, Function.comp_def]]
  refine mapM_eq_some_map _ _ _ fun tv htv => ?_
  obtain ⟨m, hm, htv⟩ := List.mem_flatMap.mp htv
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp htv
  rw [ofC_ptOf (hcirc m hm p hp)]
  rfl

theorem verifierClaims_honest (immcs : MmcsOps K) {lb : ℕ} (hb : List (List (HMat K)))
    (hcirc : ∀ m ∈ hb.flatten, ∀ p ∈ m.1.points, 1 + p.point * p.point ≠ 0) :
    ((claimsOf G immcs lb hb).flatMap fun c => c.matrices.flatMap fun m => m.points).mapM
        (fun p => (Point.from_projective_line p.point).map fun z => (z, p.values)) = some (claimsZOf hb) := by
  have hl : ((claimsOf G immcs lb hb).flatMap fun c => c.matrices.flatMap fun m => m.points) =
      hb.flatten.flatMap fun m => m.1.points := by
    simp only [claimsOf, List.flatMap_map]
    clear hcirc
    induction hb with
    | nil => rfl
    | cons ms hb ih => simp [List.flatMap_cons, List.flatten_cons, List.flatMap_append, ← ih]
  rw [hl, show claimsZOf hb = (hb.flatten.flatMap fun m => m.1.points).map
    (fun p => (ofC (ptOf p.point), p.values)) by simp [claimsZOf, List.map_flatMap]]
  refine mapM_eq_some_map _ _ _ fun p hp => ?_
  obtain ⟨m, hm, hp⟩ := List.mem_flatMap.mp hp
  rw [ofC_ptOf (hcirc m hm p hp)]
  rfl

theorem heights_ldeMat {β : Type _} (lb : ℕ) (X : List (HMat K) → β) :
    ∀ (hb : List (List (HMat K))), ((hb.map fun ms => (ms.map (ldeMat G lb), X ms)).flatMap
      fun r => r.1.map Mat.height) = (hb.flatten.map (hgt lb)).map (2 ^ ·)
  | [] => rfl
  | ms :: hb => by
    rw [List.map_cons, List.flatMap_cons, heights_ldeMat lb X hb, List.flatten_cons, List.map_append,
      List.map_append, List.map_map, List.map_map]
    simp [Function.comp_def, ldeMat]

theorem honestRun_ws_zero (lb H : ℕ) (E : ℕ → ℕ → K) (fmmcs : MmcsOps K) {S : Type _}
    (tx : CircleProverTx K fmmcs.Commitment S) (s : S) (hnone : ∀ s c, (tx.commit_round s c).2.1 = none) :
    ∀ k, ∀ w ∈ (honestRun G lb H E fmmcs tx s k).2.2.2.1, w = 0
  | 0 => by simp [honestRun]
  | k + 1 => by
    intro w hw
    simp only [honestRun, List.mem_append, List.mem_singleton] at hw
    rcases hw with hw | rfl
    · exact honestRun_ws_zero lb H E fmmcs tx s hnone k w hw
    · rw [hnone]; rfl

theorem answersOf_length (fmmcs : MmcsOps K) : ∀ (cws : List (List K)) (cur : List ℕ),
    (answersOf fmmcs cws cur).length = cws.length
  | [], _ => rfl
  | _ :: cws, cur => by simp [answersOf, answersOf_length fmmcs cws]

theorem answersOf_getElem (fmmcs : MmcsOps K) : ∀ (cws : List (List K)) (cur : List ℕ) (k : ℕ)
    (hk : k < cws.length), (answersOf fmmcs cws cur)[k]'(by rw [answersOf_length]; exact hk) =
      roundAnswer fmmcs cws[k] (cur.map (· / 2 ^ k))
  | [], _, k, hk => by simp at hk
  | cw :: cws, cur, 0, _ => by simp [answersOf]
  | cw :: cws, cur, k + 1, hk => by
    simp only [answersOf, List.getElem_cons_succ]
    rw [answersOf_getElem fmmcs cws _ k (by simpa using hk), List.map_map]
    congr 2
    funext t
    simp [Nat.div_div_eq_div_mul, pow_succ']

theorem claimedWidth_of_honest {lb H : ℕ} {Com : Type} {rounds : List (Claim K Com)} {hb : List (List (HMat K))}
    (hc : HonestClaims G lb H rounds hb) {m : HMat K} (hm : m ∈ hb.flatten) : claimedWidth m.1 = m.2.length := by
  obtain ⟨p, ps, hp⟩ := List.exists_cons_of_ne_nil (hc.points_ne m hm)
  rw [claimedWidth, hp, List.headD_cons, hc.values m hm p (by rw [hp]; exact List.mem_cons_self), List.length_map]

theorem answersOf_shape (fmmcs : MmcsOps K) : ∀ (cws : List (List K)) (cur : List ℕ),
    ∀ o ∈ answersOf fmmcs cws cur, o.sibling_values.length = cur.length ∧ ∀ s ∈ o.sibling_values, s.length = 1
  | [], _, o, ho => by simp [answersOf] at ho
  | cw :: cws, cur, o, ho => by
    rcases List.mem_cons.mp ho with rfl | ho
    · refine ⟨by simp [roundAnswer], fun s hs => ?_⟩
      simp only [roundAnswer, List.mem_map] at hs
      obtain ⟨t, -, rfl⟩ := hs; rfl
    · have := answersOf_shape fmmcs cws _ o ho
      exact ⟨by simpa using this.1, this.2⟩

/-- An honest batch's opening passes the verifier's batch check. -/
theorem inputAccept_honest (immcs : MmcsOps K) (hmm : MmcsHonest immcs) {lb H : ℕ} (ms : List (HMat K))
    (hne : ms ≠ []) (hH : ∀ m ∈ ms, hgt lb m ≤ H) (hw : ∀ m ∈ ms, claimedWidth m.1 = m.2.length)
    (indices : List ℕ) (hidx : ∀ i ∈ indices, i < 2 ^ H) :
    immcs.verify_multi_batch (immcs.commit (ms.map (ldeMat G lb))).1
      (inDims lb (⟨(immcs.commit (ms.map (ldeMat G lb))).1, ms.map Prod.fst⟩ : Claim K immcs.Commitment))
      (inReduced lb H indices (⟨(immcs.commit (ms.map (ldeMat G lb))).1, ms.map Prod.fst⟩ : Claim K immcs.Commitment))
      (immcs.open_multi_batch (indices.map (· / 2 ^ (H - (ms.map (hgt lb)).foldl max 0)))
        (immcs.commit (ms.map (ldeMat G lb))).2).1
      (immcs.open_multi_batch (indices.map (· / 2 ^ (H - (ms.map (hgt lb)).foldl max 0)))
        (immcs.commit (ms.map (ldeMat G lb))).2).2 = .ok () := by
  have htop := foldl_max_hgt_le hH
  have hdims : inDims lb (⟨(immcs.commit (ms.map (ldeMat G lb))).1, ms.map Prod.fst⟩ : Claim K immcs.Commitment) =
      (ms.map (ldeMat G lb)).map fun m => (m.width, m.height) := by
    simp only [inDims, List.map_map]
    refine List.map_congr_left fun m hm => ?_
    simp [hw m hm, ldeMat, hgt, pow_add]
  have hred : inReduced lb H indices
      (⟨(immcs.commit (ms.map (ldeMat G lb))).1, ms.map Prod.fst⟩ : Claim K immcs.Commitment) =
      indices.map (· / 2 ^ (H - (ms.map (hgt lb)).foldl max 0)) := by
    unfold inReduced
    rw [show ((ms.map Prod.fst).map fun m => 2 ^ m.domain.log_n * 2 ^ lb) = (ms.map (hgt lb)).map (2 ^ ·) by
      simp [hgt, pow_add], max?_pow _ (by simpa using hne)]
    simp only [Nat.log2_two_pow]
  rw [hdims, hred]
  refine hmm.accepts _ _ (by simpa using hne) (fun m hm => ?_) (fun I hI => ?_)
  · obtain ⟨m', -, rfl⟩ := List.mem_map.mp hm
    simp [ldeMat, Nat.log_pow (by norm_num : 1 < 2)]
  · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hI
    rw [topLog_ldeMat, Nat.div_lt_iff_lt_mul (by positivity), ← pow_add,
      show (ms.map (hgt lb)).foldl max 0 + (H - (ms.map (hgt lb)).foldl max 0) = H by omega]
    exact hidx i hi

theorem cwAt_getD (lb H : ℕ) (E : ℕ → ℕ → K) (β : ℕ → K) {k j : ℕ} (hj : j < 2 ^ (H - 1 - k)) :
    (cwAt G lb H E β k).getD j 0 = xEval (H - (lb + 1) - k) (layer E β k) (Xp G (H - k) j) := by
  rw [cwAt, List.getD_eq_getElem _ _ (by simpa using hj), List.getElem_map, List.getElem_range,
    xEval_trunc (by omega)]

theorem Xg_eq_Xp {H k : ℕ} (hk : k + 2 ≤ H) (j : ℕ) : Xg G (H - 1) k j = Xp G (H - k) (2 * j) := by
  rw [Xg, Xp, show H - k - 1 = (H - k - 2) + 1 by omega, Plonky3Lean.Proofs.Dft.rev_double,
    show H - 1 + 2 - k = H - k + 1 by omega, show H - 1 - 1 - k = H - k - 2 by omega,
    show H - 1 - k = H - k - 2 + 1 by omega]

/-! ## Completeness: the verifier accepts what the honest prover opens -/

/-- Completeness of the circle PCS, prover to verifier.

Take honest batches: columns of the FFT space of the trace size, committed as their LDEs in circle FFT order.

Take opening points on the circle and off the LDE domain.

Take commitment schemes that open and accept honestly, and prover and verifier transcripts that agree.

Then the prover returns the claimed values and a proof, and the verifier accepts the proof. -/
theorem open_verify_complete (hV : CircleGenValid G) (h2 : (2 : K) ≠ 0) (immcs fmmcs : MmcsOps K)
    (him : MmcsHonest immcs) (hfm : MmcsHonest fmmcs) {Sp Sv : Type}
    (tp : CircleProverTx K fmmcs.Commitment Sp) (tv : CircleVerifierTx K fmmcs.Commitment Sv)
    {Rel : Sp → Sv → Prop} (params : FriParameters) {H : ℕ} (agree : TxAgree params H tp tv Rel) (sp : Sp) (sv : Sv)
    (hrel : Rel sp sv) (harity : params.max_log_arity = 1) (hq : params.num_queries ≠ 0)
    (hlb : 1 ≤ params.log_blowup) {hb : List (List (HMat K))}
    (hc : HonestClaims G params.log_blowup H (claimsOf G immcs params.log_blowup hb) hb)
    (hne : ∀ ms ∈ hb, ms ≠ []) (hmax : (hb.flatten.map (hgt params.log_blowup)).max? = some H)
    (hG : H + 1 ≤ G.adicity)
    (hfft : ∀ m ∈ hb.flatten, ∀ f ∈ m.2, IsFftPoly (2 ^ (m.1.domain.log_n - 1)) f) :
    ∃ proof, open_ G immcs fmmcs tp params (requestsOf G immcs params.log_blowup hb) sp =
        some (valuesOf hb, proof) ∧
      verify G immcs fmmcs tv params (claimsOf G immcs params.log_blowup hb) proof sv = pure () := by
  set lb := params.log_blowup
  set L := hb.flatten
  set hs := heightsOf lb L
  have hbd : ∀ h ∈ hs, lb + 2 ≤ h ∧ h ≤ H := fun h hh => heightsOf_bounds hc.log_n hc.height hh
  have hH : H ∈ hs := by
    obtain ⟨m, hm, he⟩ := List.mem_map.mp (List.max?_mem hmax)
    exact mem_heightsOf.mpr ⟨m, hm, he⟩
  have hHb := hbd H hH
  have hLne : L ≠ [] := fun h => by simp [h] at hmax
  have hcirc : ∀ m ∈ L, ∀ p ∈ m.1.points, 1 + p.point * p.point ≠ 0 := hc.on_circle
  -- The prover's run, step by step.
  have hmr : (requestsOf G immcs lb hb).map (fun r => (immcs.get_matrices r.1, r.2)) =
      hb.map fun ms => (ms.map (ldeMat G lb), ms.map fun m => m.1.points.map (·.point)) := by
    simp [requestsOf, him.get]
  have hlogmax : (((hb.map fun ms => (ms.map (ldeMat G lb), ms.map fun m => m.1.points.map (·.point))).flatMap
      fun r => r.1.map Mat.height).max?).bind log2Strict = some H := by
    rw [heights_ldeMat, max?_pow _ (fun h => hLne (List.map_eq_nil_iff.mp h)), max?_eq_foldl hmax]
    simp [log2Strict_pow]
  unfold open_
  simp only [hmr]
  rw [openedValues_honest hV h2 hb (fun m hm => ⟨hc.log_n m hm, hc.height m hm⟩) hG hfft hc.values hcirc
    hc.off_domain]
  simp only [Option.bind_eq_bind, Option.bind_some]
  rw [hlogmax, Option.bind_some, proverClaims_honest hb hcirc, Option.bind_some]
  set α := (tp.batch_phase sp (claimsZOf hb)).1
  have hok : ∀ m ∈ L, ProverMatOK G lb m := fun m hm =>
    ⟨by have := hc.log_n m hm; omega, hfft m hm, by have := hc.height m hm; unfold hgt; omega, hc.values m hm,
      hc.on_circle m hm, hc.off_domain m hm⟩
  obtain ⟨st, hst, hinv⟩ := reducedOpenings_honest hV h2 α hb hok
  erw [hst, Option.bind_some, extractLambdas_honest hV h2 α hlb hG hbd hc.honestAt hinv, Option.bind_some]
  simp only [List.map_map, Function.comp_def, hfm.get]
  set s1 := (tp.batch_phase sp (claimsZOf hb)).2.2
  set mats := hs.map fun h => matOfPairs (corrCol G lb α L h)
  set flc := (fmmcs.commit mats).1
  set fld := (fmmcs.commit mats).2
  set bβ := (tp.first_layer s1 flc).1
  set s2 := (tp.first_layer s1 flc).2
  set E := friCoeffs G lb H α bβ L
  set R := H - (lb + 1)
  have hfri : mats.mapM (fun m => fold_y G bβ (pairsOf m)) = some (hs.map (fiCW G lb α bβ L)) := by
    simp only [mats, List.mapM_map]
    exact mapM_eq_some_map _ _ _ fun h hh => by
      rw [Function.comp_apply]
      exact fold_y_honest hV h2 α bβ hlb (hbd h hh).1 (by have := hbd h hh; omega) (hc.honestAt h)
  rw [hfri, Option.bind_some]
  have hchain : List.IsChain (fun l r => r.length ≤ l.length) (hs.map (fiCW G lb α bβ L)).reverse := by
    rw [← List.map_reverse]
    refine List.Pairwise.isChain ?_
    rw [List.pairwise_map]
    refine (List.pairwise_reverse.mpr ((heightsOf_pairwise lb L).imp id)).imp_of_mem fun {a b} ha hb' hab => ?_
    rw [length_fiCW, length_fiCW]
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  simp only [harity, ne_eq, not_true_eq_false, hq, show ¬ params.log_blowup = 0 by omega, or_self,
    ↓reduceIte, hchain, not_true_eq_false]
  rw [← List.map_reverse, commitPhase_honest hV h2 α bβ hlb hG hbd hH fmmcs hfm tp s2, Option.bind_some]
  simp only []
  set run := honestRun G lb H E fmmcs tp s2 R
  set final := layer E (run.1.getD · 0) R 0
  set qp := tp.query_phase run.2.2.2.2 final
  have hidx : ∀ i ∈ qp.1, i < 2 ^ H := (agree.queries _ _).2
  have hreq : (requestsOf G immcs lb hb).map (·.1) = hb.map fun ms => (immcs.commit (ms.map (ldeMat G lb))).2 := by
    simp [requestsOf]
  rw [hreq, openInputs_honest immcs him hb hne (fun m hm => hc.height m hm) qp.1, Option.bind_some]
  set cws := (List.range R).map fun i => cwAt G lb H E (run.1.getD · 0) i
  have hds : run.2.2.1 = cws.map fun cw => (fmmcs.commit [matOfPairs cw]).2 := by
    rw [(honestRun_commits (G := G) lb H E fmmcs tp s2 R).2, List.map_map]; rfl
  have hcws : cws.length = R := by simp [cws]
  have haq : answerQueries fmmcs run.2.2.1 (qp.1.map (· / 2)) = some (answersOf fmmcs cws (qp.1.map (· / 2))) := by
    rw [answerQueries_eq, hds, foldlM_aqStep_honest fmmcs hfm cws _ (fun k hk t ht => by
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp ht
      have hi' := hidx i hi
      rw [hcws] at hk
      simp only [cws, List.getElem_map, List.getElem_range, length_cwAt]
      have h1 : i / 2 / 2 ^ k < 2 ^ (H - 1 - k) := by
        rw [Nat.div_div_eq_div_mul, Nat.div_lt_iff_lt_mul (by positivity), ← pow_succ', ← pow_add,
          show H - 1 - k + (k + 1) = H by omega]; exact hi'
      rw [show 2 ^ (H - 1 - k) = 2 * 2 ^ (H - 2 - k) by rw [← pow_succ']; congr 1; omega] at h1 ⊢
      omega)]
    rfl
  rw [haq, Option.bind_some]
  refine ⟨_, rfl, ?_⟩
  -- The verifier's checks before the transcript.
  have hrl : run.1.length = R ∧ run.2.1.length = R ∧ run.2.2.1.length = R ∧ run.2.2.2.1.length = R :=
    honestRun_length (G := G) lb H E fmmcs tp s2 R
  have hql : qp.1.length = params.num_queries := (agree.queries run.2.2.2.2 final).1
  have hshape : validate_proof_shape (ME := fmmcs.Error) (IE := InputError immcs.Error fmmcs.Error) params
      (⟨run.2.1, run.2.2.2.1, ⟨hb.map fun ms =>
        ⟨(immcs.open_multi_batch (qp.1.map (· / 2 ^ (H - (ms.map (hgt lb)).foldl max 0)))
          (immcs.commit (ms.map (ldeMat G lb))).2).1,
        (immcs.open_multi_batch (qp.1.map (· / 2 ^ (H - (ms.map (hgt lb)).foldl max 0)))
          (immcs.commit (ms.map (ldeMat G lb))).2).2⟩,
        firstLayerSiblings H (st.2.mergeSort fun a b => decide (a ≤ b)) qp.1
          (fmmcs.open_multi_batch (qp.1.map (· / 2)) fld).1,
        (fmmcs.open_multi_batch (qp.1.map (· / 2)) fld).2⟩,
        answersOf fmmcs cws (qp.1.map (· / 2)), final, qp.2.1.getD 0⟩ :
        CircleFriProof K fmmcs.Commitment fmmcs.MultiProof (CircleInputProof K immcs.MultiProof fmmcs.MultiProof))
      R = pure (List.replicate R 1) := by
    have hws : params.commit_proof_of_work_bits = 0 → ∀ w ∈ run.2.2.2.1, w = 0 := fun h0 =>
      honestRun_ws_zero lb H E fmmcs tp s2 (agree.commit_none h0) R
    have hpw : params.query_proof_of_work_bits = 0 → qp.2.1.getD 0 = 0 := fun h0 => by
      rw [show qp.2.1 = none from agree.query_none h0 _ _]; rfl
    have hc1 : ¬ (params.commit_proof_of_work_bits = 0 ∧ (run.2.2.2.1.any fun x => decide ¬x = 0) = true) := by
      rintro ⟨h0, h⟩
      simp only [List.any_eq_true, decide_eq_true_eq] at h
      obtain ⟨w, hw, hw0⟩ := h
      exact hw0 (hws h0 w hw)
    have hc2 : ¬ (params.query_proof_of_work_bits = 0 ∧ ¬qp.2.1.getD 0 = 0) := fun ⟨h0, h⟩ => h (hpw h0)
    unfold validate_proof_shape
    simp only [hq, show ¬ params.log_blowup = 0 by omega, harity, ne_eq, not_true_eq_false, ↓reduceIte,
      hrl.2.1, hrl.2.2.2, answersOf_length, hcws, hc1, hc2]
    rw [Plonky3Lean.Proofs.Fri.forM_eq_pure _ ?_, pure_bind]
    intro e he
    obtain ⟨ho, hre⟩ := List.of_mem_zip he
    obtain ⟨-, h1⟩ := List.mem_replicate.mp hre
    obtain ⟨hl1, hl2⟩ := answersOf_shape fmmcs cws _ e.1 ho
    simp only [hl1, List.length_map, hql, h1, not_true_eq_false, ↓reduceIte]
    simpa using hl2
  -- The replayed transcript returns the prover's challenges.
  obtain ⟨sv1, hb1, hr1⟩ := agree.batch sp sv (claimsZOf hb) hrel
  obtain ⟨sv2, hf2, hr2⟩ := agree.first s1 sv1 flc hr1
  obtain ⟨sv3, hc3, hr3⟩ := replay_commits (G := G) (ME := fmmcs.Error) (IE := InputError immcs.Error fmmcs.Error)
    lb E fmmcs agree s2 R sv2 hr2
  obtain ⟨sv4, hq4⟩ := agree.query run.2.2.2.2 sv3 final hr3
  have hreplay : replay_transcript (ME := fmmcs.Error) (IE := InputError immcs.Error fmmcs.Error) tv
      (claimsOf G immcs lb hb)
      (⟨(tp.batch_phase sp (claimsZOf hb)).2.1.getD 0, flc, hs.map (lamAt G lb α L),
        ⟨run.2.1, run.2.2.2.1, ⟨hb.map fun ms =>
          ⟨(immcs.open_multi_batch (qp.1.map (· / 2 ^ (H - (ms.map (hgt lb)).foldl max 0)))
            (immcs.commit (ms.map (ldeMat G lb))).2).1,
          (immcs.open_multi_batch (qp.1.map (· / 2 ^ (H - (ms.map (hgt lb)).foldl max 0)))
            (immcs.commit (ms.map (ldeMat G lb))).2).2⟩,
          firstLayerSiblings H (st.2.mergeSort fun a b => decide (a ≤ b)) qp.1
            (fmmcs.open_multi_batch (qp.1.map (· / 2)) fld).1,
          (fmmcs.open_multi_batch (qp.1.map (· / 2)) fld).2⟩,
          answersOf fmmcs cws (qp.1.map (· / 2)), final, qp.2.1.getD 0⟩⟩ :
        CirclePcsProof K fmmcs.Commitment immcs.MultiProof fmmcs.MultiProof) sv =
      pure ⟨α, bβ, run.1, qp.1⟩ := by
    have txResult_ok : ∀ {α : Type} (a : α), txResult (ME := fmmcs.Error) (IE := InputError immcs.Error fmmcs.Error)
        (.ok a) = pure a := fun _ => rfl
    unfold replay_transcript
    simp only [lift, verifierClaims_honest immcs hb hcirc, lift_some_bind']
    rw [hb1, txResult_ok, pure_bind]
    dsimp only
    rw [hf2]
    dsimp only
    erw [hc3, pure_bind, hq4, txResult_ok, pure_bind]
  -- The input openings.
  have hbp : ¬ (params.batch_proof_of_work_bits = 0 ∧ (tp.batch_phase sp (claimsZOf hb)).2.1.getD 0 ≠ 0) := by
    rintro ⟨h0, h⟩; rw [agree.batch_none h0] at h; exact h rfl
  have hHms : ∀ ms ∈ hb, ∀ m ∈ ms, hgt lb m ≤ H := fun ms hms m hm =>
    hc.height m (List.mem_flatten.mpr ⟨ms, hms, hm⟩)
  have hio : List.Forall₂ (fun (bo : BatchMultiOpening K immcs.MultiProof) (ms : List (HMat K)) =>
      bo.opened_values = qp.1.map fun i => ms.map fun m => m.2.map (· (qPt G H i (hgt lb m))))
      (hb.map fun ms => ⟨(immcs.open_multi_batch (qp.1.map (· / 2 ^ (H - (ms.map (hgt lb)).foldl max 0)))
          (immcs.commit (ms.map (ldeMat G lb))).2).1,
        (immcs.open_multi_batch (qp.1.map (· / 2 ^ (H - (ms.map (hgt lb)).foldl max 0)))
          (immcs.commit (ms.map (ldeMat G lb))).2).2⟩) hb := by
    rw [List.forall₂_map_left_iff]
    exact List.forall₂_same.mpr fun ms hms => inputRows_honest hV immcs him ms (hHms ms hms)
      (fun m hm => by have := hc.log_n m (List.mem_flatten.mpr ⟨ms, hms, hm⟩); omega) hG qp.1 hidx
  have hin : ∀ bc ∈ (hb.map fun ms => (⟨(immcs.open_multi_batch (qp.1.map (· / 2 ^ (H - (ms.map (hgt lb)).foldl max 0)))
          (immcs.commit (ms.map (ldeMat G lb))).2).1,
        (immcs.open_multi_batch (qp.1.map (· / 2 ^ (H - (ms.map (hgt lb)).foldl max 0)))
          (immcs.commit (ms.map (ldeMat G lb))).2).2⟩ : BatchMultiOpening K immcs.MultiProof)).zip
        (claimsOf G immcs lb hb), immcs.verify_multi_batch bc.2.commitment (inDims lb bc.2)
        (inReduced lb H qp.1 bc.2) bc.1.opened_values bc.1.opening_proof = .ok () := by
    intro bc hbc
    rw [claimsOf, zip_map_map] at hbc
    obtain ⟨ms, hms, rfl⟩ := List.mem_map.mp hbc
    exact inputAccept_honest immcs him ms (hne ms hms) (hHms ms hms)
      (fun m hm => claimedWidth_of_honest hc (List.mem_flatten.mpr ⟨ms, hms, hm⟩)) qp.1 hidx
  -- The first layer.
  have hkeys : st.2.mergeSort (fun a b => decide (a ≤ b)) = hs := by rw [hinv.1]; rfl
  have hflopen := firstLayer_open_honest hV fmmcs hfm α L hH hbd hG qp.1 hidx
  have hfls : firstLayerSiblings H (st.2.mergeSort fun a b => decide (a ≤ b)) qp.1
      (fmmcs.open_multi_batch (qp.1.map (· / 2)) fld).1 =
      qp.1.map fun i => hs.map fun h => corr G lb α L h (-qPt G H i h) := by
    rw [hkeys]
    erw [hflopen]
    exact firstLayerSiblings_honest α L qp.1
  have hqne : qp.1 ≠ [] := fun h => hq (by rw [← hql, h]; rfl)
  have hfl : fmmcs.verify_multi_batch flc (if qp.1 = [] then [] else hs.map fun h => (2, 2 ^ (h - 1)))
      (qp.1.map (· / 2)) (qp.1.map fun i => hs.map fun h => flVals G lb H α L h i)
      (fmmcs.open_multi_batch (qp.1.map (· / 2)) fld).2 = .ok () := by
    have hdims : (hs.map fun h => (2, 2 ^ (h - 1))) = mats.map fun m => (m.width, m.height) := by
      simp only [mats, List.map_map]
      refine List.map_congr_left fun h hh => ?_
      have := hbd h hh
      show (2, 2 ^ (h - 1)) = ((matOfPairs (corrCol G lb α L h)).width, (matOfPairs (corrCol G lb α L h)).height)
      rw [height_matOfPairs_corrCol lb α L (show 1 ≤ h by omega)]
      rfl
    simp only [hqne, ↓reduceIte]
    rw [hdims, ← hflopen]
    refine hfm.accepts mats _ (by simpa [mats] using List.ne_nil_of_mem hH) (fun m hm => ?_) (fun I hI => ?_)
    · obtain ⟨h, hh, rfl⟩ := List.mem_map.mp hm
      have := hbd h hh
      rw [height_matOfPairs_corrCol lb α L (show 1 ≤ h by omega), Nat.log_pow (by norm_num)]
    · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hI
      rw [topLog_firstLayer α L hH hbd]
      have := hidx i hi
      rw [show 2 ^ H = 2 * 2 ^ (H - 1) by rw [← pow_succ']; congr 1; omega] at this
      omega
  -- The commit phase.
  set β : ℕ → K := (run.1.getD · 0)
  have hcwk : ∀ k (hk : k < cws.length), cws[k] = cwAt G lb H E β k := fun k _ => by
    simp [cws, β]
  have hsv : ∀ k < H - (lb + 1), ∀ (q i : ℕ), qp.1[q]? = some i →
      (((answersOf fmmcs cws (qp.1.map (· / 2))).map (·.sibling_values)).getD k [])[q]? =
        some [xEval (H - (lb + 1) - k) (layer E β k) (-(sgn (i / 2) k * Xq G (H - 1) (i / 2) k))] := by
    intro k hk q i hqi
    have hk' : k < cws.length := by rw [hcws]; exact hk
    have hi := hidx i (List.mem_of_getElem? hqi)
    rw [List.getD_eq_getElem _ _ (by simpa [answersOf_length] using hk'), List.getElem_map,
      answersOf_getElem fmmcs cws _ k hk', roundAnswer, List.map_map, List.getElem?_map, List.getElem?_map, hqi,
      hcwk k hk']
    simp only [Option.map_some, Function.comp_apply, Option.some.injEq, List.cons.injEq, and_true]
    set t := i / 2 / 2 ^ k
    have hg : i / 2 / 2 ^ (k + 1) = t / 2 := by
      show i / 2 / 2 ^ (k + 1) = i / 2 / 2 ^ k / 2
      rw [Nat.div_div_eq_div_mul (i / 2), pow_succ]
    have htlt : t < 2 ^ (H - 1 - k) := by
      rw [Nat.div_lt_iff_lt_mul (by positivity), ← pow_add, show H - 1 - k + k = H - 1 by omega,
        Nat.div_lt_iff_lt_mul (by norm_num), ← pow_succ, show H - 1 + 1 = H by omega]; exact hi
    have hXq : Xq G (H - 1) (i / 2) k = Xp G (H - k) (2 * (t / 2)) := by
      rw [Xq_eq_Xp (show k + 1 ≤ H - 1 by omega), hg, show H - 1 - 1 - k + 2 = H - k by omega]
    have heven : 2 ^ (H - 1 - k) = 2 * 2 ^ (H - 2 - k) := by rw [← pow_succ']; congr 1; omega
    rw [hXq, sgn, show i / 2 / 2 ^ k = t from rfl]
    rcases Nat.mod_two_eq_zero_or_one t with hb | hb
    · rw [hb, cwAt_getD lb H E β (by omega)]
      simp only [Nat.sub_zero, ↓reduceIte, one_mul]
      rw [show H - k = (H - k - 2) + 2 by omega, Xp_odd hV (by omega)]
    · rw [hb, cwAt_getD lb H E β (by omega)]
      simp [show (1 : ℕ) ≠ 0 by norm_num]
  have hfinal : final = preLayer E β R 0 := by
    rw [show final = layer E β R 0 from rfl, layer_eq]
    have hR : H - R ∉ heightsOf lb L := fun h => by have := hbd _ h; omega
    simp only [E, friCoeffs, hR, ↓reduceIte, add_zero]
  have hmmcs : ∀ k < H - (lb + 1), ∀ (c : fmmcs.Commitment) (o : CommitPhaseMultiStep K fmmcs.MultiProof),
      run.2.1[k]? = some c → (answersOf fmmcs cws (qp.1.map (· / 2)))[k]? = some o →
      fmmcs.verify_multi_batch c [(2, 2 ^ (H - 1 - (k + 1)))] (qp.1.map fun i => i / 2 / 2 ^ (k + 1))
        ((qp.1.map fun i => i / 2 / 2 ^ (k + 1)).map fun j =>
          [honestWord G (H - 1) (H - (lb + 1)) E β k j]) o.opening_proof = .ok () := by
    intro k hk c o hc ho
    have hk' : k < cws.length := by rw [hcws]; exact hk
    have hcs : run.2.1 = cws.map fun cw => (fmmcs.commit [matOfPairs cw]).1 := by
      rw [(honestRun_commits (G := G) lb H E fmmcs tp s2 R).1, List.map_map]; rfl
    rw [hcs, List.getElem?_map, List.getElem?_eq_getElem hk', Option.map_some, Option.some.injEq] at hc
    rw [List.getElem?_eq_getElem (by rw [answersOf_length]; exact hk'), answersOf_getElem fmmcs cws _ k hk',
      Option.some.injEq] at ho
    subst hc ho
    have hgroups : ((qp.1.map (· / 2)).map (· / 2 ^ k)).map (· / 2) = qp.1.map fun i => i / 2 / 2 ^ (k + 1) := by
      simp only [List.map_map]
      refine List.map_congr_left fun i _ => ?_
      simp [Nat.div_div_eq_div_mul, pow_succ, mul_comm]
    set cw := cws[k]
    have hcw : cw = cwAt G lb H E β k := hcwk k hk'
    have hheight : (matOfPairs cw).height = 2 ^ (H - 1 - (k + 1)) := by
      simp only [matOfPairs, hcw, length_cwAt]
      rw [show H - 1 - k = H - 1 - (k + 1) + 1 by omega, pow_succ, Nat.mul_div_cancel _ (by norm_num)]
    have hrows : (fmmcs.open_multi_batch (qp.1.map fun i => i / 2 / 2 ^ (k + 1))
        (fmmcs.commit [matOfPairs cw]).2).1 = (qp.1.map fun i => i / 2 / 2 ^ (k + 1)).map fun j =>
          [honestWord G (H - 1) (H - (lb + 1)) E β k j] := by
      rw [hfm.rows]
      refine List.map_congr_left fun j hj => ?_
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hj
      have hi' := hidx i hi
      have hjlt : i / 2 / 2 ^ (k + 1) < 2 ^ (H - 1 - (k + 1)) := by
        rw [Nat.div_div_eq_div_mul, Nat.div_lt_iff_lt_mul (by positivity), ← pow_succ', ← pow_add,
          show H - 1 - (k + 1) + (k + 1 + 1) = H by omega]; exact hi'
      have h2x : 2 ^ (H - 1 - k) = 2 * 2 ^ (H - 1 - (k + 1)) := by rw [← pow_succ']; congr 1; omega
      simp only [List.map_cons, List.map_nil, topLog_singleton, Nat.sub_self, pow_zero, Nat.div_one]
      rw [rowsOf_matOfPairs_getD cw (by rw [show cw.length / 2 = 2 ^ (H - 1 - (k + 1)) from hheight]; exact hjlt),
        hcw, cwAt_getD lb H E β (by rw [h2x]; omega), cwAt_getD lb H E β (by rw [h2x]; omega),
        honestWord, Xg_eq_Xp (by omega), show H - k = (H - k - 2) + 2 by omega, Xp_odd hV (by omega)]
    rw [roundAnswer, hgroups, ← hrows]
    have hacc := hfm.accepts [matOfPairs cw] (qp.1.map fun i => i / 2 / 2 ^ (k + 1)) (by simp)
      (fun m hm => by
        rw [List.mem_singleton] at hm; subst hm; rw [hheight, Nat.log_pow (by norm_num)])
      (fun I hI => by
        obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hI
        rw [topLog_singleton, hheight, Nat.log_pow (by norm_num), Nat.div_div_eq_div_mul,
          Nat.div_lt_iff_lt_mul (by positivity), ← pow_succ', ← pow_add,
          show H - 1 - (k + 1) + (k + 1 + 1) = H by omega]
        exact hidx i hi)
    simp only [List.map_cons, List.map_nil] at hacc
    rw [hheight] at hacc
    exact hacc
  exact verify_complete_honest hV h2 immcs fmmcs tv params (claimsOf G immcs lb hb) _ sv
    (by rw [claimHeights_claimsOf]; exact hmax) (by omega) (by omega) hshape hbp hreplay hrl.1 hidx hc hio hin
    hfls rfl hfl hsv hfinal hmmcs

end Plonky3Lean.Proofs.Circle
