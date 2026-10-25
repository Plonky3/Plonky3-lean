module

public import Plonky3Lean.Proofs.Circle.Query
public import Plonky3Lean.Proofs.Circle.Poly
public import Plonky3Lean.Proofs.Fri.Honest

@[expose] public section

/-!
# p3-circle: the input checks accept honest openings

Take columns that are polynomials of degree below the trace size, opened at points off the LDE domain.

At every height, the verifier's reduction then reads one function of the query point: the DEEP function.

By the DEEP quotient lemma, that function has the degree of the columns.

Its lambda correction then lies in the FFT space, and its first-layer fold is what circle FRI folds.
-/

namespace Plonky3Lean.Proofs.Circle

open Plonky3Lean.Spec.Circle Plonky3Lean.Proofs.Dft Finset
open p3_dft.mirror p3_fri.mirror p3_circle.point.mirror p3_circle.deep_quotient.mirror

set_option linter.unusedSectionVars false

variable {K : Type} [Field K] [DecidableEq K] {G : Gen (K × K)}

/-! ## The DEEP term of honest values -/

/-- The real part of the quotient by v is half the numerator, off the opening point. -/
theorem cquot_fst (h2 : (2 : K) ≠ 0) (g : K) {P Q : C K} (hPQ : P ≠ Q) :
    (cquot g (Point.v_p (ofC P) (ofC Q))).1 = g / 2 := by
  have hre := mt (v_p_denom_eq_zero h2 P Q).mp hPQ
  have hv1 : (Point.v_p (ofC P) (ofC Q)).1 ≠ 0 := fun h => hre (by rw [h, add_zero])
  rw [cquot, v_p_norm]
  field_simp

/-- The imaginary part of the quotient by v is g (P - Q)_y / (2 (1 - (P - Q)_x)), off the opening point. -/
theorem cquot_snd (h2 : (2 : K) ≠ 0) (g : K) {P Q : C K} (hPQ : P ≠ Q) :
    (cquot g (Point.v_p (ofC P) (ofC Q))).2 * (2 * (1 - (P - Q).x)) = g * (P - Q).y := by
  have hre := mt (v_p_denom_eq_zero h2 P Q).mp hPQ
  have hv1 : (Point.v_p (ofC P) (ofC Q)).1 ≠ 0 := fun h => hre (by rw [h, add_zero])
  rw [cquot, v_p_norm]
  rw [v_p_eq] at hv1 ⊢
  have hx : (Q - P).x = (P - Q).x := by simp only [C.sub_x]; ring
  have hy : (Q - P).y = -(P - Q).y := by simp only [C.sub_y]; ring
  rw [hx, hy]
  have hv1' : 1 - (P - Q).x ≠ 0 := by simpa [hx] using hv1
  field_simp

/-- The DEEP term of honest values at one opening point has the degree of the columns, off that point. -/
theorem deepTerm_circlePoly (h2 : (2 : K) ≠ 0) (α : K) {D : ℕ} (Z : C K) (fs : List (C K → K))
    (hfs : ∀ f ∈ fs, IsCirclePoly D f) :
    ∃ F, IsCirclePoly D F ∧ ∀ P, P ≠ Z → deepTerm α P Z (fs.map (· P)) (fs.map (· Z)) = F P := by
  set f : ℕ → C K → K := fun j => (fs[j]?).getD fun _ => 0
  have hf : ∀ j, IsCirclePoly D (f j) := fun j => by
    rcases h : fs[j]? with _ | g
    · simpa [f, h] using IsCirclePoly.const D (0 : K)
    · simpa [f, h] using hfs g (List.mem_of_getElem? h)
  choose g hg hgeq using fun j => (hf j).deep Z
  refine ⟨fun P => ∑ j ∈ range fs.length, (α ^ j * ((f j P - f j Z) / 2) + α ^ (fs.length + j) * (g j P / 2)),
    IsCirclePoly.sum _ fun j _ => ?_, fun P hP => ?_⟩
  · refine IsCirclePoly.add (IsCirclePoly.smul _ ?_) (IsCirclePoly.smul _ ?_)
    · simpa [div_eq_mul_inv, mul_comm, ← sub_eq_add_neg] using IsCirclePoly.smul (2 : K)⁻¹
        (IsCirclePoly.add (hf j) (IsCirclePoly.const D (-f j Z)))
    · simpa [div_eq_mul_inv, mul_comm] using IsCirclePoly.smul (2 : K)⁻¹ (hg j)
  · have hne : 1 - (P - Z).x ≠ 0 := by
      have := mt (v_p_denom_eq_zero h2 P Z).mp hP
      rw [v_p_eq, show (Z - P).x = (P - Z).x by simp only [C.sub_x]; ring] at this
      intro h; exact this (by rw [h, add_zero])
    unfold deepTerm
    rw [List.length_map]
    refine sum_congr rfl fun j hj => ?_
    have hget : ∀ Q, (fs.map (· Q)).getD j 0 = f j Q := fun Q => by
      rw [List.getD_eq_getElem?_getD, List.getElem?_map]
      rcases h : fs[j]? with _ | g <;> simp [f, h]
    rw [hget, hget, cquot_fst h2 _ hP]
    congr 1
    have hs := cquot_snd h2 (f j P - f j Z) hP
    rw [← hgeq j P] at hs
    have hc : (cquot (f j P - f j Z) (Point.v_p (ofC P) (ofC Z))).2 * 2 = g j P :=
      mul_left_cancel₀ hne (by linear_combination hs)
    rw [← hc]
    field_simp

/-! ## The DEEP function of one height -/

open p3_commit.pcs.univariate.mirror p3_circle.domain.mirror

/-- An honest matrix: its claims, and the polynomials of its columns. -/
abbrev HMat (K : Type) [Field K] := MatrixOpening K (CircleDomain K) × List (C K → K)

/-- The reduction of one matrix at the query point Q.

Each opening point adds its DEEP term times the running power of alpha, which then grows by alpha^(2 W). -/
noncomputable def matStep (α : K) (m : HMat K) (Q : C K) (e : K × K) : K × K :=
  m.1.points.foldl (fun e p => (e.1 * (α ^ (m.2.map (· Q)).length) ^ 2,
    e.2 + e.1 * deepTerm α Q (ptOf p.point) (m.2.map (· Q)) p.values)) e

/-- The running power of alpha and the reduced value after the matrices ms, at the query point Q. -/
noncomputable def deepAcc (α : K) (ms : List (HMat K)) (Q : C K) (e : K × K) : K × K :=
  ms.foldl (fun e m => matStep α m Q e) e

/-- The honest claims of a matrix: columns of degree at most D, and values that are their evaluations. -/
def HonestMat (D : ℕ) (m : HMat K) : Prop :=
  (∀ f ∈ m.2, IsCirclePoly D f) ∧ ∀ p ∈ m.1.points, p.values = m.2.map (· (ptOf p.point))

/-- The reduced value of honest matrices is a polynomial of their degree, off their opening points.

The running power of alpha does not depend on the query point. -/
theorem deepAcc_circlePoly (h2 : (2 : K) ≠ 0) (α : K) {D : ℕ} :
    ∀ (ms : List (HMat K)), (∀ m ∈ ms, HonestMat D m) → ∀ (a : K) (b : C K → K), IsCirclePoly D b →
      ∃ (a' : K) (F : C K → K), IsCirclePoly D F ∧
        ∀ Q, (∀ m ∈ ms, ∀ p ∈ m.1.points, Q ≠ ptOf p.point) → deepAcc α ms Q (a, b Q) = (a', F Q)
  | [], _, a, b, hb => ⟨a, b, hb, fun _ _ => rfl⟩
  | m :: ms, hms, a, b, hb => by
    obtain ⟨hcols, hvals⟩ := hms m List.mem_cons_self
    have hpts : ∀ (pts : List (PointOpening K)), (∀ p ∈ pts, p.values = m.2.map (· (ptOf p.point))) →
        ∀ (a : K) (b : C K → K), IsCirclePoly D b → ∃ (a' : K) (F : C K → K), IsCirclePoly D F ∧
          ∀ Q, (∀ p ∈ pts, Q ≠ ptOf p.point) →
            pts.foldl (fun e p => (e.1 * (α ^ (m.2.map (· Q)).length) ^ 2,
              e.2 + e.1 * deepTerm α Q (ptOf p.point) (m.2.map (· Q)) p.values)) (a, b Q) = (a', F Q) := by
      intro pts
      induction pts with
      | nil => exact fun _ a b hb => ⟨a, b, hb, fun _ _ => rfl⟩
      | cons p pts ih =>
        intro hv a b hb
        obtain ⟨Fp, hFp, hFpeq⟩ := deepTerm_circlePoly h2 α (ptOf p.point) m.2 hcols
        obtain ⟨a', F, hF, hFeq⟩ := ih (fun q hq => hv q (List.mem_cons_of_mem _ hq))
          (a * (α ^ m.2.length) ^ 2) (fun Q => b Q + a * Fp Q) (hb.add (hFp.smul a))
        refine ⟨a', F, hF, fun Q hQ => ?_⟩
        have := hFeq Q fun q hq => hQ q (List.mem_cons_of_mem _ hq)
        rw [List.foldl_cons, hv p List.mem_cons_self, hFpeq Q (hQ p List.mem_cons_self)]
        simp only [List.length_map] at this ⊢
        exact this
    obtain ⟨a1, F1, hF1, hF1eq⟩ := hpts m.1.points hvals a b hb
    obtain ⟨a', F, hF, hFeq⟩ := deepAcc_circlePoly h2 α ms (fun m' hm' => hms m' (List.mem_cons_of_mem _ hm'))
      a1 F1 hF1
    refine ⟨a', F, hF, fun Q hQ => ?_⟩
    rw [deepAcc, List.foldl_cons, matStep, hF1eq Q (hQ m List.mem_cons_self)]
    exact hFeq Q fun m' hm' => hQ m' (List.mem_cons_of_mem _ hm')

/-! ## The verifier's reduction of honest openings -/

open p3_circle.pcs.mirror p3_circle.ordering.mirror p3_circle.verifier.mirror p3_circle.folding.mirror

/-- The point the query of index i reads at height h. -/
noncomputable def qPt (G : Gen (K × K)) (H index h : ℕ) : C K :=
  twinPoint (genPt G (h + 1)) (genPt G (h - 1)) (cfft_permute_index (index / 2 ^ (H - h)) h)

/-- The height of the LDE of a matrix. -/
def hgt (lb : ℕ) (m : HMat K) : ℕ := m.1.domain.log_n + lb

/-- The reduction state after one honest matrix: its height's entry is reduced, and its height recorded. -/
noncomputable def stepPure (G : Gen (K × K)) (lb H index : ℕ) (α : K) (st : (ℕ → K × K) × List ℕ) (m : HMat K) :
    (ℕ → K × K) × List ℕ :=
  (Function.update st.1 (hgt lb m) (matStep α m (qPt G H index (hgt lb m)) (st.1 (hgt lb m))),
    if hgt lb m ∈ st.2 then st.2 else st.2 ++ [hgt lb m])

/-- What one matrix needs for the verifier to reduce it as the honest prover did:

- a domain of at least 2 rows, below the tallest height, and a claimed width within the widest
- at least one opening point, with honest values
- opening points on the circle, off the point the query reads. -/
structure MatOK (G : Gen (K × K)) (lb H M index : ℕ) (m : HMat K) : Prop where
  log_n : 1 ≤ m.1.domain.log_n
  height : m.1.domain.log_n + lb ≤ H
  width : m.2.length ≤ M
  points_ne : m.1.points ≠ []
  values : ∀ p ∈ m.1.points, p.values = m.2.map (· (ptOf p.point))
  points : ∀ p ∈ m.1.points, 1 + p.point * p.point ≠ 0 ∧ ptOf p.point ≠ qPt G H index (hgt lb m)

theorem claimedWidth_eq {lb H M index : ℕ} {m : HMat K} (hm : MatOK G lb H M index m) :
    claimedWidth m.1 = m.2.length := by
  obtain ⟨p, ps, hp⟩ := List.exists_cons_of_ne_nil hm.points_ne
  rw [claimedWidth, hp, List.headD_cons, hm.values p (by rw [hp]; exact List.mem_cons_self), List.length_map]

theorem reduceMatrix_honest {IME FME : Type} (hV : CircleGenValid G) (h2 : (2 : K) ≠ 0) {lb H M : ℕ} (α : K)
    (index : ℕ) (st : (ℕ → K × K) × List ℕ) (m : HMat K) (hm : MatOK G lb H M index m)
    (hG : H + 1 ≤ G.adicity) :
    reduceMatrix (IME := IME) (FME := FME) G lb H ((List.range M).map (α ^ ·)) index st
        (m.1, m.2.map (· (qPt G H index (hgt lb m))), α ^ claimedWidth m.1, (α ^ claimedWidth m.1) ^ 2) =
      pure (stepPure G lb H index α st m) := by
  obtain ⟨acc, keys⟩ := st
  have hw := claimedWidth_eq hm
  rw [hw, show m.2.length = (m.2.map (· (qPt G H index (hgt lb m)))).length by simp]
  rw [reduceMatrix_eq hV h2 α index acc keys m.1 _ hm.log_n hm.height hG (by simpa using hm.width)
    (fun p hp => by rw [hm.values p hp]; simp) hm.points]
  rfl

theorem foldl_zipIdx_fst {α β : Type _} (f : β → α → β) (l : List α) (b : β) :
    (l.zipIdx).foldl (fun b (e : α × ℕ) => f b e.1) b = l.foldl f b := by
  have := List.foldl_map (g := f) (f := Prod.fst) (l := l.zipIdx) (init := b)
  rw [List.zipIdx_map_fst] at this
  exact this.symm

theorem reduceBatch_honest {IME FME Com MP : Type} (hV : CircleGenValid G) (h2 : (2 : K) ≠ 0) {lb H M : ℕ}
    (α : K) (index query : ℕ) (st : (ℕ → K × K) × List ℕ) (ms : List (HMat K)) (bo : BatchMultiOpening K MP)
    (c : Claim K Com) (hc : c.matrices = ms.map Prod.fst)
    (hrow : bo.opened_values[query]? = some (ms.map fun m => m.2.map (· (qPt G H index (hgt lb m)))))
    (hms : ∀ m ∈ ms, MatOK G lb H M index m) (hG : H + 1 ≤ G.adicity) :
    reduceBatch (IME := IME) (FME := FME) G lb H ((List.range M).map (α ^ ·)) index query st
        (bo, c, c.matrices.map fun m => (α ^ claimedWidth m, (α ^ claimedWidth m) ^ 2)) =
      pure (ms.foldl (stepPure G lb H index α) st) := by
  unfold reduceBatch
  simp only [hrow, lift_some_bind', hc, List.length_map, ne_eq, not_true_eq_false, ↓reduceIte]
  rw [zip_map_map, List.zipIdx_map, List.foldlM_map]
  rw [foldlM_eq_pure_foldl _ _ fun st e he => ?_]
  · exact congrArg pure (foldl_zipIdx_fst _ ms st)
  · obtain ⟨hk, hek⟩ := List.mem_zipIdx' he
    simp only [Prod.map, id, List.getElem?_map, List.getElem?_eq_getElem hk, Option.map_some, ← hek,
      lift_some_bind']
    exact reduceMatrix_honest hV h2 α index st _ (hms _ (hek ▸ List.getElem_mem hk)) hG

/-- The batches of one query on honest openings reduce as the honest matrices do, in order. -/
theorem reduceBatches_honest {IME FME Com MP : Type} (hV : CircleGenValid G) (h2 : (2 : K) ≠ 0) {lb H M : ℕ}
    (α : K) (index query : ℕ) (hG : H + 1 ≤ G.adicity) :
    ∀ {io : List (BatchMultiOpening K MP)} {rounds : List (Claim K Com)} {hb : List (List (HMat K))},
      List.Forall₂ (fun c ms => c.matrices = ms.map Prod.fst) rounds hb →
      List.Forall₂ (fun bo (ms : List (HMat K)) => bo.opened_values[query]? =
        some (ms.map fun m => m.2.map (· (qPt G H index (hgt lb m))))) io hb →
      (∀ ms ∈ hb, ∀ m ∈ ms, MatOK G lb H M index m) → ∀ st,
      (io.zip (rounds.zip (rounds.map fun c => c.matrices.map fun m =>
          (α ^ claimedWidth m, (α ^ claimedWidth m) ^ 2)))).foldlM
        (reduceBatch (IME := IME) (FME := FME) G lb H ((List.range M).map (α ^ ·)) index query) st =
      pure (hb.flatten.foldl (stepPure G lb H index α) st)
  | io, _, _, hcs, hrows, hok, st => by
    induction hcs generalizing io st with
    | nil => cases hrows; rfl
    | @cons c ms rounds hb hc hcs ih =>
      cases hrows with
      | @cons bo _ io _ hrow hrows =>
      simp only [List.map_cons, List.zip_cons_cons, List.foldlM_cons, List.flatten_cons, List.foldl_append]
      rw [reduceBatch_honest hV h2 α index query st ms bo c hc hrow (hok ms List.mem_cons_self) hG, pure_bind]
      exact ih io hrows (fun ms' hms' => hok ms' (List.mem_cons_of_mem _ hms')) _

/-- The entry of height h after the honest matrices: the reduction of the matrices of that height. -/
theorem foldl_stepPure_fst (lb H index : ℕ) (α : K) (h : ℕ) :
    ∀ (ms : List (HMat K)) (st : (ℕ → K × K) × List ℕ),
      (ms.foldl (stepPure G lb H index α) st).1 h =
        deepAcc α (ms.filter fun m => hgt lb m = h) (qPt G H index h) (st.1 h)
  | [], st => rfl
  | m :: ms, st => by
    rw [List.foldl_cons, foldl_stepPure_fst lb H index α h ms, List.filter_cons]
    by_cases hm : hgt lb m = h
    · subst hm; simp [stepPure, deepAcc]
    · simp [stepPure, hm, Function.update_of_ne (Ne.symm hm)]

/-- The heights recorded after the honest matrices. -/
theorem foldl_stepPure_snd (lb H index : ℕ) (α : K) :
    ∀ (ms : List (HMat K)) (st : (ℕ → K × K) × List ℕ),
      (ms.foldl (stepPure G lb H index α) st).2 = Plonky3Lean.Proofs.Fri.keysAfter st.2 (ms.map (hgt lb))
  | [], st => rfl
  | m :: ms, st => by
    rw [List.foldl_cons, foldl_stepPure_snd lb H index α ms]
    rfl

/-- The first-layer leaf of height h at a query, in full. -/
theorem firstLayerLeaf_eq (hV : CircleGenValid G) {lb H h : ℕ} (index : ℕ) (hlb : 1 ≤ lb) (hh : lb + 1 ≤ h)
    (hhH : h ≤ H) (hG : H + 1 ≤ G.adicity) (ro sib lam : K) :
    firstLayerLeaf G lb H index (((h, ro), sib), lam) = some (h,
      (if (index / 2 ^ (H - h)) % 2 = 0 then (qPt G H index h).y else -(qPt G H index h).y),
      (if (index / 2 ^ (H - h)) % 2 = 0 then [ro - lam * vn (h - lb) (qPt G H index h), sib]
        else [sib, ro - lam * vn (h - lb) (qPt G H index h)]), (2, 2 ^ (h - 1))) := by
  have hpt := standard_nth_point hV (h := h) (by omega) (by omega) (cfft_permute_index (index / 2 ^ (H - h)) h)
  rw [standard_eq hV _ (by omega), Option.bind_some] at hpt
  unfold firstLayerLeaf
  simp only [show h ≠ 0 by omega, show ¬ h < lb by omega, show ¬ H < h by omega, ↓reduceIte,
    standard_eq hV _ (by omega : h + 1 ≤ G.adicity), hpt, v_n_ofC, show 1 ≤ h - lb by omega,
    Option.bind_eq_bind, Option.bind_some]
  split_ifs <;> rfl

/-! ## The honest DEEP function of each height, and its lambda correction -/

/-- The DEEP function of height h: the reduction of the honest matrices of that height at Q. -/
noncomputable def deepFnAt (lb : ℕ) (α : K) (L : List (HMat K)) (h : ℕ) (Q : C K) : K :=
  (deepAcc α (L.filter fun m => hgt lb m = h) Q (1, 0)).2

/-- Point k of the standard domain of size 2^h. -/
noncomputable def ptD (G : Gen (K × K)) (h k : ℕ) : C K := (2 * k + 1) • genPt G (h + 1)

/-- The DEEP function of height h on its LDE domain, in circle FFT order: the prover's reduced column. -/
noncomputable def ldeVec (G : Gen (K × K)) (lb : ℕ) (α : K) (L : List (HMat K)) (h : ℕ) : List K :=
  (List.range (2 ^ h)).map fun i => deepFnAt lb α L h (ptD G h (cfft_permute_index i h))

/-- The lambda the prover extracts at height h. -/
noncomputable def lamAt (G : Gen (K × K)) (lb : ℕ) (α : K) (L : List (HMat K)) (h : ℕ) : K :=
  ((extract_lambda G (ldeVec G lb α L h) lb).map Prod.fst).getD 0

/-- The lambda-corrected DEEP function of height h. -/
noncomputable def corr (G : Gen (K × K)) (lb : ℕ) (α : K) (L : List (HMat K)) (h : ℕ) (Q : C K) : K :=
  deepFnAt lb α L h Q - lamAt G lb α L h * vn (h - lb) Q

/-- The DEEP function of height h splits on its LDE domain as an FFT-basis function plus a multiple of v_n. -/
def DeepSplits (G : Gen (K × K)) (lb : ℕ) (α : K) (L : List (HMat K)) (h : ℕ) (c : ℕ → K) : Prop :=
  ∃ μ : K, ∀ k < 2 ^ h, deepFnAt lb α L h (ptD G h k) = fftEval (h - lb) c (ptD G h k) + μ * vn (h - lb) (ptD G h k)

open Classical in
/-- Coefficients in the FFT basis of the lambda-corrected DEEP function of height h. -/
noncomputable def deepCoeffs (G : Gen (K × K)) (lb : ℕ) (α : K) (L : List (HMat K)) (h : ℕ) : ℕ → K :=
  if hc : ∃ c, DeepSplits G lb α L h c then hc.choose else fun _ => 0

/-- What the DEEP lemma needs of the honest matrices of height h:

- columns of degree at most 2^(h - lb - 1), and values that are their evaluations
- opening points off the LDE domain of height h. -/
def HonestAt (G : Gen (K × K)) (lb : ℕ) (L : List (HMat K)) (h : ℕ) : Prop :=
  ∀ m ∈ L, hgt lb m = h → HonestMat (2 ^ (h - lb - 1)) m ∧ ∀ p ∈ m.1.points, ∀ k < 2 ^ h, ptOf p.point ≠ ptD G h k

/-- The DEEP quotient lemma at height h: the DEEP function splits. -/
theorem deep_splits (h2 : (2 : K) ≠ 0) {lb : ℕ} (α : K) {L : List (HMat K)} {h : ℕ} (hh : lb + 1 ≤ h)
    (hon : HonestAt G lb L h) : DeepSplits G lb α L h (deepCoeffs G lb α L h) := by
  suffices hc : ∃ c, DeepSplits G lb α L h c by
    unfold deepCoeffs; rw [dite_eq_left_of_eq_true (eq_true hc)]; exact hc.choose_spec
  obtain ⟨a', F, hF, hFeq⟩ := deepAcc_circlePoly h2 α (L.filter fun m => hgt lb m = h)
    (fun m hm => (hon m (List.mem_filter.mp hm).1 (by simpa using (List.mem_filter.mp hm).2)).1)
    1 (fun _ => 0) (IsCirclePoly.const _ 0)
  obtain ⟨c, μ, hc⟩ := hF.split_vn h2
  refine ⟨c, μ, fun k hk => ?_⟩
  rw [deepFnAt, hFeq _ fun m hm p hp => ?_, hc, show h - lb - 1 + 1 = h - lb by omega]
  have hm' := List.mem_filter.mp hm
  exact Ne.symm ((hon m hm'.1 (by simpa using hm'.2)).2 p hp k hk)

/-- The lambda the prover extracts is the multiple of v_n, and the corrected function is the FFT-basis one. -/
theorem corr_ptD (hV : CircleGenValid G) (h2 : (2 : K) ≠ 0) {lb : ℕ} (α : K) {L : List (HMat K)} {h : ℕ}
    (hlb : 1 ≤ lb) (hh : lb + 1 ≤ h) (hG : h + 1 ≤ G.adicity) (hon : HonestAt G lb L h) {k : ℕ} (hk : k < 2 ^ h) :
    corr G lb α L h (ptD G h k) = fftEval (h - lb) (deepCoeffs G lb α L h) (ptD G h k) := by
  obtain ⟨μ, hμ⟩ := deep_splits h2 α hh hon
  have hext := extract_lambda_split hV h2 hlb hh hG (fun k => deepFnAt lb α L h (ptD G h k)) _ μ hμ
  have hlam : lamAt G lb α L h = μ := by rw [lamAt, ldeVec]; simp only [ptD] at hext ⊢; rw [hext]; rfl
  rw [corr, hlam, hμ k hk]
  ring

/-! ## One query on honest openings -/

/-- The parity bit of a query index at height h: which member of its pair the query reads. -/
def qBit (H index h : ℕ) : ℕ := (index / 2 ^ (H - h)) % 2

/-- The y-twiddle of the first-layer leaf of height h. -/
noncomputable def yTw (G : Gen (K × K)) (H index h : ℕ) : K :=
  if qBit H index h = 0 then (qPt G H index h).y else -(qPt G H index h).y

/-- The first-layer row of height h at a query: the corrected function at its point and at the conjugate. -/
noncomputable def flVals (G : Gen (K × K)) (lb H : ℕ) (α : K) (L : List (HMat K)) (h index : ℕ) : List K :=
  if qBit H index h = 0 then [corr G lb α L h (qPt G H index h), corr G lb α L h (-qPt G H index h)]
  else [corr G lb α L h (-qPt G H index h), corr G lb α L h (qPt G H index h)]

/-- The heights of the honest matrices, increasing, as the verifier sorts them. -/
def heightsOf (lb : ℕ) (L : List (HMat K)) : List ℕ :=
  (Plonky3Lean.Proofs.Fri.keysAfter [] (L.map (hgt lb))).mergeSort (fun a b => decide (a ≤ b))

/-- The input circle FRI rolls in from height h at a query: the folded DEEP function at the round's point. -/
noncomputable def friVal (G : Gen (K × K)) (lb H : ℕ) (α β : K) (L : List (HMat K)) (h index : ℕ) : K :=
  xEval (h - lb - 1) (foldCoeffs (deepCoeffs G lb α L h) β) (sgn (index / 2) (H - h) * Xq G (H - 1) (index / 2) (H - h))

theorem qPt_eq (hV : CircleGenValid G) {H h : ℕ} (index : ℕ) (hh : 1 ≤ h) (hG : h + 1 ≤ G.adicity) :
    qPt G H index h = ptD G h (cfft_permute_index (index / 2 ^ (H - h)) h) :=
  twinPoint_standard hV hh hG _

theorem neg_ptD (hV : CircleGenValid G) {h k : ℕ} (hk : k < 2 ^ h) (hG : h + 1 ≤ G.adicity) :
    -ptD G h k = ptD G h (2 ^ h - 1 - k) := by
  rw [neg_eq_iff_add_eq_zero, ptD, ptD, ← add_nsmul,
    show 2 * k + 1 + (2 * (2 ^ h - 1 - k) + 1) = 2 ^ (h + 1) by rw [pow_succ]; omega]
  exact genPt_order_zero hV hG

/-- The first-layer fold of an honest row is the input circle FRI rolls in, equations (14) to (16). -/
theorem flVals_fold (hV : CircleGenValid G) (h2 : (2 : K) ≠ 0) {lb H h : ℕ} (α β : K) {L : List (HMat K)}
    {index : ℕ} (hi : index < 2 ^ H) (hlb : 1 ≤ lb) (hh : lb + 2 ≤ h) (hhH : h ≤ H) (hG : H + 1 ≤ G.adicity)
    (hon : HonestAt G lb L h) :
    fold_row_with_inv_twiddle (yTw G H index h)⁻¹ β (flVals G lb H α L h index) =
      some (friVal G lb H α β L h index) := by
  set j := cfft_permute_index (index / 2 ^ (H - h)) h
  have hj : j < 2 ^ h := cfft_permute_index_lt h _
  have hP := qPt_eq hV (H := H) index (by omega : 1 ≤ h) (by omega)
  have hy : (qPt G H index h).y ≠ 0 := twinPoint_standard_y_ne_zero hV h2 (by omega) (by omega) _
  have hc1 : corr G lb α L h (qPt G H index h) = fftEval (h - lb) (deepCoeffs G lb α L h) (qPt G H index h) := by
    rw [hP]; exact corr_ptD hV h2 α hlb (by omega) (by omega) hon hj
  have hc2 : corr G lb α L h (-qPt G H index h) =
      fftEval (h - lb) (deepCoeffs G lb α L h) (-qPt G H index h) := by
    rw [hP, neg_ptD hV hj (by omega)]; exact corr_ptD hV h2 α hlb (by omega) (by omega) hon (by omega)
  obtain ⟨m, hm⟩ : ∃ m, h - lb = m + 1 := ⟨h - lb - 1, by omega⟩
  have := firstLayer_fold h2 hy (qBit H index h) m (deepCoeffs G lb α L h) β
  rw [← hm] at this
  rw [yTw, flVals, hc1, hc2, this, friVal, show h - lb - 1 = m by omega,
    ← firstLayer_point_x hV (by omega) hhH hG hi]
  rfl

theorem yTw_ne_zero (hV : CircleGenValid G) (h2 : (2 : K) ≠ 0) {H h : ℕ} (index : ℕ) (hh : 1 ≤ h)
    (hG : h + 1 ≤ G.adicity) : yTw G H index h ≠ 0 := by
  have := twinPoint_standard_y_ne_zero hV h2 hh hG (cfft_permute_index (index / 2 ^ (H - h)) h)
  unfold yTw qPt
  split_ifs <;> simpa using this

theorem mem_heightsOf {lb : ℕ} {L : List (HMat K)} {h : ℕ} : h ∈ heightsOf lb L ↔ ∃ m ∈ L, hgt lb m = h := by
  rw [heightsOf, (List.mergeSort_perm _ _).mem_iff, (Plonky3Lean.Proofs.Fri.keysAfter_spec _ [] List.nodup_nil).2]
  simp

theorem heightsOf_bounds {lb H : ℕ} {L : List (HMat K)} (hlog : ∀ m ∈ L, 2 ≤ m.1.domain.log_n)
    (hH : ∀ m ∈ L, m.1.domain.log_n + lb ≤ H) {h : ℕ} (hh : h ∈ heightsOf lb L) : lb + 2 ≤ h ∧ h ≤ H := by
  obtain ⟨m, hm, rfl⟩ := mem_heightsOf.mp hh
  exact ⟨by have := hlog m hm; unfold hgt; omega, hH m hm⟩

/-- One query on honest openings.

Every height of the honest matrices gives one input to circle FRI: the folded DEEP function at the round's point.

The first-layer leaves are the corrected DEEP function at the query point and at its conjugate. -/
theorem reduceQuery_honest (hV : CircleGenValid G) (h2 : (2 : K) ≠ 0) (immcs : MmcsOps K) {FME : Type}
    {lb H M : ℕ} (α β : K) (index query : ℕ) (hlb : 1 ≤ lb) (hG : H + 1 ≤ G.adicity) (hi : index < 2 ^ H)
    {rounds : List (Claim K immcs.Commitment)} {io : List (BatchMultiOpening K immcs.MultiProof)}
    {hb : List (List (HMat K))} (hlen : io.length = rounds.length)
    (hcs : List.Forall₂ (fun c ms => c.matrices = ms.map Prod.fst) rounds hb)
    (hrows : List.Forall₂ (fun bo (ms : List (HMat K)) => bo.opened_values[query]? =
      some (ms.map fun m => m.2.map (· (qPt G H index (hgt lb m))))) io hb)
    (hok : ∀ ms ∈ hb, ∀ m ∈ ms, MatOK G lb H M index m) (hlog : ∀ m ∈ hb.flatten, 2 ≤ m.1.domain.log_n)
    (hon : ∀ h, HonestAt G lb hb.flatten h) {fls : List (List K)}
    (hfls : fls[query]? = some ((heightsOf lb hb.flatten).map fun h => corr G lb α hb.flatten h (-qPt G H index h)))
    {lambdas : List K} (hlam : lambdas = (heightsOf lb hb.flatten).map (lamAt G lb α hb.flatten)) :
    reduceQuery (FME := FME) G immcs lb H β ((List.range M).map (α ^ ·))
        (rounds.map fun c => c.matrices.map fun m => (α ^ claimedWidth m, (α ^ claimedWidth m) ^ 2))
        rounds io fls lambdas index query =
      pure (((heightsOf lb hb.flatten).map fun h => (h - 1, friVal G lb H α β hb.flatten h index)).reverse,
        (heightsOf lb hb.flatten).map (fun h => (2, 2 ^ (h - 1))),
        (heightsOf lb hb.flatten).map fun h => flVals G lb H α hb.flatten h index) := by
  set L := hb.flatten
  set hs := heightsOf lb L
  have hbd : ∀ h ∈ hs, lb + 2 ≤ h ∧ h ≤ H := fun h hh =>
    heightsOf_bounds hlog (fun m hm => by
      obtain ⟨ms, hms, hm'⟩ := List.mem_flatten.mp hm; exact (hok ms hms m hm').height) hh
  unfold reduceQuery
  simp only [hlen, ne_eq, not_true_eq_false, ↓reduceIte]
  rw [reduceBatches_honest hV h2 α index query hG hcs hrows hok, pure_bind]
  generalize hst : L.foldl (stepPure G lb H index α) (fun _ => (1, 0), []) = st
  obtain ⟨acc, keys⟩ := st
  have hacc : ∀ h, (acc h).2 = deepFnAt lb α L h (qPt G H index h) := fun h => by
    have := foldl_stepPure_fst (G := G) lb H index α h L (fun _ => (1, 0), [])
    rw [hst] at this; simp only at this; rw [this]; rfl
  have hkeys : keys.mergeSort (fun a b => decide (a ≤ b)) = hs := by
    have := foldl_stepPure_snd (G := G) lb H index α L (fun _ => (1, 0), [])
    rw [hst] at this; dsimp only at this; rw [this]; rfl
  dsimp only
  simp only [hkeys, hacc, hfls, lift_some_bind', List.length_map, hlam, not_true_eq_false, ↓reduceIte]
  rw [zip_map_map, zip_map_map]
  rw [mapM_eq_some_map (f := firstLayerLeaf G lb H index) _
    (fun e => (e.1.1.1, yTw G H index e.1.1.1, flVals G lb H α L e.1.1.1 index, (2, 2 ^ (e.1.1.1 - 1))))
    (fun e he => by
      obtain ⟨h, hh, rfl⟩ := List.mem_map.mp he
      rw [firstLayerLeaf_eq hV index hlb (by have := hbd h hh; omega) (hbd h hh).2 hG]
      rfl)]
  simp only [List.map_map, Function.comp_def, lift_some_bind']
  rw [batchInv_eq (fun y hy => by
    obtain ⟨h, hh, rfl⟩ := List.mem_map.mp hy
    exact yTw_ne_zero hV h2 index (by have := hbd h hh; omega) (by have := hbd h hh; omega))]
  simp only [lift_some_bind', List.map_map, Function.comp_def]
  rw [zip_map_map]
  rw [mapM_eq_some_map _ _ (fun e => (e.1.1 - 1, friVal G lb H α β L e.1.1 index)) (fun e he => by
      obtain ⟨h, hh, rfl⟩ := List.mem_map.mp he
      simp only
      rw [flVals_fold hV h2 α β hi hlb (hbd h hh).1 (hbd h hh).2 hG (hon h)]
      rfl)]
  simp only [lift_some_bind', List.map_map, Function.comp_def]

/-! ## The input checks on honest openings -/

/-- The dimensions one batch check passes to the scheme: each matrix's claimed width and LDE height. -/
def inDims {Com : Type} (lb : ℕ) (c : Claim K Com) : List (ℕ × ℕ) :=
  c.matrices.map fun m => (claimedWidth m, 2 ^ m.domain.log_n * 2 ^ lb)

/-- The indices one batch check passes to the scheme: each query index shifted down to the batch's tallest height. -/
def inReduced {Com : Type} (lb H : ℕ) (indices : List ℕ) (c : Claim K Com) : List ℕ :=
  match (c.matrices.map fun m => 2 ^ m.domain.log_n * 2 ^ lb).max? with
  | some h => indices.map (· / 2 ^ (H - Nat.log2 h))
  | none => indices.map fun _ => 0

/-- One batch's checks pass on an honest opening:

- one row per matrix in every opened row set
- every matrix opened at some point, below the tallest height
- a scheme that accepts the rows at the dimensions and indices the check computes. -/
theorem checkBatch_honest (immcs : MmcsOps K) {FME : Type} {lb H : ℕ} (indices : List ℕ)
    (bo : BatchMultiOpening K immcs.MultiProof) (c : Claim K immcs.Commitment)
    (hm : ∀ r ∈ bo.opened_values, r.length = c.matrices.length) (hp : ∀ m ∈ c.matrices, m.points ≠ [])
    (hh : ∀ m ∈ c.matrices, m.domain.log_n + lb ≤ H)
    (hmmcs : immcs.verify_multi_batch c.commitment (inDims lb c) (inReduced lb H indices c)
      bo.opened_values bo.opening_proof = .ok ()) :
    checkBatch (FME := FME) immcs lb H indices (bo, c) = pure () := by
  unfold checkBatch
  have h1 : (bo.opened_values.any fun x => decide (x.length ≠ c.matrices.length)) = false := by
    simp only [List.any_eq_false, ne_eq, decide_not, Bool.not_eq_true', decide_eq_false_iff_not, not_not]
    exact hm
  simp only [h1, Bool.false_eq_true, ↓reduceIte]
  rw [mapM_eq_pure_map (g := fun m => (claimedWidth m, 2 ^ m.domain.log_n * 2 ^ lb)) _ fun m hm' => by
    obtain ⟨p, ps, hps⟩ := List.exists_cons_of_ne_nil (hp m hm')
    simp only [hps, claimedWidth, List.headD_cons], pure_bind]
  have hfin : ∀ red, red = inReduced lb H indices c →
      (match immcs.verify_multi_batch c.commitment (c.matrices.map fun m => (claimedWidth m,
          2 ^ m.domain.log_n * 2 ^ lb)) red bo.opened_values bo.opening_proof with
        | .error e => throw (InputError.InputMmcsError e)
        | .ok () => pure () : IRes immcs.Error FME Unit) = pure () := by
    rintro red rfl
    split
    · rename_i e he
      exact absurd (he.symm.trans hmmcs) (by simp)
    · rfl
  split
  · next hmax =>
    rw [pure_bind]
    refine hfin _ ?_
    simp only [inReduced, hmax]
  · next h hmax =>
    obtain ⟨m, hm', rfl⟩ := List.mem_map.mp (List.max?_mem hmax)
    have hle : m.domain.log_n + lb ≤ H := hh m hm'
    have hp2 : 2 ^ m.domain.log_n * 2 ^ lb = 2 ^ (m.domain.log_n + lb) := (pow_add _ _ _).symm
    simp only [hp2, log2Strict_pow, lift_some_bind', show ¬ H < m.domain.log_n + lb by omega,
      ↓reduceIte, pure_bind]
    refine hfin _ ?_
    simp only [inReduced, hmax, hp2, Nat.log2_two_pow]

/-- Honest claims: per batch, the honest matrices behind it.

- the claims list the honest matrices' claims, batch by batch
- every domain has at least 4 rows, and its LDE lies at or below the tallest height H
- every matrix is opened at some point, on the circle and off its LDE domain
- the columns have degree below the trace size, and the claimed values are their evaluations. -/
structure HonestClaims (G : Gen (K × K)) (lb H : ℕ) {Com : Type} (rounds : List (Claim K Com))
    (hb : List (List (HMat K))) : Prop where
  shape : List.Forall₂ (fun c ms => c.matrices = ms.map Prod.fst) rounds hb
  log_n : ∀ m ∈ hb.flatten, 2 ≤ m.1.domain.log_n
  height : ∀ m ∈ hb.flatten, m.1.domain.log_n + lb ≤ H
  points_ne : ∀ m ∈ hb.flatten, m.1.points ≠ []
  cols : ∀ m ∈ hb.flatten, ∀ f ∈ m.2, IsCirclePoly (2 ^ (m.1.domain.log_n - 1)) f
  values : ∀ m ∈ hb.flatten, ∀ p ∈ m.1.points, p.values = m.2.map (· (ptOf p.point))
  on_circle : ∀ m ∈ hb.flatten, ∀ p ∈ m.1.points, 1 + p.point * p.point ≠ 0
  off_domain : ∀ m ∈ hb.flatten, ∀ p ∈ m.1.points, ∀ k < 2 ^ hgt lb m, ptOf p.point ≠ ptD G (hgt lb m) k

theorem HonestClaims.honestAt {lb H : ℕ} {Com : Type} {rounds : List (Claim K Com)} {hb : List (List (HMat K))}
    (hc : HonestClaims G lb H rounds hb) (h : ℕ) : HonestAt G lb hb.flatten h := by
  rintro m hm rfl
  refine ⟨⟨fun f hf => ?_, hc.values m hm⟩, hc.off_domain m hm⟩
  rw [show hgt lb m - lb - 1 = m.1.domain.log_n - 1 by unfold hgt; omega]
  exact hc.cols m hm f hf

theorem HonestClaims.matOK (hV : CircleGenValid G) {lb H M : ℕ} {Com : Type} {rounds : List (Claim K Com)}
    {hb : List (List (HMat K))} (hc : HonestClaims G lb H rounds hb) (hM : ∀ m ∈ hb.flatten, m.2.length ≤ M)
    (hG : H + 1 ≤ G.adicity) (index : ℕ) : ∀ ms ∈ hb, ∀ m ∈ ms, MatOK G lb H M index m := by
  intro ms hms m hm
  have hm' : m ∈ hb.flatten := List.mem_flatten.mpr ⟨ms, hms, hm⟩
  have hh := hc.height m hm'
  have hn := hc.log_n m hm'
  refine ⟨by omega, hh, hM m hm', hc.points_ne m hm', hc.values m hm', fun p hp => ⟨hc.on_circle m hm' p hp, ?_⟩⟩
  rw [qPt_eq hV index (by unfold hgt; omega) (by unfold hgt; omega)]
  exact hc.off_domain m hm' p hp _ (cfft_permute_index_lt _ _)

theorem forall₂_get {α β : Type _} {R : α → β → Prop} {l₁ : List α} {l₂ : List β} (h : List.Forall₂ R l₁ l₂)
    {i : ℕ} (h₁ : i < l₁.length) (h₂ : i < l₂.length) : R l₁[i] l₂[i] :=
  (List.forall₂_iff_get.mp h).2 i h₁ h₂

theorem map_zipIdx_fst {α γ : Type _} (F : α → γ) (l : List α) : l.zipIdx.map (fun e => F e.1) = l.map F := by
  rw [show (fun e : α × ℕ => F e.1) = F ∘ Prod.fst from rfl, ← List.map_map, List.zipIdx_map_fst]

/-- The input checks accept honest openings.

Each query index i gives the inputs circle FRI rolls in: at every height h, tallest first, the folded DEEP
function at the round's point.

The openings are honest:

- every batch opens, at each query, the columns of its matrices at the query point of their height
- the first-layer siblings are the corrected DEEP functions at the conjugate points
- the lambdas are what the prover extracts
- both commitment schemes accept the honest rows. -/
theorem open_inputs_honest (hV : CircleGenValid G) (h2 : (2 : K) ≠ 0) (immcs fmmcs : MmcsOps K) {lb H M : ℕ}
    (α β : K) (hlb : 1 ≤ lb) (hG : H + 1 ≤ G.adicity) {rounds : List (Claim K immcs.Commitment)}
    {hb : List (List (HMat K))} (hc : HonestClaims G lb H rounds hb) (hM : ∀ m ∈ hb.flatten, m.2.length ≤ M)
    (flc : fmmcs.Commitment) {lambdas : List K} (hlam : lambdas = (heightsOf lb hb.flatten).map (lamAt G lb α hb.flatten))
    {indices : List ℕ} (hidx : ∀ i ∈ indices, i < 2 ^ H)
    (ip : CircleInputProof K immcs.MultiProof fmmcs.MultiProof)
    (hio : List.Forall₂ (fun bo (ms : List (HMat K)) => bo.opened_values =
      indices.map fun i => ms.map fun m => m.2.map (· (qPt G H i (hgt lb m)))) ip.input_openings hb)
    (hin : ∀ bc ∈ ip.input_openings.zip rounds, immcs.verify_multi_batch bc.2.commitment (inDims lb bc.2)
      (inReduced lb H indices bc.2) bc.1.opened_values bc.1.opening_proof = .ok ())
    (hfls : ip.first_layer_siblings = indices.map fun i =>
      (heightsOf lb hb.flatten).map fun h => corr G lb α hb.flatten h (-qPt G H i h))
    (hfl : fmmcs.verify_multi_batch flc (if indices = [] then [] else
        (heightsOf lb hb.flatten).map fun h => (2, 2 ^ (h - 1))) (indices.map (· / 2))
      (indices.map fun i => (heightsOf lb hb.flatten).map fun h => flVals G lb H α hb.flatten h i)
      ip.first_layer_proof = .ok ()) :
    open_inputs G immcs fmmcs lb H rounds flc lambdas β ((List.range M).map (α ^ ·))
        (rounds.map fun c => c.matrices.map fun m => (α ^ claimedWidth m, (α ^ claimedWidth m) ^ 2)) indices ip =
      pure (indices.map fun i =>
        ((heightsOf lb hb.flatten).map fun h => (h - 1, friVal G lb H α β hb.flatten h i)).reverse) := by
  obtain ⟨io, fls, flp⟩ := ip
  dsimp only at hio hin hfls hfl
  set L := hb.flatten
  set hs := heightsOf lb L
  have hlen : io.length = rounds.length := hio.length_eq.trans hc.shape.length_eq.symm
  have hrowlen : ∀ bo ∈ io, bo.opened_values.length = indices.length := fun bo hbo => by
    obtain ⟨ms, -, hbm⟩ := forall₂_mem_right hio.flip bo hbo
    rw [hbm, List.length_map]
  have hok := hc.matOK hV hM hG
  unfold open_inputs
  simp only [hfls, List.length_map, ne_eq, not_true_eq_false, ↓reduceIte, hlen]
  have hany : (io.any fun bo => decide (bo.opened_values.length ≠ indices.length)) = false := by
    simpa using hrowlen
  simp only [hany, Bool.false_eq_true, ↓reduceIte]
  rw [Plonky3Lean.Proofs.Fri.forM_eq_pure _ fun bc hbc => ?_, pure_bind]
  swap
  · obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hbc
    have hk1 : k < io.length := by simp at hk; omega
    have hk2 : k < hb.length := by rw [← hio.length_eq]; exact hk1
    have hk3 : k < rounds.length := by rw [← hlen]; exact hk1
    have hcm := forall₂_get hc.shape hk3 hk2
    have hrow := forall₂_get hio hk1 hk2
    simp only [List.getElem_zip]
    refine checkBatch_honest immcs indices _ _ (fun r hr => ?_) (fun m hm => ?_) (fun m hm => ?_)
      (by simpa using hin _ (List.getElem_mem hk))
    · rw [hrow] at hr
      obtain ⟨i, -, rfl⟩ := List.mem_map.mp hr
      rw [hcm, List.length_map, List.length_map]
    · rw [hcm] at hm
      obtain ⟨m', hm', rfl⟩ := List.mem_map.mp hm
      exact hc.points_ne m' (List.mem_flatten.mpr ⟨_, List.getElem_mem hk2, hm'⟩)
    · rw [hcm] at hm
      obtain ⟨m', hm', rfl⟩ := List.mem_map.mp hm
      exact hc.height m' (List.mem_flatten.mpr ⟨_, List.getElem_mem hk2, hm'⟩)
  rw [mapM_eq_pure_map (g := fun e : ℕ × ℕ => ((hs.map fun h => (h - 1, friVal G lb H α β L h e.1)).reverse,
      hs.map (fun h => (2, 2 ^ (h - 1))), hs.map fun h => flVals G lb H α L h e.1)) _ fun e he => ?_, pure_bind]
  swap
  · obtain ⟨hq, hqe⟩ := List.mem_zipIdx' he
    have hget : ∀ {β : Type} (F : ℕ → β), (indices.map F)[e.2]? = some (F e.1) := fun F => by
      rw [List.getElem?_map, List.getElem?_eq_getElem hq, ← hqe]; rfl
    refine reduceQuery_honest hV h2 immcs α β e.1 e.2 hlb hG (hidx _ (hqe ▸ List.getElem_mem hq)) hlen hc.shape
      (hio.imp fun bo ms hbm => by rw [hbm, hget]) (hok e.1) hc.log_n hc.honestAt (hget _) hlam
  have hdims : ((Option.map (fun x => x.2.1) (indices.zipIdx.map fun e : ℕ × ℕ =>
      ((hs.map fun h => (h - 1, friVal G lb H α β L h e.1)).reverse, hs.map (fun h => (2, 2 ^ (h - 1))),
        hs.map fun h => flVals G lb H α L h e.1)).head?).getD []) =
      if indices = [] then [] else hs.map fun h => (2, 2 ^ (h - 1)) := by
    cases indices <;> simp
  rw [hdims, List.map_map, List.map_map]
  simp only [Function.comp_def]
  rw [map_zipIdx_fst (fun i => hs.map fun h => flVals G lb H α L h i),
    map_zipIdx_fst (fun i => (hs.map fun h => (h - 1, friVal G lb H α β L h i)).reverse), hfl]

end Plonky3Lean.Proofs.Circle
