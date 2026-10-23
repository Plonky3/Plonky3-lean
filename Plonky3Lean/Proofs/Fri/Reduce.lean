module

public import Plonky3Lean.Proofs.Fri.Res
public import Plonky3Lean.Spec.Fri
public import P3Fri.Pcs
public import Plonky3Lean.Proofs.Dft.Glue
public import Plonky3Lean.Proofs.Commit.Coset
public import Plonky3Lean.Proofs.Matrix.BitRev
public import Plonky3Lean.Proofs.Dft.Network

@[expose] public section

/-!
# The reduced openings

The verifier's reduction of one query, and the prover's reduced vectors, both compute the reduced opening of the claims at each height.

Their ladders of powers of alpha agree: a claim starts at the number of claimed values before it at its height.
-/

namespace Plonky3Lean.Proofs.Fri

open Finset Plonky3Lean.Spec.Fri p3_fri.verifier.mirror p3_fri.two_adic_pcs.mirror p3_dft.mirror
open p3_commit.pcs.univariate.mirror

set_option linter.unusedSectionVars false

variable {K : Type} [Field K] [DecidableEq K]

/-- One claim at a height: its height, its point, its values, and the column values at the query point. -/
abbrev Entry (K : Type) := ℕ × K × List K × List K

/-- The term of one claim at ladder position off. -/
def entryTerm (α x : K) (off : ℕ) (e : Entry K) : K :=
  (∑ i ∈ range e.2.2.1.length, α ^ (off + i) * (e.2.2.1.getD i 0 - e.2.2.2.getD i 0)) / (e.2.1 - x)

/-- The running sums and ladder counters per height. -/
def ladderStep (α : K) (xOf : ℕ → K) (st : (ℕ → K) × (ℕ → ℕ)) (e : Entry K) : (ℕ → K) × (ℕ → ℕ) :=
  (Function.update st.1 e.1 (st.1 e.1 + entryTerm α (xOf e.1) (st.2 e.1) e),
    Function.update st.2 e.1 (st.2 e.1 + e.2.2.1.length))

theorem reducedOpening_cons (α x : K) (off : ℕ) (e : K × List K × List K) (L : List (K × List K × List K)) :
    reducedOpening α x off (e :: L) = entryTerm α x off (0, e) + reducedOpening α x (off + e.2.1.length) L := by
  rfl

/-- Running the per-height sums over a list of claims gives, at each height, the reduced opening of the claims at that height. -/
theorem foldl_ladderStep (α : K) (xOf : ℕ → K) : ∀ (E : List (Entry K)) (acc : ℕ → K) (cnt : ℕ → ℕ) (h : ℕ),
    (E.foldl (ladderStep α xOf) (acc, cnt)).1 h =
      acc h + reducedOpening α (xOf h) (cnt h) ((E.filter (·.1 = h)).map (·.2))
  | [], acc, cnt, h => by simp [reducedOpening]
  | e :: E, acc, cnt, h => by
    rw [List.foldl_cons, ladderStep, foldl_ladderStep α xOf E]
    by_cases he : e.1 = h
    · subst he
      simp only [Function.update_self, List.filter_cons, decide_true, ↓reduceIte, List.map_cons]
      rw [reducedOpening_cons, add_assoc]
      rfl
    · have : decide (e.1 = h) = false := by simp [he]
      simp only [Function.update_of_ne (Ne.symm he), List.filter_cons, this, Bool.false_eq_true,
        ↓reduceIte]

/-- The ladder starts of a list of points, from counters cnt. -/
def ladderFrom : (ℕ → ℕ) → List (ℕ × PointOpening K) → List ℕ
  | _, [] => []
  | cnt, e :: l => cnt e.1 :: ladderFrom (Function.update cnt e.1 (cnt e.1 + e.2.values.length)) l

theorem foldl_ladderOffsets (pts : List (ℕ × PointOpening K)) (cnt : ℕ → ℕ) (out : List ℕ) :
    (pts.foldl (fun (st : (ℕ → ℕ) × List ℕ) e =>
      (Function.update st.1 e.1 (st.1 e.1 + e.2.values.length), st.2 ++ [st.1 e.1])) (cnt, out)).2 =
      out ++ ladderFrom cnt pts := by
  induction pts generalizing cnt out with
  | nil => simp [ladderFrom]
  | cons e pts ih => simp [ih, ladderFrom]

theorem ladderOffsets_eq (pts : List (ℕ × PointOpening K)) : ladderOffsets pts = ladderFrom (fun _ => 0) pts := by
  rw [ladderOffsets]; simpa using foldl_ladderOffsets pts (fun _ => 0) []

theorem sum_map_range {M : Type _} [AddCommMonoid M] (f : ℕ → M) (n : ℕ) :
    ((List.range n).map f).sum = ∑ i ∈ range n, f i := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]; simp

/-- The claims of one matrix with its opened row. -/
def matEntries (h : ℕ) (row : List K) (pts : List (PointOpening K)) : List (Entry K) :=
  pts.map fun p => (h, p.point, p.values, row)

theorem pointTerm_eq {α x : K} {off : ℕ} {p : PointOpening K} {row : List K}
    (hl : row.length = p.values.length) :
    pointTerm α x off p row = entryTerm α x off (0, p.point, p.values, row) := by
  simp only [pointTerm, entryTerm, hl, div_eq_mul_inv, sum_map_range, ← Finset.sum_sub_distrib, mul_sub]

/-- The query point of every height. -/
def xOfQuery (G : Gen K) (g : K) (H index : ℕ) (h : ℕ) : K :=
  (queryPoint G g H h index).getD 0

/-- One matrix of the verifier's reduction adds its claims' terms at its height, reading the ladder starts in order. -/
theorem reduceMatrix_spec {ME IE : Type} (G : Gen K) (g : K) (b H : ℕ) (α : K) (index : ℕ)
    (acc : ℕ → K) (keys : List ℕ) (cnt : ℕ → ℕ) (rest : List ℕ)
    (m : MatrixOpening K (p3_field.coset.mirror.TwoAdicMultiplicativeCoset K G.adicity G.gen))
    (row : List K) (res : RedState K)
    (h : reduceMatrix (ME := ME) (IE := IE) G g b H α index
      (acc, keys, ladderFrom cnt (m.points.map fun p => (m.domain.log_size + b, p)) ++ rest) (m, row) =
        pure res) :
    res.1 = ((matEntries (m.domain.log_size + b) row m.points).foldl
      (ladderStep α (xOfQuery G g H index)) (acc, cnt)).1 ∧ res.2.2 = rest := by
  unfold reduceMatrix at h
  dsimp only at h
  rcases hq : queryPoint G g H (m.domain.log_size + b) index with _ | x
  · rw [hq] at h; simp only [lift, lift_none_bind] at h; exact absurd h (lift_none_ne_pure _)
  rw [hq] at h
  simp only [lift, lift_some_bind] at h
  rw [bind_eq_pure] at h
  obtain ⟨⟨acc', offs'⟩, hfold, hres⟩ := h
  obtain rfl := (pure_inj hres).symm
  have hx : xOfQuery G g H index (m.domain.log_size + b) = x := by simp [xOfQuery, hq]
  simp only
  generalize m.points = pts at hfold ⊢
  induction pts generalizing acc cnt with
  | nil =>
    simp only [List.foldlM_nil, List.map_nil, ladderFrom, List.nil_append] at hfold
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (pure_inj hfold).symm
    simp [matEntries]
  | cons p pts ih =>
    rw [foldlM_cons_eq_pure] at hfold
    obtain ⟨⟨acc2, offs2⟩, hstep, hrest⟩ := hfold
    by_cases hl : row.length ≠ p.values.length
    · simp [hl] at hstep
    by_cases hz : p.point - x = 0
    · simp [hl, hz] at hstep
    simp only [hl, hz, ↓reduceIte] at hstep
    push Not at hl
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (pure_inj hstep).symm
    simp only [List.map_cons, ladderFrom, List.cons_append, List.headD_cons, List.drop_succ_cons,
      List.drop_zero] at hrest
    have := ih _ _ hrest
    simp only [matEntries, List.map_cons, List.foldl_cons] at this ⊢
    have hstepEq : ladderStep α (xOfQuery G g H index) (acc, cnt)
        (m.domain.log_size + b, p.point, p.values, row) =
        (Function.update acc (m.domain.log_size + b)
          (acc (m.domain.log_size + b) + pointTerm α x (cnt (m.domain.log_size + b)) p row),
         Function.update cnt (m.domain.log_size + b) (cnt (m.domain.log_size + b) + p.values.length)) := by
      simp only [ladderStep, hx, pointTerm_eq hl]
      rfl
    rw [hstepEq]; exact this


/-- The ladder counters after a list of points. -/
def cntAfter (cnt : ℕ → ℕ) (l : List (ℕ × PointOpening K)) : ℕ → ℕ :=
  l.foldl (fun c e => Function.update c e.1 (c e.1 + e.2.values.length)) cnt

theorem ladderFrom_append (cnt : ℕ → ℕ) (l1 l2 : List (ℕ × PointOpening K)) :
    ladderFrom cnt (l1 ++ l2) = ladderFrom cnt l1 ++ ladderFrom (cntAfter cnt l1) l2 := by
  induction l1 generalizing cnt with
  | nil => simp [ladderFrom, cntAfter]
  | cons e l1 ih => simp [ladderFrom, ih, cntAfter]

theorem foldl_ladderStep_snd (α : K) (xOf : ℕ → K) (h : ℕ) (row : List K) (pts : List (PointOpening K))
    (acc : ℕ → K) (cnt : ℕ → ℕ) :
    ((matEntries h row pts).foldl (ladderStep α xOf) (acc, cnt)).2 = cntAfter cnt (pts.map fun p => (h, p)) := by
  induction pts generalizing acc cnt with
  | nil => simp [matEntries, cntAfter]
  | cons p pts ih =>
    simp only [matEntries, List.map_cons, List.foldl_cons] at ih ⊢
    rw [ih]; rfl

/-- The matrices of one query with their opened rows, as claims, and as points with their heights. -/
def matsEntries (b : ℕ) {G : Gen K}
    (mats : List (MatrixOpening K (p3_field.coset.mirror.TwoAdicMultiplicativeCoset K G.adicity G.gen) × List K)) :
    List (Entry K) :=
  mats.flatMap fun mr => matEntries (mr.1.domain.log_size + b) mr.2 mr.1.points

def matsPoints (b : ℕ) {G : Gen K}
    (mats : List (MatrixOpening K (p3_field.coset.mirror.TwoAdicMultiplicativeCoset K G.adicity G.gen) × List K)) :
    List (ℕ × PointOpening K) :=
  mats.flatMap fun mr => mr.1.points.map fun p => (mr.1.domain.log_size + b, p)

theorem reduceMatrices_spec {ME IE : Type} (G : Gen K) (g : K) (b H : ℕ) (α : K) (index : ℕ) :
    ∀ (mats : List (MatrixOpening K (p3_field.coset.mirror.TwoAdicMultiplicativeCoset K G.adicity G.gen) × List K))
      (acc : ℕ → K) (keys : List ℕ) (cnt : ℕ → ℕ) (rest : List ℕ) (res : RedState K),
      mats.foldlM (reduceMatrix (ME := ME) (IE := IE) G g b H α index)
          (acc, keys, ladderFrom cnt (matsPoints b mats) ++ rest) = pure res →
      res.1 = ((matsEntries b mats).foldl (ladderStep α (xOfQuery G g H index)) (acc, cnt)).1
  | [], acc, keys, cnt, rest, res, h => by
    simp only [List.foldlM_nil] at h
    rw [← pure_inj h]; simp [matsEntries]
  | mr :: mats, acc, keys, cnt, rest, res, h => by
    rw [foldlM_cons_eq_pure] at h
    obtain ⟨st, hst, hrest⟩ := h
    obtain ⟨acc', keys', offs'⟩ := st
    simp only [matsPoints, List.flatMap_cons] at hst
    rw [ladderFrom_append, List.append_assoc] at hst
    obtain ⟨h1, h2⟩ := reduceMatrix_spec G g b H α index acc keys cnt _ mr.1 mr.2 _ hst
    simp only at h1 h2
    subst h1 h2
    have := reduceMatrices_spec G g b H α index mats _ keys' _ rest res (by simpa [matsPoints] using hrest)
    rw [this]
    simp only [matsEntries, List.flatMap_cons, List.foldl_append]
    congr 2
    exact Prod.ext rfl (foldl_ladderStep_snd _ _ _ _ _ _ _).symm

/-- The matrices of the claims paired with the opened rows of one query. -/
def queryMats {G : Gen K} {C : Type} (claims : List (Claim G C)) (rows : List (List (List K))) :
    List (MatrixOpening K (p3_field.coset.mirror.TwoAdicMultiplicativeCoset K G.adicity G.gen) × List K) :=
  (claims.zip rows).flatMap fun cr => cr.1.matrices.zip cr.2

theorem matsPoints_queryMats {G : Gen K} {C : Type} (b : ℕ) {claims : List (Claim G C)}
    {rows : List (List (List K))} (h : List.Forall₂ (fun c r => r.length = c.matrices.length) claims rows) :
    matsPoints b (queryMats claims rows) = openingPoints b claims := by
  induction h with
  | nil => simp [queryMats, matsPoints, openingPoints]
  | cons hcr _ ih =>
    rename_i c r cs rs
    simp only [queryMats, matsPoints, openingPoints, List.zip_cons_cons, List.flatMap_cons,
      List.flatMap_append] at ih ⊢
    rw [ih]
    congr 1
    have : ∀ (ms : List (MatrixOpening K (p3_field.coset.mirror.TwoAdicMultiplicativeCoset K G.adicity G.gen)))
        (rb : List (List K)), rb.length = ms.length →
        (ms.zip rb).flatMap (fun mr => mr.1.points.map fun p => (mr.1.domain.log_size + b, p)) =
          ms.flatMap fun m => m.points.map fun p => (m.domain.log_size + b, p) := by
      intro ms rb hl
      induction ms generalizing rb with
      | nil => simp
      | cons m ms ihm =>
        rcases rb with _ | ⟨x, rb⟩
        · simp at hl
        · simp only [List.zip_cons_cons, List.flatMap_cons, ihm rb (by simpa using hl)]
    exact this _ _ hcr

/-- The verifier's reduction of one query: at each height present, the reduced opening of the claims at that height, with the opened rows as column values and the query point of that height. -/
theorem reduceQuery_spec {ME IE : Type} (G : Gen K) (g : K) {C : Type} (b H : ℕ) (α : K)
    (claims : List (Claim G C)) (rows : List (List (List K))) (index : ℕ) (ro : List (ℕ × K))
    (halign : List.Forall₂ (fun c r => r.length = c.matrices.length) claims rows)
    (h : reduceQuery (ME := ME) (IE := IE) G g b H α claims rows index = pure ro) :
    ∀ e ∈ ro, e.2 = reducedOpening α (xOfQuery G g H index e.1) 0
      (((matsEntries b (queryMats claims rows)).filter (·.1 = e.1)).map (·.2)) := by
  unfold reduceQuery at h
  rw [bind_eq_pure] at h
  obtain ⟨⟨acc, keys, offs⟩, hfold, hres⟩ := h
  have hfold' := hfold
  rw [ladderOffsets_eq, ← matsPoints_queryMats b halign, ← List.append_nil (ladderFrom _ _)] at hfold'
  have hacc := reduceMatrices_spec G g b H α index _ _ _ _ _ _ hfold'
  simp only at hacc
  by_cases hb : b ∈ keys ∧ acc b ≠ 0
  · simp [hb] at hres
  simp only [hb, ↓reduceIte] at hres
  rw [← pure_inj hres]
  intro e he
  obtain ⟨k, -, rfl⟩ := List.mem_map.1 he
  simp only
  rw [hacc, foldl_ladderStep]
  simp

/-! ## The prover's reduced vectors -/

/-- Row r of a matrix, as a list. -/
def matRow (M : Mat K) (r : ℕ) : List K := (List.finRange M.width).map (M.entry r)

/-- One point of the prover: the weighted claimed values less the rescaled compressed row, over z - x, is the claim's term at the ladder position. -/
theorem proverTerm_eq (α x z : K) (num k : ℕ) (M : Mat K) (r : ℕ) (ys : List K)
    (hys : ys.length = M.width) :
    (α ^ (num + k * M.width) * ((List.range ys.length).map fun i => α ^ i * ys.getD i 0).sum -
        (if k = 0 then 1 else α ^ (k * M.width)) *
          ((List.finRange M.width).map fun c => α ^ c.val * α ^ num * M.entry r c).sum) * (z - x)⁻¹ =
      entryTerm α x (num + k * M.width) (0, z, ys, matRow M r) := by
  have hr : (if k = 0 then (1 : K) else α ^ (k * M.width)) = α ^ (k * M.width) := by
    split_ifs with hk <;> simp [hk]
  rw [hr, entryTerm, div_eq_mul_inv]
  congr 1
  have hrow : ∀ i (hi : i < M.width), (matRow M r).getD i 0 = M.entry r ⟨i, hi⟩ := by
    intro i hi; simp [matRow, List.getD_eq_getElem?_getD, hi]
  have h2 : ((List.finRange M.width).map fun c => α ^ c.val * α ^ num * M.entry r c).sum =
      ∑ i ∈ range M.width, α ^ i * α ^ num * (matRow M r).getD i 0 := by
    rw [← Fin.sum_univ_def, Finset.sum_range]
    exact Finset.sum_congr rfl fun i _ => by rw [hrow i i.2]
  rw [sum_map_range, hys, h2, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only
  ring

/-- The claims of one matrix of the prover at row r. -/
def proverEntries (m : MatToOpen K) (r : ℕ) : List (K × List K × List K) :=
  (m.points.zip m.openings).map fun zy => (zy.1, zy.2, matRow m.mat r)


theorem getD_map_range {α : Type _} [Zero α] (f : ℕ → α) {n r : ℕ} (hr : r < n) :
    ((List.range n).map f).getD r 0 = f r := by
  rw [List.getD_eq_getElem _ _ (by simpa using hr)]; simp

/-- The points of one matrix of the prover, from ladder position num lh + k0 w: each row gains the reduced opening of the claims left. -/
theorem foldlM_reducePoint (α : K) (inv_denoms : K → Option (List K)) (m : MatToOpen K) {lh : ℕ}
    (hlh : m.mat.height = 2 ^ lh) (xr : ℕ → K) (num : ℕ → ℕ) :
    ∀ (l : List (K × List K)) (k0 : ℕ) (num2 : ℕ → ℕ) (ro1 : List K) (res : (ℕ → ℕ) × List K),
      (∀ zy ∈ l, zy.2.length = m.mat.width) →
      (∀ zy ∈ l, ∃ inv, inv_denoms zy.1 = some inv ∧ ∀ r < 2 ^ lh, inv.getD r 0 = (zy.1 - xr r)⁻¹) →
      num2 lh = num lh + k0 * m.mat.width → ro1.length = 2 ^ lh →
      (l.zipIdx k0).foldlM (reducePoint α inv_denoms lh m.mat.width ((List.range m.mat.height).map fun r =>
        ((List.finRange m.mat.width).map fun c => α ^ c.val * α ^ num lh * m.mat.entry r c).sum))
        (num2, ro1) = some res →
      res.1 = Function.update num2 lh (num2 lh + l.length * m.mat.width) ∧ res.2.length = 2 ^ lh ∧
        ∀ r < 2 ^ lh, res.2.getD r 0 = ro1.getD r 0 +
          reducedOpening α (xr r) (num2 lh) (l.map fun zy => (zy.1, zy.2, matRow m.mat r))
  | [], k0, num2, ro1, res, _, _, _, hl, h => by
    simp only [List.zipIdx_nil, List.foldlM_nil, Option.pure_def, Option.some.injEq] at h
    subst h
    refine ⟨by simp, hl, fun r _ => by simp [reducedOpening]⟩
  | zy :: l, k0, num2, ro1, res, hw, hinv, hnum, hl, h => by
    rw [List.zipIdx_cons, List.foldlM_cons] at h
    obtain ⟨st, hst, hrest⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨inv, hinvz, hinvr⟩ := hinv zy List.mem_cons_self
    simp only [reducePoint, hinvz, Option.bind_eq_bind, Option.bind_some, Option.some.injEq] at hst
    subst hst
    have hw0 := hw zy List.mem_cons_self
    obtain ⟨h1, h2, h3⟩ := foldlM_reducePoint α inv_denoms m hlh xr num l (k0 + 1) _ _ res
      (fun x hx => hw x (List.mem_cons_of_mem _ hx)) (fun x hx => hinv x (List.mem_cons_of_mem _ hx))
      (by simp [hnum]; ring) (by simp [hl]) hrest
    refine ⟨?_, h2, fun r hr => ?_⟩
    · rw [h1, Function.update_idem, Function.update_self, List.length_cons]
      congr 1; ring
    · rw [h3 r hr]
      simp only [Function.update_self, List.map_cons, reducedOpening]
      rw [getD_map_range _ (by rw [hl]; exact hr), hinvr r hr, getD_map_range _ (by rw [hlh]; exact hr),
        hnum]
      rw [proverTerm_eq α (xr r) zy.1 (num lh) k0 m.mat r zy.2 hw0, entryTerm]
      simp only [div_eq_mul_inv, add_assoc, hw0]

/-- One matrix of the prover: at its height, each row gains the reduced opening of its claims at that row's point, from the ladder position reached so far. -/
theorem reduceMat_spec (α : K) (inv_denoms : K → Option (List K)) (m : MatToOpen K) {lh : ℕ}
    (hlh : m.mat.height = 2 ^ lh) (h32 : lh ≤ 32)
    (hw : ∀ zy ∈ m.points.zip m.openings, zy.2.length = m.mat.width) (xr : ℕ → K)
    (hinv : ∀ zy ∈ m.points.zip m.openings, ∃ inv, inv_denoms zy.1 = some inv ∧
      ∀ r < 2 ^ lh, inv.getD r 0 = (zy.1 - xr r)⁻¹)
    (num : ℕ → ℕ) (red : ℕ → Option (List K)) (hred : ∀ v, red lh = some v → v.length = 2 ^ lh)
    (st' : PcsRedState K) (h : reduceMat α inv_denoms (num, red) m = some st') :
    st'.1 = Function.update num lh (num lh + (m.points.zip m.openings).length * m.mat.width) ∧
      (∀ h' ≠ lh, st'.2 h' = red h') ∧
      ∃ v, st'.2 lh = some v ∧ v.length = 2 ^ lh ∧ ∀ r < 2 ^ lh,
        v.getD r 0 = ((red lh).getD ((List.range (2 ^ lh)).map fun _ => 0)).getD r 0 +
          reducedOpening α (xr r) (num lh) (proverEntries m r) := by
  unfold reduceMat at h
  dsimp only at h
  rw [show log2Strict m.mat.height = some lh by rw [hlh, Plonky3Lean.Proofs.Dft.log2Strict_pow]] at h
  simp only [Option.bind_eq_bind, Option.bind_some, show ¬ 32 < lh by omega, ↓reduceIte] at h
  obtain ⟨⟨num', ro⟩, hfold, hres⟩ := Option.bind_eq_some_iff.1 h
  obtain rfl := (Option.some.inj hres).symm
  have hro0l : ((red lh).getD ((List.range m.mat.height).map fun _ => 0)).length = 2 ^ lh := by
    rcases hr : red lh with _ | v
    · simp [hlh]
    · simp [hred v hr]
  obtain ⟨h1, h2, h3⟩ := foldlM_reducePoint α inv_denoms m hlh xr num _ 0 num _ _ hw hinv (by simp) hro0l
    hfold
  refine ⟨h1, fun h' hh => by simp [Function.update_of_ne hh], ro, by simp, h2, fun r hr => ?_⟩
  rw [h3 r hr, hlh]
  rfl

/-- Every claim of the prover at the row of the query index idx, with its matrix's log height. -/
def proverAllEntries (H idx : ℕ) (mats : List (MatToOpen K)) : List (Entry K) :=
  mats.flatMap fun m => (proverEntries m (idx / 2 ^ (H - Nat.log 2 m.mat.height))).map
    fun e => (Nat.log 2 m.mat.height, e)

/-- Claims all at one height run the ladder at that height only. -/
theorem foldl_ladderStep_same (α : K) (xOf : ℕ → K) (lh : ℕ) :
    ∀ (L : List (K × List K × List K)) (acc : ℕ → K) (cnt : ℕ → ℕ),
      (L.map fun e => (lh, e)).foldl (ladderStep α xOf) (acc, cnt) =
        (Function.update acc lh (acc lh + reducedOpening α (xOf lh) (cnt lh) L),
          Function.update cnt lh (cnt lh + (L.map fun e => e.2.1.length).sum))
  | [], acc, cnt => by simp [reducedOpening]
  | e :: L, acc, cnt => by
    simp only [List.map_cons, List.foldl_cons, ladderStep]
    rw [foldl_ladderStep_same α xOf lh L]
    simp only [Function.update_self, Function.update_idem, reducedOpening_cons, List.sum_cons, entryTerm]
    refine Prod.ext ?_ ?_
    · simp only; congr 1; ring
    · simp only; congr 1; ring

theorem foldl_max_ge : ∀ (l : List ℕ) (a x : ℕ), x ∈ l → x ≤ l.foldl max a
  | [], _, _, h => absurd h (by simp)
  | y :: l, a, x, h => by
    rcases List.mem_cons.1 h with rfl | h
    · exact le_trans (le_max_right a x) (foldl_max_init l _)
    · exact foldl_max_ge l _ x h
where foldl_max_init : ∀ (l : List ℕ) (b : ℕ), b ≤ l.foldl max b
  | [], _ => le_rfl
  | y :: l, b => le_trans (le_max_left b y) (foldl_max_init l _)

theorem foldl_max_le : ∀ (l : List ℕ) (a H : ℕ), (∀ x ∈ l, x ≤ H) → a ≤ H → l.foldl max a ≤ H
  | [], _, _, _, ha => ha
  | y :: l, _, H, h, ha => foldl_max_le l _ H (fun x hx => h x (List.mem_cons_of_mem _ hx))
      (max_le ha (h y List.mem_cons_self))

/-- The point of row r of a matrix of log height lh on the bit-reversed coset g H: g G_lh^rev_lh(r). -/
def rowPoint (G : Gen K) (g : K) (lh r : ℕ) : K := g * G.gen lh ^ bitRev lh r

/-- The prefix of the bit-reversed coset of order 2^H holds the bit-reversed coset of order 2^lh. -/
theorem bitrevCoset_getD (G : Gen K) (hN : Plonky3Lean.Proofs.Dft.GenNested G) (g : K) {H lh r : ℕ}
    (hHa : H ≤ G.adicity) (hlh : lh ≤ H) (hr : r < 2 ^ lh) {coset : List K}
    (hc : bitrevCoset G g H = some coset) : coset.getD r 0 = rowPoint G g lh r := by
  simp only [bitrevCoset, Plonky3Lean.Proofs.Dft.gen_get_of_le G hHa, Option.bind_eq_bind,
    Option.bind_some, Option.some.injEq] at hc
  subst hc
  have hrH : r < 2 ^ H := lt_of_lt_of_le hr (Nat.pow_le_pow_right (by norm_num) hlh)
  rw [getD_map_range _ hrH, rowPoint, Plonky3Lean.Proofs.Dft.bitRev_eq,
    show H = lh + (H - lh) by omega, Plonky3Lean.Proofs.Matrix.bitRev_add_of_lt hr,
    ← Plonky3Lean.Proofs.Dft.bitRev_eq, mul_comm (bitRev lh r), pow_mul,
    ← Plonky3Lean.Proofs.Commit.gen_sub G hN (show lh + (H - lh) ≤ G.adicity by omega) (by omega),
    show lh + (H - lh) - (H - lh) = lh by omega]

/-- The inverse denominators of a point opened in a matrix of log height lh: 1 / (z - x) at the first 2^lh coset points. -/
theorem compute_inverse_denominators_spec (G : Gen K) (hN : Plonky3Lean.Proofs.Dft.GenNested G) (g : K)
    {H : ℕ} (hHa : H ≤ G.adicity) (mats : List (MatToOpen K))
    (hH : ∀ m ∈ mats, Nat.log 2 m.mat.height ≤ H) {coset : List K}
    (hc : bitrevCoset G g H = some coset) {m : MatToOpen K} (hm : m ∈ mats) {z : K} (hz : z ∈ m.points)
    (hout : ∀ r < 2 ^ H, z ≠ coset.getD r 0) :
    ∃ inv, compute_inverse_denominators mats coset z = some inv ∧
      ∀ r < 2 ^ Nat.log 2 m.mat.height, inv.getD r 0 = (z - rowPoint G g (Nat.log 2 m.mat.height) r)⁻¹ := by
  have hlen : coset.length = 2 ^ H := by
    simp only [bitrevCoset, Plonky3Lean.Proofs.Dft.gen_get_of_le G hHa, Option.bind_eq_bind,
      Option.bind_some, Option.some.injEq] at hc
    subst hc; simp
  set hs := (mats.filter fun m => z ∈ m.points).map fun m => Nat.log 2 m.mat.height with hhs
  have hge : Nat.log 2 m.mat.height ≤ hs.foldl max 0 :=
    foldl_max_ge _ _ _ (List.mem_map.2 ⟨m, List.mem_filter.2 ⟨hm, by simpa using hz⟩, rfl⟩)
  have hle : hs.foldl max 0 ≤ H := foldl_max_le _ _ _ (by
    intro x hx; obtain ⟨m', hm', rfl⟩ := List.mem_map.1 hx; exact hH m' (List.mem_filter.1 hm').1)
    (Nat.zero_le _)
  have hall : ∀ x ∈ (coset.take (2 ^ hs.foldl max 0)).map (z - ·), x ≠ 0 := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
    obtain ⟨r, hr, rfl⟩ := List.getElem_of_mem hy
    rw [List.length_take] at hr
    rw [List.getElem_take, sub_ne_zero, ← List.getD_eq_getElem _ 0]
    exact hout r (by omega)
  refine ⟨_, by simp only [compute_inverse_denominators, batchInv, p3_commit.domain.mirror.batchInv]; rw [← hhs, ite_eq_left_of_eq_true _ _ (eq_true hall)], fun r hr => ?_⟩
  have hr' : r < 2 ^ hs.foldl max 0 := lt_of_lt_of_le hr (Nat.pow_le_pow_right (by norm_num) hge)
  have hrH : r < coset.length := by rw [hlen]; exact lt_of_lt_of_le hr' (Nat.pow_le_pow_right (by norm_num) hle)
  rw [List.getD_eq_getElem _ _ (by simp; omega)]
  simp only [List.getElem_map, List.getElem_take]
  rw [← List.getD_eq_getElem _ 0 hrH, bitrevCoset_getD G hN g hHa (hH m hm) hr hc]

theorem xOfQuery_eq (G : Gen K) (g : K) {H lh : ℕ} (hla : lh ≤ G.adicity) (idx : ℕ) :
    xOfQuery G g H idx lh = rowPoint G g lh (idx / 2 ^ (H - lh)) := by
  simp [xOfQuery, queryPoint, Plonky3Lean.Proofs.Dft.gen_get_of_le G hla, rowPoint]

/-- The prover's state agrees with the per-height sums at the rows of query idx. -/
def ProverInv (H idx : ℕ) (num : ℕ → ℕ) (red : ℕ → Option (List K)) (acc : ℕ → K) (cnt : ℕ → ℕ) : Prop :=
  num = cnt ∧ ∀ h, (red h = none → acc h = 0) ∧
    ∀ v, red h = some v → v.length = 2 ^ h ∧ v.getD (idx / 2 ^ (H - h)) 0 = acc h

theorem foldlM_reduceMat (G : Gen K) (hN : Plonky3Lean.Proofs.Dft.GenNested G) (g α : K) {H : ℕ}
    (hHa : H ≤ G.adicity) (mats : List (MatToOpen K)) {coset : List K} (hc : bitrevCoset G g H = some coset)
    (hH : ∀ m ∈ mats, Nat.log 2 m.mat.height ≤ H)
    (hpow : ∀ m ∈ mats, m.mat.height = 2 ^ Nat.log 2 m.mat.height)
    (h32 : ∀ m ∈ mats, Nat.log 2 m.mat.height ≤ 32)
    (hw : ∀ m ∈ mats, ∀ zy ∈ m.points.zip m.openings, zy.2.length = m.mat.width)
    (hout : ∀ m ∈ mats, ∀ z ∈ m.points, ∀ r < 2 ^ H, z ≠ rowPoint G g H r) {idx : ℕ} (hidx : idx < 2 ^ H) :
    ∀ (ms : List (MatToOpen K)), (∀ m ∈ ms, m ∈ mats) →
      ∀ (num : ℕ → ℕ) (red : ℕ → Option (List K)) (acc : ℕ → K) (cnt : ℕ → ℕ) (st : PcsRedState K),
      ProverInv H idx num red acc cnt →
      ms.foldlM (reduceMat α (compute_inverse_denominators mats coset)) (num, red) = some st →
      ProverInv H idx st.1 st.2 ((proverAllEntries H idx ms).foldl (ladderStep α (xOfQuery G g H idx)) (acc, cnt)).1
        ((proverAllEntries H idx ms).foldl (ladderStep α (xOfQuery G g H idx)) (acc, cnt)).2
  | [], _, num, red, acc, cnt, st, hI, h => by
    simp only [List.foldlM_nil, Option.pure_def, Option.some.injEq] at h
    subst h; simpa [proverAllEntries] using hI
  | m :: ms, hms, num, red, acc, cnt, st, hI, h => by
    have hm := hms m List.mem_cons_self
    rw [List.foldlM_cons] at h
    obtain ⟨st1, hst1, hrest⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨lh, hlh⟩ : ∃ lh, lh = Nat.log 2 m.mat.height := ⟨_, rfl⟩
    have hlhH : lh ≤ H := hlh ▸ hH m hm
    have hpow' : m.mat.height = 2 ^ lh := hlh ▸ hpow m hm
    have hinv : ∀ zy ∈ m.points.zip m.openings, ∃ inv, compute_inverse_denominators mats coset zy.1 = some inv ∧
        ∀ r < 2 ^ lh, inv.getD r 0 = (zy.1 - rowPoint G g lh r)⁻¹ := by
      intro zy hzy
      rw [hlh]
      refine compute_inverse_denominators_spec G hN g hHa mats hH hc hm (List.of_mem_zip hzy).1 ?_
      intro r hr
      rw [bitrevCoset_getD G hN g hHa le_rfl hr hc]
      exact hout m hm zy.1 (List.of_mem_zip hzy).1 r hr
    obtain ⟨hI1, hI2⟩ := hI
    obtain ⟨h1, h2, v, hv, hvl, hv3⟩ := reduceMat_spec α _ m hpow' (hlh ▸ h32 m hm) (hw m hm)
      (rowPoint G g lh) hinv num red (fun v hv => ((hI2 lh).2 v hv).1) st1 hst1
    have hr : idx / 2 ^ (H - lh) < 2 ^ lh := by
      rw [Nat.div_lt_iff_lt_mul (by positivity), ← pow_add, show lh + (H - lh) = H by omega]; exact hidx
    have hentries := foldl_ladderStep_same α (xOfQuery G g H idx) lh (proverEntries m (idx / 2 ^ (H - lh)))
      acc cnt
    have hlen : ((proverEntries m (idx / 2 ^ (H - lh))).map fun e => e.2.1.length).sum =
        (m.points.zip m.openings).length * m.mat.width := by
      simp only [proverEntries, List.map_map, Function.comp_def]
      rw [List.map_congr_left (fun zy hzy => hw m hm zy hzy), List.map_const', List.sum_replicate, smul_eq_mul]
    have hI' : ProverInv H idx st1.1 st1.2
        ((((proverEntries m (idx / 2 ^ (H - lh))).map fun e => (lh, e)).foldl
          (ladderStep α (xOfQuery G g H idx)) (acc, cnt)).1)
        ((((proverEntries m (idx / 2 ^ (H - lh))).map fun e => (lh, e)).foldl
          (ladderStep α (xOfQuery G g H idx)) (acc, cnt)).2) := by
      rw [hentries]
      dsimp only
      refine ⟨by rw [h1, hlen, hI1], fun h' => ?_⟩
      by_cases hh : h' = lh
      · subst hh
        refine ⟨by simp [hv], fun v' hv' => ?_⟩
        rw [hv] at hv'; obtain rfl := Option.some.inj hv'
        refine ⟨hvl, ?_⟩
        rw [hv3 _ hr, Function.update_self, xOfQuery_eq G g (le_trans hlhH hHa), hI1]
        congr 1
        rcases hred : red h' with _ | w
        · simp [(hI2 _).1 hred]
        · rw [Option.getD_some]; exact ((hI2 _).2 w hred).2
      · simp only [Function.update_of_ne hh]
        rw [h2 h' hh]; exact hI2 h'
    have := foldlM_reduceMat G hN g α hHa mats hc hH hpow h32 hw hout hidx ms
      (fun x hx => hms x (List.mem_cons_of_mem _ hx)) _ _ _ _ st hI' hrest
    simpa [proverAllEntries, List.foldl_append, ← hlh] using this

/-- The prover's reduced vectors: at each height present, the entry at the row of query idx is the reduced opening of the claims at that height, with the matrices' rows as column values and the query point of that height. -/
theorem reduced_openings_spec (G : Gen K) (hN : Plonky3Lean.Proofs.Dft.GenNested G) (g α : K)
    (mats : List (MatToOpen K)) {H : ℕ} (hHmax : (mats.map fun m => Nat.log 2 m.mat.height).max? = some H)
    (hHa : H ≤ G.adicity) (hpow : ∀ m ∈ mats, m.mat.height = 2 ^ Nat.log 2 m.mat.height)
    (h32 : ∀ m ∈ mats, Nat.log 2 m.mat.height ≤ 32)
    (hw : ∀ m ∈ mats, ∀ zy ∈ m.points.zip m.openings, zy.2.length = m.mat.width)
    (hout : ∀ m ∈ mats, ∀ z ∈ m.points, ∀ r < 2 ^ H, z ≠ rowPoint G g H r)
    {red : List (ℕ × List K)} (h : reduced_openings G g α mats = some red) {idx : ℕ} (hidx : idx < 2 ^ H) :
    ∀ e ∈ red, e.2.length = 2 ^ e.1 ∧ e.2.getD (idx / 2 ^ (H - e.1)) 0 =
      reducedOpening α (xOfQuery G g H idx e.1) 0 (((proverAllEntries H idx mats).filter (·.1 = e.1)).map (·.2)) := by
  have hH : ∀ m ∈ mats, Nat.log 2 m.mat.height ≤ H := fun m hm =>
    (List.max?_eq_some_iff.1 hHmax).2 _ (List.mem_map.2 ⟨m, hm, rfl⟩)
  unfold reduced_openings at h
  rw [hHmax] at h
  simp only [Option.bind_eq_bind, Option.bind_some] at h
  obtain ⟨coset, hc, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨⟨num, red'⟩, hfold, h⟩ := Option.bind_eq_some_iff.1 h
  obtain rfl := (Option.some.inj h).symm
  have hI := foldlM_reduceMat G hN g α hHa mats hc hH hpow h32 hw hout hidx mats (fun _ h => h)
    (fun _ => 0) (fun _ => none) (fun _ => 0) (fun _ => 0) _ ⟨rfl, fun _ => ⟨fun _ => rfl, by simp⟩⟩ hfold
  intro e he
  simp only [List.mem_filterMap, Option.map_eq_some_iff] at he
  obtain ⟨h', -, v, hv, rfl⟩ := he
  obtain ⟨hl, hg⟩ := (hI.2 h').2 v hv
  refine ⟨hl, ?_⟩
  rw [hg, foldl_ladderStep]
  simp

end Plonky3Lean.Proofs.Fri
