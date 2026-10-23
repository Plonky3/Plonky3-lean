module

public import P3Commit.Testing
public import Plonky3Lean.Proofs.Commit.PeriodicTable
public import Plonky3Lean.Proofs.Dft.Lde
public import Plonky3Lean.Spec.Commit

@[expose] public section

/-!
# p3-commit: the trivial scheme meets the univariate contract

The commitment is the coefficient matrix of each committed matrix, flattened.

On a coset s H of order n with generator omega, the inverse transform of the evaluations e gives the coefficients c of q with q(omega^i) = e_i.

Scaling coefficient r by s^(-r) gives p(X) = q(X / s), so p(s omega^i) = e_i:

```text
    p(X) = sum_{r < n} c_r s^(-r) X^r
```

Opening evaluates p by Horner's rule, and verifying recomputes the same values.
-/

open Polynomial Finset
open p3_commit.testing.mirror p3_commit.domain.mirror p3_commit.pcs.univariate.mirror
open p3_field.coset.mirror p3_dft.mirror
open Plonky3Lean.Spec.Commit Plonky3Lean.Proofs.Dft

namespace Plonky3Lean.Proofs.Commit

set_option linter.unusedSectionVars false

variable {K : Type _} [Field K] [DecidableEq K] (G : Gen K)

/-! ## Horner's rule -/

theorem foldl_horner_apply {w : ℕ} (entry : ℕ → Fin w → K) (x : K) (L : List ℕ) (acc : Fin w → K)
    (c : Fin w) :
    L.foldl (fun (acc : Fin w → K) r => fun c => acc c * x + entry r c) acc c =
      L.foldl (fun s r => s * x + entry r c) (acc c) := by
  induction L generalizing acc with
  | nil => rfl
  | cons r L ih => exact ih _

/-- Each column's value is sum_r entry_(r, c) x^r. -/
theorem eval_coeffs_at_pt_eq (m : Mat K) (x : K) :
    eval_coeffs_at_pt m x = (List.finRange m.width).map fun c =>
      ∑ r ∈ range m.height, m.entry r c * x ^ r := by
  simp only [eval_coeffs_at_pt]
  congr 1
  funext c
  rw [foldl_horner_apply, Plonky3Lean.Proofs.Matrix.Interp.horner_eq]
  simp

/-! ## The coefficients of a coset -/

/-- Scaling the inverse transform's coefficient r by s^(-r) gives the interpolant over s H. -/
theorem poly_scaled_idft (hV : GenValid G) {k : ℕ} (hk : k ≤ G.adicity) {s : K} (hs : s ≠ 0)
    (e : ℕ → K) :
    Spec.Dft.poly (2 ^ k) (fun r => Spec.Dft.idft (G.gen k) (2 ^ k) e r * s⁻¹ ^ r) =
      interpolant s (G.gen k) k fun i => e i.val := by
  have hω := hV k hk
  have hq := poly_idft_eq_interpolant hω e
  refine Lagrange.eq_interpolate_of_eval_eq _ (cosetPoints_injective hω hs).injOn
    (by rw [card_univ, Fintype.card_fin]; exact degree_poly_lt _ _) fun i _ => ?_
  have hnode : (Spec.Dft.poly (2 ^ k) (Spec.Dft.idft (G.gen k) (2 ^ k) e)).eval (G.gen k ^ i.val) =
      e i.val := by
    rw [hq, Spec.Dft.interpolant]
    have hinj : Function.Injective (fun j : Fin (2 ^ k) => G.gen k ^ j.val) := fun a b h =>
      cosetPoints_injective (s := 1) hω one_ne_zero (by simpa [cosetPoints] using h)
    exact Lagrange.eval_interpolate_at_node _ hinj.injOn (mem_univ i)
  rw [← hnode, eval_poly, eval_poly, cosetPoints]
  refine sum_congr rfl fun j _ => ?_
  rw [smul_eq_mul, smul_eq_mul, mul_pow, inv_pow]
  field_simp

/-! ## List plumbing -/

theorem mapM_eq_some_iff {α β : Type _} (f : α → Option β) (l : List α) (l' : List β) :
    l.mapM f = some l' ↔ List.Forall₂ (fun a b => f a = some b) l l' := by
  induction l generalizing l' with
  | nil => cases l' <;> simp
  | cons a l ih =>
    cases l' with
    | nil =>
      simp only [List.mapM_cons, Option.bind_eq_bind, List.forall₂_nil_right_iff, reduceCtorEq,
        iff_false]
      cases f a <;> simp
      cases l.mapM f <;> simp
    | cons b l' =>
      simp only [List.mapM_cons, Option.bind_eq_bind, List.forall₂_cons, ← ih]
      cases f a <;> cases l.mapM f <;> simp

theorem forM_eq_some_iff {α : Type _} (f : α → Option Unit) (l : List α) :
    l.forM f = some () ↔ ∀ a ∈ l, f a = some () := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.mem_cons, forall_eq_or_imp, ← ih]
    cases h : f a <;> simp [h]

/-! ## The flattened commitment -/

theorem length_flatValues (m : Mat K) : (flatValues m).length = m.height * m.width := by
  simp [flatValues, List.length_flatMap, List.sum_replicate]

theorem flatValues_getD (m : Mat K) {r : ℕ} (hr : r < m.height) (c : Fin m.width) :
    (flatValues m).getD (r * m.width + c.val) 0 = m.entry r c := by
  have hlen : ∀ row ∈ (List.range m.height).map fun r => (List.finRange m.width).map (m.entry r),
      row.length = m.width := by simp
  have := flatten_getElem? ((List.range m.height).map fun r => (List.finRange m.width).map (m.entry r))
    m.width hlen r c.val c.isLt
  rw [List.getD_eq_getElem?_getD, flatValues]
  show ((List.range m.height).map _).flatten[_]?.getD 0 = _
  rw [this]
  simp [hr]

/-- The polynomials a flat coefficient vector holds over a domain of size n: width |v| / n, and coefficient r of column c at r w + c. -/
noncomputable def flatPolys (v : List K) (n : ℕ) : List K[X] :=
  (List.finRange (v.length / n)).map fun c => Spec.Dft.poly n fun r => v.getD (r * (v.length / n) + c.val) 0

theorem eval_ofFlat (v : List K) {n : ℕ} (hw : v.length / n * n = v.length) (z : K) :
    eval_coeffs_at_pt (ofFlat v (v.length / n)) z = (flatPolys v n).map (Polynomial.eval z) := by
  rw [eval_coeffs_at_pt_eq, flatPolys, List.map_map]
  by_cases hw0 : v.length / n = 0
  · simp only [ofFlat]
    rw [List.finRange_eq_nil_iff.mpr hw0]
    rfl
  · have hh : (ofFlat v (v.length / n)).height = n := by
      simp only [ofFlat, hw0, ite_false]
      exact Nat.div_eq_of_eq_mul_right (Nat.pos_of_ne_zero hw0) hw.symm
    refine List.map_congr_left fun c _ => ?_
    simp only [Function.comp, eval_poly, smul_eq_mul]
    rw [hh]
    exact sum_congr rfl fun r _ => mul_comm _ _

theorem checkMatrix_eq_some (v : List K) (mo : MatrixOpening K (Coset G)) :
    checkMatrix G (v, mo) = some () ↔
      v.length / Coset.size G mo.domain * Coset.size G mo.domain = v.length ∧
        ∀ p ∈ mo.points, p.values = (flatPolys v (Coset.size G mo.domain)).map (Polynomial.eval p.point) := by
  have hn : 0 < Coset.size G mo.domain := by rw [size_eq]; positivity
  unfold checkMatrix
  dsimp only
  split_ifs with h
  · simp [h]
  · push Not at h
    rw [forM_eq_some_iff]
    simp only [h, true_and]
    refine forall₂_congr fun p _ => ?_
    rw [eval_ofFlat v h]
    split_ifs with he
    · simp [he]
    · simp only [false_iff]
      exact fun h' => he h'.symm

theorem verify_eq_some_true (cl : List (CommitmentOpening K (List (List K)) (Coset G))) :
    TrivialPcs.verify G cl = some true ↔
      ∀ o ∈ cl, o.commitment.length = o.matrices.length ∧
        ∀ cv ∈ o.commitment.zip o.matrices, checkMatrix G cv = some () := by
  induction cl with
  | nil => simp [TrivialPcs.verify]
  | cons o cl ih =>
    simp only [TrivialPcs.verify, List.mem_cons, forall_eq_or_imp]
    split_ifs with h
    · simp [h]
    · push Not at h
      rw [← ih, ← forM_eq_some_iff]
      cases (o.commitment.zip o.matrices).forM (checkMatrix G) <;> simp [h]

theorem poly_congr {n : ℕ} {f g : ℕ → K} (h : ∀ r < n, f r = g r) : Spec.Dft.poly n f = Spec.Dft.poly n g := by
  unfold Spec.Dft.poly
  exact sum_congr rfl fun r hr => by rw [h r (mem_range.mp hr)]

theorem flatPolys_eq_of (v : List K) (n w : ℕ) (hw : v.length / n = w) :
    flatPolys v n = (List.finRange w).map fun col =>
      Spec.Dft.poly n fun r => v.getD (r * w + col.val) 0 := by
  subst hw; rfl

theorem degree_flatPolys (v : List K) (n : ℕ) : ∀ q ∈ flatPolys v n, q.degree < n := by
  intro q hq
  obtain ⟨c, -, rfl⟩ := List.mem_map.mp hq
  exact degree_poly_lt _ _

/-! ## The scheme -/

section scheme

variable {K : Type} [Field K] [DecidableEq K] (G : Gen K)

/-- The backend computes the inverse transform on every power-of-two height the table covers. -/
def IdftComputes (idft : (w : ℕ) → ℕ → (ℕ → Fin w → K) → Option (ℕ → Fin w → K)) : Prop :=
  ∀ w k, k ≤ G.adicity → ∀ x, Computes (idft w (2 ^ k) x) (2 ^ k) (Spec.Dft.idft (G.gen k) (2 ^ k) x)

/-- The trivial scheme, with any challenger type: open and verify leave the challenger as it is. -/
abbrev trivialScheme (C : Type) (idft : (w : ℕ) → ℕ → (ℕ → Fin w → K) → Option (ℕ → Fin w → K))
    (pcs : TrivialPcs) : UnivariatePcs K where
  Domain := Coset G
  Commitment := List (List K)
  ProverData := List (Mat K)
  Proof := Unit
  Challenger := C
  size d := Coset.size G d
  point d i := d.shift * d.subgroup_generator ^ i.val
  commit r := pcs.commit G idft r
  open_ rs ch := (TrivialPcs.open (K := K) rs).map fun v => (v, (), ch)
  verify cl _ ch := (TrivialPcs.verify G cl).map fun b => (b, ch)

/-- One committed matrix: the coefficient matrix of an evaluation matrix that fits its domain. -/
def CommitsTo (idft : (w : ℕ) → ℕ → (ℕ → Fin w → K) → Option (ℕ → Fin w → K)) (pcs : TrivialPcs)
    (de : Coset G × Mat K) (c : Mat K) : Prop :=
  pcs.log_n ≤ de.1.log_size ∧ Coset.size G de.1 = de.2.height ∧
    ∃ y, idft de.2.width de.2.height de.2.entry = some y ∧
      c = ⟨de.2.height, de.2.width, fun r col => y r col * de.1.shift⁻¹ ^ r⟩

theorem commit_eq_some (idft : (w : ℕ) → ℕ → (ℕ → Fin w → K) → Option (ℕ → Fin w → K))
    (pcs : TrivialPcs) (r : List (Coset G × Mat K)) (cd : List (List K) × List (Mat K))
    (h : pcs.commit G idft r = some cd) :
    cd = (cd.2.map flatValues, cd.2) ∧ List.Forall₂ (CommitsTo G idft pcs) r cd.2 := by
  simp only [TrivialPcs.commit, Option.bind_eq_bind] at h
  cases hm : r.mapM fun de => if de.1.log_size < pcs.log_n then none
      else if Coset.size G de.1 ≠ de.2.height then none
      else (idft de.2.width de.2.height de.2.entry).bind fun c =>
        pure (⟨de.2.height, de.2.width, fun r col => c r col * de.1.shift⁻¹ ^ r⟩ : Mat K) with
  | none => rw [hm] at h; simp at h
  | some coeffs =>
    rw [hm] at h
    simp only [Option.bind_some, Option.pure_def, Option.some.injEq] at h
    subst h
    refine ⟨rfl, ?_⟩
    refine ((mapM_eq_some_iff _ _ _).mp hm).imp fun {de c} hdc => ?_
    split_ifs at hdc with h1 h2
    push Not at h1 h2
    cases hy : idft de.2.width de.2.height de.2.entry with
    | none => simp [hy] at hdc
    | some y =>
      simp only [hy, Option.bind_some, Option.pure_def, Option.some.injEq] at hdc
      exact ⟨h1, h2, y, hy, hdc.symm⟩

/-- The coefficient matrix of a committed matrix holds, column by column, the interpolant of the evaluations over the domain. -/
theorem commitsTo_poly (hV : GenValid G) {idft : (w : ℕ) → ℕ → (ℕ → Fin w → K) → Option (ℕ → Fin w → K)}
    (hidft : IdftComputes G idft) {pcs : TrivialPcs} {de : Coset G × Mat K} {c : Mat K}
    (h : CommitsTo G idft pcs de c) (col : Fin de.2.width) :
    Spec.Dft.poly (Coset.size G de.1) (fun r => (flatValues c).getD (r * de.2.width + col.val) 0) =
      Lagrange.interpolate univ (fun i : Fin (Coset.size G de.1) => de.1.shift * de.1.subgroup_generator ^ i.val)
        fun i => de.2.entry i.val col := by
  obtain ⟨-, hsz, y, hy, rfl⟩ := h
  obtain ⟨y', hy', hspec⟩ := hidft de.2.width de.1.log_size de.1.log_size_le de.2.entry
  rw [size_eq] at hsz
  rw [← hsz] at hy
  rw [hy] at hy'
  cases hy'
  show Spec.Dft.poly (2 ^ de.1.log_size) _ =
    interpolant de.1.shift (G.gen de.1.log_size) de.1.log_size fun i => de.2.entry i.val col
  rw [← poly_scaled_idft G hV de.1.log_size_le de.1.shift_ne_zero (fun i => de.2.entry i col)]
  refine poly_congr fun r hr => ?_
  rw [flatValues_getD (⟨de.2.height, de.2.width, fun r col => y r col * de.1.shift⁻¹ ^ r⟩ : Mat K)
    (r := r) (by show r < de.2.height; omega) col]
  dsimp only
  rw [hspec r hr, idft_col]

/-- The polynomials a committed matrix's flattened coefficients hold are its columns' interpolants. -/
theorem flatPolys_commitsTo (hV : GenValid G) {idft : (w : ℕ) → ℕ → (ℕ → Fin w → K) → Option (ℕ → Fin w → K)}
    (hidft : IdftComputes G idft) {pcs : TrivialPcs} {de : Coset G × Mat K} {c : Mat K}
    (h : CommitsTo G idft pcs de c) :
    flatPolys (flatValues c) (Coset.size G de.1) = (List.finRange de.2.width).map fun col =>
      Lagrange.interpolate univ (fun i : Fin (Coset.size G de.1) =>
        de.1.shift * de.1.subgroup_generator ^ i.val) fun i => de.2.entry i.val col := by
  have hw : (flatValues c).length / Coset.size G de.1 = de.2.width := by
    obtain ⟨-, hsz, y, -, rfl⟩ := h
    rw [length_flatValues, hsz]
    exact Nat.mul_div_cancel_left _ (by rw [← hsz, size_eq]; positivity)
  rw [flatPolys_eq_of _ _ _ hw]
  exact List.map_congr_left fun col _ => commitsTo_poly G hV hidft h col

/-- Horner's rule on a committed matrix evaluates those polynomials. -/
theorem eval_coeffs_commitsTo {idft : (w : ℕ) → ℕ → (ℕ → Fin w → K) → Option (ℕ → Fin w → K)}
    {pcs : TrivialPcs} {de : Coset G × Mat K} {c : Mat K} (h : CommitsTo G idft pcs de c) (z : K) :
    eval_coeffs_at_pt c z = (flatPolys (flatValues c) (Coset.size G de.1)).map (Polynomial.eval z) := by
  have hn : 0 < Coset.size G de.1 := by rw [size_eq]; positivity
  have hsz : c.height = Coset.size G de.1 := by obtain ⟨-, hsz, y, -, rfl⟩ := h; exact hsz.symm
  have hw : (flatValues c).length / Coset.size G de.1 = c.width := by
    rw [length_flatValues, hsz]; exact Nat.mul_div_cancel_left _ hn
  rw [eval_coeffs_at_pt_eq, flatPolys_eq_of _ _ _ hw, List.map_map]
  refine List.map_congr_left fun col _ => ?_
  simp only [Function.comp, eval_poly, smul_eq_mul, hsz]
  refine sum_congr rfl fun r hr => ?_
  rw [flatValues_getD c (by rw [hsz]; exact mem_range.mp hr) col, mul_comm]

variable {C : Type} {idft : (w : ℕ) → ℕ → (ℕ → Fin w → K) → Option (ℕ → Fin w → K)} {pcs : TrivialPcs}

/-- One round of an honest opening: Horner's values are the true ones, and every matrix check passes. -/
theorem round_honest (hV : GenValid G) (hidft : IdftComputes G idft) :
    ∀ (r : List (Coset G × Mat K)) (cs : List (Mat K)) (p : List (List K)),
      List.Forall₂ (CommitsTo G idft pcs) r cs → r.length = p.length →
      (cs.zip p).map (fun cp => cp.2.map (eval_coeffs_at_pt cp.1)) =
          (r.zip p).map (fun dp => dp.2.map ((trivialScheme G C idft pcs).columnValues dp.1.1 dp.1.2)) ∧
        ∀ cv ∈ (cs.map flatValues).zip (((r.zip p).zip ((r.zip p).map fun dp =>
            dp.2.map ((trivialScheme G C idft pcs).columnValues dp.1.1 dp.1.2))).map fun f =>
              (⟨f.1.1.1, (f.1.2.zip f.2).map fun g => ⟨g.1, g.2⟩⟩ : MatrixOpening K (Coset G))),
          checkMatrix G cv = some ()
  | [], [], [], _, _ => by simp
  | de :: r, c :: cs, z :: p, .cons hdc hrest, hlen => by
    obtain ⟨ih1, ih2⟩ := round_honest hV hidft r cs p hrest (by simpa using hlen)
    have hcol : ∀ x, eval_coeffs_at_pt c x = (trivialScheme G C idft pcs).columnValues de.1 de.2 x := by
      intro x
      rw [eval_coeffs_commitsTo G hdc, flatPolys_commitsTo G hV hidft hdc, List.map_map]
      rfl
    refine ⟨by simp [ih1, hcol], ?_⟩
    simp only [List.map_cons, List.zip_cons_cons, List.mem_cons, forall_eq_or_imp]
    refine ⟨?_, ih2⟩
    rw [checkMatrix_eq_some]
    have hn : 0 < Coset.size G de.1 := by rw [size_eq]; positivity
    have hsz := hdc.2.1
    have hw : (flatValues c).length / Coset.size G de.1 * Coset.size G de.1 = (flatValues c).length := by
      have : (flatValues c).length = de.2.height * de.2.width := by
        obtain ⟨-, -, y, -, rfl⟩ := hdc; exact length_flatValues _
      rw [this, ← hsz, Nat.mul_div_cancel_left _ hn, mul_comm]
    refine ⟨hw, fun q hq => ?_⟩
    rw [← List.map_prod_left_eq_zip, List.map_map] at hq
    obtain ⟨x, -, rfl⟩ := List.mem_map.mp hq
    dsimp only [Function.comp]
    rw [← eval_coeffs_commitsTo G hdc x, hcol x]
  | [], _ :: _, _, h, _ => by cases h
  | _ :: _, [], _, h, _ => by cases h
  | _ :: _, _ :: _, [], _, h => by simp at h
  | [], [], _ :: _, _, h => by simp at h

/-- All rounds of an honest opening. -/
theorem rounds_honest (hV : GenValid G) (hidft : IdftComputes G idft) :
    ∀ (rounds : List (List (Coset G × Mat K))) (cds : List (List (List K) × List (Mat K)))
      (pts : List (List (List K))),
      List.Forall₂ (fun r cd => pcs.commit G idft r = some cd) rounds cds →
      List.Forall₂ (fun r p => r.length = List.length p) rounds pts →
      TrivialPcs.open ((cds.map Prod.snd).zip pts) =
          some ((trivialScheme G C idft pcs).expected rounds pts) ∧
        TrivialPcs.verify G ((trivialScheme G C idft pcs).claims (cds.map Prod.fst) rounds pts
          ((trivialScheme G C idft pcs).expected rounds pts)) = some true
  | [], [], [], _, _ => ⟨rfl, rfl⟩
  | r :: rounds, cd :: cds, p :: pts, .cons hcd hcds, .cons hp hpts => by
    obtain ⟨ih1, ih2⟩ := rounds_honest hV hidft rounds cds pts hcds hpts
    obtain ⟨hcd1, hcd2⟩ := commit_eq_some G idft pcs r cd hcd
    have hlen : cd.2.length = r.length := hcd2.length_eq.symm
    obtain ⟨h1, h2⟩ := round_honest (C := C) G hV hidft r cd.2 p hcd2 hp
    constructor
    · simp only [TrivialPcs.open, List.map_cons, List.zip_cons_cons, List.mapM_cons] at ih1 ⊢
      rw [ih1]
      simp only [hlen, hp, ne_eq, not_true_eq_false, ite_false, h1, Option.bind_eq_bind,
        Option.bind_some, Option.pure_def, Option.some.injEq]
      rfl
    · replace ih2 := (verify_eq_some_true G _).mp ih2
      refine (verify_eq_some_true G _).mpr ?_
      simp only [UnivariatePcs.claims, UnivariatePcs.expected] at ih2 ⊢
      simp only [List.map_cons, List.zip_cons_cons, List.mem_cons, forall_eq_or_imp]
      refine ⟨⟨?_, ?_⟩, ih2⟩
      · rw [hcd1]; simp [hlen, hp]
      · rw [hcd1]; exact h2
  | [], _ :: _, _, h, _ => by cases h
  | _ :: _, [], _, h, _ => by cases h
  | _ :: _, _, [], _, h => by cases h
  | [], _, _ :: _, _, h => by cases h

/-- The trivial scheme meets the univariate contract, and nothing breaks its binding. -/
noncomputable def trivialContract (hV : GenValid G) (hidft : IdftComputes G idft) :
    (trivialScheme G C idft pcs).Contract where
  Broken _ := False
  extract cm m d := flatPolys (cm.getD m []) (Coset.size G d)
  completeness rounds cds pts ch _ hc hp := by
    obtain ⟨h1, h2⟩ := rounds_honest (C := C) G hV hidft rounds cds pts hc hp
    refine ⟨(), ch, ?_, ?_⟩
    · show (TrivialPcs.open _).map _ = _
      rw [h1]; rfl
    · show (TrivialPcs.verify G _).map _ = _
      rw [h2]; rfl
  soundness cl pf ch ch' h o ho m hm p hp := by
    left
    have hv : TrivialPcs.verify G cl = some true := by
      cases hver : TrivialPcs.verify G cl with
      | none => simp [hver] at h
      | some b =>
        simp only [hver, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        rw [h.1]
    obtain ⟨hlen, hcheck⟩ := (verify_eq_some_true G cl).mp hv o ho
    have hm' : m < o.commitment.length := hlen ▸ hm
    have hmem : (o.commitment[m], o.matrices[m]) ∈ o.commitment.zip o.matrices :=
      List.mem_iff_getElem.mpr ⟨m, by simp [hm, hm'], by simp⟩
    have := ((checkMatrix_eq_some G _ _).mp (hcheck _ hmem)).2 p hp
    rw [this, List.getD_eq_getElem _ _ hm']
  degree cm m d := degree_flatPolys _ _
  honest r cd _ hc m hm := by
    obtain ⟨hcd1, hcd2⟩ := commit_eq_some G idft pcs r cd hc
    have hm2 : m < cd.2.length := hcd2.length_eq ▸ hm
    have hR := hcd2.get hm hm2
    simp only [List.get_eq_getElem] at hR
    show flatPolys (cd.1.getD m []) _ = _
    rw [hcd1]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hm2,
      Option.map_some, Option.getD_some]
    exact flatPolys_commitsTo G hV hidft hR

end scheme

end Plonky3Lean.Proofs.Commit
