module

public import Plonky3Lean.Proofs.Fri.Complete
public import Plonky3Lean.Proofs.Fri.Deep
public import Plonky3Lean.Proofs.Fri.Final

@[expose] public section

/-!
# The first word is the DEEP codeword

The LDE of every column lives on the coset g H, in bit-reversed order.

So row r of a matrix of log height h holds the columns at g G_h^rev_h(r).

The FRI chain reads its words on the subgroup H, so a polynomial Q is folded as Q(g X):

```text
    word_h[t] = D_h(g G_h^rev_h(t)) = (D_h o gX)(G_h^rev_h(t))
```

Here D_h is the batched DEEP polynomial of the claims at height h.

This holds for the prover's reduced vectors and for the verifier's reduction of every query.
-/

namespace Plonky3Lean.Proofs.Fri

open Polynomial Finset Plonky3Lean.Spec.Fri p3_fri.two_adic_pcs.mirror p3_dft.mirror
open p3_fri.verifier.mirror p3_fri.mirror p3_fri.config.mirror Plonky3Lean.Proofs.Dft
open p3_commit.pcs.univariate.mirror p3_fri.transcript.mirror

set_option linter.unusedSectionVars false

variable {K : Type} [Field K] [DecidableEq K]

/-! ## Words and the coset shift -/

/-- The word of Q at log height N: Q at G_N^rev_N(i), for every index i. -/
def word (G : Gen K) (Q : K[X]) (N : ℕ) : List K := (List.range (2 ^ N)).map fun i => Q.eval (dom G N i)

theorem word_isCodeword (G : Gen K) (Q : K[X]) (N : ℕ) : IsCodeword G Q N (word G Q N) :=
  ⟨by simp [word], fun i hi => by rw [word, getD_map_range _ hi]⟩

/-- Q read on the coset g H: the polynomial Q(g X). -/
noncomputable def onCoset (Q : K[X]) (g : K) : K[X] := Q.comp (C g * X)

theorem eval_onCoset (Q : K[X]) (g x : K) : (onCoset Q g).eval x = Q.eval (g * x) := by
  simp [onCoset]

theorem degree_onCoset_le (Q : K[X]) (g : K) : (onCoset Q g).degree ≤ Q.degree := by
  rcases eq_or_ne Q 0 with rfl | hQ
  · simp [onCoset]
  rw [degree_eq_natDegree hQ]
  refine degree_le_of_natDegree_le (natDegree_comp_le.trans ?_)
  exact (Nat.mul_le_mul_left _ (natDegree_C_mul_le _ _ |>.trans natDegree_X_le)).trans_eq (mul_one _)

/-- An honest LDE row: row r of log height h holds the columns at g G_h^rev_h(r). -/
theorem rowPoint_eq (G : Gen K) (g : K) (h r : ℕ) : rowPoint G g h r = g * dom G h r := rfl

/-! ## Two lists sorted the same way -/

theorem eq_of_pairwise_gt {l1 l2 : List ℕ} (h1 : l1.Pairwise (· > ·)) (h2 : l2.Pairwise (· > ·))
    (hm : ∀ a, a ∈ l1 ↔ a ∈ l2) : l1 = l2 :=
  List.Perm.eq_of_pairwise (fun _ _ _ _ hab hba => absurd (lt_trans hab hba) (lt_irrefl _)) h1 h2
    ((List.perm_ext_iff_of_nodup (h1.imp ne_of_gt) (h2.imp ne_of_gt)).2 hm)

/-- The input heights are strictly decreasing. -/
theorem inputLogHeights_pairwise {G : Gen K} {C : Type} (b : ℕ) (claims : List (Claim G C)) :
    (inputLogHeights b claims).Pairwise (· > ·) := by
  have hs := List.pairwise_mergeSort (le := fun a b : ℕ => decide (b ≤ a))
    (fun a b c h1 h2 => by simp only [decide_eq_true_eq] at *; omega)
    (fun a b => by simp only [Bool.or_eq_true, decide_eq_true_eq]; omega)
    (claims.flatMap fun c => c.matrices.map fun m => m.domain.log_size + b)
  have hd := hs.sublist (List.dedup_sublist _)
  exact List.Pairwise.imp_of_mem (fun {a b} _ _ h => by simp only [decide_eq_true_eq] at h; omega)
    (List.Pairwise.and hd (List.nodup_dedup _))

theorem mem_inputLogHeights {G : Gen K} {C : Type} (b : ℕ) (claims : List (Claim G C)) (h : ℕ) :
    h ∈ inputLogHeights b claims ↔ ∃ c ∈ claims, ∃ m ∈ c.matrices, m.domain.log_size + b = h := by
  simp [inputLogHeights, List.mem_dedup, List.mem_mergeSort]

/-! ## The prover's first word -/

/-- An honest matrix to open, with columns cols:

- its width is the number of columns
- row r holds the columns at g G_h^rev_h(r), for h its log height
- the values claimed at a point z are the columns at z. -/
structure HonestMat (G : Gen K) (g : K) (cols : List K[X]) (m : MatToOpen K) : Prop where
  width : m.mat.width = cols.length
  entry : ∀ r < m.mat.height, ∀ c : Fin m.mat.width,
    m.mat.entry r c = (cols.getD c 0).eval (rowPoint G g (Nat.log 2 m.mat.height) r)
  openings : m.openings = m.points.map fun z => cols.map (·.eval z)

/-- The claims at log height h of the prover's matrices, each point with its matrix's columns. -/
noncomputable def proverDeep (cols : MatToOpen K → List K[X]) (h : ℕ) (mats : List (MatToOpen K)) :
    List (K × List K[X]) :=
  (mats.filter fun m => Nat.log 2 m.mat.height = h).flatMap fun m => m.points.map fun z => (z, cols m)

theorem matRow_honest {G : Gen K} {g : K} {cols : List K[X]} {m : MatToOpen K} (hm : HonestMat G g cols m)
    {r : ℕ} (hr : r < m.mat.height) :
    matRow m.mat r = cols.map (·.eval (rowPoint G g (Nat.log 2 m.mat.height) r)) := by
  refine List.ext_getElem (by simp [matRow, hm.width]) fun i h1 h2 => ?_
  simp only [matRow, List.getElem_map, List.getElem_finRange]
  rw [hm.entry r hr, List.getD_eq_getElem _ _ (by simpa using h2)]
  rfl

theorem proverEntries_honest {G : Gen K} {g : K} {cols : List K[X]} {m : MatToOpen K}
    (hm : HonestMat G g cols m) {r : ℕ} (hr : r < m.mat.height) :
    proverEntries m r = m.points.map fun z =>
      (z, cols.map (·.eval z), cols.map (·.eval (rowPoint G g (Nat.log 2 m.mat.height) r))) := by
  rw [proverEntries, hm.openings, matRow_honest hm hr]
  induction m.points <;> simp_all

/-- The prover's claims at one height, at the row of query idx, are the DEEP claims there. -/
theorem proverAllEntries_honest (G : Gen K) (g : K) (cols : MatToOpen K → List K[X]) (H idx h : ℕ) :
    ∀ (mats : List (MatToOpen K)), (∀ m ∈ mats, HonestMat G g (cols m) m) →
      (∀ m ∈ mats, idx / 2 ^ (H - Nat.log 2 m.mat.height) < m.mat.height) →
      ((proverAllEntries H idx mats).filter (·.1 = h)).map (·.2) =
        (proverDeep cols h mats).map fun e =>
          (e.1, e.2.map (·.eval e.1), e.2.map (·.eval (rowPoint G g h (idx / 2 ^ (H - h)))))
  | [], _, _ => rfl
  | m :: mats, hhon, hr => by
    have ih := proverAllEntries_honest G g cols H idx h mats (fun x hx => hhon x (List.mem_cons_of_mem _ hx))
      (fun x hx => hr x (List.mem_cons_of_mem _ hx))
    simp only [proverAllEntries, proverDeep, List.flatMap_cons] at ih ⊢
    rw [proverEntries_honest (hhon m List.mem_cons_self) (hr m List.mem_cons_self)]
    by_cases hh : Nat.log 2 m.mat.height = h
    · simp only [List.flatMap_cons, List.filter_append, List.map_append, List.filter_cons, hh, decide_true,
        ↓reduceIte, ih, List.map_map]
      congr 1
      rw [List.filter_eq_self.2 (by simp)]
      simp [Function.comp_def]
    · simp only [List.filter_append, List.map_append, List.filter_cons, hh, decide_false,
        Bool.false_eq_true, ↓reduceIte, ih, List.map_map]
      rw [List.filter_eq_nil_iff.2 (by simp [hh])]
      rfl

/-- A reduced vector exists only at the log height of some matrix. -/
theorem foldlM_reduceMat_support (α : K) (inv : K → Option (List K)) :
    ∀ (ms : List (MatToOpen K)) (st st' : PcsRedState K), ms.foldlM (reduceMat α inv) st = some st' →
      ∀ h, st'.2 h ≠ none → st.2 h ≠ none ∨ ∃ m ∈ ms, Nat.log 2 m.mat.height = h
  | [], st, st', hf, h, hh => by
    simp only [List.foldlM_nil, Option.pure_def, Option.some.injEq] at hf; subst hf; exact .inl hh
  | m :: ms, st, st', hf, h, hh => by
    rw [List.foldlM_cons] at hf
    obtain ⟨st1, h1, hrest⟩ := Option.bind_eq_some_iff.1 hf
    rcases foldlM_reduceMat_support α inv ms st1 st' hrest h hh with h2 | ⟨m', hm', rfl⟩
    · obtain ⟨num, red⟩ := st
      unfold reduceMat at h1
      dsimp only at h1
      rcases hl : log2Strict m.mat.height with _ | lh
      · simp [hl] at h1
      simp only [hl, Option.bind_eq_bind, Option.bind_some] at h1
      split_ifs at h1
      obtain ⟨⟨num', ro⟩, -, h1⟩ := Option.bind_eq_some_iff.1 h1
      obtain rfl := (Option.some.inj h1).symm
      by_cases hlh : h = lh
      · subst hlh
        refine .inr ⟨m, List.mem_cons_self, ?_⟩
        rw [log2Strict_eq_some hl, Nat.log_pow (by norm_num)]
      · exact .inl (by simpa [Function.update_of_ne hlh] using h2)
    · exact .inr ⟨m', List.mem_cons_of_mem _ hm', rfl⟩

/-- On the coset of order 2^H, point t of order 2^h is point t of order 2^H, for h <= H. -/
theorem rowPoint_le (G : Gen K) (hN : GenNested G) (g : K) {H h t : ℕ} (hHa : H ≤ G.adicity) (hh : h ≤ H)
    (ht : t < 2 ^ h) : rowPoint G g h t = rowPoint G g H t := by
  obtain ⟨coset, hc⟩ : ∃ c, bitrevCoset G g H = some c :=
    ⟨(List.range (2 ^ H)).map fun r => g * G.gen H ^ bitRev H r, by simp [bitrevCoset, gen_get_of_le G hHa]⟩
  rw [← bitrevCoset_getD G hN g hHa hh ht hc,
    bitrevCoset_getD G hN g hHa le_rfl (lt_of_lt_of_le ht (Nat.pow_le_pow_right (by norm_num) hh)) hc]

/-- The prover's first word, and every reduced vector, is the DEEP codeword on the coset g H.

At log height h it lists D_h(g G_h^rev_h(t)), for D_h the batched DEEP polynomial of the claims there.

This needs honest matrices, and opening points off the coset. -/
theorem reduced_openings_deep (G : Gen K) (hN : GenNested G) (g α : K) (mats : List (MatToOpen K))
    (cols : MatToOpen K → List K[X]) (hhon : ∀ m ∈ mats, HonestMat G g (cols m) m) {H : ℕ}
    (hHmax : (mats.map fun m => Nat.log 2 m.mat.height).max? = some H) (hHa : H ≤ G.adicity)
    (hpow : ∀ m ∈ mats, m.mat.height = 2 ^ Nat.log 2 m.mat.height)
    (h32 : ∀ m ∈ mats, Nat.log 2 m.mat.height ≤ 32)
    (hout : ∀ m ∈ mats, ∀ z ∈ m.points, ∀ r < 2 ^ H, z ≠ rowPoint G g H r)
    {red : List (ℕ × List K)} (h : reduced_openings G g α mats = some red) :
    ∀ e ∈ red, IsCodeword G (onCoset (deepPoly α 0 (proverDeep cols e.1 mats)) g) e.1 e.2 := by
  have hH : ∀ m ∈ mats, Nat.log 2 m.mat.height ≤ H := fun m hm =>
    (List.max?_eq_some_iff.1 hHmax).2 _ (List.mem_map.2 ⟨m, hm, rfl⟩)
  have hw : ∀ m ∈ mats, ∀ zy ∈ m.points.zip m.openings, zy.2.length = m.mat.width := by
    intro m hm zy hzy
    rw [(hhon m hm).openings] at hzy
    have key : ∀ (l : List K) (f : K → List K), zy ∈ l.zip (l.map f) → zy.2 = f zy.1 := by
      intro l f hl
      induction l with
      | nil => simp at hl
      | cons a l ih =>
        rcases List.mem_cons.1 hl with rfl | hl
        · rfl
        · exact ih hl
    rw [key _ _ hzy]
    simp [(hhon m hm).width]
  have spec := fun idx (hidx : idx < 2 ^ H) => reduced_openings_spec G hN g α mats hHmax hHa hpow h32 hw hout h hidx
  intro e he
  have heH : e.1 ≤ H := by
    have hred := h
    unfold reduced_openings at hred
    rw [hHmax] at hred
    simp only [Option.bind_eq_bind, Option.bind_some] at hred
    obtain ⟨coset, -, hred⟩ := Option.bind_eq_some_iff.1 hred
    obtain ⟨⟨num, red'⟩, hfold, hred⟩ := Option.bind_eq_some_iff.1 hred
    obtain rfl := (Option.some.inj hred).symm
    simp only [List.mem_filterMap, Option.map_eq_some_iff] at he
    obtain ⟨h', -, v, hv, rfl⟩ := he
    rcases foldlM_reduceMat_support α _ mats _ _ hfold h' (by simp [hv]) with h0 | ⟨m, hm, rfl⟩
    · exact absurd rfl h0
    · exact hH m hm
  refine ⟨(spec 0 (by positivity) e he).1, fun t ht => ?_⟩
  have hidx : t * 2 ^ (H - e.1) < 2 ^ H := by
    rw [show H = e.1 + (H - e.1) by omega, pow_add]
    exact Nat.mul_lt_mul_of_pos_right ht (by positivity) |>.trans_eq (by rw [Nat.add_sub_cancel_left])
  have hq : t * 2 ^ (H - e.1) / 2 ^ (H - e.1) = t := Nat.mul_div_cancel _ (by positivity)
  have hv := (spec _ hidx e he).2
  rw [hq] at hv
  rw [hv, xOfQuery_eq G g (le_trans heH hHa), hq, proverAllEntries_honest G g cols H _ e.1 mats hhon ?_, hq,
    reducedOpening_eq_deepPoly, eval_onCoset, rowPoint_eq]
  · intro e' he'
    simp only [proverDeep, List.mem_flatMap, List.mem_filter, List.mem_map, decide_eq_true_eq] at he'
    obtain ⟨m, ⟨hm, -⟩, z, hz, rfl⟩ := he'
    rw [rowPoint_le G hN g hHa heH ht]
    exact hout m hm z hz t (lt_of_lt_of_le ht (Nat.pow_le_pow_right (by norm_num) heH))
  · intro m hm
    refine lt_of_lt_of_eq ?_ (hpow m hm).symm
    rw [Nat.div_lt_iff_lt_mul (by positivity), ← pow_add,
      show Nat.log 2 m.mat.height + (H - Nat.log 2 m.mat.height) = H by have := hH m hm; omega]
    exact hidx

/-! ## The verifier's reduction of one query -/

/-- The domain type of a claimed matrix. -/
abbrev Coset (G : Gen K) := p3_field.coset.mirror.TwoAdicMultiplicativeCoset K G.adicity G.gen

/-- The claims at log height h, each point with its matrix's columns. -/
noncomputable def claimDeep {G : Gen K} {C : Type} (b h : ℕ) (cols : MatrixOpening K (Coset G) → List K[X])
    (claims : List (Claim G C)) : List (K × List K[X]) :=
  ((claims.flatMap (·.matrices)).filter fun m => m.domain.log_size + b = h).flatMap fun m =>
    m.points.map fun p => (p.point, cols m)

theorem queryMats_fst {G : Gen K} {C : Type} {claims : List (Claim G C)} {rows : List (List (List K))}
    (h : List.Forall₂ (fun c r => r.length = c.matrices.length) claims rows) :
    (queryMats claims rows).map (·.1) = claims.flatMap (·.matrices) := by
  induction h with
  | nil => rfl
  | cons hcr _ ih =>
    rename_i c r cs rs
    simp only [queryMats, List.zip_cons_cons, List.flatMap_cons, List.map_append] at ih ⊢
    rw [ih, List.map_fst_zip (le_of_eq hcr.symm)]

theorem deepClaims_eq {G : Gen K} (b h : ℕ) (cols : MatrixOpening K (Coset G) → List K[X]) :
    ∀ (mats : List (MatrixOpening K (Coset G) × List K)),
      deepClaims b h cols mats = ((mats.map (·.1)).filter fun m => m.domain.log_size + b = h).flatMap fun m =>
        m.points.map fun p => (p.point, cols m)
  | [] => rfl
  | mr :: mats => by
    by_cases hh : mr.1.domain.log_size + b = h <;>
      simp [deepClaims, hh, ← deepClaims_eq b h cols mats]

/-- The heights seen, in order of first appearance. -/
def keysAfter (keys hs : List ℕ) : List ℕ := hs.foldl (fun ks h => if h ∈ ks then ks else ks ++ [h]) keys

theorem keysAfter_spec : ∀ (hs keys : List ℕ), keys.Nodup →
    (keysAfter keys hs).Nodup ∧ ∀ h, h ∈ keysAfter keys hs ↔ h ∈ keys ∨ h ∈ hs
  | [], keys, hk => ⟨hk, by simp [keysAfter]⟩
  | x :: hs, keys, hk => by
    have hk' : (if x ∈ keys then keys else keys ++ [x]).Nodup := by
      split_ifs with hx
      · exact hk
      · exact List.Nodup.append hk (List.nodup_singleton x) (by simpa using fun h => hx h)
    obtain ⟨h1, h2⟩ := keysAfter_spec hs _ hk'
    refine ⟨h1, fun h => ?_⟩
    rw [show keysAfter keys (x :: hs) = keysAfter (if x ∈ keys then keys else keys ++ [x]) hs from rfl, h2]
    by_cases hx : x ∈ keys
    · simp only [hx, ↓reduceIte, List.mem_cons]
      constructor
      · rintro (hh | hh) <;> simp [hh]
      · rintro (hh | rfl | hh) <;> simp_all
    · simp [hx, or_assoc]

theorem foldlM_eq_pure_foldl {ME IE α β : Type} {f : β → α → Res ME IE β} {F : β → α → β} :
    ∀ (l : List α) (s : β), (∀ s, ∀ x ∈ l, f s x = pure (F s x)) → l.foldlM f s = pure (l.foldl F s)
  | [], _, _ => rfl
  | x :: l, s, h => by
    rw [List.foldlM_cons, h s x List.mem_cons_self, pure_bind,
      foldlM_eq_pure_foldl l _ fun s y hy => h s y (List.mem_cons_of_mem _ hy)]
    rfl

/-- One matrix of one query never panics or rejects on rows of the right length off the query point. -/
theorem reduceMatrix_ok {ME IE : Type} (G : Gen K) (g : K) (b H : ℕ) (α : K) (index : ℕ) (st : RedState K)
    (m : MatrixOpening K (Coset G)) (row : List K) {x : K}
    (hx : queryPoint G g H (m.domain.log_size + b) index = some x)
    (hp : ∀ p ∈ m.points, row.length = p.values.length ∧ p.point - x ≠ 0) :
    ∃ acc offs, reduceMatrix (ME := ME) (IE := IE) G g b H α index st (m, row) =
      pure (acc, (if m.domain.log_size + b ∈ st.2.1 then st.2.1 else st.2.1 ++ [m.domain.log_size + b]), offs) := by
  obtain ⟨acc, keys, offs⟩ := st
  unfold reduceMatrix
  simp only [hx, lift, lift_some_bind]
  rw [foldlM_eq_pure_foldl (F := fun (st2 : (ℕ → K) × List ℕ) p =>
    (Function.update st2.1 (m.domain.log_size + b)
      (st2.1 (m.domain.log_size + b) + pointTerm α x (st2.2.headD 0) p row), st2.2.drop 1)) _ _ ?_, pure_bind]
  · exact ⟨_, _, rfl⟩
  · intro st2 p hpm
    obtain ⟨h1, h2⟩ := hp p hpm
    obtain ⟨a, o⟩ := st2
    simp [h1, h2]

theorem foldlM_reduceMatrix_ok {ME IE : Type} (G : Gen K) (g : K) (b H : ℕ) (α : K) (index : ℕ) :
    ∀ (mats : List (MatrixOpening K (Coset G) × List K)),
      (∀ mr ∈ mats, ∃ x, queryPoint G g H (mr.1.domain.log_size + b) index = some x ∧
        ∀ p ∈ mr.1.points, mr.2.length = p.values.length ∧ p.point - x ≠ 0) →
      ∀ st : RedState K, ∃ res, mats.foldlM (reduceMatrix (ME := ME) (IE := IE) G g b H α index) st = pure res ∧
        res.2.1 = keysAfter st.2.1 (mats.map fun mr => mr.1.domain.log_size + b)
  | [], _, st => ⟨st, rfl, rfl⟩
  | mr :: mats, hok, st => by
    obtain ⟨x, hx, hp⟩ := hok mr List.mem_cons_self
    obtain ⟨acc, offs, h1⟩ := reduceMatrix_ok (ME := ME) (IE := IE) G g b H α index st mr.1 mr.2 hx hp
    obtain ⟨res, h2, h3⟩ := foldlM_reduceMatrix_ok G g b H α index mats
      (fun m hm => hok m (List.mem_cons_of_mem _ hm))
      (acc, (if mr.1.domain.log_size + b ∈ st.2.1 then st.2.1 else st.2.1 ++ [mr.1.domain.log_size + b]), offs)
    refine ⟨res, ?_, by rw [h3]; rfl⟩
    rw [List.foldlM_cons, h1, pure_bind, h2]

/-- The batched DEEP polynomial of constant columns is zero. -/
theorem deepPoly_const (α : K) : ∀ (off : ℕ) (L : List (K × List K[X])), (∀ e ∈ L, ∀ f ∈ e.2, f.degree ≤ 0) →
    deepPoly α off L = 0
  | _, [], _ => rfl
  | off, (z, fs) :: L, hL => by
    rw [deepPoly, deepPoly_const α _ L fun e he => hL e (List.mem_cons_of_mem _ he), add_zero]
    refine Finset.sum_eq_zero fun i hi => ?_
    have hf := hL _ List.mem_cons_self (fs.getD i 0)
      (by rw [List.getD_eq_getElem _ _ (by simpa using hi)]; exact List.getElem_mem _)
    rw [eq_C_of_degree_le_zero hf, deepQuot_C, mul_zero]

/-- The verifier's reduction of one query, on honest openings, is the DEEP word at every height.

At each height h of the claims, tallest first, it returns D_h at the query point of that height.

This needs four facts:

- the opened rows are the columns at the query point
- the claimed values are the columns at their points, none equal to the query point
- every height lies within the adicity
- every column has degree below its matrix's height. -/
theorem reduceQuery_eq_deep {ME IE : Type} (G : Gen K) (g : K) {C : Type} (b H : ℕ) (α : K)
    (claims : List (Claim G C)) (rows : List (List (List K))) (index : ℕ)
    (cols : MatrixOpening K (Coset G) → List K[X])
    (halign : List.Forall₂ (fun c r => r.length = c.matrices.length) claims rows)
    (hrow : ∀ mr ∈ queryMats claims rows,
      mr.2 = (cols mr.1).map (·.eval (xOfQuery G g H index (mr.1.domain.log_size + b))))
    (hval : ∀ c ∈ claims, ∀ m ∈ c.matrices, ∀ p ∈ m.points, p.values = (cols m).map (·.eval p.point))
    (hz : ∀ c ∈ claims, ∀ m ∈ c.matrices, ∀ p ∈ m.points, p.point ≠ xOfQuery G g H index (m.domain.log_size + b))
    (hHa : ∀ c ∈ claims, ∀ m ∈ c.matrices, m.domain.log_size + b ≤ G.adicity)
    (hdeg : ∀ c ∈ claims, ∀ m ∈ c.matrices, ∀ f ∈ cols m, f.degree < ↑(2 ^ m.domain.log_size)) :
    reduceQuery (ME := ME) (IE := IE) G g b H α claims rows index =
      pure ((inputLogHeights b claims).map fun h =>
        (h, (deepPoly α 0 (claimDeep b h cols claims)).eval (xOfQuery G g H index h))) := by
  have hmem : ∀ mr ∈ queryMats claims rows, ∃ c ∈ claims, mr.1 ∈ c.matrices := by
    intro mr hmr
    have := List.mem_map_of_mem (f := (·.1)) hmr
    rw [queryMats_fst halign, List.mem_flatMap] at this
    exact this
  have hval' : ∀ mr ∈ queryMats claims rows, ∀ p ∈ mr.1.points, p.values = (cols mr.1).map (·.eval p.point) :=
    fun mr hmr => let ⟨c, hc, hm⟩ := hmem mr hmr; hval c hc mr.1 hm
  have hz' : ∀ mr ∈ queryMats claims rows, ∀ p ∈ mr.1.points,
      p.point ≠ xOfQuery G g H index (mr.1.domain.log_size + b) :=
    fun mr hmr => let ⟨c, hc, hm⟩ := hmem mr hmr; hz c hc mr.1 hm
  -- The fold over the matrices succeeds, and records every height once.
  obtain ⟨⟨acc, keys, offs'⟩, hfold, hkeys⟩ := foldlM_reduceMatrix_ok (ME := ME) (IE := IE) G g b H α index
    (queryMats claims rows) (fun mr hmr => by
      obtain ⟨c, hc, hm⟩ := hmem mr hmr
      refine ⟨xOfQuery G g H index (mr.1.domain.log_size + b), by
        simp [xOfQuery, queryPoint, gen_get_of_le G (hHa c hc mr.1 hm)], fun p hp => ⟨?_, ?_⟩⟩
      · rw [hrow mr hmr, hval' mr hmr p hp, List.length_map, List.length_map]
      · exact sub_ne_zero.2 (hz' mr hmr p hp))
    (fun _ => 0, [], ladderOffsets (openingPoints b claims))
  have hfold' := hfold
  rw [ladderOffsets_eq, ← matsPoints_queryMats b halign, ← List.append_nil (ladderFrom _ _)] at hfold'
  have hacc := reduceMatrices_spec G g b H α index _ _ _ _ _ _ hfold'
  simp only at hacc hkeys
  -- The value at each height is the DEEP polynomial there.
  have hval_h : ∀ h, acc h = (deepPoly α 0 (claimDeep b h cols claims)).eval (xOfQuery G g H index h) := by
    intro h
    rw [hacc, foldl_ladderStep, matsEntries_honest b h _ cols _ hrow hval', zero_add,
      reducedOpening_eq_deepPoly, deepClaims_eq, queryMats_fst halign]
    · rfl
    · intro e he
      rw [deepClaims_eq, queryMats_fst halign] at he
      simp only [List.mem_flatMap, List.mem_filter, List.mem_map, List.mem_flatMap, decide_eq_true_eq] at he
      obtain ⟨m, ⟨⟨c, hc, hm⟩, hh⟩, p, hp, rfl⟩ := he
      rw [← hh]; exact hz c hc m hm p hp
  -- The blowup height carries only constant columns, so its value is zero.
  have hb : acc b = 0 := by
    rw [hval_h, deepPoly_const, eval_zero]
    intro e he f hf
    simp only [claimDeep, List.mem_flatMap, List.mem_filter, List.mem_map, decide_eq_true_eq] at he
    obtain ⟨m, ⟨hm, hh⟩, p, -, rfl⟩ := he
    obtain ⟨c, hc, hm⟩ := hm
    have := hdeg c hc m hm f hf
    rw [show m.domain.log_size = 0 by omega] at this
    exact Nat.WithBot.lt_one_iff_le_zero.1 (by simpa using this)
  -- The heights are those of the claims, tallest first.
  have hsorted : (keys.mergeSort fun a b => decide (b ≤ a)) = inputLogHeights b claims := by
    obtain ⟨hnd, hm⟩ := keysAfter_spec ((queryMats claims rows).map fun mr => mr.1.domain.log_size + b) [] List.nodup_nil
    rw [← hkeys] at hnd hm
    refine eq_of_pairwise_gt ?_ (inputLogHeights_pairwise b claims) fun h => ?_
    · have hs := List.pairwise_mergeSort (le := fun a b : ℕ => decide (b ≤ a))
        (fun a b c h1 h2 => by simp only [decide_eq_true_eq] at *; omega)
        (fun a b => by simp only [Bool.or_eq_true, decide_eq_true_eq]; omega) keys
      exact List.Pairwise.imp_of_mem (fun {a b} _ _ h => by simp only [decide_eq_true_eq] at h; omega)
        (List.Pairwise.and hs ((List.mergeSort_perm keys _).nodup_iff.2 hnd))
    · rw [List.mem_mergeSort, hm, mem_inputLogHeights]
      simp only [List.not_mem_nil, false_or, List.mem_map]
      constructor
      · rintro ⟨mr, hmr, rfl⟩
        obtain ⟨c, hc, hm⟩ := hmem mr hmr
        exact ⟨c, hc, mr.1, hm, rfl⟩
      · rintro ⟨c, hc, m, hm, rfl⟩
        have : m ∈ (queryMats claims rows).map (·.1) := by
          rw [queryMats_fst halign]; exact List.mem_flatMap.2 ⟨c, hc, hm⟩
        obtain ⟨mr, hmr, rfl⟩ := List.mem_map.1 this
        exact ⟨mr, hmr, rfl⟩
  unfold reduceQuery
  dsimp only
  rw [show (claims.zip rows).flatMap (fun cr => cr.1.matrices.zip cr.2) = queryMats claims rows from rfl, hfold,
    pure_bind]
  simp only [hb, ne_eq, not_true_eq_false, and_false, ↓reduceIte, hsorted]
  exact congrArg pure (List.map_congr_left fun h _ => by rw [hval_h])

/-! ## The honest commit phase -/

/-- The polynomial a round passes on: fold(P, 2^a, beta), plus beta^(2^a) times the input at the folded height. -/
noncomputable def nextPoly (inp : ℕ → Option K[X]) (lh : ℕ) (P : K[X]) (β : K) (a : ℕ) : K[X] :=
  polyFold P (2 ^ a) β + C (β ^ 2 ^ a) * (inp (lh - a)).getD 0

/-- The honest rounds from log height lh and polynomial P, at the given challenges, arities and siblings:

- each round commits the word of the running polynomial
- an input at the folded height is rolled in with its word. -/
noncomputable def honestRds (G : Gen K) (inp : ℕ → Option K[X]) : ℕ → K[X] → List (K × ℕ × List (List K)) → List (Rd K)
  | _, _, [] => []
  | lh, P, (β, a, sv) :: rest =>
    ⟨β, a, word G P lh, (inp (lh - a)).map (word G · (lh - a)), sv⟩ ::
      honestRds G inp (lh - a) (nextPoly inp lh P β a) rest

/-- The last running polynomial of the honest rounds. -/
noncomputable def honestFinal (inp : ℕ → Option K[X]) : ℕ → K[X] → List (K × ℕ × List (List K)) → K[X]
  | _, P, [] => P
  | lh, P, (β, a, _) :: rest => honestFinal inp (lh - a) (nextPoly inp lh P β a) rest

/-- The siblings of query q at index idx are, in every round, its row without the queried value. -/
def HonestSiblings (G : Gen K) (inp : ℕ → Option K[X]) (q : ℕ) :
    ℕ → ℕ → K[X] → List (K × ℕ × List (List K)) → Prop
  | _, _, _, [] => True
  | lh, idx, P, (β, a, sv) :: rest =>
    sv[q]? = some ((rowList (word G P lh) a (idx / 2 ^ a)).eraseIdx (idx % 2 ^ a)) ∧
      HonestSiblings G inp q (lh - a) (idx / 2 ^ a) (nextPoly inp lh P β a) rest

theorem honestRds_map (G : Gen K) (inp : ℕ → Option K[X]) :
    ∀ (lh : ℕ) (P : K[X]) (rounds : List (K × ℕ × List (List K))),
      (honestRds G inp lh P rounds).map Rd.β = rounds.map (·.1) ∧
      (honestRds G inp lh P rounds).map Rd.a = rounds.map (·.2.1) ∧
      (honestRds G inp lh P rounds).map Rd.sv = rounds.map (·.2.2)
  | _, _, [] => ⟨rfl, rfl, rfl⟩
  | lh, P, (β, a, sv) :: rest => by
    obtain ⟨h1, h2, h3⟩ := honestRds_map G inp (lh - a) (nextPoly inp lh P β a) rest
    simp [honestRds, h1, h2, h3]

theorem totalA_honestRds (G : Gen K) (inp : ℕ → Option K[X]) (lh : ℕ) (P : K[X])
    (rounds : List (K × ℕ × List (List K))) :
    totalA (honestRds G inp lh P rounds) = (rounds.map (·.2.1)).sum := by
  rw [totalA, (honestRds_map G inp lh P rounds).2.1]

/-- The honest rounds form an honest chain, for every query whose siblings are honest. -/
theorem honestRds_chain (G : Gen K) (inp : ℕ → Option K[X]) (q : ℕ) :
    ∀ (lh idx : ℕ) (P : K[X]) (rounds : List (K × ℕ × List (List K))),
      (∀ r ∈ rounds, 1 ≤ r.2.1) → (rounds.map (·.2.1)).sum ≤ lh → lh ≤ G.adicity → idx < 2 ^ lh →
      HonestSiblings G inp q lh idx P rounds →
      HonestChain G q lh idx (honestRds G inp lh P rounds)
        (word G (honestFinal inp lh P rounds) (lh - (rounds.map (·.2.1)).sum)) P
  | lh, idx, P, [], _, _, hla, hidx, _ => ⟨hla, by simpa [honestFinal] using word_isCodeword G P lh, hidx⟩
  | lh, idx, P, (β, a, sv) :: rest, ha, hsum, hla, hidx, ⟨hsv, hrest⟩ => by
    simp only [List.map_cons, List.sum_cons] at hsum
    have ha1 : 1 ≤ a := ha _ List.mem_cons_self
    have hidx' : idx / 2 ^ a < 2 ^ (lh - a) := by
      rw [Nat.div_lt_iff_lt_mul (by positivity), ← pow_add, Nat.sub_add_cancel (by omega)]; exact hidx
    have ih := honestRds_chain G inp q (lh - a) (idx / 2 ^ a) (nextPoly inp lh P β a) rest
      (fun r hr => ha r (List.mem_cons_of_mem _ hr)) (by omega) (by omega) hidx' hrest
    refine ⟨ha1, show a ≤ lh by omega, hla, word_isCodeword G P lh, hidx, hsv, (inp (lh - a)).getD 0, ?_, ?_⟩
    · rcases inp (lh - a) with _ | R
      · rfl
      · exact word_isCodeword G R (lh - a)
    · simpa [honestRds, honestFinal, Nat.sub_sub, nextPoly] using ih

/-- The inputs the honest rounds roll in, each at its height and shifted index. -/
def chainRolls (G : Gen K) (inp : ℕ → Option K[X]) : ℕ → ℕ → List (K × ℕ × List (List K)) → List (ℕ × K)
  | _, _, [] => []
  | lh, idx, (_, a, _) :: rest =>
    (match inp (lh - a) with
      | some R => [(lh - a, R.eval (dom G (lh - a) (idx / 2 ^ a)))]
      | none => []) ++ chainRolls G inp (lh - a) (idx / 2 ^ a) rest

theorem rolls_honestRds (G : Gen K) (inp : ℕ → Option K[X]) :
    ∀ (lh idx : ℕ) (P : K[X]) (rounds : List (K × ℕ × List (List K))),
      (rounds.map (·.2.1)).sum ≤ lh → idx < 2 ^ lh →
      rolls (honestRds G inp lh P rounds) lh idx = chainRolls G inp lh idx rounds
  | _, _, _, [], _, _ => rfl
  | lh, idx, P, (β, a, sv) :: rest, hsum, hidx => by
    simp only [List.map_cons, List.sum_cons] at hsum
    have hidx' : idx / 2 ^ a < 2 ^ (lh - a) := by
      rw [Nat.div_lt_iff_lt_mul (by positivity), ← pow_add, Nat.sub_add_cancel (by omega)]; exact hidx
    simp only [honestRds, rolls, chainRolls]
    rw [rolls_honestRds G inp (lh - a) (idx / 2 ^ a) _ rest (by omega) hidx']
    congr 1
    rcases inp (lh - a) with _ | R
    · rfl
    · simp only [Option.map_some]
      rw [word, getD_map_range _ hidx']

/-- The rolled-in inputs of the honest rounds:

- their heights strictly decrease, below the start
- each value is its input at the shifted index
- a height appears exactly when an input sits there and some round ends there. -/
theorem chainRolls_spec (G : Gen K) (inp : ℕ → Option K[X]) :
    ∀ (lh idx : ℕ) (rounds : List (K × ℕ × List (List K))),
      (∀ r ∈ rounds, 1 ≤ r.2.1) → (rounds.map (·.2.1)).sum ≤ lh →
      ((chainRolls G inp lh idx rounds).map (·.1)).Pairwise (· > ·) ∧
      (∀ e ∈ chainRolls G inp lh idx rounds, e.1 < lh ∧ ∃ R, inp e.1 = some R ∧
        e.2 = R.eval (dom G e.1 (idx / 2 ^ (lh - e.1)))) ∧
      ∀ h, h ∈ (chainRolls G inp lh idx rounds).map (·.1) ↔
        (inp h).isSome ∧ ∃ r, 1 ≤ r ∧ r ≤ rounds.length ∧ lh - ((rounds.map (·.2.1)).take r).sum = h
  | _, _, [], _, _ => ⟨by simp [chainRolls], by simp [chainRolls], fun h => by simp [chainRolls]⟩
  | lh, idx, (β, a, sv) :: rest, ha, hsum => by
    simp only [List.map_cons, List.sum_cons] at hsum
    have ha1 : 1 ≤ a := ha _ List.mem_cons_self
    obtain ⟨ih1, ih2, ih3⟩ := chainRolls_spec G inp (lh - a) (idx / 2 ^ a) rest
      (fun r hr => ha r (List.mem_cons_of_mem _ hr)) (by omega)
    have hdiv : ∀ e : ℕ × K, e.1 < lh - a → idx / 2 ^ a / 2 ^ (lh - a - e.1) = idx / 2 ^ (lh - e.1) := by
      intro e he
      rw [Nat.div_div_eq_div_mul, ← pow_add, show a + (lh - a - e.1) = lh - e.1 by omega]
    refine ⟨?_, ?_, fun h => ?_⟩
    · simp only [chainRolls, List.map_append]
      refine List.pairwise_append.2 ⟨by rcases inp (lh - a) <;> simp, ih1, fun x hx y hy => ?_⟩
      have hx' : x = lh - a := by rcases h : inp (lh - a) <;> simp_all
      obtain ⟨e, he, rfl⟩ := List.mem_map.1 hy
      have := (ih2 e he).1
      omega
    · intro e he
      simp only [chainRolls, List.mem_append] at he
      rcases he with he | he
      · rcases hR : inp (lh - a) with _ | R <;> rw [hR] at he
        · simp at he
        · simp only [List.mem_singleton] at he
          subst he
          exact ⟨by omega, R, hR, by simp [show lh - (lh - a) = a by omega]⟩
      · obtain ⟨hlt, R, hR, he2⟩ := ih2 e he
        exact ⟨by omega, R, hR, by rw [he2, hdiv e hlt]⟩
    · simp only [chainRolls, List.map_append, List.mem_append, ih3, List.length_cons]
      constructor
      · rintro (hh | ⟨hs, r, hr1, hr2, hr3⟩)
        · rcases hR : inp (lh - a) with _ | R <;> rw [hR] at hh
          · simp at hh
          · simp only [List.map_cons, List.map_nil, List.mem_singleton] at hh
            subst hh
            exact ⟨by simp [hR], 1, le_rfl, by omega, by simp⟩
        · refine ⟨hs, r + 1, by omega, by omega, ?_⟩
          simp only [List.map_cons, List.take_succ_cons, List.sum_cons]; omega
      · rintro ⟨hs, r, hr1, hr2, hr3⟩
        rcases r with _ | r
        · omega
        rcases r with _ | r
        · left
          simp only [List.map_cons, List.take_succ_cons, List.take_zero, List.sum_cons, List.sum_nil,
            add_zero] at hr3
          subst hr3
          obtain ⟨R, hR⟩ := Option.isSome_iff_exists.1 hs
          simp [hR]
        · right
          refine ⟨hs, r + 1, by omega, by omega, ?_⟩
          simp only [List.map_cons, List.take_succ_cons, List.sum_cons] at hr3; omega

/-- Folding keeps low degree: if P has degree below 2^(lh - b) and every input below 2^(h - b),
the last running polynomial has degree below 2^(lh - s - b), for s the total arity. -/
theorem degree_honestFinal (inp : ℕ → Option K[X]) (b : ℕ)
    (hinp : ∀ h R, inp h = some R → R.degree < ↑(2 ^ (h - b))) :
    ∀ (lh : ℕ) (P : K[X]) (rounds : List (K × ℕ × List (List K))),
      b + (rounds.map (·.2.1)).sum ≤ lh → P.degree < ↑(2 ^ (lh - b)) →
      (honestFinal inp lh P rounds).degree < ↑(2 ^ (lh - (rounds.map (·.2.1)).sum - b))
  | _, _, [], _, hP => by simpa [honestFinal] using hP
  | lh, P, (β, a, sv) :: rest, hsum, hP => by
    simp only [List.map_cons, List.sum_cons] at hsum ⊢
    rw [show lh - (a + (rest.map (·.2.1)).sum) - b = lh - a - (rest.map (·.2.1)).sum - b by omega]
    refine degree_honestFinal inp b hinp (lh - a) _ rest (by omega) ?_
    have h1 : (polyFold P (2 ^ a) β).degree < ↑(2 ^ (lh - a - b)) :=
      degree_polyFold_lt (a := 2 ^ a) (d := 2 ^ (lh - a - b))
        (by rw [← pow_add, show a + (lh - a - b) = lh - b by omega]; exact hP) β
    have h2 : (C (β ^ 2 ^ a) * (inp (lh - a)).getD 0).degree < ↑(2 ^ (lh - a - b)) := by
      rw [C_mul']
      refine lt_of_le_of_lt (degree_smul_le _ _) ?_
      rcases hR : inp (lh - a) with _ | R
      · simp only [Option.getD_none, degree_zero]; exact WithBot.bot_lt_coe _
      · exact hinp _ R hR
    exact lt_of_le_of_lt (degree_add_le _ _) (max_lt h1 h2)

theorem nextWord_honestRds (G : Gen K) (inp : ℕ → Option K[X]) (lh : ℕ) (P : K[X])
    (rounds : List (K × ℕ × List (List K))) {i : ℕ} (hi : i < 2 ^ lh) :
    (nextWord (honestRds G inp lh P rounds)
      (word G (honestFinal inp lh P rounds) (lh - (rounds.map (·.2.1)).sum))).getD i 0 = P.eval (dom G lh i) := by
  rcases rounds with _ | ⟨⟨β, a, sv⟩, rest⟩
  · simp only [honestRds, nextWord, honestFinal, List.map_nil, List.sum_nil, Nat.sub_zero]
    rw [word, getD_map_range _ hi]
  · simp only [honestRds, nextWord]
    rw [word, getD_map_range _ hi]

/-! ## The DEEP inputs of the claims -/

/-- D_h(g X), for D_h the batched DEEP polynomial of the claims at log height h. -/
noncomputable def deepOn {G : Gen K} {C : Type} (g α : K) (b : ℕ) (cols : MatrixOpening K (Coset G) → List K[X])
    (claims : List (Claim G C)) (h : ℕ) : K[X] :=
  onCoset (deepPoly α 0 (claimDeep b h cols claims)) g

/-- The input at log height h, when the claims have a matrix there. -/
noncomputable def deepInput {G : Gen K} {C : Type} (g α : K) (b : ℕ) (cols : MatrixOpening K (Coset G) → List K[X])
    (claims : List (Claim G C)) (h : ℕ) : Option K[X] :=
  if h ∈ inputLogHeights b claims then some (deepOn g α b cols claims h) else none

/-- Each DEEP input has degree below 2^(h - b) when every column has degree below its matrix's height. -/
theorem degree_deepOn {G : Gen K} {C : Type} (g α : K) (b : ℕ) (cols : MatrixOpening K (Coset G) → List K[X])
    (claims : List (Claim G C))
    (hdeg : ∀ c ∈ claims, ∀ m ∈ c.matrices, ∀ f ∈ cols m, f.degree < ↑(2 ^ m.domain.log_size)) (h : ℕ) :
    (deepOn g α b cols claims h).degree < ↑(2 ^ (h - b)) := by
  refine lt_of_le_of_lt (degree_onCoset_le _ g) (degree_deepPoly_lt α (WithBot.bot_lt_coe _) 0 _ ?_)
  intro e he f hf
  simp only [claimDeep, List.mem_flatMap, List.mem_filter, List.mem_map, decide_eq_true_eq] at he
  obtain ⟨m, ⟨⟨c, hc, hm⟩, hh⟩, p, -, rfl⟩ := he
  rw [← hh, Nat.add_sub_cancel]
  exact hdeg c hc m hm f hf

/-- The honest rounds roll in exactly the inputs below the tallest height, tallest first.

This needs the schedule's arities, and every input at or above the final height. -/
theorem chainRolls_eq_inputs {G : Gen K} {C : Type} (g α : K) (b : ℕ)
    (cols : MatrixOpening K (Coset G) → List K[X]) (claims : List (Claim G C)) {F A : ℕ} (hA : 0 < A)
    {L : List ℕ} (hL : fold_schedule (inputLogHeights b claims) F A = some L)
    (hF : ∀ h ∈ inputLogHeights b claims, F ≤ h) (rounds : List (K × ℕ × List (List K)))
    (hr : rounds.map (·.2.1) = L) (idx : ℕ) :
    chainRolls G (deepInput g α b cols claims) ((inputLogHeights b claims).headD 0) idx rounds =
      (inputLogHeights b claims).tail.map fun h =>
        (h, (deepOn g α b cols claims h).eval (dom G h (idx / 2 ^ ((inputLogHeights b claims).headD 0 - h)))) := by
  have hS := inputLogHeights_pairwise b claims
  rcases hSc : inputLogHeights b claims with _ | ⟨H, T⟩
  · rw [hSc] at hL
    simp only [fold_schedule, List.isChain_nil, not_true_eq_false, ↓reduceIte, Option.some.injEq] at hL
    subst hL
    rw [List.map_eq_nil_iff] at hr
    subst hr
    rfl
  rw [hSc] at hL hF hS
  simp only [List.headD_cons, List.tail_cons]
  have hTH : ∀ h ∈ T, h < H := fun h hh => List.rel_of_pairwise_cons hS hh
  have hinp : ∀ h, (deepInput g α b cols claims h).isSome ↔ h ∈ H :: T := by
    intro h; simp [deepInput, hSc]
  -- The schedule's arities, and the heights the descent reaches.
  obtain ⟨hpos, hsum, hreach⟩ : (∀ a ∈ L, 1 ≤ a) ∧ L.sum ≤ H ∧
      ∀ h ∈ T, ∃ r, 1 ≤ r ∧ r ≤ L.length ∧ H - (L.take r).sum = h := by
    rcases Nat.lt_or_ge F H with hFH | hFH
    · obtain ⟨L', hL', ha, hs, hre⟩ := fold_schedule_spec hS.isChain hA hFH
      obtain rfl := Option.some.inj (hL.symm.trans hL')
      refine ⟨fun a h => (ha a h).1, by omega, fun h hh => ?_⟩
      obtain ⟨r, hr1, hr2⟩ := hre h (List.mem_cons_of_mem _ hh) (hF h (List.mem_cons_of_mem _ hh))
      rcases r with _ | r
      · simp at hr2; have := hTH h hh; omega
      · exact ⟨r + 1, by omega, hr1, hr2⟩
    · obtain rfl : L = [] := Option.some.inj (hL.symm.trans (fold_schedule_nil hS.isChain (by simpa using hFH)))
      refine ⟨by simp, by simp, fun h hh => ?_⟩
      have := hTH h hh; have := hF h (List.mem_cons_of_mem _ hh); omega
  have hpos' : ∀ r ∈ rounds, 1 ≤ r.2.1 := fun r hr' => hpos _ (hr ▸ List.mem_map_of_mem hr')
  obtain ⟨h1, h2, h3⟩ := chainRolls_spec G (deepInput g α b cols claims) H idx rounds hpos' (by rw [hr]; exact hsum)
  set ro := chainRolls G (deepInput g α b cols claims) H idx rounds
  have hkeys : ro.map (·.1) = T := by
    refine eq_of_pairwise_gt h1 hS.of_cons fun h => ?_
    rw [h3, hinp, hr, show rounds.length = L.length by rw [← hr, List.length_map]]
    constructor
    · rintro ⟨hm, r, hr1, hr2, rfl⟩
      rcases List.mem_cons.1 hm with he | he
      · exfalso
        have : 1 ≤ (L.take r).sum := by
          obtain ⟨a, ha⟩ : ∃ a, L.take r = a :: (L.take r).tail := by
            cases L with
            | nil => simp at hr2; omega
            | cons x L => exact ⟨x, by cases r <;> simp_all⟩
          rw [ha, List.sum_cons]
          have := hpos a (List.mem_of_mem_take (ha ▸ List.mem_cons_self))
          omega
        have : (L.take r).sum ≤ L.sum := (List.take_sublist r L).sum_le_sum (fun _ _ => Nat.zero_le _)
        omega
      · exact he
    · intro hh
      exact ⟨List.mem_cons_of_mem _ hh, hreach h hh⟩
  calc ro = ro.map fun e => (e.1, (deepOn g α b cols claims e.1).eval (dom G e.1 (idx / 2 ^ (H - e.1)))) := by
        refine (List.map_id _).symm.trans (List.map_congr_left fun e he => ?_)
        obtain ⟨-, R, hR, he2⟩ := h2 e he
        have : R = deepOn g α b cols claims e.1 := by
          unfold deepInput at hR; split_ifs at hR; exact (Option.some.inj hR).symm
        exact Prod.ext rfl (by simp only [id, he2, this])
    _ = _ := by rw [← hkeys, List.map_map]; rfl

/-! ## The input checks on honest openings -/

theorem forall₂_mem_zip {α β : Type _} {R : α → β → Prop} :
    ∀ {l1 : List α} {l2 : List β}, List.Forall₂ R l1 l2 → ∀ p ∈ l1.zip l2, R p.1 p.2
  | _, _, .nil, _, hp => by simp at hp
  | _, _, .cons h hs, p, hp => by
    rcases List.mem_cons.1 hp with rfl | hp
    · exact h
    · exact forall₂_mem_zip hs p hp

theorem forall₂_mem_zip_swap {α β : Type _} {R : α → β → Prop} :
    ∀ {l1 : List α} {l2 : List β}, List.Forall₂ R l1 l2 → ∀ p ∈ l2.zip l1, R p.2 p.1
  | _, _, .nil, _, hp => by simp at hp
  | _, _, .cons h hs, p, hp => by
    rcases List.mem_cons.1 hp with rfl | hp
    · exact h
    · exact forall₂_mem_zip_swap hs p hp

/-- Honest input openings at the query indices:

- one opening per batch, with one row set per query
- the row of a matrix at query q is its columns at the query point of its height. -/
structure HonestOpenings (G : Gen K) (g : K) {C MP : Type} (b H : ℕ)
    (cols : MatrixOpening K (Coset G) → List K[X]) (claims : List (Claim G C)) (indices : List ℕ)
    (openings : List (BatchMultiOpening K MP)) : Prop where
  batches : openings.length = claims.length
  queries : ∀ bo ∈ openings, bo.opened_values.length = indices.length
  rows : ∀ q (hq : q < indices.length), List.Forall₂ (fun c bo => List.Forall₂
    (fun m row => row = (cols m).map (·.eval (xOfQuery G g H indices[q] (m.domain.log_size + b))))
    c.matrices (bo.opened_values.getD q [])) claims openings

/-- On honest openings, the input checks pass and leave, for each query index i, the DEEP word at every height:

```text
    (h, D_h(g G_h^rev_h(i >> (H - h)))),   h = the input heights, tallest first
```
-/
theorem open_inputs_deep {ME : Type} (G : Gen K) (hN : GenNested G) (g : K) {C : Type} (mmcs : MmcsOps K)
    (b : ℕ) (indices : List ℕ) (openings : List (BatchMultiOpening K mmcs.MultiProof)) (α : K)
    (claims : List (Claim G C)) (commit_of : C → mmcs.Commitment)
    (cols : MatrixOpening K (Coset G) → List K[X])
    (hHa : (inputLogHeights b claims).headD 0 ≤ G.adicity)
    (hidx : ∀ i ∈ indices, i < 2 ^ (inputLogHeights b claims).headD 0)
    (hon : HonestOpenings G g b ((inputLogHeights b claims).headD 0) cols claims indices openings)
    (hmmcs : ∀ bc ∈ openings.zip claims, ∀ dims reduced,
      mmcs.verify_multi_batch (commit_of bc.2.commitment) dims reduced bc.1.opened_values bc.1.opening_proof = .ok ())
    (hpts : ∀ c ∈ claims, ∀ m ∈ c.matrices, m.points ≠ [])
    (hval : ∀ c ∈ claims, ∀ m ∈ c.matrices, ∀ p ∈ m.points, p.values = (cols m).map (·.eval p.point))
    (hout : ∀ c ∈ claims, ∀ m ∈ c.matrices, ∀ p ∈ m.points, ∀ r < 2 ^ (inputLogHeights b claims).headD 0,
      p.point ≠ rowPoint G g ((inputLogHeights b claims).headD 0) r)
    (hdeg : ∀ c ∈ claims, ∀ m ∈ c.matrices, ∀ f ∈ cols m, f.degree < ↑(2 ^ m.domain.log_size)) :
    open_inputs (ME := ME) G g mmcs b ((inputLogHeights b claims).headD 0) indices openings α claims commit_of =
      pure (indices.map fun i => (inputLogHeights b claims).map fun h =>
        (h, (deepOn g α b cols claims h).eval
          (dom G h (i / 2 ^ ((inputLogHeights b claims).headD 0 - h))))) := by
  set H := (inputLogHeights b claims).headD 0 with hHdef
  -- Every claimed height lies at or below the tallest one.
  have hle : ∀ c ∈ claims, ∀ m ∈ c.matrices, m.domain.log_size + b ≤ H := by
    intro c hc m hm
    have hmem := (mem_inputLogHeights b claims _).2 ⟨c, hc, m, hm, rfl⟩
    rcases hS : inputLogHeights b claims with _ | ⟨H', T⟩
    · rw [hS] at hmem; simp at hmem
    · have hp := inputLogHeights_pairwise b claims
      rw [hS] at hmem hp
      rw [hHdef, hS, List.headD_cons]
      rcases List.mem_cons.1 hmem with h | h
      · omega
      · exact le_of_lt (List.rel_of_pairwise_cons hp h)
  have hHa' : ∀ c ∈ claims, ∀ m ∈ c.matrices, m.domain.log_size + b ≤ G.adicity :=
    fun c hc m hm => (hle c hc m hm).trans hHa
  -- The query point of every height is a point of the tallest coset.
  have hxq : ∀ i < 2 ^ H, ∀ h ≤ H, xOfQuery G g H i h = rowPoint G g H (i / 2 ^ (H - h)) ∧ i / 2 ^ (H - h) < 2 ^ h := by
    intro i hi h hh
    have hlt : i / 2 ^ (H - h) < 2 ^ h := by
      rw [Nat.div_lt_iff_lt_mul (by positivity), ← pow_add, show h + (H - h) = H by omega]; exact hi
    exact ⟨by rw [xOfQuery_eq G g (hh.trans hHa), rowPoint_le G hN g hHa hh hlt], hlt⟩
  have hz : ∀ i ∈ indices, ∀ c ∈ claims, ∀ m ∈ c.matrices, ∀ p ∈ m.points,
      p.point ≠ xOfQuery G g H i (m.domain.log_size + b) := by
    intro i hi c hc m hm p hp
    obtain ⟨hx, hlt⟩ := hxq i (hidx i hi) _ (hle c hc m hm)
    rw [hx]
    exact hout c hc m hm p hp _ (lt_of_lt_of_le hlt (Nat.pow_le_pow_right (by norm_num) (hle c hc m hm)))
  rw [open_inputs_honest (ME := ME) G g mmcs b H indices openings α claims commit_of hon.batches
    (fun bc hbc => ?_) (checkDenominators_honest G g b H indices claims hHa' hz)]
  · rw [mapM_eq_pure_map' (g := fun e => (inputLogHeights b claims).map fun h =>
        (h, (deepOn g α b cols claims h).eval (dom G h (e.1 / 2 ^ (H - h))))) _ fun e he => ?_]
    · congr 1
      rw [← List.zipIdx_map_fst 0 indices, List.map_map, List.zipIdx_map_fst]
      rfl
    obtain ⟨i, q⟩ := e
    obtain ⟨hq, hi⟩ := List.mem_zipIdx' he
    dsimp only
    rw [hi]
    have hrows := hon.rows q hq
    have halign : List.Forall₂ (fun c r => r.length = c.matrices.length) claims
        (openings.map fun bo => bo.opened_values.getD q []) := by
      rw [List.forall₂_map_right_iff]
      exact hrows.imp fun _ _ h => h.length_eq.symm
    rw [reduceQuery_eq_deep G g b H α claims _ indices[q] cols halign ?_ hval
      (fun c hc m hm p hp => hz _ (List.getElem_mem hq) c hc m hm p hp) hHa' hdeg]
    · refine congrArg pure (List.map_congr_left fun h hh => ?_)
      have hhH : h ≤ H := by
        obtain ⟨c, hc, m, hm, rfl⟩ := (mem_inputLogHeights b claims h).1 hh
        exact hle c hc m hm
      rw [deepOn, eval_onCoset, xOfQuery_eq G g (hhH.trans hHa), rowPoint_eq]
    · intro mr hmr
      simp only [queryMats, List.mem_flatMap] at hmr
      obtain ⟨cr, hcr, hmr⟩ := hmr
      have h1 := forall₂_mem_zip (by rw [List.forall₂_map_right_iff]; exact hrows) cr hcr
      exact forall₂_mem_zip h1 mr hmr
  · obtain ⟨bo, c⟩ := bc
    refine checkBatch_honest G mmcs b H indices commit_of bo c (hon.queries bo (List.of_mem_zip hbc).1)
      (fun r hr => ?_) (hpts c (List.of_mem_zip hbc).2) (hmmcs (bo, c) hbc)
    obtain ⟨q, hq, rfl⟩ := List.getElem_of_mem hr
    have hq' : q < indices.length := hon.queries bo (List.of_mem_zip hbc).1 ▸ hq
    have := forall₂_mem_zip_swap (hon.rows q hq') (bo, c) hbc
    simp only at this
    rw [List.getD_eq_getElem _ _ hq] at this
    exact this.length_eq.symm

/-! ## Completeness from honest commitments -/

/-- The rounds of a proof: each challenge with its arity and every query's siblings. -/
def proofRounds {Com MP IMP : Type} (proof : FriProof K Com MP IMP) (betas : List K) (L : List ℕ) :
    List (K × ℕ × List (List K)) :=
  List.zip betas (List.zip L (proof.commit_phase_openings.map (·.sibling_values)))

/-- The honest rounds of a proof, from the DEEP word of the tallest height. -/
noncomputable def proofRds (G : Gen K) (g α : K) {C Com MP IMP : Type} (params : FriParameters)
    (cols : MatrixOpening K (Coset G) → List K[X]) (claims : List (Claim G C))
    (proof : FriProof K Com MP IMP) (betas : List K) (L : List ℕ) : List (Rd K) :=
  honestRds G (deepInput g α params.log_blowup cols claims) ((inputLogHeights params.log_blowup claims).headD 0)
    (deepOn g α params.log_blowup cols claims ((inputLogHeights params.log_blowup claims).headD 0))
    (proofRounds proof betas L)

/-- The honest final polynomial of a proof. -/
noncomputable def proofFinal (G : Gen K) (g α : K) {C Com MP IMP : Type} (params : FriParameters)
    (cols : MatrixOpening K (Coset G) → List K[X]) (claims : List (Claim G C))
    (proof : FriProof K Com MP IMP) (betas : List K) (L : List ℕ) : K[X] :=
  honestFinal (deepInput g α params.log_blowup cols claims) ((inputLogHeights params.log_blowup claims).headD 0)
    (deepOn g α params.log_blowup cols claims ((inputLogHeights params.log_blowup claims).headD 0))
    (proofRounds proof betas L)

/-- Completeness of the FRI verifier from honest commitments.

The claims are honest:

- every claimed value is its column at its point
- every column has degree below its matrix's height
- every input lies at or above the final height
- every matrix is opened at some point, off the tallest coset.

The proof has the right shape, and its transcript accepts with challenges beta and indices i.

The prover is honest:

- the input rows are the columns at each query point
- the rounds fold the DEEP word of the tallest height, and roll in the DEEP words below
- the siblings are each round's rows without the queried values
- the final polynomial is the inverse transform of the final word
- both commitment schemes accept the honest rows.

Then the verifier accepts. -/
theorem verify_fri_complete_honest (G : Gen K) (hV : GenValid G) (hN : GenNested G) (h2 : (2 : K) ≠ 0) (g : K)
    {C S : Type} (fmmcs immcs : MmcsOps K) (mkTx : FriShape → VerifierTx K fmmcs.Commitment S)
    (params : FriParameters) (proof : FriProof K fmmcs.Commitment fmmcs.MultiProof immcs.MultiProof) (s : S)
    (claims : List (Claim G C)) (commit_of : C → immcs.Commitment) (α : K) (hG : G.adicity < 64)
    {L : List ℕ} (hpre : FriPre G params claims proof L) (cols : MatrixOpening K (Coset G) → List K[X])
    (hval : ∀ c ∈ claims, ∀ m ∈ c.matrices, ∀ p ∈ m.points, p.values = (cols m).map (·.eval p.point))
    (hdeg : ∀ c ∈ claims, ∀ m ∈ c.matrices, ∀ f ∈ cols m, f.degree < ↑(2 ^ m.domain.log_size))
    (hF : ∀ c ∈ claims, ∀ m ∈ c.matrices, params.log_final_poly_len ≤ m.domain.log_size)
    (hpts : ∀ c ∈ claims, ∀ m ∈ c.matrices, m.points ≠ [])
    (hout : ∀ c ∈ claims, ∀ m ∈ c.matrices, ∀ p ∈ m.points,
      ∀ r < 2 ^ (inputLogHeights params.log_blowup claims).headD 0,
        p.point ≠ rowPoint G g ((inputLogHeights params.log_blowup claims).headD 0) r)
    {betas : List K} {s1 s2 : S} {indices : List ℕ}
    (hc : (txAt G mkTx params claims L).commit_rounds s proof.commit_phase_commits proof.commit_pow_witnesses =
      pure (betas, s1))
    (hβ : betas.length = L.length)
    (hq : (txAt G mkTx params claims L).query_phase s1 proof.final_poly (some proof.query_pow_witness) =
      pure (indices, s2))
    (hidx : ∀ i ∈ indices, i < 2 ^ (inputLogHeights params.log_blowup claims).headD 0)
    (hon : HonestOpenings G g params.log_blowup ((inputLogHeights params.log_blowup claims).headD 0) cols claims
      indices proof.input_openings)
    (hin : ∀ bc ∈ proof.input_openings.zip claims, ∀ dims reduced,
      immcs.verify_multi_batch (commit_of bc.2.commitment) dims reduced bc.1.opened_values bc.1.opening_proof =
        .ok ())
    (hsib : ∀ q i, indices[q]? = some i →
      HonestSiblings G (deepInput g α params.log_blowup cols claims) q
        ((inputLogHeights params.log_blowup claims).headD 0) i
        (deepOn g α params.log_blowup cols claims ((inputLogHeights params.log_blowup claims).headD 0))
        (proofRounds proof betas L))
    (hfin : ∀ i < 2 ^ params.log_final_poly_len, proof.final_poly.getD i 0 =
      Plonky3Lean.Spec.Dft.idft (G.gen params.log_final_poly_len) (2 ^ params.log_final_poly_len)
        (fun j => (revIndex (2 ^ params.log_final_poly_len)
          ((word G (proofFinal G g α params cols claims proof betas L)
            (params.log_final_poly_len + params.log_blowup)).take (2 ^ params.log_final_poly_len))).getD j 0) i)
    (hmmcs : ∀ k (hk : k < (proofRds G g α params cols claims proof betas L).length) (c : fmmcs.Commitment)
      (o : CommitPhaseMultiStep K fmmcs.MultiProof),
      proof.commit_phase_commits[k]? = some c → proof.commit_phase_openings[k]? = some o →
      ∀ groups : List ℕ, fmmcs.verify_multi_batch c
        [(2 ^ (proofRds G g α params cols claims proof betas L)[k].a,
          2 ^ ((inputLogHeights params.log_blowup claims).headD 0 -
            (((proofRds G g α params cols claims proof betas L).take (k + 1)).map Rd.a).sum))]
        groups (groups.map fun t =>
          [rowList (proofRds G g α params cols claims proof betas L)[k].w
            (proofRds G g α params cols claims proof betas L)[k].a t]) o.opening_proof = .ok ()) :
    verify_fri G g fmmcs immcs mkTx params proof s claims commit_of α = pure () := by
  set b := params.log_blowup
  set Lf := params.log_final_poly_len
  set H := (inputLogHeights b claims).headD 0 with hHdef
  set inp := deepInput g α b cols claims
  set P0 := deepOn g α b cols claims H
  set rounds := proofRounds proof betas L with hrounds
  -- The rounds carry the schedule's arities, the transcript's challenges and the proof's siblings.
  have hsvl : (proof.commit_phase_openings.map (·.sibling_values)).length = L.length := by
    rw [List.length_map, hpre.openings]
  have hrmap : rounds.map (·.2.1) = L := by
    rw [hrounds, proofRounds, show (fun x : K × ℕ × List (List K) => x.2.1) = Prod.fst ∘ Prod.snd from rfl,
      ← List.map_map, List.map_snd_zip (by rw [List.length_zip, hsvl, hβ, min_self]),
      List.map_fst_zip (by rw [hsvl])]
  have hbmap : rounds.map (·.1) = betas := by
    rw [hrounds, proofRounds, List.map_fst_zip (by rw [List.length_zip, hsvl, hβ, min_self])]
  have hsvmap : rounds.map (·.2.2) = proof.commit_phase_openings.map (·.sibling_values) := by
    rw [hrounds, proofRounds, show (fun x : K × ℕ × List (List K) => x.2.2) = Prod.snd ∘ Prod.snd from rfl,
      ← List.map_map, List.map_snd_zip (by rw [List.length_zip, hsvl, hβ, min_self]),
      List.map_snd_zip (by rw [hsvl])]
  obtain ⟨hrsβ, hrsa, hrssv⟩ := honestRds_map G inp H P0 rounds
  -- Every input height lies between the final height and the tallest one.
  have hS : inputLogHeights b claims ≠ [] := by
    obtain ⟨c, hc, hm⟩ : ∃ c ∈ claims, c.matrices ≠ [] := by
      have := hpre.matrices; simp only [List.all_eq_false, decide_eq_true_eq] at this; exact this
    obtain ⟨m, hm⟩ := List.exists_mem_of_ne_nil _ hm
    exact List.ne_nil_of_mem ((mem_inputLogHeights b claims _).2 ⟨c, hc, m, hm, rfl⟩)
  have hFall : ∀ h ∈ inputLogHeights b claims, b + Lf ≤ h := by
    intro h hh
    obtain ⟨c, hc, m, hm, rfl⟩ := (mem_inputLogHeights b claims h).1 hh
    have := hF c hc m hm; omega
  have hFH : b + Lf ≤ H := by
    apply hFall
    rcases hSc : inputLogHeights b claims with _ | ⟨x, T⟩
    · exact absurd hSc hS
    · rw [hHdef, hSc]; simp
  have hHa : H ≤ G.adicity := hpre.height
  -- The schedule descends from H to the final height, by arities of at least 1.
  obtain ⟨hpos, hsum⟩ : (∀ a ∈ L, 1 ≤ a) ∧ L.sum = H - (b + Lf) := by
    have hdec := (inputLogHeights_pairwise b claims).isChain
    rcases Nat.lt_or_ge (b + Lf) H with hlt | hge
    · rcases hSc : inputLogHeights b claims with _ | ⟨x, T⟩
      · exact absurd hSc hS
      rw [hSc] at hdec
      have hx : H = x := by rw [hHdef, hSc]; rfl
      obtain ⟨L', hL', ha, hs, -⟩ := fold_schedule_spec hdec (Nat.pos_of_ne_zero hpre.arity) (hx ▸ hlt)
      have := hpre.schedule
      rw [hSc] at this
      obtain rfl := Option.some.inj (this.symm.trans hL')
      exact ⟨fun a h => (ha a h).1, by rw [hs, hx]⟩
    · have := hpre.schedule
      rw [fold_schedule_nil hdec (fun h0 hh0 => by
        rcases hSc : inputLogHeights b claims with _ | ⟨x, T⟩
        · rw [hSc] at hh0; simp at hh0
        · rw [hSc] at hh0; simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hh0
          subst hh0; rw [hHdef, hSc] at hge; simpa using hge)] at this
      obtain rfl := (Option.some.inj this).symm
      exact ⟨by simp, by simp; omega⟩
  have hpos' : ∀ r ∈ rounds, 1 ≤ r.2.1 := fun r hr => hpos _ (hrmap ▸ List.mem_map_of_mem hr)
  have hsum' : (rounds.map (·.2.1)).sum ≤ H := by rw [hrmap, hsum]; omega
  have hHF : H - (rounds.map (·.2.1)).sum = Lf + b := by rw [hrmap, hsum]; omega
  have hinp : ∀ h R, inp h = some R → R.degree < ↑(2 ^ (h - b)) := by
    intro h R hR
    simp only [inp, deepInput] at hR
    split_ifs at hR
    obtain rfl := Option.some.inj hR
    exact degree_deepOn g α b cols claims hdeg h
  refine verify_fri_complete G hV hN h2 g fmmcs immcs mkTx params proof s claims commit_of α hG hpre rfl
    (honestRds G inp H P0 rounds) (word G (honestFinal inp H P0 rounds) (H - (rounds.map (·.2.1)).sum)) P0
    (by rw [hrsa, hrmap]) (by rw [hrsβ, hbmap]; exact hc) hq (by rw [hrssv, hsvmap])
    (by rw [totalA_honestRds, hHF]; ring) ?_ ?_ ?_ hmmcs
  · -- The input checks return the DEEP words, which are the chain's first word and its rolled-in inputs.
    rw [open_inputs', open_inputs_deep G hN g immcs b indices proof.input_openings α claims commit_of cols hHa hidx
      hon hin hpts hval hout hdeg]
    refine congrArg pure (List.map_congr_left fun i hi => ?_)
    have hiH := hidx i hi
    rw [rolls_honestRds G inp H i P0 rounds hsum' hiH,
      chainRolls_eq_inputs g α b cols claims (Nat.pos_of_ne_zero hpre.arity) hpre.schedule
        (fun h hh => by have := hFall h hh; omega) rounds hrmap i,
      nextWord_honestRds G inp H P0 rounds hiH]
    rcases hSc : inputLogHeights b claims with _ | ⟨x, T⟩
    · exact absurd hSc hS
    have hx : H = x := by simp [hHdef, hSc]
    simp only [List.map_cons, List.tail_cons, List.headD_cons, Nat.sub_self, pow_zero, Nat.div_one, P0, hx]
  · intro q i hiq
    exact honestRds_chain G inp q H i P0 rounds hpos' hsum' hHa (hidx i (List.mem_of_getElem? hiq)) (hsib q i hiq)
  · -- The final polynomial evaluates back to the final word.
    intro j hj
    rw [totalA_honestRds, hHF] at hj
    rw [hHF]
    refine final_poly_eval G hV hN (show Lf + b ≤ G.adicity by omega) (word_isCodeword G _ _) ?_ ?_ hfin
      (H := H) (show Lf + b ≤ H by omega) hHa hj
    · have := degree_honestFinal inp b hinp H P0 rounds (by omega) (degree_deepOn g α b cols claims hdeg H)
      rwa [show H - (rounds.map (·.2.1)).sum - b = Lf by omega] at this
    · rw [hpre.final]; rfl

/-! ## The concrete transcripts -/

theorem exceptT_bind_eq_pure {ε α β : Type _} (m : ExceptT ε Option α) (k : α → ExceptT ε Option β) (b : β) :
    (m >>= k) = pure b ↔ ∃ a, m = pure a ∧ k a = pure b := by
  change Option (Except ε α) at m
  rcases m with _ | (e | a)
  · simp only [bind, ExceptT.bind, ExceptT.mk, ExceptT.bindCont]
    exact ⟨fun h => (by cases h), fun ⟨_, ha, _⟩ => (by cases ha)⟩
  · simp only [bind, ExceptT.bind, ExceptT.mk, ExceptT.bindCont]
    exact ⟨fun h => (by cases h), fun ⟨_, ha, _⟩ => (by cases ha)⟩
  · refine ⟨fun h => ⟨a, rfl, h⟩, fun ⟨a', ha, hk⟩ => ?_⟩
    obtain rfl : a = a' := Except.ok.inj (Option.some.inj ha)
    exact hk

theorem exceptT_throw_bind_ne_pure {ε α β : Type _} (e : ε) (k : α → ExceptT ε Option β) (b : β) :
    (throw e >>= k : ExceptT ε Option β) ≠ pure b := by
  rw [Ne, exceptT_bind_eq_pure]
  rintro ⟨a, ha, -⟩
  cases ha

theorem exceptT_throw_ne_pure {ε α : Type _} (e : ε) (b : α) : (throw e : ExceptT ε Option α) ≠ pure b := by
  intro h; cases h

/-- The commit rounds return one challenge per scheduled round. -/
theorem commit_rounds_length {Com S : Type} (sp : Sponge K Com S) (shape : FriShape) (s : S) (coms : List Com)
    (ws : List K) {betas : List K} {s1 : S} (h : commit_rounds sp shape s coms ws = pure (betas, s1)) :
    betas.length = shape.log_arities.length := by
  unfold commit_rounds at h
  dsimp only at h
  by_cases h1 : coms.length = shape.log_arities.length
  swap
  · simp only [ne_eq, h1, not_false_eq_true, ↓reduceIte] at h
    exact absurd h (exceptT_throw_bind_ne_pure _ _ _)
  by_cases h2 : ws.length = shape.log_arities.length
  swap
  · simp only [ne_eq, h1, h2, not_true_eq_false, not_false_eq_true, ↓reduceIte] at h
    exact absurd h (exceptT_throw_bind_ne_pure _ _ _)
  simp only [ne_eq, h1, h2, not_true_eq_false, ↓reduceIte] at h
  have key : ∀ (l : List (Com × K)) (acc : List K × S) (r : List K × S),
      l.foldlM (fun acc cw => do
        let (b, s') ← commit_round sp shape acc.2 cw
        pure (acc.1 ++ [b], s')) acc = pure r → r.1.length = acc.1.length + l.length := by
    intro l
    induction l with
    | nil => intro acc r h; simp only [List.foldlM_nil] at h; obtain rfl := Except.ok.inj (Option.some.inj h); simp
    | cons cw l ih =>
      intro acc r h
      rw [List.foldlM_cons, exceptT_bind_eq_pure] at h
      obtain ⟨acc', h1, h2⟩ := h
      rw [exceptT_bind_eq_pure] at h1
      obtain ⟨⟨b, s'⟩, -, h1⟩ := h1
      obtain rfl := Except.ok.inj (Option.some.inj h1)
      rw [ih _ _ h2]; simp; omega
  have := key _ _ _ h
  simp only [List.length_nil, List.length_zip, zero_add] at this
  rw [this, h1, h2, min_self]

/-- Every drawn query index lies below 2^b, for b the shape's index width. -/
theorem query_phase_indices_lt {Com S : Type} (sp : Sponge K Com S) (shape : FriShape) (s : S) (fp : List K)
    (w : Option K) {indices : List ℕ} {s2 : S} (h : query_phase sp shape s fp w = pure (indices, s2)) :
    ∀ i ∈ indices, i < 2 ^ shape.index_bits := by
  have key : ∀ (l : List ℕ) (acc : List ℕ × S) (r : List ℕ × S), (∀ i ∈ acc.1, i < 2 ^ shape.index_bits) →
      l.foldlM (fun acc _ => do
        let x ← ExceptT.lift (sample_bits sp acc.2 shape.index_bits)
        pure (acc.1 ++ [x.1], x.2)) acc = (pure r : ExceptT TranscriptFailure Option _) →
      ∀ i ∈ r.1, i < 2 ^ shape.index_bits := by
    intro l
    induction l with
    | nil =>
      intro acc r hacc h
      simp only [List.foldlM_nil] at h
      obtain rfl := Except.ok.inj (Option.some.inj h); exact hacc
    | cons x l ih =>
      intro acc r hacc h
      rw [List.foldlM_cons, exceptT_bind_eq_pure] at h
      obtain ⟨acc', h1, h2⟩ := h
      rw [exceptT_bind_eq_pure] at h1
      obtain ⟨y, hy, h1⟩ := h1
      obtain rfl := Except.ok.inj (Option.some.inj h1)
      unfold sample_bits at hy
      split_ifs at hy
      · exact absurd hy (by intro h; cases h)
      obtain rfl := Except.ok.inj (Option.some.inj hy)
      refine ih _ _ (fun i hi => ?_) h2
      simp only [List.mem_append, List.mem_singleton] at hi
      rcases hi with hi | rfl
      · exact hacc i hi
      · exact Nat.mod_lt _ (by positivity)
  unfold query_phase at h
  dsimp only at h
  by_cases hf : shape.final_poly_len = fp.length
  swap
  · simp only [ne_eq, hf, not_false_eq_true, ↓reduceIte] at h
    exact absurd h (exceptT_throw_bind_ne_pure _ _ _)
  simp only [ne_eq, hf, not_true_eq_false, ↓reduceIte] at h
  by_cases hq : 0 < shape.query_pow_bits
  · simp only [hq, ↓reduceIte] at h
    rcases w with _ | w
    · exact absurd h (exceptT_throw_bind_ne_pure _ _ _)
    · dsimp only at h
      rw [exceptT_bind_eq_pure] at h
      obtain ⟨y, -, h⟩ := h
      by_cases hy : y.1 = true
      · simp only [hy, ↓reduceIte, pure_bind] at h; exact key _ _ _ (by simp) h
      · simp only [hy, Bool.false_eq_true, ↓reduceIte] at h
        exact absurd h (exceptT_throw_bind_ne_pure _ _ _)
  · simp only [hq, ↓reduceIte, pure_bind] at h; exact key _ _ _ (by simp) h

/-! ## Completeness of the PCS verifier -/

/-- Completeness of the PCS verifier from honest commitments.

The claims and the prover are honest, as in the FRI statement above.

The witnesses of zero difficulty are zero, and the honest grinding witnesses pass.

The first committed word is then the DEEP word of the tallest height on the coset g H.

The verifier accepts.

No hypothesis links the first word to the claims: it is proven. -/
theorem pcs_verify_complete_honest (G : Gen K) (hV : GenValid G) (hN : GenNested G) (h2 : (2 : K) ≠ 0)
    (g : K) {C S : Type} (fmmcs immcs : MmcsOps K) (sp : Sponge K fmmcs.Commitment S) (params : FriParameters)
    (claims : List (Claim G C)) (proof : FriProof K fmmcs.Commitment fmmcs.MultiProof immcs.MultiProof) (s : S)
    (commit_of : C → immcs.Commitment) (hG : G.adicity < 64)
    {L : List ℕ} (hpre : FriPre G params claims proof L) (cols : MatrixOpening K (Coset G) → List K[X])
    (hval : ∀ c ∈ claims, ∀ m ∈ c.matrices, ∀ p ∈ m.points, p.values = (cols m).map (·.eval p.point))
    (hdeg : ∀ c ∈ claims, ∀ m ∈ c.matrices, ∀ f ∈ cols m, f.degree < ↑(2 ^ m.domain.log_size))
    (hF : ∀ c ∈ claims, ∀ m ∈ c.matrices, params.log_final_poly_len ≤ m.domain.log_size)
    (hpts : ∀ c ∈ claims, ∀ m ∈ c.matrices, m.points ≠ [])
    (hout : ∀ c ∈ claims, ∀ m ∈ c.matrices, ∀ p ∈ m.points,
      ∀ r < 2 ^ (inputLogHeights params.log_blowup claims).headD 0,
        p.point ≠ rowPoint G g ((inputLogHeights params.log_blowup claims).headD 0) r)
    {α : K} {s2 : S}
    (hb : batch_phase sp (PcsShape.from_claims params claims) (claimedState sp claims s)
      (some proof.batch_pow_witness) = pure (α, s2))
    {betas : List K} {s3 s4 : S} {indices : List ℕ}
    (hc : commit_rounds sp (FriShape.with_schedule params L ((inputLogHeights params.log_blowup claims).headD 0))
      s2 proof.commit_phase_commits proof.commit_pow_witnesses = pure (betas, s3))
    (hq : query_phase sp (FriShape.with_schedule params L ((inputLogHeights params.log_blowup claims).headD 0))
      s3 proof.final_poly (some proof.query_pow_witness) = pure (indices, s4))
    (hon : HonestOpenings G g params.log_blowup ((inputLogHeights params.log_blowup claims).headD 0) cols claims
      indices proof.input_openings)
    (hin : ∀ bc ∈ proof.input_openings.zip claims, ∀ dims reduced,
      immcs.verify_multi_batch (commit_of bc.2.commitment) dims reduced bc.1.opened_values bc.1.opening_proof =
        .ok ())
    (hsib : ∀ q i, indices[q]? = some i →
      HonestSiblings G (deepInput g α params.log_blowup cols claims) q
        ((inputLogHeights params.log_blowup claims).headD 0) i
        (deepOn g α params.log_blowup cols claims ((inputLogHeights params.log_blowup claims).headD 0))
        (proofRounds proof betas L))
    (hfin : ∀ i < 2 ^ params.log_final_poly_len, proof.final_poly.getD i 0 =
      Plonky3Lean.Spec.Dft.idft (G.gen params.log_final_poly_len) (2 ^ params.log_final_poly_len)
        (fun j => (revIndex (2 ^ params.log_final_poly_len)
          ((word G (proofFinal G g α params cols claims proof betas L)
            (params.log_final_poly_len + params.log_blowup)).take (2 ^ params.log_final_poly_len))).getD j 0) i)
    (hmmcs : ∀ k (hk : k < (proofRds G g α params cols claims proof betas L).length) (c : fmmcs.Commitment)
      (o : CommitPhaseMultiStep K fmmcs.MultiProof),
      proof.commit_phase_commits[k]? = some c → proof.commit_phase_openings[k]? = some o →
      ∀ groups : List ℕ, fmmcs.verify_multi_batch c
        [(2 ^ (proofRds G g α params cols claims proof betas L)[k].a,
          2 ^ ((inputLogHeights params.log_blowup claims).headD 0 -
            (((proofRds G g α params cols claims proof betas L).take (k + 1)).map Rd.a).sum))]
        groups (groups.map fun t =>
          [rowList (proofRds G g α params cols claims proof betas L)[k].w
            (proofRds G g α params cols claims proof betas L)[k].a t]) o.opening_proof = .ok ()) :
    verify G g fmmcs immcs sp params claims proof s commit_of = pure () :=
  pcs_verify_complete G g fmmcs immcs sp params claims proof s commit_of hpre.canonical hb
    (verify_fri_complete_honest G hV hN h2 g fmmcs immcs (verifierTx sp) params proof s2 claims commit_of α hG
      hpre cols hval hdeg hF hpts hout hc (commit_rounds_length sp _ _ _ _ hc) hq
      (query_phase_indices_lt sp _ _ _ _ hq) hon hin hsib hfin hmmcs)

end Plonky3Lean.Proofs.Fri
