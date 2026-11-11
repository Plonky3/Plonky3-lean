module

public import Plonky3Lean.Proofs.Fri.Matrix
public import Plonky3Lean.Proofs.Fri.Schedule
public import P3Fri.Verifier
public import P3Fri.Prover
public import Plonky3Lean.Proofs.Fri.Res

@[expose] public section

/-!
# The query phase

The siblings a prover sends are its row without the queried value.

The verifier rebuilds the row from them.

On an honest chain of codewords, a query's fold chain reaches the final codeword's value at the shifted index.

On any proof, an accepted chain records rows that satisfy the round-consistency relation.
-/

namespace Plonky3Lean.Proofs.Fri

open Polynomial Finset Plonky3Lean.Spec.Fri p3_fri.two_adic_pcs.mirror p3_dft.mirror
open p3_fri.verifier.mirror p3_fri.mirror Plonky3Lean.Proofs.Dft

set_option linter.unusedSectionVars false

variable {K : Type} [Field K] [DecidableEq K]

theorem filter_zipIdx_eq_eraseIdx {α : Type _} (l : List α) (k p : ℕ) (hkp : k ≤ p) :
    ((l.zipIdx k).filter fun x => x.2 ≠ p).map Prod.fst = l.eraseIdx (p - k) := by
  induction l generalizing k with
  | nil => simp
  | cons x l ih =>
    rcases Nat.eq_or_lt_of_le hkp with rfl | hlt
    · simp only [List.zipIdx_cons, List.filter_cons, ne_eq, not_true_eq_false, decide_false,
        Bool.false_eq_true, ↓reduceIte, Nat.sub_self, List.eraseIdx_cons_zero]
      have : ∀ y ∈ l.zipIdx (k + 1), y.2 ≠ k := by
        intro y hy; have := List.le_snd_of_mem_zipIdx hy; omega
      rw [List.filter_eq_self.2 (by simpa using this), List.zipIdx_eq_zip_range', List.map_fst_zip]
      simp
    · simp only [List.zipIdx_cons, List.filter_cons, ne_eq, show k ≠ p by omega, not_false_eq_true,
        decide_true, ↓reduceIte, List.map_cons]
      rw [ih (k + 1) (by omega), show p - k = (p - (k + 1)) + 1 by omega, List.eraseIdx_cons_succ]

/-- The siblings the prover sends: the row without the queried position. -/
theorem siblings_eq_eraseIdx {α : Type _} (row : List α) (p : ℕ) :
    (row.zipIdx.filter fun x => x.2 ≠ p).map Prod.fst = row.eraseIdx p := by
  simpa using filter_zipIdx_eq_eraseIdx row 0 p (Nat.zero_le p)

/-- The verifier rebuilds the row from the folded value at the queried position and the siblings. -/
theorem rebuildRow_eraseIdx (row : List K) {p : ℕ} (hp : p < row.length) :
    rebuildRow row.length p row[p] (row.eraseIdx p) = row := by
  apply List.ext_getElem (by simp [rebuildRow])
  intro j h1 h2
  simp only [rebuildRow, List.getElem_map, List.getElem_range]
  split_ifs with hjp hjp'
  · subst hjp; rfl
  · rw [List.getD_eq_getElem _ _ (by rw [List.length_eraseIdx_of_lt hp]; omega),
      List.getElem_eraseIdx]
    simp [hjp']
  · rw [List.getD_eq_getElem _ _ (by rw [List.length_eraseIdx_of_lt hp]; omega),
      List.getElem_eraseIdx]
    simp only [show ¬ j - 1 < p by omega, ↓reduceDIte]
    congr 1; omega

/-- One commit round as the verifier sees it:

- the challenge
- the log arity
- the word committed
- the input rolled in after the fold
- every query's siblings. -/
structure Rd (K : Type) where
  β : K
  a : ℕ
  w : List K
  roll : Option (List K)
  sv : List (List K)

/-- Row t of a word read at width 2^a. -/
def rowList (w : List K) (a t : ℕ) : List K := List.ofFn fun j : Fin (2 ^ a) => w.getD (t * 2 ^ a + j.val) 0

/-- The word after the first round: the next round's word, or the final word. -/
def nextWord : List (Rd K) → List K → List K
  | [], wF => wF
  | r :: _, _ => r.w

/-- The input term a round adds at index t: beta^(2^a) times the input, if one is rolled in. -/
def rollTerm (r : Rd K) (t : ℕ) : K :=
  match r.roll with
  | some u => r.β ^ 2 ^ r.a * u.getD t 0
  | none => 0

/-- The reduced openings of one query after the first: each rolled-in input at its height and shifted index. -/
def rolls : List (Rd K) → ℕ → ℕ → List (ℕ × K)
  | [], _, _ => []
  | r :: rs, lh, idx =>
    (match r.roll with
      | some u => [(lh - r.a, u.getD (idx / 2 ^ r.a) 0)]
      | none => []) ++ rolls rs (lh - r.a) (idx / 2 ^ r.a)

/-- The group index and row of every round, at the query's shifted index. -/
def recordedOf : List (Rd K) → ℕ → List (ℕ × List K)
  | [], _ => []
  | r :: rs, idx => (idx / 2 ^ r.a, rowList r.w r.a (idx / 2 ^ r.a)) :: recordedOf rs (idx / 2 ^ r.a)

/-- An honest chain for query q at index idx:

- each word has its height
- each round's siblings are its row without the queried value
- each round folds its row to the next word's value, less the input term. -/
def ChainOK (G : Gen K) (q : ℕ) : ℕ → ℕ → List (Rd K) → List K → Prop
  | lh, idx, [], wF => wF.length = 2 ^ lh ∧ idx < 2 ^ lh
  | lh, idx, r :: rs, wF => 1 ≤ r.a ∧ r.a ≤ lh ∧ r.w.length = 2 ^ lh ∧ idx < 2 ^ lh ∧
      r.sv[q]? = some ((rowList r.w r.a (idx / 2 ^ r.a)).eraseIdx (idx % 2 ^ r.a)) ∧
      fold_row G (idx / 2 ^ r.a) (lh - r.a) r.a r.β (rowList r.w r.a (idx / 2 ^ r.a)) =
        some ((nextWord rs wF).getD (idx / 2 ^ r.a) 0 - rollTerm r (idx / 2 ^ r.a)) ∧
      ChainOK G q (lh - r.a) (idx / 2 ^ r.a) rs wF

/-- The total log reduction of the rounds. -/
def totalA (rs : List (Rd K)) : ℕ := (rs.map Rd.a).sum

theorem length_rowList (w : List K) (a t : ℕ) : (rowList w a t).length = 2 ^ a := by simp [rowList]

theorem rowList_getElem (w : List K) (a idx : ℕ) :
    (rowList w a (idx / 2 ^ a))[idx % 2 ^ a]'(by rw [length_rowList]; exact Nat.mod_lt _ (by positivity)) =
      w.getD idx 0 := by
  simp [rowList, Nat.div_add_mod']

theorem rolls_lt {G : Gen K} {q : ℕ} : ∀ (rs : List (Rd K)) (lh idx : ℕ) (wF : List K),
    ChainOK G q lh idx rs wF → ∀ x ∈ rolls rs lh idx, x.1 < lh
  | [], _, _, _, _ => by simp [rolls]
  | r :: rs, lh, idx, wF, ⟨ha1, hal, _, _, _, _, hrest⟩ => by
    intro x hx
    simp only [rolls, List.mem_append] at hx
    rcases hx with hx | hx
    · rcases hr : r.roll with _ | u <;> simp [hr] at hx; rw [hx]; simp; omega
    · have := rolls_lt rs _ _ wF hrest x hx; omega

/-- On an honest chain, the fold chain of a query:

- reaches the final word's value at the shifted index
- records every round's row
- consumes every rolled-in input. -/
theorem foldlM_chain (G : Gen K) (q : ℕ) : ∀ (rs : List (Rd K)) (lh idx : ℕ) (wF : List K)
    (acc : List (ℕ × List K)), ChainOK G q lh idx rs wF →
    (rs.map fun r => (r.β, r.a, r.sv)).foldlM (foldStep G q)
        (idx, (nextWord rs wF).getD idx 0, lh, rolls rs lh idx, acc) =
      some (idx / 2 ^ totalA rs, wF.getD (idx / 2 ^ totalA rs) 0, lh - totalA rs, [],
        acc ++ recordedOf rs idx)
  | [], lh, idx, wF, acc, _ => by simp [nextWord, rolls, totalA, recordedOf]
  | r :: rs, lh, idx, wF, acc, h => by
    obtain ⟨ha1, hal, hwl, hidx, hsv, hfold, hrest⟩ := h
    have hrow := rebuildRow_eraseIdx (rowList r.w r.a (idx / 2 ^ r.a))
      (p := idx % 2 ^ r.a) (by rw [length_rowList]; exact Nat.mod_lt _ (by positivity))
    rw [rowList_getElem, length_rowList] at hrow
    have hlt := rolls_lt rs _ _ wF hrest
    have hih := foldlM_chain G q rs (lh - r.a) (idx / 2 ^ r.a) wF
      (acc ++ [(idx / 2 ^ r.a, rowList r.w r.a (idx / 2 ^ r.a))]) hrest
    have hdiv : idx / 2 ^ r.a / 2 ^ totalA rs = idx / 2 ^ totalA (r :: rs) := by
      rw [Nat.div_div_eq_div_mul, ← pow_add]; simp [totalA]
    have hsub : lh - r.a - totalA rs = lh - totalA (r :: rs) := by simp [totalA]; omega
    rw [hdiv, hsub, List.append_assoc, List.singleton_append] at hih
    rw [show nextWord (r :: rs) wF = r.w from rfl]
    simp only [List.map_cons, List.foldlM_cons, foldStep, hsv, Option.bind_eq_bind,
      Option.bind_some, hrow, hfold]
    rcases hr : r.roll with _ | u
    · have hro : rolls (r :: rs) lh idx = rolls rs (lh - r.a) (idx / 2 ^ r.a) := by
        simp [rolls, hr]
      have hrt : rollTerm r (idx / 2 ^ r.a) = 0 := by simp [rollTerm, hr]
      rw [hro, hrt, sub_zero]
      rcases hrs : rolls rs (lh - r.a) (idx / 2 ^ r.a) with _ | ⟨⟨h1, v⟩, ro'⟩
      · rw [hrs] at hih
        simpa [recordedOf] using hih
      · have := hlt (h1, v) (by rw [hrs]; simp)
        simp only [show h1 ≠ lh - r.a by simp at this; omega, ↓reduceIte, Option.bind_some]
        rw [← hrs]
        simpa [recordedOf] using hih
    · have hro : rolls (r :: rs) lh idx =
          (lh - r.a, u.getD (idx / 2 ^ r.a) 0) :: rolls rs (lh - r.a) (idx / 2 ^ r.a) := by
        simp [rolls, hr]
      have hrt : rollTerm r (idx / 2 ^ r.a) = r.β ^ 2 ^ r.a * u.getD (idx / 2 ^ r.a) 0 := by
        simp [rollTerm, hr]
      rw [hro, hrt]
      simp only [↓reduceIte, sub_add_cancel, Option.bind_some]
      simpa [recordedOf] using hih

theorem ChainOK.facts {G : Gen K} {q : ℕ} : ∀ {rs : List (Rd K)} {lh idx : ℕ} {wF : List K},
    ChainOK G q lh idx rs wF → totalA rs ≤ lh ∧ ∀ r ∈ rs, 1 ≤ r.a ∧
      ∃ s, r.sv[q]? = some s ∧ s.length = 2 ^ r.a - 1
  | [], _, _, _, _ => by simp [totalA]
  | r :: rs, lh, idx, wF, ⟨ha1, hal, _, _, hsv, _, hrest⟩ => by
    obtain ⟨ht, hr⟩ := ChainOK.facts hrest
    refine ⟨by simp only [totalA, List.map_cons, List.sum_cons] at ht ⊢; omega, ?_⟩
    intro r' hr'
    rcases List.mem_cons.1 hr' with rfl | hr'
    · refine ⟨ha1, _, hsv, ?_⟩
      rw [List.length_eraseIdx_of_lt (by rw [length_rowList]; exact Nat.mod_lt _ (by positivity)),
        length_rowList]
    · exact hr r' hr'

theorem zip_map_three {α β γ δ : Type _} (l : List α) (f : α → β) (g : α → γ) (h : α → δ) :
    List.zip (l.map f) (List.zip (l.map g) (l.map h)) = l.map fun x => (f x, g x, h x) := by
  induction l <;> simp_all

/-- Completeness of one query.

Take an honest chain from the tallest height H down to the final height.

The query's fold returns:

- the final word's value at the shifted index
- that index
- every round's group index and row. -/
theorem fold_query_complete {ME IE : Type} (G : Gen K) (q idx : ℕ) (rs : List (Rd K)) (wF : List K)
    {H Hf : ℕ} (hc : ChainOK G q H idx rs wF) (h64 : ∀ r ∈ rs, r.a < 64) (hHf : H - totalA rs = Hf) :
    fold_query (ME := ME) (IE := IE) G q idx (rs.map Rd.β) (rs.map Rd.a) (rs.map Rd.sv)
        ((H, (nextWord rs wF).getD idx 0) :: rolls rs H idx) H Hf =
      pure (wF.getD (idx / 2 ^ totalA rs) 0, idx / 2 ^ totalA rs, recordedOf rs idx) := by
  obtain ⟨hT, hrs⟩ := hc.facts
  have hany : (rs.map Rd.a).any (fun la => la = 0 ∨ 64 ≤ la) = false := by
    simp only [List.any_eq_false, List.mem_map]
    rintro _ ⟨r, hr, rfl⟩
    have := (hrs r hr).1; have := h64 r hr; simp; omega
  have hfind : ((rs.map Rd.sv).zip (rs.map Rd.a)).find? (badRound q) = none := by
    rw [List.find?_eq_none]
    intro e he
    rw [List.zip_map', List.mem_map] at he
    obtain ⟨r, hr, rfl⟩ := he
    obtain ⟨-, s, hs, hsl⟩ := hrs r hr
    simp [badRound, hs, hsl]
  have hsum : ¬ (H - Hf < (rs.map Rd.a).sum) := by simp only [totalA] at hT hHf; omega
  have hch := foldlM_chain G q rs H idx wF [] hc
  simp only [List.nil_append] at hch
  simp only [fold_query, hany, Bool.false_eq_true, ↓reduceIte, hfind, hsum, zip_map_three, lift,
    pure_bind, ne_eq, not_true_eq_false, hch, hHf, lift_some_bind]

/-- The value a round passes on: the fold, plus beta^(2^a) times the next opening.

The opening counts only if it sits at the folded height. -/
def rollIn (lh' : ℕ) (β : K) (a : ℕ) (u : K) : List (ℕ × K) → K × List (ℕ × K)
  | (h, v) :: ro => if h = lh' then (u + β ^ 2 ^ a * v, ro) else (u, (h, v) :: ro)
  | [] => (u, [])

/-- Round consistency of a recorded chain:

- each recorded row holds the running value at the queried position
- its fold, with any rolled-in opening, is the next running value
- the last running value is the final value. -/
def Consistent (G : Gen K) : ℕ → ℕ → K → List (ℕ × K) → List (K × ℕ) → List (ℕ × List K) → K →
    List (ℕ × K) → Prop
  | _, _, v, ro, [], [], fin, roF => fin = v ∧ roF = ro
  | lh, idx, v, ro, (β, a) :: rds, (g, row) :: recs, fin, roF =>
    g = idx / 2 ^ a ∧ row.length = 2 ^ a ∧ row[idx % 2 ^ a]? = some v ∧
      ∃ u, fold_row G g (lh - a) a β row = some u ∧
        Consistent G (lh - a) g (rollIn (lh - a) β a u ro).1 (rollIn (lh - a) β a u ro).2 rds recs fin roF
  | _, _, _, _, _, _, _, _ => False

theorem rebuildRow_get (n p : ℕ) (hp : p < n) (v : K) (sib : List K) :
    (rebuildRow n p v sib).length = n ∧ (rebuildRow n p v sib)[p]? = some v := by
  simp [rebuildRow, hp]

theorem foldlM_consistent (G : Gen K) (q : ℕ) :
    ∀ (rounds : List (K × ℕ × List (List K))) (idx : ℕ) (v : K) (lh : ℕ) (ro : List (ℕ × K))
      (acc : List (ℕ × List K)) (res : ChainState K),
      (∀ r ∈ rounds, 1 ≤ r.2.1 ∧ r.2.1 < 64) →
      rounds.foldlM (foldStep G q) (idx, v, lh, ro, acc) = some res →
      ∃ recs, res.2.2.2.2 = acc ++ recs ∧ res.2.2.1 = lh - (rounds.map fun r => r.2.1).sum ∧
        res.1 = idx / 2 ^ (rounds.map fun r => r.2.1).sum ∧
        Consistent G lh idx v ro (rounds.map fun r => (r.1, r.2.1)) recs res.2.1 res.2.2.2.1
  | [], idx, v, lh, ro, acc, res, _, h => by
    simp only [List.foldlM_nil, Option.pure_def, Option.some.injEq] at h
    subst h
    exact ⟨[], by simp, by simp, by simp, by simp [Consistent]⟩
  | (β, a, sv) :: rounds, idx, v, lh, ro, acc, res, ha, h => by
    simp only [List.foldlM_cons, foldStep, Option.bind_eq_bind] at h
    obtain ⟨ha1, ha64⟩ := ha _ List.mem_cons_self
    obtain ⟨st, hst, hres⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨sib, hsib, hst⟩ := Option.bind_eq_some_iff.1 hst
    obtain ⟨u, hu, hst⟩ := Option.bind_eq_some_iff.1 hst
    set row := rebuildRow (2 ^ a) (idx % 2 ^ a) v sib with hrow
    have hst' : st = (idx / 2 ^ a, (rollIn (lh - a) β a u ro).1, lh - a, (rollIn (lh - a) β a u ro).2,
        acc ++ [(idx / 2 ^ a, row)]) := by
      rcases ro with _ | ⟨⟨h1, v1⟩, ro'⟩
      · simpa [rollIn] using hst.symm
      · by_cases hh : h1 = lh - a <;> simp [rollIn, hh] at hst ⊢ <;> exact hst.symm
    subst hst'
    obtain ⟨recs, h1, h2, h3, h4⟩ := foldlM_consistent G q rounds _ _ _ _ _ res
      (fun r hr => ha r (List.mem_cons_of_mem _ hr)) hres
    obtain ⟨hlen, hget⟩ := rebuildRow_get (2 ^ a) (idx % 2 ^ a) (Nat.mod_lt _ (by positivity)) v sib
    refine ⟨(idx / 2 ^ a, row) :: recs, by simp [h1], ?_, ?_, ?_⟩
    · simp only [List.map_cons, List.sum_cons, h2]; omega
    · simp only [List.map_cons, List.sum_cons, h3, Nat.div_div_eq_div_mul, ← pow_add]
    · exact ⟨rfl, hlen, hget, u, hu, h4⟩

/-- Soundness of one query's checks.

An accepted fold chain:

- starts at the opening of the tallest height
- records rows that each hold the running value at the queried position
- folds each row to the next running value, with any rolled-in opening
- ends at the returned value at the final height
- consumes every opening. -/
theorem fold_query_sound {ME IE : Type} (G : Gen K) (q idx : ℕ) (betas : List K) (las : List ℕ)
    (svs : List (List (List K))) (ro : List (ℕ × K)) (H Hf : ℕ) {f : K} {i' : ℕ}
    {recorded : List (ℕ × List K)}
    (h : fold_query (ME := ME) (IE := IE) G q idx betas las svs ro H Hf = pure (f, i', recorded)) :
    ∃ v0 ro', ro = (H, v0) :: ro' ∧
      Consistent G H idx v0 ro' ((List.zip betas (List.zip las svs)).map fun r => (r.1, r.2.1))
        recorded f [] ∧
      H - ((List.zip betas (List.zip las svs)).map fun r => r.2.1).sum = Hf := by
  unfold fold_query at h
  by_cases hany : (las.any fun la => decide (la = 0 ∨ 64 ≤ la)) = true
  · simp only [hany, ↓reduceIte, throw_bind'] at h; exact absurd h (throw_ne_pure _ _)
  simp only [hany, Bool.false_eq_true, ↓reduceIte] at h
  cases hfind : List.find? (badRound q) (svs.zip las) with
  | some e => rcases e with ⟨sv, _⟩; by_cases hs : sv[q]?.isNone = true <;> simp [hfind, hs] at h
  | none =>
  simp only [hfind] at h
  by_cases hsum : H - Hf < las.sum
  · simp [hsum] at h
  simp only [hsum, ↓reduceIte] at h
  rcases ro with _ | ⟨⟨lh, v0⟩, ro'⟩
  · simp at h
  simp only [pure_bind] at h
  by_cases hlh : lh ≠ H
  · simp [hlh] at h
  simp only [hlh, ↓reduceIte] at h
  push Not at hlh
  subst hlh
  cases hfl : List.foldlM (foldStep G q) (idx, v0, lh, ro', []) (betas.zip (las.zip svs)) with
  | none => simp [lift, hfl] at h
  | some res =>
  obtain ⟨index, folded, log_h, roF, recs⟩ := res
  simp only [lift, hfl, lift_some_bind] at h
  by_cases hlog : log_h ≠ Hf
  · simp [hlog] at h
  simp only [hlog, ↓reduceIte] at h
  by_cases hro : roF ≠ []
  · simp [hro] at h
  simp only [hro, ↓reduceIte] at h
  push Not at hlog hro
  have heq : (folded, index, recs) = (f, i', recorded) := by
    have := congrArg (fun o : Option (Except (FriError ME IE) (K × ℕ × List (ℕ × List K))) => o) h
    exact Except.ok.inj (Option.some.inj this)
  simp only [Prod.mk.injEq] at heq
  obtain ⟨rfl, rfl, rfl⟩ := heq
  have hrng : ∀ r ∈ betas.zip (las.zip svs), 1 ≤ r.2.1 ∧ r.2.1 < 64 := by
    intro r hr
    have hm : r.2.1 ∈ las := (List.of_mem_zip (List.of_mem_zip hr).2).1
    have hall : ∀ x ∈ las, ¬x = 0 ∧ x < 64 := by simpa using hany
    have := hall _ hm; omega
  obtain ⟨recs', h1, h2, -, h4⟩ := foldlM_consistent G q _ idx v0 lh ro' [] _ hrng hfl
  simp only [List.nil_append] at h1
  subst h1
  simp only [hro] at h4
  exact ⟨v0, ro', rfl, h4, by simpa [hlog] using h2.symm⟩

/-! ## The honest prover's rounds -/

/-- An honest round: the prover's scalar matrix fold returns, at every row, the verifier's row fold. -/
theorem honest_round (G : Gen K) (hV : GenValid G) (hN : GenNested G) (h2 : (2 : K) ≠ 0) {n a : ℕ}
    (ha : 1 ≤ a) (hna : n + a ≤ G.adicity) {w : List K} (hw : w.length = 2 ^ (n + a)) (β : K) :
    ∃ f, fold_matrix_scalar G β a w = some f ∧ f.length = 2 ^ n ∧
      ∀ t < 2 ^ n, fold_row G t n a β (rowList w a t) = some (f.getD t 0) := by
  refine ⟨_, fold_matrix_scalar_rows G hV hN h2 ha hna hw β, by simp, fun t ht => ?_⟩
  rw [rowList, fold_row_eq G hV h2 ha hna, List.getD_eq_getElem _ _ (by simpa using ht)]
  simp

/-- Honest folding preserves low degree.

Fold the codeword of P, of degree below 2^(n + a - b), by 2^a.

Add beta^(2^a) times the codeword of R, of degree below 2^(n - b).

The result is a codeword of degree below 2^(n - b). -/
theorem honest_round_degree (G : Gen K) (hV : GenValid G) (hN : GenNested G) (h2 : (2 : K) ≠ 0)
    {n a b : ℕ} (ha : 1 ≤ a) (hna : n + a ≤ G.adicity) (hbn : b ≤ n) {P R : K[X]} {w u : List K}
    (hw : IsCodeword G P (n + a) w) (hP : P.degree < ↑(2 ^ (n + a - b)))
    (hu : IsCodeword G R n u) (hR : R.degree < ↑(2 ^ (n - b))) (β : K) :
    ∃ f, fold_matrix_scalar G β a w = some f ∧
      IsCodeword G (polyFold P (2 ^ a) β + C (β ^ 2 ^ a) * R) n
        (List.zipWith (fun c x => c + β ^ 2 ^ a * x) f u) ∧
      (polyFold P (2 ^ a) β + C (β ^ 2 ^ a) * R).degree < ↑(2 ^ (n - b)) := by
  obtain ⟨f, hf, hfc⟩ := fold_matrix_scalar_codeword G hV hN h2 ha hna hw β
  refine ⟨f, hf, ⟨by simp [hfc.1, hu.1], fun t ht => ?_⟩, ?_⟩
  · rw [List.getD_eq_getElem _ _ (by simp [hfc.1, hu.1, ht]), List.getElem_zipWith,
      ← List.getD_eq_getElem _ 0, ← List.getD_eq_getElem _ 0, hfc.2 t ht, hu.2 t ht]
    simp
  · refine lt_of_le_of_lt (degree_add_le _ _) (max_lt ?_ ?_)
    · have hle : ((2 ^ (n + a - b) : ℕ) : WithBot ℕ) ≤ ((2 ^ a * 2 ^ (n - b) : ℕ) : WithBot ℕ) := by
        rw [show n + a - b = a + (n - b) by omega, pow_add]
      exact degree_polyFold_lt (lt_of_lt_of_le hP hle) β
    · rw [C_mul']; exact lt_of_le_of_lt (degree_smul_le _ _) hR

end Plonky3Lean.Proofs.Fri
