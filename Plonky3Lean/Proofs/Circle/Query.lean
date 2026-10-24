module

public import Plonky3Lean.Proofs.Circle.Pcs
public import Plonky3Lean.Proofs.Circle.Deep

@[expose] public section

/-!
# p3-circle: one query of the verifier is the folding of Section 4

At round r, a query reads its running value at the point sigma_r x_r.

Here x_r is the round's x-twiddle, and sigma_r is the sign that bit r of the query index selects.

The row it rebuilds holds the values at x_r and -x_r, so its fold is equation (19):

```text
    g(x) = g_0(pi(x)) + x g_1(pi(x)),     fold = g_0 + beta g_1, read at pi(x_r) = sigma_(r+1) x_(r+1)
```

Over all rounds, a function of 2^R coefficients folds to the constant its coefficients fold to.
-/

namespace Plonky3Lean.Proofs.Circle

open Plonky3Lean.Spec.Circle Plonky3Lean.Proofs.Dft Finset
open p3_dft.mirror p3_fri.mirror p3_fri.config.mirror p3_circle.point.mirror p3_circle.folding.mirror
open p3_circle.verifier.mirror p3_circle.ordering.mirror

set_option linter.unusedSectionVars false

variable {K : Type} [Field K] [DecidableEq K] {G : Gen (K × K)}

/-- The sign bit r of the query index t selects: 1 for 0, -1 for 1. -/
def sgn (t r : ℕ) : K := if (t / 2 ^ r) % 2 = 0 then 1 else -1

/-- The even coefficients plus beta times the odd ones: the coefficients of g_0 + beta g_1. -/
def foldCoeffs (d : ℕ → K) (β : K) : ℕ → K := fun k => d (2 * k) + β * d (2 * k + 1)

theorem piX_eq_vnStep (x : K) : piX x = Point.vnStep x := by
  unfold piX Point.vnStep; ring

/-- The x-twiddle of every round is nonzero. -/
theorem Xq_ne_zero (hV : CircleGenValid G) (h2 : (2 : K) ≠ 0) {L r : ℕ} (t : ℕ) (hr : r + 1 ≤ L)
    (hG : L + 2 ≤ G.adicity) : Xq G L t r ≠ 0 := by
  have := twC_standard_ne_zero hV h2 (n := L + 1 - r) (by omega) (by omega) (j := 1)
    (b := t / 2 ^ (r + 1)) (by omega)
  simp only [twC, one_ne_zero, ↓reduceIte, Nat.sub_self, pow_zero, one_nsmul] at this
  rwa [Xq, show L + 2 - r = L + 1 - r + 1 by omega, show L - 1 - r = L + 1 - r - 1 - 1 by omega,
    show L - r = L + 1 - r - 1 by omega]

/-- Squaring the twiddle of round r gives the point round r + 1 reads. -/
theorem piX_Xq (hV : CircleGenValid G) {L t r : ℕ} (hr : r + 2 ≤ L - 1) (hG : L + 2 ≤ G.adicity) :
    piX (Xq G L t r) = sgn t (r + 1) * Xq G L t (r + 1) := by
  rw [← Xq_succ hV hr hG, piX_eq_vnStep, sgn]
  split_ifs with h0 h1 <;> first | omega | ring

/-- The row a round rebuilds holds the values at x and -x, in that order. -/
theorem rebuildRow_honest (g : K → K) (t r : ℕ) (x : K) :
    rebuildRow 2 ((t / 2 ^ r) % 2) (g (sgn t r * x)) [g (-(sgn t r * x))] = some [g x, g (-x)] := by
  rcases Nat.mod_two_eq_zero_or_one (t / 2 ^ r) with h | h
  · rw [h, rebuildRow_two 0 (by norm_num)]; simp [sgn, h]
  · rw [h, rebuildRow_two 1 (by norm_num)]; simp [sgn, h]

/-- One round of a query on honest values: the fold of the row is g_0 + beta g_1 at pi(x_r). -/
theorem foldStep_honest (h2 : (2 : K) ≠ 0) (q : ℕ) (tw : List K) {t r m : ℕ} {x β : K} (hx : x ≠ 0)
    (htw : tw[r]? = some x⁻¹) (d : ℕ → K) (lh : ℕ) (hlh : 1 ≤ lh) (svs : List (List K))
    (hsv : svs[q]? = some [xEval (m + 1) d (-(sgn t r * x))]) (ro : List (ℕ × K))
    (hro : ∀ v ro', ro = (lh, v) :: ro' → False) (acc : List (ℕ × List K)) :
    foldStep q tw (t / 2 ^ r, xEval (m + 1) d (sgn t r * x), lh, ro, acc) ((β, 1, svs), r) =
      some (t / 2 ^ (r + 1), xEval m (foldCoeffs d β) (piX x), lh - 1, ro,
        acc ++ [(t / 2 ^ (r + 1), [xEval (m + 1) d x, xEval (m + 1) d (-x)])]) := by
  have hdiv : t / 2 ^ r / 2 = t / 2 ^ (r + 1) := by rw [Nat.div_div_eq_div_mul, ← pow_succ]
  have hfold : fold_row_with_inv_twiddle x⁻¹ β [xEval (m + 1) d x, xEval (m + 1) d (-x)] =
      some (xEval m (foldCoeffs d β) (piX x)) := by
    simp only [fold_row_with_inv_twiddle, Option.some.injEq]
    rw [fold_formula, foldPair_xEval h2 hx]; rfl
  unfold foldStep
  rcases ro with _ | ⟨⟨h1, v1⟩, ro'⟩
  · simp only [hsv, pow_one, rebuildRow_honest, show ¬ lh < 1 by omega, ↓reduceIte, ne_eq, not_true_eq_false,
      htw, hfold, hdiv, Option.bind_eq_bind, Option.bind_some]
  · have hh : h1 ≠ lh := fun h => hro v1 ro' (by rw [h])
    simp only [hh, ↓reduceIte, hsv, pow_one, rebuildRow_honest, show ¬ lh < 1 by omega, ne_eq,
      not_true_eq_false, htw, hfold, hdiv, Option.bind_eq_bind, Option.bind_some]

/-- The same round when an input is rolled in first: the rolled-in sum is what the row holds. -/
theorem foldStep_honest_roll (h2 : (2 : K) ≠ 0) (q : ℕ) (tw : List K) {t r m : ℕ} {x β : K} (hx : x ≠ 0)
    (htw : tw[r]? = some x⁻¹) (d : ℕ → K) (lh : ℕ) (hlh : 1 ≤ lh) (svs : List (List K))
    (hsv : svs[q]? = some [xEval (m + 1) d (-(sgn t r * x))]) (v a : K) (ro' : List (ℕ × K))
    (hva : v + a = xEval (m + 1) d (sgn t r * x)) (acc : List (ℕ × List K)) :
    foldStep q tw (t / 2 ^ r, v, lh, (lh, a) :: ro', acc) ((β, 1, svs), r) =
      some (t / 2 ^ (r + 1), xEval m (foldCoeffs d β) (piX x), lh - 1, ro',
        acc ++ [(t / 2 ^ (r + 1), [xEval (m + 1) d x, xEval (m + 1) d (-x)])]) := by
  have hdiv : t / 2 ^ r / 2 = t / 2 ^ (r + 1) := by rw [Nat.div_div_eq_div_mul, ← pow_succ]
  have hfold : fold_row_with_inv_twiddle x⁻¹ β [xEval (m + 1) d x, xEval (m + 1) d (-x)] =
      some (xEval m (foldCoeffs d β) (piX x)) := by
    simp only [fold_row_with_inv_twiddle, Option.some.injEq]
    rw [fold_formula, foldPair_xEval h2 hx]; rfl
  unfold foldStep
  simp only [↓reduceIte, hva, hsv, pow_one, rebuildRow_honest, show ¬ lh < 1 by omega, ne_eq,
    not_true_eq_false, htw, hfold, hdiv, Option.bind_eq_bind, Option.bind_some]

theorem xEval_add (m : ℕ) (d e : ℕ → K) (x : K) :
    xEval m (fun k => d k + e k) x = xEval m d x + xEval m e x := by
  simp only [xEval, smul_add, sum_add_distrib]

theorem xEval_zero_coeffs (m : ℕ) (x : K) : xEval m (fun _ => (0 : K)) x = 0 := by
  simp [xEval]

theorem xEval_zero_levels (d : ℕ → K) (x : K) : xEval 0 d x = d 0 := by
  simp [xEval, xBasis]

/-- The coefficients of the honest layer of round r: each round folds the last one and adds its input. -/
def layer (E : ℕ → ℕ → K) (β : ℕ → K) : ℕ → ℕ → K
  | 0 => E 0
  | r + 1 => fun k => foldCoeffs (layer E β r) (β r) k + E (r + 1) k

/-- The coefficients a round holds before its input is rolled in. -/
def preLayer (E : ℕ → ℕ → K) (β : ℕ → K) : ℕ → ℕ → K
  | 0 => fun _ => 0
  | r + 1 => foldCoeffs (layer E β r) (β r)

theorem layer_eq (E : ℕ → ℕ → K) (β : ℕ → K) (r : ℕ) :
    layer E β r = fun k => preLayer E β r k + E r k := by
  cases r with
  | zero => funext k; simp [layer, preLayer]
  | succ r => rfl

/-- The honest inputs of a query from round r0 on, tallest first.

The input of round r sits at height L - r and holds the value of its function at the point the round reads. -/
noncomputable def rollsFrom (G : Gen (K × K)) (E : ℕ → ℕ → K) (P : ℕ → Prop) [DecidablePred P] (L R t r0 : ℕ) :
    List (ℕ × K) :=
  ((List.range (R - r0)).map (· + r0)).filterMap fun r =>
    if P r then some (L - r, xEval (R - r) (E r) (sgn t r * Xq G L t r)) else none

theorem rollsFrom_succ (E : ℕ → ℕ → K) (P : ℕ → Prop) [DecidablePred P] {L R t r0 : ℕ} (h : r0 < R) :
    rollsFrom G E P L R t r0 =
      (if P r0 then [(L - r0, xEval (R - r0) (E r0) (sgn t r0 * Xq G L t r0))] else []) ++
        rollsFrom G E P L R t (r0 + 1) := by
  unfold rollsFrom
  obtain ⟨n, hn⟩ : ∃ n, R - r0 = n + 1 := ⟨R - r0 - 1, by omega⟩
  rw [hn, show R - (r0 + 1) = n by omega, List.range_succ_eq_map, List.map_cons, List.map_map]
  simp only [zero_add, List.filterMap_cons]
  split_ifs <;> simp [Function.comp_def, Nat.succ_eq_add_one, add_comm, add_left_comm, hn]

theorem rollsFrom_head (E : ℕ → ℕ → K) (P : ℕ → Prop) [DecidablePred P] {L R t r0 : ℕ} (hRL : R ≤ L)
    {h : ℕ} {a : K} {ro : List (ℕ × K)} (hh : rollsFrom G E P L R t r0 = (h, a) :: ro) : h < L + 1 - r0 := by
  unfold rollsFrom at hh
  have hmem : (h, a) ∈ ((List.range (R - r0)).map (· + r0)).filterMap fun r =>
      if P r then some (L - r, xEval (R - r) (E r) (sgn t r * Xq G L t r)) else none := by
    rw [hh]; exact List.mem_cons_self
  obtain ⟨r, hr, hra⟩ := List.mem_filterMap.mp hmem
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hr
  rw [List.mem_range] at hi
  split_ifs at hra
  cases hra; omega

/-- The rounds of a query from round r0 on: each round's beta, arity one bit, and siblings. -/
def roundsFrom (β : ℕ → K) (svOf : ℕ → List (List K)) (r0 n : ℕ) : List (K × ℕ × List (List K)) :=
  (List.range n).map fun i => (β (r0 + i), 1, svOf (r0 + i))

/-- The row a query records at round r: its group index, and the honest layer at x_r and -x_r. -/
noncomputable def honestRow (G : Gen (K × K)) (L R : ℕ) (E : ℕ → ℕ → K) (β : ℕ → K) (t r : ℕ) :
    ℕ × List K :=
  (t / 2 ^ (r + 1), [xEval (R - r) (layer E β r) (Xq G L t r), xEval (R - r) (layer E β r) (-Xq G L t r)])

theorem map_range_shift {α : Type _} (f : ℕ → α) (r0 n : ℕ) :
    (List.range (n + 1)).map (fun i => f (r0 + i)) = f r0 :: (List.range n).map (fun i => f (r0 + 1 + i)) := by
  rw [List.range_succ_eq_map, List.map_cons, List.map_map, add_zero]
  congr 1
  exact List.map_congr_left fun i _ => by simp only [Function.comp_apply]; congr 1; omega

/-- The fold chain on honest data, from round r0 to the last round R.

Each round reads the honest layer at its point, and its siblings hold the layer at the conjugate point.

The chain ends at the constant term of the coefficients before the last roll-in, with every input rolled in.

It records every round's honest row. -/
theorem foldlM_honest (hV : CircleGenValid G) (h2 : (2 : K) ≠ 0) {L R : ℕ} (hRL : R + 1 ≤ L)
    (hG : L + 2 ≤ G.adicity) (q t : ℕ) (E : ℕ → ℕ → K) (β : ℕ → K) (P : ℕ → Prop) [DecidablePred P]
    (hE : ∀ r, ¬ P r → E r = fun _ => 0) (tw : List K) (htw : ∀ r < R, tw[r]? = some (Xq G L t r)⁻¹)
    (svOf : ℕ → List (List K))
    (hsv : ∀ r < R, (svOf r)[q]? = some [xEval (R - r) (layer E β r) (-(sgn t r * Xq G L t r))]) :
    ∀ n r0 (acc : List (ℕ × List K)), r0 + n = R →
      ((roundsFrom β svOf r0 n).zipIdx r0).foldlM (foldStep q tw)
        (t / 2 ^ r0, xEval (R - r0) (preLayer E β r0) (sgn t r0 * Xq G L t r0), L - r0,
          rollsFrom G E P L R t r0, acc) =
        some (t / 2 ^ R, preLayer E β R 0, L - R, [],
          acc ++ (List.range n).map fun i => honestRow G L R E β t (r0 + i))
  | 0, r0, acc, h => by
    subst h
    simp [roundsFrom, rollsFrom, xEval_zero_levels]
  | n + 1, r0, acc, h => by
    have hlt : r0 < R := by omega
    set X := Xq G L t r0
    have hX : X ≠ 0 := Xq_ne_zero hV h2 t (by omega) hG
    obtain ⟨m, hm⟩ : ∃ m, R - r0 = m + 1 := ⟨R - r0 - 1, by omega⟩
    have hnext : xEval m (foldCoeffs (layer E β r0) (β r0)) (piX X) =
        xEval (R - (r0 + 1)) (preLayer E β (r0 + 1)) (sgn t (r0 + 1) * Xq G L t (r0 + 1)) := by
      rw [show R - (r0 + 1) = m by omega]
      rcases Nat.lt_or_ge (r0 + 1) R with hr | hr
      · rw [piX_Xq hV (by omega) hG]; rfl
      · obtain rfl : m = 0 := by omega
        rw [xEval_zero_levels, xEval_zero_levels]; rfl
    have hlist : (roundsFrom β svOf r0 (n + 1)).zipIdx r0 =
        ((β r0, 1, svOf r0), r0) :: (roundsFrom β svOf (r0 + 1) n).zipIdx (r0 + 1) := by
      simp only [roundsFrom, List.range_succ_eq_map, List.map_cons, add_zero, List.map_map, List.zipIdx_cons]
      congr 3
      funext i; simp [Nat.succ_eq_add_one, add_comm, add_left_comm]
    rw [hlist, List.foldlM_cons, rollsFrom_succ E P hlt]
    have hsv' := hsv r0 hlt
    rw [hm] at hsv'
    by_cases hP : P r0
    · simp only [hP, ↓reduceIte, List.singleton_append]
      rw [foldStep_honest_roll h2 q tw hX (htw r0 hlt) (layer E β r0) (L - r0) (by omega) (svOf r0) hsv' _ _ _
        (by rw [hm, layer_eq, xEval_add]) acc]
      simp only [Option.bind_eq_bind, Option.bind_some]
      rw [hnext, show L - r0 - 1 = L - (r0 + 1) by omega,
        foldlM_honest hV h2 hRL hG q t E β P hE tw htw svOf hsv n (r0 + 1) _ (by omega)]
      rw [map_range_shift, List.append_assoc, List.singleton_append]
      simp only [honestRow, hm]; rfl
    · simp only [hP, ↓reduceIte, List.nil_append]
      have hpre : xEval (R - r0) (preLayer E β r0) (sgn t r0 * X) =
          xEval (m + 1) (layer E β r0) (sgn t r0 * X) := by
        rw [hm, layer_eq, xEval_add, hE r0 hP, xEval_zero_coeffs, add_zero]
      rw [hpre, foldStep_honest h2 q tw hX (htw r0 hlt) (layer E β r0) (L - r0) (by omega) (svOf r0) hsv'
        _ (fun v ro' hro => by
          have := rollsFrom_head (G := G) E P (by omega : R ≤ L) hro; omega) acc]
      simp only [Option.bind_eq_bind, Option.bind_some]
      rw [hnext, show L - r0 - 1 = L - (r0 + 1) by omega,
        foldlM_honest hV h2 hRL hG q t E β P hE tw htw svOf hsv n (r0 + 1) _ (by omega)]
      rw [map_range_shift, List.append_assoc, List.singleton_append]
      simp only [honestRow, hm]; rfl

/-- One query's fold chain on honest data returns the folded constant.

The inputs are rolled in at their heights, every round folds the honest layer, and the chain ends at the final height. -/
theorem fold_query_honest {ME IE : Type} (hV : CircleGenValid G) (h2 : (2 : K) ≠ 0) {lb R : ℕ} (hlb : 1 ≤ lb)
    (hG : R + lb + 2 ≤ G.adicity) (q t : ℕ) (E : ℕ → ℕ → K) (betas : List K) (hβ : betas.length = R)
    (P : ℕ → Prop) [DecidablePred P] (hE : ∀ r, ¬ P r → E r = fun _ => 0)
    (svs : List (List (List K))) (hsvl : svs.length = R) (tw : List K)
    (htw : ∀ r < R, tw[r]? = some (Xq G (R + lb) t r)⁻¹)
    (hsv : ∀ r < R, (svs.getD r [])[q]? =
      some [xEval (R - r) (layer E (betas.getD · 0) r) (-(sgn t r * Xq G (R + lb) t r))]) :
    fold_query (ME := ME) (IE := IE) lb q t betas (List.replicate R 1) svs
        (rollsFrom G E P (R + lb) R t 0) (R + lb) tw =
      pure (preLayer E (betas.getD · 0) R 0,
        (List.range R).map fun r => honestRow G (R + lb) R E (betas.getD · 0) t r) := by
  have hlist : betas.zip ((List.replicate R 1).zip svs) =
      roundsFrom (betas.getD · 0) (svs.getD · []) 0 R := by
    apply List.ext_getElem
    · simp [roundsFrom, hβ, hsvl]
    · intro i h1 h2'
      simp only [List.length_zip, List.length_replicate] at h1
      simp [roundsFrom, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show i < betas.length by omega),
        List.getElem?_eq_getElem (show i < svs.length by omega)]
  have hacc := foldlM_honest hV h2 (by omega) (by omega) q t E (betas.getD · 0) P hE tw htw
    (svs.getD · []) hsv R 0 [] (by omega)
  have h0 : xEval (R - 0) (preLayer E (betas.getD · 0) 0) (sgn t 0 * Xq G (R + lb) t 0) = 0 := by
    simp only [preLayer]; exact xEval_zero_coeffs _ _
  rw [h0] at hacc
  simp only [pow_zero, Nat.div_one, Nat.sub_zero] at hacc
  unfold fold_query
  rw [hlist, hacc]
  simp [lift, show R + lb - R = lb by omega]

/-! ## Completeness of the query checks -/

/-- The x-coordinate of group j at round r: the twiddle every query in that group uses. -/
noncomputable def Xg (G : Gen (K × K)) (L r j : ℕ) : K :=
  (genPt G (L + 2 - r) + Plonky3Lean.Spec.Matrix.bitRev (L - 1 - r) j • genPt G (L - r)).x

theorem Xq_eq_Xg (L t r : ℕ) : Xq G L t r = Xg G L r (t / 2 ^ (r + 1)) := rfl

/-- The honest codeword of round r at group j: the layer at the group's x and at its negation. -/
noncomputable def honestWord (G : Gen (K × K)) (L R : ℕ) (E : ℕ → ℕ → K) (β : ℕ → K) (r j : ℕ) : List K :=
  [xEval (R - r) (layer E β r) (Xg G L r j), xEval (R - r) (layer E β r) (-Xg G L r j)]

theorem honestRow_eq (L R : ℕ) (E : ℕ → ℕ → K) (β : ℕ → K) (t r : ℕ) :
    honestRow G L R E β t r = (t / 2 ^ (r + 1), honestWord G L R E β r (t / 2 ^ (r + 1))) := rfl

theorem desc_rollsFrom (E : ℕ → ℕ → K) (P : ℕ → Prop) [DecidablePred P] {L R : ℕ} (hRL : R ≤ L) (t : ℕ) :
    Desc (rollsFrom G E P L R t 0) := by
  apply desc_of_pairwise
  unfold rollsFrom
  rw [List.pairwise_filterMap, List.pairwise_map]
  refine List.pairwise_lt_range.imp_of_mem fun {a b} ha hb hab => ?_
  rw [List.mem_range] at ha hb
  intro x hx y hy
  split_ifs at hx hy
  cases hx; cases hy; simp only; omega

/-- A fold whose every step returns the height less one returns the height less the step count. -/
theorem foldlM_steps {ε α : Type _} (f : ℕ → α × ℕ → ExceptT ε Option ℕ) :
    ∀ (l : List α) (r0 h : ℕ), (∀ a i, (a, i) ∈ l.zipIdx r0 → f (h - (i - r0)) (a, i) = pure (h - (i - r0) - 1)) →
      (l.zipIdx r0).foldlM f h = pure (h - l.length)
  | [], _, h, _ => by simp
  | a :: l, r0, h, hf => by
    have h0 := hf a r0 (by simp)
    rw [Nat.sub_self, Nat.sub_zero] at h0
    rw [List.zipIdx_cons, List.foldlM_cons, h0, pure_bind,
      foldlM_steps f l (r0 + 1) (h - 1) fun b i hi => by
        have hi' := (List.mem_zipIdx hi).1
        have := hf b i (by rw [List.zipIdx_cons]; exact List.mem_cons_of_mem _ hi)
        rwa [show h - (i - r0) = h - 1 - (i - (r0 + 1)) by omega] at this]
    rw [List.length_cons, Nat.sub_sub, Nat.add_comm 1]

theorem mapM_eq_pure_map {ε α β : Type _} {f : α → ExceptT ε Option β} {g : α → β} :
    ∀ (l : List α), (∀ x ∈ l, f x = pure (g x)) → l.mapM f = pure (l.map g)
  | [], _ => rfl
  | x :: l, h => by
    rw [List.mapM_cons, h x List.mem_cons_self, pure_bind,
      mapM_eq_pure_map l fun y hy => h y (List.mem_cons_of_mem _ hy)]
    rfl

theorem mapInputError_pure {ME IE α : Type} (a : α) :
    mapInputError (ME := ME) (pure a : ExceptT IE Option α) = pure a := rfl

/-- The twiddle chain of a query, on any round count below the height. -/
theorem query_twiddles_eq (hV : CircleGenValid G) (h2 : (2 : K) ≠ 0) (t : ℕ) {L R : ℕ}
    (hRL : R + 1 ≤ L) (hG : L + 2 ≤ G.adicity) :
    query_x_twiddles_inv G t L R = some ((List.range R).map fun r => (Xq G L t r)⁻¹) := by
  rcases Nat.eq_zero_or_pos R with rfl | hR
  · simp [query_x_twiddles_inv]
  · exact query_x_twiddles_inv_eq hV h2 t hR hRL hG

/-- Completeness of the query checks.

Take inputs and commit-phase siblings that hold the honest layers at the points each query reads.

Take a final constant equal to the folded coefficients, and a commit-phase scheme that accepts the honest codewords.

Then the query checks accept. -/
theorem verify_queries_complete (hV : CircleGenValid G) (h2 : (2 : K) ≠ 0) {IE IP : Type} (fmmcs : MmcsOps K)
    (params : FriParameters) (proof : CircleFriProof K fmmcs.Commitment fmmcs.MultiProof IP)
    (betas : List K) (indices : List ℕ) {R : ℕ}
    (open_inputs : List ℕ → IP → ExceptT IE Option (List (List (ℕ × K))))
    (E : ℕ → ℕ → K) (P : ℕ → Prop) [DecidablePred P] (hE : ∀ r, ¬ P r → E r = fun _ => 0)
    (hlb : 1 ≤ params.log_blowup) (hG : R + params.log_blowup + 2 ≤ G.adicity) (hβ : betas.length = R)
    (hopn : proof.commit_phase_openings.length = R)
    (hopen : open_inputs indices proof.input_openings =
      pure (indices.map fun i => rollsFrom G E P (R + params.log_blowup) R (i / 2) 0))
    (hsv : ∀ r < R, ∀ (q i : ℕ), indices[q]? = some i →
      ((proof.commit_phase_openings.map (·.sibling_values)).getD r [])[q]? =
        some [xEval (R - r) (layer E (betas.getD · 0) r)
          (-(sgn (i / 2) r * Xq G (R + params.log_blowup) (i / 2) r))])
    (hfinal : proof.final_poly = preLayer E (betas.getD · 0) R 0)
    (hmmcs : ∀ r < R, ∀ (c : fmmcs.Commitment) (o : CommitPhaseMultiStep K fmmcs.MultiProof),
      proof.commit_phase_commits[r]? = some c → proof.commit_phase_openings[r]? = some o →
      ∀ groups : List ℕ, fmmcs.verify_multi_batch c [(2, 2 ^ (R + params.log_blowup - (r + 1)))] groups
        (groups.map fun j => [honestWord G (R + params.log_blowup) R E (betas.getD · 0) r j]) o.opening_proof =
          .ok ()) :
    verify_queries G fmmcs params proof betas indices (List.replicate R 1) open_inputs = pure () := by
  set L := R + params.log_blowup
  set β : ℕ → K := (betas.getD · 0)
  have hrec : ((indices.zip (indices.map fun i => rollsFrom G E P L R (i / 2) 0)).zipIdx).mapM
      (checkQuery (ME := fmmcs.Error) (IE := IE) G params.log_blowup betas (List.replicate R 1)
        (proof.commit_phase_openings.map (·.sibling_values)) proof.final_poly L) =
      pure (((indices.zip (indices.map fun i => rollsFrom G E P L R (i / 2) 0)).zipIdx).map
        fun e => (List.range R).map fun r => honestRow G L R E β (e.1.1 / 2) r) := by
    refine mapM_eq_pure_map _ fun e he => ?_
    obtain ⟨⟨i, ro⟩, q⟩ := e
    obtain ⟨hq, he'⟩ := List.mem_zipIdx' he
    simp only [List.length_zip, List.length_map, min_self] at hq
    simp only [List.getElem_zip, List.getElem_map, Prod.mk.injEq] at he'
    obtain ⟨hi, hro⟩ := he'
    rw [← hi] at hro
    subst hro
    have hiq : indices[q]? = some i := by rw [List.getElem?_eq_getElem hq, hi]
    unfold checkQuery
    have hd := desc_rollsFrom (G := G) E P (show R ≤ L by omega) (i / 2)
    rw [Desc] at hd
    simp only [hd, Bool.not_true, Bool.false_eq_true, ↓reduceIte, List.length_replicate, lift,
      query_twiddles_eq hV h2 (i / 2) (show R + 1 ≤ L by omega) (by omega), lift_some_bind']
    rw [fold_query_honest hV h2 hlb hG q (i / 2) E betas hβ P hE _ (by simpa using hopn) _
      (fun r hr => by simp [hr]; rfl) (fun r hr => hsv r hr q i hiq)]
    simp [hfinal, β]; rfl
  unfold verify_queries
  simp only [List.sum_replicate, smul_eq_mul, mul_one, hopen, mapInputError_pure, pure_bind]
  rw [hrec, pure_bind]
  set recorded := ((indices.zip (indices.map fun i => rollsFrom G E P L R (i / 2) 0)).zipIdx).map
    fun e => (List.range R).map fun r => honestRow G L R E β (e.1.1 / 2) r
  rw [foldlM_steps _ _ 0 L fun a i hai => ?_, pure_bind]
  obtain ⟨hi, ha⟩ := List.mem_zipIdx' hai
  simp only [List.length_zip, List.length_replicate, Nat.sub_zero] at hi ⊢
  obtain ⟨c, o, la⟩ := a
  simp only [List.getElem_zip, List.getElem_replicate, Prod.mk.injEq] at ha
  obtain ⟨hc, ho, rfl⟩ := ha
  have hiR : i < R := by omega
  unfold checkRound
  have hrows : recorded.map (fun rs => [(rs.getD i (0, [])).2]) =
      (recorded.map fun rs => (rs.getD i (0, [])).1).map fun j => [honestWord G L R E β i j] := by
    simp only [recorded, List.map_map]
    refine List.map_congr_left fun e _ => ?_
    simp [List.getD_eq_getElem?_getD, hiR, honestRow_eq]
  dsimp only
  rw [hrows, pow_one, show L - i - 1 = L - (i + 1) by omega,
    hmmcs i hiR c o (by rw [hc]; simp) (by rw [ho]; simp)]

/-! ## The first layer -/

local notation "rev" => Plonky3Lean.Spec.Matrix.bitRev

/-- A point of a standard domain of size 2^(n+1), read in circle FFT order at index i'.

Its x-coordinate is the circle FRI twiddle of the pair i' / 2, signed by the pair's parity. -/
theorem twinPoint_cfft_x (hV : CircleGenValid G) {n : ℕ} (hn : 1 ≤ n) (hG : n + 2 ≤ G.adicity) {i' : ℕ}
    (hi : i' < 2 ^ (n + 1)) :
    (twinPoint (genPt G (n + 2)) (genPt G n) (cfft_permute_index i' (n + 1))).x =
      (if (i' / 2) % 2 = 0 then 1 else -1) * (genPt G (n + 2) + rev (n - 1) (i' / 2 / 2) • genPt G n).x := by
  set Q := genPt G (n + 2)
  have htw : ∀ k, twinPoint Q (genPt G n) k = (2 * k + 1) • Q := fun k => by
    have := twinPoint_standard hV (n := n + 1) (by omega) hG k
    rwa [show n + 1 - 1 = n by omega] at this
  have h4 : genPt G n = 4 • Q := by
    have := genPt_nsmul hV (j := n) (k := n + 2) (by omega) hG
    rw [show n + 2 - n = 2 by omega] at this
    rw [← this]; norm_num [Q]
  have hzero : 2 ^ (n + 2) • Q = 0 := by
    have := genPt_nsmul hV (j := 0) (k := n + 2) (by omega) hG
    rwa [Nat.sub_zero, genPt_zero hV] at this
  have hone : 2 ^ (n + 1) • Q = genPt G 1 := by
    have := genPt_nsmul hV (j := 1) (k := n + 2) (by omega) hG
    rwa [show n + 2 - 1 = n + 1 by omega] at this
  set a := i' / 2
  have ha : a < 2 ^ n := by rw [pow_succ] at hi; omega
  -- Both members of the pair have the x-coordinate of (4 rev_n(a) + 1) Q.
  have hpair : (twinPoint Q (genPt G n) (cfft_permute_index i' (n + 1))).x = ((4 * rev n a + 1) • Q).x := by
    rcases Nat.even_or_odd' i' with ⟨b, hb | hb⟩
    · obtain rfl : b = a := by omega
      rw [hb, cfft_permute_index_even ha, htw]; ring_nf
    · obtain rfl : b = a := by omega
      rw [hb, cfft_permute_index_odd ha, htw, rev_complement n ha]
      have hr := Plonky3Lean.Proofs.Matrix.bitRev_lt n a
      have : (2 * (2 * (2 ^ n - 1 - rev n a) + 1) + 1) + (4 * rev n a + 1) = 2 ^ (n + 2) := by
        rw [pow_add]; omega
      have hneg : (2 * (2 * (2 ^ n - 1 - rev n a) + 1) + 1) • Q = -((4 * rev n a + 1) • Q) := by
        rw [eq_neg_iff_add_eq_zero, ← add_nsmul, this, hzero]
      rw [hneg, C.neg_x]
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [hpair, Nat.add_sub_cancel, h4, smul_smul]
  have hrev : rev (m + 1) a = (a % 2) * 2 ^ m + rev m (a / 2) := rfl
  have hQ : Q + (rev m (a / 2) * 4) • Q = (4 * rev m (a / 2) + 1) • Q := by
    rw [add_nsmul, one_nsmul, add_comm, mul_comm]
  rw [hQ, hrev]
  rcases Nat.mod_two_eq_zero_or_one a with h0 | h1
  · rw [h0]; simp
  · rw [h1, show 4 * (1 * 2 ^ m + rev m (a / 2)) + 1 = 2 ^ (m + 1 + 1) + (4 * rev m (a / 2) + 1)
      by ring, add_nsmul, hone, add_comm, add_genPt_one_x hV (by omega)]
    simp

/-- The first-layer point of a query at height h, read in circle FFT order, sits at the circle FRI point of round H - h.

Its x-coordinate is sigma_r x_r, for r = H - h. -/
theorem firstLayer_point_x (hV : CircleGenValid G) {H h : ℕ} (hh : 2 ≤ h) (hhH : h ≤ H) (hG : H + 1 ≤ G.adicity)
    {i : ℕ} (hi : i < 2 ^ H) :
    (twinPoint (genPt G (h + 1)) (genPt G (h - 1)) (cfft_permute_index (i / 2 ^ (H - h)) h)).x =
      sgn (i / 2) (H - h) * Xq G (H - 1) (i / 2) (H - h) := by
  obtain ⟨n, rfl⟩ : ∃ n, h = n + 1 := ⟨h - 1, by omega⟩
  have hi' : i / 2 ^ (H - (n + 1)) < 2 ^ (n + 1) := by
    rw [Nat.div_lt_iff_lt_mul (by positivity), ← pow_add, show n + 1 + (H - (n + 1)) = H by omega]; exact hi
  rw [show n + 1 + 1 = n + 2 by omega, Nat.add_sub_cancel, twinPoint_cfft_x hV (by omega) (by omega) hi']
  have e1 : i / 2 ^ (H - (n + 1)) / 2 = i / 2 / 2 ^ (H - (n + 1)) := by
    rw [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul, mul_comm]
  have e2 : i / 2 / 2 ^ (H - (n + 1)) / 2 = i / 2 / 2 ^ (H - (n + 1) + 1) := by
    rw [Nat.div_div_eq_div_mul, ← pow_succ]
  rw [e1, e2, sgn, Xq, show H - 1 + 2 - (H - (n + 1)) = n + 2 by omega,
    show H - 1 - 1 - (H - (n + 1)) = n - 1 by omega, show H - 1 - (H - (n + 1)) = n by omega]

/-- The first-layer fold of an honest pair is equation (14) to (16): f_0 + beta f_1 at P.x.

The verifier holds the pair in the order its parity bit b gives, with the y-twiddle signed to match. -/
theorem firstLayer_fold (h2 : (2 : K) ≠ 0) {P : C K} (hy : P.y ≠ 0) (b : ℕ) (m : ℕ) (c : ℕ → K) (β : K) :
    fold_row_with_inv_twiddle (if b = 0 then P.y else -P.y)⁻¹ β
        (if b = 0 then [fftEval (m + 1) c P, fftEval (m + 1) c (-P)]
          else [fftEval (m + 1) c (-P), fftEval (m + 1) c P]) =
      some (xEval m (foldCoeffs c β) P.x) := by
  split_ifs
  · simp only [fold_row_with_inv_twiddle, Option.some.injEq]
    rw [fold_formula, foldPair_fftEval h2 hy]; rfl
  · simp only [fold_row_with_inv_twiddle, Option.some.injEq]
    have hy' : (-P).y ≠ 0 := by rw [C.neg_y]; exact neg_ne_zero.mpr hy
    have := foldPair_fftEval h2 hy' m c β
    rw [neg_neg, C.neg_x, C.neg_y] at this
    rw [fold_formula, this]; rfl

/-! ## The DEEP quotients of one query -/

open p3_circle.deep_quotient.mirror in
theorem dot_product_range_prefix (f : ℕ → K) {M : ℕ} (r : List K) (h : r.length ≤ M) :
    dot_product ((List.range M).map f) r = dot_product ((List.range r.length).map f) r := by
  unfold dot_product
  rw [List.zip_eq_zip_take_min, List.zip_eq_zip_take_min (l₁ := (List.range r.length).map f)]
  simp [← List.map_take, List.take_range, min_eq_right h, Nat.min_eq_left h]

open p3_circle.deep_quotient.mirror in
/-- The verifier's powers of alpha run to the widest claim; the row reduction reads only as many as the row has. -/
theorem reduce_row_prefix (αW α : K) {M : ℕ} (x z : Point K) (ps qs : List K) (hpq : ps.length = qs.length)
    (hM : ps.length ≤ M) :
    deep_quotient_reduce_row αW ((List.range M).map (α ^ ·)) x z ps qs =
      deep_quotient_reduce_row αW ((List.range ps.length).map (α ^ ·)) x z ps qs := by
  unfold deep_quotient_reduce_row
  have hl : ((ps.zip qs).map fun p => -p.2 + p.1).length = ps.length := by simp [hpq]
  rw [dot_product_range_prefix _ _ (by rw [hl]; exact hM), hl]

/-- The DEEP term of one opening point at a query, Proposition 4:

```text
    sum_j alpha^j Re(q_j) + alpha^(W + j) Im(q_j),     q_j = (p_j(x) - p_j(zeta)) / v_zeta(x)
``` -/
noncomputable def deepTerm (α : K) (P Q : C K) (ps qs : List K) : K :=
  ∑ j ∈ range ps.length, (α ^ j * (cquot (ps.getD j 0 - qs.getD j 0) (Point.v_p (ofC P) (ofC Q))).1 +
    α ^ (ps.length + j) * (cquot (ps.getD j 0 - qs.getD j 0) (Point.v_p (ofC P) (ofC Q))).2)

theorem foldlM_eq_pure_foldl {ε α β : Type _} {f : β → α → ExceptT ε Option β} {g : β → α → β} :
    ∀ (l : List α) (e : β), (∀ e, ∀ p ∈ l, f e p = pure (g e p)) → l.foldlM f e = pure (l.foldl g e)
  | [], _, _ => rfl
  | p :: l, e, h => by
    rw [List.foldlM_cons, h e p List.mem_cons_self, pure_bind,
      foldlM_eq_pure_foldl l _ fun e q hq => h e q (List.mem_cons_of_mem _ hq)]
    rfl

/-- The point of the circle an opening point t names, and the neutral element at t^2 = -1. -/
noncomputable def ptOf (t : K) : C K := if h : 1 + t * t = 0 then 0 else stereo t h

open p3_circle.pcs.mirror p3_commit.pcs.univariate.mirror p3_circle.domain.mirror
  p3_circle.deep_quotient.mirror in
/-- One matrix of a query adds, at its height, every point's DEEP term times the running power of alpha.

That power is alpha^(2 W) for each point before it, W the matrix's width. -/
theorem reduceMatrix_eq {IME FME : Type} (hV : CircleGenValid G) (h2 : (2 : K) ≠ 0) {lb H : ℕ} (α : K) {M : ℕ}
    (index : ℕ) (acc : ℕ → K × K) (keys : List ℕ) (mat : MatrixOpening K (CircleDomain K)) (row : List K)
    (hn : 1 ≤ mat.domain.log_n) (hh : mat.domain.log_n + lb ≤ H) (hG : H + 1 ≤ G.adicity) (hM : row.length ≤ M)
    (hlen : ∀ p ∈ mat.points, p.values.length = row.length)
    (hpts : ∀ p ∈ mat.points, 1 + p.point * p.point ≠ 0 ∧ ptOf p.point ≠
      twinPoint (genPt G (mat.domain.log_n + lb + 1)) (genPt G (mat.domain.log_n + lb - 1))
        (cfft_permute_index (index / 2 ^ (H - (mat.domain.log_n + lb))) (mat.domain.log_n + lb))) :
    reduceMatrix (IME := IME) (FME := FME) G lb H ((List.range M).map (α ^ ·)) index (acc, keys)
        (mat, row, α ^ row.length, (α ^ row.length) ^ 2) =
      pure (Function.update acc (mat.domain.log_n + lb)
        (mat.points.foldl (fun e p => (e.1 * (α ^ row.length) ^ 2, e.2 + e.1 *
          deepTerm α (twinPoint (genPt G (mat.domain.log_n + lb + 1)) (genPt G (mat.domain.log_n + lb - 1))
            (cfft_permute_index (index / 2 ^ (H - (mat.domain.log_n + lb))) (mat.domain.log_n + lb)))
            (ptOf p.point) row p.values))
          (acc (mat.domain.log_n + lb))),
        if mat.domain.log_n + lb ∈ keys then keys else keys ++ [mat.domain.log_n + lb]) := by
  set h := mat.domain.log_n + lb
  set T := twinPoint (genPt G (h + 1)) (genPt G (h - 1)) (cfft_permute_index (index / 2 ^ (H - h)) h)
  have hpt := standard_nth_point hV (h := h) (by omega) (by omega) (cfft_permute_index (index / 2 ^ (H - h)) h)
  rw [standard_eq hV _ (by omega), Option.bind_some] at hpt
  unfold reduceMatrix
  dsimp only
  rw [ite_eq_right (by omega), standard_eq hV _ (by omega), lift_some_bind']
  erw [hpt, lift_some_bind']
  rw [foldlM_eq_pure_foldl _ _ fun e p hp => ?_, pure_bind]
  obtain ⟨hp1, hp2⟩ := hpts p hp
  have hz : Point.from_projective_line p.point = some (ofC (ptOf p.point)) := by
    rw [from_projective_line_eq, dite_eq_right hp1, ptOf, dite_eq_right hp1]
  rw [ite_eq_right (by rw [hlen p hp]; simp), hz, lift_some_bind',
    reduce_row_prefix _ α _ _ row p.values (hlen p hp).symm hM,
    reduce_row_eq_re_im h2 α T (ptOf p.point) (Ne.symm hp2) row p.values (hlen p hp).symm]
  rfl

open p3_circle.pcs.mirror in
/-- The first layer of one height at one query, on honest values, is the input circle FRI rolls in at round H - h.

Take the lambda-corrected DEEP function at height h to be a polynomial of 2^(h - lb) coefficients c in the FFT basis.

Take the sibling to be its value at the conjugate point.

Then the leaf folds to g_0 + beta g_1 at the point round H - h reads, sigma_r x_r. -/
theorem firstLayer_honest (hV : CircleGenValid G) (h2 : (2 : K) ≠ 0) {lb H h : ℕ} {i : ℕ} (hi : i < 2 ^ H)
    (hlb : lb + 2 ≤ h) (hhH : h ≤ H) (hG : H + 1 ≤ G.adicity) (c : ℕ → K) (β ro lam sib : K)
    (hro : ro - lam * vn (h - lb)
      (twinPoint (genPt G (h + 1)) (genPt G (h - 1)) (cfft_permute_index (i / 2 ^ (H - h)) h)) =
      fftEval (h - lb) c
        (twinPoint (genPt G (h + 1)) (genPt G (h - 1)) (cfft_permute_index (i / 2 ^ (H - h)) h)))
    (hsib : sib = fftEval (h - lb) c
      (-twinPoint (genPt G (h + 1)) (genPt G (h - 1)) (cfft_permute_index (i / 2 ^ (H - h)) h))) :
    ∃ y vals, firstLayerLeaf G lb H i (((h, ro), sib), lam) = some (h, y, vals, (2, 2 ^ (h - 1))) ∧
      fold_row_with_inv_twiddle y⁻¹ β vals =
        some (xEval (h - lb - 1) (foldCoeffs c β) (sgn (i / 2) (H - h) * Xq G (H - 1) (i / 2) (H - h))) := by
  set p := twinPoint (genPt G (h + 1)) (genPt G (h - 1)) (cfft_permute_index (i / 2 ^ (H - h)) h)
  have hpt := standard_nth_point hV (h := h) (by omega) (by omega) (cfft_permute_index (i / 2 ^ (H - h)) h)
  rw [standard_eq hV _ (by omega), Option.bind_some] at hpt
  have hy : p.y ≠ 0 := twinPoint_standard_y_ne_zero hV h2 (by omega) (by omega) _
  obtain ⟨m, hm⟩ : ∃ m, h - lb = m + 1 := ⟨h - lb - 1, by omega⟩
  unfold firstLayerLeaf
  simp only [show h ≠ 0 by omega, show ¬ h < lb by omega, show ¬ H < h by omega, ↓reduceIte,
    standard_eq hV _ (by omega : h + 1 ≤ G.adicity), Option.bind_eq_bind, Option.bind_some]
  erw [hpt]
  simp only [Option.bind_some, v_n_ofC, show 1 ≤ h - lb by omega, ↓reduceIte]
  refine ⟨_, _, rfl, ?_⟩
  have hfold := firstLayer_fold h2 hy ((i / 2 ^ (H - h)) % 2) m c β
  rw [← firstLayer_point_x hV (by omega) hhH hG hi, show h - lb - 1 = m by omega]
  rw [hm] at hro hsib
  convert hfold using 3 <;> (try split_ifs) <;> simp [ofC, hm, hro, hsib, p]

/-! ## Completeness of the verifier -/

open p3_circle.pcs.mirror p3_commit.pcs.univariate.mirror p3_circle.domain.mirror in
/-- Completeness of the PCS verifier, from honest inputs to circle FRI.

Take claims whose checks before the transcript pass, and a transcript that accepts the proof's witnesses.

Take input checks that return, for every query, the honest inputs at the points the query reads.

Take honest commit-phase siblings, the folded constant as the final value, and a commit-phase scheme that accepts the honest codewords.

Then the verifier accepts. -/
theorem verify_complete (hV : CircleGenValid G) (h2 : (2 : K) ≠ 0) {S : Type} (immcs fmmcs : MmcsOps K)
    (tx : CircleVerifierTx K fmmcs.Commitment S) (params : FriParameters)
    (rounds : List (Claim K immcs.Commitment))
    (proof : CirclePcsProof K fmmcs.Commitment immcs.MultiProof fmmcs.MultiProof) (s : S) {H : ℕ}
    (hmax : (claimHeights params.log_blowup rounds).max? = some H) (hlb : params.log_blowup + 1 ≤ H)
    (had : H < G.adicity) {la : List ℕ}
    (hshape : validate_proof_shape (ME := fmmcs.Error) (IE := InputError immcs.Error fmmcs.Error) params
      proof.fri_proof (H - (params.log_blowup + 1)) = pure la)
    (hbp : ¬ (params.batch_proof_of_work_bits = 0 ∧ proof.batch_pow_witness ≠ 0))
    {r : Replayed K} (hreplay : replay_transcript (ME := fmmcs.Error) (IE := InputError immcs.Error fmmcs.Error)
      tx rounds proof s = pure r)
    (E : ℕ → ℕ → K) (P : ℕ → Prop) [DecidablePred P] (hE : ∀ r, ¬ P r → E r = fun _ => 0)
    (hβ : r.betas.length = H - (params.log_blowup + 1))
    (hopen : open_inputs G immcs fmmcs params.log_blowup H rounds proof.first_layer_commitment proof.lambdas
      r.bivariate_beta ((List.range (((rounds.flatMap fun c => c.matrices.flatMap fun m =>
        m.points.map (·.values.length)).max?).getD 0)).map (r.alpha ^ ·))
      (rounds.map fun c => c.matrices.map fun m => (r.alpha ^ claimedWidth m, (r.alpha ^ claimedWidth m) ^ 2))
      r.indices proof.fri_proof.input_openings =
        pure (r.indices.map fun i => rollsFrom G E P (H - 1) (H - (params.log_blowup + 1)) (i / 2) 0))
    (hsv : ∀ k < H - (params.log_blowup + 1), ∀ (q i : ℕ), r.indices[q]? = some i →
      ((proof.fri_proof.commit_phase_openings.map (·.sibling_values)).getD k [])[q]? =
        some [xEval (H - (params.log_blowup + 1) - k) (layer E (r.betas.getD · 0) k)
          (-(sgn (i / 2) k * Xq G (H - 1) (i / 2) k))])
    (hfinal : proof.fri_proof.final_poly = preLayer E (r.betas.getD · 0) (H - (params.log_blowup + 1)) 0)
    (hmmcs : ∀ k < H - (params.log_blowup + 1), ∀ (c : fmmcs.Commitment)
      (o : CommitPhaseMultiStep K fmmcs.MultiProof),
      proof.fri_proof.commit_phase_commits[k]? = some c → proof.fri_proof.commit_phase_openings[k]? = some o →
      ∀ groups : List ℕ, fmmcs.verify_multi_batch c [(2, 2 ^ (H - 1 - (k + 1)))] groups
        (groups.map fun j => [honestWord G (H - 1) (H - (params.log_blowup + 1)) E (r.betas.getD · 0) k j])
          o.opening_proof = .ok ()) :
    verify G immcs fmmcs tx params rounds proof s = pure () := by
  obtain ⟨rfl, hsh⟩ := validate_proof_shape_spec hshape
  have hL : H - (params.log_blowup + 1) + params.log_blowup = H - 1 := by omega
  unfold verify
  rw [show (rounds.flatMap fun c => c.matrices.map fun m => m.domain.log_n + params.log_blowup) =
    claimHeights params.log_blowup rounds from rfl]
  dsimp only
  rw [hmax]
  simp only [pure_bind, show ¬ H < params.log_blowup + 1 by omega, show ¬ G.adicity ≤ H - 1 + 1 by omega,
    ↓reduceIte, hshape, hbp, hreplay]
  have := verify_queries_complete hV h2 fmmcs params proof.fri_proof r.betas r.indices
    (R := H - (params.log_blowup + 1)) _ E P hE hsh.blowup (by omega) hβ hsh.openings
    (by rw [hL]; exact hopen) (by rw [hL]; exact hsv) hfinal (by rw [hL]; exact hmmcs)
  exact this

end Plonky3Lean.Proofs.Circle
