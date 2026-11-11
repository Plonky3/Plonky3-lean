module

public import P3MultiStark.Mirror.FractionalGkr
public import Plonky3Lean.Proofs.MultiStark.FractionTree
public import Plonky3Lean.Proofs.Sumcheck.GenericDegree
public import Plonky3Lean.Proofs.MultilinearUtil.PointForms

@[expose] public section

/-!
# The fractional-GKR verifier

The verifier first measures the proof against the variable count n:

- n is at least one
- there are n layers
- layer i carries i round polynomials
- the root denominator is nonzero.

It then panics exactly when two of the interpolation nodes 0, 1, 2, 3 coincide.

Otherwise it replays every layer and accepts exactly when each layer's final check holds:

```text
    replayed claim  =  eq(rho, r) * (d1 n0 + d0 n1 + lambda d0 d1)
```

The next claim is the line through the two children at the branch challenge b.

The next point is b followed by the round challenges.

# Soundness

Take a leaf table of 2^n fractions, and an accepting run whose output claim is its true extension.

Walk the layers from the leaves to the root.

A false claim at layer i reaches layer i + 1 only through one of three events:

- lambda is the one root of N + lambda D - (N* + lambda D*)
- the round challenges are among the at most 3 i |K|^(i - 1) vectors the sum-check lets through
- b is the one root of the line through the claimed children minus the true line.

Without these events the root claim (0, d) is true.

Then every leaf denominator is nonzero and the leaves sum to zero.
-/

namespace Plonky3Lean.Proofs.MultiStark

open p3_multi_stark.fractional_gkr.mirror p3_sumcheck.generic_degree.mirror
  p3_multilinear_util.point.mirror Plonky3Lean.Proofs.Sumcheck Plonky3Lean.Proofs.MultilinearUtil
  Plonky3Lean.Spec.MultiStark Plonky3Lean.Spec.MultilinearUtil Plonky3Lean.Spec.Sumcheck Finset

set_option linter.unusedSectionVars false

noncomputable section

variable {EF S : Type _} [Field EF] [DecidableEq EF] (node : ℕ → EF) (T : VerifierTranscript EF S)

/-! ## Replaying the layers -/

/-- The challenges of a layer's rounds, and the transcript after them. -/
def roundChallenges (t : S) : List (Fin 3 → EF) → List EF × S
  | [] => ([], t)
  | rp :: rps =>
    ((T.round t (List.ofFn rp)).1 :: (roundChallenges (T.round t (List.ofFn rp)).2 rps).1,
      (roundChallenges (T.round t (List.ofFn rp)).2 rps).2)

@[simp] theorem length_roundChallenges (t : S) :
    ∀ rps : List (Fin 3 → EF), (roundChallenges T t rps).1.length = rps.length
  | [] => rfl
  | _ :: rps => by simp [roundChallenges, length_roundChallenges _ rps]

/-- One layer as the verifier sees it: the claim it inherits, the messages, and the challenges. -/
structure LayerRec (EF : Type _) where
  point : List EF
  num : EF
  den : EF
  lam : EF
  msgs : List (Fin 3 → EF)
  rs : List EF
  claims : SplitFraction EF
  branch : EF

/-- The claim the rounds reduce the batched claim to. -/
def LayerRec.running (L : LayerRec EF) : EF :=
  finalClaim (decGen node 3) (L.num + L.lam * L.den) L.msgs L.rs

/-- The layer's final check. -/
def LayerRec.passes (L : LayerRec EF) : Prop :=
  L.running node = eq L.point L.rs * L.claims.gate L.lam

instance (L : LayerRec EF) : Decidable (L.passes node) := by unfold LayerRec.passes; infer_instance

/-- The claimed numerator the layer passes down. -/
def LayerRec.nextNum (L : LayerRec EF) : EF := L.claims.n0 + L.branch * (L.claims.n1 - L.claims.n0)

/-- The claimed denominator the layer passes down. -/
def LayerRec.nextDen (L : LayerRec EF) : EF := L.claims.d0 + L.branch * (L.claims.d1 - L.claims.d0)

/-- The point the layer passes down. -/
def LayerRec.nextPoint (L : LayerRec EF) : List EF := L.branch :: L.rs

/-- The record of one layer, replayed from the claim it inherits and the transcript state. -/
def layerRec (pt : List EF) (num den : EF) (t : S) (l : FractionGkrLayerProof EF) : LayerRec EF :=
  ⟨pt, num, den, (T.begin_layer t).1, l.round_polys,
    (roundChallenges T (T.begin_layer t).2 l.round_polys).1, l.claims,
    (T.end_layer (roundChallenges T (T.begin_layer t).2 l.round_polys).2 l.claims).1⟩

/-- The transcript state after one layer. -/
def layerEnd (t : S) (l : FractionGkrLayerProof EF) : S :=
  (T.end_layer (roundChallenges T (T.begin_layer t).2 l.round_polys).2 l.claims).2

/-- The replayed layers, and the point, claim and transcript after the last one. -/
structure Replay (EF S : Type _) where
  records : List (LayerRec EF)
  point : List EF
  num : EF
  den : EF
  transcript : S

/-- Replay the layers from a point, a claim and a transcript state. -/
def replay (pt : List EF) (num den : EF) (t : S) : List (FractionGkrLayerProof EF) → Replay EF S
  | [] => ⟨[], pt, num, den, t⟩
  | l :: ls =>
    let L := layerRec T pt num den t l
    let R := replay L.nextPoint L.nextNum L.nextDen (layerEnd T t l) ls
    ⟨L :: R.records, R.point, R.num, R.den, R.transcript⟩

/-- The position of the first layer whose check fails. -/
def firstFail (Ls : List (LayerRec EF)) : Option ℕ := Ls.findIdx? fun L => !decide (L.passes node)

section Rounds

variable {weights : Fin 4 → EF} (hw : RoundPolyInterpolator.new node 3 = some weights)
include hw

theorem foldlM_roundStep : ∀ (rps : List (Fin 3 → EF)) (c : EF) (pre : List EF) (t : S),
    rps.foldlM (roundStep node T weights) (c, pre, t) =
      some (finalClaim (decGen node 3) c rps (roundChallenges T t rps).1,
        pre ++ (roundChallenges T t rps).1, (roundChallenges T t rps).2)
  | [], c, pre, t => by simp [roundChallenges, finalClaim]
  | rp :: rps, c, pre, t => by
    rw [List.foldlM_cons]
    have hev := RoundPolyInterpolator.eval_eq node (by norm_num) hw rp c (T.round t (List.ofFn rp)).1
    simp only [roundStep, hev, Option.bind_eq_bind, Option.bind_some, pure]
    rw [foldlM_roundStep rps]
    simp [roundChallenges, finalClaim]

/-- One layer of the verifier is its record: the inconsistency is noted when the check fails. -/
theorem verify_layer_eq (st : VerifyState EF S) (k : ℕ) (l : FractionGkrLayerProof EF)
    (hlen : st.point.length = l.round_polys.length) :
    verify_layer node T weights st k l =
      let L := layerRec T st.point st.numerator st.denominator st.transcript l
      some ⟨L.nextPoint, L.nextNum, L.nextDen,
        if L.passes node then st.inconsistent else st.inconsistent.or (some k),
        layerEnd T st.transcript l⟩ := by
  have hl : st.point.length =
      (roundChallenges T (T.begin_layer st.transcript).2 l.round_polys).1.length := by simp [hlen]
  simp only [verify_layer, foldlM_roundStep node T hw, List.nil_append, Option.bind_eq_bind,
    Option.bind_some, eval_eq_eq hl, Algebra.algebraMap_self]
  simp [layerRec, layerEnd, LayerRec.passes, LayerRec.running, LayerRec.nextNum, LayerRec.nextDen,
    LayerRec.nextPoint]

/-- The verifier's loop is the replay.

The first failing layer, counted from the start index, becomes the inconsistency. -/
theorem foldlM_verify_layer : ∀ (ls : List (FractionGkrLayerProof EF)) (j : ℕ) (st : VerifyState EF S),
    st.point.length = j → (∀ i (h : i < ls.length), ls[i].round_polys.length = j + i) →
    (ls.zipIdx j).foldlM (fun st p => verify_layer node T weights st p.2 p.1) st =
      let R := replay T st.point st.numerator st.denominator st.transcript ls
      some ⟨R.point, R.num, R.den, st.inconsistent.or ((firstFail node R.records).map (j + ·)),
        R.transcript⟩
  | [], j, st, _, _ => by simp [replay, firstFail]
  | l :: ls, j, st, hp, hr => by
    have hr0 : l.round_polys.length = j := by
      have := hr 0 (by simp); rw [List.getElem_cons_zero] at this; omega
    have hrs : ∀ i (h : i < ls.length), ls[i].round_polys.length = j + 1 + i := fun i h => by
      have := hr (i + 1) (by simpa using h)
      rw [List.getElem_cons_succ] at this; omega
    rw [List.zipIdx_cons, List.foldlM_cons, verify_layer_eq node T hw st j l (by omega)]
    simp only [Option.bind_eq_bind, Option.bind_some]
    rw [foldlM_verify_layer ls (j + 1) _ (by simp [LayerRec.nextPoint, layerRec]; omega) hrs]
    simp only [replay, firstFail, List.findIdx?_cons]
    by_cases hpass : (layerRec T st.point st.numerator st.denominator st.transcript l).passes node
    · simp [hpass, Option.map_map, Function.comp_def, Nat.add_assoc, Nat.add_comm 1]
    · cases st.inconsistent <;> simp [hpass]

end Rounds

/-- The round-count check passes exactly when layer i carries i round polynomials. -/
theorem firstBadRound_eq_none (ls : List (FractionGkrLayerProof EF)) :
    firstBadRound ls = none ↔ ∀ i (h : i < ls.length), ls[i].round_polys.length = i := by
  suffices ∀ j, (ls.zipIdx j).find? (fun p => p.1.round_polys.length != p.2) = none ↔
      ∀ i (h : i < ls.length), ls[i].round_polys.length = j + i by
    simpa [firstBadRound] using this 0
  induction ls with
  | nil => simp
  | cons l ls ih =>
    intro j
    rw [List.zipIdx_cons, List.find?_cons]
    by_cases hl : l.round_polys.length = j
    · simp only [hl, bne_self_eq_false, ih (j + 1)]
      refine ⟨fun h i hi => ?_, fun h i hi => ?_⟩
      · rcases i with _ | i
        · simpa using hl
        · rw [List.getElem_cons_succ]; have := h i (by simpa using hi); omega
      · have := h (i + 1) (by simpa using hi)
        rw [List.getElem_cons_succ] at this; omega
    · have hb : (l.round_polys.length != j) = true := by simpa using hl
      simp only [hb, reduceCtorEq, false_iff, not_forall]
      exact ⟨0, by simp, by simpa using hl⟩

/-- Building the interpolator panics exactly when two of the nodes 0, 1, 2, 3 coincide. -/
theorem interpolator_new_eq_none :
    RoundPolyInterpolator.new node 3 = none ↔ ¬ Function.Injective fun i : Fin 4 => node i := by
  rw [RoundPolyInterpolator.new, Proofs.Matrix.Interp.barycentric_weights_eq]
  split_ifs <;> simp_all

/-- **The verifier.**

It checks, in order:

- the variable count, the layer count, then each layer's round count
- the root denominator.

It then panics exactly when two of the nodes 0, 1, 2, 3 coincide.

Otherwise it replays every layer from the claim (0, d) at the empty point.

It rejects at the first layer whose check fails, and returns the last claim otherwise. -/
theorem verify_fractional_gkr_eq (proof : FractionGkrProof EF) (n : ℕ) :
    verify_fractional_gkr node T proof n =
      if n < 1 then some (.error .InvalidVariableCount)
      else if proof.layers.length ≠ n then some (.error (.InvalidLayerCount n proof.layers.length))
      else match firstBadRound proof.layers with
        | some (i, a) => some (.error (.InvalidRoundCount i i a))
        | none =>
          if proof.root_denominator = 0 then some (.error .ZeroRootDenominator)
          else if ¬ Function.Injective (fun i : Fin 4 => node i) then none
          else
            let R := replay T [] 0 proof.root_denominator
              (T.init n proof.root_denominator) proof.layers
            some (match firstFail node R.records with
              | some k => .error (.LayerConsistency k)
              | none => .ok ⟨R.point, R.num, R.den⟩) := by
  unfold verify_fractional_gkr
  by_cases hn : n < 1
  · simp [hn]
  by_cases hl : proof.layers.length ≠ n
  · simp [hn, hl]
  simp only [hn, hl, ↓reduceIte] at hl ⊢
  rcases hb : firstBadRound proof.layers with _ | ⟨i, a⟩
  swap
  · simp
  have hr := (firstBadRound_eq_none proof.layers).mp hb
  by_cases hd : proof.root_denominator = 0
  · simp [hd]
  rcases hw : RoundPolyInterpolator.new node 3 with _ | w
  · simp [hd, (interpolator_new_eq_none node).mp hw]
  have hinj : Function.Injective fun i : Fin 4 => node i := by
    by_contra h; rw [← interpolator_new_eq_none node, hw] at h; exact absurd h (by simp)
  simp only [hd, hinj, ↓reduceIte, not_true_eq_false, Option.bind_some, pure, bind]
  rw [foldlM_verify_layer node T hw proof.layers 0 _ rfl fun i h => by simpa using hr i h]
  simp only [Option.bind_some, Option.none_or]
  rcases firstFail node _ with _ | k <;> simp


/-! ## Soundness -/

section Sound

variable (t : ℕ → EF × EF) (n : ℕ)

/-- The true numerator of level k at a point. -/
def trueNum (k : ℕ) (ρ : List EF) : EF := rowExt (fun x => (fracLevel t n k x).1) ρ

/-- The true denominator of level k at a point. -/
def trueDen (k : ℕ) (ρ : List EF) : EF := rowExt (fun x => (fracLevel t n k x).2) ρ

/-- The true children of level k at a point: the two halves of level k + 1 there. -/
def trueChildren (k : ℕ) (r : List EF) : SplitFraction EF :=
  ⟨rowExt (fun x => (fracLevel t n (k + 1) x).1) r, rowExt (fun x => (fracLevel t n (k + 1) x).2) r,
    rowExt (fun x => (fracLevel t n (k + 1) (2 ^ k + x)).1) r,
    rowExt (fun x => (fracLevel t n (k + 1) (2 ^ k + x)).2) r⟩

/-- Lambda maps a false claim onto the true one. -/
def LayerRec.lamBad (k : ℕ) (L : LayerRec EF) : Prop :=
  (L.num ≠ trueNum t n k L.point ∨ L.den ≠ trueDen t n k L.point) ∧
    L.num + L.lam * L.den = trueNum t n k L.point + L.lam * trueDen t n k L.point

/-- The rounds carry a false batched claim to the true value at their challenges. -/
def LayerRec.roundBad (k : ℕ) (L : LayerRec EF) : Prop :=
  L.num + L.lam * L.den ≠ trueNum t n k L.point + L.lam * trueDen t n k L.point ∧
    L.running node = eq L.point L.rs * (trueChildren t n k L.rs).gate L.lam

/-- The branch carries false children to the true claim of the next level. -/
def LayerRec.branchBad (k : ℕ) (L : LayerRec EF) : Prop :=
  L.claims ≠ trueChildren t n k L.rs ∧
    L.nextNum = trueNum t n (k + 1) L.nextPoint ∧ L.nextDen = trueDen t n (k + 1) L.nextPoint

/-- One of the three events through which a false claim survives a layer. -/
def LayerRec.bad (k : ℕ) (L : LayerRec EF) : Prop :=
  L.lamBad t n k ∨ L.roundBad node t n k ∨ L.branchBad t n k

/-- **One layer.**

Take a passing layer that passes down the true claim of level k + 1.

Then its own claim is the true claim of level k, unless one of the three events happened. -/
theorem layer_sound {k : ℕ} (L : LayerRec EF) (hpass : L.passes node)
    (hnext : L.nextNum = trueNum t n (k + 1) L.nextPoint ∧
      L.nextDen = trueDen t n (k + 1) L.nextPoint) :
    (L.num = trueNum t n k L.point ∧ L.den = trueDen t n k L.point) ∨ L.bad node t n k := by
  by_cases hin : L.num = trueNum t n k L.point ∧ L.den = trueDen t n k L.point
  · exact Or.inl hin
  refine Or.inr ?_
  by_cases hlam : L.num + L.lam * L.den = trueNum t n k L.point + L.lam * trueDen t n k L.point
  · exact Or.inl ⟨not_and_or.mp hin, hlam⟩
  by_cases hround : L.running node = eq L.point L.rs * (trueChildren t n k L.rs).gate L.lam
  · exact Or.inr (Or.inl ⟨hlam, hround⟩)
  refine Or.inr (Or.inr ⟨fun hc => hround ?_, hnext⟩)
  rw [hpass, hc]

/-- Lambda is bad for at most one value. -/
theorem lam_bad_card [Fintype EF] {N D N' D' : EF} (h : N ≠ N' ∨ D ≠ D') :
    #{lam | N + lam * D = N' + lam * D'} ≤ 1 := by
  refine card_le_one.mpr fun a ha b hb => ?_
  simp only [mem_filter, mem_univ, true_and] at ha hb
  by_cases hD : D = D'
  · subst hD; exact absurd (add_right_cancel ha) (h.resolve_right (not_not.mpr rfl))
  have : (a - b) * (D - D') = 0 := by linear_combination ha - hb
  exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_right (sub_ne_zero.mpr hD))

/-- Two different lines through a point agree at most once. -/
theorem line_bad_card [Fintype EF] {a0 a1 c0 c1 : EF} (h : a0 ≠ c0 ∨ a1 ≠ c1) :
    #{b | a0 + b * (a1 - a0) = c0 + b * (c1 - c0)} ≤ 1 := by
  refine card_le_one.mpr fun x hx y hy => ?_
  simp only [mem_filter, mem_univ, true_and] at hx hy
  by_contra hxy
  have hc : (a1 - a0) - (c1 - c0) = 0 := by
    have : (x - y) * ((a1 - a0) - (c1 - c0)) = 0 := by linear_combination hx - hy
    exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hxy)
  have h0 : a0 = c0 := by linear_combination hx - x * hc
  exact h.elim (· h0) fun h1 => h1 (by linear_combination hc + h0)

/-- The branch is bad for at most one value. -/
theorem branch_bad_card [Fintype EF] {k : ℕ} {rs : List EF} (hrs : rs.length = k)
    {c : SplitFraction EF} (hc : c ≠ trueChildren t n k rs) :
    #{b | c.n0 + b * (c.n1 - c.n0) = trueNum t n (k + 1) (b :: rs) ∧
      c.d0 + b * (c.d1 - c.d0) = trueDen t n (k + 1) (b :: rs)} ≤ 1 := by
  simp only [trueNum, trueDen, ext_cons_line, hrs]
  have hne : (c.n0 ≠ (trueChildren t n k rs).n0 ∨ c.n1 ≠ (trueChildren t n k rs).n1) ∨
      (c.d0 ≠ (trueChildren t n k rs).d0 ∨ c.d1 ≠ (trueChildren t n k rs).d1) := by
    by_contra h
    push Not at h
    exact hc (by cases c; simp_all [trueChildren])
  rcases hne with hn | hd
  · refine (card_le_card fun b hb => ?_).trans (line_bad_card hn)
    simp only [mem_filter, mem_univ, true_and] at hb ⊢
    rw [hb.1]; simp only [trueChildren]
  · refine (card_le_card fun b hb => ?_).trans (line_bad_card hd)
    simp only [mem_filter, mem_univ, true_and] at hb ⊢
    rw [hb.2]; simp only [trueChildren]

/-- The layer polynomial of level k at rho, over the halves of level k + 1. -/
def levelPoly (k : ℕ) (ρ : List EF) (lam : EF) : MvPolynomial (Fin k) EF :=
  layerPoly k ρ lam (fun x => (fracLevel t n (k + 1) x).1) (fun x => (fracLevel t n (k + 1) x).2)
    (fun x => (fracLevel t n (k + 1) (2 ^ k + x)).1) (fun x => (fracLevel t n (k + 1) (2 ^ k + x)).2)

theorem eval_levelPoly {k : ℕ} {ρ : List EF} (hρ : ρ.length = k) (lam : EF) (r : Fin k → EF) :
    MvPolynomial.eval r (levelPoly t n k ρ lam) =
      eq ρ (List.ofFn r) * (trueChildren t n k (List.ofFn r)).gate lam := by
  rw [levelPoly, eval_layerPoly hρ]; rfl

theorem cubeSum_levelPoly {k : ℕ} (hk : k < n) {ρ : List EF} (hρ : ρ.length = k) (lam : EF) :
    cubeSum (levelPoly t n k ρ lam) = trueNum t n k ρ + lam * trueDen t n k ρ := by
  rw [levelPoly, cubeSum_layerPoly hρ, trueNum, trueDen, batch_level t hk]

open scoped Classical in
/-- The rounds are bad for few challenge vectors.

Take a false batched claim and any causal strategy for the round polynomials.

At most 3 k |K|^(k - 1) of the |K|^k challenge vectors carry it to the true value. -/
theorem round_bad_card [Fintype EF] (h0 : node 0 = 0) (h1 : node 1 = 1)
    (hinj : Function.Injective fun i : Fin 4 => node i) {k : ℕ} (hk : k < n) {ρ : List EF}
    (hρ : ρ.length = k) {num den lam : EF}
    (hb : num + lam * den ≠ trueNum t n k ρ + lam * trueDen t n k ρ)
    (M : Fin k → (Fin k → EF) → Fin 3 → EF) (hM : Causal M) :
    #{r | finalClaim (decGen node 3) (num + lam * den) (List.ofFn fun i => M i r) (List.ofFn r) =
      eq ρ (List.ofFn r) * (trueChildren t n k (List.ofFn r)).gate lam} * Fintype.card EF ≤
        k * 3 * Fintype.card EF ^ k := by
  have h := soundness_decoded (decGen node 3) (natDegree_decGen node hinj)
    (decGen_sum node hinj (by norm_num) h0 h1) (levelPoly t n k ρ lam)
    (individualDegreeLE_layerPoly _ _ _ _ _ _ _) (num + lam * den)
    (by rwa [cubeSum_levelPoly t n hk hρ]) M hM
  simpa only [eval_levelPoly t n hρ, eq_comm] using h

/-- **Completeness of one layer.**

From the true batched claim, the honest round polynomials replay to the check's right side.

That right side reads the true children, whose line at the branch is the true claim below. -/
theorem layer_complete (h0 : node 0 = 0) (h1 : node 1 = 1)
    (hinj : Function.Injective fun i : Fin 4 => node i) {k : ℕ} (hk : k < n) {ρ : List EF}
    (hρ : ρ.length = k) (lam : EF) (r : Fin k → EF) :
    finalClaim (decGen node 3) (trueNum t n k ρ + lam * trueDen t n k ρ)
        (List.ofFn fun i => encGen node (honestProver (levelPoly t n k ρ lam) i r)) (List.ofFn r) =
      eq ρ (List.ofFn r) * (trueChildren t n k (List.ofFn r)).gate lam := by
  rw [← cubeSum_levelPoly t n hk hρ, ← eval_levelPoly t n hρ]
  exact (completeness_decoded (decGen node 3) (encGen node)
    (fun _ _ hp hc => decGen_encGen node hinj (by norm_num) h0 h1 hp hc) _
    (individualDegreeLE_layerPoly _ _ _ _ _ _ _) r).symm

/-- The line through the true children at b is the true claim of the level below at (b, r). -/
theorem trueChildren_line {k : ℕ} {rs : List EF} (hrs : rs.length = k) (b : EF) :
    (trueChildren t n k rs).n0 + b * ((trueChildren t n k rs).n1 - (trueChildren t n k rs).n0) =
        trueNum t n (k + 1) (b :: rs) ∧
      (trueChildren t n k rs).d0 + b * ((trueChildren t n k rs).d1 - (trueChildren t n k rs).d0) =
        trueDen t n (k + 1) (b :: rs) := by
  simp [trueChildren, trueNum, trueDen, ext_cons_line, hrs]

/-- **Every layer.**

Replay passing layers from level j down to level n, ending at the true claim of the leaves.

Then the starting claim is true, unless some layer had one of its three events. -/
theorem replay_sound : ∀ (ls : List (FractionGkrLayerProof EF)) (j : ℕ) (pt : List EF)
    (num den : EF) (tr : S), (∀ i (h : i < ls.length), ls[i].round_polys.length = j + i) →
    j + ls.length = n → (∀ L ∈ (replay T pt num den tr ls).records, L.passes node) →
    (replay T pt num den tr ls).num = trueNum t n n (replay T pt num den tr ls).point →
    (replay T pt num den tr ls).den = trueDen t n n (replay T pt num den tr ls).point →
    (num = trueNum t n j pt ∧ den = trueDen t n j pt) ∨
      ∃ i, ∃ h : i < (replay T pt num den tr ls).records.length,
        ((replay T pt num den tr ls).records[i]).bad node t n (j + i)
  | [], j, pt, num, den, tr, _, hn, _, hnum, hden => by
    simp only [List.length_nil, Nat.add_zero] at hn
    subst hn
    exact Or.inl ⟨hnum, hden⟩
  | l :: ls, j, pt, num, den, tr, hr, hn, hpass, hnum, hden => by
    have hrs : ∀ i (h : i < ls.length), ls[i].round_polys.length = j + 1 + i := fun i h => by
      have := hr (i + 1) (by simpa using h)
      rw [List.getElem_cons_succ] at this; omega
    set L := layerRec T pt num den tr l
    have ih := replay_sound ls (j + 1) L.nextPoint L.nextNum L.nextDen (layerEnd T tr l) hrs
      (by simp at hn; omega) (fun L' h => hpass L' (by simp only [replay, List.mem_cons]; exact Or.inr h)) hnum hden
    rcases ih with htrue | ⟨i, hi, hbad⟩
    · rcases layer_sound node t n (k := j) L (hpass L (by simp [replay, L])) htrue with h | h
      · exact Or.inl h
      · exact Or.inr ⟨0, by simp [replay], by simpa [replay, L] using h⟩
    · exact Or.inr ⟨i + 1, by simpa [replay] using hi, by
        simpa [replay, L, Nat.add_assoc, Nat.add_comm 1] using hbad⟩

/-- **Soundness of the fractional-GKR verifier.**

Take an accepting run whose output claim is the true extension of the leaves at the output point.

Then every leaf denominator is nonzero and the leaves sum to zero.

Or some layer i had one of its three events. -/
theorem verify_sound {proof : FractionGkrProof EF} {out : FractionGkrOutput EF}
    (hacc : verify_fractional_gkr node T proof n = some (.ok out))
    (hnum : out.numerator = rowExt (fun x => (t x).1) out.point)
    (hden : out.denominator = rowExt (fun x => (t x).2) out.point) :
    ((∀ x < 2 ^ n, (t x).2 ≠ 0) ∧ ∑ x ∈ range (2 ^ n), (t x).1 / (t x).2 = 0) ∨
      ∃ i, ∃ h : i < (replay T [] 0 proof.root_denominator
          (T.init n proof.root_denominator) proof.layers).records.length,
        ((replay T [] 0 proof.root_denominator
          (T.init n proof.root_denominator) proof.layers).records[i]).bad node t n i := by
  rw [verify_fractional_gkr_eq] at hacc
  by_cases hn : n < 1
  · simp [hn] at hacc
  by_cases hl : proof.layers.length ≠ n
  · simp [hn, hl] at hacc
  simp only [hn, hl, ↓reduceIte] at hacc
  rcases hb : firstBadRound proof.layers with _ | ⟨i, a⟩
  swap
  · simp [hb] at hacc
  simp only [hb] at hacc
  by_cases hd : proof.root_denominator = 0
  · simp [hd] at hacc
  by_cases hinj : Function.Injective fun i : Fin 4 => node i
  swap
  · simp [hd, hinj] at hacc
  simp only [hd, hinj, ↓reduceIte, not_true_eq_false] at hacc
  set R := replay T [] 0 proof.root_denominator (T.init n proof.root_denominator) proof.layers
  rcases hf : firstFail node R.records with _ | k
  swap
  · simp [hf] at hacc
  simp only [hf, Option.some.injEq, Except.ok.injEq] at hacc
  subst hacc
  have hpass : ∀ L ∈ R.records, L.passes node := fun L hL => by
    have := List.findIdx?_eq_none_iff.mp hf L hL
    simpa using this
  have hfin := fracLevel_top t (le_refl n)
  rcases replay_sound node T t n proof.layers 0 [] 0 proof.root_denominator
      (T.init n proof.root_denominator)
      (fun i h => by simpa using (firstBadRound_eq_none proof.layers).mp hb i h)
      (by simp at hl; omega) hpass (by simpa [trueNum, hfin] using hnum)
      (by simpa [trueDen, hfin] using hden) with ⟨h0, h1⟩ | h
  · refine Or.inl ((root_iff t n).mp ⟨?_, ?_⟩)
    · simpa [trueNum, rowExt, vertex] using h0.symm
    · have h1' : (fracLevel t n 0 0).2 = proof.root_denominator := by
        simpa [trueDen, rowExt, vertex] using h1.symm
      rw [h1']; exact hd
  · exact Or.inr (by simpa using h)

end Sound

end

end Plonky3Lean.Proofs.MultiStark
