module

public import Plonky3Lean.Proofs.Sumcheck.Quadratic

@[expose] public section

/-!
# The quadratic sumcheck verifier, as transcribed

What the round verification absorbs, when it rejects, and what it returns.

The sponge is its history, so each challenge is a function of everything absorbed before it.
-/

namespace Plonky3Lean.Proofs.Sumcheck

open p3_sumcheck.mirror

variable {F EF : Type _} [Field EF]

/-- The steps of round i up to its challenge: the pair, then the witness when grinding. -/
def roundSteps (evals : List (EF × EF)) (wits : List F) (pow_bits i : ℕ) : List (Step F EF) :=
  .message [(evals.getD i (0, 0)).1, (evals.getD i (0, 0)).2] ::
    if 0 < pow_bits then (wits[i]?.map (Step.pow pow_bits)).toList else []

/-- The history at the start of round i. -/
def before (h : List (Step F EF)) (evals : List (EF × EF)) (wits : List F) (pow_bits : ℕ) :
    ℕ → List (Step F EF)
  | 0 => h
  | i + 1 => before h evals wits pow_bits i ++ roundSteps evals wits pow_bits i ++ [.challenge]

/-- Whether the witness of round i passes the grinding check, at the history it is checked at. -/
def grindOk (S : Sponge F EF) (h : List (Step F EF)) (evals : List (EF × EF)) (wits : List F)
    (pow_bits i : ℕ) : Bool :=
  if 0 < pow_bits then
    match wits[i]? with
    | some w => S.grind (before h evals wits pow_bits i ++
        [.message [(evals.getD i (0, 0)).1, (evals.getD i (0, 0)).2]]) pow_bits w
    | none => false
  else true

/-- The challenge of round i: the sponge sampled after the steps of round i. -/
def challengeAt (S : Sponge F EF) (h : List (Step F EF)) (evals : List (EF × EF)) (wits : List F)
    (pow_bits i : ℕ) : EF :=
  S.sample (before h evals wits pow_bits i ++ roundSteps evals wits pow_bits i)

/-- The claim after replaying the pairs against the challenges, with the basis's round identity. -/
def replay (basis : Basis) (c : EF) (evals : List (EF × EF)) (rs : List EF) : EF :=
  (evals.zip rs).foldl (fun c (m, r) => basis.reduce_claim m.1 m.2 r c) c

theorem replay_snoc (basis : Basis) (c : EF) {evals : List (EF × EF)} {rs : List EF} {k : ℕ}
    (hk : k < evals.length) (hrs : rs.length = k) (r : EF) :
    replay basis c (evals.take (k + 1)) (rs ++ [r]) =
      basis.reduce_claim (evals.getD k (0, 0)).1 (evals.getD k (0, 0)).2 r
        (replay basis c (evals.take k) rs) := by
  rw [List.take_add_one, List.getElem?_eq_getElem hk, Option.toList_some, replay, replay,
    List.zip_append (by simp [hrs, Nat.min_eq_left hk.le]), List.foldl_append]
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]

theorem foldlM_verifyRound (S : Sponge F EF) (evals : List (EF × EF)) (wits : List F) (h : List (Step F EF))
    (c : EF) (pow_bits : ℕ) (basis : Basis) {N : ℕ} (he : evals.length = N)
    (hw : wits.length = if 0 < pow_bits then N else 0) :
    ∀ k ≤ N, (List.range k).foldlM (verifyRound S evals wits pow_bits basis) ([], c, h) =
      match (List.range k).find? (fun i => !grindOk S h evals wits pow_bits i) with
      | some i => .error (.InvalidPowWitness i pow_bits)
      | none =>
        let rs := (List.range k).map (challengeAt S h evals wits pow_bits)
        .ok (rs, replay basis c (evals.take k) rs, before h evals wits pow_bits k)
  | 0, _ => rfl
  | k + 1, hk => by
    rw [List.range_succ, List.foldlM_append, foldlM_verifyRound S evals wits h c pow_bits basis he hw k
      (by omega), List.find?_append]
    rcases hf : (List.range k).find? (fun i => !grindOk S h evals wits pow_bits i) with _ | i
    swap
    · rfl
    have hkN : k < evals.length := by omega
    simp only [Option.none_or, List.find?_singleton, List.foldlM_cons, List.foldlM_nil]
    have hrs : ((List.range k).map (challengeAt S h evals wits pow_bits)).length = k := by simp
    by_cases hp : 0 < pow_bits
    · obtain ⟨w, hw'⟩ : ∃ w, wits[k]? = some w :=
        ⟨_, List.getElem?_eq_getElem (by simp [hp] at hw; omega)⟩
      by_cases hg : S.grind (before h evals wits pow_bits k ++
          [.message [(evals.getD k (0, 0)).1, (evals.getD k (0, 0)).2]]) pow_bits w = true
      all_goals simp only [List.getD_eq_getElem?_getD] at hg
      · simp [verifyRound, VerifierTranscript.round, bind, Except.bind, pure, Except.pure, hp, hw', hg,
          grindOk, replay_snoc basis c hkN hrs, challengeAt, before, roundSteps]
      · simp [verifyRound, VerifierTranscript.round, bind, Except.bind, hp, hw', hg,
          grindOk, throw, throwThe, MonadExceptOf.throw]
    · simp [verifyRound, VerifierTranscript.round, bind, Except.bind, pure, Except.pure, hp,
        grindOk, replay_snoc basis c hkN hrs, challengeAt, before, roundSteps]

/-- The round verification runs in this order:

- the two count checks
- the first round whose witness fails
- otherwise, the challenges and the replayed claim. -/
theorem verify_rounds_eq (S : Sponge F EF) (evals : List (EF × EF)) (wits : List F)
    (h : List (Step F EF)) (c : EF) (N pow_bits : ℕ) (basis : Basis) :
    verify_rounds S evals wits h c N pow_bits basis =
      if evals.length ≠ N then .error (.RoundCountMismatch N evals.length)
      else if wits.length ≠ (if 0 < pow_bits then N else 0) then
        .error (.PowWitnessCountMismatch (if 0 < pow_bits then N else 0) wits.length)
      else
        let h' := if 0 < N then h ++ [SumcheckShape.seed N pow_bits basis] else h
        match (List.range N).find? (fun i => !grindOk S h' evals wits pow_bits i) with
        | some i => .error (.InvalidPowWitness i pow_bits)
        | none =>
          let rs := (List.range N).map (challengeAt S h' evals wits pow_bits)
          .ok (rs, replay basis c evals rs, before h' evals wits pow_bits N) := by
  unfold verify_rounds
  by_cases he : evals.length = N
  · by_cases hw : wits.length = if 0 < pow_bits then N else 0
    · simp only [he, hw, ne_eq, not_true_eq_false, ↓reduceIte]
      rw [foldlM_verifyRound S evals wits _ c pow_bits basis he hw N le_rfl, ← he, List.take_length]
    · simp only [he, hw, ne_eq, not_true_eq_false, not_false_eq_true, ↓reduceIte]
      rfl
  · simp only [he, ne_eq, not_false_eq_true, ↓reduceIte]
    rfl

/-- The history at the start of round i.

It is the given history, then every earlier round with its challenge. -/
theorem before_eq (h : List (Step F EF)) (evals : List (EF × EF)) (wits : List F) (pow_bits : ℕ) :
    ∀ i, before h evals wits pow_bits i =
      h ++ (List.range i).flatMap fun j => roundSteps evals wits pow_bits j ++ [.challenge]
  | 0 => by simp [before]
  | i + 1 => by simp [before, before_eq h evals wits pow_bits i, List.range_succ]

/-- The verifier never reports a missing witness.

The witness count is checked first. -/
theorem verify_rounds_ne_missing (S : Sponge F EF) (evals : List (EF × EF)) (wits : List F)
    (h : List (Step F EF)) (c : EF) (N pow_bits : ℕ) (basis : Basis) (i b : ℕ) :
    verify_rounds S evals wits h c N pow_bits basis ≠ .error (.MissingPowWitness i b) := by
  rw [verify_rounds_eq]
  split_ifs <;> (try dsimp only) <;> (try split) <;> simp

/-- In the evaluation basis, replaying the pairs is replaying the decoded quadratics. -/
theorem replay_evaluation (c : EF) :
    ∀ (evals : List (EF × EF)) (rs : List EF), replay .Evaluation c evals rs = finalClaim decEval c evals rs
  | [], _ => by simp [replay, finalClaim]
  | _ :: _, [] => by simp [replay, finalClaim]
  | m :: ms, r :: rs => by
    rw [finalClaim, ← replay_evaluation]
    simp only [replay, List.zip_cons_cons, List.foldl_cons, reduce_claim_evaluation]

end Plonky3Lean.Proofs.Sumcheck
