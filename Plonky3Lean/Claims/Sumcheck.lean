module

public import Plonky3Lean.Proofs.Sumcheck.GenericDegree
public import Plonky3Lean.Proofs.Sumcheck.Prover

@[expose] public section

/-!
# p3-sumcheck: claims

The crate is transcribed over a field, not extracted.

The specification is the sumcheck protocol of Lund, Fortnow, Karloff and Nisan, as Thaler states it in Section 4.1:

```text
    claim:     H = sum_{b in {0,1}^n} g(b),   g of degree at most d in each variable
    round i:   the prover sends g_i of degree at most d
               the verifier checks g_i(0) + g_i(1) = c_i, samples r_i, sets c_{i+1} = g_i(r_i)
    end:       the verifier checks g(r) = c_n
```

Soundness counts the challenge vectors that accept a false claim: at most n d |F|^(n-1) of |F|^n, an error of n d / |F|.

The shipped verifier sends h(0) and the X^2 coefficient of a quadratic round, and rebuilds h(1) = c - h(0).

The generic-degree verifier sends h(x_0), h(x_2), ..., h(x_d) at the interpolation nodes, and rebuilds h(x_1) the same way.

The sponge is modelled by its history: each challenge is a function of everything absorbed before it.
-/

open MvPolynomial Finset Plonky3Lean.Spec.Sumcheck Plonky3Lean.Proofs.Sumcheck
open p3_sumcheck p3_sumcheck.mirror p3_sumcheck.lagrange.mirror

set_option linter.unusedSectionVars false

namespace Plonky3Lean.Claims.Sumcheck

variable {F : Type _} [Field F] [DecidableEq F]

/-! ## The protocol -/

/-- Completeness: the honest prover makes the verifier accept the true sum, on every challenge vector. -/
theorem protocol.completeness {n d : ℕ} (g : MvPolynomial (Fin n) F) (hg : IndividualDegreeLE g d)
    (r : Fin n → F) : Accepts d g (cubeSum g) (honestProver g) r :=
  Proofs.Sumcheck.completeness g hg r

open scoped Classical in
/-- Soundness: against a false claim and any causal prover, at most n d |F|^(n-1) challenge vectors accept. -/
theorem protocol.soundness [Fintype F] {n d : ℕ} (g : MvPolynomial (Fin n) F)
    (hg : IndividualDegreeLE g d) (H : F) (hH : H ≠ cubeSum g) (P : Fin n → (Fin n → F) → Polynomial F)
    (hP : Causal P) :
    #{r | Accepts d g H P r} * Fintype.card F ≤ n * d * Fintype.card F ^ n :=
  Proofs.Sumcheck.soundness g hg H hH P hP

/-! ## The quadratic round -/

/-- Interpolation through 0, 1 and infinity: a polynomial of degree at most 2 is recovered at r from h(0), h(1) and its X^2 coefficient. -/
theorem extrapolate_01inf.spec {p : Polynomial F} (hp : p.natDegree ≤ 2) (r : F) :
    extrapolate_01inf (p.eval 0) (p.eval 1) (p.coeff 2) r = p.eval r := by
  rw [← eval_quad, ← eq_quad hp]

/-- The evaluation basis: from h(0), h(inf) and the claim h(0) + h(1) = c, the round identity gives h(r). -/
theorem reduce_claim.evaluation {p : Polynomial F} (hp : p.natDegree ≤ 2) {c : F}
    (hc : p.eval 0 + p.eval 1 = c) (r : F) :
    Basis.Evaluation.reduce_claim (p.eval 0) (p.coeff 2) r c = p.eval r := by
  rw [reduce_claim_evaluation, ← encEval, decEval_encEval hp hc]

/-- The projective basis: from s(1), s(inf) and the claim s(0) + s(inf) = c, the round identity gives s(r). -/
theorem reduce_claim.projective {p : Polynomial F} (hp : p.natDegree ≤ 2) {c : F}
    (hc : p.eval 0 + p.coeff 2 = c) (r : F) :
    Basis.Projective.reduce_claim (p.eval 1) (p.coeff 2) r c = p.eval r := by
  rw [← hc, Basis.reduce_claim, add_sub_cancel_right, extrapolate_01inf.spec hp]

/-- Every pair of values decodes to a quadratic whose sum over {0, 1} is the claim, so the sum check of Section 4.1 always passes. -/
theorem reduce_claim.sum_check (c c_a c_inf : F) :
    (decEval c (c_a, c_inf)).natDegree ≤ 2 ∧
      (decEval c (c_a, c_inf)).eval 0 + (decEval c (c_a, c_inf)).eval 1 = c ∧
      ∀ r, Basis.Evaluation.reduce_claim c_a c_inf r c = (decEval c (c_a, c_inf)).eval r :=
  ⟨natDegree_decEval c _, decEval_sum c _, fun r => reduce_claim_evaluation c_a c_inf r c⟩

/-! ## The quadratic verifier -/

section Verifier

variable {G : Type _}

/-- A proof with the wrong number of rounds is rejected before any transcript step. -/
theorem verify_rounds.round_count (S : Sponge G F) (evals : List (F × F)) (wits : List G)
    (h : List (Step G F)) (c : F) (N pow_bits : ℕ) (basis : Basis) (hN : evals.length ≠ N) :
    verify_rounds S evals wits h c N pow_bits basis = .error (.RoundCountMismatch N evals.length) := by
  rw [verify_rounds_eq]; simp [hN]

/-- A proof with the wrong number of grinding witnesses is rejected: none without grinding, one per round with it. -/
theorem verify_rounds.witness_count (S : Sponge G F) (evals : List (F × F)) (wits : List G)
    (h : List (Step G F)) (c : F) (N pow_bits : ℕ) (basis : Basis) (hN : evals.length = N)
    (hw : wits.length ≠ if 0 < pow_bits then N else 0) :
    verify_rounds S evals wits h c N pow_bits basis =
      .error (.PowWitnessCountMismatch (if 0 < pow_bits then N else 0) wits.length) := by
  rw [verify_rounds_eq]; simp [hN, hw]

/-- The verifier never reports a missing witness, since the count is checked first. -/
theorem verify_rounds.never_missing_witness (S : Sponge G F) (evals : List (F × F)) (wits : List G)
    (h : List (Step G F)) (c : F) (N pow_bits : ℕ) (basis : Basis) (i b : ℕ) :
    verify_rounds S evals wits h c N pow_bits basis ≠ .error (.MissingPowWitness i b) :=
  verify_rounds_ne_missing S evals wits h c N pow_bits basis i b

/-- On a well-shaped proof, the first round whose witness fails is rejected. -/
theorem verify_rounds.invalid_witness (S : Sponge G F) (evals : List (F × F)) (wits : List G)
    (h : List (Step G F)) (c : F) (N pow_bits : ℕ) (basis : Basis) (hN : evals.length = N)
    (hw : wits.length = if 0 < pow_bits then N else 0) {i : ℕ}
    (hi : (List.range N).find? (fun i => !grindOk S (if 0 < N then h ++ [SumcheckShape.seed N pow_bits basis]
      else h) evals wits pow_bits i) = some i) :
    verify_rounds S evals wits h c N pow_bits basis = .error (.InvalidPowWitness i pow_bits) := by
  rw [verify_rounds_eq]
  simp only [hN, hw, ne_eq, not_true_eq_false, ↓reduceIte, hi]

/-- On a well-shaped proof whose witnesses pass, the verifier returns the challenges and the replayed claim.

Challenge i is the sponge sampled after the history at the start of round i and the steps of round i.

The claimed sum is not absorbed. -/
theorem verify_rounds.accept (S : Sponge G F) (evals : List (F × F)) (wits : List G)
    (h : List (Step G F)) (c : F) (N pow_bits : ℕ) (basis : Basis) (hN : evals.length = N)
    (hw : wits.length = if 0 < pow_bits then N else 0)
    (hi : (List.range N).find? (fun i => !grindOk S (if 0 < N then h ++ [SumcheckShape.seed N pow_bits basis]
      else h) evals wits pow_bits i) = none) :
    let h' := if 0 < N then h ++ [SumcheckShape.seed N pow_bits basis] else h
    let rs := (List.range N).map fun i =>
      S.sample (before h' evals wits pow_bits i ++ roundSteps evals wits pow_bits i)
    verify_rounds S evals wits h c N pow_bits basis =
      .ok (rs, replay basis c evals rs, before h' evals wits pow_bits N) := by
  rw [verify_rounds_eq]
  simp only [hN, hw, ne_eq, not_true_eq_false, ↓reduceIte, hi]
  rfl

/-- The history at the start of round i is the given history, then every earlier round with its challenge. -/
theorem verify_rounds.history (h : List (Step G F)) (evals : List (F × F)) (wits : List G)
    (pow_bits i : ℕ) :
    before h evals wits pow_bits i =
      h ++ (List.range i).flatMap fun j => roundSteps evals wits pow_bits j ++ [.challenge] :=
  before_eq h evals wits pow_bits i

/-- A round's steps start with its pair, so each challenge is drawn after the message it is evaluated against. -/
theorem verify_rounds.message_before_challenge (evals : List (F × F)) (wits : List G) (pow_bits i : ℕ) :
    (roundSteps evals wits pow_bits i).head? =
      some (.message [(evals.getD i (0, 0)).1, (evals.getD i (0, 0)).2]) := rfl

open scoped Classical in
/-- Soundness of the shipped quadratic verifier: against a false claim and any causal prover, at most 2 n |F|^(n-1) challenge vectors replay to g(r). -/
theorem verify_rounds.soundness [Fintype F] {n : ℕ} (g : MvPolynomial (Fin n) F)
    (hg : IndividualDegreeLE g 2) (H : F) (hH : H ≠ cubeSum g) (M : Fin n → (Fin n → F) → F × F)
    (hM : Causal M) :
    #{r | eval r g = replay .Evaluation H (List.ofFn fun i => M i r) (List.ofFn r)} *
      Fintype.card F ≤ n * 2 * Fintype.card F ^ n := by
  simpa only [replay_evaluation] using
    soundness_decoded decEval natDegree_decEval decEval_sum g hg H hH M hM

/-- Completeness of the shipped prover on a product of two multilinears: its messages replay to g(r) from the true sum. -/
theorem verify_rounds.completeness {n : ℕ} (f w : List F) (hf : f.length = 2 ^ n)
    (hw : w.length = 2 ^ n) (r : Fin n → F) :
    ∃ ms, proveProduct f w (List.ofFn r) = some ms ∧
      eval r (Spec.MultilinearUtil.mlePoly f n * Spec.MultilinearUtil.mlePoly w n) =
        replay .Evaluation (cubeSum (Spec.MultilinearUtil.mlePoly f n * Spec.MultilinearUtil.mlePoly w n))
          ms (List.ofFn r) :=
  proveProduct_complete f w hf hw r

/-- With no rounds, the final rounds return the empty point and leave the claim, whatever data the proof carries. -/
theorem verify_final_sumcheck_rounds.zero (S : Sponge G F) (data : Option (List (F × F) × List G))
    (h : List (Step G F)) (c : F) (pow_bits : ℕ) (basis : Basis) :
    verify_final_sumcheck_rounds S data h c 0 pow_bits basis = .ok ([], c, h) := rfl

/-- With rounds and no data, the final rounds are rejected. -/
theorem verify_final_sumcheck_rounds.missing (S : Sponge G F) (h : List (Step G F)) (c : F)
    {rounds : ℕ} (hr : rounds ≠ 0) (pow_bits : ℕ) (basis : Basis) :
    verify_final_sumcheck_rounds S none h c rounds pow_bits basis = .error (.MissingSumcheckData rounds) := by
  simp [verify_final_sumcheck_rounds, hr, throw, throwThe, MonadExceptOf.throw]

end Verifier

/-! ## The prover kernel -/

/-- The prefix kernel on two tables of 2^(n+1) entries sends h(0) and the X^2 coefficient of the honest round polynomial of their product. -/
theorem sumcheck_coefficients_prefix.honest (f w : List F) {n : ℕ} (hf : f.length = 2 ^ (n + 1))
    (hw : w.length = 2 ^ (n + 1)) :
    let s := honestMessage (Spec.MultilinearUtil.mlePoly f (n + 1) * Spec.MultilinearUtil.mlePoly w (n + 1))
    strategy.mirror.sumcheck_coefficients_prefix f w = some (s.eval 0, s.coeff 2) :=
  sumcheck_coefficients_prefix_honest f w hf hw

/-- The prefix kernel panics on tables of different or odd lengths. -/
theorem sumcheck_coefficients_prefix.panics (f w : List F) (h : f.length ≠ w.length ∨ f.length % 2 ≠ 0) :
    strategy.mirror.sumcheck_coefficients_prefix f w = none := by
  unfold strategy.mirror.sumcheck_coefficients_prefix
  split_ifs
  rfl

/-! ## The generic-degree verifier -/

section GenericDegree

open generic_degree.mirror

variable {G : Type _} (node : ℕ → F) {d : ℕ}

/-- The interpolator evaluates at r the polynomial of degree at most d with the transmitted values and the claim h(x_0) + h(x_1) = c, when x_0 = 0, x_1 = 1 and the nodes are distinct. -/
theorem RoundPolyInterpolator.eval.spec (hd : 0 < d) (h0 : node 0 = 0) (h1 : node 1 = 1)
    (hinj : Function.Injective fun i : Fin (d + 1) => node i) {wt : Fin (d + 1) → F}
    (hwt : RoundPolyInterpolator.new node d = some wt) {p : Polynomial F} (hp : p.natDegree ≤ d) {c : F}
    (hc : p.eval 0 + p.eval 1 = c) (r : F) :
    RoundPolyInterpolator.eval node d wt (List.ofFn (encGen (d := d) node p)) c r = some (p.eval r) := by
  rw [RoundPolyInterpolator.eval_eq node hd hwt, decGen_encGen node hinj hd h0 h1 hp hc]

/-- Building the interpolator panics exactly when two of the nodes 0, ..., d coincide. -/
theorem RoundPolyInterpolator.new.panics :
    RoundPolyInterpolator.new node d = none ↔ ¬ Function.Injective fun i : Fin (d + 1) => node i := by
  rw [RoundPolyInterpolator.new, Proofs.Matrix.Interp.barycentric_weights_eq]
  split_ifs <;> simp_all

/-- The verifier: the configuration checks, a panic on equal nodes, then the first rejected round, else the challenges and the replayed claim.

The claimed sum is absorbed after the seed, before the first challenge. -/
theorem verify.spec (S : Sponge G F) (c : F) (polys : List (List F)) (wits : List G)
    (h : List (Step G F)) (N pow_bits : ℕ) :
    verify S node c polys wits h N d pow_bits =
      if d = 0 then some (.error (.InvalidDegree d))
      else if polys.length ≠ N then some (.error (.RoundCountMismatch N polys.length))
      else if wits.length ≠ (if 0 < pow_bits then N else 0) then
        some (.error (.PowWitnessCountMismatch (if 0 < pow_bits then N else 0) wits.length))
      else if ¬ Function.Injective (fun i : Fin (d + 1) => node i) then none
      else
        let h' := h ++ [GenericDegreeShape.seed N d pow_bits, .message [c]]
        some (match (List.range N).findSome? (genErr S h' polys wits d pow_bits) with
        | some e => .error e
        | none =>
          let rs := (List.range N).map (genChallengeAt S h' polys wits pow_bits)
          .ok (rs, finalClaim (decGen node d) c (polys.map (toMsg d)) rs,
            genBefore h' polys wits pow_bits N)) :=
  verify_eq S node c polys wits h N d pow_bits

open scoped Classical in
/-- Soundness of the generic-degree verifier: against a false claim and any causal prover, at most n d |F|^(n-1) challenge vectors replay to g(r). -/
theorem verify.soundness [Fintype F] (hd : 0 < d) (h0 : node 0 = 0) (h1 : node 1 = 1)
    (hinj : Function.Injective fun i : Fin (d + 1) => node i) {n : ℕ} (g : MvPolynomial (Fin n) F)
    (hg : IndividualDegreeLE g d) (H : F) (hH : H ≠ cubeSum g) (M : Fin n → (Fin n → F) → Fin d → F)
    (hM : Causal M) :
    #{r | eval r g = finalClaim (decGen node d) H (List.ofFn fun i => M i r) (List.ofFn r)} *
      Fintype.card F ≤ n * d * Fintype.card F ^ n :=
  soundness_decoded (decGen node d) (natDegree_decGen node hinj) (decGen_sum node hinj hd h0 h1) g hg H
    hH M hM

/-- Completeness of the generic-degree verifier: the honest values replay to g(r) from the true sum. -/
theorem verify.completeness (hd : 0 < d) (h0 : node 0 = 0) (h1 : node 1 = 1)
    (hinj : Function.Injective fun i : Fin (d + 1) => node i) {n : ℕ} (g : MvPolynomial (Fin n) F)
    (hg : IndividualDegreeLE g d) (r : Fin n → F) :
    eval r g = finalClaim (decGen node d) (cubeSum g)
      (List.ofFn fun i => encGen node (honestProver g i r)) (List.ofFn r) :=
  completeness_decoded (decGen node d) (encGen node)
    (fun _ _ hp hc => decGen_encGen node hinj hd h0 h1 hp hc) g hg r

end GenericDegree

end Plonky3Lean.Claims.Sumcheck
