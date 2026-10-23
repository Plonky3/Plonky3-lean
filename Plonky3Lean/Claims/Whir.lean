module

public import Plonky3Lean.Proofs.Whir.Iteration
public import Plonky3Lean.Proofs.Whir.Query
public import Plonky3Lean.Proofs.Whir.Parameters
public import Plonky3Lean.Proofs.Whir.Robust
public import Plonky3Lean.Proofs.Whir.Zk
public import CompPoly.Fields.BabyBear.Ext4
public import ToCompPoly.Fields.KoalaBear.Extension

@[expose] public section

/-!
# p3-whir: claims

The verifier is transcribed over a field, not extracted.

The claims are stated at BabyBear and its quartic extension, and the main ones again at KoalaBear.

The specification is WHIR, eprint 2024/1586, Construction 5.1, in the encoding p3-whir uses:

```text
    sumcheck:  on the multilinear extension P~ of the table P
    code:      the univariate polynomial P^ with coefficients P, interleaved 2^k ways
    fold:      P' = P~(r, .) on the cube
    weight:    w'(x) = w(r, x) + sum_j gamma^(j+1) eq(pow(z_j), x) + sum_j gamma^(s+j+1) sel(q_j, x)
    claim:     sigma' = sigma_r + sum_j gamma^(j+1) y_j + sum_j gamma^(s+j+1) v_j
```

The sponge is its history: each challenge, index draw and grinding check is a function of what was absorbed before it.

The Merkle scheme, the grinding solver and the layout that batches the opening claims are hypotheses.
-/

open Finset Plonky3Lean.Spec.MultilinearUtil Plonky3Lean.Spec.Whir Plonky3Lean.Proofs.Whir
open p3_sumcheck.mirror p3_sumcheck.constraints.mirror p3_whir.mirror p3_whir.transcript.mirror
open p3_whir.parameters.mirror p3_whir.utils.mirror p3_multilinear_util.point.mirror

set_option linter.unusedSectionVars false

namespace Plonky3Lean.Claims.Whir

local notation "F" => BabyBear.Field
local notation "EF" => BabyBear.Ext4

/-! ## One iteration -/

/-- The fold the verifier computes from the 2^k values of row i is the folded table's polynomial at the i-th point of the folded domain. -/
theorem fold.row (P : List EF) {n : ℕ} (hP : P.length = 2 ^ n) (r : List EF) (hr : r.length ≤ n) (ω : EF)
    (i : ℕ) : mle (row P n r.length ω i) r = uni (foldTable P n r) (ω ^ i) :=
  mle_row P hP r hr ω i

/-- The folded table extends to the table's extension with its first variables set: P'~(s) = P~(r, s). -/
theorem fold.restrict (P r s : List EF) : mle (foldTable P (r.length + s.length) r) s = mle P (r ++ s) :=
  mle_foldTable P r s

/-- k honest sumcheck rounds replay the sum of P w over the cube to the sum over the folded tables. -/
theorem sumcheck.rounds (rs : List EF) {n : ℕ} (f w : List EF) (hf : f.length = 2 ^ n) (hw : w.length = 2 ^ n)
    (hk : rs.length ≤ n) :
    ∃ ms, Plonky3Lean.Proofs.Sumcheck.proveProduct f w rs = some ms ∧ ms.length = rs.length ∧
      Plonky3Lean.Proofs.Sumcheck.replay .Evaluation (∑ b ∈ range (2 ^ n), f.getD b 0 * w.getD b 0) ms rs =
        ∑ c ∈ range (2 ^ (n - rs.length)), (foldTable f n rs).getD c 0 * (foldTable w n rs).getD c 0 :=
  proveProduct_partial rs f w hf hw hk

/-- An out-of-domain answer is the sum of the table against eq(pow(z), .). -/
theorem weight.ood (P : List EF) (n : ℕ) (z : EF) :
    ∑ b ∈ range (2 ^ n), P.getD b 0 * eq (pow z n) (vertex n b) = mle P (pow z n) :=
  cubeDot_eq P n z

/-- A shift-query answer is the sum of the table against the selector of the powers of q. -/
theorem weight.query (P : List EF) {n : ℕ} (hP : P.length = 2 ^ n) (q : EF) :
    ∑ b ∈ range (2 ^ n), P.getD b 0 * sel q (vertex n b) = uni P q :=
  cubeDot_sel P hP q

/-- With honest answers, the claim update of check 2(c) is the sum of the folded table against the weight update of step 2(e). -/
theorem iteration.claim (P : List EF) {m : ℕ} (hP : P.length = 2 ^ m) (w : List EF → EF) (r : List EF) (γ : EF)
    (ood queries : List EF) :
    nextClaim (cubeDot P m fun x => w (r ++ x)) γ (ood.map fun z => mle P (pow z m)) (queries.map (uni P)) =
      cubeDot P m (nextWeight w r γ ood queries m) :=
  nextClaim_cubeDot P hP w r γ ood queries

/-- The verifier's round constraint batches its claims as check 2(c): gamma^(j+1) on the out-of-domain answers, then gamma^(s+j+1) on the query values. -/
theorem round.claim (σ γ : EF) (nv : ℕ) (pts : List (List EF)) (ys : List EF) (vars : List F) (vs : List EF)
    (hp : pts.length = ys.length) (hv : vars.length = vs.length) :
    (⟨nv, [.Eq ⟨nv, pts, ys⟩, .Select ⟨nv, vars, vs⟩], γ, 1⟩ : Constraint F EF).combine_evals σ =
      nextClaim σ γ ys vs :=
  round_combine_evals σ γ nv pts ys vars vs hp hv

/-- The verifier's round constraint weighs its points as step 2(e), with each out-of-domain point expanded to pow(z, n). -/
theorem round.weight (w : List EF → EF) (r : List EF) (γ : EF) (n : ℕ) (zs : List EF) (vars : List F)
    (vs : List EF) (hv : vars.length = vs.length) (x : List EF) :
    w (r ++ x) + weightAt (⟨n, [.Eq ⟨n, zs.map (Point.expand_from_univariate · n), zs.map fun _ => 0⟩,
      .Select ⟨n, vars, vs⟩], γ, 1⟩ : Constraint F EF) x =
      nextWeight w r γ zs (vars.map (algebraMap F EF)) n x :=
  round_weight w r γ n zs vars vs hv x

/-! ## Batched constraints -/

/-- A constraint's claim: every claimed value against its power, from the initial power on, the groups in order. -/
theorem combine_evals (c : Constraint F EF) (σ : EF) (h : ∀ s ∈ c.statements, s.WF) :
    c.combine_evals σ = σ + dot (c.statements.flatMap Statements.evals)
      (powers c.challenge c.initial_power (c.statements.flatMap Statements.evals).length) :=
  Constraint.combine_evals_eq c σ h

/-- The final weight: each constraint's batched weight at the last coordinates of the folding point, one per variable it was formed with. -/
theorem eval_constraints_poly (r : List EF) (cs : List (Constraint F EF)) (h : ∀ c ∈ cs, FitsEnd r c) :
    VariableOrder.Prefix.eval_constraints_poly cs r =
      some (cs.map fun c => weightAt c (r.drop (r.length - c.num_variables))).sum :=
  eval_constraints_poly_prefix r cs h

/-! ## The verifier -/

section Verifier

variable {Com MP D : Type _} (E : Env F EF Com MP) (PE : ProverEnv F EF Com MP D) (c : WhirConfig)

/-- Completeness: on a consistent configuration, the verifier accepts the honest prover's proof. -/
theorem verify.completeness {P0 : List F} {n : ℕ} {commitment : Com} (hv : Valid c n E.adicity)
    (hh : Honesty E PE c P0 n commitment) (seed : Step F EF) (h : List (Step F EF)) :
    ∃ out, verify E c seed (honestProof E PE c P0 n commitment (h ++ [seed])) commitment h = some (.ok out) :=
  verify_complete E PE c hv hh seed h

/-- The verifier never panics: on a consistent configuration, a layout of the polynomial's variable count and a Merkle scheme that checks row widths, every proof is accepted or rejected with an error.

Consistency includes that every folded domain fits the two-adicity, which the configuration does not check. -/
theorem verify.no_panic {n : ℕ} (hv : Valid c n E.adicity) (hw : Widths E.mmcs)
    (hlay : ∀ α, (E.initial α).num_variables = n ∧ ∀ s ∈ (E.initial α).statements, s.Dim n)
    (seed : Step F EF) (proof : WhirProof F EF Com MP) (commitment : Com) (h : List (Step F EF)) :
    (verify E c seed proof commitment h).isSome :=
  verify_some E c hv hw hlay seed proof commitment h

/-- A proof with another number of rounds is rejected before any transcript step. -/
theorem verify.round_count (seed : Step F EF) (proof : WhirProof F EF Com MP) (commitment : Com)
    (h : List (Step F EF)) (hn : proof.rounds.length ≠ c.n_rounds) :
    verify E c seed proof commitment h = some (.error (.RoundCountMismatch c.n_rounds proof.rounds.length)) := by
  simp [verify, hn]

/-- With no closing rounds, final sumcheck data in the proof is rejected rather than ignored. -/
theorem verify.unexpected_final_sumcheck (seed : Step F EF) (proof : WhirProof F EF Com MP) (commitment : Com)
    (h : List (Step F EF)) (hn : proof.rounds.length = c.n_rounds)
    (hc : ((c.round_parameters.zip proof.rounds).zipIdx).find?
      (fun e => e.1.1.pow_bits == 0 && e.1.2.pow_witness != 0) = none)
    (hf : ¬ (c.final_round_config.pow_bits = 0 ∧ proof.final_pow_witness ≠ 0))
    (h0 : c.final_sumcheck_rounds = 0) (hs : proof.final_sumcheck.isSome) :
    verify E c seed proof commitment h = some (.error .UnexpectedFinalSumcheck) := by
  simp [verify, hn, hc, hf, h0, hs]

/-- A parsed round: its claimed out-of-domain values are the proof's answers, absorbed after the root and each before the next point is drawn. -/
theorem parse_with_round.history (rp : WhirRoundProof F EF Com MP) (nv s t : ℕ) (h : List (Step F EF))
    {root : Com} {ood : EqStatement EF} {h' : List (Step F EF)}
    (hp : parse_with_round E rp nv s t h = .ok (root, ood, h')) :
    rp.commitment = some root ∧ ood.evaluations = rp.ood_answers ∧ rp.ood_answers.length = s ∧
      h' = h ++ [.message (E.enc root)] ++ rp.ood_answers.flatMap fun y => [.challenge, .message [y]] :=
  parse_with_round_history E rp nv s t h hp

end Verifier

/-! ## The query schedule -/

section Queries

variable (S : WSponge F EF)

/-- Every index a query phase plays lies in the folded domain, when each draw does. -/
theorem play_query_indices.range (hidx : ∀ h bits count, ∀ i ∈ S.indices h bits count, i < 2 ^ bits)
    (hlen : ∀ h bits count, (S.indices h bits count).length = count) (h : List (Step F EF)) {width draws : ℕ}
    (hd : draws = 0 ∨ draws < 2 ^ width) (stratified : Bool) :
    ∀ i ∈ (play_query_indices S h width draws stratified (query_summand_depths draws)).1, i < 2 ^ width :=
  play_query_indices_lt S hidx hlen h hd stratified

/-- A query phase plays its draw count, and every position when the draw count is zero. -/
theorem play_query_indices.count (hlen : ∀ h bits count, (S.indices h bits count).length = count)
    (h : List (Step F EF)) (width draws : ℕ) (stratified : Bool) :
    (play_query_indices S h width draws stratified (query_summand_depths draws)).1.length =
      if draws = 0 then 2 ^ width else draws :=
  length_play_query_indices S hlen h width draws stratified

/-- The strata of a stratified schedule are the binary digits of the count. -/
theorem query_summand_depths.sum (m : ℕ) : ((query_summand_depths m).map (2 ^ ·)).sum = m :=
  sum_query_summand_depths m

/-- A stratified draw lands in its stratum. -/
theorem stratified_index.stratum {width depth stratum low : ℕ} (hlow : low < 2 ^ (width - depth)) :
    stratified_index width depth stratum low >>> (width - depth) = stratum :=
  stratified_index_stratum hlow

/-- A positive query count below the folded domain opens at most that many distinct positions, all in the domain: the count a t-private encoding needs. -/
theorem play_query_indices.opened (hidx : ∀ h bits count, ∀ i ∈ S.indices h bits count, i < 2 ^ bits)
    (hlen : ∀ h bits count, (S.indices h bits count).length = count) (h : List (Step F EF)) {width q : ℕ}
    (hq0 : 0 < q) (hq : q < 2 ^ width) (stratified : Bool) :
    let idx := (play_query_indices S h width (query_draws (2 ^ width) q) stratified
      (query_summand_depths (query_draws (2 ^ width) q))).1
    idx.toFinset.card ≤ q ∧ ∀ i ∈ idx, i < 2 ^ width :=
  opened_le_queries S hidx hlen h hq0 hq stratified

end Queries

/-! ## Zero knowledge -/

/-- The private out-of-domain answer of a hiding round is the polynomial of the message followed by the randomness. -/
theorem zk.padded_ood (point : F) (msg rand : List EF) :
    padded_ood_t1 point msg rand = uni (msg ++ rand) (algebraMap F EF point) :=
  padded_ood_t1_eq point msg rand

/-- Lemma 9.3 of eprint 2026/391 at r = 1: at a nonzero point, the answer is a bijection of the one randomness coefficient, whatever the message. -/
theorem zk.padded_ood_bijective {point : F} (hp : point ≠ 0) (msg : List EF) :
    Function.Bijective fun x : EF => padded_ood_t1 point msg [x] :=
  padded_ood_t1_bijective hp msg

/-- At the point zero the answer is the message's constant coefficient, whatever the randomness. -/
theorem zk.padded_ood_zero (a : EF) (msg rand : List EF) : padded_ood_t1 (0 : F) (a :: msg) rand = a :=
  padded_ood_t1_zero a msg rand

/-- eval_ze_star_n is the polynomial with the given coefficients at the point. -/
theorem zk.eval_ze_star_n (point : F) (c : List EF) : eval_ze_star_n point c = uni c (algebraMap F EF point) :=
  eval_ze_star_n_eq point c

/-! ## Parameters -/

/-- The schedule check misses later folds: 28 variables at rate 1/4, schedule [8, 2, 18] and rates [10, 10] pass it, and round 1 queries a folded domain of 2^28 points, above BabyBear's two-adicity 27. -/
theorem schedule.later_fold_exceeds (cs : Counts) :
    ∃ c, schedule cs 28 2 [8, 2, 18] [10, 10] 27 = .ok c ∧
      (c.round_parameters.map (·.log_folded_domain_size)) = [22, 28] :=
  Plonky3Lean.Proofs.Whir.later_fold_exceeds cs

/-- Past the two-adicity the generator does not exist, and the verifier panics. -/
theorem two_adic_generator.panics (gen : ℕ → F) {adicity bits : ℕ} (h : adicity < bits) :
    two_adic_generator adicity gen bits = none := by
  simp [two_adic_generator, Nat.not_le.mpr h]

end Plonky3Lean.Claims.Whir

/-! ## At KoalaBear -/

namespace Plonky3Lean.Claims.Whir.KoalaBear

local notation "F" => KoalaBear.Field
local notation "EF" => KoalaBear.Ext4

/-- The fold of an opened row, at KoalaBear. -/
theorem fold.row (P : List EF) {n : ℕ} (hP : P.length = 2 ^ n) (r : List EF) (hr : r.length ≤ n) (ω : EF)
    (i : ℕ) : mle (row P n r.length ω i) r = uni (foldTable P n r) (ω ^ i) :=
  mle_row P hP r hr ω i

open scoped Classical in
/-- Completeness, at KoalaBear. -/
theorem verify.completeness {Com MP D : Type _} (E : Env F EF Com MP) (PE : ProverEnv F EF Com MP D)
    (c : WhirConfig) {P0 : List F} {n : ℕ} {commitment : Com} (hv : Valid c n E.adicity)
    (hh : Honesty E PE c P0 n commitment) (seed : Step F EF) (h : List (Step F EF)) :
    ∃ out, verify E c seed (honestProof E PE c P0 n commitment (h ++ [seed])) commitment h = some (.ok out) :=
  verify_complete E PE c hv hh seed h

end Plonky3Lean.Claims.Whir.KoalaBear
