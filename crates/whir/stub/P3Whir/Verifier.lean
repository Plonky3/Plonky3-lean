/-
Transcriptions of the WHIR verifier.

They cover pcs/verifier/mod.rs, committer/reader.rs, and the verifier transcript of transcript/mod.rs.

The domain is the two-adic one, whose query points are powers of the generator.
-/
module

public import P3Whir.Query
public import P3MultilinearUtil.Mirror.SplitEq

@[expose] public section

namespace p3_whir.mirror

open p3_sumcheck.mirror p3_sumcheck.constraints.mirror p3_whir.transcript.mirror
open p3_multilinear_util.point.mirror p3_multilinear_util.poly.mirror p3_multilinear_util.split_eq.mirror

/-- The fields of RoundConfig the verifier reads. -/
structure RoundConfig where
  pow_bits : ℕ
  folding_pow_bits : ℕ
  num_queries : ℕ
  ood_samples : ℕ
  num_variables : ℕ
  folding_factor : ℕ
  domain_size : ℕ
  log_folded_domain_size : ℕ
  deriving Inhabited

/-- The fields of WhirConfig the verifier reads. -/
structure WhirConfig where
  round_parameters : List RoundConfig
  folding_schedule : List ℕ
  starting_folding_pow_bits : ℕ
  final_sumcheck_rounds : ℕ
  final_folding_pow_bits : ℕ
  terminal_num_queries : ℕ
  terminal_pow_bits : ℕ
  final_round_config : RoundConfig
  stratified_queries : Bool

/-- WhirConfig::n_rounds. -/
def WhirConfig.n_rounds (c : WhirConfig) : ℕ := c.round_parameters.length

/-- WhirConfig::round_folding_factor, which panics past the schedule. -/
def WhirConfig.round_folding_factor (c : WhirConfig) (round : ℕ) : Option ℕ := c.folding_schedule[round]?

/-- The numbers of one query site of the shape.

They are the index width, the draw count and the summand depths. -/
structure QuerySite where
  pow_bits : ℕ
  index_bits : ℕ
  draws : ℕ
  depths : List ℕ
  deriving Inhabited

/-- The query site of a round: the folded domain, its draws and their width.

It asserts the folded size is a power of two. -/
def querySite (domain_size folding num_queries pow_bits : ℕ) : Option QuerySite :=
  let folded := domain_size >>> folding
  if folded ≠ 0 ∧ 2 ^ Nat.log 2 folded = folded then
    let draws := query_draws folded num_queries
    some ⟨pow_bits, Nat.log 2 folded, draws, query_summand_depths draws⟩
  else none

/-- The query site of a round, or of the final phase one past the last round. -/
def WhirConfig.site (c : WhirConfig) (round : ℕ) : Option QuerySite :=
  if round < c.n_rounds then do
    let p ← c.round_parameters[round]?
    let k ← c.round_folding_factor round
    querySite p.domain_size k p.num_queries p.pow_bits
  else
    querySite c.final_round_config.domain_size c.final_round_config.folding_factor
      c.terminal_num_queries c.terminal_pow_bits

/-- The errors the verifier raises. -/
inductive VerifierError where
  | MerkleProofInvalid (round : ℕ)
  | SumcheckFailed (round : ℕ)
  | StirChallengeFailed
  | StirQueryCountMismatch (round_index expected actual : ℕ)
  | Sumcheck (e : SumcheckError)
  | InvalidPowWitness (round bits : ℕ)
  | NonCanonicalPowWitness (round : ℕ)
  | UnexpectedFinalSumcheck
  | MissingRoundCommitment (round : ℕ)
  | RoundOodAnswerCountMismatch (round expected actual : ℕ)
  | RoundCountMismatch (expected actual : ℕ)
  | MissingFinalPoly
  | FinalPolyLengthMismatch (expected actual : ℕ)
  deriving DecidableEq

/-- QueryOpenings: the opened rows of one round.

They are in the base field at round 0, and in the extension after. -/
inductive QueryOpenings (F EF MP : Type _) where
  | Base (rows : List (List F)) (proof : MP)
  | Extension (rows : List (List EF)) (proof : MP)

/-- SumcheckData: the pairs of each round and the grinding witnesses. -/
abbrev SumcheckData (F EF : Type _) := List (EF × EF) × List F

/-- WhirRoundProof. -/
structure WhirRoundProof (F EF Com MP : Type _) where
  commitment : Option Com
  ood_answers : List EF
  pow_witness : F
  openings : QueryOpenings F EF MP
  sumcheck : SumcheckData F EF

/-- WhirProof, without the initial OOD answers the layout reads. -/
structure WhirProof (F EF Com MP : Type _) where
  initial_sumcheck : SumcheckData F EF
  rounds : List (WhirRoundProof F EF Com MP)
  final_poly : Option (List EF)
  final_pow_witness : F
  final_openings : QueryOpenings F EF MP
  final_sumcheck : Option (SumcheckData F EF)

section Verifier

variable {F EF Com MP : Type _} [Field F] [Field EF] [Algebra F EF] [DecidableEq F] [DecidableEq EF]

/-- What a verifier run is given besides the proof:

- the sponge
- the Merkle scheme
- the commitment encoding
- the generator
- the evaluation thresholds
- the layout. -/
structure Env (F EF Com MP : Type _) [Field EF] where
  S : WSponge F EF
  mmcs : Mmcs F EF Com MP
  enc : Com → List EF
  adicity : ℕ
  gen : ℕ → F
  thr : ℕ
  w : ℕ
  T : ℕ
  /-- The step the layout's batching phase absorbs before its challenge. -/
  layoutSeed : Step F EF
  /-- The initial constraint the layout builds from its challenge. -/
  initial : EF → Constraint F EF

variable (E : Env F EF Com MP)

/-- WhirVerifierTranscript::query_pow: nothing at zero difficulty.

Otherwise it checks the grinding and absorbs the witness. -/
def query_pow (round bits : ℕ) (witness : F) (h : List (Step F EF)) :
    Except VerifierError (List (Step F EF)) :=
  if bits = 0 then pure h
  else if E.S.grind h bits witness then pure (h ++ [.pow bits witness])
  else throw (.InvalidPowWitness round bits)

/-- A sumcheck run: its errors become verifier errors. -/
def sumcheck (data : SumcheckData F EF) (h : List (Step F EF)) (claimed : EF) (rounds pow_bits : ℕ) :
    Except VerifierError (List EF × EF × List (Step F EF)) :=
  (verify_rounds E.S.toSponge data.1 data.2 h claimed rounds pow_bits .Evaluation).mapError .Sumcheck

/-- verify_merkle_proof: the round's rows, lifted to the extension.

It first checks the variant, the count and the Merkle proof. -/
def verify_merkle_proof (openings : QueryOpenings F EF MP) (root : Com) (indices : List ℕ) (dims : ℕ × ℕ)
    (round_index : ℕ) : Except VerifierError (List (List EF)) :=
  match openings, round_index == 0 with
  | .Base rows proof, true =>
    if rows.length ≠ indices.length then
      throw (.StirQueryCountMismatch round_index indices.length rows.length)
    else if E.mmcs.verifyBase root dims indices rows proof then
      pure (rows.map (·.map (algebraMap F EF)))
    else throw (.MerkleProofInvalid round_index)
  | .Extension rows proof, false =>
    if rows.length ≠ indices.length then
      throw (.StirQueryCountMismatch round_index indices.length rows.length)
    else if E.mmcs.verifyExt root dims indices rows proof then pure rows
    else throw (.MerkleProofInvalid round_index)
  | _, _ => throw (.MerkleProofInvalid round_index)

/-- verify_stir_challenges: grind, draw the indices, and open and fold each row.

Each fold is paired with its domain point.

A panic is none, as in the generator lookup, the polynomial constructor and the evaluation. -/
def verify_stir_challenges (c : WhirConfig) (openings : QueryOpenings F EF MP) (pow_witness : F)
    (params : RoundConfig) (root : Com) (folding_randomness : List EF) (round_index : ℕ)
    (h : List (Step F EF)) : Option (Except VerifierError (SelectStatement F EF × List (Step F EF))) := do
  let site ← c.site round_index
  match query_pow E round_index site.pow_bits pow_witness h with
  | .error e => pure (.error e)
  | .ok h =>
    let (indices, h) := play_query_indices E.S h site.index_bits site.draws c.stratified_queries site.depths
    let dims := (params.domain_size >>> params.folding_factor, 2 ^ params.folding_factor)
    match verify_merkle_proof E openings root indices dims round_index with
    | .error e => pure (.error e)
    | .ok answers =>
      let folds ← answers.mapM fun a => do
        let p ← Poly.new a
        Poly.eval_ext E.thr E.w E.T p folding_randomness
      let g ← two_adic_generator E.adicity E.gen params.log_folded_domain_size
      pure (.ok (⟨params.num_variables, indices.map (g ^ ·), folds⟩, h))

/-- ParsedCommitment::parse_with_round: the root is absorbed first.

Then each OOD point is drawn and its answer absorbed. -/
def parse_with_round (rp : WhirRoundProof F EF Com MP) (num_variables ood_samples round_index : ℕ)
    (h : List (Step F EF)) : Except VerifierError (Com × EqStatement EF × List (Step F EF)) :=
  match rp.commitment with
  | none => throw (.MissingRoundCommitment round_index)
  | some root =>
    if rp.ood_answers.length ≠ ood_samples then
      throw (.RoundOodAnswerCountMismatch round_index ood_samples rp.ood_answers.length)
    else
      let h := h ++ [.message (E.enc root)]
      let (pts, h) := (List.range ood_samples).foldl (fun (acc : List (List EF) × List (Step F EF)) i =>
        let z := E.S.sample acc.2
        let point := Point.expand_from_univariate z num_variables
        (acc.1 ++ [point], acc.2 ++ [.challenge, .message [rp.ood_answers.getD i 0]])) ([], h)
      pure (root, ⟨num_variables, pts, rp.ood_answers⟩, h)

/-- The state the round loop carries:

- the constraints
- the folding randomness per phase
- the previous root
- the claim and the history. -/
structure LoopState (F EF Com : Type _) where
  constraints : List (Constraint F EF)
  randomness : List (List EF)
  prev : Com
  claimed : EF
  h : List (Step F EF)

/-- One intermediate round of replay. -/
def roundStep (c : WhirConfig) (proof : WhirProof F EF Com MP) (st : LoopState F EF Com) (round_index : ℕ) :
    Option (Except VerifierError (LoopState F EF Com)) := do
  let params ← c.round_parameters[round_index]?
  let rp ← proof.rounds[round_index]?
  match parse_with_round E rp params.num_variables params.ood_samples round_index st.h with
  | .error e => pure (.error e)
  | .ok (root, ood, h) =>
    let r ← st.randomness.getLast?
    match ← verify_stir_challenges E c rp.openings rp.pow_witness params st.prev r round_index h with
    | .error e => pure (.error e)
    | .ok (stir, h) =>
      let gamma := E.S.sample h
      let h := h ++ [.challenge]
      let constraint ← Constraint.new_with_existing_claim gamma ood.num_variables [.Eq ood, .Select stir]
      let claimed := constraint.combine_evals st.claimed
      let k ← c.round_folding_factor (round_index + 1)
      match sumcheck E rp.sumcheck h claimed k params.folding_pow_bits with
      | .error e => pure (.error e)
      | .ok (rs, claimed, h) =>
        pure (.ok ⟨st.constraints ++ [constraint], st.randomness ++ [rs], root, claimed, h⟩)

/-- One step of the round loop of replay.

An earlier rejection is kept, otherwise the round runs. -/
def loopStep (c : WhirConfig) (proof : WhirProof F EF Com MP) (acc : Except VerifierError (LoopState F EF Com))
    (round_index : ℕ) : Option (Except VerifierError (LoopState F EF Com)) :=
  match acc with
  | .error e => pure (.error e)
  | .ok st => roundStep E c proof st round_index

/-- replay, in order:

- the initial fold
- every round
- the final polynomial and its queries
- the closing fold
- the final identity. -/
def replay (c : WhirConfig) (proof : WhirProof F EF Com MP) (commitment : Com) (h : List (Step F EF)) :
    Option (Except VerifierError (List EF × List (Step F EF))) := do
  -- The layout's batching seed and challenge, then the initial sumcheck.
  let h := h ++ [E.layoutSeed]
  let alpha := E.S.sample h
  let h := h ++ [.challenge]
  let constraint := E.initial alpha
  let claimed := constraint.combine_evals 0
  let k0 ← c.round_folding_factor 0
  match sumcheck E proof.initial_sumcheck h claimed k0 c.starting_folding_pow_bits with
  | .error e => pure (.error e)
  | .ok (rs0, claimed, h) =>
  let st0 : LoopState F EF Com := ⟨[constraint], [rs0], commitment, claimed, h⟩
  match ← (List.range c.n_rounds).foldlM (loopStep E c proof) (.ok st0) with
  | .error e => pure (.error e)
  | .ok st =>
  match proof.final_poly with
  | none => pure (.error .MissingFinalPoly)
  | some final_evaluations =>
  let expected := 2 ^ c.final_round_config.num_variables
  if final_evaluations.length ≠ expected then
    pure (.error (.FinalPolyLengthMismatch expected final_evaluations.length))
  else
  let h := st.h ++ [.message final_evaluations]
  let r ← st.randomness.getLast?
  match ← verify_stir_challenges E c proof.final_openings proof.final_pow_witness c.final_round_config
      st.prev r c.n_rounds h with
  | .error e => pure (.error e)
  | .ok (stir, h) =>
  if !stir.verify final_evaluations then pure (.error .StirChallengeFailed)
  else
  -- The closing fold, played only when it has rounds.
  let fin : Except VerifierError (List EF × EF × List (Step F EF)) :=
    if 0 < c.final_sumcheck_rounds then
      (verify_final_sumcheck_rounds E.S.toSponge proof.final_sumcheck h st.claimed c.final_sumcheck_rounds
        c.final_folding_pow_bits .Evaluation).mapError .Sumcheck
    else pure ([], st.claimed, h)
  match fin with
  | .error e => pure (.error e)
  | .ok (rf, claimed, h) =>
  let folding_randomness := (st.randomness ++ [rf]).flatten
  let weights ← VariableOrder.Prefix.eval_constraints_poly st.constraints folding_randomness
  let final_value ← Poly.eval_ext E.thr E.w E.T final_evaluations rf
  if claimed ≠ weights * final_value then pure (.error (.SumcheckFailed c.final_sumcheck_rounds))
  else pure (.ok (folding_randomness, h))

/-- WhirVerifier::verify: the shape checks, then the seed and the replay. -/
def verify (c : WhirConfig) (seed : Step F EF) (proof : WhirProof F EF Com MP) (commitment : Com)
    (h : List (Step F EF)) : Option (Except VerifierError (List EF × List (Step F EF))) :=
  if proof.rounds.length ≠ c.n_rounds then
    some (.error (.RoundCountMismatch c.n_rounds proof.rounds.length))
  else match ((c.round_parameters.zip proof.rounds).zipIdx).find?
      (fun e => e.1.1.pow_bits == 0 && e.1.2.pow_witness != 0) with
  | some e => some (.error (.NonCanonicalPowWitness e.2))
  | none =>
    if c.final_round_config.pow_bits = 0 ∧ proof.final_pow_witness ≠ 0 then
      some (.error (.NonCanonicalPowWitness c.n_rounds))
    else if c.final_sumcheck_rounds = 0 ∧ proof.final_sumcheck.isSome then
      some (.error .UnexpectedFinalSumcheck)
    else replay E c proof commitment (h ++ [seed])

end Verifier

end p3_whir.mirror
