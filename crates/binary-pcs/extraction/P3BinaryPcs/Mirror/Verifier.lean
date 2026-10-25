/-
Transcriptions of the verifier: verifier.rs, the opening verifier of pcs.rs, and error.rs.

The layout that batches the opening claims is abstract.

It does three things:

- record each claim against the transcript
- absorb its seed before the batching challenge
- turn that challenge into the claimed sum and the weight polynomial.

The opening protocol is its claim capacity check, its table counts and its batch shapes.
-/
module

public import P3BinaryPcs.Fold
public import P3BinaryPcs.Transcript

@[expose] public section

namespace p3_binary_pcs.verifier.mirror

open p3_sumcheck.mirror p3_binary_dft.mirror p3_binary_pcs.mirror p3_binary_pcs.params.mirror
open p3_binary_pcs.transcript.mirror p3_binary_pcs.fold.mirror

/-- Why the verifier rejects a proof. -/
inductive BinaryPcsError (F E : Type _) where
  | RoundCountMismatch (expected actual : ℕ)
  | OpeningCountMismatch (round expected actual : ℕ)
  | RowWidthMismatch (round query expected actual : ℕ)
  | FinalCodewordLengthMismatch (expected actual : ℕ)
  | MerkleFailed (round : ℕ) (source : E)
  | FoldMismatch (round query : ℕ)
  | FinalCheck
  | InvalidPowWitness
  | OpeningBatchCountMismatch (expected actual : ℕ)
  | OpeningClaimCountExceedsSecurityBudget (actual max security_level : ℕ)
  | InvalidOpeningProtocol
  | OpeningPointShapeMismatch
  | OpeningEvalCountMismatch (expected actual : ℕ)
  | OpeningBatchSizeMismatch (table_idx expected_current expected_next actual_current actual_next : ℕ)
  | OpeningPreprocessingDepth (folding : ℕ)
  | Sumcheck (e : SumcheckError)
  | NonEmptyPowWitnesses (actual : ℕ)
  | NonCanonicalPowWitness (actual : F)

/-- The rejection a failed transcript step maps to. -/
def BinaryPcsError.ofTranscript {F E : Type _} : TranscriptFailure F → BinaryPcsError F E
  | .FinalCodewordLength expected got => .FinalCodewordLengthMismatch expected got
  | .PowWitness _ => .InvalidPowWitness
  | .NonCanonicalPowWitness actual => .NonCanonicalPowWitness actual

/-- The proof of one round: its commitment, its opened rows and its Merkle multi-proof. -/
structure RoundProof (EF ComX MPX : Type _) where
  commitment : ComX
  opened_values : List (List EF)
  multi_proof : MPX

/-- A binary PCS proof.

Each opening batch is its current and successor evaluations. -/
structure BinaryPcsProof (F EF ComX MPT MPX : Type _) where
  polynomial_evaluations : List (EF × EF)
  pow_witnesses : List F
  rounds : List (RoundProof EF ComX MPX)
  base_opened_values : List (List F)
  base_multi_proof : MPT
  final_codeword : List EF
  pow_witness : F
  evals : List (List EF × List EF)

/-- What the opening verifier reads of an opening protocol. -/
structure OpeningProtocol where
  /-- The stacked cell count, none on overflow. -/
  cells : Option ℕ
  /-- The scalar claim count, none on overflow. -/
  claims : Option ℕ
  /-- Each opening batch: its table, and its current and successor column counts. -/
  openings : List (ℕ × ℕ × ℕ)

/-- ceil(log_2 n): the bit length of n - 1. -/
def log2_ceil_usize (n : ℕ) : ℕ := if n ≤ 1 then 0 else Nat.log2 (n - 1) + 1

/-- What a verifier run is given besides the proof. -/
structure Env (F EF ComT ComX MPT MPX E : Type _) [Field F] [Field EF] where
  S : PSponge F EF
  mmcs : Mmcs F EF ComT ComX MPT MPX E
  /-- The extension elements a round root is absorbed as. -/
  enc : ComX → List EF
  /-- The alphabet's level and the challenge field's. -/
  LF : Level F
  LE : Level EF
  /-- The claim capacity the security model leaves. -/
  max_claims : ℕ
  /-- Record one batch's claim in the layout, against the history. -/
  addClaim : List (Step F EF) → ℕ → Except SumcheckError (List (Step F EF))
  /-- The step the layout absorbs before its batching challenge. -/
  layoutSeed : Step F EF
  /-- The claimed sum the constraint of a batching challenge combines from zero. -/
  claimedSum : EF → EF
  /-- The weight polynomial of a batching challenge at the fold point. -/
  weights : EF → List EF → EF

section Verifier

variable {F EF ComT ComX MPT MPX E : Type} [Field F] [Field EF] [Algebra F EF] [DecidableEq F]
  [DecidableEq EF] (V : Env F EF ComT ComX MPT MPX E)

/-- Every symbol of each queried coset.

They come in query order, and in ascending order within a coset. -/
def flat_coset_indices (indices : List ℕ) (start arity : ℕ) : List ℕ :=
  indices.flatMap fun index =>
    let first := (index >>> start) >>> arity <<< arity
    List.range' first (2 ^ arity)

/-- Check a round's shape: the row count, then a width of one for each row. -/
def check_round_shape {A : Type _} (round : ℕ) (opened_values : List (List A)) (expected_opens : ℕ) :
    Except (BinaryPcsError F E) Unit :=
  if opened_values.length ≠ expected_opens then
    .error (.OpeningCountMismatch round expected_opens opened_values.length)
  else
    match (List.range opened_values.length).find? fun q => (opened_values.getD q []).length ≠ 1 with
    | some q => .error (.RowWidthMismatch round q 1 (opened_values.getD q []).length)
    | none => .ok ()

/-- Check the round count, then the final codeword's length. -/
def check_round_and_final_lengths (c : BinaryPcsConfig) (proof : BinaryPcsProof F EF ComX MPT MPX) :
    Option (Except (BinaryPcsError F E) Unit) := do
  let batches ← c.num_fold_batches
  if batches = 0 then none
  if proof.rounds.length ≠ batches - 1 then
    return .error (.RoundCountMismatch (batches - 1) proof.rounds.length)
  if c.log_final_len ≥ USIZE_BITS then none
  if proof.final_codeword.length ≠ 2 ^ c.log_final_len then
    return .error (.FinalCodewordLengthMismatch (2 ^ c.log_final_len) proof.final_codeword.length)
  pure (.ok ())

/-- At zero difficulty, the grinding witness must be zero. -/
def check_canonical_pow_witness (c : BinaryPcsConfig) (proof : BinaryPcsProof F EF ComX MPT MPX) :
    Except (BinaryPcsError F E) Unit :=
  if c.params.pow_bits = 0 ∧ proof.pow_witness ≠ 0 then .error (.NonCanonicalPowWitness proof.pow_witness)
  else .ok ()

/-- Fold a queried coset.

A single challenge folds one pair, and more challenges fold the gathered coset. -/
def fold_query_coset {A : Type _} [Field A] [Algebra A EF] (L : Level A) (rows : List (List A))
    (query next_position : ℕ) (betas : List EF) : Option EF := do
  match betas with
  | [beta] => do
    let lo ← (← rows[2 * query]?)[0]?
    let hi ← (← rows[2 * query + 1]?)[0]?
    fold_pair L next_position beta lo hi
  | _ => do
    let size := 2 ^ betas.length
    let coset := (rows.drop (query * size)).take size
    if coset.length ≠ size then none
    let gather ← coset.mapM (·[0]?)
    fold_coset L V.LE next_position gather betas

/-- The fold check of one batch of one query: the folded coset against the next word's symbol. -/
def foldCheck (betas : List EF) (proof : BinaryPcsProof F EF ComX MPT MPX)
    (batches : List (ℕ × ℕ)) (q index batch : ℕ) : Option (Except (BinaryPcsError F E) Unit) := do
  let (start, arity) ← batches[batch]?
  let next_position := index >>> (start + arity)
  if betas.length < start + arity then none
  let bs := (betas.drop start).take arity
  let folded ← if batch = 0 then fold_query_coset V V.LF proof.base_opened_values q next_position bs
    else do
      let r ← proof.rounds[batch - 1]?
      fold_query_coset V V.LE r.opened_values q next_position bs
  let expected ← match batches[batch + 1]? with
    | some (_, next_arity) => do
      let next_size := 2 ^ next_arity
      let r ← proof.rounds[batch]?
      let row ← r.opened_values[q * next_size + next_position % next_size]?
      row[0]?
    | none => proof.final_codeword[next_position]?
  pure (if folded ≠ expected then .error (.FoldMismatch (batch + 1) q) else .ok ())

/-- Run checks in order, keeping the first rejection.

A panic is none. -/
def firstError {α ε : Type _} (xs : List α) (f : α → Option (Except ε Unit)) : Option (Except ε Unit) :=
  xs.foldlM (fun acc x => match acc with
    | .error e => pure (.error e)
    | .ok () => f x) (.ok ())

/-- Verify the query paths, in order:

- the shape checks
- the final codeword
- the grind
- the draw
- the Merkle openings
- the fold chain.

It asserts one fold challenge per round. -/
def verify_query_paths (c : BinaryPcsConfig) (base_commitment : ComT) (betas : List EF)
    (proof : BinaryPcsProof F EF ComX MPT MPX) (s : BinaryPcsShape) (h : List (Step F EF)) :
    Option (Except (BinaryPcsError F E) (List (Step F EF))) := do
  if betas.length ≠ c.num_fold_rounds then none
  match ← check_round_and_final_lengths c proof with
  | .error e => return .error e
  | .ok () =>
  match check_canonical_pow_witness c proof with
  | .error e => return .error e
  | .ok () =>
  let domain_size ← c.domain_size
  let target_queries := min c.num_queries (domain_size >>> c.log_folding_factor)
  let batches ← c.fold_batches
  let b0 ← batches[0]?
  match check_round_shape 0 proof.base_opened_values (target_queries <<< b0.2) with
  | .error e => return .error e
  | .ok () =>
  match ← firstError (List.range (batches.length - 1)) (fun i => do
      let (_, arity) ← batches[i + 1]?
      let r ← proof.rounds[i]?
      pure (check_round_shape (i + 1) r.opened_values (target_queries <<< arity))) with
  | .error e => return .error e
  | .ok () =>
  match final_codeword s proof.final_codeword h with
  | .error e => return .error (.ofTranscript e)
  | .ok h =>
  match query_pow V.S s proof.pow_witness h with
  | .error e => return .error (.ofTranscript e)
  | .ok h =>
  if c.log_folding_factor = 0 then none
  let shift := c.log_folding_factor - 1
  let (pairs, h) := query_pairs V.S s h
  let indices := pairs.map (· <<< shift)
  match V.mmcs.verifyBase base_commitment (1, domain_size) (flat_coset_indices indices 0 b0.2)
      proof.base_opened_values proof.base_multi_proof with
  | .error e => return .error (.MerkleFailed 0 e)
  | .ok () =>
  match ← firstError (List.range (batches.length - 1)) (fun i => do
      let (start, arity) ← batches[i + 1]?
      let r ← proof.rounds[i]?
      pure (match V.mmcs.verifyRound r.commitment (1, domain_size >>> start)
          (flat_coset_indices indices start arity) r.opened_values r.multi_proof with
        | .error e => .error (.MerkleFailed (i + 1) e)
        | .ok () => .ok ())) with
  | .error e => return .error e
  | .ok () =>
  match ← firstError (List.range indices.length) (fun q => do
      let index ← indices[q]?
      firstError (List.range batches.length) (foldCheck V betas proof batches q index)) with
  | .error e => return .error e
  | .ok () => pure (.ok h)

/-- Validate the opening protocol.

The cell count must be nonzero, with ceiling logarithm equal to the arity.

Then the claims must fit the budget. -/
def validate_opening_protocol (c : BinaryPcsConfig) (protocol : OpeningProtocol) :
    Except (BinaryPcsError F E) Unit :=
  match protocol.cells with
  | some total =>
    if total > 0 ∧ log2_ceil_usize total = c.num_variables then
      match protocol.claims with
      | none => .error .InvalidOpeningProtocol
      | some actual =>
        if actual > V.max_claims then
          .error (.OpeningClaimCountExceedsSecurityBudget actual V.max_claims c.params.security_level)
        else .ok ()
    else .error .InvalidOpeningProtocol
  | none => .error .InvalidOpeningProtocol

/-- The claim loop of the opening verifier: each batch's shape, then its claim recorded. -/
def addClaims (protocol : OpeningProtocol) (proof : BinaryPcsProof F EF ComX MPT MPX)
    (h : List (Step F EF)) : Option (Except (BinaryPcsError F E) (List (Step F EF))) :=
  (List.range protocol.openings.length).foldlM (fun acc i => match acc with
    | .error e => pure (.error e)
    | .ok h => do
      let (table_idx, cur, next) ← protocol.openings[i]?
      let (ec, en) ← proof.evals[i]?
      if cur ≠ ec.length ∨ next ≠ en.length then
        return .error (.OpeningBatchSizeMismatch table_idx cur next ec.length en.length)
      pure (match V.addClaim h i with
        | .error e => .error (.Sumcheck e)
        | .ok h => .ok h)) (.ok h)

/-- The state of the fold loop: the challenges so far, the running claim and the history. -/
abbrev FoldState (F EF : Type _) := List EF × EF × List (Step F EF)

/-- One fold round of the opening verifier.

It is a single sumcheck round, at zero difficulty, in the evaluation basis. -/
def foldRound (proof : BinaryPcsProof F EF ComX MPT MPX) (acc : Except (BinaryPcsError F E) (FoldState F EF))
    (r : ℕ) : Option (Except (BinaryPcsError F E) (FoldState F EF)) :=
  match acc with
  | .error e => pure (.error e)
  | .ok (betas, claimed, h) => do
    let ev ← proof.polynomial_evaluations[r]?
    pure (match verify_rounds V.S.toSponge [ev] [] h claimed 1 0 .Evaluation with
      | .error e => .error (.Sumcheck e)
      | .ok (point, claimed, h) => .ok (betas ++ [point.headD 0], claimed, h))

/-- One fold batch of the opening verifier.

It runs its rounds, then absorbs the root of its word unless it is the last. -/
def foldBatch (proof : BinaryPcsProof F EF ComX MPT MPX) (num_batches : ℕ)
    (acc : Except (BinaryPcsError F E) (FoldState F EF)) (b : ℕ × ℕ × ℕ) :
    Option (Except (BinaryPcsError F E) (FoldState F EF)) := do
  let (batch, start, arity) := b
  match ← (List.range' start arity).foldlM (foldRound V proof) acc with
  | .error e => pure (.error e)
  | .ok (betas, claimed, h) =>
    if batch + 1 < num_batches then do
      let r ← proof.rounds[batch]?
      pure (.ok (betas, claimed, h ++ [.message (V.enc r.commitment)]))
    else pure (.ok (betas, claimed, h))

/-- The opening verifier, in order:

- the protocol and shape checks
- the claims
- the batching challenge
- the fold rounds
- the final check
- the query paths.

It returns the claimed evaluations and the history the caller continues from. -/
def verify_opening (c : BinaryPcsConfig) (commitment : ComT) (proof : BinaryPcsProof F EF ComX MPT MPX)
    (protocol : OpeningProtocol) (h : List (Step F EF)) :
    Option (Except (BinaryPcsError F E) (List (List EF × List EF) × List (Step F EF))) := do
  match validate_opening_protocol V c protocol with
  | .error e => return .error e
  | .ok () =>
  if protocol.openings.length ≠ proof.evals.length then
    return .error (.OpeningBatchCountMismatch protocol.openings.length proof.evals.length)
  if proof.polynomial_evaluations.length ≠ c.num_fold_rounds then
    return .error (.Sumcheck (.RoundCountMismatch c.num_fold_rounds proof.polynomial_evaluations.length))
  if proof.pow_witnesses.length ≠ 0 then
    return .error (.NonEmptyPowWitnesses proof.pow_witnesses.length)
  match ← check_round_and_final_lengths c proof with
  | .error e => return .error e
  | .ok () =>
  match check_canonical_pow_witness c proof with
  | .error e => return .error e
  | .ok () =>
  match ← addClaims V protocol proof h with
  | .error e => return .error e
  | .ok h =>
  let s ← BinaryPcsShape.new c
  let h := h ++ [s.seed, V.layoutSeed]
  let alpha := V.S.sample h
  let h := h ++ [.challenge]
  let batches ← c.fold_batches
  let num_batches ← c.num_fold_batches
  match ← ((List.range batches.length).zip batches).foldlM
      (fun acc (b : ℕ × ℕ × ℕ) => foldBatch V proof num_batches acc b)
      (.ok ([], V.claimedSum alpha, h)) with
  | .error e => return .error e
  | .ok (betas, claimed, h) =>
  let final_value ← proof.final_codeword[0]?
  if ¬ (proof.final_codeword.all (· == final_value)) ∨ claimed ≠ V.weights alpha betas * final_value then
    return .error .FinalCheck
  match ← verify_query_paths V c commitment betas proof s h with
  | .error e => return .error e
  | .ok h => pure (.ok (proof.evals, h))

end Verifier

end p3_binary_pcs.verifier.mirror
