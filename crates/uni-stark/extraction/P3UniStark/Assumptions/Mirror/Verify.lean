/-
Transcription of the full verifier, from the proof's shape to the check at the out-of-domain point.

It does not extract.
It is generic over the configuration, the commitment scheme and the AIR, which aeneas rejects.

Each definition transcribes one Rust item, named in the crate's mirror entries.

What a transcription abstracts, beyond the other verifier transcriptions:

* the challenger is the FRI transcription's sponge, which the opening argument borrows
* the domain separator absorbs nothing, so a run starts from the state after it
* a commitment of the proof absorbs as one step, and so do the public values
* a challenge is one sample of the sponge, in the challenge field K
* the grinding witness is read through its embedding, as in the FRI transcription
* the opening argument is a parameter: the claims, the preprocessed round's index, and the state
* a machine word holds 64 bits
* the AIR's next-row reads are two flags
* a panic is none, and a rejection is an error value.

Loops, branches and the order of checks are kept.
-/
module

public import P3UniStark.Assumptions.Mirror.Verifier
public import P3UniStark.Assumptions.Mirror.Prover
public import P3UniStark.Assumptions.Mirror.Transcript
public import P3Fri

@[expose] public section

namespace p3_uni_stark.verify.mirror

open p3_air.builder.mirror p3_air.air.mirror p3_uni_stark.folder.mirror p3_uni_stark.verifier.mirror
open p3_uni_stark.prover.mirror p3_uni_stark.transcript.mirror
open p3_commit.domain.mirror p3_commit.periodic.mirror p3_commit.pcs.univariate.mirror
open p3_field.coset.mirror p3_dft.mirror p3_fri.verifier.mirror

/-- The bits of a machine word. -/
abbrev WORD_BITS : ℕ := 64

/-- The verifier key of a preprocessed trace: its width, its height in bits, and its commitment. -/
structure PreprocessedVerifierKey (C : Type) where
  width : ℕ
  degree_bits : ℕ
  commitment : C

/-- The preprocessed trace's opening: the current row, and the next row when present. -/
structure PreprocessedOpening (K : Type) where
  current : List K
  next : Option (List K)

/-- A proof. -/
structure Proof (C P F K : Type) where
  trace_commitment : C
  quotient_commitment : C
  random_commitment : Option C
  trace_local : List K
  trace_next : Option (List K)
  preprocessed : Option (PreprocessedOpening K)
  quotient_chunks : List (List K)
  random : Option (List K)
  opening_proof : P
  degree_bits : ℕ
  ood_pow_witness : F

/-- The numbers the configuration fixes.

* whether the scheme is hiding
* the smallest and largest trace heights the scheme accepts, in bits
* the grinding difficulty before the out-of-domain point
* the degree D of the challenge field over the base field. -/
structure Config where
  zk : Bool
  log_min_trace_height : ℕ
  log_max_trace_height : ℕ
  ood_pow_bits : ℕ
  D : ℕ

/-- The challenger operations the STARK adds to the FRI sponge. -/
structure StarkSponge (F K C Com S : Type) where
  sponge : p3_fri.transcript.mirror.Sponge K Com S
  observe_commitment : S → C → S
  observe_public_values : S → List F → S

/-- The degree-bits validation.

It returns the base domain's bits b - z and the extended domain's size 2^b. -/
def validate_degree_bits (degree_bits is_zk min_log_degree max_log_degree : ℕ) :
    Except InvalidProofShapeError (ℕ × ℕ) :=
  if degree_bits < is_zk + min_log_degree then throw .DegreeBitsTooSmall
  else if max_log_degree < degree_bits then throw .DegreeBitsTooLarge
  else if WORD_BITS ≤ degree_bits then throw .DegreeBitsTooLarge
  else pure (degree_bits - is_zk, 2 ^ degree_bits)

/-- The sum of two sizes in bits, with its power of two, when the power fits a word. -/
def checked_log_size_sum (a b : ℕ) : Option (ℕ × ℕ) :=
  if WORD_BITS ≤ a + b then none else some (a + b, 2 ^ (a + b))

section domains

variable {K : Type} [Field K] [DecidableEq K] (G : Gen K)

/-- The scheme's domain for a degree: the subgroup of that order.

The order must be a power of two the table covers. -/
def natural_domain_for_degree (degree : ℕ) : Option (Coset G) := do
  let l ← log2Strict degree
  TwoAdicMultiplicativeCoset.new 1 l

end domains

/-- The preprocessed trace's checks.

The width in force is the key's when one is supplied, and the AIR's otherwise.

* An opening is present exactly when that width is positive, as wide as it.
* Its next row is present exactly when the AIR reads it, with the same width.
* A key is supplied exactly when the width is positive, and declares that width.

It returns the width, and the key's commitment with the opening it binds. -/
def process_preprocessed_trace {C K : Type} (air_preprocessed_width : ℕ) (preprocessed_next_used : Bool)
    (opened : Option (PreprocessedOpening K)) (vk : Option (PreprocessedVerifierKey C)) :
    Except VerificationError (ℕ × Option (C × PreprocessedOpening K)) := do
  let preprocessed_width := (vk.map (·.width)).getD air_preprocessed_width
  let preprocessed ← match opened with
    | some p =>
      if preprocessed_width = 0 then
        throw (.InvalidProofShape .UnexpectedPreprocessedValues)
      else
        let expected_next_len := if preprocessed_next_used then preprocessed_width else 0
        let got_next := (p.next.map List.length).getD 0
        if p.current.length ≠ preprocessed_width ∨ got_next ≠ expected_next_len then
          throw (.InvalidProofShape .PreprocessedTraceWidthMismatch)
        else if !preprocessed_next_used ∧ p.next.isSome then
          throw (.InvalidProofShape .UnexpectedPreprocessedNext)
        else pure (some p)
    | none =>
      if preprocessed_width > 0 then throw (.InvalidProofShape .PreprocessedTraceWidthMismatch)
      else pure none
  match preprocessed_width, vk with
  | 0, none => pure (0, none)
  | w, some key =>
    if w = key.width then pure (w, preprocessed.map fun p => (key.commitment, p))
    else throw (.InvalidProofShape .PreprocessedVerifierKeyInconsistency)
  | _, none => throw (.InvalidProofShape .PreprocessedVerifierKeyInconsistency)

/-- A transcript failure, as the verifier reports it. -/
def ofTranscriptFailure : StarkTranscriptFailure → VerificationError
  | .MissingPreprocessedCommitment | .UnexpectedPreprocessedCommitment =>
    .InvalidProofShape .PreprocessedVerifierKeyInconsistency
  | .MissingRandomCommitment | .UnexpectedRandomCommitment => .RandomizationError
  | .OodPowWitness => .InvalidOodPowWitness

section phases

variable {F K C Com S : Type} [Field F] [Field K] [Algebra F K]

/-- The first phase, over the sponge.

It absorbs the trace commitment, the preprocessed commitment when described, and the public values.
It then draws alpha. -/
def constraint_phase (sp : StarkSponge F K C Com S) (preprocessed_width : ℕ) (s : S) (trace : C)
    (preprocessed : Option C) (public_values : List F) : Except StarkTranscriptFailure (K × S) := do
  let s := sp.observe_commitment s trace
  let s ← match decide (preprocessed_width > 0), preprocessed with
    | true, some c => pure (sp.observe_commitment s c)
    | false, none => pure s
    | true, none => throw .MissingPreprocessedCommitment
    | false, some _ => throw .UnexpectedPreprocessedCommitment
  pure (sp.sponge.sample (sp.observe_public_values s public_values))

/-- The second phase, over the sponge.

It absorbs the quotient commitment, and the randomization commitment when described.
It checks the grind when it has bits, then draws zeta.

The grind panics at a difficulty the field cannot sample. -/
def ood_phase (sp : StarkSponge F K C Com S) (has_randomization : Bool) (ood_pow_bits : ℕ) (s : S)
    (quotient : C) (random : Option C) (witness : F) : ExceptT StarkTranscriptFailure Option (K × S) := do
  let s := sp.observe_commitment s quotient
  let s ← match has_randomization, random with
    | true, some c => pure (sp.observe_commitment s c)
    | false, none => pure s
    | true, none => throw .MissingRandomCommitment
    | false, some _ => throw .UnexpectedRandomCommitment
  let s ← if ood_pow_bits > 0 then do
      let (ok, s') ← ExceptT.lift
        (p3_fri.transcript.mirror.check_witness sp.sponge s ood_pow_bits (algebraMap F K witness))
      if ok then pure s' else throw .OodPowWitness
    else pure s
  pure (sp.sponge.sample s)

end phases

section claims

variable {F K C P : Type} [Field F] [DecidableEq F] [Field K] [DecidableEq K] [Algebra F K] (G : Gen K)

/-- The claims at zeta, in round order.

* the randomization round, when present, at zeta
* the trace at zeta, and at the next point when the AIR reads the next row
* one matrix per quotient chunk, on its randomized domain, at zeta
* the preprocessed trace at zeta, and at the next point when its next row is present. -/
def opening_claims (opens_main_next : Bool) (proof : Proof C P F K) (random_values : Option (List K))
    (trace_next : List K) (preprocessed : Option (C × PreprocessedOpening K)) (trace_domain : Coset G)
    (randomized_quotient_chunks_domains : List (Coset G)) (zeta zeta_next : K) :
    List (p3_fri.verifier.mirror.Claim G C) :=
  (match proof.random_commitment, random_values with
    | some rc, some rv => [⟨rc, [⟨trace_domain, [⟨zeta, rv⟩]⟩]⟩]
    | _, _ => []) ++
  [⟨proof.trace_commitment, [⟨trace_domain, [⟨zeta, proof.trace_local⟩] ++
      (if opens_main_next then [⟨zeta_next, trace_next⟩] else [])⟩]⟩,
    ⟨proof.quotient_commitment, (randomized_quotient_chunks_domains.zip proof.quotient_chunks).map
      fun dv => ⟨dv.1, [⟨zeta, dv.2⟩]⟩⟩] ++
  (match preprocessed with
    | some (c, p) => [⟨c, [⟨trace_domain, [⟨zeta, p.current⟩] ++
        (match p.next with | some n => [⟨zeta_next, n⟩] | none => [])⟩]⟩]
    | none => [])

/-- The periodic values at zeta and the claims the opening argument answers.

* zeta on the base trace domain is rejected first
* a periodic column whose length is not a power of two dividing the height is rejected
* a missing randomization opening under a randomization commitment is rejected
* the quotient openings must pair one for one with the chunk domains
* a missing next row of the trace panics, as Rust's unwrap does. -/
def prepare_opening_claims (air : Air F) (opens_main_next : Bool) (proof : Proof C P F K)
    (preprocessed : Option (C × PreprocessedOpening K)) (trace_domain init_trace_domain : Coset G)
    (randomized_quotient_chunks_domains : List (Coset G)) (zeta : K) :
    Option (Except VerificationError (List K × List (p3_fri.verifier.mirror.Claim G C))) := do
  match check_ood_point G init_trace_domain zeta with
  | .error e => return .error e
  | .ok () =>
  match PeriodicColumns.new (air.periodic_columns.map (·.map (algebraMap F K)))
      (Coset.size G init_trace_domain) with
  | .error _ => return .error .PeriodicColumn
  | .ok periodic_columns =>
  let periodic_values ← Coset.evaluate_periodic_columns_at G init_trace_domain
    periodic_columns.columns periodic_columns.height zeta
  match Coset.next_point G init_trace_domain zeta with
  | none => return .error .NextPointUnavailable
  | some zeta_next =>
  if proof.random_commitment.isSome ∧ proof.random.isNone then return .error .RandomizationError
  let trace_next ← if opens_main_next then proof.trace_next else pure []
  if randomized_quotient_chunks_domains.length ≠ proof.quotient_chunks.length then
    return .error (.InvalidProofShape .QuotientDomainsCountMismatch)
  pure (.ok (periodic_values, opening_claims G opens_main_next proof proof.random trace_next
    preprocessed trace_domain randomized_quotient_chunks_domains zeta zeta_next))

end claims

variable {F K C Com S P PE : Type} [Field F] [DecidableEq F] [Field K] [DecidableEq K] [Algebra F K]

/-- The verifier, in Rust's order.

* the boundary assertion, the height validation, the trace domain
* the preprocessed checks and the key's height
* the quotient sizing, the chunk count, and the quotient and chunk domains
* the proof's shape checks
* the transcript: alpha, the grind, zeta
* the claims at zeta and the opening argument, run inside the transcript's bracket
* the chunk recombination and the check at zeta.

The opening argument receives the claims, the preprocessed round's index and the sponge's state.

The arguments are:

* the generator table, the field generator g, and a basis of K over F
* the configuration, the AIR, and the AIR's two next-row flags
* the sponge and the opening argument
* the proof, the public values, the optional verifier key, and the sponge's starting state. -/
noncomputable def verify_with_preprocessed {D : ℕ} (G : Gen K) (g : K) (B : Module.Basis (Fin D) F K) (cfg : Config)
    (air : Air F) (opens_main_next opens_preprocessed_next : Bool) (sp : StarkSponge F K C Com S)
    (pcs : List (p3_fri.verifier.mirror.Claim G C) → Option ℕ → S → Option (Except PE Unit))
    (proof : Proof C P F K) (public_values : List F) (vk : Option (PreprocessedVerifierKey C))
    (s0 : S) : Option (Except VerificationError Unit) := do
  if air.public_boundary_io ≠ [] then none
  let is_zk := cfg.zk.toNat
  match validate_degree_bits proof.degree_bits is_zk cfg.log_min_trace_height
      cfg.log_max_trace_height with
  | .error e => return .error (.InvalidProofShape e)
  | .ok (base_degree_bits, degree) =>
  let trace_domain ← natural_domain_for_degree G degree
  match process_preprocessed_trace air.preprocessed_width opens_preprocessed_next proof.preprocessed vk with
  | .error e => return .error e
  | .ok (preprocessed_width, preprocessed) =>
  if (vk.map fun key => decide (preprocessed_width > 0 ∧ key.degree_bits ≠ proof.degree_bits)).getD false then
    return .error (.InvalidProofShape .PreprocessedDegreeMismatch)
  let layout : AirLayout :=
    { preprocessed_width := preprocessed_width
      main_width := air.width
      num_public_values := air.num_public_values
      num_periodic_columns := air.num_periodic_columns }
  let base_domain ← natural_domain_for_degree G (2 ^ base_degree_bits)
  let log_num_quotient_chunks ← (get_log_num_quotient_chunks_for_domain air layout
    (Coset.size G base_domain) is_zk).toOption
  match checked_log_size_sum log_num_quotient_chunks is_zk with
  | none => return .error (.InvalidProofShape .QuotientDomainTooLarge)
  | some (_, num_quotient_chunks) =>
  let init_trace_domain ← natural_domain_for_degree G (degree / 2 ^ is_zk)
  match checked_log_size_sum proof.degree_bits log_num_quotient_chunks with
  | none => return .error (.InvalidProofShape .QuotientDomainTooLarge)
  | some (_, quotient_domain_size) =>
  match Coset.try_create_disjoint_domain G trace_domain g quotient_domain_size with
  | none => return .error (.InvalidProofShape .QuotientDomainTooLarge)
  | some quotient_domain =>
  let quotient_chunks_domains ← Coset.split_domains G quotient_domain num_quotient_chunks
  let randomized_quotient_chunks_domains ← quotient_chunks_domains.mapM fun d =>
    natural_domain_for_degree G (Coset.size G d * 2 ^ is_zk)
  match check_shape air opens_main_next cfg.zk cfg.D num_quotient_chunks cfg.ood_pow_bits public_values
      proof.trace_local proof.trace_next proof.quotient_chunks proof.random
      proof.random_commitment.isSome proof.ood_pow_witness with
  | .error e => return .error e
  | .ok () =>
  let preprocessed_index := preprocessed.map fun _ => is_zk + 2
  match constraint_phase sp preprocessed_width s0 proof.trace_commitment (preprocessed.map (·.1))
      public_values with
  | .error f => return .error (ofTranscriptFailure f)
  | .ok (alpha, s1) =>
  match ← (ood_phase sp cfg.zk cfg.ood_pow_bits s1 proof.quotient_commitment proof.random_commitment
      proof.ood_pow_witness).run with
  | .error f => return .error (ofTranscriptFailure f)
  | .ok (zeta, s2) =>
  match ← prepare_opening_claims G air opens_main_next proof preprocessed trace_domain init_trace_domain
      randomized_quotient_chunks_domains zeta with
  | .error e => return .error e
  | .ok (periodic_values, claims) =>
  match ← pcs claims preprocessed_index s2 with
  | .error _ => return .error .InvalidOpeningArgument
  | .ok () =>
  let quotient ← recompose_quotient_from_chunks G B quotient_chunks_domains proof.quotient_chunks zeta
  let trace_next := proof.trace_next.getD (List.replicate air.width 0)
  let preprocessed_next := match proof.preprocessed.bind (·.next) with
    | some v => some v
    | none => if preprocessed_width > 0 then some (List.replicate preprocessed_width 0) else none
  verify_constraints G air proof.trace_local trace_next (proof.preprocessed.map (·.current))
    preprocessed_next periodic_values public_values init_trace_domain zeta alpha quotient

end p3_uni_stark.verify.mirror
