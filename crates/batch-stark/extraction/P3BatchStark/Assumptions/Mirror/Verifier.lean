/-
Transcriptions of the batch verifier: its shape checks, its transcript replay, the panicking reads of its opening argument, and its final checks.

These do not extract: they are generic over the configuration, the field traits and the AIR, which aeneas rejects.

Each definition transcribes one Rust item, named in the crate's mirror entries.

What a transcription abstracts, beyond the transcript transcriptions:

* an AIR is the numbers and flags the verifier reads from it, and its quotient sizing as a function of the base degree bits;
* the configuration is the hiding flag, the extension degree, the trace-height bounds, the word size, the characteristic and the two difficulties;
* the opening argument is a predicate on the commitments, the points and the claimed values;
* each instance's constraint check at zeta is a function of the instance's openings, its challenges, alpha and zeta;
* a hash map is a list, an error carries the instance index where Rust reports one, and a panic is none.

Loops, branches and the order of checks are kept.
-/
module

public import P3BatchStark.Assumptions.Mirror.Transcript

@[expose] public section

namespace p3_batch_stark.verifier.mirror

open p3_lookup.mirror p3_batch_stark.transcript.mirror

/-- What the verifier reads from one AIR. -/
structure AirInfo where
  width : ℕ
  num_public_values : ℕ
  reads_main_next : Bool
  reads_preprocessed_next : Bool
  boundary_io_empty : Bool
  log_num_quotient_chunks : ℕ → ℕ

instance : Inhabited AirInfo := ⟨⟨0, 0, false, false, true, fun _ => 0⟩⟩

/-- What the verifier reads from the configuration. -/
structure Config where
  zk : Bool
  dimension : ℕ
  log_min_trace_height : ℕ
  log_max_trace_height : ℕ
  word_bits : ℕ
  characteristic : ℕ
  lookup_pow_bits : ℕ
  ood_pow_bits : ℕ

/-- The hiding flag as the number 0 or 1. -/
def Config.is_zk (c : Config) : ℕ := c.zk.toNat

/-- The keygen-cached data: the preprocessed width and degree bits of each instance under the global preprocessed commitment, and each instance's lookups. -/
structure CommonData (C F : Type) where
  preprocessed : Option (C × List (Option (ℕ × ℕ)))
  lookups : List (List (Lookup F))

/-- One instance's opened values. -/
structure Opened (K : Type) where
  trace_local : List K
  trace_next : Option (List K)
  preprocessed : Option (List K × Option (List K))
  quotient_chunks : List (List K)
  random : Option (List K)
  permutation_local : List K
  permutation_next : List K

instance {K : Type} : Inhabited (Opened K) := ⟨⟨[], none, none, [], none, [], []⟩⟩

/-- A batch proof. -/
structure BatchProof (C F K : Type) where
  main : C
  permutation : Option C
  quotient_chunks : C
  random : Option C
  opened : List (Opened K)
  lookup_terminals : List (Option K)
  degree_bits : List ℕ
  lookup_pow_witness : Option F
  ood_pow_witness : F

/-- Why a batch proof is rejected. -/
inductive BatchError where
  | InstanceCountMismatch
  | RandomizationError
  | DegreeBitsTooSmall (air : ℕ)
  | DegreeBitsTooLarge (air : ℕ)
  | QuotientDomainTooLarge (air : ℕ)
  | MultiplicityHeightBound (sum : ℕ)
  | PublicValuesLengthMismatch
  | TraceLocalWidthMismatch (air : ℕ)
  | TraceNextMismatch (air : ℕ)
  | UnexpectedTraceNext (air : ℕ)
  | QuotientChunksCountMismatch (air : ℕ)
  | QuotientChunkDimensionMismatch (air : ℕ)
  | UnexpectedPreprocessedValues (air : ℕ)
  | PreprocessedWidthMismatch (air : ℕ)
  | UnexpectedPreprocessedNext (air : ℕ)
  | PermutationWidthMismatch (air : ℕ)
  | TerminalPresenceMismatch (air : ℕ)
  | CommitmentMismatch
  | Transcript (e : BatchTranscriptFailure)
  | InvalidOpeningArgument
  | Constraint (air : ℕ)
  | TerminalSum
  deriving DecidableEq

/-- `validate_degree_bits`: the bits within the bounds and below the word size, as the base bits and the extended size. -/
def validate_degree_bits (cfg : Config) (air db : ℕ) : Except BatchError (ℕ × ℕ) :=
  if db < cfg.is_zk + cfg.log_min_trace_height then .error (.DegreeBitsTooSmall air)
  else if cfg.log_max_trace_height < db then .error (.DegreeBitsTooLarge air)
  else if cfg.word_bits ≤ db then .error (.DegreeBitsTooLarge air)
  else .ok (db - cfg.is_zk, 2 ^ db)

/-- The preprocessed width of an instance, zero without preprocessed columns. -/
def preprocessedWidth {C F : Type} (common : CommonData C F) (i : ℕ) : ℕ :=
  ((common.preprocessed.bind fun g => g.2[i]?.join).map (·.1)).getD 0

/-- What the shape checks hand on: the base degree bits, the committed chunk counts, the preprocessed widths and the number of instances with lookups. -/
structure Checked where
  base_degree_bits : List ℕ
  log_num_quotient_chunks : List ℕ
  num_quotient_chunks : List ℕ
  preprocessed_widths : List ℕ
  num_lookup_instances : ℕ

variable {C F K : Type}

/-- A check: pass when the condition holds, reject with the error otherwise. -/
def ensure (c : Prop) [Decidable c] (e : BatchError) : Except BatchError Unit :=
  if c then pure () else throw e

/-- The height bound's outcome as a check: a weighted sum at or above the characteristic rejects. -/
def heightResult : Option (Except ℕ Unit) → Except BatchError Unit
  | some (.error s) => throw (.MultiplicityHeightBound s)
  | _ => pure ()

/-- The checks on one instance's openings, in the verifier's order. -/
def check_instance (cfg : Config) (common : CommonData C F) (air : AirInfo) (i : ℕ) (pv : List F)
    (ov : Opened K) (terminal : Option K) (n_chunks : ℕ) : Except BatchError Unit := do
  ensure (pv.length = air.num_public_values) .PublicValuesLengthMismatch
  ensure (ov.trace_local.length = air.width) (.TraceLocalWidthMismatch i)
  if air.reads_main_next then
    ensure ((ov.trace_next.map fun v => decide (v.length = air.width)).getD false) (.TraceNextMismatch i)
  else ensure (ov.trace_next = none) (.UnexpectedTraceNext i)
  ensure (ov.quotient_chunks.length = n_chunks) (.QuotientChunksCountMismatch i)
  ensure (∀ q ∈ ov.quotient_chunks, q.length = cfg.dimension) (.QuotientChunkDimensionMismatch i)
  ensure (∀ r ∈ ov.random, r.length = cfg.dimension) .RandomizationError
  let pre_w := preprocessedWidth common i
  match ov.preprocessed with
  | some (loc, next) => do
    ensure (pre_w ≠ 0) (.UnexpectedPreprocessedValues i)
    ensure (loc.length = pre_w ∧
      (next.map List.length).getD 0 = if air.reads_preprocessed_next then pre_w else 0)
      (.PreprocessedWidthMismatch i)
    ensure (air.reads_preprocessed_next ∨ next = none) (.UnexpectedPreprocessedNext i)
  | none => ensure (pre_w = 0) (.PreprocessedWidthMismatch i)
  let lookups := common.lookups.getD i []
  let expected_perm_len := if lookups.isEmpty then 0 else (lookups.length + 1) * cfg.dimension
  ensure (ov.permutation_local.length = expected_perm_len ∧ ov.permutation_next.length = expected_perm_len)
    (.PermutationWidthMismatch i)
  ensure (terminal.isSome = !lookups.isEmpty) (.TerminalPresenceMismatch i)

/-- The shape checks of `verify_batch`, before any transcript work: counts, randomization, degree bits and chunk counts, the height bound, each instance's openings, and the permutation commitment. -/
def check_shape (cfg : Config) (airs : List AirInfo) (proof : BatchProof C F K)
    (public_values : List (List F)) (common : CommonData C F) : Except BatchError Checked := do
  let n := airs.length
  ensure (proof.opened.length = n ∧ public_values.length = n ∧ proof.degree_bits.length = n ∧
      proof.lookup_terminals.length = n ∧ common.lookups.length = n ∧
      ∀ g ∈ common.preprocessed, g.2.length = n) .InstanceCountMismatch
  ensure ((∀ ov ∈ proof.opened, ov.random.isSome = cfg.zk) ∧ proof.random.isSome = cfg.zk)
    .RandomizationError
  let sizes ← (List.range n).mapM fun i => do
    let (base_db, _) ← validate_degree_bits cfg i (proof.degree_bits.getD i 0)
    let log_chunks := (airs.getD i default).log_num_quotient_chunks base_db
    ensure (log_chunks + cfg.is_zk < cfg.word_bits) (.QuotientDomainTooLarge i)
    pure (base_db, log_chunks, 2 ^ (log_chunks + cfg.is_zk))
  let base := sizes.map (·.1)
  -- The lengths agree after the count check, so the bound's panic is unreachable here.
  heightResult (check_multiplicity_height_bound cfg.characteristic common.lookups (base.map (2 ^ ·)))
  (List.range n).forM fun i =>
    check_instance cfg common (airs.getD i default) i
      (public_values.getD i []) (proof.opened.getD i default)
      (proof.lookup_terminals.getD i none) ((sizes.map (·.2.2)).getD i 0)
  let k := (common.lookups.filter (!·.isEmpty)).length
  ensure (proof.permutation.isSome = decide (k > 0)) .CommitmentMismatch
  pure ⟨base, sizes.map (·.2.1), sizes.map (·.2.2), (List.range n).map (preprocessedWidth common), k⟩

/-- The transcript shape the verifier builds from the AIRs, the common data and the configuration. -/
def shapeOf (cfg : Config) (airs : List AirInfo) (common : CommonData C F) (checked : Checked) :
    BatchShape :=
  ⟨airs.map (·.width), airs.map (·.num_public_values), checked.preprocessed_widths,
    common.preprocessed.isSome, checked.num_lookup_instances, cfg.lookup_pow_bits, cfg.zk, cfg.ood_pow_bits⟩

/-- The transcript replay of `verify_batch`: none on a panic of the layout, then the state reached and the challenges or the rejection.

The two grind rejections stop the replay. -/
def replay [Zero F] [DecidableEq F] [Field K] (cfg : Config) (airs : List AirInfo)
    (proof : BatchProof C F K) (public_values : List (List F)) (common : CommonData C F)
    (checked : Checked) (H : List (Msg C F K) → K) (powOk : List (Msg C F K) → ℕ → F → Bool) :
    Option (St C F K × Except BatchError (List (List K) × K × K)) := do
  let shape := shapeOf cfg airs common checked
  let st := new shape
  let st := instance_bindings st proof.degree_bits
  let st := main_phase st proof.main public_values
  let st := preprocessed_phase st (common.preprocessed.map (·.1))
  let (st, r) ← lookup_phase shape H powOk 2 st common.lookups proof.lookup_pow_witness
  match r with
  | .error e => pure (st, .error (.Transcript e))
  | .ok challenges =>
    let (st, alpha) := permutation_phase H st proof.permutation (proof.lookup_terminals.filterMap id)
    let st := quotient_phase st proof.quotient_chunks proof.random
    let (st, r) := ood_phase shape H powOk st proof.ood_pow_witness
    match r with
    | .error e => pure (st, .error (.Transcript e))
    | .ok zeta => pure (delegate st, .ok (challenges, alpha, zeta))

/-- The reads of the opening argument that Rust unwraps: each instance's next row when its AIR reads it, and its randomization opening under a randomization commitment.

The permutation round lists the instances with a nonempty permutation opening, in order. -/
def opening_reads (airs : List AirInfo) (proof : BatchProof C F K) :
    Option (List (Option (List K)) × List (List K) × List ℕ) := do
  let nexts ← (List.range airs.length).mapM fun i =>
    if (airs.getD i default).reads_main_next then
      (proof.opened.getD i default).trace_next.map some
    else some none
  let randoms ← if proof.random.isSome then
      (List.range airs.length).mapM fun i => (proof.opened.getD i default).random
    else some []
  let perm := (List.range airs.length).filter fun i =>
    !(proof.opened.getD i default).permutation_local.isEmpty
  pure (nexts, randoms, perm)

/-- `verify_batch`: the boundary assertion, the shape checks, the replay, the opening argument, each instance's check at zeta with the shared alpha, and the cross-table terminal sum.

A panic is none. -/
def verify_batch [Zero F] [DecidableEq F] [Field K] [DecidableEq K] (cfg : Config) (airs : List AirInfo)
    (proof : BatchProof C F K) (public_values : List (List F)) (common : CommonData C F)
    (H : List (Msg C F K) → K) (powOk : List (Msg C F K) → ℕ → F → Bool)
    (pcsOk : List (Msg C F K) → K → Bool)
    (checkAt : ℕ → List K → K → K → Except BatchError Unit) : Option (Except BatchError Unit) := do
  if ¬ airs.all (·.boundary_io_empty) then none
  match check_shape cfg airs proof public_values common with
  | .error e => pure (.error e)
  | .ok checked =>
    let (st, r) ← replay cfg airs proof public_values common checked H powOk
    match r with
    | .error e => pure (.error e)
    | .ok (challenges, alpha, zeta) =>
      let _ ← opening_reads airs proof
      if ¬ pcsOk st.msgs zeta then return .error .InvalidOpeningArgument
      match (List.range airs.length).forM fun i => checkAt i (challenges.getD i []) alpha zeta with
      | .error e => return .error e
      | .ok () => pure ()
      if ¬ verify_terminal_sum proof.lookup_terminals then return .error .TerminalSum
      pure (.ok ())

end p3_batch_stark.verifier.mirror
