/-
Transcription of the full batch verifier, from the proof's shape to the cross-table sum.

It does not extract.
It is generic over the configuration, the commitment scheme and the AIRs, which aeneas rejects.

Each definition transcribes one Rust item, named in the crate's mirror entries.

What a transcription abstracts, beyond the other verifier transcriptions:

* the challenger is the FRI transcription's sponge, which the opening argument borrows
* the domain separator is absorbed by a seed function of the shape
* a commitment, an extension element and a list of public values each absorb as one step
* a challenge is one sample of the sponge, in the challenge field K
* a grinding witness is read through its embedding, as in the FRI transcription
* the pattern bookkeeping is the message-list transcription's, which plays the whole pattern
* the quotient sizing with lookups is a parameter, a function of the instance and its layout
* the opening argument is a parameter: the claims, the preprocessed round's index, and the state
* a machine word holds 64 bits
* an AIR's next-row reads are two flags
* a panic is none, and a rejection is an error value.

Loops, branches and the order of checks are kept.
-/
module

public import P3BatchStark.Assumptions.Mirror.Transcript
public import P3BatchStark.Assumptions.Mirror.Constraints
public import P3UniStark.Assumptions.Mirror.Verify

@[expose] public section

namespace p3_batch_stark.verify.mirror

open p3_air.air.mirror p3_lookup.mirror p3_uni_stark.verifier.mirror p3_uni_stark.verify.mirror
open p3_batch_stark.transcript.mirror p3_batch_stark.constraints.mirror
open p3_commit.domain.mirror p3_commit.periodic.mirror p3_commit.pcs.univariate.mirror
open p3_field.coset.mirror p3_dft.mirror

/-! ## Data -/

/-- An AIR of the batch, with its two next-row flags. -/
structure BatchAir (F : Type) where
  air : Air F
  opens_main_next : Bool
  opens_preprocessed_next : Bool

/-- Where an instance's preprocessed trace sits in the global commitment, and its size. -/
structure PreprocessedMeta where
  matrix_index : ℕ
  width : ℕ
  degree_bits : ℕ

/-- The global preprocessed commitment, its per-instance metadata, and its matrices' instances. -/
structure GlobalPreprocessed (C : Type) where
  commitment : C
  instances : List (Option PreprocessedMeta)
  matrix_to_instance : List ℕ

/-- The keygen-cached data: the global preprocessed commitment and each instance's lookups. -/
structure CommonData (C F : Type) where
  preprocessed : Option (GlobalPreprocessed C)
  lookups : List (List (Lookup F))

/-- One instance's opened values. -/
structure Opened (K : Type) where
  trace_local : List K
  trace_next : Option (List K)
  preprocessed : Option (PreprocessedOpening K)
  quotient_chunks : List (List K)
  random : Option (List K)
  permutation_local : List K
  permutation_next : List K

/-- A batch proof. -/
structure BatchProof (C P F K : Type) where
  main : C
  permutation : Option C
  quotient_chunks : C
  random : Option C
  opened : List (Opened K)
  opening_proof : P
  lookup_terminals : List (Option K)
  degree_bits : List ℕ
  lookup_pow_witness : Option F
  ood_pow_witness : F

/-- The numbers the configuration fixes.

* whether the scheme is hiding
* the smallest and largest trace heights, in bits
* the two grinding difficulties
* the degree D of the challenge field over the base field
* the characteristic p of the base field. -/
structure Config where
  zk : Bool
  log_min_trace_height : ℕ
  log_max_trace_height : ℕ
  lookup_pow_bits : ℕ
  ood_pow_bits : ℕ
  D : ℕ
  characteristic : ℕ

/-- Why a proof's shape is rejected, with the instance where Rust reports one. -/
inductive ShapeError where
  | InstanceCountMismatch
  | DegreeBitsTooSmall (air : ℕ)
  | DegreeBitsTooLarge (air : ℕ)
  | QuotientDomainTooLarge (air : ℕ)
  | PublicValuesLengthMismatch
  | TraceLocalWidthMismatch (air : ℕ)
  | TraceNextMismatch (air : ℕ)
  | UnexpectedTraceNext (air : ℕ)
  | QuotientChunksCountMismatch (air : ℕ)
  | QuotientChunkDimensionMismatch (air : ℕ)
  | UnexpectedPreprocessedValues (air : ℕ)
  | PreprocessedWidthMismatch (air : ℕ)
  | UnexpectedPreprocessedNext (air : ℕ)
  | QuotientDomainsCountMismatch (air : ℕ)
  | PreprocessedMetadataMismatch (air : ℕ)
  | MissingPreprocessedValues (air : ℕ)
  deriving DecidableEq

/-- Why the lookup argument rejects a proof. -/
inductive LookupFailure where
  | MultiplicityHeightBound (sum : ℕ)
  | PermutationWidthMismatch (air : ℕ)
  | PermutationLengthMismatch (air : ℕ)
  | TerminalPresenceMismatch (air : ℕ)
  | CommitmentMismatch
  | TerminalSum
  deriving DecidableEq

/-- Why the batch verifier rejects a proof. -/
inductive Error where
  | Verification (e : VerificationError)
  | Shape (e : ShapeError)
  | OodEvaluationMismatch (air : ℕ)
  | Lookup (e : LookupFailure)
  | Transcript (e : BatchTranscriptFailure)
  deriving DecidableEq

/-- The verifier's monad: a panic is none, a rejection an error. -/
abbrev M := ExceptT Error Option

/-- A read that panics when absent. -/
def panicOf {α : Type} (o : Option α) : M α := ExceptT.lift o

/-- A check: pass when the condition holds, reject with the error otherwise. -/
def ensure (c : Prop) [Decidable c] (e : Error) : Except Error Unit :=
  if c then pure () else throw e

/-- The degree-bits validation of instance i. -/
def validate_degree_bits_at (cfg : Config) (i db : ℕ) : Except Error (ℕ × ℕ) :=
  match validate_degree_bits db cfg.zk.toNat cfg.log_min_trace_height cfg.log_max_trace_height with
  | .ok r => .ok r
  | .error .DegreeBitsTooSmall => .error (.Shape (.DegreeBitsTooSmall i))
  | .error _ => .error (.Shape (.DegreeBitsTooLarge i))

/-! ## The shape checks -/

/-- What the first loop computes for one instance:

* the base degree bits and the extended domain's size
* the preprocessed width from the common data
* the quotient sizing, and the committed chunk count. -/
structure Sizes where
  base_degree_bits : ℕ
  ext_size : ℕ
  preprocessed_width : ℕ
  log_num_quotient_chunks : ℕ
  num_quotient_chunks : ℕ

section shape

variable {K : Type} [Field K] [DecidableEq K] (G : Gen K)
variable {C P F : Type} [Field F] [DecidableEq F]

/-- The preprocessed width of instance i, zero without preprocessed columns. -/
def preprocessed_width (common : CommonData C F) (i : ℕ) : M ℕ :=
  match common.preprocessed with
  | none => pure 0
  | some g => do
    let m ← panicOf g.instances[i]?
    pure ((m.map (·.width)).getD 0)

/-- The first loop on instance i: the degree bits, the preprocessed width and the quotient sizing.

The sizing receives the instance, its layout and the size of its base domain. -/
def instance_sizes (cfg : Config) (common : CommonData C F) (sizing : ℕ → AirLayout → ℕ → Option ℕ)
    (degree_bits : List ℕ) (ba : BatchAir F) (i : ℕ) : M Sizes := do
  let db ← panicOf degree_bits[i]?
  let (base_db, ext_size) ← ExceptT.mk (some (validate_degree_bits_at cfg i db))
  let pre_w ← preprocessed_width common i
  let layout : AirLayout :=
    { preprocessed_width := pre_w
      main_width := ba.air.width
      num_public_values := ba.air.num_public_values
      num_periodic_columns := ba.air.num_periodic_columns }
  let base_domain ← panicOf (natural_domain_for_degree G (2 ^ base_db))
  let log_chunks ← panicOf (sizing i layout (Coset.size G base_domain))
  match checked_log_size_sum log_chunks cfg.zk.toNat with
  | none => throw (.Shape (.QuotientDomainTooLarge i))
  | some (_, n_chunks) => pure ⟨base_db, ext_size, pre_w, log_chunks, n_chunks⟩

/-- The checks on instance i's openings, in the verifier's order. -/
def check_instance {K : Type} (cfg : Config) (ba : BatchAir F) (i : ℕ) (pv : List F) (ov : Opened K)
    (sz : Sizes) (lookups : List (Lookup F)) (terminal : Option K) : Except Error Unit := do
  ensure (pv.length = ba.air.num_public_values) (.Shape .PublicValuesLengthMismatch)
  ensure (ov.trace_local.length = ba.air.width) (.Shape (.TraceLocalWidthMismatch i))
  if ba.opens_main_next then
    ensure ((ov.trace_next.map fun v => decide (v.length = ba.air.width)).getD false)
      (.Shape (.TraceNextMismatch i))
  else ensure (ov.trace_next = none) (.Shape (.UnexpectedTraceNext i))
  ensure (ov.quotient_chunks.length = sz.num_quotient_chunks) (.Shape (.QuotientChunksCountMismatch i))
  ensure (∀ q ∈ ov.quotient_chunks, q.length = cfg.D) (.Shape (.QuotientChunkDimensionMismatch i))
  ensure (∀ r ∈ ov.random, r.length = cfg.D) (.Verification .RandomizationError)
  let pre_w := sz.preprocessed_width
  match ov.preprocessed with
  | some p => do
    ensure (pre_w ≠ 0) (.Shape (.UnexpectedPreprocessedValues i))
    ensure (p.current.length = pre_w ∧
      (p.next.map List.length).getD 0 = if ba.opens_preprocessed_next then pre_w else 0)
      (.Shape (.PreprocessedWidthMismatch i))
    ensure (ba.opens_preprocessed_next ∨ p.next = none) (.Shape (.UnexpectedPreprocessedNext i))
  | none => ensure (pre_w = 0) (.Shape (.PreprocessedWidthMismatch i))
  let expected_perm_len := if lookups.isEmpty then 0 else (lookups.length + 1) * cfg.D
  ensure (ov.permutation_local.length = expected_perm_len ∧
    ov.permutation_next.length = expected_perm_len) (.Lookup (.PermutationWidthMismatch i))
  ensure (terminal.isSome = !lookups.isEmpty) (.Lookup (.TerminalPresenceMismatch i))

/-- The verifier's shape checks, before any transcript work:

* the counts, then the randomization
* the first loop: degree bits, preprocessed widths, quotient sizing
* the multiplicity height bound
* each instance's openings
* the permutation commitment.

It returns each instance's sizes and the number of instances with lookups. -/
def check_shape (cfg : Config) (airs : List (BatchAir F)) (sizing : ℕ → AirLayout → ℕ → Option ℕ)
    (proof : BatchProof C P F K) (public_values : List (List F)) (common : CommonData C F) :
    M (List Sizes × ℕ) := do
  let n := airs.length
  ExceptT.mk (some (ensure (proof.opened.length = n ∧ public_values.length = n ∧
    proof.degree_bits.length = n ∧ proof.lookup_terminals.length = n ∧ common.lookups.length = n ∧
    ∀ g ∈ common.preprocessed, g.instances.length = n) (.Shape .InstanceCountMismatch)))
  ExceptT.mk (some (ensure ((∀ ov ∈ proof.opened, ov.random.isSome = cfg.zk) ∧
    proof.random.isSome = cfg.zk) (.Verification .RandomizationError)))
  let sizes ← airs.zipIdx.mapM fun (ba, i) => instance_sizes G cfg common sizing proof.degree_bits ba i
  match ← panicOf (check_multiplicity_height_bound cfg.characteristic common.lookups
      (sizes.map fun sz => 2 ^ sz.base_degree_bits)) with
  | .error s => throw (.Lookup (.MultiplicityHeightBound s))
  | .ok () => pure ()
  airs.zipIdx.forM fun (ba, i) => do
    let pv ← panicOf public_values[i]?
    let ov ← panicOf proof.opened[i]?
    let sz ← panicOf sizes[i]?
    let lookups ← panicOf common.lookups[i]?
    let terminal ← panicOf proof.lookup_terminals[i]?
    ExceptT.mk (some (check_instance cfg ba i pv ov sz lookups terminal))
  let k := (common.lookups.filter (!·.isEmpty)).length
  ExceptT.mk (some (ensure (proof.permutation.isSome = decide (k > 0)) (.Lookup .CommitmentMismatch)))
  pure (sizes, k)

end shape

/-! ## The transcript -/

/-- The challenger operations the batch adds to the FRI sponge.

The seed is the state after the domain separator a shape describes. -/
structure BatchSponge (F K C Com S : Type) where
  sponge : p3_fri.transcript.mirror.Sponge K Com S
  seed : BatchShape → S
  observe_commitment : S → C → S
  observe_extension : S → K → S
  observe_public_values : S → List F → S

section phases

variable {F K C Com S : Type} [Field F] [Field K] [Algebra F K] [DecidableEq F]

/-- Absorb every instance's extended degree bits, each as an extension element. -/
def instance_bindings (sp : BatchSponge F K C Com S) (s : S) (degree_bits : List ℕ) : S :=
  degree_bits.foldl (fun s (b : ℕ) => sp.observe_extension s (b : K)) s

/-- Absorb the main commitment, then every instance's public values. -/
def main_phase (sp : BatchSponge F K C Com S) (s : S) (main : C) (public_values : List (List F)) : S :=
  public_values.foldl sp.observe_public_values (sp.observe_commitment s main)

/-- Absorb the global preprocessed commitment, when there is one. -/
def preprocessed_phase (sp : BatchSponge F K C Com S) (s : S) (commitment : Option C) : S :=
  match commitment with
  | some c => sp.observe_commitment s c
  | none => s

/-- Check the lookup grind, then draw the pair and lay it out per instance.

* with no lookup, a witness is rejected, and no step is played
* with lookups, a missing witness is rejected
* at zero difficulty the witness must be zero
* the grind panics at a difficulty the field cannot sample. -/
def lookup_phase (sp : BatchSponge F K C Com S) (shape : BatchShape) (s : S)
    (all_lookups : List (List (Lookup F))) (witness : Option F) :
    ExceptT BatchTranscriptFailure Option (List (List K) × S) := do
  let bits := shape.lookup_pow_bits
  if ¬ shape.has_lookups then
    match witness with
    | some _ => throw .UnexpectedLookupPowWitness
    | none => pure (all_lookups.map fun _ => [], s)
  else
    match witness with
    | none => throw (.MissingLookupPowWitness bits)
    | some w =>
      if bits = 0 ∧ w ≠ 0 then throw .NonCanonicalLookupPowWitness
      let (ok, s) ← ExceptT.lift (p3_fri.transcript.mirror.check_witness sp.sponge s bits (algebraMap F K w))
      if !ok then throw (.LookupPowWitness bits)
      let (alpha, s) := sp.sponge.sample s
      let (beta, s) := sp.sponge.sample s
      let challenges ← ExceptT.lift (lay_out_lookup_challenges 2 all_lookups alpha beta)
      pure (challenges, s)

/-- Absorb the permutation commitment and every terminal, then draw alpha. -/
def permutation_phase (sp : BatchSponge F K C Com S) (s : S) (commitment : Option C)
    (terminals : List K) : K × S :=
  let s := match commitment with
    | some c => sp.observe_commitment s c
    | none => s
  sp.sponge.sample (terminals.foldl sp.observe_extension s)

/-- Absorb the quotient commitment, then the randomization commitment when there is one. -/
def quotient_phase (sp : BatchSponge F K C Com S) (s : S) (quotient : C) (randomization : Option C) : S :=
  let s := sp.observe_commitment s quotient
  match randomization with
  | some r => sp.observe_commitment s r
  | none => s

/-- Check the out-of-domain grind, then draw zeta.

* at zero difficulty the witness must be zero
* the grind panics at a difficulty the field cannot sample. -/
def ood_phase (sp : BatchSponge F K C Com S) (shape : BatchShape) (s : S) (witness : F) :
    ExceptT BatchTranscriptFailure Option (K × S) := do
  let bits := shape.ood_pow_bits
  if bits = 0 ∧ witness ≠ 0 then throw .NonCanonicalOodPowWitness
  let (ok, s) ← ExceptT.lift
    (p3_fri.transcript.mirror.check_witness sp.sponge s bits (algebraMap F K witness))
  if !ok then throw (.OodPowWitness bits)
  pure (sp.sponge.sample s)

variable {P : Type}

/-- The transcript, in Rust's order.

It returns the lookup challenges, alpha, zeta and the state the opening argument receives. -/
def replay (sp : BatchSponge F K C Com S) (shape : BatchShape) (proof : BatchProof C P F K)
    (public_values : List (List F)) (common : CommonData C F) : M (List (List K) × K × K × S) := do
  let s := sp.seed shape
  let s := instance_bindings sp s proof.degree_bits
  let s := main_phase sp s proof.main public_values
  let s := preprocessed_phase sp s (common.preprocessed.map (·.commitment))
  let (challenges, s) ← (lookup_phase sp shape s common.lookups proof.lookup_pow_witness).adapt
    .Transcript
  let (alpha, s) := permutation_phase sp s proof.permutation (proof.lookup_terminals.filterMap id)
  let s := quotient_phase sp s proof.quotient_chunks proof.random
  let (zeta, s) ← (ood_phase sp shape s proof.ood_pow_witness).adapt .Transcript
  pure (challenges, alpha, zeta, s)

end phases

/-- The shape the transcript is described with. -/
def shapeOf {F : Type} {C : Type} (cfg : Config) (airs : List (BatchAir F)) (common : CommonData C F)
    (sizes : List Sizes) (num_lookup_instances : ℕ) : BatchShape :=
  ⟨airs.map (·.air.width), airs.map (·.air.num_public_values), sizes.map (·.preprocessed_width),
    common.preprocessed.isSome, num_lookup_instances, cfg.lookup_pow_bits, cfg.zk, cfg.ood_pow_bits⟩

/-! ## The opening argument's claims -/

section claims

variable {F K : Type} [Field F] [DecidableEq F] [Field K] [DecidableEq K] (G : Gen K)
variable {C P : Type}

/-- A point that is rejected when absent. -/
def orReject {α : Type} (o : Option α) (e : Error) : M α :=
  match o with
  | some a => pure a
  | none => throw e

/-- Each instance's base and extended trace domains. -/
def trace_domains (cfg : Config) (degree_bits : List ℕ) : M (List (Coset G × Coset G)) :=
  degree_bits.zipIdx.mapM fun (db, i) => do
    let (_, ext_size) ← ExceptT.mk (some (validate_degree_bits_at cfg i db))
    let td ← panicOf (natural_domain_for_degree G (ext_size / 2 ^ cfg.zk.toNat))
    let ed ← panicOf (natural_domain_for_degree G ext_size)
    pure (td, ed)

/-- Each instance's quotient chunk domains.

The quotient coset has order 2^(b + L) on the extended trace domain, split into 2^(L + z) chunks. -/
def quotient_domains (g : K) (cfg : Config) (degree_bits : List ℕ) (sizes : List Sizes)
    (domains : List (Coset G × Coset G)) : M (List (List (Coset G))) :=
  (List.range degree_bits.length).mapM fun i => do
    let db ← panicOf degree_bits[i]?
    let sz ← panicOf sizes[i]?
    let n_chunks ← match checked_log_size_sum sz.log_num_quotient_chunks cfg.zk.toNat with
      | none => throw (.Shape (.QuotientDomainTooLarge i))
      | some (_, n) => pure n
    let ed ← panicOf (domains[i]?.map (·.2))
    let quotient_size ← match checked_log_size_sum db sz.log_num_quotient_chunks with
      | none => throw (.Shape (.QuotientDomainTooLarge i))
      | some (_, q) => pure q
    let qd ← orReject (Coset.try_create_disjoint_domain G ed g quotient_size)
      (.Shape (.QuotientDomainTooLarge i))
    panicOf (Coset.split_domains G qd n_chunks)

/-- The preprocessed round: one matrix per instance the global commitment lists, in matrix order.

* a listed instance must have a positive width, an opening and matching metadata
* its domain is the subgroup of the metadata's degree
* its next row is claimed when its AIR reads it. -/
def preprocessed_round (airs : List (BatchAir F)) (zeta : K) (proof : BatchProof C P F K)
    (sizes : List Sizes) (domains : List (Coset G × Coset G)) (global : GlobalPreprocessed C) :
    M (p3_fri.verifier.mirror.Claim G C) := do
  let mats ← global.matrix_to_instance.zipIdx.mapM fun (inst, matrix_index) => do
    let sz ← panicOf sizes[inst]?
    if sz.preprocessed_width = 0 then throw (.Shape (.PreprocessedMetadataMismatch inst))
    let ov ← panicOf proof.opened[inst]?
    let p ← orReject ov.preprocessed (.Shape (.MissingPreprocessedValues inst))
    let db ← panicOf proof.degree_bits[inst]?
    let pm ← orReject (← panicOf global.instances[inst]?) (.Shape (.PreprocessedMetadataMismatch inst))
    if pm.matrix_index ≠ matrix_index ∨ pm.degree_bits ≠ db then
      throw (.Shape (.PreprocessedMetadataMismatch inst))
    let pre_domain ← panicOf (natural_domain_for_degree G (2 ^ pm.degree_bits))
    let opens_next ← panicOf (airs[inst]?.map (·.opens_preprocessed_next))
    if opens_next then
      let next ← orReject p.next (.Shape (.MissingPreprocessedValues inst))
      let td ← panicOf (domains[inst]?.map (·.1))
      let zeta_next ← orReject (Coset.next_point G td zeta) (.Verification .NextPointUnavailable)
      pure (⟨pre_domain, [⟨zeta, p.current⟩, ⟨zeta_next, next⟩]⟩ : MatrixOpening K (Coset G))
    else pure ⟨pre_domain, [⟨zeta, p.current⟩]⟩
  pure ⟨global.commitment, mats⟩

/-- The permutation round: one matrix per instance with a nonempty permutation opening. -/
def permutation_round (zeta : K) (proof : BatchProof C P F K) (domains : List (Coset G × Coset G))
    (commitment : C) : M (p3_fri.verifier.mirror.Claim G C) := do
  let mats ← ((domains.zip proof.opened).zipIdx).mapM fun ((d, ov), i) => do
    if ov.permutation_local.length ≠ ov.permutation_next.length then
      throw (.Lookup (.PermutationLengthMismatch i))
    if ov.permutation_local.isEmpty then pure none
    else
      let zeta_next ← orReject (Coset.next_point G d.1 zeta) (.Verification .NextPointUnavailable)
      pure (some (⟨d.2, [⟨zeta, ov.permutation_local⟩, ⟨zeta_next, ov.permutation_next⟩]⟩ :
        MatrixOpening K (Coset G)))
  pure ⟨commitment, mats.filterMap id⟩

/-- The claims at zeta, in round order, with the chunk domains and the preprocessed round's index.

* the randomization round, when hiding, on each extended trace domain
* the trace at zeta, and at the next point when the AIR reads the next row
* one matrix per quotient chunk, on its randomized domain
* the preprocessed round, when the common data has one
* the permutation round, when the proof has a permutation commitment. -/
def commitments_with_opening_points (g : K) (cfg : Config) (airs : List (BatchAir F)) (zeta : K)
    (proof : BatchProof C P F K) (common : CommonData C F) (sizes : List Sizes) :
    M (List (p3_fri.verifier.mirror.Claim G C) × List (List (Coset G)) × Option ℕ) := do
  let domains ← trace_domains G cfg proof.degree_bits
  let random_round ← match proof.random with
    | some rc => do
      let mats ← (domains.zip proof.opened).mapM fun (d, ov) => do
        let rv ← panicOf ov.random
        pure (⟨d.2, [⟨zeta, rv⟩]⟩ : MatrixOpening K (Coset G))
      pure [(⟨rc, mats⟩ : p3_fri.verifier.mirror.Claim G C)]
    | none => pure []
  let trace_mats ← ((domains.zip proof.opened).zipIdx).mapM fun ((d, ov), i) => do
    let opens_next ← panicOf (airs[i]?.map (·.opens_main_next))
    if opens_next then
      let zeta_next ← orReject (Coset.next_point G d.1 zeta) (.Verification .NextPointUnavailable)
      let next ← panicOf ov.trace_next
      pure (⟨d.2, [⟨zeta, ov.trace_local⟩, ⟨zeta_next, next⟩]⟩ : MatrixOpening K (Coset G))
    else pure ⟨d.2, [⟨zeta, ov.trace_local⟩]⟩
  let qdoms ← quotient_domains G g cfg proof.degree_bits sizes domains
  let randomized ← qdoms.mapM fun doms => doms.mapM fun d =>
    panicOf (natural_domain_for_degree G (Coset.size G d * 2 ^ cfg.zk.toNat))
  let qc_mats ← randomized.zipIdx.mapM fun (doms, i) => do
    let ov ← panicOf proof.opened[i]?
    if doms.length ≠ ov.quotient_chunks.length then
      throw (.Shape (.QuotientDomainsCountMismatch i))
    pure ((doms.zip ov.quotient_chunks).map fun dv =>
      (⟨dv.1, [⟨zeta, dv.2⟩]⟩ : MatrixOpening K (Coset G)))
  let base := random_round ++ [⟨proof.main, trace_mats⟩, ⟨proof.quotient_chunks, qc_mats.flatten⟩]
  let preprocessed_index := common.preprocessed.map fun _ => base.length
  let pre_round ← match common.preprocessed with
    | some global => do pure [← preprocessed_round G airs zeta proof sizes domains global]
    | none => pure []
  let perm_round ← match proof.permutation with
    | some pc => do pure [← permutation_round G zeta proof domains pc]
    | none => pure []
  pure (base ++ pre_round ++ perm_round, qdoms, preprocessed_index)

end claims

/-! ## The checks at zeta -/

section zeta

variable {F K : Type} [Field F] [DecidableEq F] [Inhabited F] [Field K] [DecidableEq K] [Algebra F K]
variable (G : Gen K)

/-- The chunks of exactly D values, the remainder dropped.

A width of zero panics. -/
def chunks_exact (D : ℕ) (l : List K) : Option (List (List K)) :=
  if D = 0 then none else some ((List.range (l.length / D)).map fun j => (l.drop (j * D)).take D)

/-- A flattened permutation row as extension elements.

There are none without permutation columns. -/
noncomputable def recompose_permutation {D : ℕ} (B : Module.Basis (Fin D) F K) (aux_width : ℕ)
    (flat : List K) : Option (List K) :=
  if aux_width = 0 then some []
  else do
    let chunks ← chunks_exact D flat
    chunks.mapM (from_ext_basis_coefficients B)

/-- A rejection at zeta, with the instance a mismatch is reported at. -/
def ofCheckError (i : ℕ) : VerificationError → Error
  | .OodEvaluationMismatch => .OodEvaluationMismatch i
  | e => .Verification e

/-- Instance i's check at zeta.

* the quotient recombined from its chunks
* the permutation rows recomposed into extension elements
* a next row the AIR does not read is zeros
* the periodic columns screened, then evaluated at zeta
* the AIR and lookup constraints folded and compared with the quotient. -/
noncomputable def check_at_zeta {D : ℕ} (B : Module.Basis (Fin D) F K) (ba : BatchAir F) (i : ℕ)
    (ov : Opened K) (pre_w : ℕ) (lookups : List (Lookup F)) (terminal : Option K)
    (challenges : List K) (pv : List F) (trace_domain : Coset G) (qdoms : List (Coset G))
    (zeta alpha : K) : M Unit := do
  let quotient ← panicOf (recompose_quotient_from_chunks G B qdoms ov.quotient_chunks zeta)
  let aux_width := if lookups.isEmpty then 0 else lookups.length + 1
  let perm_local ← panicOf (recompose_permutation B aux_width ov.permutation_local)
  let perm_next ← panicOf (recompose_permutation B aux_width ov.permutation_next)
  let trace_next := ov.trace_next.getD (List.replicate ba.air.width 0)
  let pre_next := (ov.preprocessed.bind (·.next)).getD (List.replicate pre_w 0)
  let periodic ← match PeriodicColumns.new (ba.air.periodic_columns.map (·.map (algebraMap F K)))
      (Coset.size G trace_domain) with
    | .error _ => throw (.Verification .PeriodicColumn)
    | .ok pc => pure pc
  let periodic_values ← panicOf
    (Coset.evaluate_periodic_columns_at G trace_domain periodic.columns periodic.height zeta)
  match ← panicOf (verify_constraints_with_lookups G ba.air ov.trace_local trace_next
      ((ov.preprocessed.map (·.current)).getD []) pre_next perm_local perm_next challenges
      terminal.toList periodic_values lookups pv trace_domain zeta alpha quotient) with
  | .ok () => pure ()
  | .error e => throw (ofCheckError i e)

end zeta

/-! ## The verifier -/

variable {F K C Com S P PE : Type} [Field F] [DecidableEq F] [Inhabited F] [Field K] [DecidableEq K]
  [Algebra F K]

/-- Every instance's check at zeta, in order. -/
noncomputable def check_all_at_zeta {D : ℕ} (G : Gen K) (B : Module.Basis (Fin D) F K) (cfg : Config)
    (airs : List (BatchAir F)) (proof : BatchProof C P F K) (public_values : List (List F))
    (common : CommonData C F) (sizes : List Sizes) (challenges : List (List K))
    (qdoms : List (List (Coset G))) (zeta alpha : K) : M Unit := do
  let trace_domains ← sizes.mapM fun sz =>
    panicOf (natural_domain_for_degree G (sz.ext_size / 2 ^ cfg.zk.toNat))
  airs.zipIdx.forM fun (ba, i) => do
    let ov ← panicOf proof.opened[i]?
    let sz ← panicOf sizes[i]?
    let lookups ← panicOf common.lookups[i]?
    let terminal ← panicOf proof.lookup_terminals[i]?
    let ch ← panicOf challenges[i]?
    let pv ← panicOf public_values[i]?
    let td ← panicOf trace_domains[i]?
    let qd ← panicOf qdoms[i]?
    check_at_zeta G B ba i ov sz.preprocessed_width lookups terminal ch pv td qd zeta alpha

/-- The batch verifier, in Rust's order.

* the boundary assertion
* the shape checks
* the transcript: the lookup grind and pair, alpha, the out-of-domain grind and zeta
* the claims at zeta and the opening argument
* each instance's check at zeta, with the shared alpha
* the cross-table sum of the terminals.

The arguments are:

* the generator table, the field generator g, and a basis of K over F
* the configuration, the AIRs and the quotient sizing
* the sponge and the opening argument
* the proof, the public values and the common data. -/
noncomputable def verify_batch {D : ℕ} (G : Gen K) (g : K) (B : Module.Basis (Fin D) F K)
    (cfg : Config) (airs : List (BatchAir F)) (sizing : ℕ → AirLayout → ℕ → Option ℕ)
    (sp : BatchSponge F K C Com S)
    (pcs : List (p3_fri.verifier.mirror.Claim G C) → Option ℕ → S → Option (Except PE Unit))
    (proof : BatchProof C P F K) (public_values : List (List F)) (common : CommonData C F) :
    Option (Except Error Unit) := ExceptT.run do
  if airs.any (fun ba => !ba.air.public_boundary_io.isEmpty) then panicOf none
  let (sizes, k) ← check_shape G cfg airs sizing proof public_values common
  let (challenges, alpha, zeta, s) ←
    replay sp (shapeOf cfg airs common sizes k) proof public_values common
  let (claims, qdoms, preprocessed_index) ←
    commitments_with_opening_points G g cfg airs zeta proof common sizes
  match ← panicOf (pcs claims preprocessed_index s) with
  | .error _ => throw (.Verification .InvalidOpeningArgument)
  | .ok () => pure ()
  check_all_at_zeta G B cfg airs proof public_values common sizes challenges qdoms zeta alpha
  if !verify_terminal_sum proof.lookup_terminals then throw (.Lookup .TerminalSum)

end p3_batch_stark.verify.mirror
