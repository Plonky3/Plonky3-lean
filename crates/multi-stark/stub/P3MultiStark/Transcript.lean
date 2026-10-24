/-
Transcriptions of the statement transcript of p3-multi-stark and of its zerocheck transcript.

They cover the step sequences the transcripts describe, and the numbers their instance labels bind.

These do not extract.
They are generic over the AIR and the transcript field, which aeneas rejects.

Each definition transcribes one Rust item, named in the crate's mirror entries.

What a transcription abstracts:

* a step is its role and its length, without the type names the markers record as diagnostics
* an instance label is the list of the 64-bit words absorbed, each as a natural number
* an AIR is the numbers the shape reads from it.

Loops, branches and the order of steps are kept.
-/
module

public import Mathlib.Data.List.Basic

@[expose] public section

namespace p3_multi_stark.transcript.mirror

/-- The delegations the statement brackets. -/
inductive Delegation where
  | MainCommitment
  | BusArgument
  | LookupArgument
  | Zerocheck
  | IndexedLookup
  | MainOpening
  | PreprocessedOpening
  deriving DecidableEq

/-- One step of the statement's interaction pattern. -/
inductive Step where
  /-- The batched preprocessed commitment, absorbed as a message. -/
  | PreprocessedCommitment
  /-- One instance's public values, absorbed as that many field elements. -/
  | PublicValues (count : ℕ)
  /-- The opening marker of a delegation. -/
  | Begin (d : Delegation)
  /-- The closing marker of a delegation. -/
  | End (d : Delegation)
  deriving DecidableEq

/-- MultiStarkInstanceShape. -/
structure MultiStarkInstanceShape where
  num_variables : ℕ
  main_width : ℕ
  preprocessed_width : ℕ
  num_public_values : ℕ
  main_next_row_columns : List ℕ
  preprocessed_next_row_columns : List ℕ
  deriving DecidableEq

/-- MultiStarkShape. -/
structure MultiStarkShape where
  instances : List MultiStarkInstanceShape
  pow_bits : ℕ
  has_indexed : Bool
  has_bus : Bool
  deriving DecidableEq

/-- MultiStarkShape::has_preprocessed: some instance has preprocessed columns. -/
def MultiStarkShape.has_preprocessed (s : MultiStarkShape) : Bool :=
  (s.instances.filter (·.preprocessed_width ≠ 0)).length > 0

/-- delegation: the matched marker pair of one delegation. -/
def delegation (d : Delegation) : List Step := [.Begin d, .End d]

/-- MultiStarkShape::pattern, in order:

- the preprocessed commitment
- the main commitment's bracket
- one public-value step per instance
- the delegations, in the order the run performs them. -/
def MultiStarkShape.pattern (s : MultiStarkShape) : List Step :=
  (if s.has_preprocessed then [.PreprocessedCommitment] else []) ++
  delegation .MainCommitment ++
  s.instances.map (fun i => .PublicValues i.num_public_values) ++
  (if s.has_bus then delegation .BusArgument else []) ++
  delegation .LookupArgument ++
  delegation .Zerocheck ++
  (if s.has_indexed then delegation .IndexedLookup else []) ++
  delegation .MainOpening ++
  (if s.has_preprocessed then delegation .PreprocessedOpening else [])

/-- The words one successor-column list contributes: its length, then its columns. -/
def columnWords (columns : List ℕ) : List ℕ := columns.length :: columns

/-- The words one instance contributes to MultiStarkShape::domain_separator's label. -/
def instanceWords (i : MultiStarkInstanceShape) : List ℕ :=
  [i.num_variables, i.main_width, i.preprocessed_width] ++
    columnWords i.main_next_row_columns ++ columnWords i.preprocessed_next_row_columns

/-- MultiStarkShape::domain_separator: the instance label, after the version, the name and the pattern. -/
def MultiStarkShape.label (s : MultiStarkShape) : List ℕ :=
  [s.instances.length, s.pow_bits] ++ s.instances.flatMap instanceWords

/-- The zerocheck's challenges and its bracket. -/
inductive ZerocheckStep where
  | Alpha
  | Beta
  | Eta
  | BusBatching
  | Tau (count : ℕ)
  | BeginSumcheck
  | EndSumcheck
  deriving DecidableEq

/-- AirDegrees: the per-variable degree of an AIR's constraints and of its lookup links. -/
structure AirDegrees where
  constraints : ℕ
  interactions : ℕ
  deriving DecidableEq

/-- ZerocheckShape. -/
structure ZerocheckShape where
  log_height : ℕ
  lookup_point_len : ℕ
  pow_bits : ℕ
  air_degrees : List AirDegrees
  bus_degree : Option ℕ
  deriving DecidableEq

/-- ZerocheckShape::free_coordinates: the coordinates of the zerocheck point drawn here.

They come ahead of the lookup tail. -/
def ZerocheckShape.free_coordinates (s : ZerocheckShape) : ℕ := s.log_height - s.lookup_point_len

/-- ZerocheckShape::pattern, in order:

- alpha and beta
- eta, with a lookup
- lambda, with a bus
- the free coordinates
- the sumcheck's bracket. -/
def ZerocheckShape.pattern (s : ZerocheckShape) : List ZerocheckStep :=
  [.Alpha, .Beta] ++
  (if s.lookup_point_len > 0 then [.Eta] else []) ++
  (if s.bus_degree.isSome then [.BusBatching] else []) ++
  (if s.free_coordinates > 0 then [.Tau s.free_coordinates] else []) ++
  [.BeginSumcheck, .EndSumcheck]

/-- ZerocheckShape::domain_separator: the instance label, after the version, the name and the pattern. -/
def ZerocheckShape.label (s : ZerocheckShape) : List ℕ :=
  [s.log_height, s.lookup_point_len, s.pow_bits, s.air_degrees.length] ++
    s.air_degrees.flatMap (fun d => [d.constraints, d.interactions]) ++
    (match s.bus_degree with | none => [] | some d => [d])

end p3_multi_stark.transcript.mirror
