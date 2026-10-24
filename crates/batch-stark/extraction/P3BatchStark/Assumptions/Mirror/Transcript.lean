/-
Transcriptions of the batch transcript: its shape, its pattern and seed, the verifier's phases, and the layout of the lookup challenges.

These do not extract: they are generic over the challenger, the commitment and the field traits, which aeneas rejects.

Each definition transcribes one Rust item, named in the crate's mirror entries.

What a transcription abstracts:

- the sponge state is the list of messages absorbed so far, starting from the seed
- a challenge is an arbitrary function of that list, as a random oracle
- the grind check is an arbitrary predicate of that list, the bit count and the witness
- the pattern player is the list of steps played, checked against the pattern by the caller
- the seed is the protocol identity, the pattern, and the instance label as a list of numbers
- a commitment absorbs as one message, and so does a field element
- a hash map is a list of keys with their values, in first-insertion order
- a panic is none.

The order of absorptions, samples and checks is kept.
-/
module

public import P3Lookup

@[expose] public section

namespace p3_batch_stark.transcript.mirror

open p3_lookup.mirror

/-- The numbers that describe the transcript.

They come from the AIRs, the common data and the configuration, never from a proof. -/
structure BatchShape where
  trace_widths : List ℕ
  public_value_counts : List ℕ
  preprocessed_widths : List ℕ
  has_preprocessed_commitment : Bool
  num_lookup_instances : ℕ
  lookup_pow_bits : ℕ
  has_randomization_commitment : Bool
  ood_pow_bits : ℕ
  deriving DecidableEq

/-- The number of instances. -/
def BatchShape.num_instances (s : BatchShape) : ℕ := s.trace_widths.length

/-- Whether an instance declares a lookup. -/
def BatchShape.has_lookups (s : BatchShape) : Bool := decide (s.num_lookup_instances > 0)

/-- The steps of the transcript. -/
inductive Step where
  | degree_bits
  | main_commitment
  | public_values (n : ℕ)
  | preprocessed_commitment
  | lookup_pow (bits : ℕ)
  | lookup_alpha
  | lookup_beta
  | permutation_commitment
  | lookup_terminal
  | constraint_challenge
  | quotient_commitment
  | randomization_commitment
  | ood_pow (bits : ℕ)
  | zeta
  | begin_opening_argument
  | end_opening_argument
  deriving DecidableEq

/-- The steps of the lookup phase:

- the grind
- the pair
- the permutation commitment
- one terminal per instance with a lookup. -/
def BatchShape.lookupSteps (s : BatchShape) : List Step :=
  [.lookup_pow s.lookup_pow_bits, .lookup_alpha, .lookup_beta, .permutation_commitment] ++
    List.replicate s.num_lookup_instances .lookup_terminal

/-- The pattern, in the order the Rust pushes its steps. -/
def BatchShape.pattern (s : BatchShape) : List Step :=
  s.trace_widths.map (fun _ => .degree_bits) ++ [.main_commitment] ++
  s.public_value_counts.map .public_values ++
  (if s.has_preprocessed_commitment then [.preprocessed_commitment] else []) ++
  (if s.has_lookups then s.lookupSteps else []) ++
  [.constraint_challenge, .quotient_commitment] ++
  (if s.has_randomization_commitment then [.randomization_commitment] else []) ++
  [.ood_pow s.ood_pow_bits, .zeta, .begin_opening_argument, .end_opening_argument]

/-- The seed: version, protocol name, pattern, and the instance label. -/
structure DomainSeparator where
  version : ℕ
  protocol_name : String
  pattern : List Step
  label : List ℕ
  deriving DecidableEq

/-- The seed of a shape: the instance count, then every trace width, then every preprocessed width. -/
def BatchShape.domain_separator (s : BatchShape) : DomainSeparator :=
  ⟨1, "p3-batch-stark", s.pattern, s.num_instances :: (s.trace_widths ++ s.preprocessed_widths)⟩

/-- A message the sponge absorbs.

It is the seed, a commitment, a base element, an extension element, or the marker of a draw. -/
inductive Msg (C F E : Type) where
  | seed (d : DomainSeparator)
  | com (c : C)
  | base (x : F)
  | ext (x : E)
  | challenge (s : Step)

/-- Why a transcript step rejects the proof. -/
inductive BatchTranscriptFailure where
  | LookupPowWitness (bits : ℕ)
  | MissingLookupPowWitness (bits : ℕ)
  | UnexpectedLookupPowWitness
  | NonCanonicalLookupPowWitness
  | OodPowWitness (bits : ℕ)
  | NonCanonicalOodPowWitness
  deriving DecidableEq

/-- The verifier's state: the absorbed messages and the steps played. -/
structure St (C F E : Type) where
  msgs : List (Msg C F E)
  played : List Step

variable {C F E : Type}

/-- Play a step and absorb its messages. -/
def St.step (st : St C F E) (s : Step) (ms : List (Msg C F E)) : St C F E :=
  ⟨st.msgs ++ ms, st.played ++ [s]⟩

/-- Draw a challenge: the oracle at the absorbed messages, then the marker of the draw. -/
def St.draw (H : List (Msg C F E) → E) (st : St C F E) (s : Step) : St C F E × E :=
  (⟨st.msgs ++ [.challenge s], st.played ++ [s]⟩, H st.msgs)

/-- Seed a fresh transcript from the shape. -/
def new (shape : BatchShape) : St C F E := ⟨[.seed shape.domain_separator], []⟩

section Phases

variable [Zero F] [DecidableEq F] [NatCast E]

/-- Replay every instance's extended-trace degree bits, each as an extension element. -/
def instance_bindings (st : St C F E) (degree_bits : List ℕ) : St C F E :=
  degree_bits.foldl (fun st (b : ℕ) => st.step .degree_bits [.ext (b : E)]) st

/-- Replay the main commitment, then every instance's public values. -/
def main_phase (st : St C F E) (main : C) (public_values : List (List F)) : St C F E :=
  public_values.foldl (fun st pv => st.step (.public_values pv.length) (pv.map .base))
    (st.step .main_commitment [.com main])

/-- Replay the preprocessed commitment, when there is one. -/
def preprocessed_phase (st : St C F E) (commitment : Option C) : St C F E :=
  match commitment with
  | some c => st.step .preprocessed_commitment [.com c]
  | none => st

/-- Replay a grind: a step of that difficulty, then the witness.

The witness is absorbed and checked only when the difficulty is positive. -/
def observe_pow (powOk : List (Msg C F E) → ℕ → F → Bool) (st : St C F E) (s : Step) (bits : ℕ)
    (w : F) : Option (St C F E) :=
  if bits = 0 then some (st.step s [])
  else if powOk st.msgs bits w then some (st.step s [.base w]) else none

end Phases

/-! ## The lookup challenges -/

/-- The bookkeeping of the challenge layout:

- the global bus ids and widths, by name
- the next bus id
- the widest payload. -/
structure LayoutState where
  global_index : List (String × ℕ)
  global_width : List (String × ℕ)
  next_bus : ℕ
  max_message_width : ℕ

/-- The value of a key in a list map. -/
def lookupKey {β : Type} (m : List (String × β)) (k : String) : Option β := (m.find? (·.1 = k)).map (·.2)

/-- Look up a key in a list map, inserting a default when absent.

It returns the stored value, or the inserted one. -/
def orInsert {β : Type} (m : List (String × β)) (k : String) (v : β) : β × List (String × β) :=
  match lookupKey m k with
  | some x => (x, m)
  | none => (v, m ++ [(k, v)])

/-- The bus id of one lookup: a global bus shares the id of its name, a local bus takes a fresh id.

A lookup whose tuples differ in width panics.

So does a global bus whose width differs from the first width under its name. -/
def busId (st : LayoutState) (ctx : Lookup F) : Option (ℕ × LayoutState) := do
  let ctx_width ← assert_uniform_tuple_width ctx.elements
  let max_message_width := max st.max_message_width ctx_width
  match ctx.kind with
  | .Global bus =>
    let (id, global_index) := orInsert st.global_index bus st.next_bus
    let next_bus := if lookupKey st.global_index bus = none then st.next_bus + 1 else st.next_bus
    let (expected, global_width) := orInsert st.global_width bus ctx_width
    if expected ≠ ctx_width then none
    pure (id, ⟨global_index, global_width, next_bus, max_message_width⟩)
  | .Local => pure (st.next_bus, { st with next_bus := st.next_bus + 1, max_message_width })

/-- The bus ids of every lookup of every instance, in order, and the final bookkeeping. -/
def busIds (all_lookups : List (List (Lookup F))) : Option (List (List ℕ) × LayoutState) :=
  all_lookups.foldlM (fun (acc : List (List ℕ) × LayoutState) contexts => do
    let (ids, st) ← contexts.foldlM (fun (acc : List ℕ × LayoutState) ctx => do
      let (id, st) ← busId acc.2 ctx
      pure (acc.1 ++ [id], st)) ([], acc.2)
    pure (acc.1 ++ [ids], st)) ([], ⟨[], [], 0, 1⟩)

/-- Lay a sampled pair out per instance: for each lookup, its bus offset, then the shared combiner.

A gadget that does not read two challenges per lookup panics, as do the width checks. -/
def lay_out_lookup_challenges {K : Type} [Field K] (num_challenges : ℕ)
    (all_lookups : List (List (Lookup F))) (alpha beta : K) : Option (List (List K)) := do
  if num_challenges ≠ 2 then none
  let (bus_ids, st) ← busIds all_lookups
  let (_, _, bus_prefix) ← Challenges.new alpha beta st.max_message_width st.next_bus
  pure (bus_ids.map fun ids => ids.flatMap fun bus => [bus_prefix.getD bus 0, beta])

/-! ## The lookup, permutation, quotient and out-of-domain phases -/

section Phases

variable [Zero F] [DecidableEq F]

/-- Replay the lookup grind and redraw the pair, or reject the witness.

With no lookup, a witness is rejected and no step is played. -/
def lookup_phase [Field E] (shape : BatchShape) (H : List (Msg C F E) → E)
    (powOk : List (Msg C F E) → ℕ → F → Bool) (num_challenges : ℕ) (st : St C F E)
    (all_lookups : List (List (Lookup F))) (witness : Option F) :
    Option (St C F E × Except BatchTranscriptFailure (List (List E))) := do
  let bits := shape.lookup_pow_bits
  if ¬ shape.has_lookups then
    match witness with
    | some _ => pure (st, .error .UnexpectedLookupPowWitness)
    | none => pure (st, .ok (all_lookups.map fun _ => []))
  else
    match witness with
    | none => pure (st, .error (.MissingLookupPowWitness bits))
    | some w =>
      if bits = 0 ∧ w ≠ 0 then pure (st, .error .NonCanonicalLookupPowWitness)
      else
        match observe_pow powOk st (.lookup_pow bits) bits w with
        | none => pure (st.step (.lookup_pow bits) [], .error (.LookupPowWitness bits))
        | some st =>
          let (st, alpha) := st.draw H .lookup_alpha
          let (st, beta) := st.draw H .lookup_beta
          let challenges ← lay_out_lookup_challenges num_challenges all_lookups alpha beta
          pure (st, .ok challenges)

/-- Replay the permutation commitment and every terminal, then redraw the folding challenge. -/
def permutation_phase (H : List (Msg C F E) → E) (st : St C F E) (commitment : Option C)
    (terminals : List E) : St C F E × E :=
  let st := match commitment with
    | some c => st.step .permutation_commitment [.com c]
    | none => st
  let st := terminals.foldl (fun st t => st.step .lookup_terminal [.ext t]) st
  st.draw H .constraint_challenge

/-- Replay the quotient commitment, then the randomization commitment when there is one. -/
def quotient_phase (st : St C F E) (quotient : C) (randomization : Option C) : St C F E :=
  let st := st.step .quotient_commitment [.com quotient]
  match randomization with
  | some r => st.step .randomization_commitment [.com r]
  | none => st

/-- Replay the out-of-domain grind and redraw zeta, or reject the witness. -/
def ood_phase (shape : BatchShape) (H : List (Msg C F E) → E)
    (powOk : List (Msg C F E) → ℕ → F → Bool) (st : St C F E) (witness : F) :
    St C F E × Except BatchTranscriptFailure E :=
  let bits := shape.ood_pow_bits
  if bits = 0 ∧ witness ≠ 0 then (st, .error .NonCanonicalOodPowWitness)
  else
    match observe_pow powOk st (.ood_pow bits) bits witness with
    | none => (st.step (.ood_pow bits) [], .error (.OodPowWitness bits))
    | some st =>
      let (st, zeta) := st.draw H .zeta
      (st, .ok zeta)

/-- The bracket around the opening argument. -/
def delegate (st : St C F E) : St C F E :=
  (st.step .begin_opening_argument []).step .end_opening_argument []

end Phases

end p3_batch_stark.transcript.mirror
