/-
Transcriptions of transcript.rs: the shape of one run, its seed, and the verifier's steps.

The draw of distinct pairs is the challenger's rejection loop, which keeps a candidate only if it is new.
-/
module

public import P3BinaryPcs.Model
public import P3BinaryPcs.Params

@[expose] public section

namespace p3_binary_pcs.transcript.mirror

open p3_sumcheck.mirror p3_binary_pcs.mirror p3_binary_pcs.params.mirror

/-- num_distinct_queries: one test per fold pair, so at most half the domain. -/
def num_distinct_queries (domain_size num_queries : ℕ) : ℕ := min num_queries (domain_size / 2)

/-- log2_strict_usize: the exponent of a power of two, which panics on anything else. -/
def log2_strict_usize (n : ℕ) : Option ℕ :=
  if n ≠ 0 ∧ 2 ^ Nat.log2 n = n then some (Nat.log2 n) else none

/-- BinaryPcsShape. -/
structure BinaryPcsShape where
  num_variables : ℕ
  log_folding_factor : ℕ
  num_oracles : ℕ
  final_codeword_len : ℕ
  pow_bits : ℕ
  pair_bits : ℕ
  num_pairs : ℕ
  deriving DecidableEq

/-- BinaryPcsShape::new.

The subtractions panic below zero, the shifts at a word or more, and the logarithm off a power of two. -/
def BinaryPcsShape.new (c : BinaryPcsConfig) : Option BinaryPcsShape := do
  if c.log_folding_factor = 0 then none
  let shift := c.log_folding_factor - 1
  let domain ← c.domain_size
  let pair_domain := domain >>> shift
  let batches ← c.num_fold_batches
  if batches = 0 then none
  if c.log_final_len ≥ USIZE_BITS then none
  let pair_bits ← log2_strict_usize (pair_domain / 2)
  pure ⟨c.num_variables, c.log_folding_factor, batches - 1, 2 ^ c.log_final_len,
    c.params.pow_bits, pair_bits, num_distinct_queries pair_domain c.num_queries⟩

/-- The numbers the seed binds: the step counts and widths of the pattern, then the arity and the folding factor. -/
def BinaryPcsShape.seed {F EF : Type _} (s : BinaryPcsShape) : Step F EF :=
  .seed "p3-binary-pcs"
    [s.num_oracles, s.final_codeword_len, s.pow_bits, s.pair_bits, s.num_pairs,
      s.num_variables, s.log_folding_factor]

/-- sorted_pairs: the drawn pairs in ascending order, each lifted to its low position. -/
def sorted_pairs (kept : List ℕ) : List ℕ := (kept.mergeSort (· ≤ ·)).map (· <<< 1)

/-- The errors of the transcript steps. -/
inductive TranscriptFailure (F : Type _) where
  | FinalCodewordLength (expected got : ℕ)
  | PowWitness (bits : ℕ)
  | NonCanonicalPowWitness (actual : F)

section Verifier

variable {F EF : Type _} [Field F] [DecidableEq F] (S : PSponge F EF) (s : BinaryPcsShape)

/-- BinaryPcsVerifierTranscript::final_codeword: the length is checked, then every symbol absorbed. -/
def final_codeword (codeword : List EF) (h : List (Step F EF)) :
    Except (TranscriptFailure F) (List (Step F EF)) :=
  if codeword.length ≠ s.final_codeword_len then
    .error (.FinalCodewordLength s.final_codeword_len codeword.length)
  else .ok (h ++ [.message codeword])

/-- BinaryPcsVerifierTranscript::query_pow: zero is the only witness at zero difficulty; else the grind is checked and absorbed. -/
def query_pow (witness : F) (h : List (Step F EF)) : Except (TranscriptFailure F) (List (Step F EF)) :=
  if s.pow_bits = 0 then
    if witness ≠ 0 then .error (.NonCanonicalPowWitness witness) else .ok h
  else if S.grind h s.pow_bits witness then .ok (h ++ [.pow s.pow_bits witness])
  else .error (.PowWitness s.pow_bits)

/-- BinaryPcsVerifierTranscript::query_pairs: the distinct pairs, sorted and lifted to their low positions. -/
def query_pairs (h : List (Step F EF)) : List ℕ × List (Step F EF) :=
  (sorted_pairs (List.ofFn fun i => (S.pairs h s.pair_bits s.num_pairs i : ℕ)), h ++ [.challenge])

end Verifier

end p3_binary_pcs.transcript.mirror
