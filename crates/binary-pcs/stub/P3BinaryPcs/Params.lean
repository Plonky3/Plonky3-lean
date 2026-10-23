/-
Transcriptions of params.rs: the caller's parameters, and the round schedule derived from them.

A machine word has 64 bits.

The query count comes from a floating-point bound of p3-security, so it is an input: a function of the target, the rate and the grinding bits.

The integer part of p3-security's binary schedule model is transcribed beside it, from security/src/binary.rs.

A panic is none.
-/
module

public import Mathlib.Data.Nat.Log

@[expose] public section

namespace p3_binary_pcs.params.mirror

/-- The width of a machine word. -/
def USIZE_BITS : ℕ := 64

/-- POW_HEADER_BITS: the room the challenger's grinding site keeps above the difficulty. -/
def POW_HEADER_BITS : ℕ := 8

/-- POW_COUNTER_BITS: the widest grinding counter. -/
def POW_COUNTER_BITS : ℕ := 64

/-- BINARY_PCS_FIELD_BITS: the widest challenge field the security model prices. -/
def BINARY_PCS_FIELD_BITS : ℕ := 128

/-! ## The security model of p3-security -/

/-- The fields of BinaryPcsRegime. -/
structure BinaryPcsRegime where
  challenge_field_bits : ℕ
  num_variables : ℕ
  log_inv_rate : ℕ
  log_folding_factor : ℕ
  num_queries : ℕ
  query_pow_bits : ℕ
  deriving DecidableEq

/-- BinaryPcsRegime::new: the schedules the model prices. -/
def BinaryPcsRegime.new (K n r f q p : ℕ) : Option BinaryPcsRegime :=
  if K < 8 ∨ K > BINARY_PCS_FIELD_BITS ∨ ¬ K.isPowerOfTwo ∨ n = 0 ∨ r = 0 ∨
      n + r ≥ USIZE_BITS ∨ f = 0 ∨ f > n ∨ q = 0 then none
  else some ⟨K, n, r, f, q, p⟩

/-- BinaryPcsRegime::queries_are_exhaustive: every coset of the first batch is queried. -/
def BinaryPcsRegime.queries_are_exhaustive (s : BinaryPcsRegime) : Bool :=
  decide (2 ^ (s.num_variables + s.log_inv_rate - s.log_folding_factor) ≤ s.num_queries)

/-- BinaryPcsRegime::field_error_numerator: the fold and sumcheck errors over the challenge field size. -/
def BinaryPcsRegime.field_error_numerator (s : BinaryPcsRegime) : ℕ :=
  2 * 2 ^ (s.num_variables + s.log_inv_rate) - 2 * 2 ^ s.log_inv_rate + 3 * s.num_variables

/-- BinaryPcsRegime::field_security_bits: the field width less the bit length of the numerator minus one. -/
def BinaryPcsRegime.field_security_bits (s : BinaryPcsRegime) : ℕ :=
  s.challenge_field_bits - (Nat.log2 (s.field_error_numerator - 1) + 1)

/-- BinaryPcsRegime::max_security_bits: one bit is kept for the queries, unless they are exhaustive. -/
def BinaryPcsRegime.max_security_bits (s : BinaryPcsRegime) : ℕ :=
  s.field_security_bits - if s.queries_are_exhaustive then 0 else 1

/-! ## The parameters and the schedule -/

/-- BinaryPcsParams. -/
structure BinaryPcsParams where
  log_inv_rate : ℕ
  pow_bits : ℕ
  security_level : ℕ
  deriving DecidableEq

set_option linter.dupNamespace false in
/-- BinaryPcsConfig. -/
structure BinaryPcsConfig where
  params : BinaryPcsParams
  committed_field_bits : ℕ
  challenge_field_bits : ℕ
  num_variables : ℕ
  num_queries : ℕ
  log_folding_factor : ℕ
  deriving DecidableEq

/-- BinaryPcsConfigError. -/
inductive BinaryPcsConfigError where
  | InvalidFoldingFactor (requested num_variables : ℕ)
  | UnpricedChallengeField (bits : ℕ)
  | CodewordExceedsAlphabetDomain (log_len bits : ℕ)
  | CodewordLengthExceedsUsize (log_len max_bits : ℕ)
  | NoVariablesToFold
  | PowBitsExceedWitnessCapacity (requested max : ℕ)
  | SecurityLevelBelowPowBits (security_level pow_bits : ℕ)
  | SecurityLevelExceedsFieldCapacity (security_level max : ℕ)
  | ZeroQueries
  | CommittedFieldMismatch (derived actual : ℕ)
  | ChallengeFieldMismatch (derived actual : ℕ)
  deriving DecidableEq

namespace BinaryPcsConfig

variable (c : BinaryPcsConfig)

/-- try_security_regime: the model of the schedule, or the challenge width it declines. -/
def try_security_regime : Except BinaryPcsConfigError BinaryPcsRegime :=
  match BinaryPcsRegime.new c.challenge_field_bits c.num_variables c.params.log_inv_rate
      c.log_folding_factor c.num_queries c.params.pow_bits with
  | some s => .ok s
  | none => .error (.UnpricedChallengeField c.challenge_field_bits)

/-- security_regime: the model of the schedule, which panics when there is none. -/
def security_regime : Option BinaryPcsRegime :=
  match c.try_security_regime with
  | .ok s => some s
  | .error _ => none

/-- validate_security: the target must not exceed what the field leaves. -/
def validate_security : Option (Except BinaryPcsConfigError Unit) := do
  let max := (← c.security_regime).max_security_bits
  pure (if c.params.security_level > max then
    .error (.SecurityLevelExceedsFieldCapacity c.params.security_level max) else .ok ())

/-- num_fold_batches: the fold batches, the last one included, which panics at a zero factor. -/
def num_fold_batches : Option ℕ :=
  if c.log_folding_factor = 0 then none
  else some ((c.num_variables + c.log_folding_factor - 1) / c.log_folding_factor)

/-- fold_batches: each batch's first variable and challenge count; a zero step panics. -/
def fold_batches : Option (List (ℕ × ℕ)) :=
  if c.log_folding_factor = 0 then none
  else some (((List.range c.num_variables).filter (· % c.log_folding_factor = 0)).map
    fun start => (start, min c.log_folding_factor (c.num_variables - start)))

/-- num_fold_rounds: one fold per variable. -/
def num_fold_rounds : ℕ := c.num_variables

/-- log_final_len. -/
def log_final_len : ℕ := c.params.log_inv_rate

/-- log_domain_size. -/
def log_domain_size : ℕ := c.num_variables + c.params.log_inv_rate

/-- domain_size: one shifted left by the log length, which panics at a shift of a word or more. -/
def domain_size : Option ℕ :=
  if c.log_domain_size < USIZE_BITS then some (2 ^ c.log_domain_size) else none

/-- try_with_folding: a new factor, checked against the variables and the security target. -/
def try_with_folding (lff : ℕ) : Option (Except BinaryPcsConfigError BinaryPcsConfig) :=
  if lff = 0 ∨ lff > c.num_variables then
    some (.error (.InvalidFoldingFactor lff c.num_variables))
  else
    let c' := { c with log_folding_factor := lff }
    match c'.validate_security with
    | none => none
    | some (.error e) => some (.error e)
    | some (.ok ()) => some (.ok c')

/-- check_alphabets: the two widths must be those the schedule was derived for. -/
def check_alphabets (fBits efBits : ℕ) : Except BinaryPcsConfigError Unit :=
  if c.committed_field_bits ≠ fBits then .error (.CommittedFieldMismatch c.committed_field_bits fBits)
  else if c.challenge_field_bits ≠ efBits then .error (.ChallengeFieldMismatch c.challenge_field_bits efBits)
  else .ok ()

end BinaryPcsConfig

/-- try_new_with_folding: the schedule for `n` variables over levels of `fBits` and `efBits` bits.

`queries` is the query count p3-security derives from the target, the rate and the grinding bits. -/
def try_new_with_folding (queries : ℕ → ℕ → ℕ → ℕ) (fBits efBits n : ℕ) (params : BinaryPcsParams)
    (lff : ℕ) : Option (Except BinaryPcsConfigError BinaryPcsConfig) :=
  let log_len := min (n + params.log_inv_rate) (2 ^ USIZE_BITS - 1)
  if ¬ n + params.log_inv_rate < USIZE_BITS then
    some (.error (.CodewordLengthExceedsUsize log_len USIZE_BITS))
  else if n = 0 then some (.error .NoVariablesToFold)
  else if lff = 0 ∨ lff > n then some (.error (.InvalidFoldingFactor lff n))
  else if log_len > fBits then some (.error (.CodewordExceedsAlphabetDomain log_len fBits))
  else if min fBits POW_COUNTER_BITS < POW_HEADER_BITS then none
  else
    let max_pow_bits := min fBits POW_COUNTER_BITS - POW_HEADER_BITS
    if params.pow_bits > max_pow_bits then
      some (.error (.PowBitsExceedWitnessCapacity params.pow_bits max_pow_bits))
    else if params.security_level ≤ params.pow_bits then
      some (.error (.SecurityLevelBelowPowBits params.security_level params.pow_bits))
    else
      let num_queries := queries params.security_level params.log_inv_rate params.pow_bits
      if num_queries = 0 then some (.error .ZeroQueries)
      else
        let config : BinaryPcsConfig := ⟨params, fBits, efBits, n, num_queries, lff⟩
        match config.try_security_regime with
        | .error e => some (.error e)
        | .ok _ =>
          match config.validate_security with
          | none => none
          | some (.error e) => some (.error e)
          | some (.ok ()) => some (.ok config)

/-- try_new: the schedule that commits after every fold. -/
def try_new (queries : ℕ → ℕ → ℕ → ℕ) (fBits efBits n : ℕ) (params : BinaryPcsParams) :
    Option (Except BinaryPcsConfigError BinaryPcsConfig) :=
  try_new_with_folding queries fBits efBits n params 1

end p3_binary_pcs.params.mirror
