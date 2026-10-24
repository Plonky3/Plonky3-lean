/-
Transcription of the integer schedule of WhirConfig::new_with_max_domain_log, parameters/whir.rs.

The folding schedule is the derived one, an input.

The query, out-of-domain and grinding counts come from p3-security's floating-point bounds.

They are inputs, as functions of the round and the rates.
-/
module

public import P3Whir.Verifier

@[expose] public section

namespace p3_whir.parameters.mirror

open p3_whir.mirror

/-- The errors of the integer schedule. -/
inductive WhirConfigError where
  | NonRedundantStartingRate
  | InitialDomainExceedsUsize
  | FoldedDomainExceedsCapacity (log_folded_domain_size max_log_domain_size : ℕ)
  | RoundRateCountMismatch (expected actual : ℕ)
  | NonRedundantRoundRate (round log_inv_rate : ℕ)
  | RateGrowsDomain (round : ℕ)
  deriving DecidableEq

/-- The counts the floating-point bounds give.

They are per round, from the rates and the variable count. -/
structure Counts where
  queries : ℕ → ℕ
  ood : ℕ → ℕ → ℕ
  pow : ℕ → ℕ
  folding_pow : ℕ → ℕ
  starting_folding_pow : ℕ
  final_pow : ℕ
  final_folding_pow : ℕ

/-- The state of the round loop:

- the rounds so far
- the variables left
- the rate
- the domain size. -/
structure LoopState where
  rounds : List RoundConfig
  num_variables : ℕ
  log_inv_rate : ℕ
  domain_size : ℕ

/-- One iteration of the round loop. -/
def roundStep (cs : Counts) (folding : List ℕ) (st : LoopState) (e : ℕ × ℕ) :
    Except WhirConfigError LoopState :=
  let (round, next_rate) := e
  let folding_factor := folding.getD round 0
  if next_rate > st.log_inv_rate + folding_factor then throw (.RateGrowsDomain round)
  else
    let rs_reduction_factor := st.log_inv_rate + folding_factor - next_rate
    let params : RoundConfig := ⟨cs.pow round, cs.folding_pow round, cs.queries st.log_inv_rate,
      cs.ood st.num_variables next_rate, st.num_variables, folding_factor, st.domain_size,
      Nat.log 2 st.domain_size - folding_factor⟩
    pure ⟨st.rounds ++ [params], st.num_variables - folding.getD (round + 1) 0, next_rate,
      st.domain_size >>> rs_reduction_factor⟩

/-- WhirConfig::final_round_config: the codeword the final queries open.

It comes after the last round's domain reduction. -/
def finalRoundConfig (cs : Counts) (n rate0 : ℕ) (folding : List ℕ) (rounds : List RoundConfig)
    (rates : List ℕ) : RoundConfig :=
  match rounds.getLast? with
  | none =>
    ⟨cs.final_pow, cs.final_folding_pow, cs.queries rate0, 0, n - folding.getD 0 0, folding.getD 0 0,
      2 ^ (n + rate0), Nat.log 2 (2 ^ (n + rate0)) - folding.getD 0 0⟩
  | some last =>
    let r := rounds.length - 1
    let previous := if r = 0 then rate0 else rates.getD (r - 1) 0
    let rs := previous + folding.getD r 0 - rates.getD r 0
    let k := folding.getD rounds.length 0
    let domain_size := last.domain_size >>> rs
    ⟨cs.final_pow, cs.final_folding_pow, cs.queries (rates.getD r 0), 0, last.num_variables - k, k,
      domain_size, Nat.log 2 domain_size - k⟩

/-- new_with_max_domain_log, its integer part, in order:

- the rate and domain checks
- the first-fold capacity check
- the rounds. -/
def schedule (cs : Counts) (n rate0 : ℕ) (folding rates : List ℕ) (max_log : ℕ) :
    Except WhirConfigError WhirConfig := do
  if rate0 = 0 then throw .NonRedundantStartingRate
  let log_domain_size := n + rate0
  if 64 ≤ log_domain_size then throw .InitialDomainExceedsUsize
  let log_folded_domain_size := log_domain_size - folding.getD 0 0
  if log_folded_domain_size > max_log then
    throw (.FoldedDomainExceedsCapacity log_folded_domain_size max_log)
  let num_rounds := folding.length - 1
  if rates.length ≠ num_rounds then throw (.RoundRateCountMismatch num_rounds rates.length)
  match rates.findIdx? (· = 0) with
  | some round => throw (.NonRedundantRoundRate round 0)
  | none =>
    let st ← (rates.zipIdx.map fun e => (e.2, e.1)).foldlM (roundStep cs folding)
      ⟨[], n - folding.getD 0 0, rate0, 2 ^ log_domain_size⟩
    pure
      { round_parameters := st.rounds
        folding_schedule := folding
        starting_folding_pow_bits := cs.starting_folding_pow
        final_sumcheck_rounds := n - folding.sum
        final_folding_pow_bits := cs.final_folding_pow
        terminal_num_queries := cs.queries st.log_inv_rate
        terminal_pow_bits := cs.final_pow
        final_round_config := finalRoundConfig cs n rate0 folding st.rounds rates
        stratified_queries := false }

end p3_whir.parameters.mirror
