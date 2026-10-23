/-
Transcriptions of the FRI parameters, the per-round arity and the folding schedule.

What a transcription abstracts:

* a usize is a natural number, and a checked addition fails when the sum reaches 2^64;
* the testing and benchmark constructors, the security mirror and the MMCS field are left out;
* an assertion panics, and a debug assertion is checked, as in a debug build;
* a panic is none.

Loops, branches and early returns are kept.
-/
module

public import Mathlib.Data.List.Basic
public import Mathlib.Order.Basic

@[expose] public section

namespace p3_fri.config.mirror

/-- The parameters of one FRI instance, without the commitment scheme. -/
structure FriParameters where
  log_blowup : ℕ
  log_final_poly_len : ℕ
  max_log_arity : ℕ
  num_queries : ℕ
  batch_proof_of_work_bits : ℕ
  commit_proof_of_work_bits : ℕ
  query_proof_of_work_bits : ℕ

/-- The reasons a prover input cannot be folded to the terminal size. -/
inductive FriProverError where
  | InputHeightTooSmall (log_input_height log_final_height : ℕ)
  | FinalHeightOverflow
  deriving DecidableEq

namespace FriParameters

/-- The final polynomial length, 2^log_final_poly_len. -/
def final_poly_len (p : FriParameters) : ℕ := 2 ^ p.log_final_poly_len

/-- The blowup, 2^log_blowup. -/
def blowup (p : FriParameters) : ℕ := 2 ^ p.log_blowup

/-- The ethSTARK conjectured soundness: log_blowup * num_queries + query_proof_of_work_bits. -/
def conjectured_soundness_bits (p : FriParameters) : ℕ :=
  p.log_blowup * p.num_queries + p.query_proof_of_work_bits

/-- A constant final polynomial accepts every input height.

Otherwise the input must lie strictly above log_final_poly_len + log_blowup. -/
def validate_input_height (p : FriParameters) (log_input_height : ℕ) : Except FriProverError Unit :=
  if p.log_final_poly_len = 0 then .ok ()
  else
    let s := p.log_final_poly_len + p.log_blowup
    if 2 ^ 64 ≤ s then .error .FinalHeightOverflow
    else if log_input_height ≤ s then .error (.InputHeightTooSmall log_input_height s)
    else .ok ()

end FriParameters

/-- The smallest of the distance to the final height, the distance to the next input, and the cap.

It asserts a positive cap, and debug-asserts that the current height lies above the final height and the next input. -/
def compute_log_arity_for_round (log_current_height : ℕ) (next_input_log_height : Option ℕ)
    (log_final_height max_log_arity : ℕ) : Option ℕ :=
  if max_log_arity = 0 then none
  else if log_current_height ≤ log_final_height then none
  else
    let max_fold_to_target := log_current_height - log_final_height
    match next_input_log_height with
    | none => some (min max_fold_to_target max_log_arity)
    | some next =>
      if log_current_height ≤ next then none
      else some (min (min (log_current_height - next) max_fold_to_target) max_log_arity)

/-- One round of the schedule loop, with fuel: push the round's arity, descend, and roll in an input the descent reached. -/
def fold_schedule_loop (heights : List ℕ) (log_final_height max_log_arity : ℕ) :
    ℕ → ℕ → ℕ → List ℕ → Option (List ℕ)
  | 0, _, _, acc => some acc
  | fuel + 1, log_height, next_input, acc =>
    if log_height ≤ log_final_height then some acc
    else do
      let log_arity ← compute_log_arity_for_round log_height heights[next_input]?
        log_final_height max_log_arity
      let log_height' := log_height - log_arity
      let next_input' := if heights[next_input]? = some log_height' then next_input + 1 else next_input
      fold_schedule_loop heights log_final_height max_log_arity fuel log_height' next_input'
        (acc ++ [log_arity])

/-- The log-arities of every round, from the tallest input down to the final height.

It asserts strictly decreasing heights.
The loop runs while the height lies above the final height; the fuel, the tallest height, is never the bound that stops it. -/
def fold_schedule (heights : List ℕ) (log_final_height max_log_arity : ℕ) : Option (List ℕ) :=
  if ¬ heights.IsChain (· > ·) then none
  else match heights with
    | [] => some []
    | tallest :: _ =>
      if tallest ≤ log_final_height then some []
      else fold_schedule_loop heights log_final_height max_log_arity tallest tallest 1 []

end p3_fri.config.mirror
