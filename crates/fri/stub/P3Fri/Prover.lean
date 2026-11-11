/-
Transcriptions of the FRI prover.

They cover the commit phase, the query answers, the input openings, and the full prover.

What a transcription abstracts, beyond Fold.lean and Types.lean:

* the folding strategy is the two-adic one, which samples no extra index bits
* the inverse DFT of the final polynomial is a parameter, proved to be the inverse transform in p3-dft
* the committed matrix of a round is the flat folded vector read with width 2^log_arity
* a parallel loop whose items write disjoint outputs runs its items in order
* an assertion panics, and a debug assertion is checked, as in a debug build
* a panic is none, and a returned error is an error.

Loops, branches and early returns are kept.
-/
module

public import P3Fri.Config
public import P3Fri.Fold
public import P3Fri.Types

@[expose] public section

namespace p3_fri.prover.mirror

open p3_dft.mirror p3_commit.pcs.univariate.mirror p3_fri.mirror p3_fri.config.mirror
open p3_fri.two_adic_pcs.mirror

variable {K : Type} [Field K] [DecidableEq K]

/-- A flat vector read as a matrix of the given width. -/
def matOfFlat (v : List K) (w : ℕ) : Mat K := ⟨v.length / w, w, fun r c => v.getD (r * w + c.val) 0⟩

/-- The entries of a matrix, row after row. -/
def flatOfMat (m : Mat K) : List K :=
  (List.range m.height).flatMap fun r => (List.finRange m.width).map (m.entry r)

/-- What the commit phase returns.

It holds the commitments, prover data, arities, witnesses and final polynomial. -/
structure CommitPhaseResult (K C PD : Type _) where
  commits : List C
  data : List PD
  log_arities : List ℕ
  pow_witnesses : List K
  final_poly : List K

/-- The fold that a round applies.

It is the matrix fold at the packing width W and field width, with any scratch buffer. -/
structure Folder (K : Type _) where
  fold : K → ℕ → List K → Option (List K)

/-- One commit round.

It commits the vector at width 2^log_arity, draws beta, and folds.
It then adds the next input of the folded length, scaled by beta^(2^log_arity). -/
def commitRound (mmcs : MmcsOps K) {S : Type _} (tx : ProverTx K mmcs.Commitment S) (folder : Folder K)
    (log_arity : ℕ)
    (st : List K × List (List K) × List mmcs.Commitment × List mmcs.ProverData × List K × S) :
    Option (List K × List (List K) × List mmcs.Commitment × List mmcs.ProverData × List K × S) := do
  let (folded, rest, commits, data, ws, s) := st
  let arity := 2 ^ log_arity
  if folded.length % arity ≠ 0 then none
  else
    let leaves := matOfFlat folded arity
    let (commit, prover_data) := mmcs.commit [leaves]
    let (beta, witness, s') := tx.commit_round s commit
    let leaves' ← (mmcs.get_matrices prover_data).getLast?
    let folded' ← folder.fold beta log_arity (flatOfMat leaves')
    let (folded'', rest') := match rest with
      | v :: rest' =>
        if v.length = folded'.length then
          (List.zipWith (fun c x => c + beta ^ 2 ^ log_arity * x) folded' v, rest')
        else (folded', rest)
      | [] => (folded', [])
    some (folded'', rest', commits ++ [commit], data ++ [prover_data], ws ++ [witness.getD 0], s')

/-- The commit rounds of the schedule, then the final polynomial.

It keeps the first final_poly_len folded values, un-bit-reverses them and inverse-transforms them. -/
def commit_phase (mmcs : MmcsOps K) {S : Type _} (tx : ProverTx K mmcs.Commitment S) (folder : Folder K)
    (idft : List K → List K) (params : FriParameters) (inputs : List (List K)) (log_arities : List ℕ)
    (s : S) : Option (CommitPhaseResult K mmcs.Commitment mmcs.ProverData × S) := do
  if params.max_log_arity = 0 then none
  else match inputs with
    | [] => none
    | first :: rest => do
      let (folded, _, commits, data, ws, s') ← log_arities.foldlM
        (fun st la => commitRound mmcs tx folder la st) (first, rest, [], [], [], s)
      let truncated := folded.take params.final_poly_len
      some (⟨commits, data, log_arities, ws, idft (revIndex truncated.length truncated)⟩, s')

/-- The query answers, per round:

- each query's group
- one shared opening of those groups
- each group without the queried value. -/
def answer_queries (mmcs : MmcsOps K) (log_arities : List ℕ) (data : List mmcs.ProverData)
    (start_indices : List ℕ) : Option (List (CommitPhaseMultiStep K mmcs.MultiProof)) := do
  let (_, out) ← (data.zipIdx).foldlM (fun (st : List ℕ × List (CommitPhaseMultiStep K mmcs.MultiProof)) e => do
      let (current, acc) := st
      let log_arity ← log_arities[e.2]?
      let arity := 2 ^ log_arity
      let group_indices := current.map (· / arity)
      let (opened_rows, opening_proof) := mmcs.open_multi_batch group_indices e.1
      let siblings ← (current.zip opened_rows).mapM fun (index, rows) =>
        match rows with
        | [row] =>
          if row.length ≠ arity then none
          else some ((row.zipIdx.filter fun p => p.2 ≠ index % arity).map Prod.fst)
        | _ => none
      some (group_indices, acc ++ [⟨siblings, opening_proof⟩]))
    (start_indices, [])
  some out

/-- The input openings, per batch.

The indices are shifted down to the batch's tallest height and share one opening. -/
def open_inputs (mmcs : MmcsOps K) (log_global_max_height : ℕ) (indices : List ℕ)
    (data : List mmcs.ProverData) : Option (List (BatchMultiOpening K mmcs.MultiProof)) :=
  data.mapM fun pd => do
    let h ← ((mmcs.get_matrices pd).map Mat.height).max?
    let log_max_height ← log2Strict h
    if log_global_max_height < log_max_height then none
    else
      let bits_reduced := log_global_max_height - log_max_height
      let (opened_values, opening_proof) :=
        mmcs.open_multi_batch (indices.map (· / 2 ^ bits_reduced)) pd
      some ⟨opened_values, opening_proof⟩

/-- The prover at the derived schedule.

It runs the assertions, the height preflight, the commit phase, the query phase, and the openings. -/
def prove_fri (fmmcs : MmcsOps K) (immcs : MmcsOps K) {S : Type _} (tx : ProverTx K fmmcs.Commitment S)
    (folder : Folder K) (idft : List K → List K) (params : FriParameters) (inputs : List (List K))
    (log_global_max_height : ℕ) (input_data : List immcs.ProverData) (batch_pow_witness : K) (s : S) :
    Option (Except FriProverError (FriProof K fmmcs.Commitment fmmcs.MultiProof immcs.MultiProof × S)) := do
  if inputs = [] then none
  else if params.num_queries = 0 ∨ params.log_blowup = 0 ∨ params.max_log_arity = 0 then none
  else if ¬ inputs.IsChain (fun l r => r.length ≤ l.length) then none
  else do
    let log_first ← log2Strict (inputs.headD []).length
    if log_global_max_height ≠ log_first then none
    else do
      let log_min ← log2Strict (inputs.getLastD []).length
      match params.validate_input_height log_min with
      | .error e => some (.error e)
      | .ok () => do
        let input_log_heights ← inputs.mapM fun v => log2Strict v.length
        let log_arities ← fold_schedule input_log_heights
          (params.log_blowup + params.log_final_poly_len) params.max_log_arity
        let (cp, s1) ← commit_phase fmmcs tx folder idft params inputs log_arities s
        let (indices, pow_witness, s2) := tx.query_phase s1 cp.final_poly
        let input_openings ← open_inputs immcs log_global_max_height indices input_data
        let commit_phase_openings ← answer_queries fmmcs cp.log_arities cp.data indices
        some (.ok (⟨batch_pow_witness, cp.commits, cp.pow_witnesses, input_openings,
          commit_phase_openings, cp.final_poly, pow_witness.getD 0⟩, s2))

end p3_fri.prover.mirror
