/-
Transcriptions of the circle PCS prover's open path: the DEEP quotients, the lambda extraction, the first layer, the circle FRI commit phase, and the query answers.

What a transcription abstracts, beyond the models of the verifier:

- the base field and its extension are one mathlib field K, base values read through their embedding
- the commitment schemes' methods are fields of records, as in p3-fri's model
- the Lagrange denominators, cached per height and point, are recomputed, which gives the cached values
- a matrix opened at two points is read once for both, which gives the two single-point evaluations
- the first rows of a matrix are the matrix cut to that height
- a wide matrix's reduction through the lifted transform is the plain row reduction, which the crate tests it equals
- the domain's points through the parallel chain are its points, in natural order
- a map keyed by height is a function of the height and its list of keys, read in increasing order
- the prover's transcript is a record of its four phases, with explicit state, each returning its challenge and its grinding witness
- the transcript's description is left out: the run follows it, since both come from the same claims
- the circle FRI arity is 2, which the prover asserts
- a usize is a natural number, and a subtraction below zero panics
- an assertion panics, and a debug assertion is checked, as in a debug build
- a panic is none.

Loops, branches and early returns are kept.
-/
module

public import P3Circle.Pcs

@[expose] public section

namespace p3_circle.prover.mirror

open p3_dft.mirror p3_fri.mirror p3_fri.config.mirror p3_commit.pcs.univariate.mirror
open p3_commit.domain.mirror p3_circle.point.mirror p3_circle.domain.mirror p3_circle.ordering.mirror
open p3_circle.folding.mirror p3_circle.deep_quotient.mirror p3_circle.verifier.mirror p3_circle.pcs.mirror

/-- The prover's circle PCS transcript, as its four phases:

- the claims and the batching grind, which return the batching challenge and the witness
- the first-layer commitment, which returns the bivariate challenge
- a commit round and its grind, which return the folding challenge and the witness
- the final constant and the query grind, which return the query indices and the witness.

A grind at difficulty zero returns no witness. -/
structure CircleProverTx (K Com S : Type _) where
  batch_phase : S → List (Point K × List K) → K × Option K × S
  first_layer : S → Com → K × S
  commit_round : S → Com → K × Option K × S
  query_phase : S → K → List ℕ × Option K × S

variable {K : Type _} [Field K] [DecidableEq K]

/-- The rows of a matrix. -/
def rowsOf (m : Mat K) : List (List K) :=
  (List.range m.height).map fun r => (List.finRange m.width).map (m.entry r)

/-- A vector read as a matrix of width 2. -/
def matOfPairs (v : List K) : Mat K := ⟨v.length / 2, 2, fun r c => v.getD (2 * r + c.val) 0⟩

/-- The rows of a matrix of width 2, as pairs. -/
def pairsOf (m : Mat K) : List (K × K) :=
  (List.range m.height).map fun r => (if h : 0 < m.width then m.entry r ⟨0, h⟩ else 0,
    if h : 1 < m.width then m.entry r ⟨1, h⟩ else 0)

/-- The Lagrange denominators of the points toward a point: ((at - p).x + 1) / ((at - p).y s_i).

Here s_i is the selector normalizer of the shift at an even index i, and its negation at an odd one.

It debug-asserts:

- 2^log_n points
- that the normalizer of the point is s_i at the indices 0, 1, n - 2 and n - 1.

A zero denominator panics in the batch inversion. -/
def compute_lagrange_den_on_domain (points : List (Point K)) (at_ : Point K) (domain : CircleDomain K) :
    Option (List K) := do
  let n := points.length
  if n ≠ 2 ^ domain.log_n then none
  let s_p_at_shift ← Point.s_p_at_p domain.shift domain.log_n
  let s_p_at_index := fun (i : ℕ) => if i % 2 = 0 then s_p_at_shift else -s_p_at_shift
  if n < 2 then none
  let ok ← [0, 1, n - 2, n - 1].allM fun i => do
    let p ← points[i]?
    let s ← Point.s_p_at_p p domain.log_n
    pure (decide (s = s_p_at_index i))
  if !ok then none
  let diffs := points.zipIdx.map fun (pt, i) =>
    let diff := Point.sub at_ pt
    (diff.x + 1, diff.y * s_p_at_index i)
  let inv_d ← batchInv (diffs.map (·.2))
  pure (List.zipWith (· * ·) (diffs.map (·.1)) inv_d)

/-- The columns at a point, from the Lagrange denominators: v_D(point) times sum_r den_r row_r.

It asserts one denominator per row. -/
def evaluate_at_point_with_den (domain : CircleDomain K) (m : Mat K) (point : Point K) (den : List K) :
    Option (List K) := do
  let num ← CircleDomain.vanishing_poly domain point
  if den.length ≠ m.height then none
  pure ((List.finRange m.width).map fun c =>
    ((List.range m.height).map fun r => den.getD r 0 * m.entry r c).sum * num)

variable (G : Gen (K × K))

/-- The domain points of height h, in circle FFT order. -/
def permutedPoints (h : ℕ) : Option (List (Point K)) := do
  let d ← CircleDomain.standard G h
  let pts ← CircleDomain.points G d
  cfft_permute_slice pts

/-- The opened values of one matrix at its points.

The evaluation reads the first 2^(log_height - log_blowup) rows.

They hold the LDE on the twin coset of the trace size with the LDE's shift.

Its points are the first points of the LDE domain in circle FFT order. -/
def openMatrix (log_blowup : ℕ) (mat : Mat K) (points : List K) : Option (List (List K)) := do
  let log_height ← log2Strict mat.height
  let pts ← permutedPoints G log_height
  if log_height < log_blowup then none
  let log_sub := log_height - log_blowup
  let sub_height := 2 ^ log_sub
  let std ← CircleDomain.standard G log_height
  let sub_domain := CircleDomain.new log_sub std.shift
  let evals : Mat K := ⟨sub_height, mat.width, mat.entry⟩
  points.mapM fun t => do
    let zeta ← Point.from_projective_line t
    let den ← compute_lagrange_den_on_domain (pts.take sub_height) zeta sub_domain
    evaluate_at_point_with_den sub_domain evals zeta den

/-- The opened values of every matrix of every round.

It asserts one point list per matrix. -/
def openedValues (log_blowup : ℕ) (rounds : List (List (Mat K) × List (List K))) :
    Option (List (List (List (List K)))) :=
  rounds.mapM fun r => do
    if r.1.length ≠ r.2.length then none
    (r.1.zip r.2).mapM fun mp => openMatrix G log_blowup mp.1 mp.2

/-- Add one matrix's DEEP quotients to the reduced openings of its height.

The map holds, at each height, the running power of alpha and the reduced column. -/
def accumulateMatrix (alpha : K) (st : (ℕ → K × List K) × List ℕ)
    (mv : Mat K × List K × List (List K)) : Option ((ℕ → K × List K) × List ℕ) := do
  let (acc, keys) := st
  let (mat, points, values) := mv
  let log_height ← log2Strict mat.height
  let entry := if log_height ∈ keys then acc log_height else (1, List.replicate (2 ^ log_height) 0)
  let keys := if log_height ∈ keys then keys else keys ++ [log_height]
  let reduced_rows := rowwise_alpha_reduce (rowsOf mat) alpha
  let alpha_pow_width := alpha ^ mat.width
  let pts ← permutedPoints G log_height
  let entry ← (points.zip values).foldlM (fun (e : K × List K) pv => do
      let zeta ← Point.from_projective_line pv.1
      let vp ← compute_vanishing_parts pts zeta
      let reduced_ps_at_zeta := dot_product ((List.range pv.2.length).map (alpha ^ ·)) pv.2
      pure (e.1 * alpha_pow_width ^ 2,
        accumulate_deep_quotient e.2 e.1 alpha_pow_width reduced_rows vp reduced_ps_at_zeta)) entry
  pure (Function.update acc log_height entry, keys)

/-- The reduced openings of every height. -/
def reducedOpenings (alpha : K) (rounds : List (List (Mat K) × List (List K)))
    (values : List (List (List (List K)))) : Option ((ℕ → K × List K) × List ℕ) :=
  ((rounds.zip values).flatMap fun rv => (rv.1.1.zip (rv.1.2.zip rv.2)).map fun m => (m.1, m.2.1, m.2.2)).foldlM
    (accumulateMatrix G alpha) (fun _ => (1, []), [])

/-- The lambda of every height, increasing, and its corrected column.

It asserts a nonzero height. -/
def extractLambdas (log_blowup : ℕ) (ro : ℕ → K × List K) (log_heights : List ℕ) :
    Option (List (ℕ × K × List K)) :=
  log_heights.mapM fun h => do
    if h = 0 then none
    let (lambda, col) ← extract_lambda G (ro h).2 log_blowup
    pure (h, lambda, col)

/-- One commit round of circle FRI.

It commits the vector as rows of two, draws beta, folds along x, and adds the next input of the folded length. -/
def commitRound (fmmcs : MmcsOps K) {S : Type _} (tx : CircleProverTx K fmmcs.Commitment S)
    (st : List K × List (List K) × List fmmcs.Commitment × List fmmcs.ProverData × List K × S) :
    Option (List K × List (List K) × List fmmcs.Commitment × List fmmcs.ProverData × List K × S) := do
  let (folded, rest, commits, data, ws, s) := st
  let (commit, prover_data) := fmmcs.commit [matOfPairs folded]
  let (beta, witness, s') := tx.commit_round s commit
  let leaves ← (fmmcs.get_matrices prover_data).getLast?
  let folded' ← fold_x G beta 1 (pairsOf leaves)
  let (folded'', rest') := match rest with
    | v :: rest' => if v.length = folded'.length then (List.zipWith (· + ·) folded' v, rest') else (folded', rest)
    | [] => (folded', [])
  pure (folded'', rest', commits ++ [commit], data ++ [prover_data], ws ++ [witness.getD 0], s')

/-- The commit phase: fold while the vector is longer than the blowup, then read the final constant.

It asserts that the last vector has the blowup's length and is constant. -/
def commitPhase (fmmcs : MmcsOps K) {S : Type _} (tx : CircleProverTx K fmmcs.Commitment S) (log_blowup : ℕ)
    (inputs : List (List K)) (s : S) :
    Option (List fmmcs.Commitment × List fmmcs.ProverData × List K × K × S) := do
  match inputs with
  | [] => none
  | first :: rest => do
    let log_first ← log2Strict first.length
    let (folded, _, commits, data, ws, s') ← (List.range (log_first - log_blowup)).foldlM
      (fun st _ => commitRound G fmmcs tx st) (first, rest, [], [], [], s)
    if folded.length ≠ 2 ^ log_blowup then none
    let final ← folded.head?
    if folded.any (· ≠ final) then none
    pure (commits, data, ws, final, s')

/-- The query answers of the commit phase: each round's group, opened once, without the queried value. -/
def answerQueries (fmmcs : MmcsOps K) (data : List fmmcs.ProverData) (start_indices : List ℕ) :
    Option (List (CommitPhaseMultiStep K fmmcs.MultiProof)) := do
  let (_, out) ← data.foldlM (fun (st : List ℕ × List (CommitPhaseMultiStep K fmmcs.MultiProof)) pd => do
      let (current, acc) := st
      let group_indices := current.map (· / 2)
      let (opened_rows, opening_proof) := fmmcs.open_multi_batch group_indices pd
      let siblings ← (current.zip opened_rows).mapM fun (index, rows) =>
        match rows with
        | [row] => if row.length ≠ 2 then none else some ((row.zipIdx.filter fun p => p.2 ≠ index % 2).map Prod.fst)
        | _ => none
      pure (group_indices, acc ++ [⟨siblings, opening_proof⟩]))
    (start_indices, [])
  pure out

/-- The input openings, per round: the indices shifted down to the batch's tallest height, opened once. -/
def openInputs (immcs : MmcsOps K) (log_max_height : ℕ) (indices : List ℕ) (data : List immcs.ProverData) :
    Option (List (BatchMultiOpening K immcs.MultiProof)) :=
  data.mapM fun pd => do
    let h ← ((immcs.get_matrices pd).map Mat.height).max?
    let log_max_batch_height ← log2Strict h
    if log_max_height < log_max_batch_height then none
    let (opened_values, opening_proof) :=
      immcs.open_multi_batch (indices.map (· / 2 ^ (log_max_height - log_max_batch_height))) pd
    pure ⟨opened_values, opening_proof⟩

/-- The first-layer siblings: at each query and height, the other member of the opened pair. -/
def firstLayerSiblings (log_max_height : ℕ) (log_heights : List ℕ) (indices : List ℕ)
    (values : List (List (List K))) : List (List K) :=
  (indices.zip values).map fun iv => (iv.2.zip log_heights).map fun vh =>
    vh.1.getD (1 - (iv.1 / 2 ^ (log_max_height - vh.2)) % 2) 0

/-- The prover's opening of the committed matrices at their points.

It opens every matrix, batches the claims, reduces them as DEEP quotients by height, extracts the lambdas,
commits and folds the first layer, runs circle FRI, and answers the queries.

Circle FRI asserts arity 2, at least one query and a positive blowup, and inputs of non-increasing lengths. -/
def open_ (immcs fmmcs : MmcsOps K) {S : Type _} (tx : CircleProverTx K fmmcs.Commitment S) (params : FriParameters)
    (rounds : List (immcs.ProverData × List (List K)))
    (s : S) :
    Option (List (List (List (List K))) × CirclePcsProof K fmmcs.Commitment immcs.MultiProof fmmcs.MultiProof) := do
  let log_blowup := params.log_blowup
  let mrounds := rounds.map fun r => (immcs.get_matrices r.1, r.2)
  let values ← openedValues G log_blowup mrounds
  let log_max_height ← (mrounds.flatMap fun r => r.1.map Mat.height).max? >>= log2Strict
  let claims ← (mrounds.zip values).flatMap (fun rv => (rv.1.2.zip rv.2).flatMap fun pv =>
      pv.1.zip pv.2) |>.mapM fun tv => (Point.from_projective_line tv.1).map fun z => (z, tv.2)
  let (alpha, batch_pow_witness, s1) := tx.batch_phase s claims
  let (ro, keys) ← reducedOpenings G alpha mrounds values
  let log_heights := keys.mergeSort (fun a b => decide (a ≤ b))
  let per_height ← extractLambdas G log_blowup ro log_heights
  let (first_layer_commitment, first_layer_data) := fmmcs.commit (per_height.map fun e => matOfPairs e.2.2)
  let (bivariate_beta, s2) := tx.first_layer s1 first_layer_commitment
  let fri_input ← (fmmcs.get_matrices first_layer_data).mapM fun m => fold_y G bivariate_beta (pairsOf m)
  if params.max_log_arity ≠ 1 ∨ params.num_queries = 0 ∨ params.log_blowup = 0 then none
  if ¬ fri_input.reverse.IsChain (fun l r => r.length ≤ l.length) then none
  let (commits, data, ws, final, s3) ← commitPhase G fmmcs tx log_blowup fri_input.reverse s2
  let (indices, pow_witness, _) := tx.query_phase s3 final
  let input_openings ← openInputs immcs log_max_height indices (rounds.map (·.1))
  let (first_layer_values, first_layer_proof) := fmmcs.open_multi_batch (indices.map (· / 2)) first_layer_data
  let first_layer_siblings := firstLayerSiblings log_max_height log_heights indices first_layer_values
  let commit_phase_openings ← answerQueries fmmcs data (indices.map (· / 2))
  pure (values, ⟨batch_pow_witness.getD 0, first_layer_commitment, per_height.map (·.2.1),
    ⟨commits, ws, ⟨input_openings, first_layer_siblings, first_layer_proof⟩, commit_phase_openings, final,
      pow_witness.getD 0⟩⟩)

end p3_circle.prover.mirror
