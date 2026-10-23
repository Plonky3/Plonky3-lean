/-
Transcriptions of p3-stir's verifier (stir/src/verifier.rs): the virtual oracle, the query folds, the answer-polynomial checks and the final check.

A verifier step returns in ExceptT StirError Option: none is a panic, an error is a rejection.

The MMCS check of the opened rows is the predicate mmcs_ok, which the merkle-tree crate's claims are about.

The transcript is not modelled here: its challenges are inputs.
-/
module

public import P3Stir.Utils

@[expose] public section

namespace p3_stir.verifier.mirror

open p3_stir.mirror p3_stir.utils.mirror p3_dft.mirror

/-- The rejections the transcribed steps can raise.

A round is a natural number, and the final round is none. -/
inductive StirError where
  | AnsPolynomialTooLong (round : ℕ) (maximum got : ℕ)
  | MissingAnsPolynomial (round : ℕ) (nodes : ℕ)
  | UnexpectedAnsPolynomial (round : ℕ) (got : ℕ)
  | InvalidAnsConsistency (round : ℕ)
  | InvalidRoundConsistency (round : Option ℕ) (query : ℕ)
  | FinalPolyMismatch
  | FiberCount (round : Option ℕ) (expected got : ℕ)
  | FiberArity (round : Option ℕ) (fiber expected got : ℕ)
  | UnexpectedQueryOpenings (round : Option ℕ)
  | MissingQueryOpenings (round : Option ℕ)
  | QueryOpeningCount (round : Option ℕ) (expected got : ℕ)
  | OpenedRowArity (round : Option ℕ) (query expected got : ℕ)
  | MissingCommitment (round : Option ℕ)
  | InvalidMmcsProof (round : Option ℕ)
  deriving DecidableEq

/-- A verifier step: none is a panic, an error a rejection. -/
abbrev VM := ExceptT StirError Option

/-- Raise a panic inside a verifier step. -/
def panic {α : Type} : VM α := ExceptT.lift none

/-- Lift a computation that may panic. -/
def liftO {α : Type} (o : Option α) : VM α := ExceptT.lift o

variable {F EF : Type _} [Field F] [Field EF] [Algebra F EF] [DecidableEq F] [DecidableEq EF]

/-- An extension element times a base element. -/
local infixl:70 " ⋆ " => fun (a : EF) (b : F) => a * algebraMap F EF b

/-- VirtualRoundContext: what the next round needs to read the virtual oracle DegCor((g - Ans) / Z). -/
structure VirtualRoundContext (EF : Type _) where
  ans_poly : List EF
  vanishing_coeffs : List EF
  r_comb : EF
  gap : ℕ
  r_comb_pow_gap1 : EF

/-- materialize_virtual_fiber: the opened row read through DegCor((g - Ans) / Z) at the fiber points shift u_l.

The inner none is a fiber that meets the round's interpolation nodes. -/
def materialize_virtual_fiber (row_evals : List EF) (subgroup_points : List F) (shift : F)
    (prev_ctx : Option (VirtualRoundContext EF)) : Option (Option (List EF)) :=
  match prev_ctx with
  | none => some (some row_evals)
  | some ctx => do
    let arity := row_evals.length
    let points := subgroup_points.map (shift * ·)
    let p0 ← points.head?
    let common_power := p0 ^ arity
    let gap := ctx.gap
    let ans_rem ← reduce_mod_x_pow_minus_c ctx.ans_poly arity common_power
    let vanishing_rem ← reduce_mod_x_pow_minus_c ctx.vanishing_coeffs arity common_power
    let denoms := points.map fun x => eval_poly_at_base vanishing_rem x
    if (0 : EF) ∈ denoms then some none
    else do
      let steps := points.map fun x => ctx.r_comb ⋆ x
      let denoms := List.zipWith (fun denom step => if step ≠ 1 then denom * (1 - step) else denom)
        denoms steps
      let inverses ← batchInv denoms
      some (some ((List.range (min (min row_evals.length points.length)
          (min steps.length inverses.length))).map fun i =>
        let row_eval := row_evals.getD i 0
        let x := points.getD i 0
        let step := steps.getD i 0
        let quotient := (row_eval - eval_poly_at_base ans_rem x) * inverses.getD i 0
        if step = 1 then quotient * ((gap + 1 : ℕ) : EF)
        else quotient * (1 - ctx.r_comb_pow_gap1 ⋆ x ^ (gap + 1))))

/-- query_fold_value: the fiber of index j at g^j zeta^l, read through the virtual oracle and folded at the challenge. -/
def query_fold_value (row_evals : List EF) (j : ℕ) (domain_gen fiber_step : F) (arity : ℕ)
    (current_shift : F) (fold_beta : EF) (prev_ctx : Option (VirtualRoundContext EF))
    (round : Option ℕ) (query : ℕ) : VM EF := do
  let subgroup_points := shiftedPowersList fiber_step (domain_gen ^ j) arity
  let current_fiber ← liftO (materialize_virtual_fiber row_evals subgroup_points current_shift prev_ctx)
  match current_fiber with
  | none => throw (StirError.InvalidRoundConsistency round query)
  | some fiber => liftO (lagrange_interpolate_at subgroup_points fiber fold_beta)

/-- check_ans_length: at most max_ans_len coefficients, and not none while a node remains. -/
def check_ans_length (round : ℕ) (ans_polynomial : List EF) (max_ans_len : ℕ) : VM Unit :=
  if ans_polynomial.length > max_ans_len then
    throw (StirError.AnsPolynomialTooLong round max_ans_len ans_polynomial.length)
  else if ans_polynomial = [] ∧ max_ans_len > 0 then
    throw (StirError.MissingAnsPolynomial round max_ans_len)
  else pure ()

/-- resolve_ans_polynomial: the sent coefficients, or in compact mode the verifier's own interpolant. -/
def resolve_ans_polynomial (round : ℕ) (compact : Bool) (transmitted points values : List EF) :
    VM (List EF) :=
  if !compact then do
    check_ans_length round transmitted points.length
    pure transmitted
  else if transmitted ≠ [] then throw (StirError.UnexpectedAnsPolynomial round transmitted.length)
  else if points.length ≠ values.length ∨
      (List.range points.length).any (fun i => (points.take i).contains (points.getD i 0)) then
    throw (StirError.InvalidAnsConsistency round)
  else liftO (interpolate_poly points values)

/-- external_fibers_in_draw_order: ask the source once for the sorted unique indices, then lay its fibers out in draw order. -/
def external_fibers_in_draw_order (indices : List ℕ) (arity : ℕ) (round : Option ℕ)
    (source : List ℕ → VM (List (List EF))) : VM (List (List EF)) := do
  let unique := (indices.mergeSort (· ≤ ·)).dedup
  let fibers ← source unique
  if fibers.length ≠ unique.length then
    throw (StirError.FiberCount round unique.length fibers.length)
  else match (List.range fibers.length).find? (fun f => (fibers.getD f []).length ≠ arity) with
    | some f => throw (StirError.FiberArity round f arity (fibers.getD f []).length)
    | none => indices.mapM fun j => match unique.idxOf? j with
      | some pos => pure (fibers.getD pos [])
      | none => panic

/-- fetch_round_rows, for a committed oracle: the opening count, every row's arity, the commitment, then the MMCS check. -/
def fetch_committed_rows (mmcs_ok : Bool) (row_evals : Option (List (List EF)))
    (has_commitment : Bool) (expected_num_queries arity : ℕ) (round : Option ℕ) :
    VM (List (List EF)) :=
  match row_evals with
  | none => throw (StirError.MissingQueryOpenings round)
  | some rows =>
    if rows.length ≠ expected_num_queries then
      throw (StirError.QueryOpeningCount round expected_num_queries rows.length)
    else match (List.range rows.length).find? (fun q => (rows.getD q []).length ≠ arity) with
      | some q => throw (StirError.OpenedRowArity round q arity (rows.getD q []).length)
      | none =>
        if !has_commitment then throw (StirError.MissingCommitment round)
        else if !mmcs_ok then throw (StirError.InvalidMmcsProof round)
        else pure rows

/-- The state RoundVerifier carries through its query loop: points, answers, seen indices, and round 0's pairs and draws. -/
structure QueryState (F EF : Type _) where
  seen : List ℕ
  query_points : List EF
  query_answers : List EF
  first_round_pairs : List (ℕ × List EF)
  first_round_draws : List ℕ

/-- The query loop of RoundVerifier::fetch_and_fold: fold every opened row, record round 0's draws, and keep each index's first point and answer. -/
def fold_queries (G : Gen F) (round : ℕ) (fold_shift : F) (fold_log_domain current_log_domain : ℕ)
    (arity : ℕ) (current_shift : F) (fold_beta : EF) (prev_ctx : Option (VirtualRoundContext EF))
    (query_indices : List ℕ) (round_rows : List (List EF)) : VM (QueryState F EF) := do
  let fold_gen ← liftO (G.get fold_log_domain)
  let domain_gen ← liftO (G.get current_log_domain)
  let fiber_step := domain_gen ^ 2 ^ fold_log_domain
  let pairs := List.zip query_indices round_rows
  (List.range pairs.length).foldlM (fun (st : QueryState F EF) q => do
    let (j, row_evals) := pairs.getD q (0, [])
    let fold_point := algebraMap F EF fold_shift * algebraMap F EF (fold_gen ^ j)
    let fold_val ← query_fold_value row_evals j domain_gen fiber_step arity current_shift fold_beta
      prev_ctx (some round) q
    let draws := if round = 0 then st.first_round_draws ++ [j] else st.first_round_draws
    if j ∉ st.seen then
      pure ⟨st.seen ++ [j], st.query_points ++ [fold_point], st.query_answers ++ [fold_val],
        if round = 0 then st.first_round_pairs ++ [(j, row_evals)] else st.first_round_pairs, draws⟩
    else pure { st with first_round_draws := draws })
    ⟨[], [], [], [], []⟩

/-- all_points_and_values: the OOD points then the distinct query points, with their claimed values. -/
def all_points_and_values (ood_points query_points ood_answers query_answers : List EF) :
    List EF × List EF :=
  (ood_points ++ query_points, ood_answers ++ query_answers)

/-- RoundVerifier::finish: the context of the next virtual oracle. -/
def finish_ctx (r_comb : EF) (ans_polynomial all_points : List EF) : VirtualRoundContext EF :=
  let gap := all_points.length
  ⟨ans_polynomial, vanishing_poly_from_roots all_points, r_comb, gap, r_comb ^ (gap + 1)⟩

/-- RoundVerifier::new: the fold's domain, the arity, and the next domain, halved and shifted by the generator. -/
def round_geometry (generator current_shift : F) (current_log_domain log_arity : ℕ) :
    Option (ℕ × F × ℕ × ℕ × F) := do
  let (fold_log_domain, fold_shift) ← fold_domain_params current_shift current_log_domain log_arity
  let next_log_domain ← subChecked current_log_domain 1
  some (2 ^ log_arity, fold_shift, fold_log_domain, next_log_domain,
    next_domain_shift generator current_shift log_arity)

/-- The domains an OOD point must avoid: the current domain, the next domain, and the fold's domain. -/
def excluded_domains (current_shift : F) (current_log_domain : ℕ) (next_shift : F)
    (next_log_domain : ℕ) (fold_shift : F) (fold_log_domain : ℕ) : List (F × ℕ) :=
  [(current_shift, current_log_domain), (next_shift, next_log_domain), (fold_shift, fold_log_domain)]

/-- set_gamma: the coset fold point gamma / shift, which panics on a zero shift. -/
def set_gamma (gamma : EF) (current_shift : F) : Option EF :=
  (inverse current_shift).map fun s => gamma ⋆ s

/-- The final round's query loop: fold each row and compare it with the final polynomial at the queried point. -/
def check_final_queries (G : Gen F) (final_new_log_domain current_log_domain final_arity : ℕ)
    (final_new_shift current_shift : F) (fold_beta : EF) (prev_ctx : Option (VirtualRoundContext EF))
    (final_polynomial : List EF) (final_indices : List ℕ) (final_rows : List (List EF)) :
    VM Unit := do
  let final_gen ← liftO (G.get final_new_log_domain)
  let final_domain_gen ← liftO (G.get current_log_domain)
  let final_fiber_step := final_domain_gen ^ 2 ^ final_new_log_domain
  let pairs := List.zip final_indices final_rows
  (List.range pairs.length).forM fun q => do
    let (j, row_evals) := pairs.getD q (0, [])
    let fold_val ← query_fold_value row_evals j final_domain_gen final_fiber_step final_arity
      current_shift fold_beta prev_ctx none q
    let x_j := algebraMap F EF final_new_shift * algebraMap F EF (final_gen ^ j)
    let expected := eval_poly final_polynomial x_j
    if fold_val ≠ expected then throw StirError.FinalPolyMismatch else pure ()

end p3_stir.verifier.mirror
