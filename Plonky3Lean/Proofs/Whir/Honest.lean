module

public import Plonky3Lean.Proofs.Whir.HonestSumcheck
public import Plonky3Lean.Proofs.Whir.Multilinear
public import P3Whir

@[expose] public section

/-!
# The honest WHIR prover

The prover of Construction 5.1 against the verifier's sponge, in the encoding p3-whir uses.

Each round runs these steps:

- commit the interleaved codeword of the current table
- answer the out-of-domain samples with P~(pow(z))
- grind
- open the previous codeword at the drawn indices
- add the round's constraint to its weight table
- run the round's sumcheck.

It is a model of the Rust prover, not a transcription.
-/

namespace Plonky3Lean.Proofs.Whir

open Finset Plonky3Lean.Spec.MultilinearUtil Plonky3Lean.Spec.Whir Plonky3Lean.Proofs.MultilinearUtil
open p3_sumcheck.mirror p3_sumcheck.constraints.mirror p3_whir.mirror p3_whir.transcript.mirror
open p3_multilinear_util.point.mirror

set_option linter.unusedSectionVars false

variable {F EF Com MP D : Type _} [Field F] [Field EF] [Algebra F EF] [DecidableEq F] [DecidableEq EF]

/-- The configuration of the codeword queried in round t: the round's own, or the final one. -/
def queried (c : WhirConfig) (t : ℕ) : RoundConfig :=
  if t < c.n_rounds then c.round_parameters.getD t default else c.final_round_config

/-- What the prover adds to the verifier's environment:

- a grinding solver
- the Merkle commit
- its openings. -/
structure ProverEnv (F EF Com MP D : Type _) where
  solve : List (Step F EF) → ℕ → F
  commit : List (List EF) → Com × D
  openExt : D → List ℕ → MP
  openBase : List ℕ → MP

/-- The honest out-of-domain phase.

It draws each point, answers the table's extension at its expansion, and absorbs the answer. -/
def oodProve (S : WSponge F EF) (P : List EF) (nv : ℕ) (h : List (Step F EF)) (k : ℕ) :
    List (List EF) × List EF × List (Step F EF) :=
  (List.range k).foldl (fun acc _ =>
    let point := Point.expand_from_univariate (S.sample acc.2.2) nv
    let y := mle P point
    (acc.1 ++ [point], acc.2.1 ++ [y], acc.2.2 ++ [.challenge, .message [y]])) ([], [], h)

/-- The prover's state between rounds. -/
structure PState (F EF Com MP D : Type _) where
  /-- The current table, folded at every challenge so far. -/
  P : List EF
  /-- The current weight table. -/
  Wt : List EF
  claim : EF
  cons : List (Constraint F EF)
  rand : List (List EF)
  h : List (Step F EF)
  /-- The previously committed table, its variable count, its generator, and its Merkle data.

  It is none for the initial one. -/
  prevP : List EF
  prevNv : ℕ
  prevData : Option D
  prevRoot : Com
  rounds : List (WhirRoundProof F EF Com MP)

variable (E : Env F EF Com MP) (PE : ProverEnv F EF Com MP D) (c : WhirConfig)

/-- The rows of the codeword of table P in nv variables queried in round t. -/
def codeRows (P : List EF) (nv t : ℕ) : List (List EF) :=
  let q := queried c t
  (List.range (q.domain_size >>> q.folding_factor)).map
    (row P nv q.folding_factor (algebraMap F EF (E.gen q.log_folded_domain_size)))

/-- The openings of the previous codeword at the indices.

They are the base-field initial rows, or the committed extension rows. -/
def openPrev (P0 : List F) (n : ℕ) (st : PState F EF Com MP D) (t : ℕ) (idx : List ℕ) :
    QueryOpenings F EF MP :=
  match st.prevData with
  | none =>
    let q := queried c 0
    .Base (idx.map (row P0 n q.folding_factor (E.gen q.log_folded_domain_size))) (PE.openBase idx)
  | some d => .Extension (idx.map fun i => (codeRows E c st.prevP st.prevNv t).getD i []) (PE.openExt d idx)

/-- One honest intermediate round t. -/
def honestRound (P0 : List F) (n : ℕ) (st : PState F EF Com MP D) (t : ℕ) : PState F EF Com MP D :=
  let params := c.round_parameters.getD t default
  let nv := params.num_variables
  let rd := PE.commit (codeRows E c st.P nv (t + 1))
  let o := oodProve E.S st.P nv (st.h ++ [.message (E.enc rd.1)]) params.ood_samples
  let wit : F := if params.pow_bits = 0 then 0 else PE.solve o.2.2 params.pow_bits
  let h := if params.pow_bits = 0 then o.2.2 else o.2.2 ++ [.pow params.pow_bits (PE.solve o.2.2 params.pow_bits)]
  let site := (c.site t).getD default
  let qi := play_query_indices E.S h site.index_bits site.draws c.stratified_queries site.depths
  let g := E.gen params.log_folded_domain_size
  let con : Constraint F EF := ⟨nv, [.Eq ⟨nv, o.1, o.2.1⟩,
    .Select ⟨nv, qi.1.map (g ^ ·), qi.1.map fun i => uni st.P (algebraMap F EF (g ^ i))⟩],
    E.S.sample qi.2, 1⟩
  let H := honestSumcheck E.S.toSponge PE.solve params.folding_pow_bits st.P
    (List.zipWith (· + ·) st.Wt (cubeTable (weightAt con) nv)) (qi.2 ++ [.challenge])
    (c.folding_schedule.getD (t + 1) 0)
  let σ := Plonky3Lean.Proofs.Sumcheck.replay .Evaluation (con.combine_evals st.claim) H.ms H.rs
  { P := H.f, Wt := H.w, claim := σ,
    cons := st.cons ++ [con], rand := st.rand ++ [H.rs], h := H.h, prevP := st.P, prevNv := nv,
    prevData := some rd.2, prevRoot := rd.1,
    rounds := st.rounds ++ [⟨some rd.1, o.2.1, wit, openPrev E PE c P0 n st t qi.1, (H.ms, H.ws)⟩] }

/-- The honest initial fold.

It takes the layout's challenge and constraint, and runs the initial sumcheck on the weight table. -/
def honestInit (P0 : List F) (n : ℕ) (commitment : Com) (h : List (Step F EF)) :
    PState F EF Com MP D × SumcheckData F EF :=
  let con := E.initial (E.S.sample (h ++ [E.layoutSeed]))
  let H := honestSumcheck E.S.toSponge PE.solve c.starting_folding_pow_bits (P0.map (algebraMap F EF))
    (cubeTable (weightAt con) n) (h ++ [E.layoutSeed, .challenge]) (c.folding_schedule.getD 0 0)
  let σ := Plonky3Lean.Proofs.Sumcheck.replay .Evaluation (con.combine_evals 0) H.ms H.rs
  (⟨H.f, H.w, σ, [con], [H.rs], H.h, P0.map (algebraMap F EF), n, none, commitment, []⟩, (H.ms, H.ws))

/-- The state after the initial fold and every intermediate round. -/
def honestLoop (P0 : List F) (n : ℕ) (commitment : Com) (h : List (Step F EF)) : PState F EF Com MP D :=
  (List.range c.n_rounds).foldl (honestRound E PE c P0 n) (honestInit E PE c P0 n commitment h).1

/-- The honest proof, in order:

- the initial fold
- every round
- the final table, its queries and the closing sumcheck. -/
def honestProof (P0 : List F) (n : ℕ) (commitment : Com) (h : List (Step F EF)) :
    WhirProof F EF Com MP :=
  let st := honestLoop E PE c P0 n commitment h
  let site := (c.site c.n_rounds).getD default
  let h1 := st.h ++ [.message st.P]
  let wit : F := if site.pow_bits = 0 then 0 else PE.solve h1 site.pow_bits
  let h2 := if site.pow_bits = 0 then h1 else h1 ++ [.pow site.pow_bits (PE.solve h1 site.pow_bits)]
  let qi := play_query_indices E.S h2 site.index_bits site.draws c.stratified_queries site.depths
  let H := honestSumcheck E.S.toSponge PE.solve c.final_folding_pow_bits st.P st.Wt qi.2 c.final_sumcheck_rounds
  ⟨(honestInit E PE c P0 n commitment h).2, st.rounds, some st.P, wit, openPrev E PE c P0 n st c.n_rounds qi.1,
    if 0 < c.final_sumcheck_rounds then some (H.ms, H.ws) else none⟩

end Plonky3Lean.Proofs.Whir
