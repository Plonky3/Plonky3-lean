/-
Transcriptions of the zerocheck verifier of p3-multi-stark.

They cover the claim its sumcheck starts from, the round degree, and the closing check.

These do not extract.
They are generic over the field traits and the AIR, which aeneas rejects.

Each definition transcribes one Rust item, named in the crate's mirror entries.

What a transcription abstracts:

* an AIR is the numbers the verifier reads from it, its periodic columns at a point, and its folder evaluation
* the folder evaluation reads the selectors, the opened rows and the periodic values
* it returns the alpha-batched constraints and the lookup link, with alpha and the public values fixed
* whether an AIR is linked to the lookup reduction is a flag on the AIR
* the bus family is a function of the opened current rows and the periodic values, with a single error value
* a periodic declaration that does not fit is one error
* a vector is a list, and a panic is none.

Loops, branches and the order of checks are kept.
-/
module

public import P3MultiStark.Selectors
public import P3MultiStark.Opening
public import P3MultilinearUtil

@[expose] public section

namespace p3_multi_stark.zerocheck.mirror

open p3_multi_stark.selectors.mirror p3_multi_stark.opening.mirror p3_multilinear_util.point.mirror

variable {K : Type _} [Field K] [DecidableEq K]

/-- ZerocheckError: why the zerocheck verifier rejects. -/
inductive ZerocheckError where
  | Sumcheck
  | NonZeroClaimedSum
  | BusClaim
  | BusBinding
  | ClaimedSumMismatch
  | OpeningCountMismatch (expected actual : ℕ)
  | NextOpeningCountMismatch (expected actual : ℕ)
  | PreprocessedOpeningCountMismatch (expected actual : ℕ)
  | PreprocessedNextOpeningCountMismatch (expected actual : ℕ)
  | Periodic
  | LookupLinkMismatch (air : ℕ)
  | FinalSumMismatch
  deriving DecidableEq

/-- A verifier step that may reject with an error or panic: none is a panic. -/
abbrev M (α : Type) := Option (Except ZerocheckError α)

/-- What the closing check reads from one AIR. -/
structure AirView (K : Type _) where
  main_width : ℕ
  preprocessed_width : ℕ
  num_public_values : ℕ
  /-- air_periodic_evals_at: the periodic columns at a point.

  It is none when the declaration does not fit. -/
  periodic : List K → Option (List K)
  /-- The folder run over the AIR: alpha-batched constraints, then the lookup link. -/
  eval : BoundaryEvals K → List K → List K → List K → List K → List K → K × K
  /-- Whether the lookup reduction carries a link for this AIR. -/
  linked : Bool

/-- ZerocheckReduction: the challenges, the bound point and the reduced sum. -/
structure ZerocheckReduction (K : Type _) where
  alpha : K
  beta : K
  eta : K
  lambda : K
  tau : List K
  point : List K
  final_sum : K

/-- The bus family at the bound point: a function of the opened current rows and the periodic values. -/
abbrev BusTerm (K : Type _) := List (List K) → List (List K) → List (List K) → Except Unit K

/-- The body of the per-AIR loop of check_constraint_with_lookup_and_bus, in order:

- the width checks
- the suffix of the point
- the next rows
- the periodic values
- the AIR's term, weighted by its power of beta.

The subtraction of the AIR's log height from the largest panics below zero.
The slice panics past the end. -/
def checkAir (red : ZerocheckReduction K) (air : AirView K) (pv log_height : ℕ)
    (main prep : TableOpening K) (beta_pow : K) : M (K × List K) :=
  if air.main_width = 0 then none
  else if pv ≠ air.num_public_values then none
  else if main.local_values.length ≠ air.main_width then
    some (.error (.OpeningCountMismatch air.main_width main.local_values.length))
  else if main.next_values.length ≠ main.next_columns.length then
    some (.error (.NextOpeningCountMismatch main.next_columns.length main.next_values.length))
  else if prep.local_values.length ≠ air.preprocessed_width then
    some (.error (.PreprocessedOpeningCountMismatch air.preprocessed_width prep.local_values.length))
  else if prep.next_values.length ≠ prep.next_columns.length then
    some (.error (.PreprocessedNextOpeningCountMismatch prep.next_columns.length
      prep.next_values.length))
  else if red.tau.length < log_height then none
  else if red.point.length < red.tau.length - log_height then none
  else
    let point := red.point.drop (red.tau.length - log_height)
    match next_row main.next_columns main.next_values air.main_width,
      next_row prep.next_columns prep.next_values air.preprocessed_width with
    | some next, some prep_next =>
      match air.periodic point with
      | none => some (.error .Periodic)
      | some periodic =>
        let ci := air.eval (BoundaryEvals.at point) main.local_values next prep.local_values prep_next
          periodic
        if air.linked then some (.ok (beta_pow * ci.1 + red.eta * ci.2, periodic))
        else some (.ok (beta_pow * ci.1, periodic))
    | _, _ => none

/-- One entry per AIR:

- the AIR
- its public-value count
- its trace arity
- its main opening
- its preprocessed opening. -/
abbrev Entry (K : Type _) := AirView K × ℕ × ℕ × TableOpening K × TableOpening K

/-- The per-AIR loop.

It accumulates g in AIR order, the i-th AIR weighted by beta^i.
It also collects the periodic values. -/
def accumulate (red : ZerocheckReduction K) : List (Entry K) → K → K → M (K × List (List K))
  | [], g, _ => some (.ok (g, []))
  | (air, pv, h, main, prep) :: rest, g, beta_pow =>
    match checkAir red air pv h main prep beta_pow with
    | none => none
    | some (.error e) => some (.error e)
    | some (.ok (term, periodic)) =>
      match accumulate red rest (g + term) (beta_pow * red.beta) with
      | none => none
      | some (.error e) => some (.error e)
      | some (.ok (g', periodics)) => some (.ok (g', periodic :: periodics))

/-- The entries of the loop.

Each AIR is zipped with its public-value count, arity and openings. -/
def entries (airs : List (AirView K)) (pvs log_heights : List ℕ) (main prep : List (TableOpening K)) :
    List (Entry K) :=
  (airs.zip (pvs.zip (log_heights.zip (main.zip prep)))).map
    fun e => (e.1, e.2.1, e.2.2.1, e.2.2.2.1, e.2.2.2.2)

/-- The closing comparison: the bus family, the equality weight, and the final sum. -/
def closing (red : ZerocheckReduction K) (main prep : List (TableOpening K))
    (bus : Option (BusTerm K)) (g : K) (periodics : List (List K)) : M Unit :=
  let bus_term : Except ZerocheckError K := match bus with
    | none => .ok 0
    | some f =>
      match f (main.map (·.local_values)) (prep.map (·.local_values)) periodics with
      | .ok v => .ok v
      | .error _ => .error .BusBinding
  match bus_term with
  | .error e => some (.error e)
  | .ok bus_term =>
    match Point.eval_eq red.tau red.point with
    | none => none
    | some eq_at_point =>
      if red.final_sum ≠ eq_at_point * g + red.lambda * bus_term then some (.error .FinalSumMismatch)
      else some (.ok ())

/-- AirZerocheck::check_constraint_with_lookup_and_bus, in order:

- the caller's assertions
- the opening counts
- the per-AIR loop
- the closing comparison. -/
def check_constraint (airs : List (AirView K)) (pvs log_heights : List ℕ)
    (main prep : List (TableOpening K)) (red : ZerocheckReduction K)
    (bus : Option (BusTerm K)) : M Unit :=
  if airs = [] then none
  else if airs.length ≠ pvs.length then none
  else if airs.length ≠ log_heights.length then none
  else if ¬ log_heights.all (0 < ·) then none
  else if main.length ≠ airs.length then some (.error (.OpeningCountMismatch airs.length main.length))
  else if prep.length ≠ airs.length then
    some (.error (.PreprocessedOpeningCountMismatch airs.length prep.length))
  else if red.point.length ≠ red.tau.length then none
  else
    match accumulate red (entries airs pvs log_heights main prep) 0 1 with
    | none => none
    | some (.error e) => some (.error e)
    | some (.ok (g, periodics)) => closing red main prep bus g periodics

/-- The round degree of verify_reduction_with_lookup_and_bus.

It is one more than the largest AIR degree, for the eq weight.
It is widened to the bus composition degree. -/
def round_degree (air_degrees : List ℕ) (bus_degree : Option ℕ) : ℕ :=
  let air := air_degrees.foldl max 0 + 1
  match bus_degree with
  | none => air
  | some b => max air b

/-- The claim checks of verify_reduction_with_lookup_and_bus, before the sumcheck runs.

A zerocheck with neither lookup nor bus claims zero.

Otherwise the claim is eta times the lookup claim plus lambda times the batched bus claim. -/
def check_claimed_sum (claimed : K) (lookup : Option K) (bus : Option (Except Unit K))
    (eta lambda : K) : Except ZerocheckError Unit :=
  if lookup.isNone ∧ bus.isNone ∧ claimed ≠ 0 then .error .NonZeroClaimedSum
  else
    match bus with
    | some (.error _) => .error .BusClaim
    | _ =>
      let bus_claim := match bus with | some (.ok c) => c | _ => 0
      let expected := (match lookup with | none => 0 | some l => eta * l) + lambda * bus_claim
      if claimed ≠ expected then .error .ClaimedSumMismatch else .ok ()

end p3_multi_stark.zerocheck.mirror
