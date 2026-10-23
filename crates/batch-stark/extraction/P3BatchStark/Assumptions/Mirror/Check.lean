/-
Transcription of the batch's debug constraint checker.

It does not extract: it is generic over the field traits, the AIR and the lookup gadget, which aeneas rejects.

What the transcription abstracts, beyond the p3-air and p3-lookup transcriptions:

* the debug builder with permutation is p3-lookup's permutation builder over p3-air's debug builder;
* the gadget's evaluation is the AIR's evaluation, then the lookup constraints, or the check that no permutation value is passed when there is no lookup;
* a failed `assert_eq!` and a row with a failing constraint panic, which is none.

The loop over rows and the order of checks are kept.
-/
module

public import P3Lookup

@[expose] public section

namespace p3_batch_stark.checker.mirror

open p3_air.air.mirror p3_air.builder.mirror p3_lookup.mirror

variable {F : Type} [Field F] [DecidableEq F] [Inhabited F] {K : Type} [Field K] [Algebra F K]
  [DecidableEq K]

/-- The debug permutation builder of one row, with the 0/1 selectors of row r of n. -/
def rowBuilder (air : Air F) (main : Mat F) (preprocessed : Option (Mat F)) (permutation : Mat K)
    (challenges values : List K) (public_values : List F) (r : ℕ) : PermBuilder F F K DebugState :=
  let n := main.height
  { toExtensionBuilder := debugExtBuilder (rowPair main r n)
      (match preprocessed with | some p => rowPair p r n | none => ⟨[], []⟩) public_values
      (if r = 0 then 1 else 0) (if r = n - 1 then 1 else 0) (if r ≠ n - 1 then 1 else 0)
      (air.periodic_values r)
    ext := ⟨(· + ·), (· - ·), (· * ·), 0, 1⟩
    ext_of := algebraMap F K
    permutation := fun _ => rowPair permutation r n
    permutation_randomness := fun _ => challenges
    permutation_values := fun _ => values }

/-- `eval_air_and_lookups` on one row: the AIR's constraints, then the lookups' constraints. -/
def eval_air_and_lookups (air : Air F) (B : PermBuilder F F K DebugState) (s : DebugState)
    (lookups : List (Lookup F)) : Option DebugState :=
  let s := air.eval B.toAirBuilder s
  if lookups.isEmpty then
    if (B.permutation_values s).length ≠ 0 then none else some s
  else eval_all B s lookups

/-- `check_constraints`: the heights must agree, then every row must pass its AIR and lookup constraints. -/
def check_constraints (air : Air F) (main : Mat F) (preprocessed : Option (Mat F)) (permutation : Mat K)
    (challenges values : List K) (public_values : List F) (lookups : List (Lookup F)) : Option Unit := do
  let n := main.height
  if (preprocessed.map fun p => decide (p.height ≠ n)).getD false then none
  if permutation.height ≠ n then none
  (List.range n).forM fun r => do
    let s ← eval_air_and_lookups air
      (rowBuilder air main preprocessed permutation challenges values public_values r)
      (DebugState.new r) lookups
    if s.failures ≠ [] then none

end p3_batch_stark.checker.mirror
