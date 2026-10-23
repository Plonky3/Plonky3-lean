/-
Transcriptions of the prover side: the row context, the power-table tuple combiner, and the permutation-trace generator.

These do not extract: they are generic over the field traits, which aeneas rejects.

Each definition transcribes one Rust item, named in the crate's mirror entries.

What a transcription abstracts, beyond the gadget transcriptions:

* the extension field is a field K with an algebra map from F;
* p3-field's batch inversion is the entrywise inverse, and a zero entry panics, as the inverse of a zero product does;
* p3-maybe-rayon's thread count and task floor are parameters, and a parallel loop over chunks is the sequential loop;
* a chunk's flat denominator and multiplicity buffers are kept as nested lists in the same order, row, then lookup, then tuple.

Loops over rows and chunks, the zero-multiplicity skip, the exclusive checks and the three-phase prefix sum are kept.
-/
module

public import P3Lookup.Assumptions.Mirror.Logup
public import Mathlib.Algebra.Algebra.Defs

@[expose] public section

namespace p3_lookup.mirror

open p3_air.symbolic.mirror p3_air.builder.mirror p3_air.air.mirror

variable {F : Type} [Field F] [DecidableEq F]

/-- The row context of the prover: two-row windows of the main and preprocessed traces, the public values, and the selectors of row `row` of `height`.

It keeps the trait's default periodic values, which are empty.

Its assertions are never reached by resolution. -/
def LookupTraceBuilder (main preprocessed : RowWindow F) (public_values : List F)
    (height row : ℕ) : AirBuilder F F Unit where
  add := (· + ·)
  sub := (· - ·)
  mul := (· * ·)
  neg := (- ·)
  const := id
  main _ := main
  preprocessed _ := preprocessed
  is_first_row _ := if row = 0 then 1 else 0
  is_last_row _ := if row + 1 = height then 1 else 0
  is_transition _ := if row + 1 < height then 1 else 0
  assert_zero _ _ := ()
  public_values _ := public_values
  periodic_values _ := []

variable {K : Type} [Field K] [Algebra F K] [DecidableEq K]

/-- `dot_product`: the sum of products over the zipped lists. -/
def dot_product (l : List K) (r : List F) : K := ((l.zip r).map fun (a, b) => a * algebraMap F K b).sum

/-- The prover's tuple combiner: the last entry at beta^0, and each leading entry e_i times the precomputed beta^(k-1-i).

A tuple wider than the power table panics. -/
def combine_tuple (elts : List (SymbolicExpression F)) (beta_powers : List K)
    (row_ctx : AirBuilder F F Unit) : Option K :=
  match elts.getLast?, elts.dropLast with
  | none, _ => some 0
  | some last, [] => (resolve row_ctx () last).map (algebraMap F K)
  | some last, leading => do
    if beta_powers.length < elts.length then none
    let high_powers := ((beta_powers.drop 1).take (elts.length - 1)).reverse
    let leading_resolved ← leading.mapM (resolve row_ctx ())
    let lifted_last ← (resolve row_ctx () last).map (algebraMap F K)
    pure (lifted_last + dot_product high_powers leading_resolved)

/-- `chunks`: consecutive pieces of n entries, the last one shorter; a chunk size of 0 panics. -/
def chunks {α : Type _} (n : ℕ) (l : List α) : Option (List (List α)) :=
  if n = 0 then none else some (go n l.length l)
where
  /-- The pieces, with the length as fuel. -/
  go (n : ℕ) : ℕ → List α → List (List α)
    | 0, _ => []
    | _ + 1, [] => []
    | fuel + 1, a :: l => (a :: l).take n :: go n fuel ((a :: l).drop n)

/-- p3-field's batch inversion: the entrywise inverse, and a panic on a zero entry. -/
def batch_multiplicative_inverse (x : List K) : Option (List K) :=
  if x.all (· ≠ 0) then some (x.map (·⁻¹)) else none

/-- The (denominator, multiplicity) pairs of one lookup on one row.

An additive lookup gives one pair per tuple, with denominator 1 for a zero multiplicity.

An exclusive lookup gives one pair, after checking that each flag is 0 or 1 and that they sum to 0 or 1. -/
def lookup_row_terms (row_ctx : AirBuilder F F Unit) (lookup : Lookup F) (alpha : K)
    (powers : List K) : Option (List (K × F)) :=
  match lookup.flags with
  | none => lookup.elements.zipIdx.mapM fun (elts, j) => do
    let mult ← resolve row_ctx () (← lookup.multiplicities[j]?)
    if mult = 0 then pure (1, mult)
    else pure (alpha - (← combine_tuple elts powers row_ctx), mult)
  | some flags => do
    let (numerator, flag_sum, denom) ← lookup.elements.zipIdx.foldlM
      (fun (st : F × F × K) (x : List (SymbolicExpression F) × ℕ) => do
        let (elts, k) := x
        let flag ← resolve row_ctx () (← flags[k]?)
        if ¬ (flag = 0 ∨ flag = 1) then none
        let flag_sum := st.2.1 + flag
        if flag = 0 then pure (st.1, flag_sum, st.2.2)
        else
          let mult ← resolve row_ctx () (← lookup.multiplicities[k]?)
          let term := alpha - (← combine_tuple elts powers row_ctx)
          pure (st.1 + flag * mult, flag_sum, st.2.2 + term * algebraMap F K flag)) (0, 0, 0)
    if ¬ (flag_sum = 0 ∨ flag_sum = 1) then none
    pure [(denom + algebraMap F K (1 - flag_sum), numerator)]

/-- The row context at row i: rows i and i + 1 mod the height. -/
def rowContext (main : Mat F) (preprocessed : Option (Mat F)) (public_values : List F) (i : ℕ) :
    AirBuilder F F Unit :=
  let height := main.height
  LookupTraceBuilder (rowPair main i height)
    (match preprocessed with
     | some prep => rowPair prep i height
     | none => ⟨[], []⟩)
    public_values height i

/-- One chunk of rows: fill each row's pairs, invert the chunk's denominators at once, and emit each row's fractions and their total. -/
def process_chunk (rows : List ℕ) (main : Mat F) (preprocessed : Option (Mat F))
    (public_values : List F) (lookups : List (Lookup F)) (lookup_challenges : List (K × K))
    (beta_powers : List (List K)) : Option (List (List K × K)) := do
  -- Phase 1: the pairs of every row of the chunk.
  let local_terms ← rows.mapM fun i =>
    ((lookups.zip lookup_challenges).zip beta_powers).mapM fun ((lookup, (alpha, _)), powers) =>
      lookup_row_terms (rowContext main preprocessed public_values i) lookup alpha powers
  -- Phase 2: one batch inversion over the chunk.
  let local_inverses ← batch_multiplicative_inverse
    (local_terms.flatMap fun row => row.flatMap fun l => l.map (·.1))
  -- Phase 3: each lookup's fraction is the sum of inverse times multiplicity.
  let (_, out) := local_terms.foldl (fun (st : List K × List (List K × K)) row =>
    let (fracs, rest) := row.foldl (fun (acc : List K × List K) l =>
      let invs := acc.2.take l.length
      (acc.1 ++ [dot_product invs (l.map (·.2))], acc.2.drop l.length)) ([], st.1)
    (rest, st.2 ++ [(fracs, fracs.sum)])) (local_inverses, [])
  pure out

/-- The three-phase inclusive prefix sum over chunks of the given size. -/
def prefix_sum (row_totals : List K) (chunk_size : ℕ) : Option (List K) := do
  -- Phase A: a local inclusive prefix sum in each chunk.
  let local_sums := (← chunks chunk_size row_totals).map fun c => c.scanl (· + ·) 0 |>.tail
  let flat := local_sums.flatten
  -- Phase B: the offset of chunk i is the sum of the last entries of the chunks before it.
  let num_chunks := local_sums.length
  let offsets ← (List.range num_chunks).foldlM (fun (offs : List K) i =>
    if i = 0 then pure (offs ++ [0])
    else do pure (offs ++ [(← offs[i - 1]?) + (← flat[i * chunk_size - 1]?)])) []
  -- Phase C: add each chunk's offset, skipping a zero offset.
  pure ((local_sums.zip offsets).flatMap fun (c, off) => if off = 0 then c else c.map (· + off))

/-- The permutation trace and the terminal.

No lookup gives an empty trace and no terminal.

Otherwise the accumulator is column 0 and lookup i's fraction column i + 1, and the terminal is the sum over the trace.

A lookup whose slot is not its position panics, and so does an empty trace. -/
def generate_permutation (main : Mat F) (preprocessed : Option (Mat F)) (public_values : List F)
    (lookups : List (Lookup F)) (challenges : List K) (num_threads min_task_len : ℕ) :
    Option (Mat K × Option K) := do
  if lookups.isEmpty then return (⟨0, []⟩, none)
  let height := main.height
  let width := lookups.length + 1
  if ¬ (lookups.zipIdx.all fun (l, i) => l.column = i) then none
  let lookup_challenges ← lookups.mapM fun l => do
    pure ((← challenges[2 * l.column]?), (← challenges[2 * l.column + 1]?))
  let max_tuple_width := ((lookups.flatMap (·.elements)).map List.length).foldr max 0
  let beta_powers := lookup_challenges.map fun (_, beta) =>
    (List.range max_tuple_width).map fun j => beta ^ j
  let row_chunks ← chunks 1024 (List.range height)
  let rows ← row_chunks.mapM fun rows =>
    process_chunk rows main preprocessed public_values lookups lookup_challenges beta_powers
  let rows := rows.flatten
  let row_totals := rows.map (·.2)
  if num_threads = 0 then none
  let chunk_size := max ((height + num_threads - 1) / num_threads) min_task_len
  let inclusive ← prefix_sum row_totals chunk_size
  let terminal ← inclusive[height - 1]?
  let aux := (rows.zipIdx.map fun ((fracs, _), i) =>
    (if i = 0 then 0 else inclusive.getD (i - 1) 0) :: fracs).flatten
  pure (⟨width, aux⟩, some terminal)

end p3_lookup.mirror
