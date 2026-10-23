/-
Transcriptions of the lookup records, the per-AIR lookup list, its packing, and the checks run over every AIR.

These do not extract: they are generic over the field traits, which aeneas rejects.

Each definition transcribes one Rust item, named in the crate's mirror entries.

What a transcription abstracts:

* a field is a mathlib field F, and a `u32` weight is a natural number with its bound kept where Rust checks it;
* a bus name is a string;
* a panic is none;
* `BigUint` arithmetic is natural-number arithmetic, and the characteristic is a parameter.

Loops, branches and the order of checks are kept.
-/
module

public import P3Air

@[expose] public section

namespace p3_lookup.mirror

open p3_air.symbolic.mirror

/-- A lookup confined to one AIR, or shared across AIRs on a named bus. -/
inductive Kind where
  | Local
  | Global (bus : String)
  deriving DecidableEq

/-- One lookup: tuples, a signed multiplicity per tuple, a per-row weight bound, its slot, and optional exclusive flags. -/
structure Lookup (F : Type) where
  kind : Kind
  elements : List (List (SymbolicExpression F))
  multiplicities : List (SymbolicExpression F)
  count_weight : ℕ
  column : ℕ
  flags : Option (List (SymbolicExpression F)) := none

/-- Denominator slots per row: one per tuple, or one for an exclusive column. -/
def Lookup.num_denoms {F : Type} (l : Lookup F) : ℕ :=
  if l.flags.isSome then 1 else l.elements.length

/-- The largest value of a `u32`. -/
def U32_MAX : ℕ := 2 ^ 32 - 1

/-- `u32::checked_add`: none on overflow. -/
def checked_add_u32 (a b : ℕ) : Option ℕ := if a + b ≤ U32_MAX then some (a + b) else none

/-- One message on a named bus: payload, signed count and its weight. -/
structure SymbolicInteraction (F : Type) where
  bus_name : String
  fields : List (SymbolicExpression F)
  count : SymbolicExpression F
  count_weight : ℕ

/-- One local lookup: tuples with their counts and weights. -/
structure SymbolicLocalInteraction (F : Type) where
  tuples : List (List (SymbolicExpression F) × (SymbolicExpression F × ℕ))

/-- One branch of an exclusive group: flag, count, payload and weight. -/
structure SymbolicExclusiveBranch (F : Type) where
  flag : SymbolicExpression F
  count : SymbolicExpression F
  fields : List (SymbolicExpression F)
  count_weight : ℕ

/-- One exclusive group on a named bus. -/
structure SymbolicExclusiveInteraction (F : Type) where
  bus_name : String
  branches : List (SymbolicExclusiveBranch F)

/-- The width check: none unless every width equals the first; the first width, or 0 for none. -/
def assert_uniform_widths (widths : List ℕ) : Option ℕ :=
  match widths with
  | [] => some 0
  | w :: rest => if rest.all (· = w) then some w else none

/-- The width check over tuples. -/
def assert_uniform_tuple_width {F : Type} (elements : List (List (SymbolicExpression F))) :
    Option ℕ :=
  assert_uniform_widths (elements.map List.length)

/-- The lookups of an AIR, locals first, then globals, then exclusive groups, with contiguous slots.

A local lookup's weight is the sum of its tuples' weights, and an overflow panics.

An exclusive group's weight is the largest branch weight. -/
def from_interactions {F : Type} (global : List (SymbolicInteraction F))
    (local' : List (SymbolicLocalInteraction F)) (exclusive : List (SymbolicExclusiveInteraction F)) :
    Option (List (Lookup F)) := do
  let locals ← local'.zipIdx.mapM fun (i, col) => do
    let count_weight ← i.tuples.foldlM (fun acc t => checked_add_u32 acc t.2.2) 0
    let elements := i.tuples.map (·.1)
    let _ ← assert_uniform_tuple_width elements
    pure { kind := .Local, elements, multiplicities := i.tuples.map (·.2.1), count_weight,
           column := col, flags := none : Lookup F }
  let n := local'.length
  let globals := global.zipIdx.map fun (i, j) =>
    { kind := .Global i.bus_name, elements := [i.fields], multiplicities := [i.count],
      count_weight := i.count_weight, column := n + j, flags := none : Lookup F }
  let m := n + global.length
  let exclusives := exclusive.zipIdx.map fun (i, j) =>
    { kind := .Global i.bus_name, elements := i.branches.map (·.fields),
      multiplicities := i.branches.map (·.count),
      count_weight := (i.branches.map (·.count_weight)).foldr max 0,
      column := m + j, flags := some (i.branches.map (·.flag)) : Lookup F }
  pure (locals ++ globals ++ exclusives)

/-- The widths of every tuple on each global bus, buses in first-appearance order. -/
def bus_widths {F : Type} (lookups : List (Lookup F)) : List (String × List ℕ) :=
  lookups.foldl (fun buses l =>
    match l.kind with
    | .Local => buses
    | .Global bus =>
      let widths := l.elements.map List.length
      if buses.any (·.1 = bus) then
        buses.map fun b => if b.1 = bus then (b.1, b.2 ++ widths) else b
      else buses ++ [(bus, widths)]) []

/-- None unless every bus carries one width. -/
def assert_bus_widths {F : Type} (lookups : List (Lookup F)) : Option Unit :=
  (bus_widths lookups).forM fun b => do let _ ← assert_uniform_widths b.2

/-- Greedy packing of one bus's lookups into columns within a degree budget.

A lone lookup always opens a column, and the weights of merged lookups add, with an overflow panicking. -/
def pack_bus {F : Type} (max_degree : ℕ) (constraint_degree : Lookup F → ℕ) :
    List (Lookup F) → Option (List (Lookup F)) → Option (List (Lookup F))
  | members, acc => do
    let packed ← acc
    let (sealed, current) ← members.foldlM (fun (st : List (Lookup F) × Option (Lookup F)) member =>
      match st.2 with
      | none => pure (st.1, some member)
      | some cur =>
        let merged := { cur with elements := cur.elements ++ member.elements,
                                 multiplicities := cur.multiplicities ++ member.multiplicities }
        if constraint_degree merged ≤ max_degree then do
          let w ← checked_add_u32 cur.count_weight member.count_weight
          pure (st.1, some { merged with count_weight := w })
        else pure (st.1 ++ [cur], some member)) ([], none)
    pure (packed ++ sealed ++ current.toList)

/-- Fold same-bus global lookups into shared columns.

The width check runs first; exclusive and local lookups pass through in order; then each bus, in first-appearance order, is packed greedily; slots are renumbered. -/
def pack_same_bus_with_degree {F : Type} (lookups : List (Lookup F)) (max_degree : ℕ)
    (constraint_degree : Lookup F → ℕ) : Option (List (Lookup F)) := do
  assert_bus_widths lookups
  let (passed, buses) := lookups.foldl (fun (st : List (Lookup F) × List (String × List (Lookup F))) l =>
    if l.flags.isSome then (st.1 ++ [l], st.2)
    else match l.kind with
      | .Local => (st.1 ++ [l], st.2)
      | .Global bus =>
        if st.2.any (·.1 = bus) then
          (st.1, st.2.map fun b => if b.1 = bus then (b.1, b.2 ++ [l]) else b)
        else (st.1, st.2 ++ [(bus, [l])])) ([], [])
  let packed ← buses.foldl (fun acc b => pack_bus max_degree constraint_degree b.2 acc) (some passed)
  pure (packed.zipIdx.map fun (l, i) => { l with column := i })

/-- The sum of the weights of an AIR's lookups. -/
def total_count_weight {F : Type} (lookups : List (Lookup F)) : ℕ :=
  (lookups.map (·.count_weight)).sum

/-- One width per bus across every AIR: the widest global payload, or the first mismatch as (bus, expected, actual). -/
def check_bus_widths {F : Type} (lookups : List (List (Lookup F))) :
    Except (String × ℕ × ℕ) ℕ := do
  let (_, widest) ← lookups.foldlM (fun (st : List (String × ℕ) × ℕ) air =>
    (bus_widths air).foldlM (fun (st : List (String × ℕ) × ℕ) (b : String × List ℕ) =>
      b.2.foldlM (fun (st : List (String × ℕ) × ℕ) width => do
        let widest := max st.2 width
        match st.1.find? (·.1 = b.1) with
        | some (_, expected) =>
          if expected ≠ width then throw (b.1, expected, width) else pure (st.1, widest)
        | none => pure (st.1 ++ [(b.1, width)], widest)) st) st) ([], 0)
  pure widest

/-- The multiplicity height bound: the weighted height sum must stay below the characteristic p.

Unequal lengths panic. -/
def check_multiplicity_height_bound {F : Type} (p : ℕ) (lookups : List (List (Lookup F)))
    (heights : List ℕ) : Option (Except ℕ Unit) := do
  if lookups.length ≠ heights.length then none
  let weighted_height_sum :=
    ((lookups.zip heights).map fun (air, h) => total_count_weight air * h).sum
  pure (if weighted_height_sum ≥ p then .error weighted_height_sum else .ok ())

end p3_lookup.mirror
