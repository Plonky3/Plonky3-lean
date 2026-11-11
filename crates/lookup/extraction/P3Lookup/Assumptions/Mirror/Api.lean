/-
Transcriptions of the lookup API around the gadgets.

They cover:

* the challenge table and the signed counts
* the typed buses
* the debug balance check
* the indexed declarations.

These do not extract, for one of two reasons:

* they are generic over the field traits or over the builder, which aeneas rejects
* they return early from inside a loop (docs/extractor-issues.md 23).

Each definition transcribes one Rust item, named in the crate's mirror entries.

What a transcription abstracts, beyond the gadget transcriptions:

* an i32 is an integer in its range, and a u32 a natural number
* an interaction builder is the list of interactions it recorded, as the symbolic builder keeps them
* the debug check's hash map is a list of keys with their net multiplicities, in first-insertion order
* a panic is none, or false for a check that panics on failure.

Loops, branches and the order of checks are kept.
-/
module

public import P3Lookup.Assumptions.Mirror.Trace

@[expose] public section

namespace p3_lookup.mirror

open p3_air.symbolic.mirror p3_air.builder.mirror p3_air.air.mirror

/-! ## Challenges -/

/-- The challenge table: alpha, beta, and the bus offsets alpha + (i + 1) beta^W.

The offsets accumulate one gamma at a time.

A width of 0 panics. -/
def Challenges.new {K : Type _} [Field K] (alpha beta : K) (max_message_width num_bus_ids : ℕ) :
    Option (K × K × List K) := do
  if ¬ max_message_width > 0 then none
  let gamma := beta ^ max_message_width
  let (_, bus_prefix) := (List.range num_bus_ids).foldl
    (fun (st : K × List K) _ => (st.1 + gamma, st.2 ++ [st.1 + gamma])) (alpha, [])
  pure (alpha, beta, bus_prefix)

/-! ## Counts -/

/-- A constant count: the constant, with its absolute value as the bound. -/
def Count.from_i32 {F : Type _} [Ring F] (count : ℤ) : F × ℕ := ((count : F), count.natAbs)

/-- Swapping send and receive: the negated count, with the same bound. -/
def Count.neg {E : Type _} (neg : E → E) (c : E × ℕ) : E × ℕ := (neg c.1, c.2)

/-! ## Buses -/

/-- What an interaction builder records, in order.

It holds global messages, local lookups and exclusive groups. -/
structure Recorded (E : Type _) where
  global : List (String × List E × (E × ℕ)) := []
  local' : List (List (List E × (E × ℕ))) := []
  exclusive : List (String × List (E × (E × ℕ) × List E)) := []

/-- Record one global message. -/
def Recorded.push_interaction {E : Type _} (r : Recorded E) (bus_name : String) (fields : List E)
    (count : E × ℕ) : Recorded E :=
  { r with global := r.global ++ [(bus_name, fields, count)] }

/-- Record one exclusive group. -/
def Recorded.push_exclusive_interaction {E : Type _} (r : Recorded E) (bus_name : String)
    (branches : List (E × (E × ℕ) × List E)) : Recorded E :=
  { r with exclusive := r.exclusive ++ [(bus_name, branches)] }

/-- Query a table: one message with the given count. -/
def LookupBus.lookup_key {E : Type _} (bus : String) (r : Recorded E) (key : List E)
    (count : E × ℕ) : Recorded E :=
  r.push_interaction bus key count

/-- Provide a table entry: the negated number of lookups, as a provided count of weight 0. -/
def LookupBus.table_entry {E : Type _} (neg : E → E) (bus : String) (r : Recorded E)
    (key : List E) (num_lookups : E) : Recorded E :=
  r.push_interaction bus key (neg num_lookups, 0)

/-- Query a table with one of several exclusive keys.

Each branch is a unit query gated by its flag. -/
def LookupBus.lookup_key_exclusive {E : Type _} (one : E) (bus : String) (r : Recorded E)
    (branches : List (E × List E)) : Recorded E :=
  r.push_exclusive_interaction bus (branches.map fun (flag, key) => (flag, (one, 1), key))

/-- Send a message. -/
def PermutationCheckBus.send {E : Type _} (bus : String) (r : Recorded E) (fields : List E)
    (count : E × ℕ) : Recorded E :=
  r.push_interaction bus fields count

/-- Receive a message: a send with the negated count and the same bound. -/
def PermutationCheckBus.receive {E : Type _} (neg : E → E) (bus : String) (r : Recorded E)
    (fields : List E) (count : E × ℕ) : Recorded E :=
  r.push_interaction bus fields (Count.neg neg count)

/-! ## The debug balance check -/

/-- Add a key's multiplicity to a multiset.

A zero multiplicity is skipped, and a known key adds up. -/
def MultiSet.add {κ F : Type _} [DecidableEq κ] [Field F] [DecidableEq F] (m : List (κ × F))
    (key : κ) (multiplicity : F) : List (κ × F) :=
  if multiplicity = 0 then m
  else if m.any (·.1 = key) then m.map fun e => if e.1 = key then (e.1, e.2 + multiplicity) else e
  else m ++ [(key, multiplicity)]

/-- The multiset is empty when every net multiplicity is zero.

Otherwise the check panics. -/
def MultiSet.assert_empty {κ F : Type _} [Field F] [DecidableEq F] (m : List (κ × F)) : Bool :=
  m.all (·.2 = 0)

/-- One AIR instance for the debug check: its traces, public values and lookups. -/
structure LookupDebugInstance (F : Type) where
  main_trace : Mat F
  preprocessed_trace : Option (Mat F)
  public_values : List F
  lookups : List (Lookup F)

variable {F : Type} [Field F] [DecidableEq F]

/-- Add every row's tuples of one lookup, a flag multiplying an exclusive branch's count.

Resolution uses the debug row builder, whose periodic values are empty. -/
def accumulate_lookup (inst : LookupDebugInstance F) (lookup : Lookup F) (m : List (List F × F)) :
    Option (List (List F × F)) :=
  let height := inst.main_trace.height
  (List.range height).foldlM (fun m row => do
    let ctx := rowContext inst.main_trace inst.preprocessed_trace inst.public_values row
    lookup.elements.zipIdx.foldlM (fun m (elements, tuple_idx) => do
      let key ← elements.mapM (resolve ctx ())
      let count ← resolve ctx () (← lookup.multiplicities[tuple_idx]?)
      let multiplicity ← match lookup.flags with
        | some flags => do pure (count * (← resolve ctx () (← flags[tuple_idx]?)))
        | none => pure count
      pure (MultiSet.add m key multiplicity)) m) m

/-- The debug balance check.

Each local lookup balances on its own.
Each global bus balances across every instance. -/
def check_lookups (instances : List (LookupDebugInstance F)) : Option Bool := do
  let locals_ok ← instances.allM fun inst =>
    inst.lookups.allM fun lookup =>
      match lookup.kind with
      | .Local => do pure (MultiSet.assert_empty (← accumulate_lookup inst lookup []))
      | .Global _ => pure true
  let global_sets ← instances.foldlM (fun (sets : List (String × List (List F × F))) inst =>
    inst.lookups.foldlM (fun sets lookup =>
      match lookup.kind with
      | .Local => pure sets
      | .Global bus => do
        let current := (sets.find? (·.1 = bus)).map (·.2) |>.getD []
        let updated ← accumulate_lookup inst lookup current
        if sets.any (·.1 = bus) then
          pure (sets.map fun s => if s.1 = bus then (bus, updated) else s)
        else pure (sets ++ [(bus, updated)])) sets) []
  pure (locals_ok && global_sets.all fun s => MultiSet.assert_empty s.2)

/-! ## Indexed declarations -/

/-- Which committed window a column index addresses. -/
inductive TraceWindow where
  | Main
  | Preprocessed
  deriving DecidableEq

/-- Why indexed declarations are rejected, as far as one AIR's widths can tell. -/
inductive IndexedLookupError where
  | ColumnOutOfRange (table : String) (column width : ℕ)
  | RepeatedColumn (table : String) (column : ℕ)
  | EmptyPayload (table : String)
  | EmptyTable (table : String)
  deriving DecidableEq

/-- Reject a column out of range or named twice, at the first offence. -/
def check_columns (columns : List ℕ) (width : ℕ) (table : String) :
    Except IndexedLookupError Unit :=
  columns.zipIdx.forM fun (column, position) => do
    if column ≥ width then throw (.ColumnOutOfRange table column width)
    if (columns.take position).contains column then throw (.RepeatedColumn table column)

/-- Check every read, then every table, against the AIR's widths.

A read's position must be a main column, and its payload nonempty and valid.

A table's columns must be nonempty and valid in its window. -/
def IndexedLookups.new (reads : List (String × ℕ × List ℕ))
    (tables : List (String × TraceWindow × List ℕ)) (main_width preprocessed_width : ℕ) :
    Except IndexedLookupError Unit := do
  reads.forM fun (table, position, payload) => do
    if position ≥ main_width then throw (.ColumnOutOfRange table position main_width)
    if payload.isEmpty then throw (.EmptyPayload table)
    check_columns payload main_width table
  tables.forM fun (tname, window, columns) => do
    let width := match window with
      | .Main => main_width
      | .Preprocessed => preprocessed_width
    if columns.isEmpty then throw (.EmptyTable tname)
    check_columns columns width tname

end p3_lookup.mirror
