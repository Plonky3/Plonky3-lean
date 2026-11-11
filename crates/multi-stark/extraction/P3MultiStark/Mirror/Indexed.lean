/-
Transcription of the indexed-lookup planner, after each AIR's symbolic pass.

It does not extract.
It keeps a sorted map keyed by name, which the models lack, and the field is generic.

Each definition transcribes one Rust item, named in the crate's mirror entries.

What the transcription abstracts:

- the field is its bit width
- each AIR's declarations are given, already checked against its widths
- a sorted map keyed by name is a list in insertion order, sorted by name when read in order
- string order is the order of the characters, which UTF-8 byte order preserves
- a machine word is a natural number, and a panic is none.

Loops, early returns and the order of operations are kept.
-/
module

public import Mathlib.Data.List.Sort

@[expose] public section

namespace p3_multi_stark.indexed.mirror

/-- TraceWindow: which committed window a column index addresses. -/
inductive TraceWindow where
  | Main
  | Preprocessed
  deriving DecidableEq

/-- IndexedRead: a reader names a table, the column holding the entry, and the columns it pulls. -/
structure IndexedRead where
  table : String
  position : ℕ
  payload : List ℕ
  deriving DecidableEq

/-- IndexedTable: a provider names a table, its window, and the columns an entry carries. -/
structure IndexedTable where
  «name» : String
  window : TraceWindow
  columns : List ℕ
  deriving DecidableEq

/-- IndexedLookups: what one AIR declares, in emission order. -/
structure IndexedLookups where
  reads : List IndexedRead
  tables : List IndexedTable
  deriving DecidableEq

/-- IndexedLookups::is_empty. -/
def IndexedLookups.isEmpty (d : IndexedLookups) : Bool := d.reads.isEmpty && d.tables.isEmpty

/-- TablePlacement: the providing AIR, the window, the columns and the height. -/
structure TablePlacement where
  air : ℕ
  window : TraceWindow
  columns : List ℕ
  num_variables : ℕ
  deriving DecidableEq

/-- ReaderPlacement: the reading AIR, its position column, its pulled columns and its height. -/
structure ReaderPlacement where
  air : ℕ
  position : ℕ
  payload : List ℕ
  num_variables : ℕ
  deriving DecidableEq

/-- IndexedTablePlan: one table and its readers. -/
structure IndexedTablePlan where
  «name» : String
  table : TablePlacement
  readers : List ReaderPlacement
  deriving DecidableEq

/-- The planner's errors, as far as the whole batch can tell. -/
inductive IndexedPlanError where
  | TableWithoutEntries (table : String)
  | TableTooLarge (table : String) (num_variables bits : ℕ)
  | TableProvidedTwice (table : String) (first second : ℕ)
  | TableNotProvided (table : String) (air : ℕ)
  | WidthMismatch (table : String) (air pulled carried : ℕ)
  | TableNotRead (table : String) (air : ℕ)
  deriving DecidableEq

/-- One table declaration in the providers' loop.

The table needs a variable, an injective embedding, and a name no earlier provider used. -/
def addTable (bits : ℕ) (air num_variables : ℕ) (plans : List IndexedTablePlan) (table : IndexedTable) :
    Except IndexedPlanError (List IndexedTablePlan) :=
  if num_variables = 0 then .error (.TableWithoutEntries table.name)
  else if ¬ num_variables < bits then .error (.TableTooLarge table.name num_variables bits)
  else match plans.find? (·.name = table.name) with
    | some existing => .error (.TableProvidedTwice table.name existing.table.air air)
    | none => .ok (plans ++ [⟨table.name, ⟨air, table.window, table.columns, num_variables⟩, []⟩])

/-- One read in the readers' loop: its table must exist and carry as many columns as it pulls. -/
def addRead (air num_variables : ℕ) (plans : List IndexedTablePlan) (read : IndexedRead) :
    Except IndexedPlanError (List IndexedTablePlan) :=
  match plans.find? (·.name = read.table) with
  | none => .error (.TableNotProvided read.table air)
  | some plan =>
    if read.payload.length ≠ plan.table.columns.length then
      .error (.WidthMismatch read.table air read.payload.length plan.table.columns.length)
    else .ok (plans.map fun q => if q.name = read.table then
      { q with readers := q.readers ++ [⟨air, read.position, read.payload, num_variables⟩] } else q)

/-- IndexedPlan::from_declared, the planner after each AIR's symbolic pass.

- the slices must agree on length, or the planner panics
- a batch without declarations has no plan
- the providers' loop, in caller then emission order
- the readers' loop, in caller then emission order
- in name order, every table must have a reader. -/
def IndexedPlan.from_declared (bits : ℕ) (declared : List IndexedLookups) (num_variables : List ℕ) :
    Option (Except IndexedPlanError (Option (List IndexedTablePlan))) :=
  if declared.length ≠ num_variables.length then none
  else if declared.all IndexedLookups.isEmpty then some (.ok none)
  else some do
    let plans ← (declared.zipIdx).foldlM (fun plans (d, air) =>
      d.tables.foldlM (addTable bits air (num_variables.getD air 0)) plans) []
    let plans ← (declared.zipIdx).foldlM (fun plans (d, air) =>
      d.reads.foldlM (addRead air (num_variables.getD air 0)) plans) plans
    let sorted := plans.mergeSort fun a b => decide (a.name ≤ b.name)
    match sorted.find? (·.readers.isEmpty) with
    | some plan => throw (.TableNotRead plan.name plan.table.air)
    | none => pure (some sorted)

end p3_multi_stark.indexed.mirror
