/-
Transcriptions of the lookup layout and of the claim it hands to the zerocheck.

These do not extract.
They are generic over the field traits and the AIR, which aeneas rejects.

Each definition transcribes one Rust item, named in the crate's mirror entries.

What a transcription abstracts:

- a planned declaration is its tuple count and its bus identifier
- a declared one is its kind, its tuple widths, its flags and its count weight
- a symbolic expression is whether it reads a periodic column
- a sorted map keyed by bus is a list in insertion order, since only insertion order fixes an identifier
- a stable sort by decreasing height is a merge sort, which is stable
- the bus prefixes are a list, one per bus
- a machine word is a natural number, and a panic is none
- an overflow that panics in a debug build is a panic.

Loops and the order of operations are kept.
-/
module

public import P3MultilinearUtil

@[expose] public section

namespace p3_multi_stark.lookup.mirror

open p3_multilinear_util.point.mirror

/-- LookupInstancePlan: one active AIR, its offset, and per declaration its tuple count and bus. -/
structure LookupInstancePlan where
  air_index : ℕ
  num_variables : ℕ
  base_offset : ℕ
  tuple_counts : List ℕ
  bus_ids : List ℕ

/-- log2_ceil_usize. -/
def log2_ceil_usize (n : ℕ) : ℕ := if n ≤ 1 then 0 else Nat.log2 (n - 1) + 1

/-- The placement loop of LookupPlan::build.

Each instance starts at the running height, and adds one block of its height per tuple. -/
def place (height : ℕ) : List LookupInstancePlan → List LookupInstancePlan × ℕ
  | [] => ([], height)
  | i :: is =>
    let rest := place (height + i.tuple_counts.sum * 2 ^ i.num_variables) is
    ({ i with base_offset := height } :: rest.1, rest.2)

/-- AirLinkClaim::new's equality weights for one declaration's tuples.

They start at a block index, and each tuple takes the next block. -/
def tupleWeights {F EF : Type _} [Field F] [Field EF] [Algebra F EF] (prefix_len : ℕ)
    (point_prefix : List EF) : ℕ → ℕ → Option (List EF)
  | _, 0 => some []
  | block_index, count + 1 => do
    let vertex ← Point.hypercube (F := F) block_index prefix_len
    let w ← Point.eval_eq (F := F) (EF := EF) vertex point_prefix
    let ws ← tupleWeights (F := F) prefix_len point_prefix (block_index + 1) count
    pure (w :: ws)

/-- The equality weights AirLinkClaim::new gives one instance, per declaration.

The prefix the weights read is the point's coordinates above the instance's own. -/
def blockWeights {F EF : Type _} [Field F] [Field EF] [Algebra F EF] (num_variables : ℕ)
    (point : List EF) (inst : LookupInstancePlan) : Option (List (List EF)) :=
  if num_variables < inst.num_variables then none
  else
    let prefix_len := num_variables - inst.num_variables
    if point.length < prefix_len then none
    else
      let point_prefix := point.take prefix_len
      (inst.tuple_counts.foldlM (fun (acc : List (List EF) × ℕ) count => do
        let ws ← tupleWeights (F := F) prefix_len point_prefix acc.2 count
        pure (acc.1 ++ [ws], acc.2 + count)) ([], inst.base_offset >>> inst.num_variables)).map
        fun acc : List (List EF) × ℕ => acc.1

/-- The folded claim of AirLinkClaim::new: N(q) + theta (D(q) - 1). -/
def claimed_sum {EF : Type _} [Field EF] (numerator denominator theta : EF) : EF :=
  numerator + theta * (denominator - 1)

/-- The bus constant of AirLinkClaim::new: theta (prefix - 1). -/
def theta_bus_offset {EF : Type _} [Field EF] (theta bus_prefix : EF) : EF := theta * (bus_prefix - 1)

/-- Challenges::new's bus prefixes: alpha + (i + 1) beta^W, for each bus i. -/
def bus_prefixes {EF : Type _} [Field EF] (alpha beta : EF) (max_width num_buses : ℕ) : List EF :=
  (List.range num_buses).map fun i => alpha + ((i : EF) + 1) * beta ^ max_width

/-- LookupPlan::build's bus-count check.

The identifiers must stay distinct modulo p. -/
def bus_capacity_ok (p num_buses : ℕ) : Bool := !(p < num_buses)

/-! ## The planner -/

/-- Kind: whether a declaration's bus is private to it or shared by name. -/
inductive Kind where
  | Local
  | Global («name» : String)
  deriving DecidableEq

/-- Lookup: one declaration, as the planner reads it.

- the scope of its bus
- the width of each tuple, in order
- whether it carries exclusive flags
- whether one of its expressions reads a periodic column
- the static bound on its count per row -/
structure Lookup where
  kind : Kind
  widths : List ℕ
  exclusive : Bool
  periodic : Bool
  count_weight : ℕ

/-- Whether a declaration emits at least one tuple. -/
def Lookup.active (l : Lookup) : Bool := !l.widths.isEmpty

/-- LookupBus: a bus shared by name, or private to one declaration of one AIR. -/
inductive LookupBus where
  | Global («name» : String)
  | Local (instance_index interaction_index : ℕ)
  deriving DecidableEq

/-- The bus of the declaration at a position of an AIR. -/
def busOf (air index : ℕ) (l : Lookup) : LookupBus :=
  match l.kind with
  | .Local => .Local air index
  | .Global nm => .Global nm

/-- LookupError: the planner's rejections. -/
inductive LookupError where
  | BusIdentifierCapacityExceeded
  | UnsupportedCharacteristic
  | MultiplicityHeightBoundExceeded (weighted_height_sum : ℕ)
  deriving DecidableEq

/-- LookupPlan: the active AIRs in placement order, the widest payload, the bus count and the table size. -/
structure LookupPlan where
  instances : List LookupInstancePlan
  max_width : ℕ
  num_buses : ℕ
  num_variables : ℕ

/-- `1usize << n`, which overflows at 64 and panics in a debug build. -/
def shl_one (n : ℕ) : Option ℕ := if n < 64 then some (2 ^ n) else none

/-- A machine-word product or sum, which panics in a debug build when it overflows. -/
def word (n : ℕ) : Option ℕ := if n < 2 ^ 64 then some n else none

/-- The bus table: each bus with its identifier and the width its first declaration fixed. -/
abbrev BusTable := List (LookupBus × ℕ × ℕ)

/-- One declaration's bus identifier, in LookupPlan::build's inner closure.

A declaration without tuples keeps the dummy identifier 0 and allocates nothing.

A new bus takes the next identifier and fixes its width.

A known named bus must keep its width, or the planner panics. -/
def assignBus (air : ℕ) (acc : BusTable × ℕ × List ℕ) (lj : Lookup × ℕ) :
    Option (BusTable × ℕ × List ℕ) :=
  let (table, max_width, ids) := acc
  let (lookup, index) := lj
  if lookup.widths.isEmpty then some (table, max_width, ids ++ [0]) else
  let bus := busOf air index lookup
  let width := lookup.widths.headD 0
  match table.lookup bus with
  | none => some (table ++ [(bus, table.length, width)], max max_width width, ids ++ [table.length])
  | some (id, established) =>
    match bus with
    | .Global _ => if width = established then some (table, max max_width width, ids ++ [id]) else none
    | .Local _ _ => none

/-- One active AIR before placement: its position, its height and its declarations. -/
structure ActiveAir where
  air_index : ℕ
  num_variables : ℕ
  lookups : List Lookup

/-- One step of LookupPlan::build's placement loop.

The AIR starts at the running height, adds one block of its height per tuple, and numbers its buses. -/
def planStep (acc : List LookupInstancePlan × BusTable × ℕ × ℕ) (inst : ActiveAir) :
    Option (List LookupInstancePlan × BusTable × ℕ × ℕ) := do
  let (done, table, max_width, active_height) := acc
  let trace_height ← shl_one inst.num_variables
  let counts := inst.lookups.map (·.widths.length)
  let instance_height ← word (counts.sum * trace_height)
  let next ← word (active_height + instance_height)
  let (table, max_width, ids) ← (inst.lookups.zipIdx).foldlM (assignBus inst.air_index)
    (table, max_width, [])
  pure (done ++ [⟨inst.air_index, inst.num_variables, active_height, counts, ids⟩], table, max_width, next)

/-- LookupPlan::build, after each AIR's symbolic pass.

The characteristic of the base field is p.

Each AIR is its list of declarations, in emission order, with its trace height's logarithm.

The checks run in the Rust order:

- the slices agree on length, or the planner panics
- characteristic two with a tuple is an error
- an exclusive or periodic declaration panics
- a height of 64 or more overflows its shift and panics
- the weighted height sum must stay below p
- the placement loop, which panics on an overflow or a width change on a named bus
- the bus count must not exceed p
- a widest payload of 0 panics -/
def LookupPlan.build (p : ℕ) (airs : List (List Lookup)) (num_variables : List ℕ) :
    Option (Except LookupError (Option LookupPlan)) :=
  if airs.length ≠ num_variables.length then none
  else if p = 2 ∧ airs.any (·.any Lookup.active) then some (.error .UnsupportedCharacteristic)
  else if airs.flatten.any (fun l => l.exclusive || l.periodic) then none
  else (num_variables.mapM shl_one).bind fun heights =>
    let sum := (List.zipWith (fun ls h => (ls.map (·.count_weight)).sum * h) airs heights).sum
    if p ≤ sum then some (.error (.MultiplicityHeightBoundExceeded sum))
    else
      let active := ((airs.zip num_variables).zipIdx).filterMap fun ((ls, n), air) =>
        if ls.any Lookup.active then some (⟨air, n, ls⟩ : ActiveAir) else none
      let sorted := active.mergeSort fun a b => decide (b.num_variables ≤ a.num_variables)
      if sorted.isEmpty then some (.ok none)
      else (sorted.foldlM planStep ([], [], 0, 0)).bind fun (instances, table, max_width, active_height) =>
        if p < table.length then some (.error .BusIdentifierCapacityExceeded)
        else if max_width = 0 then none
        else some (.ok (some ⟨instances, max_width, table.length, log2_ceil_usize active_height⟩))

end p3_multi_stark.lookup.mirror
