/-
Transcriptions of the lookup layout and of the claim it hands to the zerocheck.

These do not extract.
They are generic over the field traits and the AIR, which aeneas rejects.

Each definition transcribes one Rust item, named in the crate's mirror entries.

What a transcription abstracts:

- a declaration is its tuple count and its bus identifier
- the bus prefixes are a list, one per bus
- a machine word is a natural number, and a panic is none.

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

end p3_multi_stark.lookup.mirror
