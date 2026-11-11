/-
Transcriptions of the Keccak-f AIR over a field of characteristic 2: its column layout, its evaluation, its round on words, its trace generator and its packed trace generator.

The evaluation and the generator do not extract: they are generic over the builder and the field traits, which aeneas rejects.

The round on words and the rho-pi table are also extracted; the transcriptions are proved equal to them.

Each definition transcribes one Rust item, named in the crate's mirror entries.

What a transcription abstracts, beyond those of the other AIR:

* a state of 25 words indexed by lane 5 y + x is a map from that index to the word;
* a block of packed words, and the 25 rows of witness words, are maps from the index to the entry;
* the slice of the inputs a block overlaps is a drop then a take, and an index into a block never leaves it;
* the trailing-zero count of a word is the index of its lowest set bit;
* the parallel loop over blocks is a sequential loop, and the scratch rows are threaded through it;
* the body of the loop over a block's rows is a separate definition;
* a panic is none.

Loops, branches and the order of assertions are kept.
-/
module

public import P3KeccakAir.Assumptions.Mirror.Generation

@[expose] public section

namespace p3_keccak_air.mirror.binary

open p3_air.builder.mirror p3_air.air.mirror p3_keccak_air.mirror

/-! ## The column layout -/

/-- The rows of one permutation: the input rows of the 24 rounds, then the output row. -/
def KECCAK_BINARY_ROWS_PER_PERM : ℕ := 25

-- The column indices of the struct's fields, in declaration order.
namespace col

def round_flags (r : ℕ) : ℕ := r
def a (y x z : ℕ) : ℕ := 25 + 320 * y + 64 * x + z

end col

/-- The number of columns. -/
def NUM_KECCAK_BINARY_COLS : ℕ := 1625

/-- The lane of A' that rho and pi rotate into B[x, y]: (y', x', rot) with x' = (x + 3 y) mod 5 and y' = x. -/
def rho_pi_source (x y : ℕ) : ℕ × ℕ × ℕ :=
  let source_x := (x + 3 * y) % 5
  let source_y := x
  (source_y, source_x, rOf source_x source_y)

/-! ## The evaluation -/

variable {F E : Type} [Field F]

/-- The evaluation of the characteristic-2 Keccak-f AIR, with or without the state booleanity. -/
def eval (constrain_booleanity : Bool) {S : Type} (B : AirBuilder F E S) (s : S) : S :=
  let main := B.main s
  let loc : ℕ → E := fun i => main.current.getD i (B.const 0)
  let nxt : ℕ → E := fun i => main.next.getD i (B.const 0)
  let flags : ℕ → E := fun r => loc (col.round_flags r)
  let next_flags : ℕ → E := fun r => nxt (col.round_flags r)
  let output_flag := flags NUM_ROUNDS
  -- The first row is the input row of round 0.
  let s := (B.when_first_row s).assert_one s (flags 0)
  let s := (B.when_first_row s).assert_zeros s ((List.range NUM_ROUNDS).map fun i => flags (i + 1))
  -- Round r < 23 is followed by round r + 1.
  let s := B.assert_zeros s ((List.range (NUM_ROUNDS - 1)).map fun r =>
    B.add (next_flags (r + 1)) (flags r))
  -- Round 23 and an output row are each followed by round 0 or an output row.
  let s := B.assert_zero s
    (B.add (B.add (B.add (next_flags 0) (next_flags NUM_ROUNDS)) (flags (NUM_ROUNDS - 1))) output_flag)
  -- No row is both round 0 and an output row.
  let s := B.assert_zero s (B.mul (flags 0) output_flag)
  -- Every state bit is a bit.
  let s := if constrain_booleanity then
      (List.range 5).foldl (fun s y => (List.range 5).foldl (fun s x =>
        B.assert_bools s ((List.range 64).map fun z => loc (col.a y x z))) s) s
    else s
  -- Theta.
  let c : ℕ → ℕ → E := fun x z => sum B.toExprOps ((List.range 5).map fun y => loc (col.a y x z))
  let d : ℕ → ℕ → E := fun x z => B.add (c ((x + 4) % 5) z) (c ((x + 1) % 5) ((z + 63) % 64))
  let a_prime : ℕ → ℕ → ℕ → E := fun y x z => B.add (d x z) (loc (col.a y x z))
  -- Rho and pi.
  let b : ℕ → ℕ → ℕ → E := fun x y z =>
    let (source_y, source_x, rot) := rho_pi_source x y
    a_prime source_y source_x ((z + 64 - rot) % 64)
  -- A round row maps its state to the next row's state, gated by 1 + output_flag.
  let not_output := B.add (B.const 1) output_flag
  (List.range 5).foldl (fun s y => (List.range 5).foldl (fun s x =>
    B.assert_zeros s ((List.range 64).map fun z =>
      let chi := B.add (b x y z) (B.mul (B.add (B.const 1) (b ((x + 1) % 5) y z)) (b ((x + 2) % 5) y z))
      let round_map := B.mul not_output (B.add chi (nxt (col.a y x z)))
      if x = 0 ∧ y = 0 then
        let rc_bit := sum B.toExprOps
          (((List.range NUM_ROUNDS).filter fun r => rcBit r z ≠ 0).map fun r => flags r)
        B.add round_map rc_bit
      else round_map)) s) s

/-- The number of state bits in a row. -/
def NUM_STATE_BITS : ℕ := 1600

/-- The round-flag constraints: 25 on the first row, 23 round steps, the wrap, and exclusivity. -/
def NUM_FLAG_CONSTRAINTS : ℕ := KECCAK_BINARY_ROWS_PER_PERM + (NUM_ROUNDS - 1) + 2

/-- The number of constraints the AIR reports: the flags, the booleanity if stated, and the round map. -/
def num_constraints (constrain_booleanity : Bool) : Option ℕ :=
  let booleanity := if constrain_booleanity then NUM_STATE_BITS else 0
  some (NUM_FLAG_CONSTRAINTS + booleanity + NUM_STATE_BITS)

/-! ## The round on words -/

/-- A state of 25 words, indexed by lane 5 y + x. -/
abbrev LState := ℕ → Word

/-- Apply round `round` of Keccak-f to a state indexed by lane 5 y + x. -/
def keccak_round (state : LState) (round : ℕ) : LState :=
  -- Theta.
  let c : ℕ → Word := fun x => (List.range 5).foldl (fun acc y => acc ^^^ state (5 * y + x)) 0
  let d : ℕ → Word := fun x => c ((x + 4) % 5) ^^^ (c ((x + 1) % 5)).rotateLeft 1
  -- Rho and pi.
  let b : ℕ → Word := fun i =>
    let (source_y, source_x, rot) := rho_pi_source (i % 5) (i / 5)
    (state (5 * source_y + source_x) ^^^ d source_x).rotateLeft rot
  -- Chi.
  let state : LState := fun i =>
    let y := i / 5
    let x := i % 5
    b i ^^^ ((~~~b (5 * y + (x + 1) % 5)) &&& b (5 * y + (x + 2) % 5))
  -- Iota.
  Function.update state 0 (state 0 ^^^ BitVec.ofNat 64 (RC.getD round 0))

/-! ## The trace generator -/

/-- A row of the column struct: the round flags, then the state bits. -/
structure KeccakBinaryCols (T : Type) where
  round_flags : ℕ → T
  a : ℕ → ℕ → ℕ → T

/-- The zero row. -/
def KeccakBinaryCols.zero {T : Type} [Zero T] : KeccakBinaryCols T := ⟨fun _ => 0, fun _ _ _ => 0⟩

/-- The cells of a row, in the struct's `repr(C)` order. -/
def KeccakBinaryCols.cells {T : Type} (r : KeccakBinaryCols T) : List T :=
  (List.range 25).map r.round_flags ++
    (List.range 5).flatMap fun y => (List.range 5).flatMap fun x => (List.range 64).map (r.a y x)

/-- Write the bits of a state into the state columns of a row. -/
def write_state (row : KeccakBinaryCols F) (state : LState) : KeccakBinaryCols F :=
  { row with a := fun y x => u64_to_bits_le (state (5 * y + x)) }

/-- Fill the 25 rows of one permutation, starting from zeroed rows. -/
def generate_perm_rows (input : LState) : List (KeccakBinaryCols F) :=
  let (round_rows, state) := (List.range NUM_ROUNDS).foldl
    (fun (acc : List (KeccakBinaryCols F) × LState) round =>
      let (rows, state) := acc
      let row : KeccakBinaryCols F :=
        { KeccakBinaryCols.zero with round_flags := Function.update (fun _ => 0) round 1 }
      let row := write_state row state
      (rows ++ [row], keccak_round state round)) ([], input)
  let output_row : KeccakBinaryCols F :=
    { KeccakBinaryCols.zero with round_flags := Function.update (fun _ => 0) NUM_ROUNDS 1 }
  round_rows ++ [write_state output_row state]

/-- The trace of the given permutations, padded to a power-of-two height with output rows of the zero state.

It panics when 2 is not 0 in the field, or when there is no input. -/
def generate_binary_trace_rows [DecidableEq F] (inputs : List LState) (_extra_capacity_bits : ℕ) :
    Option (Mat F) :=
  if (2 : F) ≠ 0 then none
  else if inputs = [] then none
  else
    let num_perm_rows := inputs.length * KECCAK_BINARY_ROWS_PER_PERM
    let num_rows := num_perm_rows.nextPowerOfTwo
    let perm_rows := inputs.flatMap generate_perm_rows
    -- The state of a padding row is already zero.
    let padding_row : KeccakBinaryCols F :=
      { KeccakBinaryCols.zero with round_flags := Function.update (fun _ => 0) NUM_ROUNDS 1 }
    let padding_rows := List.replicate (num_rows - num_perm_rows) padding_row
    some ⟨NUM_KECCAK_BINARY_COLS, (perm_rows ++ padding_rows).flatMap KeccakBinaryCols.cells⟩

/-! ## The packed trace generator -/

/-- The number of trace rows packed into one word. -/
def BITS_PER_WORD : ℕ := 64

/-- The column of the output flag, the only set cell of a padding row. -/
def OUTPUT_FLAG_COLUMN : ℕ := NUM_ROUNDS

/-- The number of trailing zero bits of a 32-bit word, 32 for the zero word. -/
def trailing_zeros (x : BitVec 32) : ℕ := ((List.range 32).find? (x.getLsbD ·)).getD 32

/-- The witness words of one row: the one-hot row kind, then the state lane by lane. -/
structure RowWords where
  flags : BitVec 32
  state : LState

/-- The default row: no flag and the zero state. -/
def RowWords.default : RowWords := ⟨0, fun _ => 0⟩

/-- Fill the words of the 25 rows of one permutation. -/
def generate_perm_words (rows : ℕ → RowWords) (input : LState) : ℕ → RowWords :=
  let (rows, state) := (List.range NUM_ROUNDS).foldl
    (fun (acc : (ℕ → RowWords) × LState) round =>
      let (rows, state) := acc
      (Function.update rows round ⟨1#32 <<< round, state⟩, keccak_round state round)) (rows, input)
  Function.update rows NUM_ROUNDS ⟨1#32 <<< NUM_ROUNDS, state⟩

/-- Set bit `shift` of every column of a block that holds a 1 cell of a row. -/
def pack_row (block : ℕ → BitVec 64) (words : RowWords) (shift : ℕ) : ℕ → BitVec 64 :=
  -- The row kind is one-hot, so exactly one flag column takes a bit.
  let flag := trailing_zeros words.flags
  let block := Function.update block flag (block flag ||| 1#64 <<< shift)
  -- A lane's cells are its bits, so its 64 columns take them in one sweep.
  (List.range 25).foldl (fun block lane =>
    (List.range 64).foldl (fun block index =>
      let column := KECCAK_BINARY_ROWS_PER_PERM + 64 * lane + index
      Function.update block column (block column ||| ((words.state lane >>> index) &&& 1) <<< shift))
      block) block

/-- Pack the rows `64 b` to `64 b + 63` of the trace into the block of physical row `b`. -/
def pack_block (block : ℕ → BitVec 64) (block_index : ℕ) (inputs : List LState) (num_rows : ℕ)
    (rows : ℕ → RowWords) : (ℕ → BitVec 64) × (ℕ → RowWords) :=
  let num_perm_rows := inputs.length * KECCAK_BINARY_ROWS_PER_PERM
  let block_start := block_index * BITS_PER_WORD
  let block_end := min (block_start + BITS_PER_WORD) num_rows
  let perm_rows_end := min block_end num_perm_rows
  let (block, rows) :=
    if block_start < perm_rows_end then
      let first_perm := block_start / KECCAK_BINARY_ROWS_PER_PERM
      let last_perm := (perm_rows_end - 1) / KECCAK_BINARY_ROWS_PER_PERM
      -- Each permutation overlapping the block is regenerated, and its rows inside it are read out.
      ((inputs.drop first_perm).take (last_perm + 1 - first_perm)).zipIdx.foldl
        (fun (acc : (ℕ → BitVec 64) × (ℕ → RowWords)) (input, offset) =>
          let (block, rows) := acc
          let rows := generate_perm_words rows input
          let perm_start := (first_perm + offset) * KECCAK_BINARY_ROWS_PER_PERM
          let start := max block_start perm_start
          let stop := min perm_rows_end (perm_start + KECCAK_BINARY_ROWS_PER_PERM)
          let block := (List.range' start (stop - start)).foldl
            (fun block row => pack_row block (rows (row - perm_start)) (row - block_start)) block
          (block, rows)) (block, rows)
    else (block, rows)
  -- The state of a padding row is zero.
  let pad_start := max block_start num_perm_rows
  let block := (List.range' pad_start (block_end - pad_start)).foldl (fun block row =>
    Function.update block OUTPUT_FLAG_COLUMN
      (block OUTPUT_FLAG_COLUMN ||| 1#64 <<< (row - block_start))) block
  (block, rows)

/-- The trace packed into one word per 64 rows.

Bit `k` of word `(w, j)` is set when cell `(64 w + k, j)` is 1, and the bits past the height are zero.

The scratch rows of one permutation are reused from block to block.

It panics when 2 is not 0 in the field, or when there is no input. -/
def generate_binary_trace_packed [DecidableEq F] (inputs : List LState) : Option (Mat (BitVec 64)) :=
  if (2 : F) ≠ 0 then none
  else if inputs = [] then none
  else
    let num_perm_rows := inputs.length * KECCAK_BINARY_ROWS_PER_PERM
    let num_rows := num_perm_rows.nextPowerOfTwo
    let num_blocks := (num_rows + BITS_PER_WORD - 1) / BITS_PER_WORD
    let (words, _) := (List.range num_blocks).foldl
      (fun (acc : List (BitVec 64) × (ℕ → RowWords)) block_index =>
        let (words, rows) := acc
        let (block, rows) := pack_block (fun _ => 0) block_index inputs num_rows rows
        (words ++ (List.range NUM_KECCAK_BINARY_COLS).map block, rows)) ([], fun _ => RowWords.default)
    some ⟨NUM_KECCAK_BINARY_COLS, words⟩

end p3_keccak_air.mirror.binary
