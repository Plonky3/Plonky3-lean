/-
Transcriptions of the Keccak-f AIR over a field of characteristic 2: its column layout, its evaluation, its round on words and its trace generator.

The evaluation and the generator do not extract: they are generic over the builder and the field traits, which aeneas rejects.

The round on words and the rho-pi table are also extracted; the transcriptions are proved equal to them.

Each definition transcribes one Rust item, named in the crate's mirror entries.

What a transcription abstracts, beyond those of the other AIR:

* a state of 25 words indexed by lane 5 y + x is a map from that index to the word;
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

end p3_keccak_air.mirror.binary
