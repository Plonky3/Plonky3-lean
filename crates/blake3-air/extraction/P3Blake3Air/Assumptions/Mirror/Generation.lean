/-
Transcriptions of the trace generator of the BLAKE3 AIR over a prime field.

These do not extract: they are generic over the field traits, which aeneas rejects, and they reinterpret rows through `align_to`.

Each definition transcribes one Rust item, named in the crate's mirror entries.

What a transcription abstracts:

* the field is a mathlib field F, a `u16` enters it as a natural number, and a `bool` as 0 or 1;
* a `u32` is a 32-bit vector, and a `usize` a natural number, whose casts to `u32` keep its low 32 bits;
* `counter.wrapping_shr(32)` is `counter / 2^32`, as on a 64-bit target, the extraction target;
* a row is the column struct with one function per field, and the trace's values are the rows' cells in the struct's `repr(C)` order;
* an array that a loop fills at every index is the function of its index, and an array written at one index is updated there;
* the reserved extra capacity, which does not change the trace, is ignored;
* the parallel iterators are the sequential maps they compute;
* a panic is none.

Loops, branches and the order of writes are kept.
-/
module

public import P3Blake3Air.Assumptions.Mirror.Air
public import Mathlib.Data.Nat.Bits

@[expose] public section

namespace p3_blake3_air.mirror

open p3_air.air.mirror

/-- A 32-bit word. -/
abbrev Word := BitVec 32

/-- A row of the column struct, field by field. -/
structure Blake3Cols (T : Type) where
  inputs : ℕ → ℕ → T
  chaining_values : ℕ → ℕ → ℕ → T
  counter_low : ℕ → T
  counter_hi : ℕ → T
  block_len : ℕ → T
  flags : ℕ → T
  initial_row0 : ℕ → ℕ → T
  initial_row2 : ℕ → ℕ → T
  full_rounds : ℕ → FullRound T
  final_round_helpers : ℕ → ℕ → T
  outputs : ℕ → ℕ → ℕ → T

namespace Blake3Cols

variable {T : Type}

/-- The zero state. -/
def zeroState [Zero T] : Blake3State T := ⟨fun _ _ => 0, fun _ _ => 0, fun _ _ => 0, fun _ _ => 0⟩

/-- The zero row, as the generator's buffer starts. -/
def zero [Zero T] : Blake3Cols T :=
  ⟨fun _ _ => 0, fun _ _ _ => 0, fun _ => 0, fun _ => 0, fun _ => 0, fun _ => 0, fun _ _ => 0,
    fun _ _ => 0, fun _ => ⟨zeroState, zeroState, zeroState, zeroState⟩, fun _ _ => 0,
    fun _ _ _ => 0⟩

/-- The cells of `n` words of `m` cells each, word by word. -/
def words (n m : ℕ) (f : ℕ → ℕ → T) : List T := (List.range n).flatMap fun j => (List.range m).map (f j)

/-- The cells of a state, in the struct's `repr(C)` order. -/
def stateCells (st : Blake3State T) : List T :=
  words 4 2 st.row0 ++ words 4 32 st.row1 ++ words 4 2 st.row2 ++ words 4 32 st.row3

/-- The cells of a full round. -/
def roundCells (fr : FullRound T) : List T :=
  stateCells fr.state_prime ++ stateCells fr.state_middle ++ stateCells fr.state_middle_prime ++
    stateCells fr.state_output

/-- The cells of a row, in the struct's `repr(C)` order. -/
def cells (r : Blake3Cols T) : List T :=
  words 16 32 r.inputs ++ words 2 128 (fun h i => r.chaining_values h (i / 32) (i % 32)) ++
    (List.range 32).map r.counter_low ++ (List.range 32).map r.counter_hi ++
    (List.range 32).map r.block_len ++ (List.range 32).map r.flags ++
    words 4 2 r.initial_row0 ++ words 4 2 r.initial_row2 ++
    (List.range 7).flatMap (fun i => roundCells (r.full_rounds i)) ++
    words 4 32 r.final_round_helpers ++
    words 4 128 (fun q i => r.outputs q (i / 32) (i % 32))

end Blake3Cols

variable {F : Type} [Field F]

/-- The bits of a word, least significant first: bit i is `val & (1 << i) != 0`. -/
def u32_to_bits_le (val : Word) : ℕ → F := fun i =>
  if val &&& (1#32 <<< i) ≠ 0 then 1 else 0

/-- The low 16 bits of a word, `w as u16`, as a field element. -/
def lowLimb (w : Word) : F := ((w.toNat % 2 ^ 16 : ℕ) : F)

/-- The high 16 bits of a word, `(w >> 16) as u16`, as a field element. -/
def highLimb (w : Word) : F := (((w >>> 16).toNat % 2 ^ 16 : ℕ) : F)

/-- IV word `i`: its low half plus its high half shifted up by 16. -/
def ivWord (i : ℕ) : Word := BitVec.ofNat 32 (ivHalf i 0) + (BitVec.ofNat 32 (ivHalf i 1) <<< 16)

/-- A state as the generator holds it: `state r i` is word i of row r. -/
abbrev WState := ℕ → ℕ → Word

/-- Half of a quarter round.

The first half rotates by 16 and 12, the second by 8 and 7. -/
def verifiable_half_round (a b c d m : Word) (flag : Bool) : Word × Word × Word × Word :=
  let (rot_1, rot_2) := if flag then (8, 7) else (16, 12)
  let a := a + b
  let a := a + m
  let d := (d ^^^ a).rotateRight rot_1
  let c := c + d
  let b := (b ^^^ c).rotateRight rot_2
  (a, b, c, d)

/-- Write a state into a trace state: rows 0 and 2 as limbs, rows 1 and 3 as bits. -/
def save_state_to_trace (state : WState) : Blake3State F :=
  ⟨fun i l => if l = 0 then lowLimb (state 0 i) else highLimb (state 0 i),
    fun i => u32_to_bits_le (state 1 i),
    fun i l => if l = 0 then lowLimb (state 2 i) else highLimb (state 2 i),
    fun i => u32_to_bits_le (state 3 i)⟩

/-- Write the words a half round returns into word positions (0, ia), (1, ib), (2, ic), (3, id). -/
def setWords (state : WState) (ia ib ic id : ℕ) (w : Word × Word × Word × Word) : WState :=
  let state := Function.update state 0 (Function.update (state 0) ia w.1)
  let state := Function.update state 1 (Function.update (state 1) ib w.2.1)
  let state := Function.update state 2 (Function.update (state 2) ic w.2.2.1)
  Function.update state 3 (Function.update (state 3) id w.2.2.2)

/-- Four half quarter rounds on the columns, or on the diagonals when `diag` holds. -/
def halfRounds (state : WState) (m_vec : ℕ → Word) (diag flag : Bool) (offset : ℕ) : WState :=
  (List.range 4).foldl (fun state i =>
    let (ib, ic, id) := if diag then ((i + 1) % 4, (i + 2) % 4, (i + 3) % 4) else (i, i, i)
    setWords state i ib ic id
      (verifiable_half_round (state 0 i) (state 1 ib) (state 2 ic) (state 3 id) (m_vec (offset + 2 * i)) flag))
    state

/-- Fill the four states of a full round, and return the state after the round. -/
def generate_trace_row_for_round (state : WState) (m_vec : ℕ → Word) : FullRound F × WState :=
  let state := halfRounds state m_vec false false 0
  let state_prime := save_state_to_trace state
  let state := halfRounds state m_vec false true 1
  let state_middle := save_state_to_trace state
  let state := halfRounds state m_vec true false 8
  let state_middle_prime := save_state_to_trace state
  let state := halfRounds state m_vec true true 9
  (⟨state_prime, state_middle, state_middle_prime, save_state_to_trace state⟩, state)

/-- Fill the row of one compression: 16 message words and 8 chaining words, under a counter and a block length. -/
def generate_trace_rows_for_perm (input : ℕ → Word) (counter block_len : ℕ) : Blake3Cols F :=
  let cv : ℕ → Word := fun i => input (16 + i)
  let state : WState := fun r i =>
    if r = 0 then cv i
    else if r = 1 then cv (4 + i)
    else if r = 2 then ivWord i
    else if i = 0 then BitVec.ofNat 32 counter
    else if i = 1 then BitVec.ofNat 32 (counter / 2 ^ 32)
    else if i = 2 then BitVec.ofNat 32 block_len
    else 0
  -- Seven rounds, the message permuted between rounds.
  let (rounds, state, _) := (List.range 7).foldl
    (fun (acc : (ℕ → FullRound F) × WState × (ℕ → Word)) r =>
      let (rounds, state, m_vec) := acc
      let m_vec := if r = 0 then m_vec else permute m_vec
      let (fr, state) := generate_trace_row_for_round state m_vec
      (Function.update rounds r fr, state, m_vec))
    ((Blake3Cols.zero (T := F)).full_rounds, state, input)
  { inputs := fun i => u32_to_bits_le (input i)
    chaining_values := fun h j => u32_to_bits_le (input (16 + 4 * h + j))
    counter_low := u32_to_bits_le (BitVec.ofNat 32 counter)
    counter_hi := u32_to_bits_le (BitVec.ofNat 32 (counter / 2 ^ 32))
    block_len := u32_to_bits_le (BitVec.ofNat 32 block_len)
    flags := fun _ => 0
    initial_row0 := fun i l => if l = 0 then lowLimb (cv i) else highLimb (cv i)
    initial_row2 := fun i l => (ivHalf i l : F)
    full_rounds := rounds
    final_round_helpers := fun i => u32_to_bits_le (state 2 i)
    outputs := fun q i =>
      if q = 0 then u32_to_bits_le (state 0 i ^^^ state 2 i)
      else if q = 1 then u32_to_bits_le (state 1 i ^^^ state 3 i)
      else if q = 2 then u32_to_bits_le (state 2 i ^^^ input (16 + i))
      else u32_to_bits_le (state 3 i ^^^ input (20 + i)) }

/-- The trace of the given compressions, one per row: row k has counter k and block length the number of rows.

It panics unless the number of inputs is a power of two, which `n &&& (n - 1) = 0` with n > 0 tests. -/
def generate_trace_rows (inputs : List (ℕ → Word)) (_extra_capacity_bits : ℕ) : Option (Mat F) :=
  let num_rows := inputs.length
  if num_rows ≠ 0 ∧ num_rows &&& (num_rows - 1) = 0 then
    some ⟨NUM_BLAKE3_COLS, (inputs.zipIdx.map fun (input, counter) =>
      generate_trace_rows_for_perm input counter num_rows).flatMap Blake3Cols.cells⟩
  else none

end p3_blake3_air.mirror
