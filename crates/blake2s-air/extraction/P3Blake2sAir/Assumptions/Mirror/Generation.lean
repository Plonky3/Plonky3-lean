/-
Transcriptions of the BLAKE2s trace generator: the compression input, the G step on words, the row, its cells, the generator, and the read-back of the state and the output.

The generator does not extract: it is generic over the field traits, which aeneas rejects.

The G step on words and the carry word are also extracted, and proved equal to these.

Each definition transcribes one Rust item, named in the crate's mirror entries.

What a transcription abstracts, beyond those of the evaluation:

* the working state, an array of four rows of four words, is a map from the row and the position to the word;
* the counter, a `u64`, is a 64-bit vector;
* the parallel loop over rows is a map;
* the reserved capacity of the trace is dropped, since it does not change the trace;
* a panic is none.

Loops, branches and the order of operations are kept.
-/
module

public import P3Blake2sAir.Assumptions.Mirror.Air

@[expose] public section

namespace p3_blake2s_air.mirror

open p3_air.air.mirror

/-- The inputs of one compression. -/
structure Blake2sCompressionInput where
  chaining_value : List Word
  block : List Word
  counter : BitVec 64
  last_block : Bool

/-- The finalization word: all ones when the flag is set, zero otherwise. -/
def Blake2sCompressionInput.flag_word (input : Blake2sCompressionInput) : Word :=
  if input.last_block then -1 else 0

/-! ## The G step on words -/

/-- The witness words of one G step, in column order. -/
structure GWords where
  add1_carries : Word
  d1 : Word
  b1 : Word
  add2_carries : Word
  d2 : Word
  b2 : Word

/-- The carries into bits 1 to 31 of `x + y`, given `sum = x + y mod 2^32`, shifted down by one. -/
def carries_word (x y sum : Word) : Word := (sum ^^^ x ^^^ y) >>> 1

/-- Apply one G step to the state, and return the witness words it contributes. -/
def g_words (state : ℕ → ℕ → Word) (slots : List ℕ) (mx my : Word) : GWords × (ℕ → ℕ → Word) :=
  let ia := slots.getD 0 0
  let ib := slots.getD 1 0
  let ic := slots.getD 2 0
  let id := slots.getD 3 0
  let a := state 0 ia
  let b := state 1 ib
  let c := state 2 ic
  let d := state 3 id
  let a_plus_b := a + b
  let a1 := a_plus_b + mx
  let d1 := (d ^^^ a1).rotateRight 16
  let c1 := c + d1
  let b1 := (b ^^^ c1).rotateRight 12
  let a1_plus_b1 := a1 + b1
  let a2 := a1_plus_b1 + my
  let d2 := (d1 ^^^ a2).rotateRight 8
  let c2 := c1 + d2
  let b2 := (b1 ^^^ c2).rotateRight 7
  let state := Function.update state 0 (Function.update (state 0) ia a2)
  let state := Function.update state 1 (Function.update (state 1) ib b2)
  let state := Function.update state 2 (Function.update (state 2) ic c2)
  let state := Function.update state 3 (Function.update (state 3) id d2)
  (⟨carries_word a b a_plus_b, d1, b1, carries_word a1 b1 a1_plus_b1, d2, b2⟩, state)

/-! ## The row -/

variable {F : Type} [Field F]

/-- A row of the column struct, field by field. -/
structure Blake2sBinaryCols (T : Type) where
  chaining_value : ℕ → ℕ → T
  block : ℕ → ℕ → T
  counter_low : ℕ → T
  counter_high : ℕ → T
  last_block : T
  rounds : ℕ → ℕ → Blake2sBinaryGCols T

namespace Blake2sBinaryCols

variable {T : Type}

/-- The zero row. -/
def zero [Zero T] : Blake2sBinaryCols T :=
  ⟨fun _ _ => 0, fun _ _ => 0, fun _ => 0, fun _ => 0, 0,
    fun _ _ => ⟨fun _ => 0, fun _ => 0, fun _ => 0, fun _ => 0, fun _ => 0, fun _ => 0⟩⟩

/-- The cells of a block of `n` fields of `w` cells each. -/
def cellBlock (f : ℕ → ℕ → T) (n w : ℕ) : List T := (List.range n).flatMap fun i => (List.range w).map (f i)

/-- The cells of one G step, in the struct's order. -/
def gCells (g : Blake2sBinaryGCols T) : List T :=
  (List.range 31).map g.add1_carries ++ (List.range 32).map g.d1 ++ (List.range 32).map g.b1 ++
    (List.range 31).map g.add2_carries ++ (List.range 32).map g.d2 ++ (List.range 32).map g.b2

/-- The cells of a row, in the struct's `repr(C)` order. -/
def cells (r : Blake2sBinaryCols T) : List T :=
  cellBlock r.chaining_value 8 32 ++ cellBlock r.block 16 32 ++ (List.range 32).map r.counter_low ++
    (List.range 32).map r.counter_high ++ [r.last_block] ++
    (List.range NUM_ROUNDS).flatMap (fun round =>
      (List.range G_PER_ROUND).flatMap fun g => gCells (r.rounds round g))

/-- The row a slice of cells holds, field by field, as the borrow reads it. -/
def ofCells [Zero T] (l : List T) : Blake2sBinaryCols T :=
  let c (i : ℕ) : T := l.getD i 0
  ⟨fun i b => c (col.chaining_value i b), fun i b => c (col.block i b), fun b => c (col.counter_low b),
    fun b => c (col.counter_high b), c col.last_block, fun r g =>
      ⟨fun k => c (col.add1_carries r g k), fun b => c (col.d1 r g b), fun b => c (col.b1 r g b),
        fun k => c (col.add2_carries r g k), fun b => c (col.d2 r g b), fun b => c (col.b2 r g b)⟩⟩

end Blake2sBinaryCols

/-! ## The generator -/

/-- The low bits of a word as field cells, lowest bit first. -/
def word_to_bits_le (word : Word) : ℕ → F := fun i =>
  if (word >>> i) &&& 1 = 1 then 1 else 0

/-- Apply one G step to the state, writing its witness as field cells. -/
def generate_g (state : ℕ → ℕ → Word) (slots : List ℕ) (mx my : Word) :
    Blake2sBinaryGCols F × (ℕ → ℕ → Word) :=
  let (words, state) := g_words state slots mx my
  (⟨word_to_bits_le words.add1_carries, u32_to_bits_le words.d1, u32_to_bits_le words.b1,
    word_to_bits_le words.add2_carries, u32_to_bits_le words.d2, u32_to_bits_le words.b2⟩, state)

/-- Fill a row with the witness of a single compression. -/
def generate_trace_row (row : Blake2sBinaryCols F) (input : Blake2sCompressionInput) :
    Blake2sBinaryCols F :=
  let counter_low : Word := input.counter.setWidth 32
  let counter_high : Word := (input.counter >>> 32).setWidth 32
  let last_block := input.flag_word
  -- The input cells.
  let row := { row with
    chaining_value := fun i => u32_to_bits_le (input.chaining_value.getD i 0)
    block := fun i => u32_to_bits_le (input.block.getD i 0)
    counter_low := u32_to_bits_le counter_low
    counter_high := u32_to_bits_le counter_high
    last_block := if input.last_block then 1 else 0 }
  -- The initial state.
  let parameters := [counter_low, counter_high, last_block]
  let state : ℕ → ℕ → Word := fun r i =>
    if r = 0 then input.chaining_value.getD i 0
    else if r = 1 then input.chaining_value.getD (4 + i) 0
    else if r = 2 then IV.getD i 0
    else if r = 3 then IV.getD (4 + i) 0 ^^^ parameters.getD i 0
    else 0
  let m := input.block
  -- Ten rounds of eight G steps, writing each step's witness.
  let acc := (List.range NUM_ROUNDS).foldl (fun acc r =>
    let schedule := SIGMA.getD r []
    (List.range G_PER_ROUND).foldl (fun (acc : Blake2sBinaryCols F × (ℕ → ℕ → Word)) g =>
      let (cols, state) := generate_g acc.2 (G_SCHEDULE.getD g []) (m.getD (schedule.getD (2 * g) 0) 0)
        (m.getD (schedule.getD (2 * g + 1) 0) 0)
      ({ acc.1 with rounds := Function.update acc.1.rounds r (Function.update (acc.1.rounds r) g cols) },
        state)) acc) (row, state)
  acc.1

/-- The trace of the given inputs, one compression per row.

It panics when 2 is not 0 in the field, or when the number of inputs is not a positive power of two. -/
def generate_binary_trace_rows [DecidableEq F] (inputs : List Blake2sCompressionInput)
    (_extra_capacity_bits : ℕ) : Option (Mat F) := do
  if (2 : F) ≠ 0 then none
  if inputs.length = 0 then none
  if 2 ^ Nat.log 2 inputs.length ≠ inputs.length then none
  pure ⟨NUM_BLAKE2S_BINARY_COLS,
    (inputs.map (generate_trace_row Blake2sBinaryCols.zero)).flatMap Blake2sBinaryCols.cells⟩

/-! ## Reading a row back -/

/-- The word stored as 32 cells, least significant bit first, or none when a cell is not a bit. -/
def read_word [DecidableEq F] (bits : ℕ → F) : Option Word :=
  (List.range 32).foldlM (fun (word : Word) i =>
    if bits i = 0 ∨ bits i = 1 then
      some (word ||| (BitVec.ofBool (bits i = 1)).setWidth 32 <<< i)
    else none) 0

/-- The state `v[0..16]` after the given round, read from the witness of its diagonal steps.

It panics when the round is not below ten, or when a cell read is not a bit. -/
def state_after_round [DecidableEq F] (r : Blake2sBinaryCols F) (round : ℕ) : Option (List Word) := do
  if NUM_ROUNDS ≤ round then none
  (List.range G_PER_ROUND).foldlM (fun (v : List Word) g => do
    let cols := r.rounds round g
    let slots := G_SCHEDULE.getD g []
    let d1 ← read_word cols.d1
    let b1 ← read_word cols.b1
    let d2 ← read_word cols.d2
    let b2 ← read_word cols.b2
    let v := v.set (slots.getD 0 0) (d1 ^^^ d2.rotateLeft 8)
    let v := v.set (4 + slots.getD 1 0) b2
    let v := v.set (8 + slots.getD 2 0) (b1 ^^^ b2.rotateLeft 7)
    pure (v.set (12 + slots.getD 3 0) d2)) (List.replicate 16 0)

/-- The compression output `h'[i] = h[i] ^ v[i] ^ v[i + 8]` of a row, read from its witness.

It panics when a cell read is not a bit. -/
def compression_output [DecidableEq F] (r : Blake2sBinaryCols F) : Option (List Word) := do
  let v ← state_after_round r (NUM_ROUNDS - 1)
  let cv ← (List.range 8).mapM fun i => read_word (r.chaining_value i)
  pure ((List.range 8).map fun i => cv.getD i 0 ^^^ v.getD i 0 ^^^ v.getD (i + 8) 0)

end p3_blake2s_air.mirror
