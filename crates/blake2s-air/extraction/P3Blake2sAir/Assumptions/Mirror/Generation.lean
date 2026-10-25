/-
Transcriptions of the BLAKE2s trace generator: the compression input, the G step on words, the row, its cells, the generator, the read-back of the state and the output, and the packed generator.

The generator does not extract: it is generic over the field traits, which aeneas rejects.

The G step on words and the carry word are also extracted, and proved equal to these.

Each definition transcribes one Rust item, named in the crate's mirror entries.

What a transcription abstracts, beyond those of the evaluation:

* the working state, an array of four rows of four words, is a map from the row and the position to the word;
* the counter, a `u64`, is a 64-bit vector;
* the parallel loop over rows is a map, and the parallel loop over groups of 64 inputs is a flat map;
* 32 bit planes, an array of 64 rows and a group's input words are maps from the index to the entry;
* the packed row the column struct borrows from a slice of words is the struct of planes, laid out by its cells;
* the transpose's loop, which runs while the width is not zero, is seven iterations of a step that does nothing at width zero;
* the scratch carries the additions without a carry column write are dropped;
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

/-! ## The packed generator -/

/-- A word of 64 lanes as 32 bit planes: bit `k` of plane `i` is bit `i` of the word of lane `k`. -/
abbrev Planes := ℕ → BitVec 64

/-- The bit planes of `x + y mod 2^32`, by a ripple-carry adder, and the planes of the carries into bits 1 to 31. -/
def add_planes (x y : Planes) (carries : ℕ → BitVec 64) : Planes × (ℕ → BitVec 64) :=
  let (sum, carries, carry) := (List.range 31).foldl
    (fun (acc : Planes × (ℕ → BitVec 64) × BitVec 64) bit =>
      let (sum, carries, carry) := acc
      -- Full adder on bit `bit` of every lane.
      let half := x bit ^^^ y bit
      let sum := Function.update sum bit (half ^^^ carry)
      let carry := (x bit &&& y bit) ||| (carry &&& half)
      (sum, Function.update carries bit carry, carry)) (fun _ => 0, carries, 0)
  -- The carry out of bit 31 is dropped.
  (Function.update sum 31 (x 31 ^^^ y 31 ^^^ carry), carries)

/-- The bit planes of `(x ^ y) >>> amount`. -/
def xor_rotate_right (x y : Planes) (amount : ℕ) : Planes := fun bit =>
  x ((bit + amount) % 32) ^^^ y ((bit + amount) % 32)

/-- One iteration of the transpose's loop, while the width is not zero.

It swaps the two off-diagonal quarters of every aligned square of twice the width, then halves the width. -/
def transpose_step (acc : (ℕ → BitVec 64) × ℕ × BitVec 64) (_ : ℕ) : (ℕ → BitVec 64) × ℕ × BitVec 64 :=
  let (rows, width, mask) := acc
  if width ≠ 0 then
    let bases := (List.range ((64 + 2 * width - 1) / (2 * width))).map (· * (2 * width))
    let rows := bases.foldl (fun (rows : ℕ → BitVec 64) base =>
      (List.range' base width).foldl (fun (rows : ℕ → BitVec 64) row =>
        -- Swap the high half of the upper row with the low half of the lower row.
        let swap : BitVec 64 := ((rows row >>> width) ^^^ rows (row + width)) &&& mask
        let rows : ℕ → BitVec 64 := Function.update rows row (rows row ^^^ swap <<< width)
        Function.update rows (row + width) (rows (row + width) ^^^ swap)) rows) rows
    let width := width / 2
    (rows, width, mask ^^^ mask <<< width)
  else (rows, width, mask)

/-- Transpose a 64 x 64 bit matrix: bit `j` of row `i` moves to bit `i` of row `j`.

The loop runs while the width is not zero: six times, from width 32 down to width 1. -/
def transpose_bits (rows : ℕ → BitVec 64) : ℕ → BitVec 64 :=
  ((List.range 7).foldl transpose_step (rows, 32, 0x0000_0000_ffff_ffff#64)).1

/-- A bit plane with bit `k` set when input `k` satisfies the predicate. -/
def lane_mask (inputs : List Blake2sCompressionInput) (flag : Blake2sCompressionInput → Bool) : BitVec 64 :=
  inputs.zipIdx.foldl (fun mask (input, lane) => mask ||| (BitVec.ofBool (flag input)).setWidth 64 <<< lane) 0

/-- The 32-bit input words of one compression, in column order. -/
def input_words (input : Blake2sCompressionInput) : ℕ → Word := fun i =>
  if i < 8 then input.chaining_value.getD i 0
  else if i < 24 then input.block.getD (i - 8) 0
  else if i = 24 then input.counter.setWidth 32
  else if i = 25 then (input.counter >>> 32).setWidth 32
  else 0

/-- Apply one G step to the bit planes of the state, and return its witness planes. -/
def g_planes (state : ℕ → ℕ → Planes) (slots : List ℕ) (mx my : Planes) :
    Blake2sBinaryGCols (BitVec 64) × (ℕ → ℕ → Planes) :=
  let ia := slots.getD 0 0
  let ib := slots.getD 1 0
  let ic := slots.getD 2 0
  let id := slots.getD 3 0
  let a := state 0 ia
  let b := state 1 ib
  let c := state 2 ic
  let d := state 3 id
  -- Additions without a carry column write their carries to scratch space.
  let (a_plus_b, add1_carries) := add_planes a b (fun _ => 0)
  let a1 := (add_planes a_plus_b mx (fun _ => 0)).1
  let d1 := xor_rotate_right d a1 16
  let c1 := (add_planes c d1 (fun _ => 0)).1
  let b1 := xor_rotate_right b c1 12
  let (a1_plus_b1, add2_carries) := add_planes a1 b1 (fun _ => 0)
  let a2 := (add_planes a1_plus_b1 my (fun _ => 0)).1
  let d2 := xor_rotate_right d1 a2 8
  let c2 := (add_planes c1 d2 (fun _ => 0)).1
  let b2 := xor_rotate_right b1 c2 7
  let state := Function.update state 0 (Function.update (state 0) ia a2)
  let state := Function.update state 1 (Function.update (state 1) ib b2)
  let state := Function.update state 2 (Function.update (state 2) ic c2)
  let state := Function.update state 3 (Function.update (state 3) id d2)
  (⟨add1_carries, d1, b1, add2_carries, d2, b2⟩, state)

/-- The packed row of up to 64 compressions: lane `k` of every column holds input `k`, and absent lanes stay zero. -/
def generate_block (inputs : List Blake2sCompressionInput) : Blake2sBinaryCols (BitVec 64) :=
  -- The input words, two per lane, transposed into 64 planes per pair.
  let words : ℕ → ℕ → Word := fun lane => (inputs[lane]?.map input_words).getD fun _ => 0
  let pairs : ℕ → ℕ → BitVec 64 := fun pair => transpose_bits fun row =>
    (words row (2 * pair)).setWidth 64 ||| (words row (2 * pair + 1)).setWidth 64 <<< 32
  let input_plane : ℕ → BitVec 64 := fun c => pairs (c / 64) (c % 64)
  let cv : ℕ → Planes := fun i b => input_plane (32 * i + b)
  let m : ℕ → Planes := fun i b => input_plane (256 + 32 * i + b)
  let counter_low : Planes := fun b => input_plane (768 + b)
  let counter_high : Planes := fun b => input_plane (800 + b)
  -- The finalization flag.
  let last_block := lane_mask inputs (·.last_block)
  -- The constant words are set only in the lanes that hold an input.
  let lanes := BitVec.allOnes 64 >>> (64 - inputs.length)
  let iv_planes : Word → Planes := fun word bit => if (word >>> bit) &&& 1 = 1 then lanes else 0
  -- The flag plane is repeated over all 32 bits, which inverts v[14] in the lanes that set the flag.
  let parameters : List Planes := [counter_low, counter_high, fun _ => last_block]
  let state : ℕ → ℕ → Planes := fun r i =>
    if r = 0 then cv i
    else if r = 1 then cv (4 + i)
    else if r = 2 then iv_planes (IV.getD i 0)
    else if r = 3 then
      (if i < 3 then fun bit => iv_planes (IV.getD (4 + i) 0) bit ^^^ (parameters.getD i (fun _ => 0)) bit
      else iv_planes (IV.getD (4 + i) 0))
    else fun _ => 0
  -- Ten rounds of eight G steps, writing each step's witness planes.
  let (rounds, _) := (List.range NUM_ROUNDS).foldl
    (fun (acc : (ℕ → ℕ → Blake2sBinaryGCols (BitVec 64)) × (ℕ → ℕ → Planes)) r =>
      let schedule := SIGMA.getD r []
      (List.range G_PER_ROUND).foldl
        (fun (acc : (ℕ → ℕ → Blake2sBinaryGCols (BitVec 64)) × (ℕ → ℕ → Planes)) g =>
          let (cols, state) := g_planes acc.2 (G_SCHEDULE.getD g []) (m (schedule.getD (2 * g) 0))
            (m (schedule.getD (2 * g + 1) 0))
          (Function.update acc.1 r (Function.update (acc.1 r) g cols), state)) acc)
    ((Blake2sBinaryCols.zero : Blake2sBinaryCols (BitVec 64)).rounds, state)
  ⟨cv, m, counter_low, counter_high, last_block, rounds⟩

/-- The trace packed into one word per 64 rows: bit `k` of word `(w, j)` is set when cell `(64 w + k, j)` is 1.

It panics when 2 is not 0 in the field, or when the number of inputs is not a positive power of two. -/
def generate_binary_trace_packed [DecidableEq F] (inputs : List Blake2sCompressionInput) :
    Option (Mat (BitVec 64)) := do
  if (2 : F) ≠ 0 then none
  if inputs.length = 0 then none
  if 2 ^ Nat.log 2 inputs.length ≠ inputs.length then none
  let num_blocks := (inputs.length + 63) / 64
  pure ⟨NUM_BLAKE2S_BINARY_COLS, (List.range num_blocks).flatMap fun w =>
    (generate_block ((inputs.drop (64 * w)).take 64)).cells⟩

end p3_blake2s_air.mirror
