/-
Transcriptions of the BLAKE3 AIR over a field of characteristic 2: its column layout, its evaluation, its G step on words, its trace generator and its output reader.

The evaluation and the generator do not extract: they are generic over the builder and the field traits, which aeneas rejects.

The G step on words and the schedule are also extracted; the transcriptions are proved equal to them.

Each definition transcribes one Rust item, named in the crate's mirror entries.

What a transcription abstracts, beyond those of the other AIR:

* a state of four rows of four words is a map from the row and the word to the word's bits, or to the word;
* the schedule permuted in place between rounds is, at round r, the identity permuted r times;
* a panic is none.

The bit-sliced generator, which packs 64 rows into each `u64`, is not transcribed.

Loops, branches and the order of assertions are kept.
-/
module

public import P3Blake3Air.Assumptions.Mirror.Generation

@[expose] public section

namespace p3_blake3_air.mirror.binary

open p3_air.builder.mirror p3_air.air.mirror p3_blake3_air.mirror

/-! ## The column layout -/

/-- The rounds of one compression. -/
def NUM_ROUNDS : ℕ := 7

/-- The G steps of one round. -/
def G_PER_ROUND : ℕ := 8

/-- The word of rows a, b, c and d that each G step of a round mixes: four columns, then four diagonals. -/
def G_SCHEDULE : List (List ℕ) :=
  [[0, 0, 0, 0], [1, 1, 1, 1], [2, 2, 2, 2], [3, 3, 3, 3],
   [0, 1, 2, 3], [1, 2, 3, 0], [2, 3, 0, 1], [3, 0, 1, 2]]

/-- Entry `j` of step `g` of the schedule. -/
def slot (g j : ℕ) : ℕ := (G_SCHEDULE.getD g []).getD j 0

-- The column indices of the struct's fields, in declaration order.
namespace col

def chaining_value (i k : ℕ) : ℕ := 32 * i + k
def block (i k : ℕ) : ℕ := 256 + 32 * i + k
def counter_low (k : ℕ) : ℕ := 768 + k
def counter_high (k : ℕ) : ℕ := 800 + k
def block_len (k : ℕ) : ℕ := 832 + k
def flags (k : ℕ) : ℕ := 864 + k

/-- The first column of G step `g` of round `r`. -/
def g (r g : ℕ) : ℕ := 896 + 1520 * r + 190 * g

def add1_carries (r g k : ℕ) : ℕ := col.g r g + k
def d1 (r g k : ℕ) : ℕ := col.g r g + 31 + k
def b1 (r g k : ℕ) : ℕ := col.g r g + 63 + k
def add2_carries (r g k : ℕ) : ℕ := col.g r g + 95 + k
def d2 (r g k : ℕ) : ℕ := col.g r g + 126 + k
def b2 (r g k : ℕ) : ℕ := col.g r g + 158 + k

end col

/-- The number of columns. -/
def NUM_BLAKE3_BINARY_COLS : ℕ := 11536

/-- The words of one compression's input: chaining value, block, two counter halves, block length and flags. -/
def NUM_INPUT_WORDS : ℕ := 8 + 16 + 4

/-- The input bits. -/
def NUM_INPUT_BITS : ℕ := NUM_INPUT_WORDS * 32

/-- Constraints per G step: two 3-operand and two 2-operand additions. -/
def CONSTRAINTS_PER_G : ℕ := 2 * (31 + 32) + 2 * 32

/-- The constraints of every G step. -/
def NUM_G_CONSTRAINTS : ℕ := NUM_ROUNDS * G_PER_ROUND * CONSTRAINTS_PER_G

/-- The number of constraints the AIR reports: the input booleanity if stated, and every G step. -/
def num_constraints (constrain_booleanity : Bool) : Option ℕ :=
  let booleanity := if constrain_booleanity then NUM_INPUT_BITS else 0
  some (booleanity + NUM_G_CONSTRAINTS)

/-- IV word `index`, as its low half or its high half shifted up by 16. -/
def iv_word (index : ℕ) : Word := BitVec.ofNat 32 (ivHalf index 0) ||| (BitVec.ofNat 32 (ivHalf index 1) <<< 16)

/-! ## The evaluation -/

variable {F E : Type} [Field F]

/-- The bits of x xor (y rotated left by shift). -/
def xor_rotl (O : ExprOps F E) (x y : ℕ → E) (shift : ℕ) : ℕ → E := fun i =>
  O.add (x i) (y ((i + 32 - shift) % 32))

/-- The majority of three bits, (x + z) (y + z) + z in characteristic 2. -/
def maj (O : ExprOps F E) (x y z : E) : E := O.add (O.mul (O.add x z) (O.add y z)) z

section steps

variable {S : Type} (B : AirBuilder F E S)

/-- Assert sum = x + y mod 2^32 on bits.

The carry into bit i is sum_i + x_i + y_i.

It is 0 at bit 0, and the majority of the previous bit's operands and carry above. -/
def add2 (s : S) (x y sum : ℕ → E) : S :=
  let carries : ℕ → E := fun i => B.add (B.add (sum i) (x i)) (y i)
  let s := B.assert_zero s (carries 0)
  (List.range 31).foldl (fun s i =>
    B.assert_zero s (B.add (maj B.toExprOps (x i) (y i) (carries i)) (carries (i + 1)))) s

/-- Assert sum = x + y + z mod 2^32 on bits.

The carries of x + y are columns, and the sum t = x + y they fix is added to z. -/
def add3 (s : S) (x y z : ℕ → E) (carries : ℕ → E) (sum : ℕ → E) : S :=
  let s := B.assert_zero s (B.add (B.mul (x 0) (y 0)) (carries 0))
  let s := (List.range 30).foldl (fun s i =>
    B.assert_zero s (B.add (maj B.toExprOps (x (i + 1)) (y (i + 1)) (carries i)) (carries (i + 1)))) s
  let t : ℕ → E := fun i =>
    if i = 0 then B.add (x 0) (y 0) else B.add (B.add (x i) (y i)) (carries (i - 1))
  add2 B s t z sum

end steps

/-- The state: each row is a map from the word to its bits. -/
structure State (E : Type) where
  a : ℕ → ℕ → E
  b : ℕ → ℕ → E
  c : ℕ → ℕ → E
  d : ℕ → ℕ → E

/-- Constrain one G step and advance the state to its output. -/
def eval_g {S : Type} (B : AirBuilder F E S) (s : S) (state : State E) (ia ib ic id : ℕ)
    (mx my : ℕ → E) (add1_carries d1 b1 add2_carries d2 b2 : ℕ → E) : S × State E :=
  let b := state.b ib
  let d := state.d id
  -- a1 = a + b + mx, where a1 = d xor (d1 <<< 16).
  let a1 := xor_rotl B.toExprOps d d1 16
  let s := add3 B s (state.a ia) b mx add1_carries a1
  -- c1 = c + d1, where c1 = b xor (b1 <<< 12).
  let c1 := xor_rotl B.toExprOps b b1 12
  let s := add2 B s (state.c ic) d1 c1
  -- a2 = a1 + b1 + my, where a2 = d1 xor (d2 <<< 8).
  let a2 := xor_rotl B.toExprOps d1 d2 8
  let s := add3 B s a1 b1 my add2_carries a2
  -- c2 = c1 + d2, where c2 = b1 xor (b2 <<< 7).
  let c2 := xor_rotl B.toExprOps b1 b2 7
  let s := add2 B s c1 d2 c2
  (s, ⟨Function.update state.a ia a2, Function.update state.b ib b2,
    Function.update state.c ic c2, Function.update state.d id d2⟩)

section body

variable {S : Type} (B : AirBuilder F E S) (loc : ℕ → E)

/-- Row d of the initial state: the counter halves, the block length and the flags. -/
def initial_d : ℕ → ℕ → E := fun j k => loc (col.counter_low (32 * j + k))

/-- The input bits are bits. -/
def assert_inputs (s : S) : S :=
  let words : List (ℕ → E) :=
    (List.range 8).map (fun i k => loc (col.chaining_value i k)) ++
      (List.range 16).map (fun i k => loc (col.block i k)) ++ (List.range 4).map (initial_d loc)
  words.foldl (fun s word => B.assert_bools s ((List.range 32).map word)) s

/-- The initial state: the chaining value, the IV as constant bits, and the counter, length and flags. -/
def initial_state : State E :=
  ⟨fun i k => loc (col.chaining_value i k), fun i k => loc (col.chaining_value (4 + i) k),
    fun i k => B.const (u32_to_bits_le (iv_word i) k), initial_d loc⟩

/-- G step g of round r, from a state, with the message permuted r times. -/
def g_step (r g : ℕ) (acc : S × State E) : S × State E :=
  let m : ℕ → ℕ := permute^[r] id
  let cell : ℕ → ℕ → E := fun base k => loc (base + k)
  eval_g B acc.1 acc.2 (slot g 0) (slot g 1) (slot g 2) (slot g 3)
    (fun k => loc (col.block (m (2 * g)) k)) (fun k => loc (col.block (m (2 * g + 1)) k))
    (cell (col.add1_carries r g 0)) (cell (col.d1 r g 0)) (cell (col.b1 r g 0))
    (cell (col.add2_carries r g 0)) (cell (col.d2 r g 0)) (cell (col.b2 r g 0))

/-- The seven rounds of eight G steps. -/
def rounds (acc : S × State E) : S × State E :=
  (List.range NUM_ROUNDS).foldl (fun acc r =>
    (List.range G_PER_ROUND).foldl (fun acc g => g_step B loc r g acc) acc) acc

end body

/-- The evaluation of the characteristic-2 BLAKE3 AIR, with or without the input booleanity. -/
def eval (constrain_booleanity : Bool) {S : Type} (B : AirBuilder F E S) (s : S) : S :=
  let main := B.main s
  let loc : ℕ → E := fun i => main.current.getD i (B.const 0)
  let s := if constrain_booleanity then assert_inputs B loc s else s
  (rounds B loc (s, initial_state B loc)).1

/-! ## The G step on words -/

/-- A state of four rows of four words: `state r i` is word i of row r. -/
abbrev WState := ℕ → ℕ → Word

/-- The witness words of one G step. -/
structure GWords where
  add1_carries : Word
  d1 : Word
  b1 : Word
  add2_carries : Word
  d2 : Word
  b2 : Word

/-- The carries into bits 1 to 31 of x + y, given their sum, shifted down to start at bit 0. -/
def carries_word (x y sum : Word) : Word := (sum ^^^ x ^^^ y) >>> 1

/-- Apply one G step to the state, and return the witness words it contributes. -/
def g_words (state : WState) (ia ib ic id : ℕ) (mx my : Word) : GWords × WState :=
  let (a, b, c, d) := (state 0 ia, state 1 ib, state 2 ic, state 3 id)
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
  let state := setWords state ia ib ic id (a2, b2, c2, d2)
  (⟨carries_word a b a_plus_b, d1, b1, carries_word a1 b1 a1_plus_b1, d2, b2⟩, state)

/-! ## The trace generator -/

/-- The inputs of one compression. -/
structure Blake3CompressionInput where
  chaining_value : ℕ → Word
  block : ℕ → Word
  counter : BitVec 64
  block_len : Word
  flags : Word

/-- The witness columns of one G step. -/
structure Blake3BinaryGCols (T : Type) where
  add1_carries : ℕ → T
  d1 : ℕ → T
  b1 : ℕ → T
  add2_carries : ℕ → T
  d2 : ℕ → T
  b2 : ℕ → T

/-- A row of the column struct. -/
structure Blake3BinaryCols (T : Type) where
  chaining_value : ℕ → ℕ → T
  block : ℕ → ℕ → T
  counter_low : ℕ → T
  counter_high : ℕ → T
  block_len : ℕ → T
  flags : ℕ → T
  rounds : ℕ → ℕ → Blake3BinaryGCols T

/-- The cells of one G step's columns. -/
def Blake3BinaryGCols.cells {T : Type} (g : Blake3BinaryGCols T) : List T :=
  (List.range 31).map g.add1_carries ++ (List.range 32).map g.d1 ++ (List.range 32).map g.b1 ++
    (List.range 31).map g.add2_carries ++ (List.range 32).map g.d2 ++ (List.range 32).map g.b2

/-- The cells of a row, in the struct's `repr(C)` order. -/
def Blake3BinaryCols.cells {T : Type} (r : Blake3BinaryCols T) : List T :=
  Blake3Cols.words 8 32 r.chaining_value ++ Blake3Cols.words 16 32 r.block ++
    (List.range 32).map r.counter_low ++ (List.range 32).map r.counter_high ++
    (List.range 32).map r.block_len ++ (List.range 32).map r.flags ++
    (List.range 7).flatMap fun round => (List.range 8).flatMap fun g => (r.rounds round g).cells

/-- The low `N` bits of a word, least significant first. -/
def word_to_bits_le (word : Word) : ℕ → F := fun i => if word.getLsbD i then 1 else 0

/-- The witness columns of one G step, from its witness words. -/
def generate_g (words : GWords) : Blake3BinaryGCols F :=
  ⟨word_to_bits_le words.add1_carries, u32_to_bits_le words.d1, u32_to_bits_le words.b1,
    word_to_bits_le words.add2_carries, u32_to_bits_le words.d2, u32_to_bits_le words.b2⟩

/-- Fill the row of one compression. -/
def generate_trace_row (input : Blake3CompressionInput) : Blake3BinaryCols F :=
  let counter_low : Word := input.counter.setWidth 32
  let counter_high : Word := (input.counter >>> 32).setWidth 32
  let cv := input.chaining_value
  let state : WState := fun r i =>
    if r = 0 then cv i
    else if r = 1 then cv (4 + i)
    else if r = 2 then iv_word i
    else if i = 0 then counter_low
    else if i = 1 then counter_high
    else if i = 2 then input.block_len
    else input.flags
  let (rounds, _, _) := (List.range NUM_ROUNDS).foldl
    (fun (acc : (ℕ → ℕ → Blake3BinaryGCols F) × WState × (ℕ → Word)) round_idx =>
      let (rounds, state, m) := acc
      let m := if round_idx > 0 then permute m else m
      let (row, state) := (List.range G_PER_ROUND).foldl
        (fun (acc : (ℕ → Blake3BinaryGCols F) × WState) g =>
          let (row, state) := acc
          let (words, state) :=
            g_words state (slot g 0) (slot g 1) (slot g 2) (slot g 3) (m (2 * g)) (m (2 * g + 1))
          (Function.update row g (generate_g words), state)) (rounds round_idx, state)
      (Function.update rounds round_idx row, state, m))
    (fun _ _ => ⟨fun _ => 0, fun _ => 0, fun _ => 0, fun _ => 0, fun _ => 0, fun _ => 0⟩,
      state, input.block)
  { chaining_value := fun i => u32_to_bits_le (cv i)
    block := fun i => u32_to_bits_le (input.block i)
    counter_low := u32_to_bits_le counter_low
    counter_high := u32_to_bits_le counter_high
    block_len := u32_to_bits_le input.block_len
    flags := u32_to_bits_le input.flags
    rounds := rounds }

/-- The trace of the given compressions, one per row.

It panics when 2 is not 0 in the field, or when the number of inputs is not a positive power of two. -/
def generate_binary_trace_rows [DecidableEq F] (inputs : List Blake3CompressionInput)
    (_extra_capacity_bits : ℕ) : Option (Mat F) :=
  if (2 : F) ≠ 0 then none
  else if inputs.length = 0 then none
  else if inputs.length &&& (inputs.length - 1) ≠ 0 then none
  else some ⟨NUM_BLAKE3_BINARY_COLS, (inputs.map generate_trace_row).flatMap Blake3BinaryCols.cells⟩

/-! ## Reading the output -/

/-- Read a word from 32 cells, least significant first, with a panic when a cell is not a bit. -/
def read_word [DecidableEq F] (bits : ℕ → F) : Option Word :=
  (List.range 32).foldlM (fun word i =>
    if bits i = 0 ∨ bits i = 1 then some (word ||| (BitVec.ofBool (bits i = 1)).setWidth 32 <<< i)
    else none) 0

/-- The compression output a row holds: the final state from the last round's G steps, then the feed-forward. -/
def compression_output [DecidableEq F] (r : Blake3BinaryCols F) : Option (ℕ → Word) := do
  let v ← (List.range G_PER_ROUND).foldlM (fun (v : ℕ → Word) g => do
    let cols := r.rounds (NUM_ROUNDS - 1) g
    let d1 ← read_word cols.d1
    let b1 ← read_word cols.b1
    let d2 ← read_word cols.d2
    let b2 ← read_word cols.b2
    let v := Function.update v (slot g 0) (d1 ^^^ d2.rotateLeft 8)
    let v := Function.update v (4 + slot g 1) b2
    let v := Function.update v (8 + slot g 2) (b1 ^^^ b2.rotateLeft 7)
    pure (Function.update v (12 + slot g 3) d2)) (fun _ => 0)
  let cv ← (List.range 8).foldlM (fun (cv : ℕ → Word) i => do
    let w ← read_word (r.chaining_value i)
    pure (Function.update cv i w)) (fun _ => 0)
  pure fun i => if i < 8 then v i ^^^ v (i + 8) else v i ^^^ cv (i - 8)

end p3_blake3_air.mirror.binary
