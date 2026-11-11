/-
Transcriptions of the SHA-256 AIR over a field of characteristic 2: its column layout, its evaluation, its sigma functions on words, its trace generator and its packed trace generator.

The evaluation and the generator do not extract: they are generic over the builder and the field traits, which aeneas rejects.

The sigma functions on words are also extracted; the transcriptions are proved equal to them.

Each definition transcribes one Rust item, named in the crate's mirror entries.

What a transcription abstracts, beyond those of the other AIR:

* a slice of words is a list of maps from the bit index to the bit, and an array of carry words is a list of maps from the carry index to the carry;
* the assertion that an addition gets one stored-carry word per middle word, which every call meets, is dropped;
* a block of packed words is a map from the column to the word, and a group of 64 inputs is a drop then a take;
* the parallel loop over groups is a sequential loop, and the scratch row is threaded through it;
* a panic is none.

Loops, branches and the order of assertions are kept.
-/
module

public import P3Sha256Air.Assumptions.Mirror.Generation

@[expose] public section

namespace p3_sha256_air.mirror.binary

open p3_air.builder.mirror p3_air.air.mirror p3_sha256_air.mirror

/-- The stored-carry additions of T1: five words take four additions, the last reading its carries off T1. -/
def T1_CARRIES : ℕ := 3

/-- The stored-carry additions of a schedule word: four words take three additions. -/
def SCHEDULE_CARRIES : ℕ := 2

/-- Bit i of x >>> n, on a word stored least significant bit first. -/
def rotr_index (i n : ℕ) : ℕ := (i + n) % 32

/-! ## The column layout -/

-- The column indices of the struct's fields, in declaration order.
namespace col

def a_chain (k b : ℕ) : ℕ := 32 * k + b
def e_chain (k b : ℕ) : ℕ := 2176 + 32 * k + b
def w (t b : ℕ) : ℕ := 4352 + 32 * t + b
def sched_carries (i j c : ℕ) : ℕ := 6400 + 62 * i + 31 * j + c
def ch (t b : ℕ) : ℕ := 9376 + 220 * t + b
def maj (t b : ℕ) : ℕ := 9376 + 220 * t + 32 + b
def t1_carries (t j c : ℕ) : ℕ := 9376 + 220 * t + 64 + 31 * j + c
def t1 (t b : ℕ) : ℕ := 9376 + 220 * t + 157 + b
def new_a_carries (t c : ℕ) : ℕ := 9376 + 220 * t + 189 + c
def h_out (i b : ℕ) : ℕ := 23456 + 32 * i + b

end col

/-- The number of columns. -/
def NUM_SHA256_BINARY_COLS : ℕ := 23712

/-- The input bits: the chaining value and the block. -/
def NUM_INPUT_BITS : ℕ := (STATE_WORDS + BLOCK_WORDS) * 32

/-- The constraints of an addition that stores its carries. -/
def STORED_CARRY_ADD : ℕ := 31

/-- The constraints of an addition that reads its carries off the sum. -/
def SUM_CARRY_ADD : ℕ := 32

/-- The constraints of a schedule word. -/
def CONSTRAINTS_PER_SCHEDULE_WORD : ℕ := SCHEDULE_CARRIES * STORED_CARRY_ADD + SUM_CARRY_ADD

/-- The constraints of a round: Ch, Maj, T1, new e and new a. -/
def CONSTRAINTS_PER_ROUND : ℕ :=
  32 + 32 + (T1_CARRIES * STORED_CARRY_ADD + SUM_CARRY_ADD) + SUM_CARRY_ADD +
    (STORED_CARRY_ADD + SUM_CARRY_ADD)

/-- The constraints past the input booleanity: the schedule, the rounds and the output. -/
def NUM_HASH_CONSTRAINTS : ℕ := SCHEDULE_EXTENSIONS * CONSTRAINTS_PER_SCHEDULE_WORD +
  NUM_COMPRESSION_ROUNDS * CONSTRAINTS_PER_ROUND + STATE_WORDS * SUM_CARRY_ADD

/-- The number of constraints the AIR reports: the input booleanity if stated, and the hash. -/
def num_constraints (constrain_booleanity : Bool) : Option ℕ :=
  let booleanity := if constrain_booleanity then NUM_INPUT_BITS else 0
  some (booleanity + NUM_HASH_CONSTRAINTS)

/-! ## The evaluation -/

variable {F E : Type} [Field F]

/-- The bits of (x >>> r0) ^ (x >>> r1) ^ (x >>> r2). -/
def xor3_rot (O : ExprOps F E) (x : ℕ → E) (r0 r1 r2 : ℕ) : ℕ → E := fun i =>
  O.add (O.add (x (rotr_index i r0)) (x (rotr_index i r1))) (x (rotr_index i r2))

/-- The bits of (x >>> r0) ^ (x >>> r1) ^ (x >> s). -/
def xor3_shift (O : ExprOps F E) (x : ℕ → E) (r0 r1 s : ℕ) : ℕ → E := fun i =>
  let rotated := O.add (x (rotr_index i r0)) (x (rotr_index i r1))
  if i + s < 32 then O.add rotated (x (i + s)) else rotated

/-- The majority of three bits, (x + z) (y + z) + z in characteristic 2. -/
def maj (O : ExprOps F E) (x y z : E) : E := O.add (O.mul (O.add x z) (O.add y z)) z

section add

variable {S : Type} (B : AirBuilder F E S)

/-- One stored-carry addition of the loop below: the state and the partial sum, then a word and its carries.

The carry into bit 0 is the product of the low bits.

The carry into bit i is the majority of bit i - 1's operands and carry. -/
def add_many_step (acc : S × (ℕ → E)) (wc : (ℕ → E) × (ℕ → E)) : S × (ℕ → E) :=
  let partial_sum := acc.2
  let word := wc.1
  let carries := wc.2
  let s := B.assert_zero acc.1 (B.add (B.mul (partial_sum 0) (word 0)) (carries 0))
  let s := (List.range' 1 30).foldl (fun s i =>
    B.assert_zero s (B.add (maj B.toExprOps (partial_sum i) (word i) (carries (i - 1)))
      (carries i))) s
  let partial_sum : ℕ → E := fun i =>
    if i = 0 then B.add (partial_sum 0) (word 0)
    else B.add (B.add (partial_sum i) (word i)) (carries (i - 1))
  (s, partial_sum)

/-- Constrain sum = words[0] + words[1] + ... mod 2^32.

Addition j adds words[j + 1] to the partial sum, with carries[j] its carries into bits 1 to 31.

The last addition reads its carries off the sum. -/
def add_many (s : S) (words : List (ℕ → E)) (carries : List (ℕ → E)) (sum : ℕ → E) : S :=
  let N := carries.length
  let acc := ((words.drop 1).take N).zip carries |>.foldl (add_many_step B)
    (s, words.getD 0 (fun _ => B.const 0))
  let s := acc.1
  let partial_sum := acc.2
  let last := words.getD (N + 1) (fun _ => B.const 0)
  let carry : ℕ → E := fun i => B.add (B.add (sum i) (partial_sum i)) (last i)
  let s := B.assert_zero s (carry 0)
  (List.range 31).foldl (fun s i =>
    B.assert_zero s (B.add (maj B.toExprOps (partial_sum i) (last i) (carry i)) (carry (i + 1)))) s

end add

/-- The evaluation of the characteristic-2 SHA-256 AIR, with or without the input booleanity. -/
def eval (constrain_booleanity : Bool) {S : Type} (B : AirBuilder F E S) (s : S) : S :=
  let main := B.main s
  let loc : ℕ → E := fun i => main.current.getD i (B.const 0)
  let a_chain : ℕ → ℕ → E := fun k b => loc (col.a_chain k b)
  let e_chain : ℕ → ℕ → E := fun k b => loc (col.e_chain k b)
  let w : ℕ → ℕ → E := fun t b => loc (col.w t b)
  let s := if constrain_booleanity then
      let words := ((List.range 4).map a_chain) ++ ((List.range 4).map e_chain) ++
        ((List.range BLOCK_WORDS).map w)
      words.foldl (fun s word => B.assert_bools s ((List.range 32).map word)) s
    else s
  -- W[t] = σ1(W[t-2]) + W[t-7] + σ0(W[t-15]) + W[t-16].
  let s := (List.range SCHEDULE_EXTENSIONS).foldl (fun s i =>
    let t := BLOCK_WORDS + i
    add_many B s
      [xor3_shift B.toExprOps (w (t - 2)) 17 19 10, w (t - 7),
        xor3_shift B.toExprOps (w (t - 15)) 7 18 3, w (t - 16)]
      ((List.range SCHEDULE_CARRIES).map fun j c => loc (col.sched_carries i j c)) (w t)) s
  let s := (List.range NUM_COMPRESSION_ROUNDS).foldl (fun s t =>
    let a := a_chain (t + 3)
    let b := a_chain (t + 2)
    let c := a_chain (t + 1)
    let d := a_chain t
    let e := e_chain (t + 3)
    let f := e_chain (t + 2)
    let g := e_chain (t + 1)
    let h := e_chain t
    let ch : ℕ → E := fun i => loc (col.ch t i)
    let maj_word : ℕ → E := fun i => loc (col.maj t i)
    let t1 : ℕ → E := fun i => loc (col.t1 t i)
    -- Ch(e, f, g) = e (f + g) + g.
    let s := (List.range 32).foldl (fun s i =>
      B.assert_zero s (B.add (B.add (B.mul (e i) (B.add (f i) (g i))) (g i)) (ch i))) s
    -- Maj(a, b, c) is the bitwise majority.
    let s := (List.range 32).foldl (fun s i =>
      B.assert_zero s (B.add (maj B.toExprOps (a i) (b i) (c i)) (maj_word i))) s
    -- T1 = h + Σ1(e) + Ch + K[t] + W[t].
    let s := add_many B s
      [h, xor3_rot B.toExprOps e 6 11 25, ch,
        fun i => B.const (u32_to_bits_le (F := F) (BitVec.ofNat 32 (kOf t)) i), w t]
      ((List.range T1_CARRIES).map fun j c => loc (col.t1_carries t j c)) t1
    -- new e = d + T1.
    let s := add_many B s [d, t1] [] (e_chain (t + 4))
    -- new a = T1 + Σ0(a) + Maj.
    add_many B s [t1, xor3_rot B.toExprOps a 2 13 22, maj_word]
      [fun c => loc (col.new_a_carries t c)] (a_chain (t + 4))) s
  -- H'[i] = H[i] + final working variable i.
  (List.range STATE_WORDS).foldl (fun s i =>
    let chain := if i < 4 then a_chain else e_chain
    let h_in := chain (3 - i % 4)
    let last := chain (NUM_COMPRESSION_ROUNDS + 3 - i % 4)
    add_many B s [h_in, last] [] (fun b => loc (col.h_out i b))) s

/-! ## The sigma functions on words -/

/-- Σ0(x) = (x >>> 2) ^ (x >>> 13) ^ (x >>> 22). -/
def big_sigma0 (x : Word) : Word := x.rotateRight 2 ^^^ x.rotateRight 13 ^^^ x.rotateRight 22

/-- Σ1(x) = (x >>> 6) ^ (x >>> 11) ^ (x >>> 25). -/
def big_sigma1 (x : Word) : Word := x.rotateRight 6 ^^^ x.rotateRight 11 ^^^ x.rotateRight 25

/-- σ0(x) = (x >>> 7) ^ (x >>> 18) ^ (x >> 3). -/
def small_sigma0 (x : Word) : Word := x.rotateRight 7 ^^^ x.rotateRight 18 ^^^ x >>> 3

/-- σ1(x) = (x >>> 17) ^ (x >>> 19) ^ (x >> 10). -/
def small_sigma1 (x : Word) : Word := x.rotateRight 17 ^^^ x.rotateRight 19 ^^^ x >>> 10

/-! ## The trace generator -/

/-- The schedule witness of one word. -/
structure Sha256BinaryScheduleCols (T : Type) where
  carries : ℕ → ℕ → T

/-- The witness of one round. -/
structure Sha256BinaryRoundCols (T : Type) where
  ch : ℕ → T
  maj : ℕ → T
  t1_carries : ℕ → ℕ → T
  t1 : ℕ → T
  new_a_carries : ℕ → T

/-- A row of the column struct, field by field. -/
structure Sha256BinaryCols (T : Type) where
  a_chain : ℕ → ℕ → T
  e_chain : ℕ → ℕ → T
  w : ℕ → ℕ → T
  schedule : ℕ → Sha256BinaryScheduleCols T
  rounds : ℕ → Sha256BinaryRoundCols T
  h_out : ℕ → ℕ → T

namespace Sha256BinaryCols

variable {T : Type}

/-- The zero row. -/
def zero [Zero T] : Sha256BinaryCols T :=
  ⟨fun _ _ => 0, fun _ _ => 0, fun _ _ => 0, fun _ => ⟨fun _ _ => 0⟩,
    fun _ => ⟨fun _ => 0, fun _ => 0, fun _ _ => 0, fun _ => 0, fun _ => 0⟩, fun _ _ => 0⟩

/-- The cells of one round, in the struct's order. -/
def roundCells (r : Sha256BinaryRoundCols T) : List T :=
  (List.range 32).map r.ch ++ (List.range 32).map r.maj ++ Sha256Cols.block r.t1_carries T1_CARRIES 31 ++
    (List.range 32).map r.t1 ++ (List.range 31).map r.new_a_carries

/-- The cells of a row, in the struct's `repr(C)` order. -/
def cells (r : Sha256BinaryCols T) : List T :=
  Sha256Cols.block r.a_chain CHAIN_LEN 32 ++ Sha256Cols.block r.e_chain CHAIN_LEN 32 ++
    Sha256Cols.block r.w NUM_COMPRESSION_ROUNDS 32 ++
    (List.range SCHEDULE_EXTENSIONS).flatMap (fun i =>
      Sha256Cols.block (r.schedule i).carries SCHEDULE_CARRIES 31) ++
    (List.range NUM_COMPRESSION_ROUNDS).flatMap (fun t => roundCells (r.rounds t)) ++
    Sha256Cols.block r.h_out STATE_WORDS 32

end Sha256BinaryCols

/-- The carries into bits 1 to 31 of x + y, given sum = x + y mod 2^32: the bits of sum ^ x ^ y above bit 0. -/
def carry_bits (x y sum : Word) : ℕ → F := fun i =>
  if ((sum ^^^ x ^^^ y) >>> (i + 1)) &&& 1 = 1 then 1 else 0

/-- Add the words in order: the sum, and the carries of every addition but the last.

It panics unless there are two more words than stored carries. -/
def add_with_carries (N : ℕ) (words : List Word) : Option (Word × List (ℕ → F)) :=
  if words.length ≠ N + 2 then none
  else
    let (partial_sum, carries) := (List.range N).foldl (fun (acc : Word × List (ℕ → F)) j =>
      let (partial_sum, carries) := acc
      let sum := partial_sum + words.getD (j + 1) 0
      let c := carry_bits (F := F) partial_sum (words.getD (j + 1) 0) sum
      (sum, carries ++ [c])) (words.getD 0 0, [])
    some (partial_sum + words.getD (N + 1) 0, carries)

/-- Fill a row with the witness of one compression, or none when an addition panics. -/
def generate_trace_row (row : Sha256BinaryCols F) (input : List Word) : Option (Sha256BinaryCols F) := do
  let block : ℕ → Word := fun i => input.getD i 0
  let h_in : ℕ → Word := fun i => input.getD (BLOCK_WORDS + i) 0
  -- The message schedule.
  let w : ℕ → Word := fun t => if t < BLOCK_WORDS then block t else 0
  let (row, w) ← (List.range SCHEDULE_EXTENSIONS).foldlM
    (fun (acc : Sha256BinaryCols F × (ℕ → Word)) i => do
      let (row, w) := acc
      let t := BLOCK_WORDS + i
      let (w_t, carries) ← add_with_carries (F := F) SCHEDULE_CARRIES
        [small_sigma1 (w (t - 2)), w (t - 7), small_sigma0 (w (t - 15)), w (t - 16)]
      pure ({ row with
          schedule := Function.update row.schedule i ⟨fun j => carries.getD j (fun _ => 0)⟩ },
        Function.update w t w_t)) (row, w)
  let row := { row with w := fun t => u32_to_bits_le (w t) }
  -- The working-state chains, from the chaining value in round-shift order.
  let a_chain : ℕ → Word := fun k =>
    if k = 0 then h_in 3 else if k = 1 then h_in 2 else if k = 2 then h_in 1
    else if k = 3 then h_in 0 else 0
  let e_chain : ℕ → Word := fun k =>
    if k = 0 then h_in 7 else if k = 1 then h_in 6 else if k = 2 then h_in 5
    else if k = 3 then h_in 4 else 0
  let (row, a_chain, e_chain) ← (List.range NUM_COMPRESSION_ROUNDS).foldlM
    (fun (acc : Sha256BinaryCols F × (ℕ → Word) × (ℕ → Word)) t => do
      let (row, a_chain, e_chain) := acc
      let (a, b, c, d) := (a_chain (t + 3), a_chain (t + 2), a_chain (t + 1), a_chain t)
      let (e, f, g, h) := (e_chain (t + 3), e_chain (t + 2), e_chain (t + 1), e_chain t)
      let ch := (e &&& f) ^^^ (~~~e &&& g)
      let mj := (a &&& b) ^^^ (a &&& c) ^^^ (b &&& c)
      let (t1, t1_carries) ← add_with_carries (F := F) T1_CARRIES
        [h, big_sigma1 e, ch, BitVec.ofNat 32 (kOf t), w t]
      let (new_a, new_a_carries) ← add_with_carries (F := F) 1 [t1, big_sigma0 a, mj]
      let round : Sha256BinaryRoundCols F :=
        ⟨u32_to_bits_le ch, u32_to_bits_le mj, fun j => t1_carries.getD j (fun _ => 0),
          u32_to_bits_le t1, new_a_carries.getD 0 (fun _ => 0)⟩
      pure ({ row with rounds := Function.update row.rounds t round },
        Function.update a_chain (t + 4) new_a, Function.update e_chain (t + 4) (d + t1)))
    (row, a_chain, e_chain)
  let row := { row with
    a_chain := fun k => u32_to_bits_le (a_chain k)
    e_chain := fun k => u32_to_bits_le (e_chain k) }
  -- The output chaining value.
  let final_state : ℕ → Word := fun i =>
    let chain := if i < 4 then a_chain else e_chain
    chain (NUM_COMPRESSION_ROUNDS + 3 - i % 4)
  pure { row with h_out := fun i => u32_to_bits_le (h_in i + final_state i) }

/-- The trace of the given inputs, one compression per row.

It panics when 2 is not 0 in the field, or when the number of inputs is not a power of two. -/
def generate_binary_trace_rows [DecidableEq F] (inputs : List (List Word)) (_extra_capacity_bits : ℕ) :
    Option (Mat F) := do
  if (2 : F) ≠ 0 then none
  if ¬ (inputs.length ≠ 0 ∧ 2 ^ Nat.log 2 inputs.length = inputs.length) then none
  let rows ← inputs.mapM (generate_trace_row Sha256BinaryCols.zero)
  pure ⟨NUM_SHA256_BINARY_COLS, rows.flatMap Sha256BinaryCols.cells⟩

/-- The trace packed into one word per 64 rows.

Bit `k` of word `(w, j)` is set when cell `(64 w + k, j)` is 1.

Each group of 64 inputs fills one packed row, one lane per input.

A scratch row is reused from lane to lane and from group to group.

It panics when 2 is not 0 in the field, or when the number of inputs is not a positive power of two. -/
def generate_binary_trace_packed [DecidableEq F] (inputs : List (List Word)) :
    Option (Mat (BitVec 64)) := do
  if (2 : F) ≠ 0 then none
  if inputs.length = 0 then none
  if 2 ^ Nat.log 2 inputs.length ≠ inputs.length then none
  let num_blocks := (inputs.length + 63) / 64
  let (words, _) ← (List.range num_blocks).foldlM
    (fun (acc : List (BitVec 64) × Sha256BinaryCols F) w => do
      let (words, row) := acc
      let input_block := (inputs.drop (64 * w)).take 64
      let (block, row) ← input_block.zipIdx.foldlM
        (fun (acc : (ℕ → BitVec 64) × Sha256BinaryCols F) (input, lane) => do
          let (block, row) := acc
          let row ← generate_trace_row row input
          -- Set bit `lane` of every column whose cell is 1.
          let block := row.cells.zipIdx.foldl (fun block (bit, column) =>
            if bit = 1 then Function.update block column (block column ||| 1#64 <<< lane) else block) block
          pure (block, row)) (fun _ => 0, row)
      pure (words ++ (List.range NUM_SHA256_BINARY_COLS).map block, row)) ([], Sha256BinaryCols.zero)
  pure ⟨NUM_SHA256_BINARY_COLS, words⟩

end p3_sha256_air.mirror.binary
