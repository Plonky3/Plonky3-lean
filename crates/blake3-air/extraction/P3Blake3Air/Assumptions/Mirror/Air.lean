/-
Transcriptions of the BLAKE3 AIR over a prime field: its column layout, the word helpers of p3-air it calls, and its evaluation.

These do not extract: the evaluation is generic over the builder, whose associated types are bounded by the field traits, which aeneas rejects.

Each definition transcribes one Rust item, named in the crate's mirror entries.

What a transcription abstracts, beyond the builder transcriptions of p3-air:

* a row of the column struct is a map from a column index to a value, with the indices of the struct's `repr(C)` layout;
* a borrowed state or quarter round is the map from its word and bit (or limb) to the cell it names;
* a cell past a window reads as the constant 0, where the Rust panics, and a window of the AIR's width holds every cell;
* the checked conversion of 2^16 into the prime subfield is the field element 2^16, where the Rust panics for a characteristic of at most 2^16;
* multiplying by `TWO.exp_u64(e)` multiplies by the constant 2^e, which is what the symbolic expressions fold it to;
* the message permuted in place between rounds is, at round r, the message permuted r times;
* a variable is an expression, which is what every arithmetic operation on it does first.

Loops, branches and the order of assertions are kept.
-/
module

public import P3Air.Assumptions.Mirror.Air
public import P3KeccakAir.Assumptions.Mirror.Air
public import P3Blake3Air.Assumptions.Mirror.Constants

@[expose] public section

namespace p3_blake3_air.mirror

open p3_air.builder.mirror

/-! ## The column layout -/

-- The column indices of the struct's fields, in declaration order.
namespace col

def inputs (i k : ℕ) : ℕ := 32 * i + k
def chaining_values (h j k : ℕ) : ℕ := 512 + 128 * h + 32 * j + k
def counter_low (k : ℕ) : ℕ := 768 + k
def counter_hi (k : ℕ) : ℕ := 800 + k
def block_len (k : ℕ) : ℕ := 832 + k
def flags (k : ℕ) : ℕ := 864 + k
def initial_row0 (j l : ℕ) : ℕ := 896 + 2 * j + l
def initial_row2 (j l : ℕ) : ℕ := 904 + 2 * j + l

/-- The first column of state s of full round r.

The states are, in order, the middle and output states of the columns, then of the diagonals. -/
def state (r s : ℕ) : ℕ := 912 + 1088 * r + 272 * s

def final_round_helpers (j k : ℕ) : ℕ := 8528 + 32 * j + k
def outputs (q j k : ℕ) : ℕ := 8656 + 128 * q + 32 * j + k

end col

/-- The number of columns: the size of the struct over bytes. -/
def NUM_BLAKE3_COLS : ℕ := 9168

/-- A state: rows 0 and 2 as two 16-bit limbs per word, rows 1 and 3 as 32 bits per word. -/
structure Blake3State (T : Type _) where
  row0 : ℕ → ℕ → T
  row1 : ℕ → ℕ → T
  row2 : ℕ → ℕ → T
  row3 : ℕ → ℕ → T

/-- The cells of the state whose first column is `base`, read through `loc`. -/
def stateAt {T : Type _} (loc : ℕ → T) (base : ℕ) : Blake3State T :=
  ⟨fun j l => loc (base + 2 * j + l), fun j k => loc (base + 8 + 32 * j + k),
    fun j l => loc (base + 136 + 2 * j + l), fun j k => loc (base + 144 + 32 * j + k)⟩

/-- The four states of a full round. -/
structure FullRound (T : Type _) where
  state_prime : Blake3State T
  state_middle : Blake3State T
  state_middle_prime : Blake3State T
  state_output : Blake3State T

/-- The cells of full round `r`. -/
def fullRoundAt {T : Type _} (loc : ℕ → T) (r : ℕ) : FullRound T :=
  ⟨stateAt loc (col.state r 0), stateAt loc (col.state r 1), stateAt loc (col.state r 2),
    stateAt loc (col.state r 3)⟩

/-- The words a quarter round reads and writes, and its two message words as limbs. -/
structure QuarterRound (T U : Type _) where
  a : ℕ → T
  b : ℕ → T
  c : ℕ → T
  d : ℕ → T
  m_two_i : ℕ → U
  a_prime : ℕ → T
  b_prime : ℕ → T
  c_prime : ℕ → T
  d_prime : ℕ → T
  m_two_i_plus_one : ℕ → U
  a_output : ℕ → T
  b_output : ℕ → T
  c_output : ℕ → T
  d_output : ℕ → T

/-! ## The word helpers of p3-air -/

variable {F E : Type}

/-- Pack bits, least significant first, as acc <- 2 acc + bit from the last.

The empty list packs to the constant 0. -/
def pack_bits_le [Zero F] (O : ExprOps F E) (bits : List E) : E :=
  match bits.reverse with
  | [] => O.const 0
  | x :: xs => xs.foldl (fun acc elem => O.add (p3_keccak_air.mirror.double O acc) elem) x

/-- Bits 0 to 15 of a word. -/
def low16 [Zero F] (O : ExprOps F E) (bits : ℕ → E) : E :=
  pack_bits_le O ((List.range BITS_PER_LIMB).map bits)

/-- Bits 16 to 31 of a word. -/
def high16 [Zero F] (O : ExprOps F E) (bits : ℕ → E) : E :=
  pack_bits_le O ((List.range' BITS_PER_LIMB BITS_PER_LIMB).map bits)

/-- Multiply by 2^e. -/
def mul_2exp [Field F] (O : ExprOps F E) (x : E) (e : ℕ) : E := O.mul x (O.const (2 ^ e))

variable [Field F] {S : Type}

/-- Assert a = b + c + d mod 2^32, on 16-bit limbs. -/
def add3 (B : AirBuilder F E S) (s : S) (a b c d : ℕ → E) : S :=
  let two_16 : F := (2 ^ 16 : ℕ)
  let two_32 := two_16 * two_16
  let acc_16 := B.sub (B.sub (B.sub (a 0) (b 0)) (c 0)) (d 0)
  let acc_32 := B.sub (B.sub (B.sub (a 1) (b 1)) (c 1)) (d 1)
  let acc := B.add acc_16 (mul_2exp B.toExprOps acc_32 16)
  B.assert_zeros s
    [B.mul (B.mul acc (B.add acc (B.const two_32))) (B.add acc (B.const (two_32 + two_32))),
     B.mul (B.mul acc_16 (B.add acc_16 (B.const two_16))) (B.add acc_16 (B.const (two_16 + two_16)))]

/-- Assert a = b + c mod 2^32, on 16-bit limbs. -/
def add2 (B : AirBuilder F E S) (s : S) (a b c : ℕ → E) : S :=
  let two_16 : F := (2 ^ 16 : ℕ)
  let two_32 := two_16 * two_16
  let acc_16 := B.sub (B.sub (a 0) (b 0)) (c 0)
  let acc_32 := B.sub (B.sub (a 1) (b 1)) (c 1)
  let acc := B.add acc_16 (mul_2exp B.toExprOps acc_32 16)
  B.assert_zeros s
    [B.mul acc (B.add acc (B.const two_32)), B.mul acc_16 (B.add acc_16 (B.const two_16))]

/-- Assert that c is 32 bits and that the limbs of a are those of b xor (c rotated left by shift). -/
def xor_32_shift (B : AirBuilder F E S) (s : S) (a b c : ℕ → E) (shift : ℕ) : S :=
  let s := B.assert_bools s ((List.range 32).map c)
  let sum_0_16 := pack_bits_le B.toExprOps ((List.range 16).map fun i =>
    p3_keccak_air.mirror.xor B.toExprOps (b i) (c ((32 + i - shift) % 32)))
  let sum_16_32 := pack_bits_le B.toExprOps ((List.range 16).map fun i =>
    p3_keccak_air.mirror.xor B.toExprOps (b (16 + i)) (c ((32 + (i + 16) - shift) % 32)))
  B.assert_zeros s [B.sub (a 0) sum_0_16, B.sub (a 1) sum_16_32]

/-! ## The evaluation -/

section steps

variable (B : AirBuilder F E S)

/-- The constraints of one quarter round, given its inputs, its middle words and its outputs. -/
def quarter_round_function (s : S) (t : QuarterRound E E) : S :=
  -- a' = a + b + m_{2i}.
  let b_limbs : ℕ → E := fun l => if l = 0 then low16 B.toExprOps t.b else high16 B.toExprOps t.b
  let s := add3 B s (t.a_prime) (t.a) b_limbs t.m_two_i
  -- a' = d xor (d' <<< 16).
  let s := xor_32_shift B s t.a_prime t.d t.d_prime 16
  -- c' = c + d'.
  let d_prime_limbs : ℕ → E := fun l =>
    if l = 0 then low16 B.toExprOps t.d_prime else high16 B.toExprOps t.d_prime
  let s := add2 B s t.c_prime t.c d_prime_limbs
  -- c' = b xor (b' <<< 12).
  let s := xor_32_shift B s t.c_prime t.b t.b_prime 12
  -- a'' = a' + b' + m_{2i + 1}.
  let b_prime_limbs : ℕ → E := fun l =>
    if l = 0 then low16 B.toExprOps t.b_prime else high16 B.toExprOps t.b_prime
  let s := add3 B s t.a_output t.a_prime b_prime_limbs t.m_two_i_plus_one
  -- a'' = d' xor (d'' <<< 8).
  let s := xor_32_shift B s t.a_output t.d_prime t.d_output 8
  -- c'' = c' + d''.
  let d_output_limbs : ℕ → E := fun l =>
    if l = 0 then low16 B.toExprOps t.d_output else high16 B.toExprOps t.d_output
  let s := add2 B s t.c_output t.c_prime d_output_limbs
  -- c'' = b' xor (b'' <<< 7).
  xor_32_shift B s t.c_output t.b_prime t.b_output 7

end steps

/-- The quarter round on column `index`. -/
def full_round_to_column_quarter_round {T U : Type _} (input : Blake3State T)
    (round_data : FullRound T) (m_vector : ℕ → ℕ → U) (index : ℕ) : QuarterRound T U :=
  { a := input.row0 index, b := input.row1 index, c := input.row2 index, d := input.row3 index,
    m_two_i := m_vector (2 * index),
    a_prime := round_data.state_prime.row0 index, b_prime := round_data.state_prime.row1 index,
    c_prime := round_data.state_prime.row2 index, d_prime := round_data.state_prime.row3 index,
    m_two_i_plus_one := m_vector (2 * index + 1),
    a_output := round_data.state_middle.row0 index, b_output := round_data.state_middle.row1 index,
    c_output := round_data.state_middle.row2 index, d_output := round_data.state_middle.row3 index }

/-- The quarter round on diagonal `index`. -/
def full_round_to_diagonal_quarter_round {T U : Type _} (round_data : FullRound T)
    (m_vector : ℕ → ℕ → U) (index : ℕ) : QuarterRound T U :=
  { a := round_data.state_middle.row0 index,
    b := round_data.state_middle.row1 ((index + 1) % 4),
    c := round_data.state_middle.row2 ((index + 2) % 4),
    d := round_data.state_middle.row3 ((index + 3) % 4),
    m_two_i := m_vector (2 * index + 8),
    a_prime := round_data.state_middle_prime.row0 index,
    b_prime := round_data.state_middle_prime.row1 ((index + 1) % 4),
    c_prime := round_data.state_middle_prime.row2 ((index + 2) % 4),
    d_prime := round_data.state_middle_prime.row3 ((index + 3) % 4),
    m_two_i_plus_one := m_vector (2 * index + 9),
    a_output := round_data.state_output.row0 index,
    b_output := round_data.state_output.row1 ((index + 1) % 4),
    c_output := round_data.state_output.row2 ((index + 2) % 4),
    d_output := round_data.state_output.row3 ((index + 3) % 4) }

/-- The constraints of a full round: the four columns, then the four diagonals. -/
def verify_round (B : AirBuilder F E S) (s : S) (input : Blake3State E) (round_data : FullRound E)
    (m_vector : ℕ → ℕ → E) : S :=
  let s := (List.range 4).foldl (fun s index =>
    quarter_round_function B s (full_round_to_column_quarter_round input round_data m_vector index)) s
  (List.range 4).foldl (fun s index =>
    quarter_round_function B s (full_round_to_diagonal_quarter_round round_data m_vector index)) s

/-! Each step of the evaluation below is one loop of the Rust body, over the row `loc`. -/

section body

variable (B : AirBuilder F E S) (loc : ℕ → E)

/-- Row 3 of the initial state: the counter halves, the block length and the flags. -/
def initial_row_3 : ℕ → ℕ → E := fun j k => loc (col.counter_low (32 * j + k))

/-- The inputs, the chaining values, the counter, the block length and the flags are bits. -/
def assert_inputs (s : S) : S :=
  let words : List (ℕ → E) :=
    (List.range 16).map (fun i k => loc (col.inputs i k)) ++
      (List.range 4).map (fun j k => loc (col.chaining_values 0 j k)) ++
      (List.range 4).map (fun j k => loc (col.chaining_values 1 j k)) ++
      (List.range 4).map (initial_row_3 loc)
  words.foldl (fun s elem => (List.range 32).foldl (fun s k => B.assert_bool s (elem k)) s) s

/-- Row 0 of the initial state packs the first four chaining values. -/
def assert_initial_row0 (s : S) : S :=
  (List.range 4).foldl (fun s j =>
    let bits : ℕ → E := fun k => loc (col.chaining_values 0 j k)
    let s := B.assert_eq s (low16 B.toExprOps bits) (loc (col.initial_row0 j 0))
    B.assert_eq s (high16 B.toExprOps bits) (loc (col.initial_row0 j 1))) s

/-- Row 2 of the initial state holds the first four IV words. -/
def assert_initial_row2 (s : S) : S :=
  (List.range 4).foldl (fun s j =>
    let s := B.assert_eq s (loc (col.initial_row2 j 0)) (B.const (ivHalf j 0 : F))
    B.assert_eq s (loc (col.initial_row2 j 1)) (B.const (ivHalf j 1 : F))) s

/-- The message words as limbs packed from their bits. -/
def m_values : ℕ → ℕ → E := fun i l =>
  let bits : ℕ → E := fun k => loc (col.inputs i k)
  if l = 0 then low16 B.toExprOps bits else high16 B.toExprOps bits

/-- The initial state. -/
def initial_state : Blake3State E :=
  ⟨fun j l => loc (col.initial_row0 j l), fun j k => loc (col.chaining_values 1 j k),
    fun j l => loc (col.initial_row2 j l), initial_row_3 loc⟩

/-- The input of round r: the initial state, or the output of round r - 1. -/
def round_input (r : ℕ) : Blake3State E :=
  if r = 0 then initial_state loc else (fullRoundAt loc (r - 1)).state_output

/-- The seven rounds, with the message permuted r times before round r. -/
def verify_rounds (s : S) : S :=
  (List.range 7).foldl (fun s r =>
    verify_round B s (round_input loc r) (fullRoundAt loc r) (permute^[r] (m_values B loc))) s

/-- The final state. -/
def final : Blake3State E := (fullRoundAt loc 6).state_output

/-- The helpers are the bits of row 2 of the final state. -/
def assert_helpers (s : S) : S :=
  (List.range 4).foldl (fun s j =>
    let helpers : ℕ → E := fun k => loc (col.final_round_helpers j k)
    let s := B.assert_eq s (low16 B.toExprOps helpers) ((final loc).row2 j 0)
    B.assert_eq s (high16 B.toExprOps helpers) ((final loc).row2 j 1)) s

/-- Outputs 0 to 3 are bits. -/
def assert_outputs_bool (s : S) : S :=
  (List.range 4).foldl (fun s j =>
    (List.range 32).foldl (fun s k => B.assert_bool s (loc (col.outputs 0 j k))) s) s

/-- Row 0 of the final state is output word j xor helper word j. -/
def assert_output_row0 (s : S) : S :=
  (List.range 4).foldl (fun s j =>
    xor_32_shift B s ((final loc).row0 j) (fun k => loc (col.outputs 0 j k))
      (fun k => loc (col.final_round_helpers j k)) 0) s

/-- Output word block q, bit by bit, is the xor of two bit words. -/
def assert_output_xor (q : ℕ) (x y : ℕ → ℕ → E) (s : S) : S :=
  (List.range 4).foldl (fun s j => (List.range 32).foldl (fun s k =>
    B.assert_eq s (loc (col.outputs q j k)) (p3_keccak_air.mirror.xor B.toExprOps (x j k) (y j k))) s) s

end body

/-- The evaluation of the BLAKE3 AIR over a prime field. -/
def eval (B : AirBuilder F E S) (s : S) : S :=
  let main := B.main s
  let loc : ℕ → E := fun i => main.current.getD i (B.const 0)
  let s := assert_inputs B loc s
  let s := assert_initial_row0 B loc s
  let s := assert_initial_row2 B loc s
  let s := verify_rounds B loc s
  let s := assert_helpers B loc s
  let s := assert_outputs_bool B loc s
  let s := assert_output_row0 B loc s
  -- Outputs 4 to 7: row 1 xor row 3 of the final state.
  let s := assert_output_xor B loc 1 (final loc).row1 (final loc).row3 s
  -- Outputs 8 to 11: the first four chaining values xor the helpers.
  let s := assert_output_xor B loc 2 (fun j k => loc (col.chaining_values 0 j k))
    (fun j k => loc (col.final_round_helpers j k)) s
  -- Outputs 12 to 15: the last four chaining values xor row 3 of the final state.
  assert_output_xor B loc 3 (fun j k => loc (col.chaining_values 1 j k)) (final loc).row3 s

end p3_blake3_air.mirror
