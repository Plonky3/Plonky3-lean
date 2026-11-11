/-
Transcriptions of the BLAKE2s AIR over a field of characteristic 2: its constants, its column layout and its evaluation.

The evaluation does not extract: it is generic over the builder, whose associated types are bounded by the field traits, which aeneas rejects.

The constants are also extracted, and proved equal to these.

Each definition transcribes one Rust item, named in the crate's mirror entries.

What a transcription abstracts, beyond the builder transcriptions of p3-air:

* a row of the column struct is a map from a column index to a value, with the indices of the struct's `repr(C)` layout;
* a cell past a window reads as the constant 0, where the Rust panics, and a window of the AIR's width holds every cell;
* an array of bits or carries is a map from the bit index to the bit;
* a variable is an expression, which is what every arithmetic operation on it does first.

Loops, branches and the order of assertions are kept.
-/
module

public import P3Air.Assumptions.Mirror.Air
public import Batteries.Data.BitVec

@[expose] public section

namespace p3_blake2s_air.mirror

open p3_air.builder.mirror

/-- A 32-bit word. -/
abbrev Word := BitVec 32

/-! ## The constants -/

/-- The initialization vector. -/
def IV : List Word :=
  [0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19]

/-- The message schedule: row `r` lists the message word each G input reads in round `r`. -/
def SIGMA : List (List ℕ) := [
  [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15],
  [14, 10, 4, 8, 9, 15, 13, 6, 1, 12, 0, 2, 11, 7, 5, 3],
  [11, 8, 12, 0, 5, 2, 15, 13, 10, 14, 3, 6, 7, 1, 9, 4],
  [7, 9, 3, 1, 13, 12, 11, 14, 2, 6, 5, 10, 4, 0, 15, 8],
  [9, 0, 5, 7, 2, 4, 10, 15, 14, 1, 11, 12, 6, 8, 3, 13],
  [2, 12, 6, 10, 0, 11, 8, 3, 4, 13, 7, 5, 15, 14, 1, 9],
  [12, 5, 1, 15, 14, 13, 4, 10, 0, 7, 6, 3, 9, 2, 8, 11],
  [13, 11, 7, 14, 12, 1, 3, 9, 5, 0, 15, 4, 8, 6, 2, 10],
  [6, 15, 14, 9, 11, 3, 0, 8, 12, 2, 13, 7, 1, 4, 10, 5],
  [10, 2, 8, 4, 7, 6, 1, 5, 15, 11, 9, 14, 3, 12, 13, 0]]

/-- The rounds of one compression. -/
def NUM_ROUNDS : ℕ := 10

/-- The G steps of one round. -/
def G_PER_ROUND : ℕ := 8

/-- The positions of the four words each G step of a round mixes, within their state rows. -/
def G_SCHEDULE : List (List ℕ) :=
  [[0, 0, 0, 0], [1, 1, 1, 1], [2, 2, 2, 2], [3, 3, 3, 3],
   [0, 1, 2, 3], [1, 2, 3, 0], [2, 3, 0, 1], [3, 0, 1, 2]]

/-- The 32-bit input words: the chaining value, the block and the two counter halves. -/
def NUM_INPUT_WORDS : ℕ := 8 + 16 + 2

/-- The input cells: 32 per input word, and the finalization flag. -/
def NUM_INPUT_BITS : ℕ := NUM_INPUT_WORDS * 32 + 1

/-- The constraints of one G step: two three-word additions and two two-word additions. -/
def CONSTRAINTS_PER_G : ℕ := 2 * (31 + 32) + 2 * 32

/-- The constraints of all G steps. -/
def NUM_G_CONSTRAINTS : ℕ := NUM_ROUNDS * G_PER_ROUND * CONSTRAINTS_PER_G

/-- The number of constraints the AIR reports: the input booleanity if stated, and the G steps. -/
def num_constraints (constrain_booleanity : Bool) : Option ℕ :=
  let booleanity := if constrain_booleanity then NUM_INPUT_BITS else 0
  some (booleanity + NUM_G_CONSTRAINTS)

/-! ## The column layout -/

-- The column indices of the struct's fields, in declaration order.
namespace col

def chaining_value (i b : ℕ) : ℕ := 32 * i + b
def block (i b : ℕ) : ℕ := 256 + 32 * i + b
def counter_low (b : ℕ) : ℕ := 768 + b
def counter_high (b : ℕ) : ℕ := 800 + b
def last_block : ℕ := 832

/-- The first column of G step `g` of round `r`. -/
def g_base (r g : ℕ) : ℕ := 833 + 190 * (8 * r + g)

def add1_carries (r g c : ℕ) : ℕ := g_base r g + c
def d1 (r g b : ℕ) : ℕ := g_base r g + 31 + b
def b1 (r g b : ℕ) : ℕ := g_base r g + 63 + b
def add2_carries (r g c : ℕ) : ℕ := g_base r g + 95 + c
def d2 (r g b : ℕ) : ℕ := g_base r g + 126 + b
def b2 (r g b : ℕ) : ℕ := g_base r g + 158 + b

end col

/-- The number of columns. -/
def NUM_BLAKE2S_BINARY_COLS : ℕ := 16033

/-! ## The evaluation -/

variable {F E : Type} [Field F]

/-- The bits of a word, least significant first: bit i is `val & (1 << i) != 0`. -/
def u32_to_bits_le (val : Word) : ℕ → F := fun i =>
  if val &&& (1#32 <<< i) ≠ 0 then 1 else 0

/-- The witness columns of one G step, as maps from the bit index. -/
structure Blake2sBinaryGCols (T : Type) where
  add1_carries : ℕ → T
  d1 : ℕ → T
  b1 : ℕ → T
  add2_carries : ℕ → T
  d2 : ℕ → T
  b2 : ℕ → T

/-- The working state as bits: four rows of four words. -/
structure State (E : Type) where
  a : ℕ → ℕ → E
  b : ℕ → ℕ → E
  c : ℕ → ℕ → E
  d : ℕ → ℕ → E

/-- The bits of `x ^ (y <<< shift)`, where `x` is already an expression. -/
def xor_rotl (O : ExprOps F E) (x y : ℕ → E) (shift : ℕ) : ℕ → E := fun i =>
  O.add (x i) (y ((i + 32 - shift) % 32))

/-- The bits of `x ^ (y <<< shift)`, where `x` is held in trace columns. -/
def xor_rotl_var (O : ExprOps F E) (x y : ℕ → E) (shift : ℕ) : ℕ → E := fun i =>
  O.add (x i) (y ((i + 32 - shift) % 32))

/-- The majority of three bits, `(x + z) (y + z) + z` in characteristic 2. -/
def maj (O : ExprOps F E) (x y z : E) : E := O.add (O.mul (O.add x z) (O.add y z)) z

section add

variable {S : Type} (B : AirBuilder F E S)

/-- Constrain `sum = x + y mod 2^32`, with each carry read off the sum as `sum_i + x_i + y_i`. -/
def add2 (s : S) (x y sum : ℕ → E) : S :=
  let carries : ℕ → E := fun i => B.add (B.add (sum i) (x i)) (y i)
  let s := B.assert_zero s (carries 0)
  (List.range 31).foldl (fun s i =>
    B.assert_zero s (B.add (maj B.toExprOps (x i) (y i) (carries i)) (carries (i + 1)))) s

/-- Constrain `sum = x + y + z mod 2^32`, with the carries of `x + y` stored in columns.

Entry `i` of the carries is the carry into bit `i + 1` of `x + y`. -/
def add3 (s : S) (x y z carries sum : ℕ → E) : S :=
  let s := B.assert_zero s (B.add (B.mul (x 0) (y 0)) (carries 0))
  let s := (List.range' 1 30).foldl (fun s i =>
    B.assert_zero s (B.add (maj B.toExprOps (x i) (y i) (carries (i - 1))) (carries i))) s
  let t : ℕ → E := fun i =>
    if i = 0 then B.add (x 0) (y 0) else B.add (B.add (x i) (y i)) (carries (i - 1))
  add2 B s t z sum

/-- Constrain one G step, and replace the four words it mixes with their new values.

The four slots are the positions of the `a`, `b`, `c`, `d` words within their state rows. -/
def eval_g (s : S) (state : State E) (slots : List ℕ) (mx my : ℕ → E)
    (cols : Blake2sBinaryGCols E) : S × State E :=
  let ia := slots.getD 0 0
  let ib := slots.getD 1 0
  let ic := slots.getD 2 0
  let id := slots.getD 3 0
  let b := state.b ib
  let d := state.d id
  -- a_1 = a + b + m_x, with a_1 = d ^ (d_1 <<< 16).
  let a1 := xor_rotl B.toExprOps d cols.d1 16
  let s := add3 B s (state.a ia) b mx cols.add1_carries a1
  -- c_1 = c + d_1, with c_1 = b ^ (b_1 <<< 12).
  let c1 := xor_rotl_var B.toExprOps b cols.b1 12
  let s := add2 B s (state.c ic) cols.d1 c1
  -- a_2 = a_1 + b_1 + m_y, with a_2 = d_1 ^ (d_2 <<< 8).
  let a2 := xor_rotl_var B.toExprOps cols.d1 cols.d2 8
  let s := add3 B s a1 cols.b1 my cols.add2_carries a2
  -- c_2 = c_1 + d_2, with c_2 = b_1 ^ (b_2 <<< 7).
  let c2 := xor_rotl_var B.toExprOps cols.b1 cols.b2 7
  let s := add2 B s c1 cols.d2 c2
  (s, { a := Function.update state.a ia a2
        b := Function.update state.b ib cols.b2
        c := Function.update state.c ic c2
        d := Function.update state.d id cols.d2 })

end add

/-- The evaluation of the BLAKE2s AIR, with or without the input booleanity. -/
def eval (constrain_booleanity : Bool) {S : Type} (B : AirBuilder F E S) (s : S) : S :=
  let main := B.main s
  let loc : ℕ → E := fun i => main.current.getD i (B.const 0)
  let chaining_value : ℕ → ℕ → E := fun i b => loc (col.chaining_value i b)
  let block : ℕ → ℕ → E := fun i b => loc (col.block i b)
  let counter_low : ℕ → E := fun b => loc (col.counter_low b)
  let counter_high : ℕ → E := fun b => loc (col.counter_high b)
  let last_block := loc col.last_block
  -- The input booleanity, in column order.
  let s := if constrain_booleanity then
      let words := (List.range 8).map chaining_value ++ (List.range 16).map block ++
        [counter_low, counter_high]
      let s := words.foldl (fun s word => B.assert_bools s ((List.range 32).map word)) s
      B.assert_bool s last_block
    else s
  -- The words XORed into v[12..15]: the counter halves and the flag repeated over 32 bits.
  let parameters : List (ℕ → E) := [counter_low, counter_high, fun _ => last_block]
  let state : State E :=
    { a := chaining_value
      b := fun i => chaining_value (4 + i)
      c := fun i bit => B.const (u32_to_bits_le (IV.getD i 0) bit)
      d := fun i =>
        let iv : ℕ → E := fun bit => B.const (u32_to_bits_le (IV.getD (4 + i) 0) bit)
        match parameters[i]? with
        | none => iv
        | some word => fun bit => B.add (iv bit) (word bit) }
  let gcols (r g : ℕ) : Blake2sBinaryGCols E :=
    ⟨fun c => loc (col.add1_carries r g c), fun b => loc (col.d1 r g b), fun b => loc (col.b1 r g b),
      fun c => loc (col.add2_carries r g c), fun b => loc (col.d2 r g b), fun b => loc (col.b2 r g b)⟩
  -- Ten rounds of eight G steps.
  -- Step g of round r reads schedule entries 2g and 2g + 1.
  let acc := (List.range NUM_ROUNDS).foldl (fun acc r =>
    let schedule := SIGMA.getD r []
    (List.range G_PER_ROUND).foldl (fun acc g =>
      eval_g B acc.1 acc.2 (G_SCHEDULE.getD g []) (block (schedule.getD (2 * g) 0))
        (block (schedule.getD (2 * g + 1) 0)) (gcols r g)) acc) (s, state)
  acc.1

end p3_blake2s_air.mirror
