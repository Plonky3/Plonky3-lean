/-
Transcriptions of the SHA-256 AIR over a prime field: its column layout, the addition helpers it calls, and its evaluation.

These do not extract: the evaluation is generic over the builder, whose associated types are bounded by the field traits, which aeneas rejects.

Each definition transcribes one Rust item, named in the crate's mirror entries.

What a transcription abstracts, beyond the builder transcriptions of p3-air:

* a row of the column struct is a map from a column index to a value, with the indices of the struct's `repr(C)` layout;
* a cell past a window reads as the constant 0, where the Rust panics, and a window of the AIR's width holds every cell;
* an array of two limbs is a map from the limb index to the limb;
* a variable is an expression, which is what every arithmetic operation on it does first;
* the constant 2^16 is checked to lie below the characteristic, and the Rust panics otherwise; the check is dropped, and the claims say what they assume of the characteristic.

Loops, branches and the order of assertions are kept.
-/
module

public import P3Air.Assumptions.Mirror.Air
public import P3Sha256Air.Assumptions.Mirror.Constants

@[expose] public section

namespace p3_sha256_air.mirror

open p3_air.builder.mirror

/-! ## The column layout -/

-- The column indices of the struct's fields, in declaration order.
namespace col

def h_in (i limb : ℕ) : ℕ := 2 * i + limb
def a_chain (k b : ℕ) : ℕ := 16 + 32 * k + b
def e_chain (k b : ℕ) : ℕ := 2192 + 32 * k + b
def w (t b : ℕ) : ℕ := 4368 + 32 * t + b
def sched_sigma0 (i limb : ℕ) : ℕ := 6416 + 2 * i + limb
def sched_sigma1 (i limb : ℕ) : ℕ := 6512 + 2 * i + limb
def sched_tmp (i limb : ℕ) : ℕ := 6608 + 2 * i + limb
def sigma1_e (t limb : ℕ) : ℕ := 6704 + 12 * t + limb
def ch (t limb : ℕ) : ℕ := 6704 + 12 * t + 2 + limb
def tmp1 (t limb : ℕ) : ℕ := 6704 + 12 * t + 4 + limb
def t1 (t limb : ℕ) : ℕ := 6704 + 12 * t + 6 + limb
def sigma0_a (t limb : ℕ) : ℕ := 6704 + 12 * t + 8 + limb
def maj (t limb : ℕ) : ℕ := 6704 + 12 * t + 10 + limb
def h_out (i b : ℕ) : ℕ := 7472 + 32 * i + b

end col

/-- The number of columns: the size of the struct over bytes. -/
def NUM_SHA256_COLS : ℕ := 7728

/-! ## The field helpers on expressions -/

variable {F E : Type}

/-- 2 x, as x + x. -/
def double (O : ExprOps F E) (x : E) : E := O.add x x

/-- The arithmetic xor x + y - x (2 y). -/
def xor (O : ExprOps F E) (x y : E) : E := O.sub (O.add x y) (O.mul x (double O y))

/-- The triple xor, as two xors. -/
def xor3 (O : ExprOps F E) (x y z : E) : E := xor O (xor O x y) z

/-- x^power by square and multiply over the bits of power, from the constant 1. -/
def exp_u64 [One F] (O : ExprOps F E) (x : E) (power : ℕ) : E :=
  ((List.range (Nat.size power)).foldl (fun (acc : E × E) j =>
    let (current, product) := acc
    let product := if power.testBit j then O.mul product current else product
    (O.mul current current, product)) (x, O.const 1)).2

/-- x 2^exp, as x times the constant 2 raised to exp. -/
def mul_2exp_u64 [One F] [OfNat F 2] (O : ExprOps F E) (x : E) (exp : ℕ) : E :=
  O.mul x (exp_u64 O (O.const 2) exp)

/-- The bits folded from the last: acc <- 2 acc + bit, starting from the last bit, and the constant 0 for no bit. -/
def pack_bits_le [Zero F] (O : ExprOps F E) (bits : List E) : E :=
  match bits.reverse with
  | [] => O.const 0
  | x :: rest => rest.foldl (fun acc e => O.add (double O acc) e) x

/-! ## The addition helpers of p3-air -/

section add

variable [Field F] {S : Type} (B : AirBuilder F E S)

/-- a = b + c mod 2^32 on 16-bit limbs: acc (acc + 2^32) = 0 and acc_16 (acc_16 + 2^16) = 0. -/
def add2 (s : S) (a b c : ℕ → E) : S :=
  let two_16 : F := 65536
  let two_32 := two_16 * two_16
  let acc_16 := B.sub (B.sub (a 0) (b 0)) (c 0)
  let acc_32 := B.sub (B.sub (a 1) (b 1)) (c 1)
  let acc := B.add acc_16 (mul_2exp_u64 B.toExprOps acc_32 16)
  B.assert_zeros s [B.mul acc (B.add acc (B.const two_32)),
    B.mul acc_16 (B.add acc_16 (B.const two_16))]

/-- a = b + c + d mod 2^32 on 16-bit limbs: the cubic checks with roots 0, -2^32, -2^33 and 0, -2^16, -2^17. -/
def add3 (s : S) (a b c d : ℕ → E) : S :=
  let two_16 : F := 65536
  let two_32 := two_16 * two_16
  let acc_16 := B.sub (B.sub (B.sub (a 0) (b 0)) (c 0)) (d 0)
  let acc_32 := B.sub (B.sub (B.sub (a 1) (b 1)) (c 1)) (d 1)
  let acc := B.add acc_16 (mul_2exp_u64 B.toExprOps acc_32 16)
  B.assert_zeros s [
    B.mul (B.mul acc (B.add acc (B.const two_32))) (B.add acc (B.const (two_32 + two_32))),
    B.mul (B.mul acc_16 (B.add acc_16 (B.const two_16))) (B.add acc_16 (B.const (two_16 + two_16)))]

/-- `add2` with the output given as an expression. -/
def add2_expr_out (s : S) (a b c : ℕ → E) : S :=
  let two_16 : F := 65536
  let two_32 := two_16 * two_16
  let acc_16 := B.sub (B.sub (a 0) (b 0)) (c 0)
  let acc_32 := B.sub (B.sub (a 1) (b 1)) (c 1)
  let acc := B.add acc_16 (mul_2exp_u64 B.toExprOps acc_32 BITS_PER_LIMB)
  B.assert_zeros s [B.mul acc (B.add acc (B.const two_32)),
    B.mul acc_16 (B.add acc_16 (B.const two_16))]

/-- `add3` with the output given as an expression. -/
def add3_expr_out (s : S) (a b c d : ℕ → E) : S :=
  let two_16 : F := 65536
  let two_32 := two_16 * two_16
  let acc_16 := B.sub (B.sub (B.sub (a 0) (b 0)) (c 0)) (d 0)
  let acc_32 := B.sub (B.sub (B.sub (a 1) (b 1)) (c 1)) (d 1)
  let acc := B.add acc_16 (mul_2exp_u64 B.toExprOps acc_32 BITS_PER_LIMB)
  B.assert_zeros s [
    B.mul (B.mul acc (B.add acc (B.const two_32))) (B.add acc (B.const (two_32 + two_32))),
    B.mul (B.mul acc_16 (B.add acc_16 (B.const two_16))) (B.add acc_16 (B.const (two_16 + two_16)))]

end add

/-! ## The word helpers of the AIR -/

/-- The two limbs of a word of bits: bits 0 to 15, and bits 16 to 31. -/
def pack_word [Zero F] (O : ExprOps F E) (bits : ℕ → E) : ℕ → E := fun limb =>
  pack_bits_le O ((List.range' (limb * BITS_PER_LIMB) BITS_PER_LIMB).map bits)

/-- The four sigma functions. -/
inductive SigmaSpec where
  | BigSigma0
  | BigSigma1
  | SmallSigma0
  | SmallSigma1

/-- A rotation or a logical shift. -/
inductive ShiftKind where
  | Rotate
  | Logical

/-- The two rotations and the third rotation or shift of a sigma function. -/
def sigma_params : SigmaSpec → ℕ × ℕ × ℕ × ShiftKind
  | .BigSigma0 => (2, 13, 22, .Rotate)
  | .BigSigma1 => (6, 11, 25, .Rotate)
  | .SmallSigma0 => (7, 18, 3, .Logical)
  | .SmallSigma1 => (17, 19, 10, .Logical)

section asserts

variable [Field F] {S : Type} (B : AirBuilder F E S)

/-- The packed word equals the packing of the bits. -/
def assert_packed_equals_bits (s : S) (packed bits : ℕ → E) : S :=
  let lo := pack_word B.toExprOps bits 0
  let hi := pack_word B.toExprOps bits 1
  B.assert_zeros s [B.sub (packed 0) lo, B.sub (packed 1) hi]

/-- The packed word equals sigma of the bits: bit i is the triple xor of the bits the sigma function reads. -/
def assert_sigma_matches (s : S) (bits : ℕ → E) (spec : SigmaSpec) (packed : ℕ → E) : S :=
  let (r1, r2, r3, kind) := sigma_params spec
  let get_shifted_bit : ℕ → E := fun i =>
    match kind with
    | .Rotate => bits ((i + r3) % WORD_BITS)
    | .Logical => if i + r3 < WORD_BITS then bits (i + r3) else B.const 0
  let built : ℕ → E := fun limb =>
    (List.range' (limb * BITS_PER_LIMB) BITS_PER_LIMB).reverse.foldl (fun acc i =>
      let b1 := bits ((i + r1) % WORD_BITS)
      let b2 := bits ((i + r2) % WORD_BITS)
      let b3 := get_shifted_bit i
      B.add (double B.toExprOps acc) (xor3 B.toExprOps b1 b2 b3)) (B.const 0)
  B.assert_zeros s [B.sub (packed 0) (built 0), B.sub (packed 1) (built 1)]

/-- The packed word equals Ch(e, f, g): bit i is e_i f_i + (1 - e_i) g_i. -/
def assert_ch_matches (s : S) (e f g packed : ℕ → E) : S :=
  let built : ℕ → E := fun limb =>
    (List.range' (limb * BITS_PER_LIMB) BITS_PER_LIMB).reverse.foldl (fun acc i =>
      let ch_i := B.add (B.mul (e i) (f i)) (B.mul (B.sub (B.const 1) (e i)) (g i))
      B.add (double B.toExprOps acc) ch_i) (B.const 0)
  B.assert_zeros s [B.sub (packed 0) (built 0), B.sub (packed 1) (built 1)]

/-- The packed word equals Maj(a, b, c): bit i is a_i b_i + c_i xor(a_i, b_i). -/
def assert_maj_matches (s : S) (a b c packed : ℕ → E) : S :=
  let built : ℕ → E := fun limb =>
    (List.range' (limb * BITS_PER_LIMB) BITS_PER_LIMB).reverse.foldl (fun acc i =>
      let maj_i := B.add (B.mul (a i) (b i)) (B.mul (c i) (xor B.toExprOps (a i) (b i)))
      B.add (double B.toExprOps acc) maj_i) (B.const 0)
  B.assert_zeros s [B.sub (packed 0) (built 0), B.sub (packed 1) (built 1)]

end asserts

/-! ## The evaluation -/

/-! Each step of the evaluation below is one function of the Rust body, over the row `loc`. -/

section steps

variable [Field F] {S : Type} (B : AirBuilder F E S) (loc : ℕ → E)

/-- Every bit column is boolean: the schedule, the two chains, and the output. -/
def eval_bit_range_checks (s : S) : S :=
  let s := (List.range NUM_COMPRESSION_ROUNDS).foldl (fun s t =>
    B.assert_bools s ((List.range WORD_BITS).map fun b => loc (col.w t b))) s
  let s := (List.range CHAIN_LEN).foldl (fun s k =>
    B.assert_bools s ((List.range WORD_BITS).map fun b => loc (col.a_chain k b))) s
  let s := (List.range CHAIN_LEN).foldl (fun s k =>
    B.assert_bools s ((List.range WORD_BITS).map fun b => loc (col.e_chain k b))) s
  (List.range STATE_WORDS).foldl (fun s i =>
    B.assert_bools s ((List.range WORD_BITS).map fun b => loc (col.h_out i b))) s

/-- The packed input words are the first four entries of each chain, in reverse. -/
def eval_initial_state (s : S) : S :=
  let s := (List.range 4).foldl (fun s i =>
    let chain_idx := 3 - i
    assert_packed_equals_bits B s (fun limb => loc (col.h_in i limb))
      (fun b => loc (col.a_chain chain_idx b))) s
  (List.range 4).foldl (fun s i =>
    let chain_idx := 3 - i
    assert_packed_equals_bits B s (fun limb => loc (col.h_in (4 + i) limb))
      (fun b => loc (col.e_chain chain_idx b))) s

/-- The schedule words 16 to 63: two sigma checks and two additions each. -/
def eval_message_schedule (s : S) : S :=
  (List.range SCHEDULE_EXTENSIONS).foldl (fun s i =>
    let t := i + BLOCK_WORDS
    let wb : ℕ → ℕ → E := fun t b => loc (col.w t b)
    let s := assert_sigma_matches B s (wb (t - 15)) .SmallSigma0
      (fun limb => loc (col.sched_sigma0 i limb))
    let s := assert_sigma_matches B s (wb (t - 2)) .SmallSigma1
      (fun limb => loc (col.sched_sigma1 i limb))
    let w_tm7_packed_expr := pack_word B.toExprOps (wb (t - 7))
    let s := add2 B s (fun limb => loc (col.sched_tmp i limb))
      (fun limb => loc (col.sched_sigma1 i limb)) w_tm7_packed_expr
    let w_t_packed_expr := pack_word B.toExprOps (wb t)
    let sched_sigma0_expr : ℕ → E := fun limb => loc (col.sched_sigma0 i limb)
    let w_tm16_packed_expr := pack_word B.toExprOps (wb (t - 16))
    add3_expr_out B s w_t_packed_expr (fun limb => loc (col.sched_tmp i limb)) sched_sigma0_expr
      w_tm16_packed_expr) s

/-- The 64 rounds: the two sigma checks, Ch and Maj, and the four additions of each. -/
def eval_compression (s : S) : S :=
  (List.range NUM_COMPRESSION_ROUNDS).foldl (fun s t =>
    let ab : ℕ → ℕ → E := fun k b => loc (col.a_chain k b)
    let eb : ℕ → ℕ → E := fun k b => loc (col.e_chain k b)
    let a_bits := ab (t + 3)
    let b_bits := ab (t + 2)
    let c_bits := ab (t + 1)
    let d_bits := ab t
    let e_bits := eb (t + 3)
    let f_bits := eb (t + 2)
    let g_bits := eb (t + 1)
    let h_bits := eb t
    let s := assert_sigma_matches B s e_bits .BigSigma1 (fun limb => loc (col.sigma1_e t limb))
    let s := assert_ch_matches B s e_bits f_bits g_bits (fun limb => loc (col.ch t limb))
    let ch_expr : ℕ → E := fun limb => loc (col.ch t limb)
    let h_packed_expr := pack_word B.toExprOps h_bits
    let s := add3 B s (fun limb => loc (col.tmp1 t limb)) (fun limb => loc (col.sigma1_e t limb))
      ch_expr h_packed_expr
    let k_expr : ℕ → E := fun limb =>
      if limb = 0 then B.const ((kOf t &&& 0xFFFF : ℕ) : F)
      else B.const ((kOf t >>> BITS_PER_LIMB : ℕ) : F)
    let w_packed_expr := pack_word B.toExprOps (fun b => loc (col.w t b))
    let s := add3 B s (fun limb => loc (col.t1 t limb)) (fun limb => loc (col.tmp1 t limb))
      k_expr w_packed_expr
    let s := assert_sigma_matches B s a_bits .BigSigma0 (fun limb => loc (col.sigma0_a t limb))
    let s := assert_maj_matches B s a_bits b_bits c_bits (fun limb => loc (col.maj t limb))
    let new_a_packed_expr := pack_word B.toExprOps (ab (t + 4))
    let sigma0_a_expr : ℕ → E := fun limb => loc (col.sigma0_a t limb)
    let maj_expr : ℕ → E := fun limb => loc (col.maj t limb)
    let s := add3_expr_out B s new_a_packed_expr (fun limb => loc (col.t1 t limb)) sigma0_a_expr
      maj_expr
    let new_e_packed_expr := pack_word B.toExprOps (eb (t + 4))
    let d_packed_expr := pack_word B.toExprOps d_bits
    add2_expr_out B s new_e_packed_expr (fun limb => loc (col.t1 t limb)) d_packed_expr) s

/-- The output words are the input words plus the last four entries of each chain. -/
def eval_finalization (s : S) : S :=
  let s := (List.range 4).foldl (fun s i =>
    let packed_expr := pack_word B.toExprOps (fun b => loc (col.a_chain (CHAIN_LEN - 1 - i) b))
    let h_out_expr := pack_word B.toExprOps (fun b => loc (col.h_out i b))
    add2_expr_out B s h_out_expr (fun limb => loc (col.h_in i limb)) packed_expr) s
  (List.range 4).foldl (fun s i =>
    let packed_expr := pack_word B.toExprOps (fun b => loc (col.e_chain (CHAIN_LEN - 1 - i) b))
    let h_out_expr := pack_word B.toExprOps (fun b => loc (col.h_out (4 + i) b))
    add2_expr_out B s h_out_expr (fun limb => loc (col.h_in (4 + i) limb)) packed_expr) s

end steps

/-- The evaluation of the SHA-256 AIR. -/
def eval [Field F] {S : Type} (B : AirBuilder F E S) (s : S) : S :=
  let main := B.main s
  let loc : ℕ → E := fun i => main.current.getD i (B.const 0)
  let s := eval_bit_range_checks B loc s
  let s := eval_initial_state B loc s
  let s := eval_message_schedule B loc s
  let s := eval_compression B loc s
  eval_finalization B loc s

end p3_sha256_air.mirror
