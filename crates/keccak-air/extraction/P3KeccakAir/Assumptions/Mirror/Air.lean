/-
Transcriptions of the Keccak-f AIR over a field of size at least 2^16: its column layout, its round flags and its evaluation.

These do not extract: the evaluation is generic over the builder, whose associated types are bounded by the field traits, which aeneas rejects.

Each definition transcribes one Rust item, named in the crate's mirror entries.

What a transcription abstracts, beyond the builder transcriptions of p3-air:

* a row of the column struct is a map from a column index to a value, with the indices of the struct's `repr(C)` layout;
* a cell past a window reads as the constant 0, where the Rust panics, and a window of the AIR's width holds every cell;
* the sum of an iterator of expressions adds them from the left, and an empty sum is the constant 0, as the symbolic expressions do;
* a variable is an expression, which is what every arithmetic operation on it does first.

Loops, branches and the order of assertions are kept.
-/
module

public import P3Air.Assumptions.Mirror.Air
public import P3KeccakAir.Assumptions.Mirror.Constants

@[expose] public section

namespace p3_keccak_air.mirror

open p3_air.builder.mirror

/-! ## The column layout -/

-- The column indices of the struct's fields, in declaration order.
namespace col

def step_flags (i : ℕ) : ℕ := i
def export_ : ℕ := 24
def preimage (y x limb : ℕ) : ℕ := 25 + 20 * y + 4 * x + limb
def a (y x limb : ℕ) : ℕ := 125 + 20 * y + 4 * x + limb
def c (x z : ℕ) : ℕ := 225 + 64 * x + z
def c_prime (x z : ℕ) : ℕ := 545 + 64 * x + z
def a_prime (y x z : ℕ) : ℕ := 865 + 320 * y + 64 * x + z
def a_prime_prime (y x limb : ℕ) : ℕ := 2465 + 20 * y + 4 * x + limb
def a_prime_prime_0_0_bits (z : ℕ) : ℕ := 2565 + z
def a_prime_prime_prime_0_0_limbs (limb : ℕ) : ℕ := 2629 + limb

end col

/-- The number of columns: the size of the struct over bytes. -/
def NUM_KECCAK_COLS : ℕ := 2633

/-- Bit z of lane B[x, y]: a bit of A', since rho and pi only move bits.

B[x, y] is ROT(A'[(x + 3 y) mod 5, x], R[(x + 3 y) mod 5][x]). -/
def b {T : Type _} (row : ℕ → T) (x y z : ℕ) : T :=
  let a := (x + 3 * y) % 5
  let b := x
  let rot := rOf a b
  row (col.a_prime b a ((z + 64 - rot) % 64))

/-- Limb `limb` of lane A'''[x, y]: the separate limbs for lane (0, 0), and A'' for the others. -/
def a_prime_prime_prime {T : Type _} (row : ℕ → T) (y x limb : ℕ) : T :=
  if y = 0 ∧ x = 0 then row (col.a_prime_prime_prime_0_0_limbs limb)
  else row (col.a_prime_prime y x limb)

/-! ## The field helpers on expressions -/

variable {F E : Type}

/-- 2 x, as x + x. -/
def double (O : ExprOps F E) (x : E) : E := O.add x x

/-- The arithmetic xor x + y - x (2 y). -/
def xor (O : ExprOps F E) (x y : E) : E := O.sub (O.add x y) (O.mul x (double O y))

/-- The triple xor, as two xors. -/
def xor3 (O : ExprOps F E) (x y z : E) : E := xor O (xor O x y) z

/-- The arithmetic and-not (1 - x) y. -/
def andn [One F] (O : ExprOps F E) (x y : E) : E := O.mul (O.sub (O.const 1) x) y

/-- The sum of a list of expressions: added from the left, and the constant 0 when empty. -/
def sum [Zero F] (O : ExprOps F E) : List E → E
  | [] => O.const 0
  | x :: xs => xs.foldl O.add x

/-- The limb whose bits, least significant first, are those of `bit` at positions limb 16 to limb 16 + 15.

The bits are folded from the most significant: acc <- 2 acc + bit. -/
def limbOf [Zero F] (O : ExprOps F E) (bit : ℕ → E) (limb : ℕ) : E :=
  (List.range' (limb * BITS_PER_LIMB) BITS_PER_LIMB).reverse.foldl
    (fun acc z => O.add (double O acc) (bit z)) (O.const 0)

/-! ## The evaluation -/

variable [Field F]

/-- The round flags: one-hot at round 0 on the first row, and rotated forward on each transition. -/
def eval_round_flags {S : Type} (B : AirBuilder F E S) (s : S) : S :=
  let main := B.main s
  let loc : ℕ → E := fun i => main.current.getD i (B.const 0)
  let nxt : ℕ → E := fun i => main.next.getD i (B.const 0)
  let s := (B.when_first_row s).assert_one s (loc (col.step_flags 0))
  let s := (B.when_first_row s).assert_zeros s
    ((List.range (NUM_ROUNDS - 1)).map fun i => loc (col.step_flags (i + 1)))
  (B.when_transition s).assert_zeros s ((List.range NUM_ROUNDS).map fun i =>
    B.sub (loc (col.step_flags i)) (nxt (col.step_flags ((i + 1) % NUM_ROUNDS))))

/-! Each step of the evaluation below is one loop of the Rust body, over the rows `loc` and `nxt`. -/

section steps

variable {S : Type} (B : AirBuilder F E S) (loc nxt : ℕ → E)

/-- If this is the first step, the input A must match the preimage. -/
def assert_first_step (first_step : E) (s : S) : S :=
  (List.range 5).foldl (fun s y => (List.range 5).foldl (fun s x =>
    (B.when first_step).assert_zeros s ((List.range U64_LIMBS).map fun limb =>
      B.sub (loc (col.preimage y x limb)) (loc (col.a y x limb)))) s) s

/-- If this is not the final step, the local and next preimages must match. -/
def assert_preimage_carry (transition_and_not_final : E) (s : S) : S :=
  (List.range 5).foldl (fun s y => (List.range 5).foldl (fun s x =>
    (B.when transition_and_not_final).assert_zeros s ((List.range U64_LIMBS).map fun limb =>
      B.sub (loc (col.preimage y x limb)) (nxt (col.preimage y x limb)))) s) s

/-- The export flag is a bit, and is off on every step but the final one. -/
def assert_export (not_final_step : E) (s : S) : S :=
  let s := B.assert_bool s (loc col.export_)
  (B.when not_final_step).assert_zero s (loc col.export_)

/-- C is boolean, and C'[x, z] = xor(C[x, z], C[x - 1, z], C[x + 1, z - 1]). -/
def assert_c_prime (s : S) : S :=
  (List.range 5).foldl (fun s x =>
    let s := B.assert_bools s ((List.range 64).map fun z => loc (col.c x z))
    B.assert_zeros s ((List.range 64).map fun z =>
      let xor := xor3 B.toExprOps (loc (col.c x z)) (loc (col.c ((x + 4) % 5) z))
        (loc (col.c ((x + 1) % 5) ((z + 63) % 64)))
      B.sub (loc (col.c_prime x z)) xor)) s

/-- A' is boolean, and the limbs of A are those of xor(A', C, C'). -/
def assert_a_limbs (s : S) : S :=
  (List.range 5).foldl (fun s x =>
    let c_xor_c_prime : ℕ → E := fun z =>
      xor B.toExprOps (loc (col.c x z)) (loc (col.c_prime x z))
    (List.range 5).foldl (fun s y =>
      let get_bit : ℕ → E := fun z => xor B.toExprOps (loc (col.a_prime y x z)) (c_xor_c_prime z)
      let s := B.assert_bools s ((List.range 64).map fun z => loc (col.a_prime y x z))
      B.assert_zeros s ((List.range U64_LIMBS).map fun limb =>
        B.sub (limbOf B.toExprOps get_bit limb) (loc (col.a y x limb)))) s) s

/-- The parity of A'[x, 0..5, z] is C'[x, z]: diff (diff - 2) (diff - 4) = 0. -/
def assert_parity (s : S) : S :=
  (List.range 5).foldl (fun s x =>
    let four := double B.toExprOps (B.const 2)
    B.assert_zeros s ((List.range 64).map fun z =>
      let sum := sum B.toExprOps ((List.range 5).map fun y => loc (col.a_prime y x z))
      let diff := B.sub sum (loc (col.c_prime x z))
      B.mul (B.mul diff (B.sub diff (B.const 2))) (B.sub diff four))) s

/-- A''[x, y] = xor(B[x, y], andn(B[x + 1, y], B[x + 2, y])). -/
def assert_chi (s : S) : S :=
  (List.range 5).foldl (fun s y => (List.range 5).foldl (fun s x =>
    let get_bit : ℕ → E := fun z =>
      let andn := andn B.toExprOps (b loc ((x + 1) % 5) y z) (b loc ((x + 2) % 5) y z)
      xor B.toExprOps andn (b loc x y z)
    B.assert_zeros s ((List.range U64_LIMBS).map fun limb =>
      B.sub (limbOf B.toExprOps get_bit limb) (loc (col.a_prime_prime y x limb)))) s) s

/-- The bits of A''[0, 0] are boolean, and its limbs are theirs. -/
def assert_a_prime_prime_0_0 (s : S) : S :=
  let s := B.assert_bools s ((List.range 64).map fun z => loc (col.a_prime_prime_0_0_bits z))
  B.assert_zeros s ((List.range U64_LIMBS).map fun limb =>
    B.sub (limbOf B.toExprOps (fun z => loc (col.a_prime_prime_0_0_bits z)) limb)
      (loc (col.a_prime_prime 0 0 limb)))

/-- A'''[0, 0] = A''[0, 0] xor RC, with the bit of RC the sum of the flags of the rounds that set it. -/
def assert_iota (s : S) : S :=
  let get_xored_bit : ℕ → E := fun i =>
    let rc_bit_i := sum B.toExprOps
      (((List.range NUM_ROUNDS).filter fun r => rcBit r i ≠ 0).map fun r => loc (col.step_flags r))
    xor B.toExprOps rc_bit_i (loc (col.a_prime_prime_0_0_bits i))
  B.assert_zeros s ((List.range U64_LIMBS).map fun limb =>
    B.sub (limbOf B.toExprOps get_xored_bit limb) (loc (col.a_prime_prime_prime_0_0_limbs limb)))

/-- This round's output is the next round's input. -/
def assert_output (transition_and_not_final : E) (s : S) : S :=
  (List.range 5).foldl (fun s x => (List.range 5).foldl (fun s y =>
    (B.when transition_and_not_final).assert_zeros s ((List.range U64_LIMBS).map fun limb =>
      B.sub (a_prime_prime_prime loc y x limb) (nxt (col.a y x limb)))) s) s

end steps

/-- The evaluation of the Keccak-f AIR. -/
def eval {S : Type} (B : AirBuilder F E S) (s : S) : S :=
  let s := eval_round_flags B s
  let main := B.main s
  let loc : ℕ → E := fun i => main.current.getD i (B.const 0)
  let nxt : ℕ → E := fun i => main.next.getD i (B.const 0)
  let first_step := loc (col.step_flags 0)
  let final_step := loc (col.step_flags (NUM_ROUNDS - 1))
  let not_final_step := B.sub (B.const 1) final_step
  let transition_and_not_final := B.mul (B.is_transition s) not_final_step
  let s := assert_first_step B loc first_step s
  let s := assert_preimage_carry B loc nxt transition_and_not_final s
  let s := assert_export B loc not_final_step s
  let s := assert_c_prime B loc s
  let s := assert_a_limbs B loc s
  let s := assert_parity B loc s
  let s := assert_chi B loc s
  let s := assert_a_prime_prime_0_0 B loc s
  let s := assert_iota B loc s
  assert_output B loc nxt transition_and_not_final s

end p3_keccak_air.mirror
