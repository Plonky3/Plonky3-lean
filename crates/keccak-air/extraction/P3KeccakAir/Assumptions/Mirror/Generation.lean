/-
Transcriptions of the trace generator of the Keccak-f AIR over a field of size at least 2^16.

These do not extract: they are generic over the field traits, which aeneas rejects, and they reinterpret rows through `align_to`.

Each definition transcribes one Rust item, named in the crate's mirror entries.

What a transcription abstracts:

* the field is a mathlib field F, a `u16` enters it as a natural number, and a `bool` as 0 or 1;
* a `u64` is a 64-bit vector;
* a row is the column struct with one function per field, and the trace's values are the rows' cells in the struct's `repr(C)` order;
* an array that a loop fills at every index is the function of its index, and an array written at one index is updated there;
* the reserved extra capacity, which does not change the trace, is ignored;
* the parallel iterators are the sequential maps they compute.

Loops, branches and the order of writes are kept.
-/
module

public import P3KeccakAir.Assumptions.Mirror.Air
public import Batteries.Data.BitVec

@[expose] public section

namespace p3_keccak_air.mirror

open p3_air.air.mirror

/-- A lane. -/
abbrev Word := BitVec 64

/-- A row of the column struct, field by field. -/
structure KeccakCols (T : Type) where
  step_flags : ℕ → T
  export_ : T
  preimage : ℕ → ℕ → ℕ → T
  a : ℕ → ℕ → ℕ → T
  c : ℕ → ℕ → T
  c_prime : ℕ → ℕ → T
  a_prime : ℕ → ℕ → ℕ → T
  a_prime_prime : ℕ → ℕ → ℕ → T
  a_prime_prime_0_0_bits : ℕ → T
  a_prime_prime_prime_0_0_limbs : ℕ → T

namespace KeccakCols

variable {T : Type}

/-- The zero row, as the generator's buffers start. -/
def zero [Zero T] : KeccakCols T :=
  ⟨fun _ => 0, 0, fun _ _ _ => 0, fun _ _ _ => 0, fun _ _ => 0, fun _ _ => 0, fun _ _ _ => 0,
    fun _ _ _ => 0, fun _ => 0, fun _ => 0⟩

/-- The cells of a lane-limb field, y first, then x, then the limb. -/
def limbCells (f : ℕ → ℕ → ℕ → T) : List T :=
  (List.range 5).flatMap fun y => (List.range 5).flatMap fun x => (List.range 4).map (f y x)

/-- The cells of a row, in the struct's `repr(C)` order. -/
def cells (r : KeccakCols T) : List T :=
  (List.range 24).map r.step_flags ++ [r.export_] ++ limbCells r.preimage ++ limbCells r.a ++
    ((List.range 5).flatMap fun x => (List.range 64).map (r.c x)) ++
    ((List.range 5).flatMap fun x => (List.range 64).map (r.c_prime x)) ++
    ((List.range 5).flatMap fun y => (List.range 5).flatMap fun x => (List.range 64).map (r.a_prime y x)) ++
    limbCells r.a_prime_prime ++ (List.range 64).map r.a_prime_prime_0_0_bits ++
    (List.range 4).map r.a_prime_prime_prime_0_0_limbs

/-- Limb `limb` of lane A'''[x, y]: the separate limbs for lane (0, 0), and A'' for the others. -/
def a_prime_prime_prime' (r : KeccakCols T) (y x limb : ℕ) : T :=
  if y = 0 ∧ x = 0 then r.a_prime_prime_prime_0_0_limbs limb else r.a_prime_prime y x limb

end KeccakCols

variable {F : Type} [Field F]

/-- The bits of a word, least significant first: bit i is `val & (1 << i) != 0`. -/
def u64_to_bits_le (val : Word) : ℕ → F := fun i =>
  if val &&& (1#64 <<< i) ≠ 0 then 1 else 0

/-- The four 16-bit limbs of a word, least significant first: limb i is `(val >> 16 i) as u16`. -/
def u64_to_16_bit_limbs (val : Word) : ℕ → F := fun i =>
  (((val >>> (16 * i)).toNat % 2 ^ 16 : ℕ) : F)

/-- A state as the generator holds it: `state x y` is lane (x, y). -/
abbrev WState := ℕ → ℕ → Word

/-- Fill the row of round `round` from the round's input state, and return the round's output state. -/
def generate_trace_row_for_round (row : KeccakCols F) (round : ℕ) (current_state : WState) :
    KeccakCols F × WState :=
  let row := { row with step_flags := Function.update row.step_flags round 1 }
  -- C[x] = xor(A[x, 0], A[x, 1], A[x, 2], A[x, 3], A[x, 4]).
  let state_c : ℕ → Word := fun x => (List.range 5).foldl (fun acc y => acc ^^^ current_state x y) 0
  let row := { row with c := fun x => u64_to_bits_le (state_c x) }
  -- C'[x, z] = xor(C[x, z], C[x - 1, z], C[x + 1, z - 1]).
  let state_c_prime : ℕ → Word := fun x =>
    state_c x ^^^ state_c ((x + 4) % 5) ^^^ (state_c ((x + 1) % 5)).rotateLeft 1
  let row := { row with c_prime := fun x => u64_to_bits_le (state_c_prime x) }
  -- A'[x, y, z] = xor(A[x, y, z], C[x, z], C'[x, z]).
  let current_state : WState := fun i j => current_state i j ^^^ state_c i ^^^ state_c_prime i
  let row := { row with a_prime := fun y x => u64_to_bits_le (current_state x y) }
  -- B[i, j] = ROT(A'[(i + 3 j) mod 5, i], R[(i + 3 j) mod 5][i]).
  let current_state : WState := fun i j =>
    let new_i := (i + 3 * j) % 5
    let new_j := i
    (current_state new_i new_j).rotateLeft (rOf new_i new_j)
  -- A''[x, y] = xor(B[x, y], andn(B[x + 1, y], B[x + 2, y])).
  let current_state : WState := fun i j =>
    current_state i j ^^^ ((~~~current_state ((i + 1) % 5) j) &&& current_state ((i + 2) % 5) j)
  let row := { row with a_prime_prime := fun y x => u64_to_16_bit_limbs (current_state x y) }
  let row := { row with a_prime_prime_0_0_bits := u64_to_bits_le (current_state 0 0) }
  -- A''[0, 0] is additionally xored with RC.
  let current_state : WState :=
    Function.update current_state 0
      (Function.update (current_state 0) 0 (current_state 0 0 ^^^ BitVec.ofNat 64 (RC.getD round 0)))
  let row := { row with a_prime_prime_prime_0_0_limbs := u64_to_16_bit_limbs (current_state 0 0) }
  (row, current_state)

/-- Fill the `len` rows of one permutation from zeroed rows: rows past 24 are never asked for. -/
def generate_trace_rows_for_perm (len : ℕ) (input : List Word) : List (KeccakCols F) :=
  -- The input lane x + 5 y is lane (x, y) of the state.
  let current_state : WState := fun x y => input.getD (5 * y + x) 0
  -- The initial state is stored y first, for the preimage columns.
  let initial_state : ℕ → ℕ → ℕ → F := fun y x => u64_to_16_bit_limbs (current_state x y)
  let row0 : KeccakCols F := { KeccakCols.zero with a := initial_state, preimage := initial_state }
  let (row0, current_state) := generate_trace_row_for_round row0 0 current_state
  let (rows, _) := (List.range' 1 (len - 1)).foldl (fun (acc : List (KeccakCols F) × WState) round =>
    let (rows, current_state) := acc
    let prev := rows.getLast?.getD KeccakCols.zero
    -- Copy the previous row's output to this row's input.
    let row : KeccakCols F :=
      { KeccakCols.zero with
        preimage := initial_state
        a := fun y x limb => prev.a_prime_prime_prime' y x limb }
    let (row, current_state) := generate_trace_row_for_round row round current_state
    (rows ++ [row], current_state)) ([row0], current_state)
  rows

/-- The trace of the given permutations, padded to a power-of-two height with the permutation of the zero state. -/
def generate_trace_rows (inputs : List (List Word)) (_extra_capacity_bits : ℕ) : Mat F :=
  let num_rows := (inputs.length * NUM_ROUNDS).nextPowerOfTwo
  let real_rows := inputs.flatMap fun input => generate_trace_rows_for_perm NUM_ROUNDS input
  let padding_len := num_rows - inputs.length * NUM_ROUNDS
  -- Every padding chunk is a prefix of the zero state's 24 rows.
  let zero_block : List (KeccakCols F) := generate_trace_rows_for_perm NUM_ROUNDS (List.replicate 25 0)
  let padding_rows := (List.range padding_len).map fun j => zero_block.getD (j % NUM_ROUNDS) KeccakCols.zero
  ⟨NUM_KECCAK_COLS, (real_rows ++ padding_rows).flatMap KeccakCols.cells⟩

end p3_keccak_air.mirror
