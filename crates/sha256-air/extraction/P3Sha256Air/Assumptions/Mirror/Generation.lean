/-
Transcriptions of the trace generator of the SHA-256 AIR over a prime field.

These do not extract: they are generic over the field traits, which aeneas rejects, and they reinterpret rows through `align_to`.

Each definition transcribes one Rust item, named in the crate's mirror entries.

What a transcription abstracts:

* the field is a mathlib field F, a `u16` enters it as a natural number, and a `bool` as 0 or 1;
* a `u32` is a 32-bit vector;
* a row is the column struct with one function per field, and the trace's values are the rows' cells in the struct's `repr(C)` order;
* an array that a loop fills at every index is the function of its index, and an array written at one index is updated there;
* the eight working variables of the compression loop are the fields of one record;
* the reserved extra capacity, which does not change the trace, is ignored;
* the parallel iterator is the sequential map it computes;
* a panic is none.

Loops, branches and the order of writes are kept.
-/
module

public import P3Sha256Air.Assumptions.Mirror.Air
public import Batteries.Data.BitVec

@[expose] public section

namespace p3_sha256_air.mirror

open p3_air.air.mirror

/-- A word. -/
abbrev Word := BitVec 32

/-- The packed intermediates of one round, field by field. -/
structure Sha256RoundCols (T : Type) where
  sigma1_e : ℕ → T
  ch : ℕ → T
  tmp1 : ℕ → T
  t1 : ℕ → T
  sigma0_a : ℕ → T
  maj : ℕ → T

/-- A row of the column struct, field by field. -/
structure Sha256Cols (T : Type) where
  h_in : ℕ → ℕ → T
  a_chain : ℕ → ℕ → T
  e_chain : ℕ → ℕ → T
  w : ℕ → ℕ → T
  sched_sigma0 : ℕ → ℕ → T
  sched_sigma1 : ℕ → ℕ → T
  sched_tmp : ℕ → ℕ → T
  rounds : ℕ → Sha256RoundCols T
  h_out : ℕ → ℕ → T

namespace Sha256Cols

variable {T : Type}

/-- The zero row, as the generator's buffer starts. -/
def zero [Zero T] : Sha256Cols T :=
  ⟨fun _ _ => 0, fun _ _ => 0, fun _ _ => 0, fun _ _ => 0, fun _ _ => 0, fun _ _ => 0, fun _ _ => 0,
    fun _ => ⟨fun _ => 0, fun _ => 0, fun _ => 0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun _ _ => 0⟩

/-- The cells of an array of `n` arrays of `m` cells, entry by entry. -/
def block (f : ℕ → ℕ → T) (n m : ℕ) : List T := (List.range n).flatMap fun i => (List.range m).map (f i)

/-- The 12 cells of one round, in the struct's order. -/
def roundCells (r : Sha256RoundCols T) : List T :=
  (List.range 2).map r.sigma1_e ++ (List.range 2).map r.ch ++ (List.range 2).map r.tmp1 ++
    (List.range 2).map r.t1 ++ (List.range 2).map r.sigma0_a ++ (List.range 2).map r.maj

/-- The cells of a row, in the struct's `repr(C)` order. -/
def cells (r : Sha256Cols T) : List T :=
  block r.h_in STATE_WORDS U32_LIMBS ++ block r.a_chain CHAIN_LEN WORD_BITS ++
    block r.e_chain CHAIN_LEN WORD_BITS ++ block r.w NUM_COMPRESSION_ROUNDS WORD_BITS ++
    block r.sched_sigma0 SCHEDULE_EXTENSIONS U32_LIMBS ++
    block r.sched_sigma1 SCHEDULE_EXTENSIONS U32_LIMBS ++
    block r.sched_tmp SCHEDULE_EXTENSIONS U32_LIMBS ++
    (List.range NUM_COMPRESSION_ROUNDS).flatMap (fun t => roundCells (r.rounds t)) ++
    block r.h_out STATE_WORDS WORD_BITS

end Sha256Cols

variable {F : Type} [Field F]

/-- The bits of a word, least significant first: bit i is `val & (1 << i) != 0`. -/
def u32_to_bits_le (val : Word) : ℕ → F := fun i =>
  if val &&& (1#32 <<< i) ≠ 0 then 1 else 0

/-- The two 16-bit limbs of a word: `value as u16` and `(value >> 16) as u16`. -/
def u32_to_limbs (value : Word) : ℕ → ℕ := fun limb =>
  if limb = 0 then value.toNat % 2 ^ 16 else (value >>> BITS_PER_LIMB).toNat % 2 ^ 16

/-- A word's limbs in the field. -/
def limbsF (value : Word) : ℕ → F := fun limb => ((u32_to_limbs value limb : ℕ) : F)

/-- The eight working variables of the compression loop. -/
structure WorkVars where
  a : Word
  b : Word
  c : Word
  d : Word
  e : Word
  f : Word
  g : Word
  h : Word

/-- Fill a row from one input: the block, then the chaining value. -/
def generate_trace_row_for_compression (row : Sha256Cols F) (input : List Word) : Sha256Cols F :=
  -- Step 1: the block and the chaining value.
  let block : ℕ → Word := fun i => input.getD i 0
  let h_in : ℕ → Word := fun i => input.getD (BLOCK_WORDS + i) 0
  let row := { row with h_in := fun i => limbsF (h_in i) }
  -- Step 2: the message schedule.
  let w_words : ℕ → Word := fun t => if t < BLOCK_WORDS then block t else 0
  let row := { row with w := fun t => if t < BLOCK_WORDS then u32_to_bits_le (block t) else row.w t }
  let (row, w_words) := (List.range' BLOCK_WORDS SCHEDULE_EXTENSIONS).foldl
    (fun (acc : Sha256Cols F × (ℕ → Word)) t =>
      let (row, w_words) := acc
      let i := t - BLOCK_WORDS
      let w_m15 := w_words (t - 15)
      let w_m2 := w_words (t - 2)
      let w_m7 := w_words (t - 7)
      let w_m16 := w_words (t - 16)
      let s0 := w_m15.rotateRight 7 ^^^ w_m15.rotateRight 18 ^^^ w_m15 >>> 3
      let s1 := w_m2.rotateRight 17 ^^^ w_m2.rotateRight 19 ^^^ w_m2 >>> 10
      let tmp := s1 + w_m7
      let w_t := tmp + s0 + w_m16
      let w_words := Function.update w_words t w_t
      let row := { row with
        w := Function.update row.w t (u32_to_bits_le w_t)
        sched_sigma0 := Function.update row.sched_sigma0 i (limbsF s0)
        sched_sigma1 := Function.update row.sched_sigma1 i (limbsF s1)
        sched_tmp := Function.update row.sched_tmp i (limbsF tmp) }
      (row, w_words)) (row, w_words)
  -- Step 3: the compression loop, from the chain prefixes.
  let row := { row with
    a_chain := fun k => if k = 0 then u32_to_bits_le (h_in 3) else if k = 1 then u32_to_bits_le (h_in 2)
      else if k = 2 then u32_to_bits_le (h_in 1) else if k = 3 then u32_to_bits_le (h_in 0)
      else row.a_chain k
    e_chain := fun k => if k = 0 then u32_to_bits_le (h_in 7) else if k = 1 then u32_to_bits_le (h_in 6)
      else if k = 2 then u32_to_bits_le (h_in 5) else if k = 3 then u32_to_bits_le (h_in 4)
      else row.e_chain k }
  let v : WorkVars := ⟨h_in 0, h_in 1, h_in 2, h_in 3, h_in 4, h_in 5, h_in 6, h_in 7⟩
  let (row, v) := (List.range NUM_COMPRESSION_ROUNDS).foldl
    (fun (acc : Sha256Cols F × WorkVars) t =>
      let (row, v) := acc
      let sigma1_e := v.e.rotateRight 6 ^^^ v.e.rotateRight 11 ^^^ v.e.rotateRight 25
      let ch := (v.e &&& v.f) ^^^ (~~~v.e &&& v.g)
      let tmp1 := v.h + sigma1_e + ch
      let t1 := tmp1 + BitVec.ofNat 32 (kOf t) + w_words t
      let sigma0_a := v.a.rotateRight 2 ^^^ v.a.rotateRight 13 ^^^ v.a.rotateRight 22
      let maj := (v.a &&& v.b) ^^^ (v.a &&& v.c) ^^^ (v.b &&& v.c)
      let new_a := t1 + sigma0_a + maj
      let new_e := v.d + t1
      let round : Sha256RoundCols F :=
        ⟨limbsF sigma1_e, limbsF ch, limbsF tmp1, limbsF t1, limbsF sigma0_a, limbsF maj⟩
      let row := { row with
        rounds := Function.update row.rounds t round
        a_chain := Function.update row.a_chain (t + 4) (u32_to_bits_le new_a)
        e_chain := Function.update row.e_chain (t + 4) (u32_to_bits_le new_e) }
      (row, ⟨new_a, v.a, v.b, v.c, new_e, v.e, v.f, v.g⟩)) (row, v)
  -- Step 4: the output, H[i] plus the final working variable i.
  let final_state : ℕ → Word := fun i =>
    match i with
    | 0 => v.a | 1 => v.b | 2 => v.c | 3 => v.d | 4 => v.e | 5 => v.f | 6 => v.g | _ => v.h
  { row with h_out := fun i => u32_to_bits_le (h_in i + final_state i) }

/-- The trace of the given inputs, one compression per row.

It panics when the number of inputs is not a power of two. -/
def generate_trace_rows (inputs : List (List Word)) (_extra_capacity_bits : ℕ) : Option (Mat F) :=
  if ¬ (inputs.length ≠ 0 ∧ 2 ^ Nat.log 2 inputs.length = inputs.length) then none
  else
    let rows := inputs.map (generate_trace_row_for_compression Sha256Cols.zero)
    some ⟨NUM_SHA256_COLS, rows.flatMap Sha256Cols.cells⟩

end p3_sha256_air.mirror
