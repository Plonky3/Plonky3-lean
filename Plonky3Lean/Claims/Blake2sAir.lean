module

public import Plonky3Lean.Proofs.Blake2sAir.Trace
public import Plonky3Lean.Proofs.Blake2sAir.Degree
public import Plonky3Lean.Proofs.Blake2sAir.Extracted
public import Plonky3Lean.Proofs.Blake2sAir.Packed
public import Plonky3Lean.Proofs.Hash.Blake2s.Vectors

@[expose] public section

/-!
# p3-blake2s-air: claims

# Overview

These claims hold at the Plonky3 commit pinned in `plonky3/`.

The constants, the G step on words and the carry word are extracted.

The AIR evaluation, the trace generator and the output read-back are transcriptions.

The evaluation is parametric, so it is an AIR of the p3-air model.

A trace satisfies the AIR when every constraint polynomial vanishes on every row.

The specification is RFC 7693, in `Plonky3Lean.Spec.Blake2s`.

It reproduces the RFC's test vectors:

- the digest of "abc", and its working vector after every round
- the self-test of appendix E

# The AIR

A row holds one compression, all as bits:

- the chaining value, the message block, the counter and the final-block flag
- for each of the 80 G steps, the carries of its two stored additions
- for each G step, the words `d_1`, `b_1`, `d_2`, `b_2`.

```text
    cells 0 .. 833       inputs: 8 + 16 + 2 words of 32 bits, and 1 flag
    cells 833 .. 16033   80 G steps of 190 cells
```

The additions are ripple-carry adders whose sums are XORs, valid in characteristic 2 only.

- On a row whose input cells are bits, the output read back is the RFC 7693 compression of the inputs.
- With the booleanity stated, the input cells are bits by the constraints.
- No intermediate needs a range check: every cell is forced to a bit.
- The evaluation does not check the characteristic.
- The generator does.
- On a positive power-of-two number of inputs, the generator's trace satisfies the AIR in characteristic 2.
- The generator panics otherwise.
- Every constraint has degree multiple at most 2, the declared bound.
-/

open Aeneas Aeneas.Std
open p3_air.symbolic.mirror p3_air.air.mirror p3_blake2s_air.mirror Plonky3Lean.Spec.Air
open Plonky3Lean.Proofs.Air Plonky3Lean.Proofs.Blake2sAir

namespace Plonky3Lean.Claims.Blake2sAir

/-! ## The specification and the RFC's test vectors -/

/-- The specification gives the digest of "abc" printed in RFC 7693, appendix B. -/
theorem spec.hash_abc : Plonky3Lean.Spec.Blake2s.hash [] Proofs.Blake2s.abc 32 = Proofs.Blake2s.bytes
    [0x50, 0x8C, 0x5E, 0x8C, 0x32, 0x7C, 0x14, 0xE2, 0xE1, 0xA7, 0x2B, 0xA3, 0x4E, 0xEB, 0x45, 0x2F,
     0x37, 0x45, 0x8B, 0x20, 0x9E, 0xD6, 0x3A, 0x29, 0x4D, 0x99, 0x9B, 0x4C, 0x86, 0x67, 0x59, 0x82] :=
  Proofs.Blake2s.hash_abc

/-- The specification gives the working vector of appendix B after the last round. -/
theorem spec.rounds_abc :
    Plonky3Lean.Spec.Blake2s.rounds (Plonky3Lean.Spec.Blake2s.blockWords Proofs.Blake2s.abc)
      (Plonky3Lean.Spec.Blake2s.init Proofs.Blake2s.abcH 3 true) 10 =
    [0xD9C994AA, 0xCFEC3AA6, 0x700D0AB2, 0x2C38670E, 0xAF6A1F66, 0x1D023EF3, 0x1D9EC27D,
      0x945357A5, 0x3E9FFEBD, 0x969FE811, 0xEF485E21, 0xA632797A, 0xDEEF082E, 0xAF3D80E1,
      0x4E86829B, 0x4DEAFD3A] :=
  Proofs.Blake2s.rounds_abc_10

/-- The specification passes the self-test of RFC 7693, appendix E. -/
theorem spec.selftest : Plonky3Lean.Spec.Blake2s.hash [] Proofs.Blake2s.selftestDigests 32 =
    Proofs.Blake2s.bytes
    [0x6A, 0x41, 0x1F, 0x08, 0xCE, 0x25, 0xAD, 0xCD, 0xFB, 0x02, 0xAB, 0xA6, 0x41, 0x45, 0x1C, 0xEC,
     0x53, 0xC5, 0x98, 0xB2, 0x4F, 0x4F, 0xC7, 0x87, 0xFB, 0xDC, 0x88, 0x79, 0x7F, 0x4C, 0x1D, 0xFE] :=
  Proofs.Blake2s.selftest

/-! ## Constants and extracted code -/

/-- The extracted initialization vector is the transcribed one, and that of RFC 7693, section 2.6. -/
theorem constants.IV.eq_rfc :
    p3_blake2s_air.constants.IV.val.map UScalar.bv = p3_blake2s_air.mirror.IV ∧
      p3_blake2s_air.constants.IV.val.map UScalar.bv = Plonky3Lean.Spec.Blake2s.IV :=
  ⟨IV_extracted, IV_rfc⟩

/-- The extracted message schedule is the transcribed one, and that of RFC 7693, section 2.7. -/
theorem constants.SIGMA.eq_rfc :
    p3_blake2s_air.constants.SIGMA.val.map (fun row => row.val.map (·.val)) = p3_blake2s_air.mirror.SIGMA ∧
      p3_blake2s_air.constants.SIGMA.val.map (fun row => row.val.map (·.val)) =
        Plonky3Lean.Spec.Blake2s.SIGMA :=
  ⟨SIGMA_extracted, SIGMA_rfc⟩

/-- The extracted schedule of G positions never panics, and is the transcribed one. -/
theorem binary.G_SCHEDULE.eq : ∃ s, p3_blake2s_air.binary.G_SCHEDULE = .ok s ∧
    s.val.map (fun row => row.val.map (·.val)) = p3_blake2s_air.mirror.G_SCHEDULE :=
  G_SCHEDULE_extracted

/-- Round `r` of RFC 7693 is the eight G steps at the positions of the transcribed schedule. -/
theorem binary.G_SCHEDULE.eq_rfc (m v : List (BitVec 32)) {r : ℕ} (hr : r < 10) :
    Plonky3Lean.Spec.Blake2s.round m v r = (List.range 8).foldl (gStep m r) v :=
  round_eq m v hr

/-- The extracted carry word never panics, and is `(sum ^ x ^ y) >> 1`. -/
theorem binary.generation.carries_word.eq (x y s : Std.U32) :
    p3_blake2s_air.binary.generation.carries_word x y s = .ok ⟨(s.bv ^^^ x.bv ^^^ y.bv) >>> 1⟩ :=
  carries_word_eq x y s

/-- With every position below 4, the extracted G step on words never panics.

It returns the words and the state of the transcription. -/
theorem binary.generation.g_words.spec (state : Std.Array (Std.Array Std.U32 4#usize) 4#usize)
    (a : Std.Array Std.Usize 4#usize) (mx my : Std.U32) (ha : ∀ j < 4, (a.val[j]!).val < 4) :
    ∃ r, p3_blake2s_air.binary.generation.g_words state a mx my = .ok r ∧
      let m := p3_blake2s_air.mirror.g_words (cellOf state) (a.val.map (·.val)) mx.bv my.bv
      (r.1.add1_carries.bv = m.1.add1_carries ∧ r.1.d1.bv = m.1.d1 ∧ r.1.b1.bv = m.1.b1 ∧
        r.1.add2_carries.bv = m.1.add2_carries ∧ r.1.d2.bv = m.1.d2 ∧ r.1.b2.bv = m.1.b2) ∧
      ∀ row < 4, ∀ i < 4, cellOf r.2 row i = m.2 row i :=
  g_words_extracted state a mx my ha

/-- The extracted G step on words panics when a position is not below 4. -/
theorem binary.generation.g_words.panics (state : Std.Array (Std.Array Std.U32 4#usize) 4#usize)
    (a : Std.Array Std.Usize 4#usize) (mx my : Std.U32) (ha : ∃ j < 4, 4 ≤ (a.val[j]!).val) :
    p3_blake2s_air.binary.generation.g_words state a mx my = .fail .panic :=
  g_words_panics state a mx my ha

/-- On a state holding a working vector, the transcribed G step computes G of RFC 7693, section 3.1.

It returns the witness words of G, and moves the state as G moves the vector. -/
theorem binary.generation.g_words.eq_rfc {st : ℕ → ℕ → BitVec 32} {v : List (BitVec 32)} (hs : GS st v)
    {slots : List ℕ} (hsl : ∀ j < 4, slots.getD j 0 < 4) (X Y : BitVec 32) :
    (g_words st slots X Y).1 = gwOf v slots X Y ∧
      GS (g_words st slots X Y).2 (Plonky3Lean.Spec.Blake2s.G v (slots.getD 0 0) (4 + slots.getD 1 0)
        (8 + slots.getD 2 0) (12 + slots.getD 3 0) X Y) :=
  g_words_spec hs hsl X Y

/-! ## The packed generator's helpers

The packed generator holds a word of 64 trace rows as 32 planes of 64 bits.

Bit `k` of plane `i` is bit `i` of the word of lane `k`. -/

/-- The extracted adder on planes never panics.

In every lane, it returns the sum of the two words modulo `2^32`.

It also returns the ripple carries into bits 1 to 31, in place of the carry planes it is given. -/
theorem binary.generation.add_planes.spec (x y : Std.Array Std.U64 32#usize) (c : Std.Array Std.U64 31#usize) :
    ∃ sum c', p3_blake2s_air.binary.generation.add_planes x y c = .ok (sum, c') ∧
      (∀ k, laneWord sum k = laneWord x k + laneWord y k) ∧
      ∀ k, ∀ i < 31, (c'.val[i]!).bv.getLsbD k = BitVec.carry (i + 1) (laneWord x k) (laneWord y k) false :=
  add_planes_spec x y c

/-- The extracted rotation on planes never panics for an amount below 32.

In every lane, it returns `(x ^ y) >>> amount`. -/
theorem binary.generation.xor_rotate_right.spec (x y : Std.Array Std.U64 32#usize) (amount : Std.Usize)
    (ha : amount.val < 32) :
    ∃ out, p3_blake2s_air.binary.generation.xor_rotate_right x y amount = .ok out ∧
      ∀ k, laneWord out k = (laneWord x k ^^^ laneWord y k).rotateRight amount.val :=
  xor_rotate_right_spec x y amount ha

/-! ## Soundness -/

variable {F : Type} [Field F] [DecidableEq F]

/-- Soundness: take a row of a trace that satisfies the AIR in characteristic 2, with its input cells bits.

The output read back never panics, and is the RFC 7693 compression.

The compression is of the chaining value, block, counter and flag that the row's input cells hold.

The input cells are bits when the booleanity is stated. -/
theorem sound (h2 : (2 : F) = 0) {cb : Bool} {T : Instance F}
    (hT : Satisfies (constraints (blake2sAir cb)) T) {i : ℕ} (hi : i < T.height)
    (hb : cb = true ∨ BoolOk (fun c => (rowCells T i).getD c 0)) :
    compression_output (Blake2sBinaryCols.ofCells (rowCells T i)) =
      some (Plonky3Lean.Spec.Blake2s.compress (cvOf (fun c => (rowCells T i).getD c 0))
        (blockOf (fun c => (rowCells T i).getD c 0)) (counterOf (fun c => (rowCells T i).getD c 0))
        (flagOf (fun c => (rowCells T i).getD c 0))) :=
  Proofs.Blake2sAir.sound h2 hT hi hb

/-- On a row of input bits, the input cells are the bits of the words the soundness theorem names:

- the chaining value
- the message block
- the low and the high word of the counter
- the final-block flag. -/
theorem sound.inputs {loc : ℕ → F} (hb : BoolOk loc) :
    (∀ i < 8, ∀ b < 32, loc (col.chaining_value i b) =
      Plonky3Lean.Proofs.KeccakAir.bitF (((cvOf loc).getD i 0).getLsbD b)) ∧
    (∀ k < 16, ∀ b < 32, loc (col.block k b) =
      Plonky3Lean.Proofs.KeccakAir.bitF (((blockOf loc).getD k 0).getLsbD b)) ∧
    (∀ b < 32, loc (col.counter_low b) =
      Plonky3Lean.Proofs.KeccakAir.bitF ((BitVec.ofNat 32 (counterOf loc)).getLsbD b)) ∧
    (∀ b < 32, loc (col.counter_high b) =
      Plonky3Lean.Proofs.KeccakAir.bitF ((BitVec.ofNat 32 (counterOf loc / 2 ^ 32)).getLsbD b)) ∧
    loc col.last_block = Plonky3Lean.Proofs.KeccakAir.bitF (flagOf loc) :=
  inputs_hold hb

/-- Soundness of one row, on its working state: after ten rounds it holds the RFC 7693 working vector. -/
theorem row_sound (h2 : (2 : F) = 0) {cb : Bool} {env : Var → F} {L : AirLayout}
    (h : eval cb (Plonky3Lean.Proofs.KeccakAir.propBuilder env L) True)
    (hb : cb = true ∨ BoolOk (Plonky3Lean.Proofs.KeccakAir.rowOf env L 0)) :
    BoolOk (Plonky3Lean.Proofs.KeccakAir.rowOf env L 0) ∧
      StateHolds (finalState (Plonky3Lean.Proofs.KeccakAir.rowOf env L 0))
        (Plonky3Lean.Spec.Blake2s.rounds (blockOf (Plonky3Lean.Proofs.KeccakAir.rowOf env L 0))
          (Plonky3Lean.Spec.Blake2s.init (cvOf (Plonky3Lean.Proofs.KeccakAir.rowOf env L 0))
            (counterOf (Plonky3Lean.Proofs.KeccakAir.rowOf env L 0))
            (flagOf (Plonky3Lean.Proofs.KeccakAir.rowOf env L 0))) 10) :=
  Proofs.Blake2sAir.row_sound h2 h hb

/-! ## Completeness and panics -/

/-- Completeness: in characteristic 2, the generator's trace satisfies the AIR.

The number of inputs must be a positive power of two.

This holds with or without the booleanity. -/
theorem complete [Inhabited F] (h2 : (2 : F) = 0) (cb : Bool) {inputs : List Blake2sCompressionInput}
    (h : inputs.length ≠ 0 ∧ 2 ^ Nat.log 2 inputs.length = inputs.length) (e : ℕ) :
    ∃ M, generate_binary_trace_rows (F := F) inputs e = some M ∧
      Satisfies (constraints (blake2sAir cb)) (instOf (blake2sAir cb) M []) :=
  Proofs.Blake2sAir.complete h2 cb h e

/-- The debug checker accepts the generator's trace, in characteristic 2. -/
theorem check_complete [Inhabited F] (h2 : (2 : F) = 0) (cb : Bool) {inputs : List Blake2sCompressionInput}
    (h : inputs.length ≠ 0 ∧ 2 ^ Nat.log 2 inputs.length = inputs.length) (e : ℕ) :
    ∃ M, generate_binary_trace_rows (F := F) inputs e = some M ∧
      check_constraints (blake2sAir cb) M [] = .ok () :=
  Proofs.Blake2sAir.check_complete h2 cb h e

/-- The generator panics unless 2 is 0 in the field and the number of inputs is a positive power of two. -/
theorem generate_binary_trace_rows.panics {inputs : List Blake2sCompressionInput}
    (h : ¬ ((2 : F) = 0 ∧ inputs.length ≠ 0 ∧ 2 ^ Nat.log 2 inputs.length = inputs.length)) (e : ℕ) :
    generate_binary_trace_rows (F := F) inputs e = none := by
  simp only [generate_eq, h, ↓reduceIte]

/-- In characteristic 2, the output read back from a generated row is the RFC 7693 compression of the input. -/
theorem generate_trace_row.output (h2 : (2 : F) = 0) (input : Blake2sCompressionInput) :
    compression_output (Blake2sBinaryCols.ofCells
        (generate_trace_row (Blake2sBinaryCols.zero : Blake2sBinaryCols F) input).cells) =
      some (Plonky3Lean.Spec.Blake2s.compress (cvIn input) (blockIn input) input.counter.toNat
        input.last_block) :=
  gen_output h2 input

/-- Reading a word back panics exactly when one of its 32 cells is neither 0 nor 1. -/
theorem read_word.panics (bits : ℕ → F) :
    read_word bits = none ↔ ∃ b < 32, bits b ≠ 0 ∧ bits b ≠ 1 :=
  read_word_none bits

/-- Reading the state back panics when the round is not below ten. -/
theorem state_after_round.panics (r : Blake2sBinaryCols F) {round : ℕ} (h : 10 ≤ round) :
    state_after_round r round = none :=
  state_after_round_none r h

/-! ## Constraint degrees and count -/

/-- Over GF(2), every symbolic constraint has degree multiple at most 2, the declared bound.

No constraint reads a transition selector. -/
theorem degree_gf2 (cb : Bool) :
    ∀ e ∈ (blake2sAir (F := ZMod 2) cb).eval
        (symbolicBuilder (AirLayout.from_air (blake2sAir (F := ZMod 2) cb))) [],
      e.degree_multiple ≤ 2 ∧ transitionCount e = 0 :=
  constraints_bounded (top_gf2 cb)

/-- Over GF(2), the AIR asserts exactly the number of constraints it reports, with or without the booleanity. -/
theorem num_constraints_gf2 (cb : Bool) :
    some ((blake2sAir (F := ZMod 2) cb).eval
        (symbolicBuilder (AirLayout.from_air (blake2sAir (F := ZMod 2) cb))) []).length =
      num_constraints cb :=
  num_constraints_eq cb

end Plonky3Lean.Claims.Blake2sAir
