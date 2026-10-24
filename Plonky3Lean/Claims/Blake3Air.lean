module

public import Plonky3Lean.Proofs.Blake3Air.Fields
public import Plonky3Lean.Proofs.Blake3Air.Small
public import Plonky3Lean.Proofs.Blake3Air.Complete
public import Plonky3Lean.Proofs.Blake3Air.Extracted
public import Plonky3Lean.Proofs.Blake3Air.Binary.Complete

@[expose] public section

/-!
# p3-blake3-air: claims

# Overview

These claims hold at the Plonky3 commit pinned in `plonky3/`.

The constants, the generator's half quarter round and the characteristic-2 carry word are extracted.

The two AIR evaluations, the two trace generators and the output reader are transcriptions.

Each transcription has a mirror entry.

Each evaluation is parametric, so it is an AIR of the p3-air model.

A trace satisfies an AIR when every constraint polynomial vanishes on every row.

The specification is the BLAKE3 compression function of the BLAKE3 paper, section 2.2.

It lives in `Plonky3Lean.Spec.Blake3`.

# The AIR over a prime field

A row holds one compression.

```text
    input bits      block, chaining value, counter halves, block length, flags
    7 rounds        4 states per round: rows 0 and 2 as 16-bit limbs, rows 1 and 3 as bits
    output bits     the 16 output words
```

- Soundness needs a characteristic above 3 * 2^16.
- On every row of a satisfying trace, the output cells hold the bits of a compression.
- That compression is of the words the input cells hold.
- Over fields of 65537 and 131071 elements, the addition constraints accept wrong sums.
- The generator's trace satisfies the AIR in every field, and the debug checker accepts it.
- Row k of the generator's trace compresses input k with counter k and no flags.
- Its block length is the number of rows, not the length of a block.
- Every constraint has degree multiple at most 3 and reads no selector, so it fits the quotient's 2 chunks.

# The AIR over a field of characteristic 2

A row holds one compression: the input bits, then the carries and four words of each of the 56 G steps.

- When the input cells are bits, the reader returns the compression of the row's inputs.
- The input cells are bits when the AIR states their booleanity, or when the commitment holds only bits.
- The generator succeeds on 2^k inputs, and its trace satisfies the AIR with or without the booleanity.
- Every constraint has degree multiple at most 2 and reads no selector, so it fits a single quotient chunk.
- The AIR asserts exactly the number of constraints it reports.
-/

open Plonky3Lean.Spec.Air Plonky3Lean.Proofs.Air Plonky3Lean.Proofs.KeccakAir Plonky3Lean.Proofs.Blake3Air
open p3_air.air.mirror p3_air.symbolic.mirror p3_blake3_air.mirror

namespace Plonky3Lean.Claims.Blake3Air

variable {F : Type} [Field F] [DecidableEq F]

/-! ## Soundness over a prime field -/

/-- Soundness on every row of a satisfying trace.

- The input cells hold the bits of a block, a chaining value, the counter halves, a block length and flags.
- The output cells hold the bits of their compression. -/
theorem sound (hp : 3 * 2 ^ 16 < ringChar F) {T : Instance F} (hT : Satisfies (constraints blake3Air) T)
    {i : ℕ} (hi : i < T.height) :
    (∀ j < 16, BitsRep (fun k => T.main i (col.inputs j k)) ((blockOf (T.main i)).getD j 0)) ∧
    (∀ hh < 2, ∀ j < 4, BitsRep (fun k => T.main i (col.chaining_values hh j k))
      ((cvOf (T.main i)).getD (4 * hh + j) 0)) ∧
    (∀ j < 4, BitsRep (fun k => T.main i (col.counter_low (32 * j + k))) (row3Of (T.main i) j)) ∧
    ∀ q < 4, ∀ j < 4, BitsRep (fun k => T.main i (col.outputs q j k))
      ((Plonky3Lean.Spec.Blake3.compress (cvOf (T.main i)) (blockOf (T.main i))
        ((row3Of (T.main i) 0).toNat + 2 ^ 32 * (row3Of (T.main i) 1).toNat) (row3Of (T.main i) 2)
        (row3Of (T.main i) 3)).getD (4 * q + j) 0) :=
  trace_sound hp hT hi

/-- BabyBear, KoalaBear, Goldilocks and Mersenne31 have characteristic above 3 * 2^16, as soundness needs. -/
theorem ringChar_fields : 3 * 2 ^ 16 < ringChar BabyBear.Field ∧ 3 * 2 ^ 16 < ringChar KoalaBear.Field ∧
    3 * 2 ^ 16 < ringChar Goldilocks.Field ∧ 3 * 2 ^ 16 < ringChar Mersenne31.Field :=
  ⟨ringChar_babyBear, ringChar_koalaBear, ringChar_goldilocks, ringChar_mersenne31⟩

/-- Over a field of 65537 elements, the two-operand addition constraints accept 2^16 + 1 = 0 + 0. -/
theorem add2_small_field :
    Add2C (F := ZMod 65537) (fun _ => 1) (fun _ => 0) (fun _ => 0) ∧ (1 + 2 ^ 16 * 1) % 2 ^ 32 ≠ (0 + 0 : ℕ) :=
  add2C_accepts_wrong_sum

/-- Over a field of 131071 elements, the three-operand addition constraints accept 0 = 65535 + 65535 + 1. -/
theorem add3_small_field :
    Add3C (F := ZMod 131071) (fun _ => 0) (fun l => if l = 0 then 65535 else 0)
        (fun l => if l = 0 then 65535 else 0) (fun l => if l = 0 then 1 else 0) ∧
      (0 : ℕ) ≠ (65535 + 65535 + 1) % 2 ^ 32 :=
  add3C_accepts_wrong_sum

/-! ## Completeness over any field -/

/-- The generator succeeds on any list of 2^k inputs. -/
theorem generate_some (inputs : List (ℕ → Word)) (e : ℕ) {k : ℕ} (hk : inputs.length = 2 ^ k) :
    generate_trace_rows (F := F) inputs e = some (matOf (genRows inputs)) :=
  Proofs.Blake3Air.generate_some inputs e hk

/-- Completeness: whenever the generator returns a trace, it satisfies the AIR, in every field. -/
theorem complete [Inhabited F] (inputs : List (ℕ → Word)) (e : ℕ) {M : Mat F}
    (hM : generate_trace_rows (F := F) inputs e = some M) :
    Satisfies (constraints blake3Air) (instOf blake3Air M []) :=
  Proofs.Blake3Air.complete inputs e hM

/-- The debug checker accepts the generator's trace. -/
theorem check_complete [Inhabited F] (inputs : List (ℕ → Word)) (e : ℕ) {M : Mat F}
    (hM : generate_trace_rows (F := F) inputs e = some M) : check_constraints blake3Air M [] = .ok () :=
  Proofs.Blake3Air.check_complete inputs e hM

/-- Row k of the generator's trace compresses input k with counter k and no flags.

Its block length is the number of rows. -/
theorem generated_outputs (hp : 3 * 2 ^ 16 < ringChar F) [Inhabited F] (inputs : List (ℕ → Word)) (e : ℕ)
    {M : Mat F} (hM : generate_trace_rows (F := F) inputs e = some M) {k : ℕ} (hk : k < inputs.length) :
    ∀ q < 4, ∀ j < 4, BitsRep (fun b => (instOf blake3Air M []).main k (col.outputs q j b))
      ((Plonky3Lean.Spec.Blake3.compress ((List.range 8).map fun i => (inputs.getD k fun _ => 0) (16 + i))
        ((List.range 16).map (inputs.getD k fun _ => 0)) k (BitVec.ofNat 32 inputs.length) 0).getD
        (4 * q + j) 0) :=
  Proofs.Blake3Air.generated_outputs hp inputs e hM hk

/-! ## Constraint degrees and the quotient -/

/-- Over BabyBear, every symbolic constraint has degree multiple at most 3 and reads no selector. -/
theorem degree_babyBear :
    ∀ e ∈ (blake3Air (F := BabyBear.Field)).eval
        (symbolicBuilder (AirLayout.from_air (blake3Air (F := BabyBear.Field)))) [],
      e.degree_multiple ≤ 3 ∧ transitionCount e = 0 :=
  bounded_of_topD 3 _ top_babyBear

/-- Over KoalaBear, the same bounds hold. -/
theorem degree_koalaBear :
    ∀ e ∈ (blake3Air (F := KoalaBear.Field)).eval
        (symbolicBuilder (AirLayout.from_air (blake3Air (F := KoalaBear.Field)))) [],
      e.degree_multiple ≤ 3 ∧ transitionCount e = 0 :=
  bounded_of_topD 3 _ top_koalaBear

/-- Over Goldilocks, the same bounds hold. -/
theorem degree_goldilocks :
    ∀ e ∈ (blake3Air (F := Goldilocks.Field)).eval
        (symbolicBuilder (AirLayout.from_air (blake3Air (F := Goldilocks.Field)))) [],
      e.degree_multiple ≤ 3 ∧ transitionCount e = 0 :=
  bounded_of_topD 3 _ top_goldilocks

/-- Over Mersenne31, the same bounds hold. -/
theorem degree_mersenne31 :
    ∀ e ∈ (blake3Air (F := Mersenne31.Field)).eval
        (symbolicBuilder (AirLayout.from_air (blake3Air (F := Mersenne31.Field)))) [],
      e.degree_multiple ≤ 3 ∧ transitionCount e = 0 :=
  bounded_of_topD 3 _ top_mersenne31

/-- Over BabyBear, the quotient sizing gives 2 chunks.

Every constraint polynomial fits them, for degree bounds of a trace of n rows. -/
theorem quotient_fits_babyBear {n : ℕ} (hn : 1 ≤ n) {σ : Var → Polynomial BabyBear.Field}
    {periods : List ℕ} (hσ : DegreeBounds σ n periods)
    (hp : ∀ j p : ℕ, periods[j]? = some p → 0 < p → p < n → p ∣ n) :
    get_log_quotient_degree (blake3Air (F := BabyBear.Field))
        (AirLayout.from_air (blake3Air (F := BabyBear.Field))) n 0 = .ok 1 ∧
      ∀ e ∈ (blake3Air (F := BabyBear.Field)).eval
          (symbolicBuilder (AirLayout.from_air (blake3Air (F := BabyBear.Field)))) [],
        FitsChunks n (2 ^ 1) (constraintPoly σ (toPoly e)) :=
  quotient_fits_of_bounded (d := 3) rfl degree_babyBear rfl hn hσ hp

/-! ## Extracted code -/

/-- The extracted IV halves and message permutation are the transcribed ones. -/
theorem constants.eq_mirror :
    p3_blake3_air.constants.IV.val.map (fun w => w.val.map (·.val)) = IV ∧
      p3_blake3_air.constants.MSG_PERMUTATION.val.map (·.val) = MSG_PERMUTATION :=
  ⟨IV_eq, MSG_PERMUTATION_eq⟩

/-- The transcribed IV and message permutation are those of the BLAKE3 paper. -/
theorem constants.eq_spec :
    (List.range 8).map (fun i => ivWord i) = Plonky3Lean.Spec.Blake3.IV ∧
      MSG_PERMUTATION = Plonky3Lean.Spec.Blake3.MSG_PERMUTATION := by
  constructor <;> decide

/-- The extracted half quarter round never panics and computes the transcribed one. -/
theorem generation.verifiable_half_round.eq_mirror (a b c d m : Aeneas.Std.U32) (flag : Bool) :
    p3_blake3_air.generation.verifiable_half_round a b c d m flag =
      let r := verifiable_half_round a.bv b.bv c.bv d.bv m.bv flag
      .ok (⟨r.1⟩, ⟨r.2.1⟩, ⟨r.2.2.1⟩, ⟨r.2.2.2⟩) :=
  verifiable_half_round_eq a b c d m flag

/-- The extracted carry word never panics and computes the transcribed one. -/
theorem binary.generation.carries_word.eq_mirror (x y s : Aeneas.Std.U32) :
    p3_blake3_air.binary.generation.carries_word x y s =
      .ok ⟨p3_blake3_air.mirror.binary.carries_word x.bv y.bv s.bv⟩ :=
  carries_word_eq x y s

/-! ## The AIR over a field of characteristic 2 -/

section binary

open Plonky3Lean.Proofs.Blake3Air.Binary p3_blake3_air.mirror.binary

/-- Soundness on a row of a satisfying trace whose input cells are bits.

The reader returns the compression of the row's chaining value, block, counter, block length and flags. -/
theorem binary.sound (h2 : (2 : F) = 0) {cb : Bool} {T : Instance F}
    (hT : Satisfies (constraints (binaryAir cb)) T) {i : ℕ} (hi : i < T.height)
    (hbits : cb = true ∨ InputBits (T.main i)) :
    compression_output (rowCols (T.main i)) = some fun p =>
      (Plonky3Lean.Spec.Blake3.compress (cvB (T.main i)) (blkB (T.main i))
        ((row3B (T.main i) 0).toNat + 2 ^ 32 * (row3B (T.main i) 1).toNat) (row3B (T.main i) 2)
        (row3B (T.main i) 3)).getD p 0 :=
  trace_sound h2 hT hi hbits

/-- Over a field of characteristic 2, the generator succeeds on any list of 2^k inputs. -/
theorem binary.generate_some (h2 : (2 : F) = 0) (inputs : List Blake3CompressionInput) (e : ℕ) {k : ℕ}
    (hk : inputs.length = 2 ^ k) :
    generate_binary_trace_rows (F := F) inputs e = some (matOfB (inputs.map generate_trace_row)) :=
  Proofs.Blake3Air.Binary.generate_some h2 inputs e hk

/-- Completeness: whenever the generator returns a trace, it satisfies the AIR, with or without the booleanity. -/
theorem binary.complete [Inhabited F] (h2 : (2 : F) = 0) (cb : Bool) (inputs : List Blake3CompressionInput)
    (e : ℕ) {M : Mat F} (hM : generate_binary_trace_rows (F := F) inputs e = some M) :
    Satisfies (constraints (binaryAir cb)) (instOf (binaryAir cb) M []) :=
  Proofs.Blake3Air.Binary.complete h2 cb inputs e hM

/-- Over GF(2), every symbolic constraint has degree multiple at most 2, the AIR's hint, and reads no selector. -/
theorem binary.degree_gf2 (cb : Bool) :
    ∀ e ∈ (binaryAir (F := ZMod 2) cb).eval
        (symbolicBuilder (AirLayout.from_air (binaryAir (F := ZMod 2) cb))) [],
      e.degree_multiple ≤ 2 ∧ transitionCount e = 0 :=
  bounded_of_topD 2 _ (top_gf2 cb)

/-- Over GF(2), the quotient sizing gives 1 chunk, and every constraint polynomial fits it. -/
theorem binary.quotient_fits_gf2 (cb : Bool) {n : ℕ} (hn : 1 ≤ n) {σ : Var → Polynomial (ZMod 2)}
    {periods : List ℕ} (hσ : DegreeBounds σ n periods)
    (hp : ∀ j p : ℕ, periods[j]? = some p → 0 < p → p < n → p ∣ n) :
    get_log_quotient_degree (binaryAir (F := ZMod 2) cb)
        (AirLayout.from_air (binaryAir (F := ZMod 2) cb)) n 0 = .ok 0 ∧
      ∀ e ∈ (binaryAir (F := ZMod 2) cb).eval
          (symbolicBuilder (AirLayout.from_air (binaryAir (F := ZMod 2) cb))) [],
        FitsChunks n (2 ^ 0) (constraintPoly σ (toPoly e)) :=
  quotient_fits_of_bounded (d := 2) rfl (binary.degree_gf2 cb) rfl hn hσ hp

/-- The AIR asserts exactly the number of constraints it reports, in every field, with or without the booleanity. -/
theorem binary.num_constraints (cb : Bool) :
    some ((binaryAir (F := F) cb).eval
        (symbolicBuilder (AirLayout.from_air (binaryAir (F := F) cb))) []).length =
      p3_blake3_air.mirror.binary.num_constraints cb :=
  num_constraints_eq cb

end binary

end Plonky3Lean.Claims.Blake3Air
