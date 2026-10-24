module

public import Plonky3Lean.Proofs.Sha256Air.Complete
public import Plonky3Lean.Proofs.Sha256Air.Degree
public import Plonky3Lean.Proofs.Sha256Air.Extracted
public import Plonky3Lean.Proofs.Sha256Air.Binary.Sound

@[expose] public section

/-!
# p3-sha256-air: claims

# Overview

These claims hold at the Plonky3 commit pinned in `plonky3/`.

The constants, the limb split and the sigma functions of the characteristic-2 generator are extracted.

The two AIR evaluations and the two trace generators are transcriptions with mirror entries.

Each evaluation is parametric, so it is an AIR of the p3-air model.

A trace satisfies an AIR when every constraint polynomial vanishes on every row.

The specification is FIPS 180-4, in `Plonky3Lean.Spec.Sha256`.

# The AIR over a prime field

A row holds one compression:

- the input chaining value, as 16-bit limbs
- the schedule and the two working-variable chains, as bits
- the packed round intermediates
- the output, as bits

```text
    a_chain[0..4] = H_3, H_2, H_1, H_0     a_chain[t + 4] = a after round t
    e_chain[0..4] = H_7, H_6, H_5, H_4     e_chain[t + 4] = e after round t
```

- Soundness needs a characteristic above `7 * 2^16`.
- Below that, the debug checker accepts wrong compressions: over the prime 262147, a forged round 63 passes.
- The Rust checks only that 2^16 lies below the characteristic, and panics otherwise.
- The transcription drops that check.
- On a power-of-two number of inputs, the generator's trace satisfies the AIR in every field.
- On any other number, the generator panics.
- Every constraint has degree multiple at most 3, the declared bound.
- So every constraint polynomial fits 2 quotient chunks.

# The AIR over a field of characteristic 2

A row holds, all as bits:

- the input chaining value and block
- the carries of every stored-carry addition
- the output

- On a row whose input cells are bits, the output is the compression of the input.
- With the booleanity stated, the input cells are bits by the constraints.
- Every constraint has degree multiple at most 2.
- The AIR asserts exactly the number of constraints it reports.
-/

open Plonky3Lean.Spec.Air Plonky3Lean.Spec.Sha256 Plonky3Lean.Proofs.Air
open Plonky3Lean.Proofs.Sha256Air p3_air.air.mirror p3_air.symbolic.mirror p3_sha256_air.mirror
open Plonky3Lean.Proofs.KeccakAir (bitF)

namespace Plonky3Lean.Claims.Sha256Air

variable {F : Type} [Field F]

/-! ## Soundness over a prime field -/

/-- Soundness: over a characteristic above 7 * 2^16, each row of a satisfying trace computes one compression.

- the packed input columns hold the limbs of a chaining value H
- the first 16 schedule words hold the bits of a block M
- the output columns hold the bits of the FIPS 180-4 compression of H and M -/
theorem sound [DecidableEq F] (hp : 7 * 2 ^ 16 < ringChar F) {T : Instance F}
    (hT : Satisfies (constraints sha256Air) T) {i : ℕ} (hi : i < T.height) :
    ∃ H M : List (BitVec 32), H.length = 8 ∧ M.length = 16 ∧
      (∀ j < 8, ∀ limb < 2, T.main i (col.h_in j limb) =
        (((H.getD j 0).toNat / 2 ^ (16 * limb) % 2 ^ 16 : ℕ) : F)) ∧
      (∀ t < 16, ∀ b < 32, T.main i (col.w t b) = bitF ((M.getD t 0).getLsbD b)) ∧
      (∀ j < 8, ∀ b < 32, T.main i (col.h_out j b) = bitF (((compress H M).getD j 0).getLsbD b)) := by
  obtain ⟨H, M, h1, h2, h3, h4, h5⟩ := Proofs.Sha256Air.sound (by simpa using hp) hT hi
  refine ⟨H, M, h1, h2, fun j hj limb hl => ?_, h4, h5⟩
  rw [h3 j hj limb hl, limbOf]
  interval_cases limb <;> norm_num

/-- BabyBear, KoalaBear, Goldilocks and Mersenne31 have characteristic above 7 * 2^16, as soundness needs. -/
theorem ringChar_fields : 7 * 2 ^ 16 < ringChar BabyBear.Field ∧ 7 * 2 ^ 16 < ringChar KoalaBear.Field ∧
    7 * 2 ^ 16 < ringChar Goldilocks.Field ∧ 7 * 2 ^ 16 < ringChar Mersenne31.Field := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [ZMod.ringChar_zmod_n] <;> decide

/-! ## Completeness over any field -/

/-- Completeness: on a power-of-two number of inputs, the generator's trace satisfies the AIR, in every field. -/
theorem complete [Inhabited F] {inputs : List (List (BitVec 32))}
    (h : inputs.length ≠ 0 ∧ 2 ^ Nat.log 2 inputs.length = inputs.length) (e : ℕ) :
    ∃ M, generate_trace_rows (F := F) inputs e = some M ∧
      Satisfies (constraints sha256Air) (instOf sha256Air M []) :=
  Proofs.Sha256Air.complete h e

/-- The debug checker accepts the generator's trace. -/
theorem check_complete [Inhabited F] [DecidableEq F] {inputs : List (List (BitVec 32))}
    (h : inputs.length ≠ 0 ∧ 2 ^ Nat.log 2 inputs.length = inputs.length) (e : ℕ) :
    ∃ M, generate_trace_rows (F := F) inputs e = some M ∧ check_constraints sha256Air M [] = .ok () :=
  Proofs.Sha256Air.check_complete h e

/-- The generator panics when the number of inputs is not a power of two. -/
theorem generate_trace_rows.panics {inputs : List (List (BitVec 32))}
    (h : ¬ (inputs.length ≠ 0 ∧ 2 ^ Nat.log 2 inputs.length = inputs.length)) (e : ℕ) :
    generate_trace_rows (F := F) inputs e = none :=
  generate_panics h e

/-! ## Constraint degrees and the quotient -/

/-- Over BabyBear, every symbolic constraint has degree multiple at most 3 and no transition selector. -/
theorem degree_babyBear :
    ∀ e ∈ (sha256Air (F := BabyBear.Field)).eval
        (symbolicBuilder (AirLayout.from_air (sha256Air (F := BabyBear.Field)))) [],
      e.degree_multiple ≤ 3 ∧ transitionCount e = 0 :=
  constraints_bounded top_babyBear

/-- Over KoalaBear, the same bounds hold. -/
theorem degree_koalaBear :
    ∀ e ∈ (sha256Air (F := KoalaBear.Field)).eval
        (symbolicBuilder (AirLayout.from_air (sha256Air (F := KoalaBear.Field)))) [],
      e.degree_multiple ≤ 3 ∧ transitionCount e = 0 :=
  constraints_bounded top_koalaBear

/-- Over Goldilocks, the same bounds hold. -/
theorem degree_goldilocks :
    ∀ e ∈ (sha256Air (F := Goldilocks.Field)).eval
        (symbolicBuilder (AirLayout.from_air (sha256Air (F := Goldilocks.Field)))) [],
      e.degree_multiple ≤ 3 ∧ transitionCount e = 0 :=
  constraints_bounded top_goldilocks

/-- Over Mersenne31, the same bounds hold. -/
theorem degree_mersenne31 :
    ∀ e ∈ (sha256Air (F := Mersenne31.Field)).eval
        (symbolicBuilder (AirLayout.from_air (sha256Air (F := Mersenne31.Field)))) [],
      e.degree_multiple ≤ 3 ∧ transitionCount e = 0 :=
  constraints_bounded top_mersenne31

/-- Over BabyBear, the quotient sizing gives 2 chunks, and every constraint polynomial fits them. -/
theorem quotient_fits_babyBear {n : ℕ} (hn : 1 ≤ n) {σ : Var → Polynomial BabyBear.Field}
    {periods : List ℕ} (hσ : DegreeBounds σ n periods)
    (hp : ∀ j p : ℕ, periods[j]? = some p → 0 < p → p < n → p ∣ n) :
    get_log_quotient_degree (sha256Air (F := BabyBear.Field))
        (AirLayout.from_air (sha256Air (F := BabyBear.Field))) n 0 = .ok 1 ∧
      ∀ e ∈ (sha256Air (F := BabyBear.Field)).eval
          (symbolicBuilder (AirLayout.from_air (sha256Air (F := BabyBear.Field)))) [],
        FitsChunks n (2 ^ 1) (constraintPoly σ (toPoly e)) :=
  quotient_fits top_babyBear hn hσ hp

/-- Over BabyBear, the AIR asserts 8096 constraints. -/
theorem num_constraints_babyBear :
    ((sha256Air (F := BabyBear.Field)).eval
        (symbolicBuilder (AirLayout.from_air (sha256Air (F := BabyBear.Field)))) []).length = 8096 :=
  Proofs.Sha256Air.num_constraints

/-! ## Constants and extracted code -/

/-- The transcribed round constants are those of FIPS 180-4, section 4.2.2. -/
theorem SHA256_K.eq_fips : ∀ t < 64, BitVec.ofNat 32 (kOf t) = K.getD t 0 := kOf_bv

/-- The extracted round constants are the transcribed ones, and FIPS 180-4's. -/
theorem constants.SHA256_K.eq_fips :
    p3_sha256_air.constants.SHA256_K.val.map (·.val) = SHA256_K ∧
      p3_sha256_air.constants.SHA256_K.val.map Aeneas.Std.UScalar.bv = K :=
  ⟨SHA256_K_eq, SHA256_K_bv⟩

/-- The extracted initial hash value is the transcribed one, and FIPS 180-4's. -/
theorem constants.SHA256_IV.eq_fips :
    p3_sha256_air.constants.SHA256_IV.val.map (·.val) = SHA256_IV ∧
      p3_sha256_air.constants.SHA256_IV.val.map Aeneas.Std.UScalar.bv = H0 :=
  ⟨SHA256_IV_eq, SHA256_IV_bv⟩

/-- The extracted limb split never panics, and returns the low and the high 16 bits. -/
theorem constants.u32_to_limbs.spec (value : Aeneas.Std.U32) :
    ∃ out, p3_sha256_air.constants.u32_to_limbs value = .ok out ∧
      out.val.map (·.val) = [value.val % 2 ^ 16, value.val / 2 ^ 16] :=
  u32_to_limbs_eq value

/-- The extracted sigma functions never panic, and are those of FIPS 180-4, section 4.1.2. -/
theorem binary.generation.sigma.eq_fips (x : Aeneas.Std.U32) :
    p3_sha256_air.binary.generation.big_sigma0 x = .ok ⟨bigSigma0 x.bv⟩ ∧
      p3_sha256_air.binary.generation.big_sigma1 x = .ok ⟨bigSigma1 x.bv⟩ ∧
      p3_sha256_air.binary.generation.small_sigma0 x = .ok ⟨smallSigma0 x.bv⟩ ∧
      p3_sha256_air.binary.generation.small_sigma1 x = .ok ⟨smallSigma1 x.bv⟩ :=
  ⟨big_sigma0_eq x, big_sigma1_eq x, small_sigma0_eq x, small_sigma1_eq x⟩

/-! ## The AIR over a field of characteristic 2 -/

/-- Soundness in characteristic 2: each row of a satisfying trace computes one compression.

- the row's input cells must be bits, which the booleanity, when stated, enforces
- the chains start with a chaining value H, the schedule with a block M
- the output columns hold the bits of the compression of H and M -/
theorem binary.sound [DecidableEq F] (h2 : (2 : F) = 0) {cb : Bool} {T : Instance F}
    (hT : Satisfies (constraints (binaryAir cb)) T) {i : ℕ} (hi : i < T.height)
    (hbits : cb = true ∨ Proofs.Sha256Air.Binary.InputBits T i) :
    ∃ H M : List (BitVec 32), H.length = 8 ∧ M.length = 16 ∧
      (∀ j < 4, ∀ b < 32, T.main i (binary.col.a_chain (3 - j) b) = bitF ((H.getD j 0).getLsbD b)) ∧
      (∀ j < 4, ∀ b < 32,
        T.main i (binary.col.e_chain (3 - j) b) = bitF ((H.getD (4 + j) 0).getLsbD b)) ∧
      (∀ t < 16, ∀ b < 32, T.main i (binary.col.w t b) = bitF ((M.getD t 0).getLsbD b)) ∧
      (∀ j < 8, ∀ b < 32,
        T.main i (binary.col.h_out j b) = bitF (((compress H M).getD j 0).getLsbD b)) :=
  Proofs.Sha256Air.Binary.binary_sound h2 hT hi hbits

/-- Over GF(2), every symbolic constraint has degree multiple at most 2, the declared bound.

No constraint reads a transition selector. -/
theorem binary.degree_gf2 (cb : Bool) :
    ∀ e ∈ (binaryAir (F := ZMod 2) cb).eval
        (symbolicBuilder (AirLayout.from_air (binaryAir (F := ZMod 2) cb))) [],
      e.degree_multiple ≤ 2 ∧ transitionCount e = 0 :=
  binary_constraints_bounded (top_binary_gf2 cb)

/-- Over GF(2), the AIR asserts exactly the number of constraints it reports, with or without the booleanity. -/
theorem binary.num_constraints_gf2 (cb : Bool) :
    some ((binaryAir (F := ZMod 2) cb).eval
        (symbolicBuilder (AirLayout.from_air (binaryAir (F := ZMod 2) cb))) []).length =
      p3_sha256_air.mirror.binary.num_constraints cb :=
  binary_num_constraints cb

end Plonky3Lean.Claims.Sha256Air
