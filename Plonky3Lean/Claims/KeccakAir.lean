module

public import Plonky3Lean.Proofs.KeccakAir.Fields
public import Plonky3Lean.Proofs.KeccakAir.Complete
public import Plonky3Lean.Proofs.KeccakAir.Extracted
public import Plonky3Lean.Proofs.KeccakAir.Binary.Complete
public import Plonky3Lean.Proofs.KeccakAir.Binary.Degree
public import Plonky3Lean.Proofs.KeccakAir.Binary.Extracted

@[expose] public section

/-!
# p3-keccak-air: claims

These claims hold at the Plonky3 commit pinned in `plonky3/`.

The tables and the characteristic-2 round on words are extracted.

The two AIR evaluations and the two trace generators are transcriptions with mirror entries.

Each evaluation is parametric, so it is an AIR of the p3-air model.

A trace satisfies an AIR when every constraint polynomial vanishes on every row.

The last row's next row is row 0.

The specification is FIPS 202, as transcribed in the Keccak specification module.

## The AIR over a field of size at least 2^16

A row holds one round:

- 24 one-hot flags
- the round's input as 16-bit limbs
- the bits of C, C', A' and A''[0, 0]

```text
    rows 24 m .. 24 m + 23    one permutation, round k on row 24 m + k
    preimage                  the permutation's input, on all 24 rows
    A''' on row 24 m + 23     the permutation's output
```

The claims:

- soundness needs a characteristic of at least 2^16, where a limb determines its 16 bits
- every row's flags are one-hot at the row index mod 24
- on a whole permutation with preimage state A, row 24 m + k holds the limbs of Rnd^k(A)
- the permutation's output limbs are those of Keccak-f[1600](A)
- the generator's trace satisfies the AIR in every field, and the debug checker accepts it
- every constraint has degree multiple at most 3 and at most one transition selector along a product
- so every constraint polynomial fits the quotient's at most 2 chunks

## The AIR over a field of characteristic 2

A row holds 25 one-hot flags and the 1600 state bits.

The flags mark a round r < 24 or an output row.

The claims:

- every row is one-hot
- a round-0 row starts 24 round rows, whose successor holds Keccak-f[1600] of its state
- this holds when the AIR states the booleanity of the state
- without the booleanity, it holds when the trace's state cells are bits
- the generator's trace satisfies the AIR, with or without the booleanity
- the extracted round on words computes Rnd of FIPS 202 below round 24, and panics from round 24
-/

open Plonky3Lean.Spec.Air Plonky3Lean.Spec.Keccak Plonky3Lean.Proofs.Air
open Plonky3Lean.Proofs.KeccakAir p3_air.air.mirror p3_air.symbolic.mirror p3_keccak_air.mirror

namespace Plonky3Lean.Claims.KeccakAir

variable {F : Type} [Field F] [DecidableEq F]

/-! ## Soundness over a field of size at least 2^16 -/

/-- In a satisfying trace, the flags of row i are one-hot at i mod 24. -/
theorem flags {T : Instance F} (hT : Satisfies (constraints keccakAir) T) :
    ∀ i < T.height, ∀ r < 24, T.main i (col.step_flags r) = if r = i % 24 then 1 else 0 := by
  intro i hi r hr
  rw [← cur_eq T i (by simp only [col.step_flags, NUM_KECCAK_COLS]; omega)]
  exact flags_eq hT i hi r hr

/-- Soundness on one permutation.

Take rows 24 m to 24 m + 23 of a satisfying trace, and let A be the state the preimage limbs hold.

Row 24 m + k holds the limbs of Rnd^k(A).

The output limbs are those of Keccak-f[1600](A). -/
theorem sound (hp : 2 ^ 16 ≤ ringChar F) {T : Instance F} (hT : Satisfies (constraints keccakAir) T)
    {m : ℕ} (hm : 24 * m + 24 ≤ T.height) :
    ∃ A : State,
      (∀ k < 24, ∀ x y : Fin 5, ∀ limb : Fin 4,
        T.main (24 * m + k) (col.preimage y x limb) = (stateLimb A x y limb : F)) ∧
      (∀ k < 24, ∀ x y : Fin 5, ∀ limb : Fin 4,
        T.main (24 * m + k) (col.a y x limb) =
          (stateLimb ((List.range k).foldl (fun A r => rnd A r) A) x y limb : F)) ∧
      ∀ x y : Fin 5, ∀ limb : Fin 4,
        a_prime_prime_prime (T.main (24 * m + 23)) y x limb = (stateLimb (keccakP 24 A) x y limb : F) := by
  refine ⟨toState (inB (cur T (24 * m))), fun k hk x y limb => ?_,
    fun k hk x y limb => input_limbs hp hT hm hk x y limb, fun x y limb => ?_⟩
  · rw [← cur_eq T _ (by simp only [col.preimage, NUM_KECCAK_COLS]; omega),
      preimage_const hp hT hm hk x.isLt y.isLt limb.isLt, preimage_eq hp hT hm]
  · rw [← output_eq_keccakP hp hT hm]
    unfold a_prime_prime_prime
    split_ifs
    · exact (cur_eq T _ (by simp only [col.a_prime_prime_prime_0_0_limbs, NUM_KECCAK_COLS]; omega)).symm
    · exact (cur_eq T _ (by simp only [col.a_prime_prime, NUM_KECCAK_COLS]; omega)).symm

/-- BabyBear, KoalaBear, Goldilocks and Mersenne31 have characteristic at least 2^16, as soundness needs. -/
theorem ringChar_fields : 2 ^ 16 ≤ ringChar BabyBear.Field ∧ 2 ^ 16 ≤ ringChar KoalaBear.Field ∧
    2 ^ 16 ≤ ringChar Goldilocks.Field ∧ 2 ^ 16 ≤ ringChar Mersenne31.Field :=
  ⟨ringChar_babyBear, ringChar_koalaBear, ringChar_goldilocks, ringChar_mersenne31⟩

/-! ## Completeness over any field -/

omit [DecidableEq F] in
/-- Completeness: the generator's trace of any inputs satisfies the AIR, in every field. -/
theorem complete [Inhabited F] (inputs : List (List Word)) (e : ℕ) :
    Satisfies (constraints keccakAir) (instOf keccakAir (generate_trace_rows (F := F) inputs e) []) :=
  Proofs.KeccakAir.complete inputs e

/-- The debug checker accepts the generator's trace of any inputs. -/
theorem check_complete [Inhabited F] (inputs : List (List Word)) (e : ℕ) :
    check_constraints keccakAir (generate_trace_rows (F := F) inputs e) [] = .ok () :=
  Proofs.KeccakAir.check_complete inputs e

/-! ## Constraint degrees and the quotient -/

/-- Over BabyBear, every symbolic constraint has degree multiple at most 3.

It also has at most one transition selector along a product. -/
theorem degree_babyBear :
    ∀ e ∈ (keccakAir (F := BabyBear.Field)).eval
        (symbolicBuilder (AirLayout.from_air (keccakAir (F := BabyBear.Field)))) [],
      e.degree_multiple ≤ 3 ∧ transitionCount e ≤ 1 :=
  keccak_constraints_bounded top_babyBear

/-- Over KoalaBear, the same bounds hold. -/
theorem degree_koalaBear :
    ∀ e ∈ (keccakAir (F := KoalaBear.Field)).eval
        (symbolicBuilder (AirLayout.from_air (keccakAir (F := KoalaBear.Field)))) [],
      e.degree_multiple ≤ 3 ∧ transitionCount e ≤ 1 :=
  keccak_constraints_bounded top_koalaBear

/-- Over Goldilocks, the same bounds hold. -/
theorem degree_goldilocks :
    ∀ e ∈ (keccakAir (F := Goldilocks.Field)).eval
        (symbolicBuilder (AirLayout.from_air (keccakAir (F := Goldilocks.Field)))) [],
      e.degree_multiple ≤ 3 ∧ transitionCount e ≤ 1 :=
  keccak_constraints_bounded top_goldilocks

/-- Over Mersenne31, the same bounds hold. -/
theorem degree_mersenne31 :
    ∀ e ∈ (keccakAir (F := Mersenne31.Field)).eval
        (symbolicBuilder (AirLayout.from_air (keccakAir (F := Mersenne31.Field)))) [],
      e.degree_multiple ≤ 3 ∧ transitionCount e ≤ 1 :=
  keccak_constraints_bounded top_mersenne31

/-- Over BabyBear, the quotient sizing gives at most 2 chunks.

Every constraint polynomial fits them, for degree bounds of a trace of n rows. -/
theorem quotient_fits_babyBear {n : ℕ} (hn : 1 ≤ n) {σ : Var → Polynomial BabyBear.Field}
    {periods : List ℕ} (hσ : DegreeBounds σ n periods)
    (hp : ∀ j p : ℕ, periods[j]? = some p → 0 < p → p < n → p ∣ n) :
    ∃ L ≤ 1, get_log_quotient_degree (keccakAir (F := BabyBear.Field))
        (AirLayout.from_air (keccakAir (F := BabyBear.Field))) n 0 = .ok L ∧
      ∀ e ∈ (keccakAir (F := BabyBear.Field)).eval
          (symbolicBuilder (AirLayout.from_air (keccakAir (F := BabyBear.Field)))) [],
        FitsChunks n (2 ^ L) (constraintPoly σ (toPoly e)) :=
  keccak_quotient_fits top_babyBear hn hσ hp

/-! ## Tables -/

/-- Entry [x][y] of the rho table is the rotation Algorithm 2 gives lane (x, y). -/
theorem R.eq_fips : ∀ x < 5, ∀ y < 5,
    rOf x y = Plonky3Lean.Proofs.Keccak.rhoOffsets.getD (x + 5 * y) 0 := rOf_eq

/-- Bit z of the table's round constant r is bit z of the round constant of round r, from Algorithm 6. -/
theorem RC_BITS.eq_fips {r z : ℕ} (hr : r < 24) (hz : z < 64) :
    (rcBit r z ≠ 0) = (roundConstant r (Fin.ofNat 64 z) = true) := rcBit_eq hr hz

/-- The round constants agree with their bits, bit for bit. -/
theorem RC.eq_RC_BITS : ∀ k < 24, ∀ z < 64,
    (BitVec.ofNat 64 (RC.getD k 0)).getLsbD z = decide (rcBit k z ≠ 0) := rc_getLsbD

/-- The extracted tables are the transcribed ones. -/
theorem constants.eq_mirror :
    p3_keccak_air.constants.R.val.map (fun row => row.val.map (·.val)) = R ∧
      p3_keccak_air.constants.RC.val.map (·.val) = RC ∧
      p3_keccak_air.constants.RC_BITS.val.map (fun row => row.val.map (·.val)) = RC_BITS :=
  ⟨R_eq, RC_eq, RC_BITS_eq⟩

/-- The extracted round constants are those of Algorithm 6. -/
theorem constants.RC.eq_lfsr :
    p3_keccak_air.constants.RC.val.map Aeneas.Std.UScalar.bv =
      (List.range 24).map Plonky3Lean.Proofs.Keccak.rcWord := RC_eq_lfsr

/-! ## The AIR over a field of characteristic 2 -/

section binary

open Plonky3Lean.Proofs.KeccakAir.Binary p3_keccak_air.mirror.binary

/-- The characteristic-2 generator's round on words computes Rnd(A, k) of FIPS 202. -/
theorem binary.keccak_round.eq_fips (S : LState) {k : ℕ} (hk : k < 24) :
    lanesState (keccak_round S k) = rnd (lanesState S) k := keccak_round_eq S hk

/-- The extracted characteristic-2 round never panics for a round below 24.

It computes Rnd(A, k) of FIPS 202 on the state its 25 words hold. -/
theorem binary.generation.keccak_round.eq_fips (state : Aeneas.Std.Array Aeneas.Std.U64 25#usize)
    (round : Aeneas.Std.Usize) (hr : round.val < 24) :
    ∃ out, p3_keccak_air.binary.generation.keccak_round state round = .ok out ∧
      lanesState (fun j => (out.val[j]!).bv) = rnd (lanesState (fun j => (state.val[j]!).bv)) round.val := by
  obtain ⟨out, h1, h2⟩ := keccak_round_extracted state round hr
  refine ⟨out, h1, ?_⟩
  rw [← keccak_round_eq _ hr]
  funext x y z
  simp only [lanesState]
  rw [h2 _ (by omega)]

/-- For a round of 24 or more, the extracted round panics. -/
theorem binary.generation.keccak_round.panics (state : Aeneas.Std.Array Aeneas.Std.U64 25#usize)
    (round : Aeneas.Std.Usize) (hr : 24 ≤ round.val) :
    p3_keccak_air.binary.generation.keccak_round state round = .fail .panic :=
  keccak_round_panics state round hr

/-- In a satisfying trace of the AIR with the booleanity, every row's flags are one-hot. -/
theorem binary.onehot (h2 : (2 : F) = 0) {cb : Bool} {T : Instance F}
    (hT : Satisfies (constraints (binaryAir cb)) T) :
    ∀ i < T.height, ∃ k < 25, ∀ r < 25, T.main i r = if r = k then 1 else 0 := by
  intro i hi
  obtain ⟨k, hk, h⟩ := onehot_all h2 hT i hi
  exact ⟨k, hk, (onehot_curB T i k).mp h⟩

/-- Soundness with the booleanity.

From a round-0 row i, rows i + k mod n are rounds k < 24.

Row i + 24 mod n holds Keccak-f[1600] of row i's state. -/
theorem binary.sound (h2 : (2 : F) = 0) {T : Instance F}
    (hT : Satisfies (constraints (binaryAir true)) T) {i : ℕ} (hi : i < T.height)
    (h0 : ∀ r < 25, T.main i r = if r = 0 then 1 else 0) :
    (∀ k < 24, ∀ r < 25, T.main ((i + k) % T.height) r = if r = k then 1 else 0) ∧
      traceState T ((i + 24) % T.height) = keccakP 24 (traceState T i) := by
  obtain ⟨h1, h2'⟩ := perm_sound h2 hT (bits_of_constrained hT) hi ((onehot_curB T i 0).mpr h0)
  refine ⟨fun k hk => (onehot_curB T _ k).mp (h1 k hk), ?_⟩
  rw [← stateOf_curB, ← stateOf_curB, h2']

/-- Soundness without the booleanity, for a trace whose state cells are bits. -/
theorem binary.sound_boolean_trace (h2 : (2 : F) = 0) {T : Instance F}
    (hT : Satisfies (constraints (binaryAir false)) T)
    (hbits : ∀ i < T.height, ∀ y < 5, ∀ x < 5, ∀ z < 64,
      T.main i (binary.col.a y x z) = 0 ∨ T.main i (binary.col.a y x z) = 1)
    {i : ℕ} (hi : i < T.height) (h0 : ∀ r < 25, T.main i r = if r = 0 then 1 else 0) :
    (∀ k < 24, ∀ r < 25, T.main ((i + k) % T.height) r = if r = k then 1 else 0) ∧
      traceState T ((i + 24) % T.height) = keccakP 24 (traceState T i) := by
  have hb : ∀ i < T.height, ∀ y < 5, ∀ x < 5, ∀ z < 64,
      curB false T i (binary.col.a y x z) * (curB false T i (binary.col.a y x z) - 1) = 0 := by
    intro j hj y hy x hx z hz
    rw [curB_eq T j (by simp only [binary.col.a, NUM_KECCAK_BINARY_COLS]; omega)]
    rcases hbits j hj y hy x hx z hz with h | h <;> simp [h]
  obtain ⟨h1, h2'⟩ := perm_sound h2 hT hb hi ((onehot_curB T i 0).mpr h0)
  refine ⟨fun k hk => (onehot_curB T _ k).mp (h1 k hk), ?_⟩
  rw [← stateOf_curB, ← stateOf_curB, h2']

/-- Completeness over a field of characteristic 2.

The generator succeeds on a nonempty list of inputs.

Its trace satisfies the AIR, with or without the booleanity. -/
theorem binary.complete [Inhabited F] (h2 : (2 : F) = 0) (cb : Bool) {inputs : List LState}
    (hne : inputs ≠ []) (e : ℕ) :
    ∃ M, generate_binary_trace_rows (F := F) inputs e = some M ∧
      Satisfies (constraints (binaryAir cb)) (instOf (binaryAir cb) M []) :=
  Proofs.KeccakAir.Binary.complete h2 cb hne e

/-- Over GF(2), every symbolic constraint has degree multiple at most 3, the AIR's hint.

It also has at most one transition selector along a product. -/
theorem binary.degree_gf2 (cb : Bool) :
    ∀ e ∈ (binaryAir (F := ZMod 2) cb).eval
        (symbolicBuilder (AirLayout.from_air (binaryAir (F := ZMod 2) cb))) [],
      e.degree_multiple ≤ 3 ∧ transitionCount e ≤ 1 :=
  binary_constraints_bounded (top_binary_gf2 cb)

/-- Over GF(2), the AIR asserts exactly the number of constraints it reports.

This holds with or without the booleanity. -/
theorem binary.num_constraints_gf2 (cb : Bool) :
    some ((binaryAir (F := ZMod 2) cb).eval
        (symbolicBuilder (AirLayout.from_air (binaryAir (F := ZMod 2) cb))) []).length =
      p3_keccak_air.mirror.binary.num_constraints cb :=
  count_binary_gf2 cb

end binary

end Plonky3Lean.Claims.KeccakAir
