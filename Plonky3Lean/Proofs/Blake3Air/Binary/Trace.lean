module

public import Plonky3Lean.Proofs.Blake3Air.Binary.Reader
public import Plonky3Lean.Proofs.Blake3Air.GenRow

@[expose] public section

/-!
# Soundness of the characteristic-2 BLAKE3 AIR on a trace

On every row of a satisfying trace whose input cells are bits, the reader returns a compression.

It is the BLAKE3 compression of the row's inputs.

The input cells are bits when the AIR states their booleanity, or when the trace commitment only holds bits.
-/

set_option linter.unusedSectionVars false

namespace Plonky3Lean.Proofs.Blake3Air.Binary

open p3_air.builder.mirror p3_air.air.mirror p3_blake3_air.mirror p3_blake3_air.mirror.binary
open Plonky3Lean.Spec.Air Plonky3Lean.Proofs.Air Plonky3Lean.Proofs.KeccakAir Plonky3Lean.Proofs.Blake3Air

variable {F : Type} [Field F] [DecidableEq F]

section words

variable (loc : ℕ → F)

/-- The chaining value a row holds. -/
def cvB : List Word := (List.range 8).map fun i => decodeWord fun k => loc (col.chaining_value i k)

/-- The block a row holds. -/
def blkB : List Word := (List.range 16).map fun i => decodeWord fun k => loc (col.block i k)

/-- Word j of the last state row: the counter halves, the block length and the flags. -/
def row3B (j : ℕ) : Word := decodeWord fun k => loc (binary.col.counter_low (32 * j + k))

/-- The input cells are bits. -/
def InputBits : Prop := ∀ c < NUM_INPUT_BITS, loc c * (loc c - 1) = 0

end words

theorem inputBits_of_assert (env : Var → F) (L : AirLayout)
    (h : binary.assert_inputs (propBuilder env L) (rowOf env L 0) True) : InputBits (rowOf env L 0) := by
  simp [binary.assert_inputs, AirBuilder.assert_bools, AirBuilder.bool_check, AirBuilder.assert_zeros,
    propBuilder, foldl_and] at h
  obtain ⟨hcv, hb, hd⟩ := h
  intro c hc
  simp only [NUM_INPUT_BITS, NUM_INPUT_WORDS] at hc
  apply mul_eq_zero.mpr
  by_cases h1 : c < 256
  · have := hcv (c / 32) (by omega) (c % 32) (by omega)
    rwa [col.chaining_value, show 32 * (c / 32) + c % 32 = c by omega] at this
  · by_cases h2 : c < 768
    · have := hb ((c - 256) / 32) (by omega) ((c - 256) % 32) (by omega)
      rwa [col.block, show 256 + 32 * ((c - 256) / 32) + (c - 256) % 32 = c by omega] at this
    · have := hd ((c - 768) / 32) (by omega) ((c - 768) % 32) (by omega)
      rwa [initial_d, binary.col.counter_low,
        show 768 + (32 * ((c - 768) / 32) + (c - 768) % 32) = c by omega] at this

/-- The initial state of a row. -/
def initB (loc : ℕ → F) : List Word :=
  cvB loc ++ Plonky3Lean.Spec.Blake3.IV.take 4 ++ [row3B loc 0, row3B loc 1, row3B loc 2, row3B loc 3]

theorem length_initB (loc : ℕ → F) : (initB loc).length = 16 := by
  simp [initB, cvB, Plonky3Lean.Spec.Blake3.IV]

theorem iv_word_eq : ∀ j < 4, iv_word j = Plonky3Lean.Spec.Blake3.IV.getD j 0 := by decide

theorem initB_getD (loc : ℕ → F) {j : ℕ} (hj : j < 4) :
    (initB loc).getD j 0 = decodeWord (fun k => loc (col.chaining_value j k)) ∧
    (initB loc).getD (4 + j) 0 = decodeWord (fun k => loc (col.chaining_value (4 + j) k)) ∧
    (initB loc).getD (8 + j) 0 = Plonky3Lean.Spec.Blake3.IV.getD j 0 ∧
    (initB loc).getD (12 + j) 0 = row3B loc j := by
  interval_cases j <;> simp [initB, cvB, List.getD_eq_getElem?_getD, Plonky3Lean.Spec.Blake3.IV]

/-- The initial state's cells hold the initial state, when the input cells are bits. -/
theorem init_stB (env : Var → F) (L : AirLayout) (hb : InputBits (rowOf env L 0)) :
    StB (binary.initial_state (propBuilder env L) (rowOf env L 0)) fun p => (initB (rowOf env L 0)).getD p 0 := by
  intro j hj
  obtain ⟨e0, e1, e2, e3⟩ := initB_getD (rowOf env L 0) hj
  have hcv : ∀ i < 8, ∀ k < 32, rowOf env L 0 (col.chaining_value i k) *
      (rowOf env L 0 (col.chaining_value i k) - 1) = 0 := fun i hi k hk =>
    hb _ (by simp only [col.chaining_value, NUM_INPUT_BITS, NUM_INPUT_WORDS]; omega)
  refine ⟨?_, ?_, ?_, ?_⟩ <;> beta_reduce
  · rw [e0]; exact bitsRep_decode (hcv j (by omega))
  · rw [e1]; exact bitsRep_decode (hcv (4 + j) (by omega))
  · rw [e2, ← iv_word_eq j hj]; exact bitsRep_u32 _
  · rw [e3]
    exact bitsRep_decode fun k hk =>
      hb _ (by simp only [binary.col.counter_low, NUM_INPUT_BITS, NUM_INPUT_WORDS]; omega)

/-! ## A trace -/

/-- Row i of a trace, as the row builder reads it. -/
abbrev curB (cb : Bool) (T : Instance F) (i : ℕ) : ℕ → F :=
  rowOf (rowEnv T i) (AirLayout.from_air (binaryAir (F := F) cb)) 0

omit [DecidableEq F] in
theorem curB_eq (cb : Bool) (T : Instance F) (i : ℕ) {c : ℕ} (hc : c < NUM_BLAKE3_BINARY_COLS) :
    curB cb T i c = T.main i c := by
  simp [curB, rowOf, AirLayout.from_air, binaryAir, hc, rowEnv]

theorem schedule_split : schedule = ((List.range 6).flatMap fun r => (List.range 8).map fun g => (r, g)) ++
    (List.range 8).map fun g => (6, g) := rfl

theorem words_cur (cb : Bool) (T : Instance F) (i : ℕ) :
    cvB (curB cb T i) = cvB (T.main i) ∧ blkB (curB cb T i) = blkB (T.main i) ∧
      ∀ j < 4, row3B (curB cb T i) j = row3B (T.main i) j := by
  refine ⟨List.map_congr_left fun j hj => decodeWord_congr fun k hk => curB_eq cb T i ?_,
    List.map_congr_left fun j hj => decodeWord_congr fun k hk => curB_eq cb T i ?_,
    fun j hj => decodeWord_congr fun k hk => curB_eq cb T i ?_⟩ <;>
  simp_all [col.chaining_value, col.block, binary.col.counter_low, NUM_BLAKE3_BINARY_COLS] <;> omega

/-- Soundness on a row of a satisfying trace whose input cells are bits.

The reader returns the compression of the row's chaining value, block, counter, block length and flags. -/
theorem trace_sound (h2 : (2 : F) = 0) {cb : Bool} {T : Instance F}
    (hT : Satisfies (constraints (binaryAir cb)) T) {i : ℕ} (hi : i < T.height)
    (hbits : cb = true ∨ InputBits (T.main i)) :
    compression_output (rowCols (T.main i)) = some fun p =>
      (Plonky3Lean.Spec.Blake3.compress (cvB (T.main i)) (blkB (T.main i))
        ((row3B (T.main i) 0).toNat + 2 ^ 32 * (row3B (T.main i) 1).toNat) (row3B (T.main i) 2)
        (row3B (T.main i) 3)).getD p 0 := by
  have hev := (eval_iff (rowEnv T i) (AirLayout.from_air (binaryAir (F := F) cb)) cb).mp
    ((satisfies_iff_rows _ T).mp hT i hi)
  have hb : InputBits (curB cb T i) := by
    rcases hbits with h | h
    · exact inputBits_of_assert _ _ (hev.1 h)
    · intro c hc
      rw [curB_eq cb T i (by simp only [NUM_INPUT_BITS, NUM_INPUT_WORDS,
        NUM_BLAKE3_BINARY_COLS] at hc ⊢; omega)]
      exact h c hc
  obtain ⟨hcvw, hblkw, h3w⟩ := words_cur cb T i
  rw [← hcvw, ← hblkw, ← h3w 0 (by norm_num), ← h3w 1 (by norm_num), ← h3w 2 (by norm_num),
    ← h3w 3 (by norm_num)]
  have hst0 := init_stB (rowEnv T i) _ hb
  have hsnd : ∀ (a : ℕ × ℕ) (s : Prop) (x : State F),
      (g_step (propBuilder (rowEnv T i) (AirLayout.from_air (binaryAir (F := F) cb))) (curB cb T i) a.1 a.2 (s, x)).2 =
      (g_step (propBuilder (rowEnv T i) (AirLayout.from_air (binaryAir (F := F) cb))) (curB cb T i) a.1 a.2 (True, x)).2 :=
    fun _ _ _ => rfl
  obtain ⟨hpre, hlast⟩ := (checksP_append _ hsnd _ _ _).mp (schedule_split ▸ hev.2)
  have hblk : ∀ j < 16, BitsRep (fun k => curB cb T i (col.block j k)) ((blkB (curB cb T i)).getD j 0) := by
    intro j hj
    rw [show (blkB (curB cb T i)).getD j 0 = decodeWord fun k => curB cb T i (col.block j k) by
      simp [blkB, List.getD_eq_getElem?_getD, hj]]
    exact bitsRep_decode fun k hk => hb _ (by simp only [col.block, NUM_INPUT_BITS, NUM_INPUT_WORDS]; omega)
  have hst6 := sched_sound h2 _ _ hblk _ (fun rg h => by
    simp only [List.mem_flatMap, List.mem_map, List.mem_range] at h
    obtain ⟨r, -, g, hg, rfl⟩ := h; exact hg) hst0 hpre
  rw [gfold_rounds _ _ (length_initB _)] at hst6
  have hcv : ∀ j < 8, BitsRep (fun k => curB cb T i (col.chaining_value j k)) ((cvB (curB cb T i)).getD j 0) := by
    intro j hj
    rw [show (cvB (curB cb T i)).getD j 0 = decodeWord fun k => curB cb T i (col.chaining_value j k) by
      simp [cvB, List.getD_eq_getElem?_getD, hj]]
    exact bitsRep_decode fun k hk => hb _ (by
      simp only [col.chaining_value, NUM_INPUT_BITS, NUM_INPUT_WORDS]; omega)
  rw [reader_sound h2 _ _ hblk hst6 hlast hcv (fun c hc => (curB_eq cb T i hc).symm)]
  congr 1
  funext p
  have hround : ∀ q, roundF (fun j => (Plonky3Lean.Spec.Blake3.rounds 6 (initB (curB cb T i))
      (blkB (curB cb T i))).getD j 0) (fun j => (blkB (curB cb T i)).getD (msgIdx 6 j) 0) q =
      (Plonky3Lean.Spec.Blake3.rounds 7 (initB (curB cb T i)) (blkB (curB cb T i))).getD q 0 := by
    intro q
    rw [rounds_succ 6, round_getD _ _ (length_rounds _ _ _ (length_initB _))]
    exact congrFun (roundF_congr _ fun j hj => by
      rw [msgIdx_eq, Plonky3Lean.Proofs.Blake3.permute_iter_getD _ _ _ hj]) q
  have hinit : cvB (curB cb T i) ++ Plonky3Lean.Spec.Blake3.IV.take 4 ++
      [BitVec.ofNat 32 ((row3B (curB cb T i) 0).toNat + 2 ^ 32 * (row3B (curB cb T i) 1).toNat),
        BitVec.ofNat 32 (((row3B (curB cb T i) 0).toNat + 2 ^ 32 * (row3B (curB cb T i) 1).toNat) / 2 ^ 32),
        row3B (curB cb T i) 2, row3B (curB cb T i) 3] = initB (curB cb T i) := by
    rw [(counter_words _ _).1, (counter_words _ _).2]; rfl
  dsimp only
  by_cases hp : p < 16
  · rw [compress_getD _ _ _ _ _ hp]
    dsimp only
    rw [hinit]
    by_cases h8 : p < 8
    · simp only [h8, ite_true, hp, show p + 8 < 16 by omega, hround]
    · simp only [h8, ite_false, hp, ite_true, show p - 8 < 8 by omega, hround]
  · have hlen : (Plonky3Lean.Spec.Blake3.compress (cvB (curB cb T i)) (blkB (curB cb T i))
        ((row3B (curB cb T i) 0).toNat + 2 ^ 32 * (row3B (curB cb T i) 1).toNat) (row3B (curB cb T i) 2)
        (row3B (curB cb T i) 3)).length = 16 := by simp [Plonky3Lean.Spec.Blake3.compress]
    simp only [hp, show ¬ p < 8 by omega, show ¬ p - 8 < 8 by omega, ite_false]
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
    rfl

end Plonky3Lean.Proofs.Blake3Air.Binary
