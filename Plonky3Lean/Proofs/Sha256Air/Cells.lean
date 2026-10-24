module

public import Plonky3Lean.Proofs.Sha256Air.Parametric
public import Plonky3Lean.Proofs.KeccakAir.Cells
public import Mathlib.Tactic.IntervalCases

@[expose] public section

/-!
# The cells of a row

A row of the column struct lays its fields out in declaration order.

Cell `c` of the row is the field entry that the column index `c` names.
-/

set_option linter.unusedSectionVars false

namespace Plonky3Lean.Proofs.Sha256Air

open p3_sha256_air.mirror
open Plonky3Lean.Proofs.KeccakAir (length_flatMap_range getD_flatMap_range getD_append_le
  getD_append_lt)

variable {T : Type}

theorem length_block (f : ℕ → ℕ → T) (n m : ℕ) : (Sha256Cols.block f n m).length = m * n := by
  rw [Sha256Cols.block, length_flatMap_range (m := m)]; simp

theorem getD_block (f : ℕ → ℕ → T) {n m i j c : ℕ} (hi : i < n) (hj : j < m) (hc : c = m * i + j)
    (d : T) : (Sha256Cols.block f n m).getD c d = f i j := by
  subst hc
  rw [Sha256Cols.block, getD_flatMap_range (m := m) (by simp) hi hj]
  simp [hj]

theorem length_roundCells (r : Sha256RoundCols T) : (Sha256Cols.roundCells r).length = 12 := by
  simp [Sha256Cols.roundCells]

theorem length_rounds (r : ℕ → Sha256RoundCols T) :
    ((List.range 64).flatMap fun t => Sha256Cols.roundCells (r t)).length = 768 := by
  rw [length_flatMap_range (m := 12) (fun t => length_roundCells _)]

theorem length_cells (r : Sha256Cols T) : r.cells.length = NUM_SHA256_COLS := by
  simp only [Sha256Cols.cells, List.length_append, length_block, length_rounds, NUM_SHA256_COLS,
    STATE_WORDS, U32_LIMBS, CHAIN_LEN, WORD_BITS, BITS_PER_LIMB, NUM_COMPRESSION_ROUNDS,
    SCHEDULE_EXTENSIONS, BLOCK_WORDS]

/-- Cell `off` of round t, for `off < 12`. -/
def roundCell (r : Sha256RoundCols T) (off : ℕ) : T :=
  if off < 2 then r.sigma1_e off else if off < 4 then r.ch (off - 2)
  else if off < 6 then r.tmp1 (off - 4) else if off < 8 then r.t1 (off - 6)
  else if off < 10 then r.sigma0_a (off - 8) else r.maj (off - 10)

theorem getD_roundCells (r : Sha256RoundCols T) {off : ℕ} (h : off < 12) (d : T) :
    (Sha256Cols.roundCells r).getD off d = roundCell r off := by
  unfold Sha256Cols.roundCells roundCell
  interval_cases off <;> rfl

theorem getD_rounds (r : ℕ → Sha256RoundCols T) {c t off : ℕ} (ht : t < 64) (ho : off < 12)
    (hc : c = 12 * t + off) (d : T) :
    ((List.range 64).flatMap fun t => Sha256Cols.roundCells (r t)).getD c d = roundCell (r t) off := by
  subst hc
  rw [getD_flatMap_range (m := 12) (fun t => length_roundCells _) ht ho, getD_roundCells _ ho]

section cells

variable [Zero T] (r : Sha256Cols T)

/-- Walk the cells' blocks to the one a column index lies in. -/
macro "cells_tac" : tactic => `(tactic| (
  simp only [Sha256Cols.cells, List.append_assoc]
  repeat (first
    | rw [getD_append_le (by simp only [length_block, length_rounds, col.h_in, col.a_chain,
        col.e_chain, col.w, col.sched_sigma0, col.sched_sigma1, col.sched_tmp, col.sigma1_e, col.ch,
        col.tmp1, col.t1, col.sigma0_a, col.maj, col.h_out, STATE_WORDS, U32_LIMBS, CHAIN_LEN,
        WORD_BITS, BITS_PER_LIMB, NUM_COMPRESSION_ROUNDS, SCHEDULE_EXTENSIONS, BLOCK_WORDS]; omega)]
    | rw [getD_append_lt (by simp only [length_block, length_rounds, col.h_in, col.a_chain,
        col.e_chain, col.w, col.sched_sigma0, col.sched_sigma1, col.sched_tmp, col.sigma1_e, col.ch,
        col.tmp1, col.t1, col.sigma0_a, col.maj, col.h_out, STATE_WORDS, U32_LIMBS, CHAIN_LEN,
        WORD_BITS, BITS_PER_LIMB, NUM_COMPRESSION_ROUNDS, SCHEDULE_EXTENSIONS, BLOCK_WORDS]; omega)])
  simp only [length_block, length_rounds, col.h_in, col.a_chain, col.e_chain, col.w,
    col.sched_sigma0, col.sched_sigma1, col.sched_tmp, col.sigma1_e, col.ch, col.tmp1, col.t1,
    col.sigma0_a, col.maj, col.h_out, STATE_WORDS, U32_LIMBS, CHAIN_LEN, WORD_BITS, BITS_PER_LIMB,
    NUM_COMPRESSION_ROUNDS, SCHEDULE_EXTENSIONS, BLOCK_WORDS]))

theorem cell_h_in {i l : ℕ} (hi : i < 8) (hl : l < 2) : r.cells.getD (col.h_in i l) 0 = r.h_in i l := by
  cells_tac; exact getD_block _ hi hl (by omega) _

theorem cell_a {k b : ℕ} (hk : k < 68) (hb : b < 32) :
    r.cells.getD (col.a_chain k b) 0 = r.a_chain k b := by
  cells_tac; exact getD_block _ hk hb (by omega) _

theorem cell_e {k b : ℕ} (hk : k < 68) (hb : b < 32) :
    r.cells.getD (col.e_chain k b) 0 = r.e_chain k b := by
  cells_tac; exact getD_block _ hk hb (by omega) _

theorem cell_w {t b : ℕ} (ht : t < 64) (hb : b < 32) : r.cells.getD (col.w t b) 0 = r.w t b := by
  cells_tac; exact getD_block _ ht hb (by omega) _

theorem cell_s0 {i l : ℕ} (hi : i < 48) (hl : l < 2) :
    r.cells.getD (col.sched_sigma0 i l) 0 = r.sched_sigma0 i l := by
  cells_tac; exact getD_block _ hi hl (by omega) _

theorem cell_s1 {i l : ℕ} (hi : i < 48) (hl : l < 2) :
    r.cells.getD (col.sched_sigma1 i l) 0 = r.sched_sigma1 i l := by
  cells_tac; exact getD_block _ hi hl (by omega) _

theorem cell_tmp {i l : ℕ} (hi : i < 48) (hl : l < 2) :
    r.cells.getD (col.sched_tmp i l) 0 = r.sched_tmp i l := by
  cells_tac; exact getD_block _ hi hl (by omega) _

theorem cell_round {t off : ℕ} (ht : t < 64) (ho : off < 12) :
    r.cells.getD (6704 + 12 * t + off) 0 = roundCell (r.rounds t) off := by
  cells_tac; exact getD_rounds _ ht ho (by omega) _

theorem cell_h_out {i b : ℕ} (hi : i < 8) (hb : b < 32) :
    r.cells.getD (col.h_out i b) 0 = r.h_out i b := by
  cells_tac; exact getD_block _ hi hb (by omega) _

end cells

end Plonky3Lean.Proofs.Sha256Air
