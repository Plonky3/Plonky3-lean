module

public import Plonky3Lean.Proofs.Blake3Air.Parametric
public import Plonky3Lean.Proofs.KeccakAir.Cells
public import Mathlib.Tactic.IntervalCases

@[expose] public section

/-!
# The cells of a row

A row of the column struct lays its fields out in declaration order.

Cell `c` of the row is the field entry that the column index `c` names.
-/

set_option linter.unusedSectionVars false

namespace Plonky3Lean.Proofs.Blake3Air

open p3_blake3_air.mirror Plonky3Lean.Proofs.KeccakAir

variable {T : Type}

theorem length_words (n m : ℕ) (f : ℕ → ℕ → T) : (Blake3Cols.words n m f).length = m * n := by
  rw [Blake3Cols.words, length_flatMap_range (m := m)]; simp

theorem getD_words {n m : ℕ} (f : ℕ → ℕ → T) {c j k : ℕ} (hc : c = m * j + k) (hj : j < n) (hk : k < m)
    (d : T) : (Blake3Cols.words n m f).getD c d = f j k := by
  subst hc
  rw [Blake3Cols.words, getD_flatMap_range (m := m) (by simp) hj hk]
  simp [hk]

theorem length_stateCells (st : Blake3State T) : (Blake3Cols.stateCells st).length = 272 := by
  simp [Blake3Cols.stateCells, length_words]

theorem length_roundCells (fr : FullRound T) : (Blake3Cols.roundCells fr).length = 1088 := by
  simp [Blake3Cols.roundCells, length_stateCells]

theorem length_allRoundCells (f : ℕ → FullRound T) :
    ((List.range 7).flatMap fun i => Blake3Cols.roundCells (f i)).length = 7616 := by
  rw [length_flatMap_range (m := 1088) (fun i => length_roundCells _)]

theorem getD_stateCells (st : Blake3State T) {c : ℕ} (hc : c < 272) (d : T) :
    (Blake3Cols.stateCells st).getD c d =
      if c < 8 then st.row0 (c / 2) (c % 2)
      else if c < 136 then st.row1 ((c - 8) / 32) ((c - 8) % 32)
      else if c < 144 then st.row2 ((c - 136) / 2) ((c - 136) % 2)
      else st.row3 ((c - 144) / 32) ((c - 144) % 32) := by
  simp only [Blake3Cols.stateCells, List.append_assoc]
  split_ifs with h1 h2 h3
  · rw [getD_append_lt (by rw [length_words]; omega), getD_words _ (j := c / 2) (k := c % 2) (by omega)
      (by omega) (by omega)]
  · rw [getD_append_le (by rw [length_words]; omega), length_words,
      getD_append_lt (by rw [length_words]; omega),
      getD_words _ (j := (c - 8) / 32) (k := (c - 8) % 32) (by omega) (by omega) (by omega)]
  · rw [getD_append_le (by rw [length_words]; omega), length_words,
      getD_append_le (by rw [length_words]; omega), length_words,
      getD_append_lt (by rw [length_words]; omega),
      getD_words _ (j := (c - 136) / 2) (k := (c - 136) % 2) (by omega) (by omega) (by omega)]
  · rw [getD_append_le (by rw [length_words]; omega), length_words,
      getD_append_le (by rw [length_words]; omega), length_words,
      getD_append_le (by rw [length_words]; omega), length_words,
      getD_words _ (j := (c - 144) / 32) (k := (c - 144) % 32) (by omega) (by omega) (by omega)]

theorem length_cells (r : Blake3Cols T) : r.cells.length = NUM_BLAKE3_COLS := by
  simp only [Blake3Cols.cells, List.length_append, length_words, length_allRoundCells, List.length_map,
    List.length_range, NUM_BLAKE3_COLS]

/-- Cell c of a row. -/
abbrev getc [Zero T] (r : Blake3Cols T) (c : ℕ) : T := r.cells.getD c 0

/-- Unfold the cells into their blocks and walk to the block a column index lies in. -/
macro "cells_tac" : tactic => `(tactic| (
  unfold Plonky3Lean.Proofs.Blake3Air.getc p3_blake3_air.mirror.Blake3Cols.cells
  simp only [List.append_assoc]
  repeat (first
    | rw [getD_append_le (by simp only [length_words, length_allRoundCells, List.length_map,
        List.length_range, col.inputs, col.chaining_values, col.counter_low, col.initial_row0,
        col.initial_row2, col.state, col.final_round_helpers, col.outputs]; omega)]
    | rw [getD_append_lt (by simp only [length_words, length_allRoundCells, List.length_map,
        List.length_range, col.inputs, col.chaining_values, col.counter_low, col.initial_row0,
        col.initial_row2, col.state, col.final_round_helpers, col.outputs]; omega)])
  try simp only [length_words, length_allRoundCells, List.length_map, List.length_range]))

section cells

variable [Zero T] (r : Blake3Cols T)

theorem cell_inputs {i k : ℕ} (hi : i < 16) (hk : k < 32) : getc r (col.inputs i k) = r.inputs i k := by
  cells_tac; exact getD_words _ (by unfold col.inputs; omega) hi hk _

theorem cell_cv {h j k : ℕ} (hh : h < 2) (hj : j < 4) (hk : k < 32) :
    getc r (col.chaining_values h j k) = r.chaining_values h j k := by
  cells_tac
  rw [getD_words _ (j := h) (k := 32 * j + k) (by unfold col.chaining_values; omega) hh (by omega)]
  congr 1 <;> omega

theorem cell_counter_low {k : ℕ} (hk : k < 32) : getc r (col.counter_low k) = r.counter_low k := by
  cells_tac; exact getD_map_range_of _ (by unfold col.counter_low; omega) hk _

theorem cell_counter_hi {k : ℕ} (hk : k < 32) : getc r (col.counter_low (32 + k)) = r.counter_hi k := by
  cells_tac; exact getD_map_range_of _ (by unfold col.counter_low; omega) hk _

theorem cell_block_len {k : ℕ} (hk : k < 32) : getc r (col.counter_low (64 + k)) = r.block_len k := by
  cells_tac; exact getD_map_range_of _ (by unfold col.counter_low; omega) hk _

theorem cell_flags {k : ℕ} (hk : k < 32) : getc r (col.counter_low (96 + k)) = r.flags k := by
  cells_tac; exact getD_map_range_of _ (by unfold col.counter_low; omega) hk _

theorem cell_init0 {j l : ℕ} (hj : j < 4) (hl : l < 2) :
    getc r (col.initial_row0 j l) = r.initial_row0 j l := by
  cells_tac; exact getD_words _ (by unfold col.initial_row0; omega) hj hl _

theorem cell_init2 {j l : ℕ} (hj : j < 4) (hl : l < 2) :
    getc r (col.initial_row2 j l) = r.initial_row2 j l := by
  cells_tac; exact getD_words _ (by unfold col.initial_row2; omega) hj hl _

theorem cell_state {rd s c : ℕ} (hr : rd < 7) (hs : s < 4) (hc : c < 272) :
    getc r (col.state rd s + c) =
      (Blake3Cols.stateCells ([(r.full_rounds rd).state_prime, (r.full_rounds rd).state_middle,
        (r.full_rounds rd).state_middle_prime, (r.full_rounds rd).state_output].getD s
        Blake3Cols.zeroState)).getD c 0 := by
  cells_tac
  have key := getD_flatMap_range (m := 1088) (fun i => length_roundCells (r.full_rounds i)) hr
    (j := 272 * s + c) (by omega) 0
  rw [show col.state rd s + c - 32 * 16 - 128 * 2 - 32 - 32 - 32 - 32 - 2 * 4 - 2 * 4 =
      1088 * rd + (272 * s + c) by
    unfold col.state; omega, key]
  simp only [Blake3Cols.roundCells, List.append_assoc]
  interval_cases s
  · rw [getD_append_lt (by rw [length_stateCells]; omega)]; simp
  · rw [getD_append_le (by rw [length_stateCells]; omega), length_stateCells,
      getD_append_lt (by rw [length_stateCells]; omega)]; simp
  · rw [getD_append_le (by rw [length_stateCells]; omega), length_stateCells,
      getD_append_le (by rw [length_stateCells]; omega), length_stateCells,
      getD_append_lt (by rw [length_stateCells]; omega)]; simp [show 544 + c - 272 - 272 = c by omega]
  · rw [getD_append_le (by rw [length_stateCells]; omega), length_stateCells,
      getD_append_le (by rw [length_stateCells]; omega), length_stateCells,
      getD_append_le (by rw [length_stateCells]; omega), length_stateCells]
    simp [show 816 + c - 272 - 272 - 272 = c by omega]

theorem cell_helpers {j k : ℕ} (hj : j < 4) (hk : k < 32) :
    getc r (col.final_round_helpers j k) = r.final_round_helpers j k := by
  cells_tac; exact getD_words _ (by unfold col.final_round_helpers; omega) hj hk _

theorem cell_outputs {q j k : ℕ} (hq : q < 4) (hj : j < 4) (hk : k < 32) :
    getc r (col.outputs q j k) = r.outputs q j k := by
  cells_tac
  rw [getD_words _ (j := q) (k := 32 * j + k) (by unfold col.outputs; omega) hq (by omega)]
  congr 1 <;> omega

end cells

end Plonky3Lean.Proofs.Blake3Air
