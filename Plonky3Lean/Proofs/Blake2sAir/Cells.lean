module

public import P3Blake2sAir
public import Plonky3Lean.Proofs.KeccakAir.Cells

@[expose] public section

/-!
# The cells of a row of the BLAKE2s AIR

A row lays its fields out in declaration order.

Cell `c` of the row is the entry that the column index `c` names.

```text
    0 .. 256      chaining value, 8 words of 32 bits
    256 .. 768    message block, 16 words
    768 .. 800    counter, low word
    800 .. 832    counter, high word
    832           final-block flag
    833 ..        80 G steps of 190 cells, round by round
```
-/

set_option linter.unusedSectionVars false

namespace Plonky3Lean.Proofs.Blake2sAir

open p3_blake2s_air.mirror Blake2sBinaryCols
open Plonky3Lean.Proofs.KeccakAir (length_flatMap_range getD_flatMap_range getD_append_le getD_append_lt
  getD_map_range_of)

variable {T : Type}

theorem length_cellBlock (f : ℕ → ℕ → T) (n w : ℕ) : (cellBlock f n w).length = w * n := by
  rw [cellBlock, length_flatMap_range (m := w)]; simp

/-- Close a bound on a position within the concatenated cells. -/
macro "len_tac" : tactic => `(tactic| ((try simp only [List.length_append, List.length_map,
  List.length_range, length_cellBlock, List.length_singleton, col.chaining_value, col.block,
  col.counter_low, col.counter_high, col.last_block, col.g_base] at *) <;> omega))

theorem getD_cellBlock (f : ℕ → ℕ → T) {n w i j c : ℕ} (hi : i < n) (hj : j < w) (hc : c = w * i + j)
    (d : T) : (cellBlock f n w).getD c d = f i j := by
  subst hc
  rw [cellBlock, getD_flatMap_range (m := w) (by simp) hi hj]
  simp [hj]

theorem length_gCells (g : Blake2sBinaryGCols T) : (gCells g).length = 190 := by simp [gCells]

theorem length_roundCells (r : ℕ → Blake2sBinaryGCols T) :
    ((List.range G_PER_ROUND).flatMap fun g => gCells (r g)).length = 1520 := by
  rw [length_flatMap_range (m := 190) (fun _ => length_gCells _)]; rfl

theorem length_rounds (r : ℕ → ℕ → Blake2sBinaryGCols T) :
    ((List.range NUM_ROUNDS).flatMap fun round =>
      (List.range G_PER_ROUND).flatMap fun g => gCells (r round g)).length = 15200 := by
  rw [length_flatMap_range (m := 1520) (fun _ => length_roundCells _)]; rfl

theorem length_cells (r : Blake2sBinaryCols T) : r.cells.length = NUM_BLAKE2S_BINARY_COLS := by
  simp only [cells, List.length_append, length_cellBlock, List.length_map, List.length_range,
    List.length_singleton, length_rounds]
  rfl

/-- The cells of one G step, field by field. -/
theorem getD_gCells [Zero T] (g : Blake2sBinaryGCols T) :
    (∀ c < 31, (gCells g).getD c 0 = g.add1_carries c) ∧
    (∀ b < 32, (gCells g).getD (31 + b) 0 = g.d1 b) ∧
    (∀ b < 32, (gCells g).getD (63 + b) 0 = g.b1 b) ∧
    (∀ c < 31, (gCells g).getD (95 + c) 0 = g.add2_carries c) ∧
    (∀ b < 32, (gCells g).getD (126 + b) 0 = g.d2 b) ∧
    (∀ b < 32, (gCells g).getD (158 + b) 0 = g.b2 b) := by
  unfold gCells
  simp only [List.append_assoc]
  refine ⟨fun c hc => ?_, fun b hb => ?_, fun b hb => ?_, fun c hc => ?_, fun b hb => ?_, fun b hb => ?_⟩
  · rw [getD_append_lt (by len_tac)]; exact getD_map_range_of _ rfl hc _
  · rw [getD_append_le (by len_tac), getD_append_lt (by len_tac)]
    exact getD_map_range_of _ (by len_tac) hb _
  · rw [getD_append_le (by len_tac), getD_append_le (by len_tac), getD_append_lt (by len_tac)]
    exact getD_map_range_of _ (by len_tac) hb _
  · rw [getD_append_le (by len_tac), getD_append_le (by len_tac), getD_append_le (by len_tac),
      getD_append_lt (by len_tac)]
    exact getD_map_range_of _ (by len_tac) hc _
  · rw [getD_append_le (by len_tac), getD_append_le (by len_tac), getD_append_le (by len_tac),
      getD_append_le (by len_tac), getD_append_lt (by len_tac)]
    exact getD_map_range_of _ (by len_tac) hb _
  · rw [getD_append_le (by len_tac), getD_append_le (by len_tac), getD_append_le (by len_tac),
      getD_append_le (by len_tac), getD_append_le (by len_tac)]
    exact getD_map_range_of _ (by len_tac) hb _

section cells

variable [Zero T] (r : Blake2sBinaryCols T)

theorem cell_cv {i b : ℕ} (hi : i < 8) (hb : b < 32) :
    r.cells.getD (col.chaining_value i b) 0 = r.chaining_value i b := by
  rw [cells, List.append_assoc, List.append_assoc, List.append_assoc, List.append_assoc,
    getD_append_lt (by len_tac)]
  exact getD_cellBlock _ hi hb (by simp only [col.chaining_value]) _

theorem cell_block {i b : ℕ} (hi : i < 16) (hb : b < 32) :
    r.cells.getD (col.block i b) 0 = r.block i b := by
  rw [cells, List.append_assoc, List.append_assoc, List.append_assoc, List.append_assoc,
    getD_append_le (by len_tac),
    getD_append_lt (by len_tac)]
  exact getD_cellBlock _ hi hb (by len_tac) _

theorem cell_counter_low {b : ℕ} (hb : b < 32) :
    r.cells.getD (col.counter_low b) 0 = r.counter_low b := by
  rw [cells, List.append_assoc, List.append_assoc, List.append_assoc, List.append_assoc,
    getD_append_le (by len_tac),
    getD_append_le (by len_tac),
    getD_append_lt (by len_tac)]
  exact getD_map_range_of _ (by len_tac) hb _

theorem cell_counter_high {b : ℕ} (hb : b < 32) :
    r.cells.getD (col.counter_high b) 0 = r.counter_high b := by
  rw [cells, List.append_assoc, List.append_assoc, List.append_assoc, List.append_assoc,
    getD_append_le (by len_tac),
    getD_append_le (by len_tac),
    getD_append_le (by len_tac),
    getD_append_lt (by len_tac)]
  exact getD_map_range_of _ (by len_tac) hb _

theorem cell_last_block : r.cells.getD col.last_block 0 = r.last_block := by
  rw [cells, List.append_assoc, List.append_assoc, List.append_assoc, List.append_assoc,
    getD_append_le (by len_tac),
    getD_append_le (by len_tac),
    getD_append_le (by len_tac),
    getD_append_le (by len_tac),
    getD_append_lt (by len_tac)]
  simp [length_cellBlock, col.last_block]

/-- Cell `off` of G step `g` of round `rd`. -/
theorem cell_g {rd g off : ℕ} (hr : rd < 10) (hg : g < 8) (ho : off < 190) :
    r.cells.getD (col.g_base rd g + off) 0 = (gCells (r.rounds rd g)).getD off 0 := by
  rw [cells, getD_append_le (by len_tac)]
  simp only [List.length_append, length_cellBlock, List.length_map, List.length_range,
    List.length_singleton, col.g_base]
  rw [show 833 + 190 * (8 * rd + g) + off - (32 * 8 + 32 * 16 + 32 + 32 + 1) = 1520 * rd + (190 * g + off)
      by omega, getD_flatMap_range (m := 1520) (n := NUM_ROUNDS) (fun _ => length_roundCells _) hr (by omega),
    getD_flatMap_range (m := 190) (n := G_PER_ROUND) (fun _ => length_gCells _) hg ho]

end cells

end Plonky3Lean.Proofs.Blake2sAir
