module

public import Plonky3Lean.Proofs.Blake3Air.Binary.GenRow
public import Plonky3Lean.Proofs.Blake3Air.Cells

@[expose] public section

/-!
# The cells of a characteristic-2 row

A row of the column struct lays its fields out in declaration order.

Cell `c` of the row is the field entry that the column index `c` names.
-/

set_option linter.unusedSectionVars false

namespace Plonky3Lean.Proofs.Blake3Air.Binary

open p3_blake3_air.mirror p3_blake3_air.mirror.binary Plonky3Lean.Proofs.KeccakAir Plonky3Lean.Proofs.Blake3Air

variable {T : Type}

theorem length_gcells (g : Blake3BinaryGCols T) : g.cells.length = 190 := by
  simp [Blake3BinaryGCols.cells]

theorem length_roundG (f : ℕ → Blake3BinaryGCols T) :
    ((List.range 8).flatMap fun g => (f g).cells).length = 1520 := by
  rw [length_flatMap_range (m := 190) (fun g => length_gcells _)]

theorem length_allG (f : ℕ → ℕ → Blake3BinaryGCols T) :
    ((List.range 7).flatMap fun r => (List.range 8).flatMap fun g => (f r g).cells).length = 10640 := by
  rw [length_flatMap_range (m := 1520) (fun r => length_roundG _)]

theorem length_cellsB (r : Blake3BinaryCols T) : r.cells.length = NUM_BLAKE3_BINARY_COLS := by
  simp only [Blake3BinaryCols.cells, List.length_append, length_words, length_allG, List.length_map,
    List.length_range, NUM_BLAKE3_BINARY_COLS]

/-- Cell c of a row. -/
abbrev getcB [Zero T] (r : Blake3BinaryCols T) (c : ℕ) : T := r.cells.getD c 0

section cells

variable [Zero T] (r : Blake3BinaryCols T)

theorem cellB_cv {i k : ℕ} (hi : i < 8) (hk : k < 32) :
    getcB r (col.chaining_value i k) = r.chaining_value i k := by
  unfold getcB Blake3BinaryCols.cells
  simp only [List.append_assoc]
  rw [getD_append_lt (by rw [length_words]; unfold col.chaining_value; omega)]
  exact getD_words _ (by unfold col.chaining_value; omega) hi hk _

theorem cellB_block {i k : ℕ} (hi : i < 16) (hk : k < 32) : getcB r (col.block i k) = r.block i k := by
  unfold getcB Blake3BinaryCols.cells
  simp only [List.append_assoc]
  rw [getD_append_le (by rw [length_words]; unfold col.block; omega), length_words,
    getD_append_lt (by rw [length_words]; unfold col.block; omega)]
  exact getD_words _ (by unfold col.block; omega) hi hk _

theorem cellB_row3 {j k : ℕ} (hj : j < 4) (hk : k < 32) :
    getcB r (binary.col.counter_low (32 * j + k)) =
      [r.counter_low k, r.counter_high k, r.block_len k, r.flags k].getD j 0 := by
  unfold getcB Blake3BinaryCols.cells
  simp only [List.append_assoc]
  rw [getD_append_le (by rw [length_words]; unfold binary.col.counter_low; omega), length_words,
    getD_append_le (by rw [length_words]; unfold binary.col.counter_low; omega), length_words]
  simp only [binary.col.counter_low]
  interval_cases j
  · rw [getD_append_lt (by simp; omega)]; exact getD_map_range_of _ (by omega) hk _
  · rw [getD_append_le (by simp; omega), getD_append_lt (by simp; omega)]
    exact getD_map_range_of _ (by simp; omega) hk _
  · rw [getD_append_le (by simp; omega), getD_append_le (by simp; omega), getD_append_lt (by simp; omega)]
    exact getD_map_range_of _ (by simp; omega) hk _
  · rw [getD_append_le (by simp; omega), getD_append_le (by simp; omega), getD_append_le (by simp; omega),
      getD_append_lt (by simp; omega)]
    exact getD_map_range_of _ (by simp; omega) hk _

theorem cellB_g {rd g c : ℕ} (hr : rd < 7) (hg : g < 8) (hc : c < 190) :
    getcB r (col.g rd g + c) = (r.rounds rd g).cells.getD c 0 := by
  unfold getcB Blake3BinaryCols.cells
  simp only [List.append_assoc]
  rw [getD_append_le (by rw [length_words]; unfold col.g; omega), length_words,
    getD_append_le (by rw [length_words]; unfold col.g; omega), length_words]
  repeat rw [getD_append_le (by simp; unfold col.g; omega)]
  simp only [List.length_map, List.length_range]
  rw [show col.g rd g + c - 32 * 8 - 32 * 16 - 32 - 32 - 32 - 32 = 1520 * rd + (190 * g + c) by
      unfold col.g; omega,
    getD_flatMap_range (m := 1520) (fun r => length_roundG _) hr (by omega),
    getD_flatMap_range (m := 190) (fun g => length_gcells _) hg hc]

variable {rd g : ℕ} (hr : rd < 7) (hg : g < 8)
include hr hg

theorem cellB_add1 {k : ℕ} (hk : k < 31) :
    getcB r (col.add1_carries rd g k) = (r.rounds rd g).add1_carries k := by
  rw [col.add1_carries, cellB_g r hr hg (by omega), Blake3BinaryGCols.cells]
  simp only [List.append_assoc]
  rw [getD_append_lt (by simp only [List.length_map, List.length_range]; omega)]; exact getD_map_range_of _ rfl hk _

theorem cellB_d1 {k : ℕ} (hk : k < 32) : getcB r (col.d1 rd g k) = (r.rounds rd g).d1 k := by
  rw [col.d1, Nat.add_assoc, cellB_g r hr hg (by omega), Blake3BinaryGCols.cells]
  simp only [List.append_assoc]
  rw [getD_append_le (by simp only [List.length_map, List.length_range]; omega), getD_append_lt (by simp only [List.length_map, List.length_range]; omega)]
  exact getD_map_range_of _ (by simp only [List.length_map, List.length_range]; omega) hk _

theorem cellB_b1 {k : ℕ} (hk : k < 32) : getcB r (col.b1 rd g k) = (r.rounds rd g).b1 k := by
  rw [col.b1, Nat.add_assoc, cellB_g r hr hg (by omega), Blake3BinaryGCols.cells]
  simp only [List.append_assoc]
  rw [getD_append_le (by simp only [List.length_map, List.length_range]; omega), getD_append_le (by simp only [List.length_map, List.length_range]; omega), getD_append_lt (by simp only [List.length_map, List.length_range]; omega)]
  exact getD_map_range_of _ (by simp only [List.length_map, List.length_range]; omega) hk _

theorem cellB_add2 {k : ℕ} (hk : k < 31) :
    getcB r (col.add2_carries rd g k) = (r.rounds rd g).add2_carries k := by
  rw [col.add2_carries, Nat.add_assoc, cellB_g r hr hg (by omega), Blake3BinaryGCols.cells]
  simp only [List.append_assoc]
  rw [getD_append_le (by simp only [List.length_map, List.length_range]; omega), getD_append_le (by simp only [List.length_map, List.length_range]; omega), getD_append_le (by simp only [List.length_map, List.length_range]; omega),
    getD_append_lt (by simp only [List.length_map, List.length_range]; omega)]
  exact getD_map_range_of _ (by simp only [List.length_map, List.length_range]; omega) hk _

theorem cellB_d2 {k : ℕ} (hk : k < 32) : getcB r (col.d2 rd g k) = (r.rounds rd g).d2 k := by
  rw [col.d2, Nat.add_assoc, cellB_g r hr hg (by omega), Blake3BinaryGCols.cells]
  simp only [List.append_assoc]
  rw [getD_append_le (by simp only [List.length_map, List.length_range]; omega), getD_append_le (by simp only [List.length_map, List.length_range]; omega), getD_append_le (by simp only [List.length_map, List.length_range]; omega),
    getD_append_le (by simp only [List.length_map, List.length_range]; omega), getD_append_lt (by simp only [List.length_map, List.length_range]; omega)]
  exact getD_map_range_of _ (by simp only [List.length_map, List.length_range]; omega) hk _

theorem cellB_b2 {k : ℕ} (hk : k < 32) : getcB r (col.b2 rd g k) = (r.rounds rd g).b2 k := by
  rw [col.b2, Nat.add_assoc, cellB_g r hr hg (by omega), Blake3BinaryGCols.cells]
  simp only [List.append_assoc]
  rw [getD_append_le (by simp only [List.length_map, List.length_range]; omega), getD_append_le (by simp only [List.length_map, List.length_range]; omega), getD_append_le (by simp only [List.length_map, List.length_range]; omega),
    getD_append_le (by simp only [List.length_map, List.length_range]; omega), getD_append_le (by simp only [List.length_map, List.length_range]; omega)]
  exact getD_map_range_of _ (by simp only [List.length_map, List.length_range]; omega) hk _

end cells

end Plonky3Lean.Proofs.Blake3Air.Binary
