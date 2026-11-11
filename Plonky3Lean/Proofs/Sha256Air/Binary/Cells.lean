module

public import Plonky3Lean.Proofs.Sha256Air.Cells

@[expose] public section

/-!
# The cells of a row of the characteristic-2 AIR

A row lays its fields out in declaration order, and cell `c` is the entry the column index `c` names.
-/

set_option linter.unusedSectionVars false

namespace Plonky3Lean.Proofs.Sha256Air.Binary

open p3_sha256_air.mirror.binary
open Plonky3Lean.Proofs.Sha256Air (length_block getD_block)
open Plonky3Lean.Proofs.KeccakAir (length_flatMap_range getD_flatMap_range getD_append_le getD_append_lt
  getD_map_range_of)

variable {T : Type}

theorem length_schedB (s : ℕ → Sha256BinaryScheduleCols T) :
    ((List.range 48).flatMap fun i =>
      p3_sha256_air.mirror.Sha256Cols.block (s i).carries SCHEDULE_CARRIES 31).length = 2976 := by
  rw [length_flatMap_range (m := 62) (fun i => by rw [length_block]; rfl)]

theorem length_roundCellsB (r : Sha256BinaryRoundCols T) : (Sha256BinaryCols.roundCells r).length = 220 := by
  simp [Sha256BinaryCols.roundCells, length_block, T1_CARRIES]

theorem length_roundsB (r : ℕ → Sha256BinaryRoundCols T) :
    ((List.range 64).flatMap fun t => Sha256BinaryCols.roundCells (r t)).length = 14080 := by
  rw [length_flatMap_range (m := 220) (fun t => length_roundCellsB _)]

theorem length_cellsB (r : Sha256BinaryCols T) : r.cells.length = NUM_SHA256_BINARY_COLS := by
  rw [Sha256BinaryCols.cells, show p3_sha256_air.mirror.SCHEDULE_EXTENSIONS = 48 from rfl,
    show p3_sha256_air.mirror.NUM_COMPRESSION_ROUNDS = 64 from rfl]
  simp only [List.length_append, length_block, length_schedB, length_roundsB]
  rfl

section cells

variable [Zero T] (r : Sha256BinaryCols T)

theorem getD_round_field (rr : ℕ → Sha256BinaryRoundCols T) {t off : ℕ} (ht : t < 64) (ho : off < 220) :
    ((List.range 64).flatMap fun t => Sha256BinaryCols.roundCells (rr t)).getD (220 * t + off) 0 =
      (Sha256BinaryCols.roundCells (rr t)).getD off 0 :=
  getD_flatMap_range (m := 220) (fun _ => length_roundCellsB _) ht ho _

theorem getD_sched_field (s : ℕ → Sha256BinaryScheduleCols T) {i off : ℕ} (hi : i < 48) (ho : off < 62) :
    ((List.range 48).flatMap fun i =>
      p3_sha256_air.mirror.Sha256Cols.block (s i).carries SCHEDULE_CARRIES 31).getD (62 * i + off) 0 =
      (p3_sha256_air.mirror.Sha256Cols.block (s i).carries SCHEDULE_CARRIES 31).getD off 0 :=
  getD_flatMap_range (m := 62) (fun i => by rw [length_block]; rfl) hi ho _

/-- Walk the cells' blocks to the one a column index lies in. -/
macro "cellsB_tac" : tactic => `(tactic| (
  simp only [Sha256BinaryCols.cells, p3_sha256_air.mirror.CHAIN_LEN,
    p3_sha256_air.mirror.NUM_COMPRESSION_ROUNDS, p3_sha256_air.mirror.SCHEDULE_EXTENSIONS,
    p3_sha256_air.mirror.BLOCK_WORDS, p3_sha256_air.mirror.STATE_WORDS, Nat.reduceSub, Nat.reduceAdd,
    List.append_assoc]
  repeat (first
    | rw [getD_append_le (by simp only [length_block, length_schedB, length_roundsB, col.a_chain,
        col.e_chain, col.w, col.sched_carries, col.ch, col.maj, col.t1_carries, col.t1, col.new_a_carries,
        col.h_out, p3_sha256_air.mirror.CHAIN_LEN, p3_sha256_air.mirror.STATE_WORDS]; omega)]
    | rw [getD_append_lt (by simp only [length_block, length_schedB, length_roundsB, col.a_chain,
        col.e_chain, col.w, col.sched_carries, col.ch, col.maj, col.t1_carries, col.t1, col.new_a_carries,
        col.h_out, p3_sha256_air.mirror.CHAIN_LEN, p3_sha256_air.mirror.STATE_WORDS]; omega)])
  simp only [length_block, length_schedB, length_roundsB, col.a_chain, col.e_chain, col.w,
    col.sched_carries, col.ch, col.maj, col.t1_carries, col.t1, col.new_a_carries, col.h_out,
    p3_sha256_air.mirror.CHAIN_LEN, p3_sha256_air.mirror.STATE_WORDS]))

theorem cellB_a {k b : ℕ} (hk : k < 68) (hb : b < 32) : r.cells.getD (col.a_chain k b) 0 = r.a_chain k b := by
  cellsB_tac; exact getD_block _ hk hb (by omega) _

theorem cellB_e {k b : ℕ} (hk : k < 68) (hb : b < 32) : r.cells.getD (col.e_chain k b) 0 = r.e_chain k b := by
  cellsB_tac; exact getD_block _ hk hb (by omega) _

theorem cellB_w {t b : ℕ} (ht : t < 64) (hb : b < 32) : r.cells.getD (col.w t b) 0 = r.w t b := by
  cellsB_tac; exact getD_block _ ht hb (by omega) _

theorem cellB_h {i b : ℕ} (hi : i < 8) (hb : b < 32) : r.cells.getD (col.h_out i b) 0 = r.h_out i b := by
  cellsB_tac; exact getD_block _ hi hb (by omega) _

theorem cellB_sched {i j c : ℕ} (hi : i < 48) (hj : j < 2) (hc : c < 31) :
    r.cells.getD (col.sched_carries i j c) 0 = (r.schedule i).carries j c := by
  cellsB_tac
  rw [show 6400 + 62 * i + 31 * j + c - 32 * 68 - 32 * 68 - 32 * 64 = 62 * i + (31 * j + c) by omega,
    getD_sched_field _ hi (by omega)]
  exact getD_block _ (by simpa [SCHEDULE_CARRIES] using hj) hc rfl _

/-- The cells of a round, field by field. -/
theorem getD_roundCellsB (rr : Sha256BinaryRoundCols T) :
    (∀ b < 32, (Sha256BinaryCols.roundCells rr).getD b 0 = rr.ch b) ∧
    (∀ b < 32, (Sha256BinaryCols.roundCells rr).getD (32 + b) 0 = rr.maj b) ∧
    (∀ j < 3, ∀ c < 31, (Sha256BinaryCols.roundCells rr).getD (64 + (31 * j + c)) 0 = rr.t1_carries j c) ∧
    (∀ b < 32, (Sha256BinaryCols.roundCells rr).getD (157 + b) 0 = rr.t1 b) ∧
    (∀ c < 31, (Sha256BinaryCols.roundCells rr).getD (189 + c) 0 = rr.new_a_carries c) := by
  unfold Sha256BinaryCols.roundCells
  simp only [List.append_assoc]
  refine ⟨fun b hb => ?_, fun b hb => ?_, fun j hj c hc => ?_, fun b hb => ?_, fun c hc => ?_⟩
  · rw [getD_append_lt (by simpa using hb)]; exact getD_map_range_of _ rfl hb _
  · rw [getD_append_le (by simp), getD_append_lt (by simpa using hb)]
    exact getD_map_range_of _ (by simp) hb _
  · rw [getD_append_le (by simp; omega), getD_append_le (by simp; omega),
      getD_append_lt (by simp [length_block, T1_CARRIES]; omega)]
    exact getD_block _ (by simpa [T1_CARRIES] using hj) hc (by simp; omega) _
  · rw [getD_append_le (by simp; omega), getD_append_le (by simp; omega),
      getD_append_le (by simp [length_block, T1_CARRIES]; omega),
      getD_append_lt (by simp [length_block, T1_CARRIES]; omega)]
    exact getD_map_range_of _ (by simp [length_block, T1_CARRIES]; omega) hb _
  · rw [getD_append_le (by simp; omega), getD_append_le (by simp; omega),
      getD_append_le (by simp [length_block, T1_CARRIES]; omega),
      getD_append_le (by simp [length_block, T1_CARRIES]; omega)]
    exact getD_map_range_of _ (by simp [length_block, T1_CARRIES]; omega) hc _

theorem cellB_round {t off : ℕ} (ht : t < 64) (ho : off < 220) :
    r.cells.getD (9376 + 220 * t + off) 0 = (Sha256BinaryCols.roundCells (r.rounds t)).getD off 0 := by
  cellsB_tac
  rw [show 9376 + 220 * t + off - 32 * 68 - 32 * 68 - 32 * 64 - 2976 = 220 * t + off by omega,
    getD_round_field _ ht ho]

end cells

end Plonky3Lean.Proofs.Sha256Air.Binary
