module

public import P3KeccakAir
public import Mathlib.Data.List.GetD
public import Mathlib.Algebra.BigOperators.Group.List.Basic

@[expose] public section

/-!
# The cells of a row

A row of the column struct lays its fields out in declaration order.

Cell `c` of the row is the field entry that the column index `c` names.
-/

namespace Plonky3Lean.Proofs.KeccakAir

open p3_keccak_air.mirror

variable {T : Type}

theorem length_flatMap_range {G : ℕ → List T} {m : ℕ} (hG : ∀ i, (G i).length = m) (n : ℕ) :
    ((List.range n).flatMap G).length = m * n := by
  induction n with
  | zero => simp
  | succ n ih => simp [List.range_succ, List.flatMap_append, ih, hG, Nat.mul_succ]

theorem getD_flatMap_range {G : ℕ → List T} {m : ℕ} (hG : ∀ i, (G i).length = m) {n i j : ℕ}
    (hi : i < n) (hj : j < m) (d : T) :
    ((List.range n).flatMap G).getD (m * i + j) d = (G i).getD j d := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [List.range_succ, List.flatMap_append]
    rcases Nat.lt_or_ge i n with h | h
    · rw [List.getD_append _ _ _ _ (by rw [length_flatMap_range hG]; nlinarith), ih h]
    · obtain rfl : i = n := by omega
      rw [List.getD_append_right _ _ _ _ (by rw [length_flatMap_range hG]; omega),
        length_flatMap_range hG]
      simp

theorem length_limbCells (f : ℕ → ℕ → ℕ → T) : (KeccakCols.limbCells f).length = 100 := by
  rw [KeccakCols.limbCells, length_flatMap_range (m := 20)]
  intro y; rw [length_flatMap_range (m := 4)]; simp

theorem getD_limbCells (f : ℕ → ℕ → ℕ → T) {y x limb : ℕ} (hy : y < 5) (hx : x < 5) (hl : limb < 4)
    (d : T) : (KeccakCols.limbCells f).getD (20 * y + 4 * x + limb) d = f y x limb := by
  have h4 : ∀ x, ((List.range 4).map (f y x)).length = 4 := by simp
  have h20 : ∀ y, ((List.range 5).flatMap fun x => (List.range 4).map (f y x)).length = 20 := by
    intro y; rw [length_flatMap_range (m := 4)]; simp
  rw [KeccakCols.limbCells, Nat.add_assoc, getD_flatMap_range h20 hy (by omega),
    getD_flatMap_range h4 hx hl]
  simp [hl]

theorem length_lanes (f : ℕ → ℕ → T) : ((List.range 5).flatMap fun x => (List.range 64).map (f x)).length = 320 := by
  rw [length_flatMap_range (m := 64)]; simp

theorem length_lanes3 (f : ℕ → ℕ → ℕ → T) :
    ((List.range 5).flatMap fun y => (List.range 5).flatMap fun x => (List.range 64).map (f y x)).length =
      1600 := by
  rw [length_flatMap_range (m := 320)]; intro y; exact length_lanes _

theorem getD_lanes (f : ℕ → ℕ → T) {x z : ℕ} (hx : x < 5) (hz : z < 64) (d : T) :
    ((List.range 5).flatMap fun x => (List.range 64).map (f x)).getD (64 * x + z) d = f x z := by
  rw [getD_flatMap_range (m := 64) (by simp) hx hz]; simp [hz]

theorem getD_lanes3 (f : ℕ → ℕ → ℕ → T) {y x z : ℕ} (hy : y < 5) (hx : x < 5) (hz : z < 64) (d : T) :
    ((List.range 5).flatMap fun y => (List.range 5).flatMap fun x => (List.range 64).map (f y x)).getD
      (320 * y + 64 * x + z) d = f y x z := by
  rw [Nat.add_assoc, getD_flatMap_range (m := 320) (fun y => length_lanes _) hy (by omega),
    getD_lanes _ hx hz]

theorem getD_append_le {l l' : List T} {n : ℕ} (h : l.length ≤ n) (d : T) :
    (l ++ l').getD n d = l'.getD (n - l.length) d := List.getD_append_right _ _ _ _ h

theorem getD_append_lt {l l' : List T} {n : ℕ} (h : n < l.length) (d : T) :
    (l ++ l').getD n d = l.getD n d := List.getD_append _ _ _ _ h

theorem length_cells (r : KeccakCols T) : r.cells.length = NUM_KECCAK_COLS := by
  simp [p3_keccak_air.mirror.KeccakCols.cells, length_limbCells, NUM_KECCAK_COLS]

theorem getD_limbCells_of (f : ℕ → ℕ → ℕ → T) {n y x limb : ℕ} (hn : n = 20 * y + 4 * x + limb)
    (hy : y < 5) (hx : x < 5) (hl : limb < 4) (d : T) :
    (KeccakCols.limbCells f).getD n d = f y x limb := hn ▸ getD_limbCells f hy hx hl d

theorem getD_lanes_of (f : ℕ → ℕ → T) {n x z : ℕ} (hn : n = 64 * x + z) (hx : x < 5) (hz : z < 64)
    (d : T) : ((List.range 5).flatMap fun x => (List.range 64).map (f x)).getD n d = f x z :=
  hn ▸ getD_lanes f hx hz d

theorem getD_lanes3_of (f : ℕ → ℕ → ℕ → T) {n y x z : ℕ} (hn : n = 320 * y + 64 * x + z)
    (hy : y < 5) (hx : x < 5) (hz : z < 64) (d : T) :
    ((List.range 5).flatMap fun y => (List.range 5).flatMap fun x => (List.range 64).map (f y x)).getD
      n d = f y x z := hn ▸ getD_lanes3 f hy hx hz d

theorem getD_map_range_of (f : ℕ → T) {n i m : ℕ} (hn : n = i) (hi : i < m) (d : T) :
    ((List.range m).map f).getD n d = f i := by
  subst hn; simp [hi]

section cells

variable [Zero T] (r : KeccakCols T)


/-- Unfold the cells into their blocks and walk to the block a column index lies in. -/
macro "cells_tac" : tactic => `(tactic| (
  simp only [p3_keccak_air.mirror.KeccakCols.cells, List.append_assoc]
  repeat (first
    | rw [getD_append_le (by simp only [List.length_map, List.length_range, List.length_cons,
        List.length_nil, length_limbCells, length_lanes, length_lanes3, col.step_flags, col.export_,
        col.preimage, col.a, col.c, col.c_prime, col.a_prime, col.a_prime_prime,
        col.a_prime_prime_0_0_bits, col.a_prime_prime_prime_0_0_limbs]; omega)]
    | rw [getD_append_lt (by simp only [List.length_map, List.length_range, List.length_cons,
        List.length_nil, length_limbCells, length_lanes, length_lanes3, col.step_flags, col.export_,
        col.preimage, col.a, col.c, col.c_prime, col.a_prime, col.a_prime_prime,
        col.a_prime_prime_0_0_bits, col.a_prime_prime_prime_0_0_limbs]; omega)])
  simp only [List.length_map, List.length_range, List.length_cons, List.length_nil, length_limbCells,
    length_lanes, length_lanes3, col.step_flags, col.export_, col.preimage, col.a, col.c, col.c_prime,
    col.a_prime, col.a_prime_prime, col.a_prime_prime_0_0_bits, col.a_prime_prime_prime_0_0_limbs]))

theorem cell_step_flags {i : ℕ} (hi : i < 24) : r.cells.getD (col.step_flags i) 0 = r.step_flags i := by
  cells_tac; exact getD_map_range_of _ rfl hi _

theorem cell_export : r.cells.getD col.export_ 0 = r.export_ := by
  cells_tac; rfl

theorem cell_preimage {y x limb : ℕ} (hy : y < 5) (hx : x < 5) (hl : limb < 4) :
    r.cells.getD (col.preimage y x limb) 0 = r.preimage y x limb := by
  cells_tac; exact getD_limbCells_of _ (by omega) hy hx hl _

theorem cell_a {y x limb : ℕ} (hy : y < 5) (hx : x < 5) (hl : limb < 4) :
    r.cells.getD (col.a y x limb) 0 = r.a y x limb := by
  cells_tac; exact getD_limbCells_of _ (by omega) hy hx hl _

theorem cell_c {x z : ℕ} (hx : x < 5) (hz : z < 64) : r.cells.getD (col.c x z) 0 = r.c x z := by
  cells_tac; exact getD_lanes_of _ (by omega) hx hz _

theorem cell_c_prime {x z : ℕ} (hx : x < 5) (hz : z < 64) :
    r.cells.getD (col.c_prime x z) 0 = r.c_prime x z := by
  cells_tac; exact getD_lanes_of _ (by omega) hx hz _

theorem cell_a_prime {y x z : ℕ} (hy : y < 5) (hx : x < 5) (hz : z < 64) :
    r.cells.getD (col.a_prime y x z) 0 = r.a_prime y x z := by
  cells_tac; exact getD_lanes3_of _ (by omega) hy hx hz _

theorem cell_a_prime_prime {y x limb : ℕ} (hy : y < 5) (hx : x < 5) (hl : limb < 4) :
    r.cells.getD (col.a_prime_prime y x limb) 0 = r.a_prime_prime y x limb := by
  cells_tac; exact getD_limbCells_of _ (by omega) hy hx hl _

theorem cell_bits {z : ℕ} (hz : z < 64) :
    r.cells.getD (col.a_prime_prime_0_0_bits z) 0 = r.a_prime_prime_0_0_bits z := by
  cells_tac; exact getD_map_range_of _ (by omega) hz _

theorem cell_limbs {limb : ℕ} (hl : limb < 4) :
    r.cells.getD (col.a_prime_prime_prime_0_0_limbs limb) 0 = r.a_prime_prime_prime_0_0_limbs limb := by
  cells_tac; exact getD_map_range_of _ (by omega) hl _

end cells

end Plonky3Lean.Proofs.KeccakAir
