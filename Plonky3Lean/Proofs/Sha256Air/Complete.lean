module

public import Plonky3Lean.Proofs.Sha256Air.GenSat
public import Plonky3Lean.Proofs.Sha256Air.Sound
public import Plonky3Lean.Proofs.Air.Check

@[expose] public section

/-!
# Completeness of the SHA-256 AIR over a prime field

The generator panics unless the number of inputs is a power of two.

Otherwise its trace satisfies the AIR in every field, and the debug checker accepts it.
-/

set_option linter.unusedSectionVars false

namespace Plonky3Lean.Proofs.Sha256Air

open p3_air.builder.mirror p3_air.air.mirror p3_sha256_air.mirror Plonky3Lean.Spec.Air
open Plonky3Lean.Proofs.Air
open Plonky3Lean.Proofs.KeccakAir (rowOf satisfies_iff_rows getD_map_range_of)

variable {F : Type} [Field F]

/-- The input count is a power of two. -/
def IsPow2 (n : ℕ) : Prop := n ≠ 0 ∧ 2 ^ Nat.log 2 n = n

instance (n : ℕ) : Decidable (IsPow2 n) := by unfold IsPow2; infer_instance

/-- The trace of a list of rows. -/
def matOf (rows : List (Sha256Cols F)) : Mat F := ⟨NUM_SHA256_COLS, rows.flatMap Sha256Cols.cells⟩

/-- The generator panics exactly when the number of inputs is not a power of two. -/
theorem generate_eq (inputs : List (List p3_sha256_air.mirror.Word)) (e : ℕ) :
    generate_trace_rows (F := F) inputs e =
      if IsPow2 inputs.length then some (matOf (inputs.map (genRow (F := F)))) else none := by
  unfold generate_trace_rows IsPow2
  split_ifs <;> rfl

theorem matOf_height (rows : List (Sha256Cols F)) : (matOf rows).height = rows.length := by
  simp only [Mat.height, matOf, NUM_SHA256_COLS, List.length_flatMap, length_cells, List.map_const',
    List.sum_replicate, smul_eq_mul]
  simp

theorem matOf_cell (rows : List (Sha256Cols F)) {i c : ℕ} (hi : i < rows.length)
    (hc : c < NUM_SHA256_COLS) : ((matOf rows).row i).getD c 0 = getc (rows.getD i Sha256Cols.zero) c := by
  have hk : i * NUM_SHA256_COLS + c < NUM_SHA256_COLS * rows.length := by
    have h1 := Nat.mul_le_mul_right NUM_SHA256_COLS (Nat.succ_le_of_lt hi)
    rw [Nat.succ_mul, Nat.mul_comm rows.length] at h1
    omega
  simp only [Mat.row, matOf, getc]
  rw [List.getD_eq_getElem?_getD, List.getElem?_take, ite_eq_left hc, List.getElem?_drop,
    ← List.getD_eq_getElem?_getD,
    Plonky3Lean.Proofs.Keccak.getD_flatMap_uniform _ _ (fun r => length_cells r) _ _ _ hk,
    show (i * NUM_SHA256_COLS + c) / NUM_SHA256_COLS = i by
      rw [Nat.mul_comm, Nat.mul_add_div (by simp [NUM_SHA256_COLS]), Nat.div_eq_of_lt hc, add_zero],
    show (i * NUM_SHA256_COLS + c) % NUM_SHA256_COLS = c by
      rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hc]]

theorem getc_of_le (r : Sha256Cols F) {c : ℕ} (hc : NUM_SHA256_COLS ≤ c) : getc r c = 0 := by
  rw [getc, List.getD_eq_default _ _ (by rw [length_cells]; exact hc)]

/-- The current row the row builder reads is the row's cells. -/
theorem cur_matOf [Inhabited F] (rows : List (Sha256Cols F)) {i : ℕ} (hi : i < rows.length) :
    rowOf (rowEnv (instOf sha256Air (matOf rows) []) i) (AirLayout.from_air (sha256Air (F := F))) 0 =
      getc (rows.getD i Sha256Cols.zero) := by
  funext c
  simp only [rowOf, rowEnv, instOf, AirLayout.from_air, sha256Air]
  by_cases hc : c < NUM_SHA256_COLS
  · rw [getD_map_range_of _ rfl hc, matOf_cell rows hi hc]
  · simp [hc, getc_of_le _ (Nat.le_of_not_lt hc)]

/-- Completeness: on a power-of-two number of inputs, the generator's trace satisfies the AIR, in every field. -/
theorem complete [Inhabited F] {inputs : List (List p3_sha256_air.mirror.Word)}
    (h : IsPow2 inputs.length) (e : ℕ) :
    ∃ M, generate_trace_rows (F := F) inputs e = some M ∧
      Satisfies (constraints sha256Air) (instOf sha256Air M []) := by
  refine ⟨matOf (inputs.map (genRow (F := F))), by simp only [generate_eq, h, ↓reduceIte], ?_⟩
  rw [satisfies_iff_rows]
  change ∀ i < (matOf (inputs.map (genRow (F := F)))).height, _
  rw [matOf_height]
  intro i hi
  apply (eval_iff _ _).mpr
  rw [cur_matOf _ hi, List.getD_eq_getElem _ _ hi, List.getElem_map]
  exact gen_rowSpec _

/-- The debug checker accepts the generator's trace. -/
theorem check_complete [Inhabited F] [DecidableEq F] {inputs : List (List p3_sha256_air.mirror.Word)}
    (h : IsPow2 inputs.length) (e : ℕ) :
    ∃ M, generate_trace_rows (F := F) inputs e = some M ∧ check_constraints sha256Air M [] = .ok () := by
  obtain ⟨M, hM, hs⟩ := complete (F := F) h e
  refine ⟨M, hM, ?_⟩
  simp only [generate_eq, h, ↓reduceIte, Option.some.injEq] at hM
  subst hM
  have hsh : Shapes sha256Air (matOf (inputs.map (genRow (F := F)))) [] :=
    ⟨rfl, by simp [sha256Air], fun _ => rfl, rfl, rfl⟩
  rw [check_constraints_ok_iff hsh]
  refine ⟨by simp [PrepHeight, sha256Air], by simp [PeriodicShapes, sha256Air], ?_, hs⟩
  simp [boundary_io_mismatches, validate, sha256Air]
  rfl

/-- The generator panics when the number of inputs is not a power of two. -/
theorem generate_panics {inputs : List (List p3_sha256_air.mirror.Word)} (h : ¬ IsPow2 inputs.length)
    (e : ℕ) : generate_trace_rows (F := F) inputs e = none := by
  simp only [generate_eq, h, ↓reduceIte]

end Plonky3Lean.Proofs.Sha256Air
