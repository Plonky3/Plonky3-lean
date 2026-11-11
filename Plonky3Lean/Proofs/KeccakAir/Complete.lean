module

public import Plonky3Lean.Proofs.KeccakAir.Perm
public import Plonky3Lean.Proofs.KeccakAir.Sound
public import Plonky3Lean.Proofs.Air.Check

@[expose] public section

/-!
# Completeness of the Keccak-f AIR

The generator's trace satisfies the AIR, for any list of inputs and in any field.

Row i of the trace is row i mod 24 of permutation i / 24.

The permutations past the inputs are those of the zero state.
-/

set_option linter.unusedSectionVars false

namespace Plonky3Lean.Proofs.KeccakAir

open p3_air.builder.mirror p3_air.air.mirror p3_keccak_air.mirror Plonky3Lean.Spec.Air
open Plonky3Lean.Proofs.Air

variable {F : Type} [Field F]

/-! ## One row of a permutation -/

section permRow

variable (input : List Word) {k : ℕ} (hk : k < 24)

theorem permRow_flag {r : ℕ} (hr : r < 24) :
    getc (permRow (F := F) input k) (col.step_flags r) = if r = k then 1 else 0 := by
  rw [getc, cell_step_flags _ hr, permRow, gen_step_flags, Function.update_apply]
  rfl

theorem permRow_preimage {y x limb : ℕ} (hy : y < 5) (hx : x < 5) (hl : limb < 4) :
    getc (permRow (F := F) input k) (col.preimage y x limb) = limbsOf (initState input) y x limb := by
  rw [getc, cell_preimage _ hy hx hl, permRow, gen_preimage]; rfl

theorem permRow_a {y x limb : ℕ} (hy : y < 5) (hx : x < 5) (hl : limb < 4) :
    getc (permRow (F := F) input k) (col.a y x limb) = limbsOf (stateAt (F := F) input k) y x limb := by
  rw [getc, cell_a _ hy hx hl, permRow, gen_a]; rfl

theorem permRow_output {y x limb : ℕ} (hy : y < 5) (hx : x < 5) (hl : limb < 4) :
    a_prime_prime_prime (getc (permRow (F := F) input k)) y x limb =
      limbsOf (stateAt (F := F) input (k + 1)) y x limb := by
  have h := congrFun (congrFun (congrFun (appp_eq (baseRow (F := F) input k) k
    (stateAt (F := F) input k)) y) x) limb
  have hs : stateAt (F := F) input (k + 1) = roundW (F := F) (stateAt (F := F) input k) k := by
    simp only [stateAt, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
  rw [hs, ← h]
  unfold a_prime_prime_prime KeccakCols.a_prime_prime_prime'
  split_ifs
  · rw [getc, cell_limbs _ hl]; rfl
  · rw [getc, cell_a_prime_prime _ hy hx hl]; rfl

theorem permRow_export : getc (permRow (F := F) input k) col.export_ = 0 := by
  rw [getc, cell_export, permRow, gen_export]; rfl

end permRow

/-! ## The trace -/

/-- The input of permutation j: the given one, or the zero state past the last. -/
def inputOf (inputs : List (List Word)) (j : ℕ) : List Word := inputs.getD j (List.replicate 25 0)

/-- The rows of the generator's trace. -/
def traceRows (inputs : List (List Word)) : List (KeccakCols F) :=
  inputs.flatMap (fun input => (List.range 24).map (permRow input)) ++
    (List.range ((inputs.length * 24).nextPowerOfTwo - inputs.length * 24)).map
      (fun j => ((List.range 24).map (permRow (List.replicate 25 0))).getD (j % 24) KeccakCols.zero)

theorem generate_eq (inputs : List (List Word)) (e : ℕ) :
    generate_trace_rows (F := F) inputs e = ⟨NUM_KECCAK_COLS, (traceRows inputs).flatMap KeccakCols.cells⟩ := by
  simp only [generate_trace_rows, traceRows, perm_rows]
  rfl

theorem length_traceRows (inputs : List (List Word)) :
    (traceRows (F := F) inputs).length = (inputs.length * 24).nextPowerOfTwo := by
  have h := Nat.le_nextPowerOfTwo (inputs.length * 24)
  simp only [traceRows, List.length_append, List.length_map, List.length_range]
  simp only [List.length_flatMap, List.length_map, List.length_range, List.map_const',
    List.sum_replicate, smul_eq_mul]
  omega

/-- Row i of the trace is row i mod 24 of permutation i / 24. -/
theorem traceRows_getD (inputs : List (List Word)) {i : ℕ}
    (hi : i < (inputs.length * 24).nextPowerOfTwo) :
    (traceRows (F := F) inputs).getD i KeccakCols.zero = permRow (inputOf inputs (i / 24)) (i % 24) := by
  have hlen : (inputs.flatMap (fun input => (List.range 24).map (permRow (F := F) input))).length =
      inputs.length * 24 := by
    simp only [List.length_flatMap, List.length_map, List.length_range, List.map_const',
      List.sum_replicate, smul_eq_mul]
  unfold traceRows
  by_cases hr : i < inputs.length * 24
  · rw [getD_append_lt (by omega), Plonky3Lean.Proofs.Keccak.getD_flatMap_uniform _ _ (m := 24)
      (by simp) _ _ [] (by rw [Nat.mul_comm]; exact hr)]
    have hq : i / 24 < inputs.length := by omega
    simp [inputOf, List.getElem?_eq_getElem hq, List.getElem?_range (Nat.mod_lt i (by omega : 0 < 24))]
  · rw [getD_append_le (by omega), hlen,
      List.getD_eq_getElem _ _ (by simp only [List.length_map, List.length_range]; omega)]
    simp only [List.getElem_map, List.getElem_range]
    rw [getD_map_range_of _ (by omega : (i - inputs.length * 24) % 24 = i % 24) (Nat.mod_lt _ (by omega))]
    have hq : inputs.length ≤ i / 24 := by omega
    simp [inputOf, List.getElem?_eq_none hq]

section mat

variable (rows : List (KeccakCols F))

/-- The trace of a list of rows. -/
def matOf : Mat F := ⟨NUM_KECCAK_COLS, rows.flatMap KeccakCols.cells⟩

theorem matOf_height : (matOf rows).height = rows.length := by
  simp only [Mat.height, matOf, NUM_KECCAK_COLS, List.length_flatMap, length_cells, List.map_const',
    List.sum_replicate, smul_eq_mul]
  simp

theorem matOf_cell {i c : ℕ} (hi : i < rows.length) (hc : c < NUM_KECCAK_COLS) :
    ((matOf rows).row i).getD c 0 = getc (rows.getD i KeccakCols.zero) c := by
  have hk : i * NUM_KECCAK_COLS + c < NUM_KECCAK_COLS * rows.length := by
    have h1 := Nat.mul_le_mul_right NUM_KECCAK_COLS (Nat.succ_le_of_lt hi)
    rw [Nat.succ_mul, Nat.mul_comm rows.length] at h1
    omega
  simp only [Mat.row, matOf, getc]
  rw [List.getD_eq_getElem?_getD, List.getElem?_take, ite_eq_left hc, List.getElem?_drop,
    ← List.getD_eq_getElem?_getD,
    Plonky3Lean.Proofs.Keccak.getD_flatMap_uniform _ _ (fun r => length_cells r) _ _ _ hk,
    show (i * NUM_KECCAK_COLS + c) / NUM_KECCAK_COLS = i by
      rw [Nat.mul_comm, Nat.mul_add_div (by simp [NUM_KECCAK_COLS]), Nat.div_eq_of_lt hc, add_zero],
    show (i * NUM_KECCAK_COLS + c) % NUM_KECCAK_COLS = c by
      rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hc]]

theorem getc_of_le (r : KeccakCols F) {c : ℕ} (hc : NUM_KECCAK_COLS ≤ c) : getc r c = 0 := by
  rw [getc, List.getD_eq_default _ _ (by rw [length_cells]; exact hc)]

/-- The current row the row builder reads is the row's cells. -/
theorem cur_matOf [Inhabited F] {i : ℕ} (hi : i < rows.length) :
    cur (instOf keccakAir (matOf rows) []) i = getc (rows.getD i KeccakCols.zero) := by
  funext c
  simp only [cur, rowOf, rowEnv, instOf, layout, AirLayout.from_air, keccakAir]
  by_cases hc : c < NUM_KECCAK_COLS
  · have hi' : i < (matOf rows).height := by rw [matOf_height]; exact hi
    rw [getD_map_range_of _ rfl hc, matOf_cell rows hi hc]
  · simp [hc, getc_of_le _ (Nat.le_of_not_lt hc)]

end mat

theorem next_matOf [Inhabited F] (rows : List (KeccakCols F)) {i : ℕ} (hi : i < rows.length) :
    rowOf (rowEnv (instOf keccakAir (matOf rows) []) i) (layout (F := F)) 1 =
      getc (rows.getD ((i + 1) % rows.length) KeccakCols.zero) := by
  funext c
  have hn : (i + 1) % rows.length < rows.length := Nat.mod_lt _ (by omega)
  simp only [rowOf, rowEnv, instOf, layout, AirLayout.from_air, keccakAir, matOf_height]
  by_cases hc : c < NUM_KECCAK_COLS
  · rw [getD_map_range_of _ rfl hc, matOf_cell rows hn hc]
  · simp [hc, getc_of_le _ (Nat.le_of_not_lt hc)]

/-- Row i of the generator's trace, for i below its height n, meets the row constraints. -/
theorem rowSpec_trace (inputs : List (List Word)) {i : ℕ}
    (hi : i < (inputs.length * 24).nextPowerOfTwo) :
    let n := (inputs.length * 24).nextPowerOfTwo
    let P : ℕ → KeccakCols F := fun j => permRow (inputOf inputs (j / 24)) (j % 24)
    RowSpec (getc (P i)) (getc (P ((i + 1) % n))) (if i = 0 then 1 else 0)
      (if i = n - 1 then 0 else 1) := by
  intro n P
  have hk : i % 24 < 24 := Nat.mod_lt _ (by omega)
  -- The next row, when it is in the same permutation.
  have hsame : ¬ i = n - 1 → ¬ i % 24 = 23 →
      (i + 1) % n = i + 1 ∧ (i + 1) / 24 = i / 24 ∧ (i + 1) % 24 = i % 24 + 1 := fun h1 h2 =>
    ⟨Nat.mod_eq_of_lt (by omega), by omega, by omega⟩
  have hflag : ∀ j, ∀ r < 24, getc (P j) (col.step_flags r) = if r = j % 24 then 1 else 0 :=
    fun j r hr => permRow_flag _ hr
  constructor
  · split_ifs with h0
    · subst h0; rw [hflag 0 0 (by omega)]; simp
    · simp
  · intro r hr
    split_ifs with h0
    · subst h0; rw [hflag 0 _ (by omega)]; simp
    · simp
  · intro r hr
    split_ifs with h1
    · simp
    · rw [hflag i r hr, hflag _ _ (Nat.mod_lt _ (by omega)), Nat.mod_eq_of_lt (by omega : i + 1 < n)]
      have : (r = i % 24) ↔ ((r + 1) % 24 = (i + 1) % 24) := by omega
      by_cases h : r = i % 24 <;> simp [h, this.not.mp]
  · intro y hy x hx limb hl
    rw [hflag i 0 (by omega)]
    split_ifs with h0
    · rw [permRow_preimage _ hy hx hl, permRow_a _ hy hx hl, ← h0]; simp [stateAt]
    · simp
  · intro y hy x hx limb hl
    rw [hflag i 23 (by omega)]
    by_cases h1 : i = n - 1
    · simp [h1]
    by_cases h2 : i % 24 = 23
    · simp [h2]
    obtain ⟨e1, e2, -⟩ := hsame h1 h2
    simp only [P, e1, e2, permRow_preimage _ hy hx hl, sub_self, mul_zero]
  · rw [permRow_export]; ring
  · rw [permRow_export]; ring
  · exact intra_c_prime _ _ _
  · exact intra_a_limbs _ _ _ rfl
  · exact intra_parity _ _ _
  · exact intra_chi _ _ _
  · exact (intra_bits _ _ _).1
  · exact (intra_bits _ _ _).2
  · exact intra_iota _ _ _ hk rfl
  · intro x hx y hy limb hl
    rw [hflag i 23 (by omega)]
    by_cases h1 : i = n - 1
    · simp [h1]
    by_cases h2 : i % 24 = 23
    · simp [h2]
    obtain ⟨e1, e2, e3⟩ := hsame h1 h2
    simp only [P, e1, e2, e3, permRow_output _ hy hx hl, permRow_a _ hy hx hl, sub_self, mul_zero]

/-- Completeness: the generator's trace satisfies the AIR's constraint polynomials, in every field. -/
theorem complete [Inhabited F] (inputs : List (List Word)) (e : ℕ) :
    Satisfies (constraints keccakAir) (instOf keccakAir (generate_trace_rows (F := F) inputs e) []) := by
  rw [generate_eq, satisfies_iff_rows]
  change ∀ i < (matOf (traceRows inputs)).height, _
  rw [matOf_height, length_traceRows]
  intro i hi
  have hi' : i < (traceRows (F := F) inputs).length := by rw [length_traceRows]; exact hi
  apply (eval_iff _ _).mpr
  change RowSpec (cur (instOf keccakAir (matOf (traceRows inputs)) []) i)
    (rowOf (rowEnv (instOf keccakAir (matOf (traceRows inputs)) []) i) (layout (F := F)) 1)
    (rowEnv (instOf keccakAir (matOf (traceRows inputs)) []) i .isFirstRow)
    (rowEnv (instOf keccakAir (matOf (traceRows inputs)) []) i .isTransition)
  rw [cur_matOf _ hi', next_matOf _ hi', traceRows_getD _ hi, length_traceRows,
    traceRows_getD _ (Nat.mod_lt _ (by omega))]
  have h := rowSpec_trace (F := F) inputs hi
  simp only [rowEnv, instOf, matOf_height, length_traceRows]
  exact h

/-- The debug checker accepts the generator's trace. -/
theorem check_complete [Inhabited F] [DecidableEq F] (inputs : List (List Word)) (e : ℕ) :
    check_constraints keccakAir (generate_trace_rows (F := F) inputs e) [] = .ok () := by
  have hs : Shapes keccakAir (generate_trace_rows (F := F) inputs e) [] :=
    ⟨by rw [generate_eq]; rfl, by simp [keccakAir], fun _ => rfl, rfl, rfl⟩
  rw [check_constraints_ok_iff hs]
  refine ⟨by simp [PrepHeight, keccakAir], by simp [PeriodicShapes, keccakAir], ?_, complete inputs e⟩
  simp [boundary_io_mismatches, validate, keccakAir]
  rfl

end Plonky3Lean.Proofs.KeccakAir
