module

public import Plonky3Lean.Proofs.KeccakAir.Binary.Sound
public import Plonky3Lean.Proofs.KeccakAir.Binary.Round
public import Plonky3Lean.Proofs.KeccakAir.Complete

@[expose] public section

/-!
# Completeness of the characteristic-2 Keccak-f AIR

Over a field of characteristic 2, the generator's trace satisfies the AIR.

This holds with or without the state booleanity.

Row 25 j + r of the trace is round r of permutation j for r < 24, and its output row for r = 24.

The rows past the last permutation are output rows with the zero state, and there is always at least one.
-/

set_option linter.unusedSectionVars false

namespace Plonky3Lean.Proofs.KeccakAir.Binary

open p3_air.builder.mirror p3_air.air.mirror p3_keccak_air.mirror p3_keccak_air.mirror.binary
open Plonky3Lean.Spec.Air Plonky3Lean.Spec.Keccak Plonky3Lean.Proofs.Air Plonky3Lean.Proofs.KeccakAir

variable {F : Type} [Field F]

/-! ## Cells -/

/-- A cell of a row. -/
def getcB (r : KeccakBinaryCols F) (c : ℕ) : F := r.cells.getD c 0

theorem length_cellsB (r : KeccakBinaryCols F) : r.cells.length = NUM_KECCAK_BINARY_COLS := by
  simp [KeccakBinaryCols.cells, NUM_KECCAK_BINARY_COLS]

theorem cellB_flag (r : KeccakBinaryCols F) {i : ℕ} (hi : i < 25) :
    getcB r (col.round_flags i) = r.round_flags i := by
  rw [getcB, KeccakBinaryCols.cells, getD_append_lt (by simp [col.round_flags]; omega)]
  exact getD_map_range_of _ rfl hi _

theorem cellB_a (r : KeccakBinaryCols F) {y x z : ℕ} (hy : y < 5) (hx : x < 5) (hz : z < 64) :
    getcB r (binary.col.a y x z) = r.a y x z := by
  rw [getcB, KeccakBinaryCols.cells, getD_append_le (by simp [binary.col.a]; omega)]
  exact getD_lanes3_of _ (by simp [binary.col.a]; omega) hy hx hz _

theorem getcB_of_le (r : KeccakBinaryCols F) {c : ℕ} (hc : NUM_KECCAK_BINARY_COLS ≤ c) : getcB r c = 0 := by
  rw [getcB, List.getD_eq_default _ _ (by rw [length_cellsB]; exact hc)]

/-! ## The rows of one permutation -/

/-- The state after r rounds. -/
def stateAtB (input : LState) (r : ℕ) : LState := (List.range r).foldl keccak_round input

/-- The row with flag k and state S. -/
def flagRow (k : ℕ) (S : LState) : KeccakBinaryCols F :=
  write_state { KeccakBinaryCols.zero with round_flags := Function.update (fun _ => 0) k 1 } S

/-- Row r of a permutation: round r for r < 24, the output row for r = 24. -/
def permRowB (input : LState) (r : ℕ) : KeccakBinaryCols F := flagRow (min r 24) (stateAtB input r)

theorem perm_rowsB (input : LState) :
    generate_perm_rows (F := F) input = (List.range 25).map (permRowB input) := by
  have key : ∀ k ≤ 24, (List.range k).foldl
      (fun (acc : List (KeccakBinaryCols F) × LState) round =>
        let (rows, state) := acc
        let row : KeccakBinaryCols F :=
          { KeccakBinaryCols.zero with round_flags := Function.update (fun _ => 0) round 1 }
        let row := write_state row state
        (rows ++ [row], keccak_round state round)) ([], input) =
      ((List.range k).map (permRowB input), stateAtB input k) := by
    intro k hk
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [List.range_succ, List.foldl_append, ih (by omega)]
      simp only [List.foldl_cons, List.foldl_nil, List.map_append, List.map_cons, List.map_nil,
        Prod.mk.injEq]
      refine ⟨?_, ?_⟩
      · simp only [permRowB, flagRow, show min k 24 = k by omega]
      · simp only [stateAtB, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
  simp only [generate_perm_rows, NUM_ROUNDS, key 24 le_rfl, List.range_succ (n := 24),
    List.map_append, List.map_cons, List.map_nil]
  rfl

/-! ## The constraints of one row, from the kinds and states of two rows -/

/-- Flags k may be followed by flags k':

- k + 1 below round 23
- an output row after round 23
- round 0 or an output row after an output row. -/
def Succ (k k' : ℕ) : Prop := (k < 23 ∧ k' = k + 1) ∨ (k = 23 ∧ k' = 24) ∨ (k = 24 ∧ (k' = 0 ∨ k' = 24))

section local_

variable [DecidableEq F] (h2 : (2 : F) = 0)
include h2

theorem bitF_self_add (b : Bool) : (bitF b : F) + bitF b = 0 := by
  rw [bitF_add h2]; simp [bitF]

theorem bitF_cancel (c r : Bool) : (bitF c : F) + bitF (c ^^ r) + bitF r = 0 := by
  cases c <;> cases r <;> simp [bitF, one_add_one_eq_two, h2]

/-- Two rows meet the row constraints when:

- their kinds follow each other
- their states are words
- their states follow by the round. -/
theorem rowSpecB_local (cb : Bool) {loc nxt : ℕ → F} {first : F} {k k' : ℕ} {Sl Sn : LState}
    (hk : k < 25) (hf : OneHot loc k) (hf' : OneHot nxt k') (hs : Succ k k')
    (hl : ∀ y < 5, ∀ x < 5, ∀ z < 64, loc (binary.col.a y x z) = bitF ((Sl (5 * y + x)).getLsbD z))
    (hn : ∀ y < 5, ∀ x < 5, ∀ z < 64, nxt (binary.col.a y x z) = bitF ((Sn (5 * y + x)).getLsbD z))
    (hr : k < 24 → lanesState Sn = rnd (lanesState Sl) k) (hfirst : first = 0 ∨ (first = 1 ∧ k = 0)) :
    RowSpecB cb loc nxt first := by
  have hb : ∀ y < 5, ∀ x < 5, ∀ z < 64, loc (binary.col.a y x z) * (loc (binary.col.a y x z) - 1) = 0 :=
    fun y hy x hx z hz => by rw [hl y hy x hx z hz]; exact bitF_bool _
  have hst : stateOf loc = lanesState Sl := by
    funext x y z; simp only [stateOf, lanesState, hl _ y.isLt _ x.isLt _ z.isLt, bv_bitF]
  constructor
  · rcases hfirst with h | ⟨h, rfl⟩
    · simp [h]
    · rw [h, hf 0 (by omega)]; simp
  · intro i hi
    rcases hfirst with h | ⟨h, rfl⟩
    · simp [h]
    · rw [h, hf (i + 1) (by omega)]; simp
  · intro r hr
    rw [hf r (by omega), hf' (r + 1) (by omega)]
    rcases hs with ⟨hk23, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl | rfl⟩
    · by_cases hrk : r = k
      · subst hrk; simp [one_add_one_eq_two, h2]
      · rw [ite_eq_right (show ¬ r + 1 = k + 1 by omega), ite_eq_right hrk]; ring
    all_goals rw [ite_eq_right (by omega), ite_eq_right (by omega)]; ring
  · rw [hf 23 (by omega), hf 24 (by omega), hf' 0 (by omega), hf' 24 (by omega)]
    rcases hs with ⟨_, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl | rfl⟩
    · rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
        ite_eq_right (by omega)]; ring
    · simp [one_add_one_eq_two, h2]
    · simp [one_add_one_eq_two, h2]
    · simp [one_add_one_eq_two, h2]
  · rw [hf 0 (by omega), hf 24 (by omega)]; split_ifs <;> simp_all
  · intro _ y hy x hx z hz; exact hb y hy x hx z hz
  · intro y hy x hx z hz
    by_cases hk24 : k < 24
    · have hB1 := colB_eq h2 hb (⟨x, hx⟩ + 1) ⟨y, hy⟩ ⟨z, hz⟩
      have hB2 := colB_eq h2 hb (⟨x, hx⟩ + 2) ⟨y, hy⟩ ⟨z, hz⟩
      rw [fin5_add, Fin.val_one] at hB1
      rw [fin5_add, Fin.val_two] at hB2
      have hnx : nxt (binary.col.a y x z) = bitF (rnd (lanesState Sl) k ⟨x, hx⟩ ⟨y, hy⟩ ⟨z, hz⟩) := by
        rw [hn y hy x hx z hz, ← hr hk24]; rfl
      simp only [roundExpr]
      rw [hf 24 (by omega), ite_eq_right (show ¬ (24 = k) by omega), add_zero, one_mul,
        colB_eq h2 hb ⟨x, hx⟩ ⟨y, hy⟩ ⟨z, hz⟩, hB1, hB2, one_add_bitF_mul h2, bitF_add h2, hnx, ← hst]
      simp only [rnd, iota, chi, Bool.xor_true, Fin.ext_iff, Fin.val_zero]
      split_ifs with h0
      · have hsum : sum fieldOps (((List.range 24).filter fun r => rcBit r z ≠ 0).map fun r =>
            loc (col.round_flags r)) = bitF (decide (rcBit k z ≠ 0)) := by
          rw [sum_eq, List.map_congr_left (g := fun r => if r = k then (1 : F) else 0)
            (fun r hr => hf r (by simp at hr; omega)), sum_onehot _ ((List.nodup_range).filter _)]
          by_cases hrc : rcBit k z ≠ 0 <;> simp [hrc, hk24, bitF]
        have hrc : decide (rcBit k z ≠ 0) = roundConstant k ⟨z, hz⟩ := by
          have := rcBit_eq hk24 hz
          rw [show (Fin.ofNat 64 z : Fin 64) = ⟨z, hz⟩ from Fin.ext (Nat.mod_eq_of_lt hz)] at this
          simp [this]
        rw [hsum, hrc]
        exact bitF_cancel h2 _ _
      · rw [bitF_self_add h2]
    · obtain rfl : k = 24 := by omega
      simp only [roundExpr]
      rw [hf 24 (by omega), ite_eq_left rfl, one_add_one_eq_two, h2, zero_mul]
      split_ifs
      · rw [zero_add, sum_eq]
        apply List.sum_eq_zero
        intro v hv
        simp only [List.mem_map, List.mem_filter, List.mem_range] at hv
        obtain ⟨r, ⟨hr24, -⟩, rfl⟩ := hv
        rw [hf r (by omega), ite_eq_right (by omega)]
      · rfl

end local_

/-! ## The trace -/

/-- A padding row: an output row with the zero state. -/
def padRow : KeccakBinaryCols F :=
  { KeccakBinaryCols.zero with round_flags := Function.update (fun _ => 0) NUM_ROUNDS 1 }

/-- The input of permutation j. -/
def inputOfB (inputs : List LState) (j : ℕ) : LState := inputs.getD j (fun _ => 0)

/-- The rows of the generator's trace. -/
def rowsB (inputs : List LState) : List (KeccakBinaryCols F) :=
  inputs.flatMap (fun input => (List.range 25).map (permRowB input)) ++
    List.replicate ((inputs.length * 25).nextPowerOfTwo - inputs.length * 25) padRow

/-- The trace of a list of rows. -/
def matB (rows : List (KeccakBinaryCols F)) : Mat F :=
  ⟨NUM_KECCAK_BINARY_COLS, rows.flatMap KeccakBinaryCols.cells⟩

theorem generate_binary_eq [DecidableEq F] (h2 : (2 : F) = 0) {inputs : List LState} (hne : inputs ≠ [])
    (e : ℕ) : generate_binary_trace_rows (F := F) inputs e = some (matB (rowsB inputs)) := by
  have hp : (generate_perm_rows (F := F)) = fun input => (List.range 25).map (permRowB input) :=
    funext perm_rowsB
  simp only [generate_binary_trace_rows, h2, ne_eq, not_true_eq_false, ↓reduceIte, hne,
    KECCAK_BINARY_ROWS_PER_PERM, hp]
  rfl

theorem length_rowsB (inputs : List LState) :
    (rowsB (F := F) inputs).length = (inputs.length * 25).nextPowerOfTwo := by
  have h := Nat.le_nextPowerOfTwo (inputs.length * 25)
  simp only [rowsB, List.length_append, List.length_replicate, List.length_flatMap, List.length_map,
    List.length_range, List.map_const', List.sum_replicate, smul_eq_mul]
  omega

/-- Row i of the trace: row i mod 25 of permutation i / 25, or a padding row. -/
theorem rowsB_getD (inputs : List LState) {i : ℕ} (hi : i < (inputs.length * 25).nextPowerOfTwo) :
    (rowsB (F := F) inputs).getD i KeccakBinaryCols.zero =
      if i < inputs.length * 25 then permRowB (inputOfB inputs (i / 25)) (i % 25) else padRow := by
  have hlen : (inputs.flatMap (fun input => (List.range 25).map (permRowB (F := F) input))).length =
      inputs.length * 25 := by
    simp only [List.length_flatMap, List.length_map, List.length_range, List.map_const',
      List.sum_replicate, smul_eq_mul]
  unfold rowsB
  split_ifs with hr
  · rw [getD_append_lt (by omega), Plonky3Lean.Proofs.Keccak.getD_flatMap_uniform _ _ (m := 25)
      (by simp) _ _ (fun _ => 0) (by rw [Nat.mul_comm]; exact hr)]
    have hq : i / 25 < inputs.length := by omega
    simp [inputOfB, List.getElem?_eq_getElem hq, List.getElem?_range (Nat.mod_lt i (by omega : 0 < 25))]
  · rw [getD_append_le (by omega), hlen, List.getD_eq_getElem _ _ (by simp; omega)]
    simp

section matB

variable (rows : List (KeccakBinaryCols F))

theorem matB_height : (matB rows).height = rows.length := by
  simp only [Mat.height, matB, NUM_KECCAK_BINARY_COLS, List.length_flatMap, length_cellsB,
    List.map_const', List.sum_replicate, smul_eq_mul]
  simp

theorem matB_cell {i c : ℕ} (hi : i < rows.length) (hc : c < NUM_KECCAK_BINARY_COLS) :
    ((matB rows).row i).getD c 0 = getcB (rows.getD i KeccakBinaryCols.zero) c := by
  have hk : i * NUM_KECCAK_BINARY_COLS + c < NUM_KECCAK_BINARY_COLS * rows.length := by
    have h1 := Nat.mul_le_mul_right NUM_KECCAK_BINARY_COLS (Nat.succ_le_of_lt hi)
    rw [Nat.succ_mul, Nat.mul_comm rows.length] at h1
    omega
  simp only [Mat.row, matB, getcB]
  rw [List.getD_eq_getElem?_getD, List.getElem?_take, ite_eq_left hc, List.getElem?_drop,
    ← List.getD_eq_getElem?_getD,
    Plonky3Lean.Proofs.Keccak.getD_flatMap_uniform _ _ (fun r => length_cellsB r) _ _ _ hk,
    show (i * NUM_KECCAK_BINARY_COLS + c) / NUM_KECCAK_BINARY_COLS = i by
      rw [Nat.mul_comm, Nat.mul_add_div (by simp [NUM_KECCAK_BINARY_COLS]), Nat.div_eq_of_lt hc,
        add_zero],
    show (i * NUM_KECCAK_BINARY_COLS + c) % NUM_KECCAK_BINARY_COLS = c by
      rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hc]]

theorem curB_matB [Inhabited F] (cb : Bool) {i : ℕ} (hi : i < rows.length) :
    curB cb (instOf (binaryAir cb) (matB rows) []) i = getcB (rows.getD i KeccakBinaryCols.zero) := by
  funext c
  simp only [curB, rowOf, rowEnv, instOf, AirLayout.from_air, binaryAir]
  by_cases hc : c < NUM_KECCAK_BINARY_COLS
  · rw [getD_map_range_of _ rfl hc, matB_cell rows hi hc]
  · simp [hc, getcB_of_le _ (Nat.le_of_not_lt hc)]

end matB

/-! ## Every row meets the constraints -/

section rows

variable (inputs : List LState)

/-- The kind of row j: its round, or 24 for an output or padding row. -/
def kindB (j : ℕ) : ℕ := if j < inputs.length * 25 then j % 25 else 24

/-- The state of row j. -/
def stB (j : ℕ) : LState :=
  if j < inputs.length * 25 then stateAtB (inputOfB inputs (j / 25)) (j % 25) else fun _ => 0

theorem flagRow_onehot (k : ℕ) (S : LState) : OneHot (getcB (flagRow (F := F) k S)) k := by
  intro r hr
  simp only [cellB_flag _ hr, flagRow, write_state, Function.update_apply]

theorem flagRow_state (k : ℕ) (S : LState) {y x z : ℕ} (hy : y < 5) (hx : x < 5) (hz : z < 64) :
    getcB (flagRow (F := F) k S) (binary.col.a y x z) = bitF ((S (5 * y + x)).getLsbD z) := by
  rw [cellB_a _ hy hx hz, flagRow, write_state]
  exact u64_bits_eq _ hz

theorem row_onehot {j : ℕ} (hj : j < (inputs.length * 25).nextPowerOfTwo) :
    OneHot (getcB ((rowsB (F := F) inputs).getD j KeccakBinaryCols.zero)) (kindB inputs j) := by
  rw [rowsB_getD _ hj, kindB]
  split_ifs
  · rw [permRowB, show min (j % 25) 24 = j % 25 by omega]; exact flagRow_onehot _ _
  · intro r hr; simp only [cellB_flag _ hr, padRow, Function.update_apply, NUM_ROUNDS]

theorem row_state {j : ℕ} (hj : j < (inputs.length * 25).nextPowerOfTwo) :
    ∀ y < 5, ∀ x < 5, ∀ z < 64, getcB ((rowsB (F := F) inputs).getD j KeccakBinaryCols.zero)
      (binary.col.a y x z) = bitF ((stB inputs j (5 * y + x)).getLsbD z) := by
  intro y hy x hx z hz
  rw [rowsB_getD _ hj, stB]
  split_ifs
  · exact flagRow_state _ _ hy hx hz
  · rw [cellB_a _ hy hx hz]; simp [padRow, KeccakBinaryCols.zero, bitF]

end rows

/-- Completeness: over a field of characteristic 2, the generator's trace satisfies the AIR.

This holds with or without the state booleanity. -/
theorem complete [Inhabited F] [DecidableEq F] (h2 : (2 : F) = 0) (cb : Bool) {inputs : List LState}
    (hne : inputs ≠ []) (e : ℕ) :
    ∃ M, generate_binary_trace_rows (F := F) inputs e = some M ∧
      Satisfies (constraints (binaryAir cb)) (instOf (binaryAir cb) M []) := by
  refine ⟨_, generate_binary_eq h2 hne e, ?_⟩
  have hL : 0 < inputs.length := List.length_pos_iff.mpr hne
  rw [satisfies_iff_rows]
  change ∀ i < (matB (rowsB inputs)).height, _
  rw [matB_height, length_rowsB]
  intro i hi
  set n := (inputs.length * 25).nextPowerOfTwo
  have hle : inputs.length * 25 ≤ n := Nat.le_nextPowerOfTwo _
  have hi' : i < (rowsB (F := F) inputs).length := by rw [length_rowsB]; exact hi
  have hn' : (i + 1) % n < (rowsB (F := F) inputs).length := by
    rw [length_rowsB]; exact Nat.mod_lt _ (by omega)
  apply (eval_iff _ _ _).mpr
  change RowSpecB cb (curB cb (instOf (binaryAir cb) (matB (rowsB inputs)) []) i)
    (rowOf (rowEnv (instOf (binaryAir cb) (matB (rowsB inputs)) []) i)
      (AirLayout.from_air (binaryAir cb)) 1)
    (rowEnv (instOf (binaryAir cb) (matB (rowsB inputs)) []) i .isFirstRow)
  rw [rowOf_next_mod, curB_matB _ _ hi']
  have hh : (instOf (binaryAir cb) (matB (rowsB (F := F) inputs)) []).height = n := by
    simp only [instOf, matB_height, length_rowsB, n]
  rw [hh, curB_matB _ _ hn']
  simp only [rowEnv]
  refine rowSpecB_local h2 cb (k := kindB inputs i) (k' := kindB inputs ((i + 1) % n))
    (by unfold kindB; split_ifs <;> omega) (row_onehot _ hi) (row_onehot _ (Nat.mod_lt _ (by omega)))
    ?_ (row_state _ hi) (row_state _ (Nat.mod_lt _ (by omega))) ?_ ?_
  · unfold Succ kindB
    rcases (by omega : i + 1 < n ∨ i + 1 = n) with hlt | heq
    · rw [Nat.mod_eq_of_lt hlt]
      split_ifs <;> omega
    · rw [heq, Nat.mod_self]
      split_ifs <;> omega
  · intro hk
    have hA : i < inputs.length * 25 := by unfold kindB at hk; split_ifs at hk with h <;> omega
    have hr24 : i % 25 < 24 := by unfold kindB at hk; rwa [ite_eq_left hA] at hk
    have hB : i + 1 < inputs.length * 25 := by omega
    rw [Nat.mod_eq_of_lt (by omega : i + 1 < n), kindB, ite_eq_left hA, stB, stB, ite_eq_left hA, ite_eq_left hB,
      show (i + 1) / 25 = i / 25 by omega, show (i + 1) % 25 = i % 25 + 1 by omega, stateAtB,
      List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    exact keccak_round_eq _ hr24
  · split_ifs with h0
    · subst h0; right; refine ⟨rfl, ?_⟩; unfold kindB; rw [ite_eq_left (by omega)]
    · left; rfl

end Plonky3Lean.Proofs.KeccakAir.Binary
