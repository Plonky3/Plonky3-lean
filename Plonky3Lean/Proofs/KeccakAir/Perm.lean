module

public import Plonky3Lean.Proofs.KeccakAir.GenRow

@[expose] public section

/-!
# The rows of one permutation

The generator fills the 24 rows of a permutation one round at a time.

Row k holds round k: its input limbs are those of the state after k rounds, and its preimage is the input state.
-/

set_option linter.unusedSectionVars false

namespace Plonky3Lean.Proofs.KeccakAir

open p3_keccak_air.mirror

variable {F : Type} [Field F]

/-- The state the generator reads from an input: lane (x, y) is word x + 5 y. -/
def initState (input : List Word) : WState := fun x y => input.getD (5 * y + x) 0

/-- The output state of round k on the words. -/
def roundW (S : WState) (k : ℕ) : WState := (generate_trace_row_for_round (F := F) KeccakCols.zero k S).2

theorem gen_snd (row : KeccakCols F) (k : ℕ) (S : WState) :
    (generate_trace_row_for_round row k S).2 = roundW (F := F) S k := rfl

/-- The state after k rounds. -/
def stateAt (input : List Word) (k : ℕ) : WState := (List.range k).foldl (roundW (F := F)) (initState input)

/-- The limb fields of a state, stored y first. -/
def limbsOf (S : WState) : ℕ → ℕ → ℕ → F := fun y x => u64_to_16_bit_limbs (S x y)

/-- Row k of a permutation, before its round is filled in. -/
def baseRow (input : List Word) (k : ℕ) : KeccakCols F :=
  { KeccakCols.zero with preimage := limbsOf (initState input), a := limbsOf (stateAt (F := F) input k) }

/-- Row k of a permutation. -/
def permRow (input : List Word) (k : ℕ) : KeccakCols F :=
  (generate_trace_row_for_round (baseRow input k) k (stateAt (F := F) input k)).1

/-- The output limbs of a round are the limbs of its output state. -/
theorem appp_eq (row : KeccakCols F) (k : ℕ) (S : WState) :
    (fun y x limb => (generate_trace_row_for_round row k S).1.a_prime_prime_prime' y x limb) =
      limbsOf (roundW (F := F) S k) := by
  funext y x limb
  simp only [KeccakCols.a_prime_prime_prime', limbsOf, ← gen_snd row, gen_state]
  split_ifs with h1 h2 h2
  · rw [gen_limbs]
  · exact absurd ⟨h1.2, h1.1⟩ h2
  · exact absurd ⟨h2.2, h2.1⟩ h1
  · simp only [gen_a_prime_prime]

/-- The generator's rows of a permutation are its rows 0 to 23. -/
theorem perm_rows (input : List Word) :
    generate_trace_rows_for_perm (F := F) NUM_ROUNDS input = (List.range 24).map (permRow input) := by
  have key : ∀ m ≤ 23, (List.range' 1 m).foldl (fun (acc : List (KeccakCols F) × WState) round =>
      let (rows, current_state) := acc
      let prev := rows.getLast?.getD KeccakCols.zero
      let row : KeccakCols F :=
        { KeccakCols.zero with
          preimage := fun y x => u64_to_16_bit_limbs (initState input x y)
          a := fun y x limb => prev.a_prime_prime_prime' y x limb }
      let (row, current_state) := generate_trace_row_for_round row round current_state
      (rows ++ [row], current_state))
        ([permRow input 0], roundW (F := F) (initState input) 0) =
      ((List.range (m + 1)).map (permRow input), stateAt (F := F) input (m + 1)) := by
    intro m hm
    induction m with
    | zero => rfl
    | succ m ih =>
      rw [List.range'_concat, List.foldl_append, ih (by omega)]
      simp only [List.foldl_cons, List.foldl_nil]
      have hlast : ((List.range (m + 1)).map (permRow (F := F) input)).getLast?.getD KeccakCols.zero =
          permRow input m := by
        rw [List.getLast?_map, List.getLast?_range]; rfl
      have hsucc : stateAt (F := F) input (m + 1) = roundW (F := F) (stateAt (F := F) input m) m := by
        simp only [stateAt, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
      have ha : (fun y x limb => (permRow (F := F) input m).a_prime_prime_prime' y x limb) =
          limbsOf (stateAt (F := F) input (m + 1)) := by
        rw [hsucc]; exact appp_eq _ _ _
      rw [hlast, show 1 + 1 * m = m + 1 by omega, ha]
      have hS : stateAt (F := F) input (m + 1 + 1) = roundW (F := F) (stateAt (F := F) input (m + 1)) (m + 1) := by
        simp only [stateAt, List.range_succ (n := m + 1), List.foldl_append, List.foldl_cons,
          List.foldl_nil]
      rw [List.range_succ (n := m + 1), List.map_append, hS]
      rfl

  simp only [generate_trace_rows_for_perm, NUM_ROUNDS]
  exact congrArg Prod.fst (key 23 le_rfl)

end Plonky3Lean.Proofs.KeccakAir
