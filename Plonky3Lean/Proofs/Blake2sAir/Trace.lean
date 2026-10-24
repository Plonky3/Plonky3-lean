module

public import Plonky3Lean.Proofs.Blake2sAir.Output
public import Plonky3Lean.Proofs.Blake2sAir.Complete

@[expose] public section

/-!
# The BLAKE2s AIR on traces

- Soundness: on a satisfying row of input bits, the output read back is the compression of its inputs.
- The debug checker accepts the generator's trace.
- The output read back from a generated row is the RFC 7693 compression of the generator's input.
-/

set_option linter.unusedSectionVars false

namespace Plonky3Lean.Proofs.Blake2sAir

open p3_air.builder.mirror p3_air.air.mirror p3_blake2s_air.mirror Plonky3Lean.Spec.Air
open Plonky3Lean.Proofs.Air
open Plonky3Lean.Proofs.KeccakAir (propBuilder rowOf bitF satisfies_iff_rows)
open Plonky3Lean.Proofs.Sha256Air (Holds)

variable {F : Type} [Field F] [DecidableEq F]

/-- The cells of row `i` of a trace, as the borrow reads them. -/
def rowCells (T : Instance F) (i : ℕ) : List F := (List.range NUM_BLAKE2S_BINARY_COLS).map (T.main i)

/-- Soundness on a trace.

Take a row of a trace that satisfies the AIR in characteristic 2.

Let its input cells be bits, which the booleanity enforces when stated.

Then the output read back from the row never panics, and is the RFC 7693 compression of:

- the chaining value the row's first 256 cells hold
- the block the next 512 cells hold
- the counter the next 64 cells hold, low word first
- the final-block flag the next cell holds. -/
theorem sound (h2 : (2 : F) = 0) {cb : Bool} {T : Instance F}
    (hT : Satisfies (constraints (blake2sAir cb)) T) {i : ℕ} (hi : i < T.height)
    (hb : cb = true ∨ BoolOk (fun c => (rowCells T i).getD c 0)) :
    compression_output (Blake2sBinaryCols.ofCells (rowCells T i)) =
      some (Plonky3Lean.Spec.Blake2s.compress (cvOf (fun c => (rowCells T i).getD c 0))
        (blockOf (fun c => (rowCells T i).getD c 0)) (counterOf (fun c => (rowCells T i).getD c 0))
        (flagOf (fun c => (rowCells T i).getD c 0))) :=
  output_sound (env := rowEnv T i) (L := AirLayout.from_air (blake2sAir (F := F) cb)) h2
    ((satisfies_iff_rows (blake2sAir cb) T).mp hT i hi) hb

/-- The debug checker accepts the generator's trace, in characteristic 2. -/
theorem check_complete [Inhabited F] (h2 : (2 : F) = 0) (cb : Bool)
    {inputs : List Blake2sCompressionInput}
    (h : inputs.length ≠ 0 ∧ 2 ^ Nat.log 2 inputs.length = inputs.length) (e : ℕ) :
    ∃ M, generate_binary_trace_rows (F := F) inputs e = some M ∧
      check_constraints (blake2sAir cb) M [] = .ok () := by
  obtain ⟨M, hM, hs⟩ := complete h2 cb h e
  refine ⟨M, hM, ?_⟩
  simp only [generate_eq, h2, h, ne_eq, not_false_eq_true, and_self, ↓reduceIte,
    Option.some.injEq] at hM
  subst hM
  have hsh : Shapes (blake2sAir cb) (matOf (inputs.map (generate_trace_row (F := F) Blake2sBinaryCols.zero))) [] :=
    ⟨rfl, by simp [blake2sAir], fun _ => rfl, rfl, rfl⟩
  rw [check_constraints_ok_iff hsh]
  refine ⟨by simp [PrepHeight, blake2sAir], by simp [PeriodicShapes, blake2sAir], ?_, hs⟩
  simp [boundary_io_mismatches, validate, blake2sAir]
  rfl

/-- The message block of the input, as sixteen words. -/
def blockIn (input : Blake2sCompressionInput) : List Word :=
  (List.range 16).map fun i => input.block.getD i 0

/-- In characteristic 2, the output read back from a generated row is the RFC 7693 compression of the input. -/
theorem gen_output (h2 : (2 : F) = 0) (input : Blake2sCompressionInput) :
    compression_output (Blake2sBinaryCols.ofCells
        (generate_trace_row (Blake2sBinaryCols.zero : Blake2sBinaryCols F) input).cells) =
      some (Plonky3Lean.Spec.Blake2s.compress (cvIn input) (blockIn input) input.counter.toNat
        input.last_block) := by
  set R := generate_trace_row (Blake2sBinaryCols.zero : Blake2sBinaryCols F) input
  let env : Var → F := fun v => match v with
    | .main _ c => getc R c
    | _ => 0
  let L : AirLayout := AirLayout.from_air (blake2sAir (F := F) true)
  have hloc : rowOf env L 0 = genLoc input := by
    funext c
    simp only [rowOf, L, env, AirLayout.from_air, blake2sAir]
    by_cases hc : c < NUM_BLAKE2S_BINARY_COLS
    · rw [Plonky3Lean.Proofs.KeccakAir.getD_map_range_of _ rfl hc]
    · simp [hc, getc_of_le _ (Nat.le_of_not_lt hc)]
  have hcells : (List.range L.main_width).map (fun c => env (.main 0 c)) = R.cells := by
    apply List.ext_getElem (by simp [L, AirLayout.from_air, blake2sAir, length_cells])
    intro n h1 h2'
    simp [env, getc, List.getElem?_eq_getElem h2']
  have := output_sound h2 (gen_eval input h2 true env L hloc) (Or.inl rfl)
  rw [hcells, hloc] at this
  obtain ⟨e1, e2, e3⟩ := gen_inputs (F := F) input
  have e4 : blockOf (genLoc (F := F) input) = blockIn input :=
    List.map_congr_left fun k hk => wordOf_eq (gen_block input (List.mem_range.mp hk))
  rw [this, e1, e2, e3, e4]

end Plonky3Lean.Proofs.Blake2sAir
