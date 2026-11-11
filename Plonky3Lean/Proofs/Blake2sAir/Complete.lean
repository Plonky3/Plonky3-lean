module

public import Plonky3Lean.Proofs.Blake2sAir.GenRow
public import Plonky3Lean.Proofs.Air.Check

@[expose] public section

/-!
# Completeness of the BLAKE2s AIR

In characteristic 2, the row the generator fills from any input meets every constraint:

- its input cells are bits, so the booleanity holds
- each G step's witness is honest, so its four additions hold.

So, on a positive power-of-two number of inputs, the generator's trace satisfies the AIR.

This holds with or without the booleanity.
-/

set_option linter.unusedSectionVars false

namespace Plonky3Lean.Proofs.Blake2sAir

open p3_air.builder.mirror p3_air.air.mirror p3_blake2s_air.mirror Plonky3Lean.Spec.Air
open Plonky3Lean.Proofs.KeccakAir (propBuilder fieldOps rowOf bitF)
open Plonky3Lean.Proofs.Sha256Air (Holds)
open Plonky3Lean.Spec.Blake2s (rounds init)
open Plonky3Lean.Proofs.Air (instOf constraints)

variable {F : Type} [Field F]

/-- Cell `c` of a row. -/
def getc (r : Blake2sBinaryCols F) (c : ℕ) : F := r.cells.getD c 0

section row

variable (input : Blake2sCompressionInput)

/-- The cells of the generated row. -/
abbrev genLoc : ℕ → F := getc (generate_trace_row Blake2sBinaryCols.zero input)

theorem gen_cv {i : ℕ} (hi : i < 8) :
    Holds (fun b => genLoc (F := F) input (col.chaining_value i b)) (input.chaining_value.getD i 0) :=
  fun b hb => by
    show getc _ _ = _
    rw [getc, cell_cv _ hi hb, (gen_spec input).1.1]
    exact u32_bits _ hb

theorem gen_block {k : ℕ} (hk : k < 16) : Holds (msg (genLoc (F := F) input) k) (input.block.getD k 0) :=
  fun b hb => by
    rw [msg, genLoc, getc, cell_block _ hk hb, (gen_spec input).1.2.1]
    exact u32_bits _ hb

theorem gen_lo : Holds (fun b => genLoc (F := F) input (col.counter_low b)) (input.counter.setWidth 32) :=
  fun b hb => by
    show getc _ _ = _
    rw [getc, cell_counter_low _ hb, (gen_spec input).1.2.2.1]
    exact u32_bits _ hb

theorem gen_hi :
    Holds (fun b => genLoc (F := F) input (col.counter_high b)) ((input.counter >>> 32).setWidth 32) :=
  fun b hb => by
    show getc _ _ = _
    rw [getc, cell_counter_high _ hb, (gen_spec input).1.2.2.2.1]
    exact u32_bits _ hb

theorem gen_flag : genLoc (F := F) input col.last_block = bitF input.last_block := by
  rw [genLoc, getc, cell_last_block, (gen_spec input).1.2.2.2.2]
  cases h : input.last_block <;> simp [inputRow, bitF, h]

/-- The witness cells of step `g` of round `r` are those the generator computes. -/
theorem gen_gcols {r g : ℕ} (hr : r < 10) (hg : g < 8) :
    let w := witAt (F := F) input.block (rounds input.block (v0 input) r) r g
    (∀ c < 31, (gcolsOf (genLoc (F := F) input) r g).add1_carries c = w.add1_carries c) ∧
    (∀ b < 32, (gcolsOf (genLoc (F := F) input) r g).d1 b = w.d1 b) ∧
    (∀ b < 32, (gcolsOf (genLoc (F := F) input) r g).b1 b = w.b1 b) ∧
    (∀ c < 31, (gcolsOf (genLoc (F := F) input) r g).add2_carries c = w.add2_carries c) ∧
    (∀ b < 32, (gcolsOf (genLoc (F := F) input) r g).d2 b = w.d2 b) ∧
    (∀ b < 32, (gcolsOf (genLoc (F := F) input) r g).b2 b = w.b2 b) := by
  intro w
  obtain ⟨c1, c2, c3, c4, c5, c6⟩ := getD_gCells ((generate_trace_row (Blake2sBinaryCols.zero : Blake2sBinaryCols F)
    input).rounds r g)
  have e := (gen_spec (F := F) input).2 r hr g hg
  refine ⟨fun c hc => ?_, fun b hb => ?_, fun b hb => ?_, fun c hc => ?_, fun b hb => ?_, fun b hb => ?_⟩ <;>
  simp only [gcolsOf, genLoc, getc, col.add1_carries, col.d1, col.b1, col.add2_carries, col.d2, col.b2]
  · rw [cell_g _ hr hg (by omega), c1 c hc, e]
  · rw [Nat.add_assoc, cell_g _ hr hg (by omega), c2 b hb, e]
  · rw [Nat.add_assoc, cell_g _ hr hg (by omega), c3 b hb, e]
  · rw [Nat.add_assoc, cell_g _ hr hg (by omega), c4 c hc, e]
  · rw [Nat.add_assoc, cell_g _ hr hg (by omega), c5 b hb, e]
  · rw [Nat.add_assoc, cell_g _ hr hg (by omega), c6 b hb, e]


theorem bitF_bool (b : Bool) : (bitF b : F) * (bitF b - 1) = 0 := by cases b <;> simp [bitF]

theorem holds_bool {x : ℕ → F} {W : Word} (h : Holds x W) {b : ℕ} (hb : b < 32) :
    x b * (x b - 1) = 0 := by
  rw [h b hb]; exact bitF_bool _

theorem gen_bool : BoolOk (genLoc (F := F) input) :=
  ⟨fun i hi b hb => holds_bool (gen_cv input hi) hb, fun k hk b hb => holds_bool (gen_block input hk) hb,
    fun b hb => holds_bool (gen_lo input) hb, fun b hb => holds_bool (gen_hi input) hb,
    by rw [gen_flag]; exact bitF_bool _⟩

variable [DecidableEq F]

theorem wordOf_eq {x : ℕ → F} {W : Word} (h : Holds x W) : Plonky3Lean.Proofs.Sha256Air.wordOf x = W :=
  Holds.unique (Plonky3Lean.Proofs.Sha256Air.holds_wordOf fun _ hb => holds_bool h hb) h

theorem gen_inputs :
    cvOf (genLoc (F := F) input) = cvIn input ∧ counterOf (genLoc (F := F) input) = input.counter.toNat ∧
      flagOf (genLoc (F := F) input) = input.last_block := by
  refine ⟨List.map_congr_left fun i hi => wordOf_eq (gen_cv input (List.mem_range.mp hi)), ?_, ?_⟩
  · rw [counterOf, wordOf_eq (gen_lo input), wordOf_eq (gen_hi input)]
    have := input.counter.isLt
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
    omega
  · rw [flagOf, gen_flag]
    cases input.last_block <;> simp [bitF]

variable (h2 : (2 : F) = 0)
include h2

/-- The state before the rounds holds the RFC's initial working vector of the input. -/
theorem gen_init : StateHolds (initState (genLoc (F := F) input)) (v0 input) := by
  have := init_sound h2 (gen_bool (F := F) input)
  obtain ⟨e1, e2, e3⟩ := gen_inputs (F := F) input
  rwa [e1, e2, e3] at this

/-- Step `n` of round `R` meets its constraints, and moves the state as G moves the vector. -/
theorem gen_step {R n : ℕ} (hR : R < 10) (hn : n < 8) {st : State F}
    (hs : StateHolds st ((List.range n).foldl (gStep input.block R) (rounds input.block (v0 input) R))) :
    CStep (genLoc input) R st n ∧ StateHolds (TStep (genLoc input) R st n)
      ((List.range (n + 1)).foldl (gStep input.block R) (rounds input.block (v0 input) R)) := by
  obtain ⟨c1, c2, c3, c4, c5, c6⟩ := gen_gcols (F := F) input hR hn
  have hsl : ∀ j < 4, (G_SCHEDULE.getD n []).getD j 0 < 4 := fun j hj => g_schedule_lt n hj
  have hok : CStep (genLoc input) R st n :=
    step_complete h2 hs hsl (gen_block input (sigma_lt _ _)) (gen_block input (sigma_lt _ _))
      (fun i hi => by rw [c1 i hi]; exact carries_bits _ _ hi)
      (fun b hb => by rw [c2 b hb]; exact u32_bits _ hb)
      (fun b hb => by rw [c3 b hb]; exact u32_bits _ hb)
      (fun i hi => by rw [c4 i hi]; exact carries_bits _ _ hi)
      (fun b hb => by rw [c5 b hb]; exact u32_bits _ hb)
      (fun b hb => by rw [c6 b hb]; exact u32_bits _ hb)
  refine ⟨hok, ?_⟩
  rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
  exact step_sound h2 hs hsl (gen_block input (sigma_lt _ _)) (gen_block input (sigma_lt _ _)) hok

theorem gen_round_chain {R : ℕ} (hR : R < 10) : ∀ k n, n + k = 8 → ∀ st : State F,
    StateHolds st ((List.range n).foldl (gStep input.block R) (rounds input.block (v0 input) R)) →
    Chain (CStep (genLoc input) R) (TStep (genLoc input) R) (List.range' n k) st
  | 0, _, _, _, _ => trivial
  | k + 1, n, hk, st, hs => by
    rw [List.range'_succ]
    obtain ⟨hc, ht⟩ := gen_step input h2 hR (by omega) hs
    exact ⟨hc, gen_round_chain hR k (n + 1) (by omega) _ ht⟩

theorem gen_chain : ∀ k n, n + k = 10 → ∀ st : State F,
    StateHolds st (rounds input.block (v0 input) n) →
    Chain (CRound (genLoc input)) (TRound (genLoc input)) (List.range' n k) st
  | 0, _, _, _, _ => trivial
  | k + 1, n, hk, st, hs => by
    rw [List.range'_succ]
    have hc : CRound (genLoc input) st n := by
      rw [CRound, G_PER_ROUND, List.range_eq_range']
      exact gen_round_chain input h2 (by omega) 8 0 rfl st (by rw [List.range_zero, List.foldl_nil]; exact hs)
    refine ⟨hc, gen_chain k (n + 1) (by omega) _ ?_⟩
    rw [rounds_succ _ _ (by omega)]
    exact chain_inv (U := gStep input.block n) (I := StateHolds) (fun g st v hg hs =>
      step_sound h2 hs (fun j hj => g_schedule_lt g hj) (gen_block input (sigma_lt _ _))
        (gen_block input (sigma_lt _ _)) hg) _ _ _ hc hs

/-- In characteristic 2, the generated row meets its constraints, with or without the booleanity. -/
theorem gen_eval (cb : Bool) (env : Var → F) (L : AirLayout) (hloc : rowOf env L 0 = genLoc input) :
    eval cb (propBuilder env L) True := by
  rw [eval_iff, hloc]
  refine ⟨fun _ => gen_bool input, ?_⟩
  rw [NUM_ROUNDS, List.range_eq_range']
  exact gen_chain input h2 10 0 rfl _ (gen_init input h2)

end row

/-! ## The trace -/

/-- The trace of a list of rows. -/
def matOf (rows : List (Blake2sBinaryCols F)) : Mat F :=
  ⟨NUM_BLAKE2S_BINARY_COLS, rows.flatMap Blake2sBinaryCols.cells⟩

/-- The generator panics unless 2 is 0 in the field and the number of inputs is a positive power of two. -/
theorem generate_eq [DecidableEq F] (inputs : List Blake2sCompressionInput) (e : ℕ) :
    generate_binary_trace_rows (F := F) inputs e =
      if (2 : F) = 0 ∧ inputs.length ≠ 0 ∧ 2 ^ Nat.log 2 inputs.length = inputs.length then
        some (matOf (inputs.map (generate_trace_row Blake2sBinaryCols.zero)))
      else none := by
  unfold generate_binary_trace_rows
  by_cases h1 : (2 : F) = 0 <;> by_cases h2 : inputs.length = 0 <;>
    by_cases h3 : 2 ^ Nat.log 2 inputs.length = inputs.length <;> simp [h1, h2, h3, matOf]

theorem matOf_height (rows : List (Blake2sBinaryCols F)) : (matOf rows).height = rows.length := by
  simp only [Mat.height, matOf, NUM_BLAKE2S_BINARY_COLS, List.length_flatMap, length_cells,
    List.map_const', List.sum_replicate, smul_eq_mul]
  simp

theorem matOf_cell (rows : List (Blake2sBinaryCols F)) {i c : ℕ} (hi : i < rows.length)
    (hc : c < NUM_BLAKE2S_BINARY_COLS) :
    ((matOf rows).row i).getD c 0 = getc (rows.getD i Blake2sBinaryCols.zero) c := by
  have hk : i * NUM_BLAKE2S_BINARY_COLS + c < NUM_BLAKE2S_BINARY_COLS * rows.length := by
    have h1 := Nat.mul_le_mul_right NUM_BLAKE2S_BINARY_COLS (Nat.succ_le_of_lt hi)
    rw [Nat.succ_mul, Nat.mul_comm rows.length] at h1
    omega
  simp only [Mat.row, matOf, getc]
  rw [List.getD_eq_getElem?_getD, List.getElem?_take, ite_eq_left hc, List.getElem?_drop,
    ← List.getD_eq_getElem?_getD,
    Plonky3Lean.Proofs.Keccak.getD_flatMap_uniform _ _ (fun r => length_cells r) _ _ _ hk,
    show (i * NUM_BLAKE2S_BINARY_COLS + c) / NUM_BLAKE2S_BINARY_COLS = i by
      rw [Nat.mul_comm, Nat.mul_add_div (by simp [NUM_BLAKE2S_BINARY_COLS]), Nat.div_eq_of_lt hc,
        add_zero],
    show (i * NUM_BLAKE2S_BINARY_COLS + c) % NUM_BLAKE2S_BINARY_COLS = c by
      rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hc]]

theorem getc_of_le (r : Blake2sBinaryCols F) {c : ℕ} (hc : NUM_BLAKE2S_BINARY_COLS ≤ c) : getc r c = 0 := by
  rw [getc, List.getD_eq_default _ _ (by rw [length_cells]; exact hc)]

theorem cur_matOf [Inhabited F] (cb : Bool) (rows : List (Blake2sBinaryCols F)) {i : ℕ}
    (hi : i < rows.length) :
    rowOf (rowEnv (instOf (blake2sAir cb) (matOf rows) []) i) (AirLayout.from_air (blake2sAir (F := F) cb)) 0 =
      getc (rows.getD i Blake2sBinaryCols.zero) := by
  funext c
  simp only [rowOf, rowEnv, instOf, AirLayout.from_air, blake2sAir]
  by_cases hc : c < NUM_BLAKE2S_BINARY_COLS
  · rw [Plonky3Lean.Proofs.KeccakAir.getD_map_range_of _ rfl hc, matOf_cell rows hi hc]
  · simp [hc, getc_of_le _ (Nat.le_of_not_lt hc)]

/-- Completeness: on a positive power-of-two number of inputs, the generator's trace satisfies the AIR.

This holds in characteristic 2, with or without the booleanity. -/
theorem complete [Inhabited F] [DecidableEq F] (h2 : (2 : F) = 0) (cb : Bool)
    {inputs : List Blake2sCompressionInput}
    (h : inputs.length ≠ 0 ∧ 2 ^ Nat.log 2 inputs.length = inputs.length) (e : ℕ) :
    ∃ M, generate_binary_trace_rows (F := F) inputs e = some M ∧
      Satisfies (constraints (blake2sAir cb)) (instOf (blake2sAir cb) M []) := by
  refine ⟨matOf (inputs.map (generate_trace_row Blake2sBinaryCols.zero)), by simp [generate_eq, h2, h], ?_⟩
  rw [Plonky3Lean.Proofs.KeccakAir.satisfies_iff_rows]
  change ∀ i < (matOf (inputs.map (generate_trace_row (F := F) Blake2sBinaryCols.zero))).height, _
  rw [matOf_height]
  intro i hi
  refine gen_eval (inputs.getD i ⟨[], [], 0, false⟩) h2 cb _ _ ?_
  rw [cur_matOf cb _ hi, List.getD_eq_getElem _ _ hi, List.getElem_map, List.getD_eq_getElem _ _
    (by simpa using hi)]

end Plonky3Lean.Proofs.Blake2sAir
