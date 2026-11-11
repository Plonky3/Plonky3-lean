module

public import Plonky3Lean.Proofs.Blake3Air.Binary.Cells
public import Plonky3Lean.Proofs.Blake3Air.Complete

@[expose] public section

/-!
# Completeness of the characteristic-2 BLAKE3 AIR

Over a field of characteristic 2, the generator succeeds on any nonempty power-of-two list of inputs.

Its trace satisfies the AIR, with or without the input booleanity.
-/

set_option linter.unusedSectionVars false

namespace Plonky3Lean.Proofs.Blake3Air.Binary

open p3_air.builder.mirror p3_air.air.mirror p3_blake3_air.mirror p3_blake3_air.mirror.binary
open Plonky3Lean.Spec.Air Plonky3Lean.Proofs.Air Plonky3Lean.Proofs.KeccakAir Plonky3Lean.Proofs.Blake3Air

variable {F : Type} [Field F] [DecidableEq F] (h2 : (2 : F) = 0)

theorem schedule_pre : ∀ k < 56, pre (schedule.getD k (0, 0)).1 (schedule.getD k (0, 0)).2 = schedule.take k ∧
    (schedule.getD k (0, 0)).1 < 7 ∧ (schedule.getD k (0, 0)).2 < 8 := by decide

theorem length_schedule : schedule.length = 56 := rfl

include h2

/-- Along the schedule, a generated row's G steps satisfy their constraints. -/
theorem gen_checks (env : Var → F) (L : AirLayout) (input : Blake3CompressionInput)
    (hloc : ∀ c < NUM_BLAKE3_BINARY_COLS, rowOf env L 0 c = getcB (generate_trace_row (F := F) input) c) :
    ∀ n ≤ 56, ∀ st : State F, StB st (flat (wfold input.block (schedule.take (56 - n)) (initW input))) →
      checksP (fun rg : ℕ × ℕ => g_step (propBuilder env L) (rowOf env L 0) rg.1 rg.2)
        (schedule.drop (56 - n)) st := by
  intro n
  induction n with
  | zero =>
    intro _ st _
    rw [show 56 - 0 = 56 from rfl, List.drop_of_length_le (by rw [length_schedule])]
    trivial
  | succ n ih =>
    intro hn st hst
    have hk : 56 - (n + 1) < 56 := by omega
    obtain ⟨hpre, hr, hg⟩ := schedule_pre _ hk
    set rg := schedule.getD (56 - (n + 1)) (0, 0) with hrg
    rw [show schedule.drop (56 - (n + 1)) = rg :: schedule.drop (56 - n) by
      rw [List.drop_eq_getElem_cons (by rw [length_schedule]; omega), hrg, List.getD_eq_getElem _ _
        (by rw [length_schedule]; omega), show 56 - (n + 1) + 1 = 56 - n by omega]]
    obtain ⟨r, g⟩ := rg
    simp only at hpre hr hg
    -- The state before the step, as the generator holds it.
    set σ := flat (wfold input.block (pre r g) (initW input)) with hσ
    have hst' : StB st σ := by rw [hσ, hpre]; exact hst
    have hrow := gen_row_eq (F := F) input
    have hcell : ∀ {c : ℕ}, c < NUM_BLAKE3_BINARY_COLS → rowOf env L 0 c =
        getcB (generate_trace_row (F := F) input) c := fun hc => hloc _ hc
    -- The cells of the step's message words and witness columns.
    have hm : ∀ t < 2, BitsRep (fun k => rowOf env L 0 (col.block (msgIdx r (2 * g + t)) k))
        ((permute^[r] input.block) (2 * g + t)) := by
      intro t ht k hk
      have hi : msgIdx r (2 * g + t) < 16 := by
        rw [msgIdx_eq]; exact Plonky3Lean.Proofs.Blake3.permPow_lt _ _ (by omega)
      beta_reduce
      rw [hcell (by simp only [col.block, NUM_BLAKE3_BINARY_COLS]; omega), cellB_block _ hi hk, hrow,
        permute_iter_apply, ← msgIdx_eq]
      exact u32_bits_eq _ hk
    have hw := wstep_words input.block (wfold input.block (pre r g) (initW input)) r g
    have hcol : ∀ {f : Blake3BinaryGCols F → ℕ → F} {c : ℕ → ℕ} {n' : ℕ},
        (∀ k < n', c k < NUM_BLAKE3_BINARY_COLS) →
        (∀ k < n', getcB (generate_trace_row (F := F) input) (c k) = f ((generate_trace_row input).rounds r g) k) →
        ∀ k < n', rowOf env L 0 (c k) = f (generate_g (wstep input.block
          (wfold input.block (pre r g) (initW input)) (r, g)).1) k := by
      intro f c n' hc hf k hk
      rw [hcell (hc k hk), hf k hk, hrow]
      simp only [hr, hg, ite_true]
    dsimp only at hw
    have h0 := slot_lt g 0; have h1 := slot_lt g 1; have h2' := slot_lt g 2; have h3 := slot_lt g 3
    have e1 := hcol (f := fun c => c.add1_carries) (c := fun k => col.add1_carries r g k) (n' := 31)
      (fun k hk => by simp only [col.add1_carries, col.g, NUM_BLAKE3_BINARY_COLS]; omega)
      (fun k hk => cellB_add1 _ hr hg hk)
    have e2 := hcol (f := fun c => c.d1) (c := fun k => col.d1 r g k) (n' := 32)
      (fun k hk => by simp only [col.d1, col.g, NUM_BLAKE3_BINARY_COLS]; omega)
      (fun k hk => cellB_d1 _ hr hg hk)
    have e3 := hcol (f := fun c => c.b1) (c := fun k => col.b1 r g k) (n' := 32)
      (fun k hk => by simp only [col.b1, col.g, NUM_BLAKE3_BINARY_COLS]; omega)
      (fun k hk => cellB_b1 _ hr hg hk)
    have e4 := hcol (f := fun c => c.add2_carries) (c := fun k => col.add2_carries r g k) (n' := 31)
      (fun k hk => by simp only [col.add2_carries, col.g, NUM_BLAKE3_BINARY_COLS]; omega)
      (fun k hk => cellB_add2 _ hr hg hk)
    have e5 := hcol (f := fun c => c.d2) (c := fun k => col.d2 r g k) (n' := 32)
      (fun k hk => by simp only [col.d2, col.g, NUM_BLAKE3_BINARY_COLS]; omega)
      (fun k hk => cellB_d2 _ hr hg hk)
    have e6 := hcol (f := fun c => c.b2) (c := fun k => col.b2 r g k) (n' := 32)
      (fun k hk => by simp only [col.b2, col.g, NUM_BLAKE3_BINARY_COLS]; omega)
      (fun k hk => cellB_b2 _ hr hg hk)
    simp only [hw, generate_g] at e1 e2 e3 e4 e5 e6
    have hGB := gB_complete h2 (hst' _ h0).1 (hst' _ h1).2.1 (hst' _ h2').2.2.1 (hst' _ h3).2.2.2
      (hm 0 (by norm_num)) (hm 1 (by norm_num))
      (fun k hk => (e1 k hk).trans (carries_bits _ _ hk))
      (fun k hk => (e2 k hk).trans (u32_bits_eq _ hk)) (fun k hk => (e3 k hk).trans (u32_bits_eq _ hk))
      (fun k hk => (e4 k hk).trans (carries_bits _ _ hk))
      (fun k hk => (e5 k hk).trans (u32_bits_eq _ hk)) (fun k hk => (e6 k hk).trans (u32_bits_eq _ hk))
    refine ⟨?_, ?_⟩
    · simp only [g_step, prop_eval_g, true_and]
      exact hGB
    · refine ih (by omega) _ ?_
      have hnext := (step_rep h2 env L hst' h0 h1 h2' h3 (hm 0 (by norm_num)) (hm 1 (by norm_num)) hGB True).1
      rw [show schedule.take (56 - n) = pre r g ++ [(r, g)] by
        rw [hpre, show 56 - n = 56 - (n + 1) + 1 by omega, List.take_add_one,
          List.getElem?_eq_getElem (by rw [length_schedule]; omega), Option.toList_some, hrg,
          List.getD_eq_getElem _ _ (by rw [length_schedule]; omega)],
        wfold_append]
      simp only [wfold, List.foldl_cons, List.foldl_nil]
      rw [flat_wstep]
      exact hnext

/-- A generated row satisfies the row constraints, with or without the booleanity. -/
theorem gen_row_holds (env : Var → F) (L : AirLayout) (cb : Bool) (input : Blake3CompressionInput)
    (hloc : ∀ c < NUM_BLAKE3_BINARY_COLS, rowOf env L 0 c = getcB (generate_trace_row (F := F) input) c) :
    binary.eval cb (propBuilder env L) True := by
  have hrow := gen_row_eq (F := F) input
  have hcv : ∀ i < 8, BitsRep (fun k => rowOf env L 0 (col.chaining_value i k)) (input.chaining_value i) := by
    intro i hi k hk
    beta_reduce
    rw [hloc _ (by simp only [col.chaining_value, NUM_BLAKE3_BINARY_COLS]; omega), cellB_cv _ hi hk, hrow]
    exact u32_bits_eq _ hk
  have hblk : ∀ i < 16, BitsRep (fun k => rowOf env L 0 (col.block i k)) (input.block i) := by
    intro i hi k hk
    beta_reduce
    rw [hloc _ (by simp only [col.block, NUM_BLAKE3_BINARY_COLS]; omega), cellB_block _ hi hk, hrow]
    exact u32_bits_eq _ hk
  have hd : ∀ j < 4, BitsRep (initial_d (rowOf env L 0) j) (initW input 3 j) := by
    intro j hj k hk
    simp only [initial_d]
    rw [hloc _ (by simp only [binary.col.counter_low, NUM_BLAKE3_BINARY_COLS]; omega), cellB_row3 _ hj hk, hrow]
    interval_cases j <;> simp [initW, u32_bits_eq _ hk]
  apply (eval_iff env L cb).mpr
  refine ⟨fun _ => ?_, ?_⟩
  · simp [binary.assert_inputs, AirBuilder.assert_bools, AirBuilder.bool_check, AirBuilder.assert_zeros,
      propBuilder, foldl_and]
    refine ⟨fun i hi k hk => ?_, fun i hi k hk => ?_, fun j hj k hk => ?_⟩
    · have e := hcv i hi k hk; simp only at e
      rw [e]; cases (input.chaining_value i).getLsbD k <;> simp [bitF]
    · have e := hblk i hi k hk; simp only at e
      rw [e]; cases (input.block i).getLsbD k <;> simp [bitF]
    · have e := hd j hj k hk
      rw [e]; cases (initW input 3 j).getLsbD k <;> simp [bitF]
  · have h := gen_checks h2 env L input hloc 56 le_rfl (binary.initial_state (propBuilder env L) (rowOf env L 0))
    simp only [Nat.sub_self, List.take_zero, List.drop_zero] at h
    refine h fun j hj => ⟨?_, ?_, ?_, ?_⟩
    · simpa [wfold, flat, show j / 4 = 0 by omega, show j % 4 = j by omega, initW, binary.initial_state]
        using hcv j (by omega)
    · simpa [wfold, flat, show (4 + j) / 4 = 1 by omega, show (4 + j) % 4 = j by omega, initW,
        binary.initial_state] using hcv (4 + j) (by omega)
    · simp only [wfold, List.foldl_nil, flat, show (8 + j) / 4 = 2 by omega, show (8 + j) % 4 = j by omega]
      intro k hk
      exact u32_bits_eq _ hk
    · simpa [wfold, flat, show (12 + j) / 4 = 3 by omega, show (12 + j) % 4 = j by omega,
        binary.initial_state] using hd j hj

omit h2

section mat

variable (rows : List (Blake3BinaryCols F))

/-- The trace of a list of rows. -/
def matOfB : Mat F := ⟨NUM_BLAKE3_BINARY_COLS, rows.flatMap Blake3BinaryCols.cells⟩

theorem matOfB_height : (matOfB rows).height = rows.length := by
  simp only [Mat.height, matOfB, NUM_BLAKE3_BINARY_COLS, List.length_flatMap, length_cellsB,
    List.map_const', List.sum_replicate, smul_eq_mul]
  simp

theorem matOfB_cell {i c : ℕ} (hi : i < rows.length) (hc : c < NUM_BLAKE3_BINARY_COLS) :
    ((matOfB rows).row i).getD c 0 = getcB (rows.getD i ⟨fun _ _ => 0, fun _ _ => 0, fun _ => 0, fun _ => 0,
      fun _ => 0, fun _ => 0, fun _ _ => ⟨fun _ => 0, fun _ => 0, fun _ => 0, fun _ => 0, fun _ => 0,
      fun _ => 0⟩⟩) c := by
  have hk : i * NUM_BLAKE3_BINARY_COLS + c < NUM_BLAKE3_BINARY_COLS * rows.length := by
    have h1 := Nat.mul_le_mul_right NUM_BLAKE3_BINARY_COLS (Nat.succ_le_of_lt hi)
    rw [Nat.succ_mul, Nat.mul_comm rows.length] at h1
    omega
  simp only [Mat.row, matOfB, getcB]
  rw [List.getD_eq_getElem?_getD, List.getElem?_take, ite_eq_left hc, List.getElem?_drop,
    ← List.getD_eq_getElem?_getD,
    Plonky3Lean.Proofs.Keccak.getD_flatMap_uniform _ _ (fun r => length_cellsB r) _ _ _ hk,
    show (i * NUM_BLAKE3_BINARY_COLS + c) / NUM_BLAKE3_BINARY_COLS = i by
      rw [Nat.mul_comm, Nat.mul_add_div (by simp [NUM_BLAKE3_BINARY_COLS]), Nat.div_eq_of_lt hc, add_zero],
    show (i * NUM_BLAKE3_BINARY_COLS + c) % NUM_BLAKE3_BINARY_COLS = c by
      rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hc]]

end mat

theorem generate_binary_eq (inputs : List Blake3CompressionInput) (e : ℕ) :
    generate_binary_trace_rows (F := F) inputs e =
      if (2 : F) ≠ 0 then none else if inputs.length = 0 then none
      else if inputs.length &&& (inputs.length - 1) ≠ 0 then none
      else some (matOfB (inputs.map generate_trace_row)) := rfl

include h2 in
/-- Completeness over a field of characteristic 2.

Whenever the generator returns a trace, it satisfies the AIR, with or without the booleanity. -/
theorem complete [Inhabited F] (cb : Bool) (inputs : List Blake3CompressionInput) (e : ℕ) {M : Mat F}
    (hM : generate_binary_trace_rows (F := F) inputs e = some M) :
    Satisfies (constraints (binaryAir cb)) (instOf (binaryAir cb) M []) := by
  rw [generate_binary_eq] at hM
  split_ifs at hM
  obtain rfl := Option.some.inj hM
  rw [satisfies_iff_rows]
  change ∀ i < (matOfB (inputs.map (generate_trace_row (F := F)))).height, _
  rw [matOfB_height]
  intro i hi
  have hl : i < inputs.length := by simpa using hi
  refine gen_row_holds h2 _ _ cb (inputs.getD i ⟨fun _ => 0, fun _ => 0, 0, 0, 0⟩) fun c hc => ?_
  simp only [rowOf, rowEnv, instOf, AirLayout.from_air, binaryAir]
  rw [getD_map_range_of _ rfl hc, matOfB_cell _ hi hc]
  simp [List.getD_eq_getElem?_getD, hl]

include h2 in
/-- Over a field of characteristic 2, the generator succeeds on any list of 2^k inputs. -/
theorem generate_some (inputs : List Blake3CompressionInput) (e : ℕ) {k : ℕ} (hk : inputs.length = 2 ^ k) :
    generate_binary_trace_rows (F := F) inputs e = some (matOfB (inputs.map generate_trace_row)) := by
  rw [generate_binary_eq, hk, Nat.and_two_pow_sub_one_eq_mod, Nat.mod_self]
  simp [h2]

end Plonky3Lean.Proofs.Blake3Air.Binary
