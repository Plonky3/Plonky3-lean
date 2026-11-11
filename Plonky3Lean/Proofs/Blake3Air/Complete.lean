module

public import Plonky3Lean.Proofs.Blake3Air.GenRow
public import Plonky3Lean.Proofs.Blake3Air.Sound
public import Plonky3Lean.Proofs.Air.Check
public import Plonky3Lean.Proofs.Hash.Keccak.Lanes

@[expose] public section

/-!
# Completeness of the prime-field BLAKE3 AIR

The generator's trace satisfies the AIR, for any number of inputs that is a power of two, and in every field.

Row k compresses input k under counter k and block length n, the number of rows, with no flags.
-/

set_option linter.unusedSectionVars false

namespace Plonky3Lean.Proofs.Blake3Air

open p3_air.builder.mirror p3_air.air.mirror p3_blake3_air.mirror Plonky3Lean.Spec.Air
open Plonky3Lean.Proofs.Air Plonky3Lean.Proofs.KeccakAir

variable {F : Type} [Field F]

/-! ## The generator's states -/

section gen

variable (input : ℕ → Word) (counter block_len : ℕ)

/-- The generator's initial state. -/
def genInit : WState := fun r i =>
  if r = 0 then input (16 + i)
  else if r = 1 then input (16 + (4 + i))
  else if r = 2 then ivWord i
  else if i = 0 then BitVec.ofNat 32 counter
  else if i = 1 then BitVec.ofNat 32 (counter / 2 ^ 32)
  else if i = 2 then BitVec.ofNat 32 block_len
  else 0

/-- The generator's state before round r, from the initial state S. -/
def genSt (S : WState) : ℕ → WState
  | 0 => S
  | r + 1 => (generate_trace_row_for_round (F := F) (genSt S r) (permute^[r] input)).2

theorem gen_fold (S : WState) {n : ℕ} :
    (List.range n).foldl
      (fun (acc : (ℕ → FullRound F) × WState × (ℕ → Word)) r =>
        let (rounds, state, m_vec) := acc
        let m_vec := if r = 0 then m_vec else permute m_vec
        let (fr, state) := generate_trace_row_for_round state m_vec
        (Function.update rounds r fr, state, m_vec))
      ((Blake3Cols.zero (T := F)).full_rounds, S, input) =
      (fun r => if r < n then (generate_trace_row_for_round (F := F) (genSt (F := F) input S r)
          (permute^[r] input)).1 else (Blake3Cols.zero (T := F)).full_rounds r,
        genSt (F := F) input S n, if n = 0 then input else permute^[n - 1] input) := by
  induction n with
  | zero => simp [genSt]
  | succ n ih =>
    rw [List.range_succ, List.foldl_append, ih]
    simp only [List.foldl_cons, List.foldl_nil, Nat.add_one_ne_zero, ite_false, Nat.add_sub_cancel]
    have hm : (if n = 0 then (if n = 0 then input else permute^[n - 1] input)
        else permute (if n = 0 then input else permute^[n - 1] input)) = permute^[n] input := by
      rcases n with _ | n
      · rfl
      · simp [← Function.iterate_succ_apply' permute]
    rw [hm]
    refine Prod.ext ?_ (Prod.ext rfl rfl)
    funext r
    simp only [Function.update_apply]
    split_ifs with h1 h2 h2 <;> first | subst h1; rfl | rfl | omega

end gen

end Plonky3Lean.Proofs.Blake3Air

namespace Plonky3Lean.Proofs.Blake3Air

open p3_air.builder.mirror p3_air.air.mirror p3_blake3_air.mirror Plonky3Lean.Spec.Air
open Plonky3Lean.Proofs.Air Plonky3Lean.Proofs.KeccakAir

variable {F : Type} [Field F] (input : ℕ → Word) (counter block_len : ℕ)

/-- The generator's state before round r. -/
abbrev gst (r : ℕ) : WState := genSt (F := F) input (genInit input counter block_len) r

/-- The generated row, field by field. -/
theorem gen_row_eq :
    generate_trace_rows_for_perm (F := F) input counter block_len =
      { inputs := fun i => u32_to_bits_le (input i)
        chaining_values := fun h j => u32_to_bits_le (input (16 + 4 * h + j))
        counter_low := u32_to_bits_le (BitVec.ofNat 32 counter)
        counter_hi := u32_to_bits_le (BitVec.ofNat 32 (counter / 2 ^ 32))
        block_len := u32_to_bits_le (BitVec.ofNat 32 block_len)
        flags := fun _ => 0
        initial_row0 := fun i l => if l = 0 then lowLimb (input (16 + i)) else highLimb (input (16 + i))
        initial_row2 := fun i l => (ivHalf i l : F)
        full_rounds := fun r => if r < 7 then
            (generate_trace_row_for_round (F := F) (gst (F := F) input counter block_len r)
              (permute^[r] input)).1
          else (Blake3Cols.zero (T := F)).full_rounds r
        final_round_helpers := fun i => u32_to_bits_le (gst (F := F) input counter block_len 7 2 i)
        outputs := fun q i =>
          let st := gst (F := F) input counter block_len 7
          if q = 0 then u32_to_bits_le (st 0 i ^^^ st 2 i)
          else if q = 1 then u32_to_bits_le (st 1 i ^^^ st 3 i)
          else if q = 2 then u32_to_bits_le (st 2 i ^^^ input (16 + i))
          else u32_to_bits_le (st 3 i ^^^ input (20 + i)) } := by
  unfold generate_trace_rows_for_perm
  simp only [gen_fold]
  rfl

omit [Field F] in
/-- The cells of state s of round rd of a row are that state's entries. -/
theorem stateAt_getc [Zero F] (row : Blake3Cols F) {rd s : ℕ} (hr : rd < 7) (hs : s < 4) :
    let st := [(row.full_rounds rd).state_prime, (row.full_rounds rd).state_middle,
      (row.full_rounds rd).state_middle_prime, (row.full_rounds rd).state_output].getD s
      Blake3Cols.zeroState
    (∀ j < 4, ∀ l < 2, (stateAt (getc row) (col.state rd s)).row0 j l = st.row0 j l) ∧
    (∀ j < 4, ∀ k < 32, (stateAt (getc row) (col.state rd s)).row1 j k = st.row1 j k) ∧
    (∀ j < 4, ∀ l < 2, (stateAt (getc row) (col.state rd s)).row2 j l = st.row2 j l) ∧
    (∀ j < 4, ∀ k < 32, (stateAt (getc row) (col.state rd s)).row3 j k = st.row3 j k) := by
  refine ⟨fun j hj l hl => ?_, fun j hj k hk => ?_, fun j hj l hl => ?_, fun j hj k hk => ?_⟩ <;>
    simp only [stateAt] <;> rw [Nat.add_assoc] <;> try rw [Nat.add_assoc]
  · rw [cell_state row hr hs (by omega), getD_stateCells _ (by omega)]
    simp [show 2 * j + l < 8 by omega, show (2 * j + l) / 2 = j by omega, show (2 * j + l) % 2 = l by omega]
  · rw [cell_state row hr hs (by omega), getD_stateCells _ (by omega)]
    simp [show ¬ 8 + (32 * j + k) < 8 by omega, show 8 + (32 * j + k) < 136 by omega]
    congr 1 <;> omega
  · rw [cell_state row hr hs (by omega), getD_stateCells _ (by omega)]
    simp [show ¬ 136 + (2 * j + l) < 8 by omega, show ¬ 136 + (2 * j + l) < 136 by omega,
      show 136 + (2 * j + l) < 144 by omega]
    congr 1 <;> omega
  · rw [cell_state row hr hs (by omega), getD_stateCells _ (by omega)]
    simp [show ¬ 144 + (32 * j + k) < 8 by omega, show ¬ 144 + (32 * j + k) < 136 by omega,
      show ¬ 144 + (32 * j + k) < 144 by omega]
    congr 1 <;> omega

omit [Field F] in
theorem gRep_cells [Field F] (row : Blake3Cols F) {rd s : ℕ} (hr : rd < 7) (hs : s < 4) {σ : WState}
    (h : GRep ([(row.full_rounds rd).state_prime, (row.full_rounds rd).state_middle,
      (row.full_rounds rd).state_middle_prime, (row.full_rounds rd).state_output].getD s
      Blake3Cols.zeroState) σ) : GRep (stateAt (getc row) (col.state rd s)) σ := by
  obtain ⟨e0, e1, e2, e3⟩ := stateAt_getc row hr hs
  intro j hj
  obtain ⟨a, b, c, d⟩ := h j hj
  exact ⟨⟨(e0 j hj 0 (by norm_num)).trans a.1, (e0 j hj 1 (by norm_num)).trans a.2⟩,
    fun k hk => (e1 j hj k hk).trans (b k hk),
    ⟨(e2 j hj 0 (by norm_num)).trans c.1, (e2 j hj 1 (by norm_num)).trans c.2⟩,
    fun k hk => (e3 j hj k hk).trans (d k hk)⟩

theorem bitF_bool (b : Bool) : (bitF b : F) * (bitF b - 1) = 0 := by cases b <;> simp [bitF]

theorem bool_of_bitsRep {f : ℕ → F} {w : Word} (h : BitsRep f w) {k : ℕ} (hk : k < 32) :
    f k * (f k - 1) = 0 := by rw [h k hk]; exact bitF_bool _

theorem ivWord_limbs : ∀ j < 4, (ivWord j).toNat % 2 ^ 16 = ivHalf j 0 ∧
    (ivWord j).toNat / 2 ^ 16 = ivHalf j 1 := by decide

/-- Output cells holding the bits of a xor of words satisfy the xor constraints. -/
theorem xor_eq_of_bits {o x y : ℕ → F} {wx wy : Word} (hx : BitsRep x wx) (hy : BitsRep y wy)
    (ho : BitsRep o (wx ^^^ wy)) :
    ∀ k ∈ List.range 32, o k - p3_keccak_air.mirror.xor fieldOps (x k) (y k) = 0 := by
  intro k hk
  rw [List.mem_range] at hk
  rw [ho k hk, hx k hk, hy k hk, xor_bit, BitVec.getLsbD_xor, sub_self]

section genRow

variable [DecidableEq F]

/-- Each generated row satisfies the row constraints, in every field. -/
theorem gen_rowSpec : RowSpec (getc (generate_trace_rows_for_perm (F := F) input counter block_len)) := by
  set row := generate_trace_rows_for_perm (F := F) input counter block_len with hrowdef
  have hrow := gen_row_eq (F := F) input counter block_len
  rw [← hrowdef] at hrow
  -- The bit cells of the inputs.
  have hin : ∀ i < 16, BitsRep (fun k => getc row (col.inputs i k)) (input i) := fun i hi k hk => by
    beta_reduce; rw [cell_inputs row hi hk, hrow]; exact u32_bits_eq _ hk
  have hcv : ∀ h < 2, ∀ j < 4, BitsRep (fun k => getc row (col.chaining_values h j k))
      (input (16 + 4 * h + j)) := fun h hh j hj k hk => by
    beta_reduce; rw [cell_cv row hh hj hk, hrow]; exact u32_bits_eq _ hk
  have h3 : ∀ j < 4, BitsRep (initial_row_3 (getc row) j) (gst (F := F) input counter block_len 0 3 j) := by
    intro j hj k hk
    simp only [initial_row_3, gst, genSt, genInit]
    interval_cases j
    · rw [Nat.mul_zero, Nat.zero_add, cell_counter_low row hk, hrow]; exact u32_bits_eq _ hk
    · rw [show 32 * 1 + k = 32 + k by omega, cell_counter_hi row hk, hrow]; exact u32_bits_eq _ hk
    · rw [show 32 * 2 + k = 64 + k by omega, cell_block_len row hk, hrow]; exact u32_bits_eq _ hk
    · rw [show 32 * 3 + k = 96 + k by omega, cell_flags row hk, hrow]; simp [bitF]
  -- The four trace states of each round hold the generator's states.
  have hst : ∀ rd < 7, ∀ s < 4, GRep (stateAt (getc row) (col.state rd s))
      ([halfRounds (gst (F := F) input counter block_len rd) (permute^[rd] input) false false 0,
        halfRounds (halfRounds (gst (F := F) input counter block_len rd) (permute^[rd] input) false false 0)
          (permute^[rd] input) false true 1,
        halfRounds (halfRounds (halfRounds (gst (F := F) input counter block_len rd) (permute^[rd] input)
          false false 0) (permute^[rd] input) false true 1) (permute^[rd] input) true false 8,
        gst (F := F) input counter block_len (rd + 1)].getD s 0) := by
    intro rd hr s hs
    apply gRep_cells row hr hs
    rw [hrow]
    simp only [hr, ite_true, generate_trace_row_for_round]
    interval_cases s <;>
      simp only [List.getD_cons_zero, List.getD_cons_succ, gst, genSt, generate_trace_row_for_round] <;>
      exact gRep_save _
  have hinit : GRep (round_input (getc row) 0) (gst (F := F) input counter block_len 0) := by
    intro j hj
    simp only [round_input, ite_true, initial_state]
    refine ⟨?_, ?_, ?_, h3 j hj⟩
    · have := limbsRep_save (F := F) (input (16 + j))
      refine ⟨?_, ?_⟩ <;> simp only [gst, genSt, genInit, ite_true] <;>
        rw [cell_init0 row hj (by norm_num), hrow]
      exacts [this.1, this.2]
    · have hg : gst (F := F) input counter block_len 0 1 j = input (16 + 4 * 1 + j) := by
        simp only [gst, genSt, genInit, one_ne_zero, ite_false, ite_true]; congr 1; omega
      rw [hg]; exact hcv 1 (by norm_num) j hj
    · obtain ⟨e0, e1⟩ := ivWord_limbs j hj
      have hg : gst (F := F) input counter block_len 0 2 j = ivWord j := by
        simp only [gst, genSt, genInit, OfNat.ofNat_ne_zero, ite_false, OfNat.ofNat_ne_one, ite_true]
      rw [hg]
      refine ⟨?_, ?_⟩
      · show getc row (col.initial_row2 j 0) = _
        rw [cell_init2 row hj (by norm_num), hrow, e0]
      · show getc row (col.initial_row2 j 1) = _
        rw [cell_init2 row hj (by norm_num), hrow, e1]
  have hinput : ∀ rd < 7, GRep (round_input (getc row) rd) (gst (F := F) input counter block_len rd) := by
    intro rd hr
    rcases rd with _ | rd
    · exact hinit
    · simpa [round_input, fullRoundAt] using hst rd (by omega) 3 (by norm_num)
  have hm : ∀ rd, ∀ i < 16, LimbsRep ((permute^[rd] fun i => limbs fun k => getc row (col.inputs i k)) i)
      ((permute^[rd] input) i) := by
    intro rd i hi
    rw [permute_iter_apply, permute_iter_apply]
    exact limbsRep_limbs (hin _ (Plonky3Lean.Proofs.Blake3.permPow_lt rd i hi))
  -- The final state, its helpers and the outputs.
  have hfin : GRep (final (getc row)) (gst (F := F) input counter block_len 7) := by
    simpa [final, fullRoundAt] using hst 6 (by norm_num) 3 (by norm_num)
  have hhelp : ∀ j < 4, BitsRep (fun k => getc row (col.final_round_helpers j k))
      (gst (F := F) input counter block_len 7 2 j) := fun j hj k hk => by
    beta_reduce; rw [cell_helpers row hj hk, hrow]; exact u32_bits_eq _ hk
  have hout : ∀ q < 4, ∀ j < 4, BitsRep (fun k => getc row (col.outputs q j k))
      (let st := gst (F := F) input counter block_len 7
       if q = 0 then st 0 j ^^^ st 2 j else if q = 1 then st 1 j ^^^ st 3 j
       else if q = 2 then st 2 j ^^^ input (16 + j) else st 3 j ^^^ input (20 + j)) := by
    intro q hq j hj k hk
    beta_reduce
    rw [cell_outputs row hq hj hk, hrow]
    interval_cases q <;> exact u32_bits_eq _ hk
  refine ⟨?_, fun j hj => ?_, fun j hj => ?_, fun rd hrd => ?_, fun j hj => ?_, fun j hj k hk => ?_,
    fun j hj => ?_, fun j hj => ?_, fun j hj => ?_, fun j hj => ?_⟩
  · intro elem helem k hk
    rw [List.mem_range] at hk
    simp only [List.mem_append, List.mem_map, List.mem_range] at helem
    rcases helem with ((⟨i, hi, rfl⟩ | ⟨j, hj, rfl⟩) | ⟨j, hj, rfl⟩) | ⟨j, hj, rfl⟩
    · exact bool_of_bitsRep (hin i hi) hk
    · exact bool_of_bitsRep (hcv 0 (by norm_num) j hj) hk
    · exact bool_of_bitsRep (hcv 1 (by norm_num) j hj) hk
    · exact bool_of_bitsRep (h3 j hj) hk
  · rw [List.mem_range] at hj
    obtain ⟨hL0, hL1⟩ := limbsRep_limbs (hcv 0 (by norm_num) j hj)
    obtain ⟨hS0, hS1⟩ := limbsRep_save (F := F) (input (16 + j))
    simp only [limbs, ite_true, one_ne_zero, ite_false, Nat.mul_zero, Nat.add_zero] at hL0 hL1 hS0 hS1
    have hI : row.initial_row0 = fun i l => if l = 0 then lowLimb (input (16 + i))
        else highLimb (input (16 + i)) := by rw [hrow]
    rw [cell_init0 row hj (by norm_num), cell_init0 row hj (by norm_num), hI, hL0, hL1]
    simp only [ite_true, one_ne_zero, ite_false]
    exact ⟨sub_eq_zero.mpr hS0.symm, sub_eq_zero.mpr hS1.symm⟩
  · rw [List.mem_range] at hj
    have hI : row.initial_row2 = fun i l => (ivHalf i l : F) := by rw [hrow]
    rw [cell_init2 row hj (by norm_num), cell_init2 row hj (by norm_num), hI]
    exact ⟨sub_self _, sub_self _⟩
  · rw [List.mem_range] at hrd
    have h0 := hst rd hrd 0 (by norm_num)
    have h1 := hst rd hrd 1 (by norm_num)
    have h2 := hst rd hrd 2 (by norm_num)
    have h4 := hst rd hrd 3 (by norm_num)
    simp only [List.getD_cons_zero, List.getD_cons_succ] at h0 h1 h2 h4
    exact round_complete (hinput rd hrd) (hm rd) h0 h1 h2 h4
  · rw [List.mem_range] at hj
    obtain ⟨hL0, hL1⟩ := limbsRep_limbs (hhelp j hj)
    obtain ⟨-, -, hr2, -⟩ := hfin j hj
    simp only [limbs, ite_true, one_ne_zero, ite_false] at hL0 hL1
    exact ⟨sub_eq_zero.mpr (hL0.trans hr2.1.symm), sub_eq_zero.mpr (hL1.trans hr2.2.symm)⟩
  · rw [List.mem_range] at hj hk
    exact bool_of_bitsRep (hout 0 (by norm_num) j hj) hk
  · rw [List.mem_range] at hj
    obtain ⟨hr0, -, -, -⟩ := hfin j hj
    refine xorC_complete (by norm_num) (hout 0 (by norm_num) j hj) (hhelp j hj) ?_
    simpa [rotateLeft_zero', BitVec.xor_assoc] using hr0
  · rw [List.mem_range] at hj
    obtain ⟨-, hr1, -, hr3⟩ := hfin j hj
    exact xor_eq_of_bits hr1 hr3 (by simpa using hout 1 (by norm_num) j hj)
  · rw [List.mem_range] at hj
    refine xor_eq_of_bits (hcv 0 (by norm_num) j hj) (hhelp j hj) ?_
    simpa [BitVec.xor_comm] using hout 2 (by norm_num) j hj
  · rw [List.mem_range] at hj
    obtain ⟨-, -, -, hr3⟩ := hfin j hj
    refine xor_eq_of_bits (hcv 1 (by norm_num) j hj) hr3 ?_
    have := hout 3 (by norm_num) j hj
    simp only [OfNat.ofNat_ne_zero, ite_false, OfNat.ofNat_ne_one] at this
    rw [BitVec.xor_comm, show 16 + 4 * 1 + j = 20 + j by omega]
    simpa using this

end genRow

/-! ## The trace -/

section mat

variable (rows : List (Blake3Cols F))

/-- The trace of a list of rows. -/
def matOf : Mat F := ⟨NUM_BLAKE3_COLS, rows.flatMap Blake3Cols.cells⟩

theorem matOf_height : (matOf rows).height = rows.length := by
  simp only [Mat.height, matOf, NUM_BLAKE3_COLS, List.length_flatMap, length_cells, List.map_const',
    List.sum_replicate, smul_eq_mul]
  simp

theorem matOf_cell {i c : ℕ} (hi : i < rows.length) (hc : c < NUM_BLAKE3_COLS) :
    ((matOf rows).row i).getD c 0 = getc (rows.getD i Blake3Cols.zero) c := by
  have hk : i * NUM_BLAKE3_COLS + c < NUM_BLAKE3_COLS * rows.length := by
    have h1 := Nat.mul_le_mul_right NUM_BLAKE3_COLS (Nat.succ_le_of_lt hi)
    rw [Nat.succ_mul, Nat.mul_comm rows.length] at h1
    omega
  simp only [Mat.row, matOf, getc]
  rw [List.getD_eq_getElem?_getD, List.getElem?_take, ite_eq_left hc, List.getElem?_drop,
    ← List.getD_eq_getElem?_getD,
    Plonky3Lean.Proofs.Keccak.getD_flatMap_uniform _ _ (fun r => length_cells r) _ _ _ hk,
    show (i * NUM_BLAKE3_COLS + c) / NUM_BLAKE3_COLS = i by
      rw [Nat.mul_comm, Nat.mul_add_div (by simp [NUM_BLAKE3_COLS]), Nat.div_eq_of_lt hc, add_zero],
    show (i * NUM_BLAKE3_COLS + c) % NUM_BLAKE3_COLS = c by
      rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hc]]

theorem getc_of_le (r : Blake3Cols F) {c : ℕ} (hc : NUM_BLAKE3_COLS ≤ c) : getc r c = 0 := by
  rw [getc, List.getD_eq_default _ _ (by rw [length_cells]; exact hc)]

/-- The row the row builder reads is the row's cells. -/
theorem cur_matOf [Inhabited F] [DecidableEq F] {i : ℕ} (hi : i < rows.length) :
    cur (instOf blake3Air (matOf rows) []) i = getc (rows.getD i Blake3Cols.zero) := by
  funext c
  simp only [cur, rowOf, rowEnv, instOf, AirLayout.from_air, blake3Air]
  by_cases hc : c < NUM_BLAKE3_COLS
  · rw [getD_map_range_of _ rfl hc, matOf_cell rows hi hc]
  · rw [getc_of_le _ (Nat.le_of_not_lt hc), List.getD_eq_default _ _ (by simp; omega)]

end mat

/-- The generator's rows: row k compresses input k under counter k and block length n. -/
def genRows (inputs : List (ℕ → Word)) : List (Blake3Cols F) :=
  inputs.zipIdx.map fun (input, counter) => generate_trace_rows_for_perm input counter inputs.length

theorem generate_eq (inputs : List (ℕ → Word)) (e : ℕ) :
    generate_trace_rows (F := F) inputs e =
      if inputs.length ≠ 0 ∧ inputs.length &&& (inputs.length - 1) = 0 then some (matOf (genRows inputs))
      else none := rfl

/-- Completeness: whenever the generator returns a trace, it satisfies the AIR, in every field. -/
theorem complete [Inhabited F] [DecidableEq F] (inputs : List (ℕ → Word)) (e : ℕ) {M : Mat F}
    (hM : generate_trace_rows (F := F) inputs e = some M) :
    Satisfies (constraints blake3Air) (instOf blake3Air M []) := by
  rw [generate_eq] at hM
  split_ifs at hM
  obtain rfl := Option.some.inj hM
  rw [satisfies_iff_rows]
  change ∀ i < (matOf (genRows inputs)).height, _
  rw [matOf_height]
  intro i hi
  apply (eval_iff _ _).mpr
  change RowSpec (cur (instOf blake3Air (matOf (genRows inputs)) []) i)
  rw [cur_matOf _ hi]
  have hl : i < inputs.length := by simpa [genRows] using hi
  have : (genRows (F := F) inputs).getD i Blake3Cols.zero =
      generate_trace_rows_for_perm (inputs.getD i fun _ => 0) i inputs.length := by
    simp [genRows, List.getD_eq_getElem?_getD, hl]
  rw [this]
  exact gen_rowSpec _ _ _

/-- The debug checker accepts the generator's trace. -/
theorem check_complete [Inhabited F] [DecidableEq F] (inputs : List (ℕ → Word)) (e : ℕ) {M : Mat F}
    (hM : generate_trace_rows (F := F) inputs e = some M) :
    check_constraints blake3Air M [] = .ok () := by
  have hw : M.width = NUM_BLAKE3_COLS := by
    rw [generate_eq] at hM; split_ifs at hM; obtain rfl := Option.some.inj hM; rfl
  have hs : Shapes blake3Air M [] := ⟨hw, by simp [blake3Air], fun _ => rfl, rfl, rfl⟩
  rw [check_constraints_ok_iff hs]
  refine ⟨by simp [PrepHeight, blake3Air], by simp [PeriodicShapes, blake3Air], ?_, complete inputs e hM⟩
  simp [boundary_io_mismatches, validate, blake3Air]
  rfl

end Plonky3Lean.Proofs.Blake3Air

namespace Plonky3Lean.Proofs.Blake3Air

open p3_air.builder.mirror p3_air.air.mirror p3_blake3_air.mirror Plonky3Lean.Spec.Air
open Plonky3Lean.Proofs.Air Plonky3Lean.Proofs.KeccakAir

variable {F : Type} [Field F] [DecidableEq F]

theorem decodeWord_u32 (w : Word) : decodeWord (u32_to_bits_le w : ℕ → F) = w :=
  BitsRep.unique (bitsRep_decode fun _ hk => bool_of_bitsRep (bitsRep_u32 w) hk) (bitsRep_u32 w)

/-- The generator succeeds on any list of 2^k inputs. -/
theorem generate_some (inputs : List (ℕ → Word)) (e : ℕ) {k : ℕ} (hk : inputs.length = 2 ^ k) :
    generate_trace_rows (F := F) inputs e = some (matOf (genRows inputs)) := by
  rw [generate_eq, hk, Nat.and_two_pow_sub_one_eq_mod, Nat.mod_self]
  simp

open Plonky3Lean.Spec.Blake3 in
theorem compress_counter (cv blk : List (BitVec 32)) {c c' : ℕ} (bl fl : BitVec 32)
    (h1 : BitVec.ofNat 32 c = BitVec.ofNat 32 c') (h2 : BitVec.ofNat 32 (c / 2 ^ 32) = BitVec.ofNat 32 (c' / 2 ^ 32)) :
    compress cv blk c bl fl = compress cv blk c' bl fl := by
  simp only [compress, h1, h2]

/-- The generator's row k compresses input k with counter k, block length the number of rows, and no flags. -/
theorem generated_outputs (hp : 3 * 2 ^ 16 < ringChar F) [Inhabited F] (inputs : List (ℕ → Word)) (e : ℕ)
    {M : Mat F} (hM : generate_trace_rows (F := F) inputs e = some M) {k : ℕ} (hk : k < inputs.length) :
    ∀ q < 4, ∀ j < 4, BitsRep (fun b => (instOf blake3Air M []).main k (col.outputs q j b))
      ((Plonky3Lean.Spec.Blake3.compress ((List.range 8).map fun i => (inputs.getD k fun _ => 0) (16 + i))
        ((List.range 16).map (inputs.getD k fun _ => 0)) k (BitVec.ofNat 32 inputs.length) 0).getD
        (4 * q + j) 0) := by
  have hT := complete inputs e hM
  have hM' := hM
  rw [generate_eq] at hM'
  split_ifs at hM'
  obtain rfl := Option.some.inj hM'
  have hkh : k < (instOf blake3Air (matOf (genRows (F := F) inputs)) []).height := by
    simp only [instOf, matOf_height]; simpa [genRows] using hk
  obtain ⟨-, -, -, hout⟩ := trace_sound hp hT hkh
  set input := inputs.getD k fun _ => 0
  have hrowk : (genRows (F := F) inputs).getD k Blake3Cols.zero =
      generate_trace_rows_for_perm input k inputs.length := by
    simp [genRows, List.getD_eq_getElem?_getD, hk, input]
  have hlen : k < (genRows (F := F) inputs).length := by simpa [genRows] using hk
  have hcell : ∀ c < NUM_BLAKE3_COLS, (instOf blake3Air (matOf (genRows (F := F) inputs)) []).main k c =
      getc (generate_trace_rows_for_perm (F := F) input k inputs.length) c := fun c hc => by
    simp only [instOf]; rw [matOf_cell _ hlen hc, hrowk]
  have hrow := gen_row_eq (F := F) input k inputs.length
  have hblk : blockOf ((instOf blake3Air (matOf (genRows (F := F) inputs)) []).main k) =
      (List.range 16).map input := List.map_congr_left fun i hi => by
    rw [List.mem_range] at hi
    rw [← decodeWord_u32 (F := F) (input i)]
    exact decodeWord_congr fun b hb => by
      rw [hcell _ (by simp only [col.inputs, NUM_BLAKE3_COLS]; omega), cell_inputs _ hi hb, hrow]
  have hcv : cvOf ((instOf blake3Air (matOf (genRows (F := F) inputs)) []).main k) =
      (List.range 8).map fun i => input (16 + i) := List.map_congr_left fun i hi => by
    rw [List.mem_range] at hi
    rw [← decodeWord_u32 (F := F) (input (16 + i))]
    exact decodeWord_congr fun b hb => by
      rw [hcell _ (by simp only [col.chaining_values, NUM_BLAKE3_COLS]; omega),
        cell_cv _ (by omega) (by omega) hb, hrow]
      simp only
      congr 2; omega
  have h3 : ∀ j < 4, row3Of ((instOf blake3Air (matOf (genRows (F := F) inputs)) []).main k) j =
      [BitVec.ofNat 32 k, BitVec.ofNat 32 (k / 2 ^ 32), BitVec.ofNat 32 inputs.length, 0].getD j 0 := by
    intro j hj
    rw [← decodeWord_u32 (F := F) ([BitVec.ofNat 32 k, BitVec.ofNat 32 (k / 2 ^ 32),
      BitVec.ofNat 32 inputs.length, 0].getD j 0)]
    refine decodeWord_congr fun b hb => ?_
    simp only [initial_row_3]
    rw [hcell _ (by simp only [col.counter_low, NUM_BLAKE3_COLS]; omega)]
    interval_cases j
    · rw [Nat.mul_zero, Nat.zero_add, cell_counter_low _ hb, hrow]; rfl
    · rw [show 32 * 1 + b = 32 + b by omega, cell_counter_hi _ hb, hrow]; rfl
    · rw [show 32 * 2 + b = 64 + b by omega, cell_block_len _ hb, hrow]; rfl
    · rw [show 32 * 3 + b = 96 + b by omega, cell_flags _ hb, hrow]
      simp [u32_to_bits_le]
  intro q hq j hj
  have := hout q hq j hj
  rw [hblk, hcv, h3 0 (by norm_num), h3 1 (by norm_num), h3 2 (by norm_num), h3 3 (by norm_num)] at this
  simp only [List.getD_cons_zero, List.getD_cons_succ] at this
  rwa [compress_counter _ _ _ _ (c' := k) (counter_words _ _).1 (counter_words _ _).2] at this

end Plonky3Lean.Proofs.Blake3Air
