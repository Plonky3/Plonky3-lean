module

public import Plonky3Lean.Proofs.Blake3Air.Binary.Trace

@[expose] public section

/-!
# The characteristic-2 generator's words

The generator runs the G steps in schedule order on a state of four rows of four words.

Read as a 16-word state, its G step is the quarter round of the specification.

Its witness words are those of the two half quarter rounds.

Its carries are those of the two three-operand additions.
-/

set_option linter.unusedSectionVars false

namespace Plonky3Lean.Proofs.Blake3Air.Binary

open p3_air.builder.mirror p3_air.air.mirror p3_blake3_air.mirror p3_blake3_air.mirror.binary
open Plonky3Lean.Proofs.KeccakAir Plonky3Lean.Proofs.Blake3Air

/-- G step (r, g) of the generator, on a state, with the message words of a block. -/
def wstep (blk : ℕ → Word) (st : binary.WState) (rg : ℕ × ℕ) : GWords × binary.WState :=
  g_words st (slot rg.2 0) (slot rg.2 1) (slot rg.2 2) (slot rg.2 3) ((permute^[rg.1] blk) (2 * rg.2))
    ((permute^[rg.1] blk) (2 * rg.2 + 1))

/-- The generator's state after a list of G steps. -/
def wfold (blk : ℕ → Word) (l : List (ℕ × ℕ)) (st : binary.WState) : binary.WState :=
  l.foldl (fun st rg => (wstep blk st rg).2) st

/-- The G steps before step g of round r. -/
def pre (r g : ℕ) : List (ℕ × ℕ) :=
  ((List.range r).flatMap fun r => (List.range 8).map fun g => (r, g)) ++ (List.range g).map fun g => (r, g)

/-- A generator state read as a 16-word state. -/
def flat (st : binary.WState) : ℕ → Word := fun p => st (p / 4) (p % 4)

variable {F : Type} [Field F]

theorem gen_inner (blk : ℕ → Word) (r : ℕ) (row0 : ℕ → Blake3BinaryGCols F) (S : binary.WState) (n : ℕ) :
    (List.range n).foldl
      (fun (acc : (ℕ → Blake3BinaryGCols F) × binary.WState) g =>
        let (row, state) := acc
        let (words, state) :=
          g_words state (slot g 0) (slot g 1) (slot g 2) (slot g 3) ((permute^[r] blk) (2 * g))
            ((permute^[r] blk) (2 * g + 1))
        (Function.update row g (generate_g words), state)) (row0, S) =
      (fun g => if g < n then generate_g (wstep blk (wfold blk ((List.range g).map fun g => (r, g)) S) (r, g)).1
        else row0 g, wfold blk ((List.range n).map fun g => (r, g)) S) := by
  induction n with
  | zero => simp [wfold]
  | succ n ih =>
    rw [List.range_succ, List.foldl_append, ih]
    simp only [List.foldl_cons, List.foldl_nil]
    refine Prod.ext ?_ ?_
    · funext g
      simp only [Function.update_apply]
      by_cases h : g = n
      · subst h; simp [wstep]
      · by_cases h' : g < n
        · simp [h, h', show g < n + 1 by omega]
        · simp [h, h', show ¬ g < n + 1 by omega]
    · simp [wfold, wstep, List.foldl_append]

end Plonky3Lean.Proofs.Blake3Air.Binary

namespace Plonky3Lean.Proofs.Blake3Air.Binary

open p3_air.builder.mirror p3_air.air.mirror p3_blake3_air.mirror p3_blake3_air.mirror.binary
open Plonky3Lean.Proofs.KeccakAir Plonky3Lean.Proofs.Blake3Air

variable {F : Type} [Field F]

theorem wfold_append (blk : ℕ → Word) (l₁ l₂ : List (ℕ × ℕ)) (st : binary.WState) :
    wfold blk (l₁ ++ l₂) st = wfold blk l₂ (wfold blk l₁ st) := List.foldl_append

theorem gen_outer (blk : ℕ → Word) (rounds0 : ℕ → ℕ → Blake3BinaryGCols F) (S0 : binary.WState) (n : ℕ) :
    (List.range n).foldl
      (fun (acc : (ℕ → ℕ → Blake3BinaryGCols F) × binary.WState × (ℕ → Word)) round_idx =>
        let (rounds, state, m) := acc
        let m := if round_idx > 0 then permute m else m
        let (row, state) := (List.range G_PER_ROUND).foldl
          (fun (acc : (ℕ → Blake3BinaryGCols F) × binary.WState) g =>
            let (row, state) := acc
            let (words, state) :=
              g_words state (slot g 0) (slot g 1) (slot g 2) (slot g 3) (m (2 * g)) (m (2 * g + 1))
            (Function.update row g (generate_g words), state)) (rounds round_idx, state)
        (Function.update rounds round_idx row, state, m)) (rounds0, S0, blk) =
      (fun r => if r < n then (fun g => if g < 8 then generate_g (wstep blk (wfold blk (pre r g) S0) (r, g)).1
          else rounds0 r g) else rounds0 r,
        wfold blk ((List.range n).flatMap fun r => (List.range 8).map fun g => (r, g)) S0,
        if n = 0 then blk else permute^[n - 1] blk) := by
  induction n with
  | zero => simp [wfold]
  | succ n ih =>
    rw [List.range_succ, List.foldl_append, ih]
    simp only [List.foldl_cons, List.foldl_nil, Nat.add_one_ne_zero, ite_false, Nat.add_sub_cancel]
    have hm : (if n > 0 then permute (if n = 0 then blk else permute^[n - 1] blk)
        else (if n = 0 then blk else permute^[n - 1] blk)) = permute^[n] blk := by
      rcases n with _ | n
      · rfl
      · simp [← Function.iterate_succ_apply' permute]
    rw [hm, show G_PER_ROUND = 8 from rfl, gen_inner]
    refine Prod.ext ?_ (Prod.ext ?_ rfl)
    · funext r
      simp only [Function.update_apply]
      by_cases h : r = n
      · subst h
        funext g
        simp only [ite_true, show r < r + 1 by omega]
        split_ifs <;> first | omega | simp [pre, wfold_append]
      · by_cases h' : r < n
        · simp [h, h', show r < n + 1 by omega]
        · simp [h, h', show ¬ r < n + 1 by omega]
    · simp [List.range_succ, List.flatMap_append, wfold_append]

end Plonky3Lean.Proofs.Blake3Air.Binary

namespace Plonky3Lean.Proofs.Blake3Air.Binary

open p3_air.builder.mirror p3_air.air.mirror p3_blake3_air.mirror p3_blake3_air.mirror.binary
open Plonky3Lean.Proofs.KeccakAir Plonky3Lean.Proofs.Blake3Air

variable {F : Type} [Field F]

/-- The generator's initial state of a compression input. -/
def initW (input : Blake3CompressionInput) : binary.WState := fun r i =>
  if r = 0 then input.chaining_value i
  else if r = 1 then input.chaining_value (4 + i)
  else if r = 2 then iv_word i
  else if i = 0 then input.counter.setWidth 32
  else if i = 1 then (input.counter >>> 32).setWidth 32
  else if i = 2 then input.block_len
  else input.flags

/-- The generated row, field by field. -/
theorem gen_row_eq (input : Blake3CompressionInput) :
    generate_trace_row (F := F) input =
      { chaining_value := fun i => u32_to_bits_le (input.chaining_value i)
        block := fun i => u32_to_bits_le (input.block i)
        counter_low := u32_to_bits_le (input.counter.setWidth 32)
        counter_high := u32_to_bits_le ((input.counter >>> 32).setWidth 32)
        block_len := u32_to_bits_le input.block_len
        flags := u32_to_bits_le input.flags
        rounds := fun r => if r < 7 then (fun g => if g < 8 then
            generate_g (wstep input.block (wfold input.block (pre r g) (initW input)) (r, g)).1
          else ⟨fun _ => 0, fun _ => 0, fun _ => 0, fun _ => 0, fun _ => 0, fun _ => 0⟩)
          else fun _ => ⟨fun _ => 0, fun _ => 0, fun _ => 0, fun _ => 0, fun _ => 0, fun _ => 0⟩ } := by
  unfold generate_trace_row
  simp only [show NUM_ROUNDS = 7 from rfl, gen_outer]
  rfl

end Plonky3Lean.Proofs.Blake3Air.Binary

namespace Plonky3Lean.Proofs.Blake3Air.Binary

open p3_air.builder.mirror p3_air.air.mirror p3_blake3_air.mirror p3_blake3_air.mirror.binary
open Plonky3Lean.Proofs.KeccakAir Plonky3Lean.Proofs.Blake3Air

theorem flat_setWords (st : binary.WState) {ia ib ic id : ℕ} (ha : ia < 4) (hb : ib < 4) (hc : ic < 4)
    (hd : id < 4) (w : Word × Word × Word × Word) :
    flat (setWords st ia ib ic id w) = updF (flat st) ia (4 + ib) (8 + ic) (12 + id) w.1 w.2.1 w.2.2.1 w.2.2.2 := by
  funext p
  simp only [flat, setWords, updF, Function.update_apply]
  by_cases h12 : p = 12 + id
  · subst h12; simp [show (12 + id) / 4 = 3 by omega, show (12 + id) % 4 = id by omega]
  by_cases h8 : p = 8 + ic
  · subst h8; simp [h12, show (8 + ic) / 4 = 2 by omega, show (8 + ic) % 4 = ic by omega]
  by_cases h4 : p = 4 + ib
  · subst h4; simp [h12, h8, show (4 + ib) / 4 = 1 by omega, show (4 + ib) % 4 = ib by omega]
  by_cases h0 : p = ia
  · subst h0; simp [h12, h8, h4, show p / 4 = 0 by omega, show p % 4 = p by omega]
  simp only [h12, h8, h4, h0, ite_false]
  rcases (show p / 4 = 0 ∨ p / 4 = 1 ∨ p / 4 = 2 ∨ p / 4 = 3 ∨ 4 ≤ p / 4 by omega) with
    e | e | e | e | e
  · rw [e]; simp [Function.update_of_ne (show p % 4 ≠ ia by omega)]
  · rw [e]; simp [Function.update_of_ne (show p % 4 ≠ ib by omega)]
  · rw [e]; simp [Function.update_of_ne (show p % 4 ≠ ic by omega)]
  · rw [e]; simp [Function.update_of_ne (show p % 4 ≠ id by omega)]
  · simp [show p / 4 ≠ 0 by omega, show p / 4 ≠ 1 by omega, show p / 4 ≠ 2 by omega,
      show p / 4 ≠ 3 by omega]

/-- Read as a 16-word state, a G step of the generator is the quarter round on that state. -/
theorem flat_wstep (blk : ℕ → Word) (st : binary.WState) (r g : ℕ) :
    flat (wstep blk st (r, g)).2 = gF (flat st) (slot g 0) (4 + slot g 1) (8 + slot g 2) (12 + slot g 3)
      ((permute^[r] blk) (2 * g)) ((permute^[r] blk) (2 * g + 1)) := by
  have h0 := slot_lt g 0; have h1 := slot_lt g 1; have h2 := slot_lt g 2; have h3 := slot_lt g 3
  rw [gF_eq_updF]
  simp only [wstep, g_words]
  rw [flat_setWords _ h0 h1 h2 h3]
  simp only [flat, show (4 + slot g 1) / 4 = 1 by omega, show (4 + slot g 1) % 4 = slot g 1 by omega,
    show (8 + slot g 2) / 4 = 2 by omega, show (8 + slot g 2) % 4 = slot g 2 by omega,
    show (12 + slot g 3) / 4 = 3 by omega, show (12 + slot g 3) % 4 = slot g 3 by omega,
    show slot g 0 / 4 = 0 by omega, show slot g 0 % 4 = slot g 0 by omega, verifiable_half_round]
  rfl

end Plonky3Lean.Proofs.Blake3Air.Binary

namespace Plonky3Lean.Proofs.Blake3Air.Binary

open p3_air.builder.mirror p3_air.air.mirror p3_blake3_air.mirror p3_blake3_air.mirror.binary
open Plonky3Lean.Proofs.KeccakAir Plonky3Lean.Proofs.Blake3Air

/-- The witness words of a generator G step, with the carries of its two three-operand sums. -/
theorem wstep_words (blk : ℕ → Word) (st : binary.WState) (r g : ℕ) :
    let σ := flat st
    let rr := verifiable_half_round (σ (slot g 0)) (σ (4 + slot g 1)) (σ (8 + slot g 2)) (σ (12 + slot g 3))
      ((permute^[r] blk) (2 * g)) false
    let rr' := verifiable_half_round rr.1 rr.2.1 rr.2.2.1 rr.2.2.2 ((permute^[r] blk) (2 * g + 1)) true
    (wstep blk st (r, g)).1 = ⟨carries_word (σ (slot g 0)) (σ (4 + slot g 1)) (σ (slot g 0) + σ (4 + slot g 1)),
      rr.2.2.2, rr.2.1, carries_word rr.1 rr.2.1 (rr.1 + rr.2.1), rr'.2.2.2, rr'.2.1⟩ := by
  have h0 := slot_lt g 0; have h1 := slot_lt g 1; have h2 := slot_lt g 2; have h3 := slot_lt g 3
  simp only [wstep, g_words, flat, show (4 + slot g 1) / 4 = 1 by omega, show (4 + slot g 1) % 4 = slot g 1 by omega,
    show (8 + slot g 2) / 4 = 2 by omega, show (8 + slot g 2) % 4 = slot g 2 by omega,
    show (12 + slot g 3) / 4 = 3 by omega, show (12 + slot g 3) % 4 = slot g 3 by omega,
    show slot g 0 / 4 = 0 by omega, show slot g 0 % 4 = slot g 0 by omega, verifiable_half_round]
  rfl

variable {F : Type} [Field F]

/-- Bit i of the carry word of x + y is the carry into bit i + 1. -/
theorem carries_bits (x y : Word) {i : ℕ} (hi : i < 31) :
    (word_to_bits_le (carries_word x y (x + y)) i : F) = bitF (BitVec.carry (i + 1) x y false) := by
  simp only [word_to_bits_le, carries_word, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_xor, Nat.add_comm 1 i]
  rw [BitVec.getLsbD_add (show i + 1 < 32 by omega)]
  cases BitVec.carry (i + 1) x y false <;> cases x.getLsbD (i + 1) <;> cases y.getLsbD (i + 1) <;> simp [bitF]

end Plonky3Lean.Proofs.Blake3Air.Binary
