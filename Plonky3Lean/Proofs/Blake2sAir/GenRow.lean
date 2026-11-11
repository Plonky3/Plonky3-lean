module

public import Plonky3Lean.Proofs.Blake2sAir.Step
public import Plonky3Lean.Proofs.Blake2sAir.Cells

@[expose] public section

/-!
# The generated row

The generator runs the RFC 7693 rounds on a working state of words.

Each G step writes the carries of its two stored additions and the words `d_1`, `b_1`, `d_2`, `b_2`.

So the row it fills holds, at step `g` of round `r`, the witness of G on the working vector before that step.
-/

set_option linter.unusedSectionVars false

namespace Plonky3Lean.Proofs.Blake2sAir

open p3_blake2s_air.mirror
open Plonky3Lean.Spec.Blake2s (G init rounds)

variable {F : Type} [Field F]

/-- The generator's state holds a working vector, row by row. -/
def GS (st : ℕ → ℕ → Word) (v : List Word) : Prop :=
  v.length = 16 ∧ ∀ r < 4, ∀ i < 4, st r i = v.getD (4 * r + i) 0

/-- The witness words of G on a working vector, at the given positions, with two message words. -/
def gwOf (v : List Word) (slots : List ℕ) (X Y : Word) : GWords :=
  let A := v.getD (slots.getD 0 0) 0
  let B := v.getD (4 + slots.getD 1 0) 0
  let C := v.getD (8 + slots.getD 2 0) 0
  let D := v.getD (12 + slots.getD 3 0) 0
  let a1 := A + B + X
  let d1 := (D ^^^ a1).rotateRight 16
  let c1 := C + d1
  let b1 := (B ^^^ c1).rotateRight 12
  let a2 := a1 + b1 + Y
  let d2 := (d1 ^^^ a2).rotateRight 8
  let c2 := c1 + d2
  ⟨carries_word A B (A + B), d1, b1, carries_word a1 b1 (a1 + b1), d2, (b1 ^^^ c2).rotateRight 7⟩

/-- The cells of a step's witness words. -/
def witOf (w : GWords) : Blake2sBinaryGCols F :=
  ⟨word_to_bits_le w.add1_carries, u32_to_bits_le w.d1, u32_to_bits_le w.b1,
    word_to_bits_le w.add2_carries, u32_to_bits_le w.d2, u32_to_bits_le w.b2⟩

/-- The state the G step on words leaves: the four words of `gWords`, at the four positions. -/
theorem g_words_state (st : ℕ → ℕ → Word) (slots : List ℕ) (X Y : Word) :
    (g_words st slots X Y).2 = fun r i =>
      let w := gWords (st 0 (slots.getD 0 0)) (st 1 (slots.getD 1 0)) (st 2 (slots.getD 2 0))
        (st 3 (slots.getD 3 0)) X Y
      if r = 0 ∧ i = slots.getD 0 0 then w.1
      else if r = 1 ∧ i = slots.getD 1 0 then w.2.1
      else if r = 2 ∧ i = slots.getD 2 0 then w.2.2.1
      else if r = 3 ∧ i = slots.getD 3 0 then w.2.2.2
      else st r i := by
  funext r i
  simp only [g_words, Function.update_apply]
  split_ifs <;> try first | rfl | (exfalso; omega)
  all_goals first
    | (obtain ⟨rfl, rfl⟩ := ‹_ ∧ _›; rw [Function.update_self]; rfl)
    | (subst_vars; rw [Function.update_of_ne (fun h => by simp_all)])

/-- The G step on words computes the witness words of G, and moves the state as G moves the vector. -/
theorem g_words_spec {st : ℕ → ℕ → Word} {v : List Word} (hs : GS st v) {slots : List ℕ}
    (hsl : ∀ j < 4, slots.getD j 0 < 4) (X Y : Word) :
    (g_words st slots X Y).1 = gwOf v slots X Y ∧
      GS (g_words st slots X Y).2
        (G v (slots.getD 0 0) (4 + slots.getD 1 0) (8 + slots.getD 2 0) (12 + slots.getD 3 0) X Y) := by
  obtain ⟨hlen, hst⟩ := hs
  have ha0 := hsl 0 (by norm_num)
  have hb0 := hsl 1 (by norm_num)
  have hc0 := hsl 2 (by norm_num)
  have hd0 := hsl 3 (by norm_num)
  have ea : st 0 (slots.getD 0 0) = v.getD (slots.getD 0 0) 0 := by
    simpa using hst 0 (by norm_num) _ ha0
  have eb : st 1 (slots.getD 1 0) = v.getD (4 + slots.getD 1 0) 0 := hst 1 (by norm_num) _ hb0
  have ec : st 2 (slots.getD 2 0) = v.getD (8 + slots.getD 2 0) 0 := hst 2 (by norm_num) _ hc0
  have ed : st 3 (slots.getD 3 0) = v.getD (12 + slots.getD 3 0) 0 := hst 3 (by norm_num) _ hd0
  refine ⟨by simp only [g_words, gwOf, ea, eb, ec, ed], by rw [length_G, hlen], fun r hr i hi => ?_⟩
  rw [g_words_state, G_getD hlen ha0 hb0 hc0 hd0]
  dsimp only
  rw [ea, eb, ec, ed]
  generalize gWords (v.getD (slots.getD 0 0) 0) (v.getD (4 + slots.getD 1 0) 0)
    (v.getD (8 + slots.getD 2 0) 0) (v.getD (12 + slots.getD 3 0) 0) X Y = w
  generalize slots.getD 0 0 = ia at *
  generalize slots.getD 1 0 = ib at *
  generalize slots.getD 2 0 = ic at *
  generalize slots.getD 3 0 = id at *
  interval_cases r
  all_goals split_ifs <;> first | rfl | (exfalso; omega) | exact (‹False ∧ _›).1.elim |
    exact hst _ (by norm_num) _ hi

/-! ## The generator's loops -/

theorem generate_g_eq (st : ℕ → ℕ → Word) (slots : List ℕ) (X Y : Word) :
    generate_g (F := F) st slots X Y = (witOf (g_words st slots X Y).1, (g_words st slots X Y).2) := rfl

/-- One step of the generator's inner loop, as the transcription writes it. -/
def genStep (m : List Word) (r : ℕ) (acc : Blake2sBinaryCols F × (ℕ → ℕ → Word)) (g : ℕ) :
    Blake2sBinaryCols F × (ℕ → ℕ → Word) :=
  let schedule := SIGMA.getD r []
  let (cols, state) := generate_g acc.2 (G_SCHEDULE.getD g []) (m.getD (schedule.getD (2 * g) 0) 0)
    (m.getD (schedule.getD (2 * g + 1) 0) 0)
  ({ acc.1 with rounds := Function.update acc.1.rounds r (Function.update (acc.1.rounds r) g cols) },
    state)

/-- The witness the generator writes at step `g` of round `r`, from the vector before round `r`. -/
def witAt (m v : List Word) (r g : ℕ) : Blake2sBinaryGCols F :=
  witOf (gwOf ((List.range g).foldl (gStep m r) v) (G_SCHEDULE.getD g [])
    (m.getD ((SIGMA.getD r []).getD (2 * g) 0) 0) (m.getD ((SIGMA.getD r []).getD (2 * g + 1) 0) 0))

/-- The input fields of two rows agree. -/
def SameInputs (a b : Blake2sBinaryCols F) : Prop :=
  a.chaining_value = b.chaining_value ∧ a.block = b.block ∧ a.counter_low = b.counter_low ∧
    a.counter_high = b.counter_high ∧ a.last_block = b.last_block

omit [Field F] in
theorem sameInputs_refl [Field F] (a : Blake2sBinaryCols F) : SameInputs a a := ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- The inner loop over the eight steps of round `r` writes their witnesses, and moves the state as G does. -/
theorem inner_fold (m : List Word) (r : ℕ) (v : List Word) :
    ∀ n ≤ 8, ∀ acc : Blake2sBinaryCols F × (ℕ → ℕ → Word), GS acc.2 v →
      GS ((List.range n).foldl (genStep m r) acc).2 ((List.range n).foldl (gStep m r) v) ∧
      (∀ g < n, ((List.range n).foldl (genStep m r) acc).1.rounds r g = witAt m v r g) ∧
      (∀ r', r' ≠ r → ((List.range n).foldl (genStep m r) acc).1.rounds r' = acc.1.rounds r') ∧
      SameInputs ((List.range n).foldl (genStep m r) acc).1 acc.1 := by
  intro n
  induction n with
  | zero => intro _ acc hs; exact ⟨hs, fun _ h => absurd h (Nat.not_lt_zero _), fun _ _ => rfl,
      sameInputs_refl _⟩
  | succ n ih =>
    intro hn acc hs
    obtain ⟨hgs, hw, hr, hi⟩ := ih (by omega) acc hs
    simp only [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    generalize (List.range n).foldl (genStep m r) acc = res at hgs hw hr hi
    obtain ⟨row, st⟩ := res
    have hsl : ∀ j < 4, (G_SCHEDULE.getD n []).getD j 0 < 4 := fun j hj => g_schedule_lt n hj
    obtain ⟨e1, e2⟩ := g_words_spec hgs hsl (m.getD ((SIGMA.getD r []).getD (2 * n) 0) 0)
      (m.getD ((SIGMA.getD r []).getD (2 * n + 1) 0) 0)
    simp only [genStep, generate_g_eq]
    refine ⟨e2, fun g hg => ?_, fun r' hr' => ?_, hi⟩
    · by_cases e : g = n
      · subst e; simp only [Function.update_self, e1]; rfl
      · rw [Function.update_self, Function.update_of_ne e]; exact hw g (by omega)
    · rw [Function.update_of_ne hr']; exact hr r' hr'

/-- One round of the generator's outer loop. -/
def genRound (m : List Word) (acc : Blake2sBinaryCols F × (ℕ → ℕ → Word)) (r : ℕ) :
    Blake2sBinaryCols F × (ℕ → ℕ → Word) :=
  (List.range G_PER_ROUND).foldl (genStep m r) acc

theorem rounds_succ (m v : List Word) {n : ℕ} (hn : n < 10) :
    rounds m v (n + 1) = (List.range 8).foldl (gStep m n) (rounds m v n) := by
  rw [rounds, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, ← rounds,
    round_eq _ _ hn]

/-- The outer loop over the ten rounds writes every step's witness, and moves the state as the rounds do. -/
theorem outer_fold (m v : List Word) :
    ∀ n ≤ 10, ∀ acc : Blake2sBinaryCols F × (ℕ → ℕ → Word), GS acc.2 v →
      GS ((List.range n).foldl (genRound m) acc).2 (rounds m v n) ∧
      (∀ r < n, ∀ g < 8, ((List.range n).foldl (genRound m) acc).1.rounds r g =
        witAt m (rounds m v r) r g) ∧
      SameInputs ((List.range n).foldl (genRound m) acc).1 acc.1 := by
  intro n
  induction n with
  | zero => intro _ acc hs; exact ⟨hs, fun _ h => absurd h (Nat.not_lt_zero _), sameInputs_refl _⟩
  | succ n ih =>
    intro hn acc hs
    obtain ⟨hgs, hw, hi⟩ := ih (by omega) acc hs
    simp only [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    generalize (List.range n).foldl (genRound m) acc = res at hgs hw hi
    obtain ⟨e1, e2, e3, e4⟩ := inner_fold m n (rounds m v n) 8 le_rfl res hgs
    refine ⟨by rw [rounds_succ _ _ (by omega)]; exact e1, fun r hr g hg => ?_, ?_⟩
    · by_cases e : r = n
      · subst e; exact e2 g hg
      · rw [genRound, show G_PER_ROUND = 8 from rfl, e3 r e]; exact hw r (by omega) g hg
    · obtain ⟨a1, a2, a3, a4, a5⟩ := e4
      obtain ⟨b1, b2, b3, b4, b5⟩ := hi
      exact ⟨a1.trans b1, a2.trans b2, a3.trans b3, a4.trans b4, a5.trans b5⟩

/-! ## The generated row -/

section input

variable (input : Blake2sCompressionInput)

/-- The row with the input cells written. -/
def inputRow : Blake2sBinaryCols F :=
  { (Blake2sBinaryCols.zero : Blake2sBinaryCols F) with
    chaining_value := fun i => u32_to_bits_le (input.chaining_value.getD i 0)
    block := fun i => u32_to_bits_le (input.block.getD i 0)
    counter_low := u32_to_bits_le (input.counter.setWidth 32)
    counter_high := u32_to_bits_le ((input.counter >>> 32).setWidth 32)
    last_block := if input.last_block then 1 else 0 }

/-- The generator's initial state. -/
def state0 : ℕ → ℕ → Word := fun r i =>
  if r = 0 then input.chaining_value.getD i 0
  else if r = 1 then input.chaining_value.getD (4 + i) 0
  else if r = 2 then IV.getD i 0
  else if r = 3 then IV.getD (4 + i) 0 ^^^
    [input.counter.setWidth 32, (input.counter >>> 32).setWidth 32, input.flag_word].getD i 0
  else 0

/-- The chaining value of the input, as eight words. -/
def cvIn : List Word := (List.range 8).map fun i => input.chaining_value.getD i 0

/-- The working vector before the rounds, by RFC 7693. -/
def v0 : List Word := init (cvIn input) input.counter.toNat input.last_block

theorem gen_eq :
    generate_trace_row (Blake2sBinaryCols.zero : Blake2sBinaryCols F) input =
      ((List.range NUM_ROUNDS).foldl (genRound input.block) (inputRow input, state0 input)).1 := rfl

end input

theorem ofNat_div_counter (c : BitVec 64) :
    BitVec.ofNat 32 (c.toNat / 2 ^ 32) = (c >>> 32).setWidth 32 := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

theorem cvIn_getD (input : Blake2sCompressionInput) {j : ℕ} (hj : j < 8) :
    (cvIn input).getD j 0 = input.chaining_value.getD j 0 := by
  simp [cvIn, List.getD_eq_getElem?_getD, hj]

theorem gs_state0 (input : Blake2sCompressionInput) : GS (state0 input) (v0 input) := by
  have hlen : (cvIn input).length = 8 := by simp [cvIn]
  refine ⟨by simp only [v0, init]; split <;> simp [hlen, Plonky3Lean.Spec.Blake2s.IV],
    fun r hr i hi => ?_⟩
  rw [v0, init_getD hlen]
  interval_cases r
  · rw [ite_f (by omega), ite_f (by omega), ite_f (by omega), List.getD_append _ _ _ _ (by omega),
      Nat.mul_zero, Nat.zero_add, cvIn_getD _ (by omega)]
    rfl
  · rw [ite_f (by omega), ite_f (by omega), ite_f (by omega), List.getD_append _ _ _ _ (by omega),
      Nat.mul_one, cvIn_getD _ (by omega)]
    rfl
  · rw [ite_f (by omega), ite_f (by omega), ite_f (by omega),
      List.getD_append_right _ _ _ _ (by omega), hlen, IV_eq.symm]
    simp [state0]
  · interval_cases i
    · simp [state0, IV_eq, BitVec.ofNat_toNat]
    · simp only [state0, IV_eq, ofNat_div_counter]
      rfl
    · cases h : input.last_block
      · simp [state0, IV_eq, Blake2sCompressionInput.flag_word, h]
      · simp [state0, IV_eq, Blake2sCompressionInput.flag_word, h]
        rw [show (4294967295#32 : Word) = BitVec.allOnes 32 by decide, BitVec.xor_allOnes]
    · rw [ite_f (by omega), ite_f (by omega), ite_f (by omega),
        List.getD_append_right _ _ _ _ (by omega), hlen, IV_eq.symm]
      simp [state0]

/-- What the generator writes into a row, field by field. -/
theorem gen_spec (input : Blake2sCompressionInput) :
    SameInputs (generate_trace_row (Blake2sBinaryCols.zero : Blake2sBinaryCols F) input)
      (inputRow input) ∧
    ∀ r < 10, ∀ g < 8, (generate_trace_row (Blake2sBinaryCols.zero : Blake2sBinaryCols F) input).rounds r g =
      witAt input.block (rounds input.block (v0 input) r) r g := by
  obtain ⟨-, hw, hi⟩ := outer_fold (F := F) input.block (v0 input) 10 le_rfl (inputRow input, state0 input)
    (gs_state0 input)
  rw [gen_eq]
  exact ⟨hi, hw⟩

end Plonky3Lean.Proofs.Blake2sAir
