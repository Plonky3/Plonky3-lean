module

public import Plonky3Lean.Proofs.Blake2sAir.Sound

@[expose] public section

/-!
# The output read off a satisfying row is the compression

The Rust reads the compression output back from the witness of the last round.

On a row that meets its constraints in characteristic 2, with its input cells bits:

- every cell it reads is a bit, so the read-back never panics
- the state it reads after round 9 is the RFC 7693 working vector after ten rounds
- the output is the RFC 7693 compression of the row's chaining value, block, counter and flag.
-/

set_option linter.unusedSectionVars false

namespace Plonky3Lean.Proofs.Blake2sAir

open p3_air.builder.mirror p3_air.air.mirror p3_blake2s_air.mirror Plonky3Lean.Spec.Air
open Plonky3Lean.Proofs.KeccakAir (propBuilder fieldOps rowOf bitF)
open Plonky3Lean.Proofs.Sha256Air (Holds rotr_bit)
open Plonky3Lean.Proofs.Sha256Air.Binary (add_bitF)

variable {F : Type} [Field F]

/-! ## Reading words -/

theorem foldlM_some_of_mem {α β : Type} {f : α → β → Option α} (g : α → β → α) :
    ∀ (l : List β) (a : α), (∀ a, ∀ b ∈ l, f a b = some (g a b)) → l.foldlM f a = some (l.foldl g a)
  | [], _, _ => rfl
  | b :: l, a, h => by
    simp only [List.foldlM_cons, List.foldl_cons, h a b (by simp), Option.bind_eq_bind,
      Option.bind_some]
    exact foldlM_some_of_mem g l _ fun a b hb => h a b (by simp [hb])

/-- The bits below `n` of a word, set one at a time from bit 0. -/
theorem foldl_bits (W : Word) : ∀ n ≤ 32, ∀ k < 32,
    ((List.range n).foldl (fun (word : Word) i => word ||| (BitVec.ofBool (W.getLsbD i)).setWidth 32 <<< i)
      0).getLsbD k = (decide (k < n) && W.getLsbD k)
  | 0, _, k, _ => by simp
  | n + 1, hn, k, hk => by
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, BitVec.getLsbD_or,
      foldl_bits W n (by omega) k hk]
    simp only [BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth, BitVec.getLsbD_ofBool]
    by_cases e : k = n
    · subst e; simp [hk]
    · rcases Nat.lt_or_ge k n with h | h
      · simp [h, show k < n + 1 by omega]
      · simp [show ¬ k < n by omega, show ¬ k < n + 1 by omega, show k - n ≠ 0 by omega]

/-- Cells that hold a word read back as that word. -/
theorem read_word_eq [DecidableEq F] {bits : ℕ → F} {W : Word} (h : Holds bits W) :
    read_word bits = some W := by
  unfold read_word
  rw [foldlM_some_of_mem (fun (word : Word) i => word ||| (BitVec.ofBool (W.getLsbD i)).setWidth 32 <<< i)
    _ _ fun word i hi => ?_]
  · congr 1
    apply BitVec.eq_of_getLsbD_eq
    intro k hk
    rw [foldl_bits W 32 le_rfl k hk]
    simp [hk]
  · have hi : i < 32 := List.mem_range.mp hi
    rw [h i hi]
    cases W.getLsbD i <;> simp [bitF]

theorem foldlM_guard {α β : Type} (P : β → Prop) [DecidablePred P] (g : α → β → α) :
    ∀ (l : List β) (a : α), l.foldlM (fun a b => if P b then some (g a b) else none) a =
      if ∀ b ∈ l, P b then some (l.foldl g a) else none
  | [], _ => by simp
  | b :: l, a => by
    by_cases hb : P b
    · simp only [List.foldlM_cons, hb, ite_true, Option.bind_eq_bind, Option.bind_some,
        foldlM_guard P g l, List.foldl_cons, List.forall_mem_cons, true_and]
    · simp [hb]

/-- Reading a word panics exactly when one of its 32 cells is neither 0 nor 1. -/
theorem read_word_none [DecidableEq F] (bits : ℕ → F) :
    read_word bits = none ↔ ∃ b < 32, bits b ≠ 0 ∧ bits b ≠ 1 := by
  unfold read_word
  rw [foldlM_guard (fun i => bits i = 0 ∨ bits i = 1)
    (fun (word : Word) i => word ||| (BitVec.ofBool (bits i = 1)).setWidth 32 <<< i)]
  split_ifs with h
  · simp only [false_iff, not_exists, not_and]
    intro b hb h0 h1
    rcases h b (List.mem_range.mpr hb) with e | e <;> contradiction
  · simp only [List.mem_range, not_forall, not_or] at h
    obtain ⟨b, hb, h0, h1⟩ := h
    exact iff_of_true rfl ⟨b, hb, h0, h1⟩

/-- The read-back of the state panics when the round is not below ten. -/
theorem state_after_round_none [DecidableEq F] (r : Blake2sBinaryCols F) {round : ℕ} (h : 10 ≤ round) :
    state_after_round r round = none := by
  simp [state_after_round, NUM_ROUNDS, h]

/-! ## The state after the last round -/

/-- The words the last round's diagonal steps leave, row by row of the state. -/
theorem lastRound_eq (loc : ℕ → F) (st : State F) :
    (∀ j < 4, (TRound loc st 9).a j =
      xor_rotl_var fieldOps (gcolsOf loc 9 (4 + j)).d1 (gcolsOf loc 9 (4 + j)).d2 8) ∧
    (∀ j < 4, (TRound loc st 9).b j = (gcolsOf loc 9 (4 + (j + 3) % 4)).b2) ∧
    (∀ j < 4, (TRound loc st 9).c j =
      xor_rotl_var fieldOps (gcolsOf loc 9 (4 + (j + 2) % 4)).b1 (gcolsOf loc 9 (4 + (j + 2) % 4)).b2 7) ∧
    (∀ j < 4, (TRound loc st 9).d j = (gcolsOf loc 9 (4 + (j + 1) % 4)).d2) := by
  refine ⟨fun j hj => ?_, fun j hj => ?_, fun j hj => ?_, fun j hj => ?_⟩ <;>
  interval_cases j <;>
  simp [TRound, TStep, gNext, G_SCHEDULE, G_PER_ROUND, List.range_succ, Function.update]

/-- The list the read-back writes, from the words of the eight steps of a round. -/
def readback (D1 B1 D2 B2 : ℕ → Word) : List Word :=
  (List.range 8).foldl (fun v g =>
    let sl := G_SCHEDULE.getD g []
    (((v.set (sl.getD 0 0) (D1 g ^^^ (D2 g).rotateLeft 8)).set (4 + sl.getD 1 0) (B2 g)).set
      (8 + sl.getD 2 0) (B1 g ^^^ (B2 g).rotateLeft 7)).set (12 + sl.getD 3 0) (D2 g))
    (List.replicate 16 0)

/-- The diagonal steps write every word last. -/
theorem readback_getD (D1 B1 D2 B2 : ℕ → Word) :
    (∀ j < 4, (readback D1 B1 D2 B2).getD j 0 = D1 (4 + j) ^^^ (D2 (4 + j)).rotateLeft 8) ∧
    (∀ j < 4, (readback D1 B1 D2 B2).getD (4 + j) 0 = B2 (4 + (j + 3) % 4)) ∧
    (∀ j < 4, (readback D1 B1 D2 B2).getD (8 + j) 0 =
      B1 (4 + (j + 2) % 4) ^^^ (B2 (4 + (j + 2) % 4)).rotateLeft 7) ∧
    (∀ j < 4, (readback D1 B1 D2 B2).getD (12 + j) 0 = D2 (4 + (j + 1) % 4)) := by
  refine ⟨fun j hj => ?_, fun j hj => ?_, fun j hj => ?_, fun j hj => ?_⟩ <;>
  interval_cases j <;>
  simp [readback, G_SCHEDULE, List.range_succ, List.replicate_succ]

/-! ## The read-back of a satisfying row -/

theorem holds_wordOf_self [DecidableEq F] {x : ℕ → F} {W : Word} (h : Holds x W) :
    Holds x (Plonky3Lean.Proofs.Sha256Air.wordOf x) :=
  Plonky3Lean.Proofs.Sha256Air.holds_wordOf fun b hb => by
    rw [h b hb]; cases W.getLsbD b <;> simp [bitF]

theorem mapM_eq_some {α β : Type} {f : α → Option β} (g : α → β) :
    ∀ l : List α, (∀ a ∈ l, f a = some (g a)) → l.mapM f = some (l.map g)
  | [], _ => rfl
  | a :: l, h => by
    rw [List.mapM_cons, h a (by simp), mapM_eq_some g l fun b hb => h b (by simp [hb])]
    rfl

variable (h2 : (2 : F) = 0)
include h2

/-- The witness words of every step of the last round are words of bits. -/
theorem round9_bits [DecidableEq F] {cb : Bool} {env : Var → F} {L : AirLayout}
    (h : eval cb (propBuilder env L) True) (hb : cb = true ∨ BoolOk (rowOf env L 0)) :
    ∀ g < 8, (∃ W, Holds (gcolsOf (rowOf env L 0) 9 g).d1 W) ∧
      (∃ W, Holds (gcolsOf (rowOf env L 0) 9 g).b1 W) ∧
      (∃ W, Holds (gcolsOf (rowOf env L 0) 9 g).d2 W) ∧
      (∃ W, Holds (gcolsOf (rowOf env L 0) 9 g).b2 W) := by
  intro g hg
  obtain ⟨hbool, hchain⟩ := (eval_iff cb env L).mp h
  have hB : BoolOk (rowOf env L 0) := hb.elim hbool id
  have hm := msg_holds hB
  have hstep : ∀ (r g : ℕ) (st : State F) (v : List Word), CStep (rowOf env L 0) r st g →
      StateHolds st v → StateHolds (TStep (rowOf env L 0) r st g) (gStep (blockOf (rowOf env L 0)) r v g) :=
    fun r g st v hg hs =>
      step_sound h2 hs (fun j hj => g_schedule_lt g hj) (hm _ (sigma_lt _ _)) (hm _ (sigma_lt _ _)) hg
  obtain ⟨st, v, hs, hr⟩ := chain_each
    (U := fun v r => (List.range 8).foldl (gStep (blockOf (rowOf env L 0)) r) v) (I := StateHolds)
    (fun r st v hr hs => chain_inv (U := gStep (blockOf (rowOf env L 0)) r) (I := StateHolds)
      (hstep r) _ _ _ hr hs) _ _ _ hchain (init_sound h2 hB) 9 (by simp [NUM_ROUNDS])
  obtain ⟨st', v', hs', hc⟩ := chain_each (U := gStep (blockOf (rowOf env L 0)) 9) (I := StateHolds)
    (hstep 9) _ _ _ hr hs g (by simpa [G_PER_ROUND] using hg)
  exact step_bits h2 hs' (fun j hj => g_schedule_lt g hj) (hm _ (sigma_lt _ _)) (hm _ (sigma_lt _ _)) hc

/-- On a row that meets its constraints, with input bits, the output read back is the compression.

It reads the row's chaining value, block, counter and flag from its input cells.

It never panics. -/
theorem output_sound [DecidableEq F] {cb : Bool} {env : Var → F} {L : AirLayout}
    (h : eval cb (propBuilder env L) True) (hb : cb = true ∨ BoolOk (rowOf env L 0)) :
    compression_output (Blake2sBinaryCols.ofCells
        ((List.range L.main_width).map fun c => env (.main 0 c))) =
      some (Plonky3Lean.Spec.Blake2s.compress (cvOf (rowOf env L 0)) (blockOf (rowOf env L 0))
        (counterOf (rowOf env L 0)) (flagOf (rowOf env L 0))) := by
  have bits := round9_bits h2 h hb
  obtain ⟨hB, hS⟩ := row_sound h2 h hb
  set loc := rowOf env L 0 with hloc
  let D1 : ℕ → Word := fun g => Plonky3Lean.Proofs.Sha256Air.wordOf (gcolsOf loc 9 g).d1
  let B1 : ℕ → Word := fun g => Plonky3Lean.Proofs.Sha256Air.wordOf (gcolsOf loc 9 g).b1
  let D2 : ℕ → Word := fun g => Plonky3Lean.Proofs.Sha256Air.wordOf (gcolsOf loc 9 g).d2
  let B2 : ℕ → Word := fun g => Plonky3Lean.Proofs.Sha256Air.wordOf (gcolsOf loc 9 g).b2
  have hD1 : ∀ g < 8, Holds (gcolsOf loc 9 g).d1 (D1 g) := fun g hg =>
    holds_wordOf_self (bits g hg).1.choose_spec
  have hB1 : ∀ g < 8, Holds (gcolsOf loc 9 g).b1 (B1 g) := fun g hg =>
    holds_wordOf_self (bits g hg).2.1.choose_spec
  have hD2 : ∀ g < 8, Holds (gcolsOf loc 9 g).d2 (D2 g) := fun g hg =>
    holds_wordOf_self (bits g hg).2.2.1.choose_spec
  have hB2 : ∀ g < 8, Holds (gcolsOf loc 9 g).b2 (B2 g) := fun g hg =>
    holds_wordOf_self (bits g hg).2.2.2.choose_spec
  -- The read-back of the last round.
  have hsar : state_after_round (Blake2sBinaryCols.ofCells
      ((List.range L.main_width).map fun c => env (.main 0 c))) 9 = some (readback D1 B1 D2 B2) := by
    unfold state_after_round
    simp only [NUM_ROUNDS, show ¬ (10 ≤ 9) by omega, ite_false, Option.bind_eq_bind, Option.pure_def]
    exact foldlM_some_of_mem _ _ _ fun v g hg => by
      have hg' : g < 8 := List.mem_range.mp hg
      have r1 : read_word ((Blake2sBinaryCols.ofCells
          ((List.range L.main_width).map fun c => env (.main 0 c))).rounds 9 g).d1 = some (D1 g) :=
        read_word_eq (hD1 g hg')
      have r2 : read_word ((Blake2sBinaryCols.ofCells
          ((List.range L.main_width).map fun c => env (.main 0 c))).rounds 9 g).b1 = some (B1 g) :=
        read_word_eq (hB1 g hg')
      have r3 : read_word ((Blake2sBinaryCols.ofCells
          ((List.range L.main_width).map fun c => env (.main 0 c))).rounds 9 g).d2 = some (D2 g) :=
        read_word_eq (hD2 g hg')
      have r4 : read_word ((Blake2sBinaryCols.ofCells
          ((List.range L.main_width).map fun c => env (.main 0 c))).rounds 9 g).b2 = some (B2 g) :=
        read_word_eq (hB2 g hg')
      rw [r1, Option.bind_some, r2, Option.bind_some, r3, Option.bind_some, r4, Option.bind_some]
  have hcv : (List.range 8).mapM (fun i => read_word ((Blake2sBinaryCols.ofCells
      ((List.range L.main_width).map fun c => env (.main 0 c))).chaining_value i)) = some (cvOf loc) :=
    mapM_eq_some _ _ fun i hi =>
      read_word_eq (Plonky3Lean.Proofs.Sha256Air.holds_wordOf (hB.1 i (List.mem_range.mp hi)))
  -- The words read are the working vector after ten rounds.
  have hfin : finalState loc = TRound loc ((List.range 9).foldl (TRound loc) (initState loc)) 9 := by
    rw [finalState, NUM_ROUNDS, List.range_succ, List.foldl_append]
    rfl
  rw [hfin] at hS
  obtain ⟨-, hS⟩ := hS
  obtain ⟨fa, fb, fc, fd⟩ := lastRound_eq loc ((List.range 9).foldl (TRound loc) (initState loc))
  obtain ⟨ra, rb, rc, rd⟩ := readback_getD D1 B1 D2 B2
  have hRB : ∀ k < 16, (readback D1 B1 D2 B2).getD k 0 =
      (Plonky3Lean.Spec.Blake2s.rounds (blockOf loc)
        (Plonky3Lean.Spec.Blake2s.init (cvOf loc) (counterOf loc) (flagOf loc)) 10).getD k 0 := by
    intro k hk
    rcases Nat.lt_or_ge k 8 with h8 | h8
    · rcases Nat.lt_or_ge k 4 with h4 | h4
      · have := (hS k h4).1
        rw [fa k h4, xor_rotl_var_eq] at this
        rw [ra k h4]
        exact Holds.unique (xor_rotl_holds h2 (n := 8) (by norm_num) (hD1 (4 + k) (by omega)) (hD2 (4 + k) (by omega))) this
      · obtain ⟨j, rfl⟩ : ∃ j, k = 4 + j := ⟨k - 4, by omega⟩
        have := (hS j (by omega)).2.1
        rw [fb j (by omega)] at this
        rw [rb j (by omega)]
        exact Holds.unique (hB2 (4 + (j + 3) % 4) (by omega)) this
    · rcases Nat.lt_or_ge k 12 with h12 | h12
      · obtain ⟨j, rfl⟩ : ∃ j, k = 8 + j := ⟨k - 8, by omega⟩
        have := (hS j (by omega)).2.2.1
        rw [fc j (by omega), xor_rotl_var_eq] at this
        rw [rc j (by omega)]
        exact Holds.unique (xor_rotl_holds h2 (n := 7) (by norm_num) (hB1 (4 + (j + 2) % 4) (by omega))
          (hB2 (4 + (j + 2) % 4) (by omega))) this
      · obtain ⟨j, rfl⟩ : ∃ j, k = 12 + j := ⟨k - 12, by omega⟩
        have := (hS j (by omega)).2.2.2
        rw [fd j (by omega)] at this
        rw [rd j (by omega)]
        exact Holds.unique (hD2 (4 + (j + 1) % 4) (by omega)) this
  unfold compression_output
  simp only [NUM_ROUNDS, Nat.reduceSub, hsar, hcv, Option.bind_eq_bind, Option.bind_some,
    Option.pure_def, Plonky3Lean.Spec.Blake2s.compress, Option.some.injEq]
  refine List.map_congr_left fun i hi => ?_
  have hi := List.mem_range.mp hi
  rw [hRB i (by omega), hRB (i + 8) (by omega)]

end Plonky3Lean.Proofs.Blake2sAir
