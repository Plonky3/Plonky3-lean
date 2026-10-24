module

public import Plonky3Lean.Proofs.Blake3Air.Binary.Sound

@[expose] public section

/-!
# The output reader

The reader recovers the final state from the last round's witness columns.

Each G step's columns give the four words it writes, and the diagonal steps write every word.

So when every step writes what the generator's G step computes, the reader returns the final state.
-/

set_option linter.unusedSectionVars false

namespace Plonky3Lean.Proofs.Blake3Air.Binary

open p3_air.builder.mirror p3_air.air.mirror p3_blake3_air.mirror p3_blake3_air.mirror.binary
open Plonky3Lean.Proofs.KeccakAir Plonky3Lean.Proofs.Blake3Air

/-- Write four words at four positions, in order. -/
def updF (v : ℕ → Word) (a b c d : ℕ) (A B C D : Word) : ℕ → Word :=
  Function.update (Function.update (Function.update (Function.update v a A) b B) c C) d D

/-- The positions G step g writes. -/
def posOf (g : ℕ) : List ℕ := [slot g 0, 4 + slot g 1, 8 + slot g 2, 12 + slot g 3]

theorem updF_mem (v w : ℕ → Word) {a b c d : ℕ} (A B C D : Word) {p : ℕ} (hp : p ∈ [a, b, c, d]) :
    updF v a b c d A B C D p = updF w a b c d A B C D p := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  simp only [updF, Function.update_apply]
  split_ifs <;> first | rfl | (exfalso; tauto)

theorem updF_not_mem (v : ℕ → Word) {a b c d : ℕ} (A B C D : Word) {p : ℕ} (hp : p ∉ [a, b, c, d]) :
    updF v a b c d A B C D p = v p := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hp
  simp [updF, hp.1, hp.2.1, hp.2.2.1, hp.2.2.2]

theorem gF_eq_updF (σ : ℕ → Word) (a b c d : ℕ) (mx my : Word) :
    gF σ a b c d mx my =
      let r := verifiable_half_round (σ a) (σ b) (σ c) (σ d) mx false
      let r' := verifiable_half_round r.1 r.2.1 r.2.2.1 r.2.2.2 my true
      updF σ a b c d r'.1 r'.2.1 r'.2.2.1 r'.2.2.2 := rfl

/-- Every word index below 16 is written by a diagonal step. -/
theorem written (p : ℕ) (hp : p < 16) : ∃ g < 8, p ∈ posOf g := by
  interval_cases p <;> decide

/-- Two chains of the same writes agree on every written position.

The second starts from 0, so it is 0 elsewhere. -/
theorem upd_chain (τ v : ℕ → ℕ → Word) (vals : ℕ → Word × Word × Word × Word)
    (hτ : ∀ n, τ (n + 1) = updF (τ n) (slot n 0) (4 + slot n 1) (8 + slot n 2) (12 + slot n 3)
      (vals n).1 (vals n).2.1 (vals n).2.2.1 (vals n).2.2.2)
    (hv : ∀ n, v (n + 1) = updF (v n) (slot n 0) (4 + slot n 1) (8 + slot n 2) (12 + slot n 3)
      (vals n).1 (vals n).2.1 (vals n).2.2.1 (vals n).2.2.2)
    (hv0 : v 0 = fun _ => 0) :
    ∀ n p, v n p = if ∃ g < n, p ∈ posOf g then τ n p else 0 := by
  intro n
  induction n with
  | zero => intro p; simp [hv0]
  | succ n ih =>
    intro p
    rw [hτ, hv]
    by_cases hp : p ∈ posOf n
    · rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨n, by omega, hp⟩)]
      exact updF_mem _ _ _ _ _ _ hp
    · rw [updF_not_mem _ _ _ _ _ hp, updF_not_mem _ _ _ _ _ hp, ih]
      congr 1
      apply propext
      constructor
      · rintro ⟨g, hg, h⟩; exact ⟨g, by omega, h⟩
      · rintro ⟨g, hg, h⟩
        refine ⟨g, ?_, h⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hg with h' | h'
        · exact h'
        · subst h'; exact absurd h hp

variable {F : Type} [Field F]

theorem foldl_snd {α X : Type} (g : α → Prop × X → Prop × X)
    (h2 : ∀ a s x, (g a (s, x)).2 = (g a (True, x)).2) (l : List α) (s s' : Prop) (x : X) :
    (l.foldl (fun acc a => g a acc) (s, x)).2 = (l.foldl (fun acc a => g a acc) (s', x)).2 := by
  induction l generalizing s s' x with
  | nil => rfl
  | cons a l ih =>
    rw [List.foldl_cons, List.foldl_cons,
      show g a (s, x) = ((g a (s, x)).1, (g a (True, x)).2) from Prod.ext rfl (h2 a s x),
      show g a (s', x) = ((g a (s', x)).1, (g a (True, x)).2) from Prod.ext rfl (h2 a s' x), ih]

theorem checksP_append {α X : Type} (g : α → Prop × X → Prop × X)
    (h2 : ∀ a s x, (g a (s, x)).2 = (g a (True, x)).2) (l₁ l₂ : List α) (x : X) :
    checksP g (l₁ ++ l₂) x ↔ checksP g l₁ x ∧ checksP g l₂ (l₁.foldl (fun acc a => g a acc) (True, x)).2 := by
  induction l₁ generalizing x with
  | nil => simp [checksP]
  | cons a l ih =>
    rw [List.cons_append, checksP, checksP, ih, List.foldl_cons,
      show g a (True, x) = ((g a (True, x)).1, (g a (True, x)).2) from rfl,
      foldl_snd g h2 l (g a (True, x)).1 True]
    exact and_assoc.symm

/-- A trace row seen as the column struct. -/
def rowCols (loc : ℕ → F) : Blake3BinaryCols F where
  chaining_value i k := loc (col.chaining_value i k)
  block i k := loc (col.block i k)
  counter_low k := loc (binary.col.counter_low k)
  counter_high k := loc (binary.col.counter_high k)
  block_len k := loc (binary.col.block_len k)
  flags k := loc (binary.col.flags k)
  rounds r g := ⟨fun k => loc (col.add1_carries r g k), fun k => loc (col.d1 r g k),
    fun k => loc (col.b1 r g k), fun k => loc (col.add2_carries r g k), fun k => loc (col.d2 r g k),
    fun k => loc (col.b2 r g k)⟩

theorem written_iff (p : ℕ) : (∃ g < 8, p ∈ posOf g) ↔ p < 16 := by
  constructor
  · rintro ⟨g, -, h⟩
    simp only [posOf, List.mem_cons, List.not_mem_nil, or_false] at h
    have := slot_lt g 0; have := slot_lt g 1; have := slot_lt g 2; have := slot_lt g 3
    omega
  · exact written p

/-- When every column reads as a word, the reader's fold over the steps computes the writes of those words. -/
theorem reader_fold [DecidableEq F] (r : Blake3BinaryCols F) (D1 B1 D2 B2 : ℕ → Word)
    (hw : ∀ g < 8, read_word (r.rounds 6 g).d1 = some (D1 g) ∧ read_word (r.rounds 6 g).b1 = some (B1 g) ∧
      read_word (r.rounds 6 g).d2 = some (D2 g) ∧ read_word (r.rounds 6 g).b2 = some (B2 g)) :
    ∀ n ≤ 8, (List.range n).foldlM (fun (v : ℕ → Word) g => do
      let cols := r.rounds (NUM_ROUNDS - 1) g
      let d1 ← read_word cols.d1
      let b1 ← read_word cols.b1
      let d2 ← read_word cols.d2
      let b2 ← read_word cols.b2
      let v := Function.update v (slot g 0) (d1 ^^^ d2.rotateLeft 8)
      let v := Function.update v (4 + slot g 1) b2
      let v := Function.update v (8 + slot g 2) (b1 ^^^ b2.rotateLeft 7)
      pure (Function.update v (12 + slot g 3) d2)) (fun _ => 0) =
    some ((List.range n).foldl (fun v g => updF v (slot g 0) (4 + slot g 1) (8 + slot g 2) (12 + slot g 3)
      (D1 g ^^^ (D2 g).rotateLeft 8) (B2 g) (B1 g ^^^ (B2 g).rotateLeft 7) (D2 g)) (fun _ => 0)) := by
  intro n hn
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.range_succ, List.foldlM_append, ih (by omega), List.foldl_append]
    obtain ⟨e1, e2, e3, e4⟩ := hw n (by omega)
    simp only [List.foldlM_cons, List.foldlM_nil, List.foldl_cons, List.foldl_nil, NUM_ROUNDS,
      Option.bind_eq_bind, Option.bind_some, e1, e2, e3, e4]
    rfl

theorem cv_fold [DecidableEq F] (r : Blake3BinaryCols F) (cvw : ℕ → Word)
    (hw : ∀ i < 8, read_word (r.chaining_value i) = some (cvw i)) :
    ∀ n ≤ 8, (List.range n).foldlM (fun (cv : ℕ → Word) i => do
      let w ← read_word (r.chaining_value i)
      pure (Function.update cv i w)) (fun _ => 0) = some (fun i => if i < n then cvw i else 0) := by
  intro n hn
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.range_succ, List.foldlM_append, ih (by omega)]
    simp only [List.foldlM_cons, List.foldlM_nil, Option.bind_eq_bind, Option.bind_some,
      hw n (by omega)]
    show some _ = some _
    congr 1
    funext i
    simp only [Function.update_apply]
    by_cases h1 : i = n
    · subst h1; simp
    · by_cases h3 : i < n
      · simp [h1, h3, show i < n + 1 by omega]
      · simp [h1, h3, show ¬ i < n + 1 by omega]

variable (h2 : (2 : F) = 0)
include h2

/-- In a round whose constraints hold, step g's columns hold the generator's words from the state before it. -/
theorem round_witness (env : Plonky3Lean.Spec.Air.Var → F) (L : AirLayout) {blk : ℕ → Word}
    (hblk : ∀ i < 16, BitsRep (fun k => rowOf env L 0 (col.block i k)) (blk i)) {st : State F}
    {σ : ℕ → Word} (hst : StB st σ) (r : ℕ)
    (hchk : checksP (fun rg : ℕ × ℕ => g_step (propBuilder env L) (rowOf env L 0) rg.1 rg.2)
      ((List.range 8).map fun g => (r, g)) st) (g : ℕ) (hg : g < 8) :
    let τ := gfold blk ((List.range g).map fun g => (r, g)) σ
    let rr := verifiable_half_round (τ (slot g 0)) (τ (4 + slot g 1)) (τ (8 + slot g 2))
      (τ (12 + slot g 3)) (blk (msgIdx r (2 * g))) false
    let rr' := verifiable_half_round rr.1 rr.2.1 rr.2.2.1 rr.2.2.2 (blk (msgIdx r (2 * g + 1))) true
    BitsRep (fun k => rowOf env L 0 (col.d1 r g k)) rr.2.2.2 ∧
      BitsRep (fun k => rowOf env L 0 (col.b1 r g k)) rr.2.1 ∧
      BitsRep (fun k => rowOf env L 0 (col.d2 r g k)) rr'.2.2.2 ∧
      BitsRep (fun k => rowOf env L 0 (col.b2 r g k)) rr'.2.1 := by
  have hsplit : (List.range 8).map (fun g => (r, g)) = (List.range g).map (fun g => (r, g)) ++
      (r, g) :: (List.range' (g + 1) (7 - g)).map (fun g => (r, g)) := by
    rw [List.range_eq_range', List.range_eq_range', show 8 = g + ((7 - g) + 1) by omega,
      ← List.range'_append_1, List.range'_succ]
    simp
  rw [hsplit] at hchk
  have hsnd : ∀ (a : ℕ × ℕ) (s : Prop) (x : State F), (g_step (propBuilder env L) (rowOf env L 0) a.1 a.2 (s, x)).2 =
      (g_step (propBuilder env L) (rowOf env L 0) a.1 a.2 (True, x)).2 := fun _ _ _ => rfl
  obtain ⟨hpre, hstep, -⟩ := (checksP_append _ hsnd _ _ st).mp hchk
  have hst' := sched_sound h2 env L hblk _ (fun rg h => by
    simp only [List.mem_map, List.mem_range] at h; obtain ⟨g', hg', rfl⟩ := h; simp; omega) hst hpre
  simp only [g_step, prop_eval_g, true_and] at hstep
  have hm : ∀ t < 2, msgIdx r (2 * g + t) < 16 := fun t ht => by
    rw [msgIdx_eq]; exact Plonky3Lean.Proofs.Blake3.permPow_lt _ _ (by omega)
  exact (step_rep h2 env L hst' (slot_lt _ _) (slot_lt _ _) (slot_lt _ _) (slot_lt _ _)
    (hblk _ (hm 0 (by norm_num))) (hblk _ (hm 1 (by norm_num))) hstep True).2

/-- The reader returns the feed-forward of the last round's output state, when the last round's constraints hold. -/
theorem reader_sound [DecidableEq F] (env : Plonky3Lean.Spec.Air.Var → F) (L : AirLayout) {blk : ℕ → Word}
    (hblk : ∀ i < 16, BitsRep (fun k => rowOf env L 0 (col.block i k)) (blk i)) {st : State F}
    {σ : ℕ → Word} (hst : StB st σ)
    (hchk : checksP (fun rg : ℕ × ℕ => g_step (propBuilder env L) (rowOf env L 0) rg.1 rg.2)
      ((List.range 8).map fun g => (6, g)) st) {cvw : ℕ → Word}
    (hcv : ∀ i < 8, BitsRep (fun k => rowOf env L 0 (col.chaining_value i k)) (cvw i))
    {loc : ℕ → F} (hloc : ∀ c < NUM_BLAKE3_BINARY_COLS, loc c = rowOf env L 0 c) :
    compression_output (rowCols loc) = some fun i =>
      let τ : ℕ → Word := fun p => if p < 16 then roundF σ (fun j => blk (msgIdx 6 j)) p else 0
      if i < 8 then τ i ^^^ τ (i + 8) else τ i ^^^ (if i - 8 < 8 then cvw (i - 8) else 0) := by
  -- The states before each step of the last round, and the words each step writes.
  let τs : ℕ → ℕ → Word := fun n => gfold blk ((List.range n).map fun g => (6, g)) σ
  let rr : ℕ → Word × Word × Word × Word := fun g =>
    verifiable_half_round (τs g (slot g 0)) (τs g (4 + slot g 1)) (τs g (8 + slot g 2))
      (τs g (12 + slot g 3)) (blk (msgIdx 6 (2 * g))) false
  let rr' : ℕ → Word × Word × Word × Word := fun g =>
    verifiable_half_round (rr g).1 (rr g).2.1 (rr g).2.2.1 (rr g).2.2.2 (blk (msgIdx 6 (2 * g + 1))) true
  have hwit := fun g (hg : g < 8) => round_witness h2 env L hblk hst 6 hchk g hg
  have tr : ∀ {c : ℕ → ℕ} {w : Word}, (∀ k < 32, c k < NUM_BLAKE3_BINARY_COLS) →
      BitsRep (fun k => rowOf env L 0 (c k)) w → read_word (fun k => loc (c k)) = some w :=
    fun hc h => read_word_eq (bitsRep_congr (fun k hk => (hloc _ (hc k hk)).symm) h)
  have hw : ∀ g < 8, read_word ((rowCols loc).rounds 6 g).d1 = some (rr g).2.2.2 ∧
      read_word ((rowCols loc).rounds 6 g).b1 = some (rr g).2.1 ∧
      read_word ((rowCols loc).rounds 6 g).d2 = some (rr' g).2.2.2 ∧
      read_word ((rowCols loc).rounds 6 g).b2 = some (rr' g).2.1 := fun g hg =>
    ⟨tr (fun k hk => by simp only [col.d1, col.g, NUM_BLAKE3_BINARY_COLS]; omega) (hwit g hg).1,
      tr (fun k hk => by simp only [col.b1, col.g, NUM_BLAKE3_BINARY_COLS]; omega) (hwit g hg).2.1,
      tr (fun k hk => by simp only [col.d2, col.g, NUM_BLAKE3_BINARY_COLS]; omega) (hwit g hg).2.2.1,
      tr (fun k hk => by simp only [col.b2, col.g, NUM_BLAKE3_BINARY_COLS]; omega) (hwit g hg).2.2.2⟩
  have hc : ∀ i < 8, read_word ((rowCols loc).chaining_value i) = some (cvw i) :=
    fun i hi => tr (fun k hk => by simp only [col.chaining_value, NUM_BLAKE3_BINARY_COLS]; omega)
      (hcv i hi)
  unfold compression_output
  rw [show G_PER_ROUND = 8 from rfl, reader_fold _ (fun g => (rr g).2.2.2) (fun g => (rr g).2.1) (fun g => (rr' g).2.2.2)
    (fun g => (rr' g).2.1) hw 8 le_rfl, cv_fold _ cvw hc 8 le_rfl]
  simp only [Option.bind_eq_bind, Option.bind_some, Option.pure_def]
  congr 1
  -- The reader's writes agree with the states' on every word.
  have hchain := upd_chain τs (fun n => (List.range n).foldl (fun v g => updF v (slot g 0) (4 + slot g 1)
      (8 + slot g 2) (12 + slot g 3) ((rr g).2.2.2 ^^^ (rr' g).2.2.2.rotateLeft 8) (rr' g).2.1
      ((rr g).2.1 ^^^ (rr' g).2.1.rotateLeft 7) (rr' g).2.2.2) (fun _ => 0))
    (fun g => (((rr g).2.2.2 ^^^ (rr' g).2.2.2.rotateLeft 8), (rr' g).2.1,
      ((rr g).2.1 ^^^ (rr' g).2.1.rotateLeft 7), (rr' g).2.2.2))
    (fun n => by
      simp only [τs]
      rw [List.range_succ, List.map_append, gfold_append]
      simp only [List.map_cons, List.map_nil, gfold, List.foldl_cons, List.foldl_nil]
      have e1 : (rr n).2.2.2 ^^^ (rr' n).2.2.2.rotateLeft 8 = (rr' n).1 := by
        rw [show (rr' n).2.2.2 = ((rr n).2.2.2 ^^^ (rr' n).1).rotateRight 8 from rfl,
          xor_rotl_rotr _ _ (by norm_num)]
      have e3 : (rr n).2.1 ^^^ (rr' n).2.1.rotateLeft 7 = (rr' n).2.2.1 := by
        rw [show (rr' n).2.1 = ((rr n).2.1 ^^^ (rr' n).2.2.1).rotateRight 7 from rfl,
          xor_rotl_rotr _ _ (by norm_num)]
      rw [gF_eq_updF]
      dsimp only
      rw [e1, e3]
      rfl)
    (fun n => by simp only [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil])
    rfl 8
  have hv : ∀ p, (List.range 8).foldl (fun v g => updF v (slot g 0) (4 + slot g 1)
      (8 + slot g 2) (12 + slot g 3) ((rr g).2.2.2 ^^^ (rr' g).2.2.2.rotateLeft 8) (rr' g).2.1
      ((rr g).2.1 ^^^ (rr' g).2.1.rotateLeft 7) (rr' g).2.2.2) (fun _ => 0) p =
      if p < 16 then roundF σ (fun j => blk (msgIdx 6 j)) p else 0 := by
    intro p
    rw [hchain p]
    simp only [written_iff, τs, gfold_round]
  funext i
  simp only [hv]

end Plonky3Lean.Proofs.Blake3Air.Binary
