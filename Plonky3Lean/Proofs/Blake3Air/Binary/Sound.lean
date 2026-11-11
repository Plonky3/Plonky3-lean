module

public import Plonky3Lean.Proofs.Blake3Air.Binary.Words
public import Plonky3Lean.Proofs.Blake3Air.Binary.Degree
public import Plonky3Lean.Proofs.Blake3Air.Sound

@[expose] public section

/-!
# Soundness of the characteristic-2 BLAKE3 AIR

Let a trace satisfy the AIR, over a field of characteristic 2.

When the AIR states the input booleanity, or when the trace's input cells are bits:

- every G step forces its witness columns to the words of the generator's G step,
- the output the row reader recovers is the BLAKE3 compression of the row's inputs.
-/

set_option linter.unusedSectionVars false

namespace Plonky3Lean.Proofs.Blake3Air.Binary

open p3_air.builder.mirror p3_air.air.mirror p3_blake3_air.mirror p3_blake3_air.mirror.binary
open Plonky3Lean.Spec.Air Plonky3Lean.Proofs.Air Plonky3Lean.Proofs.KeccakAir Plonky3Lean.Proofs.Blake3Air

variable {F : Type} [Field F]

/-! ## The row builder -/

section prop

variable (env : Var → F) (L : AirLayout)

theorem prop_eval_g (s : Prop) (st : State F) (ia ib ic id : ℕ) (mx my c1 d1 b1 c2 d2 b2 : ℕ → F) :
    (eval_g (propBuilder env L) s st ia ib ic id mx my c1 d1 b1 c2 d2 b2).1 =
      (s ∧ GB (st.a ia) (st.b ib) (st.c ic) (st.d id) mx my c1 d1 b1 c2 d2 b2) := by
  simp only [eval_g, prop_add3, prop_add2, pb_ops, GB, and_assoc]

theorem snd_eval_g (s s' : Prop) (st : State F) (ia ib ic id : ℕ) (mx my c1 d1 b1 c2 d2 b2 : ℕ → F) :
    (eval_g (propBuilder env L) s st ia ib ic id mx my c1 d1 b1 c2 d2 b2).2 =
      (eval_g (propBuilder env L) s' st ia ib ic id mx my c1 d1 b1 c2 d2 b2).2 := rfl

/-- The checks of a list of state-carrying steps, each from true and from the state its predecessors reach. -/
def checksP {α X : Type} (g : α → Prop × X → Prop × X) : List α → X → Prop
  | [], _ => True
  | a :: l, x => (g a (True, x)).1 ∧ checksP g l (g a (True, x)).2

theorem foldl_checksP {α X : Type} (g : α → Prop × X → Prop × X)
    (h1 : ∀ a s x, (g a (s, x)).1 = (s ∧ (g a (True, x)).1))
    (h2 : ∀ a s x, (g a (s, x)).2 = (g a (True, x)).2) (l : List α) (s : Prop) (x : X) :
    (l.foldl (fun acc a => g a acc) (s, x)).1 = (s ∧ checksP g l x) := by
  induction l generalizing s x with
  | nil => simp [checksP]
  | cons a l ih =>
    rw [List.foldl_cons, show g a (s, x) = ((g a (s, x)).1, (g a (s, x)).2) from rfl, ih, h1, h2]
    simp [checksP, and_assoc]

/-- The row builder accepts a row exactly when its constraints hold.

- The input booleanity holds, if stated.
- Every G step's constraints hold along the states. -/
theorem eval_iff (cb : Bool) :
    binary.eval cb (propBuilder env L) True ↔
      (cb = true → binary.assert_inputs (propBuilder env L) (rowOf env L 0) True) ∧
        checksP (fun rg : ℕ × ℕ => g_step (propBuilder env L) (rowOf env L 0) rg.1 rg.2) schedule
          (binary.initial_state (propBuilder env L) (rowOf env L 0)) := by
  have hf : ∀ s x, (rounds (propBuilder env L) (rowOf env L 0) (s, x)).1 =
      (s ∧ checksP (fun rg : ℕ × ℕ => g_step (propBuilder env L) (rowOf env L 0) rg.1 rg.2) schedule x) := by
    intro s x
    rw [← foldl_checksP _ (fun a s x => by simp only [g_step, prop_eval_g, true_and])
      (fun a s x => rfl), schedule, List.foldl_flatMap]
    simp only [List.foldl_map]
    rfl
  have hloc : (fun i => ((propBuilder env L).main True).current.getD i ((propBuilder env L).const 0)) =
      rowOf env L 0 := rfl
  show (rounds _ _ (_, _)).1 ↔ _
  rw [hloc, hf]
  cases cb <;> simp

end prop

/-! ## States -/

/-- A state's bit cells hold a 16-word state. -/
def StB (st : State F) (σ : ℕ → Word) : Prop :=
  ∀ j < 4, BitsRep (st.a j) (σ j) ∧ BitsRep (st.b j) (σ (4 + j)) ∧ BitsRep (st.c j) (σ (8 + j)) ∧
    BitsRep (st.d j) (σ (12 + j))

theorem gF_apply (σ : ℕ → Word) (a b c d : ℕ) (mx my : Word) (p : ℕ) :
    gF σ a b c d mx my p =
      let r := verifiable_half_round (σ a) (σ b) (σ c) (σ d) mx false
      let r' := verifiable_half_round r.1 r.2.1 r.2.2.1 r.2.2.2 my true
      if p = d then r'.2.2.2 else if p = c then r'.2.2.1 else if p = b then r'.2.1
      else if p = a then r'.1 else σ p := by
  simp only [gF, Function.update_apply]

theorem slot_lt (g j : ℕ) : slot g j < 4 := by
  simp only [slot, G_SCHEDULE]
  rcases g with _ | _ | _ | _ | _ | _ | _ | _ | g <;> rcases j with _ | _ | _ | _ | j <;> simp

/-- The message word G step g of round r reads. -/
def msgIdx (r g : ℕ) : ℕ := (permute^[r] id) g

theorem msgIdx_eq (r i : ℕ) : msgIdx r i = Plonky3Lean.Proofs.Blake3.permPow r i := by
  simp only [msgIdx, permute_iter_apply, id]

/-- The quarter rounds of a list of G steps, on maps, with the message words of a block. -/
def gfold (blk : ℕ → Word) (l : List (ℕ × ℕ)) (σ : ℕ → Word) : ℕ → Word :=
  l.foldl (fun σ rg => gF σ (slot rg.2 0) (4 + slot rg.2 1) (8 + slot rg.2 2) (12 + slot rg.2 3)
    (blk (msgIdx rg.1 (2 * rg.2))) (blk (msgIdx rg.1 (2 * rg.2 + 1)))) σ

theorem gfold_round (blk : ℕ → Word) (r : ℕ) (σ : ℕ → Word) :
    gfold blk ((List.range 8).map fun g => (r, g)) σ = roundF σ fun i => blk (msgIdx r i) := rfl

theorem gfold_append (blk : ℕ → Word) (l₁ l₂ : List (ℕ × ℕ)) (σ : ℕ → Word) :
    gfold blk (l₁ ++ l₂) σ = gfold blk l₂ (gfold blk l₁ σ) := List.foldl_append

theorem roundF_congr (σ : ℕ → Word) {m m' : ℕ → Word} (h : ∀ i < 16, m i = m' i) :
    roundF σ m = roundF σ m' := by
  simp only [roundF, diagsF, colsF, h 0 (by norm_num), h 1 (by norm_num), h 2 (by norm_num),
    h 3 (by norm_num), h 4 (by norm_num), h 5 (by norm_num), h 6 (by norm_num), h 7 (by norm_num),
    h 8 (by norm_num), h 9 (by norm_num), h 10 (by norm_num), h 11 (by norm_num), h 12 (by norm_num),
    h 13 (by norm_num), h 14 (by norm_num), h 15 (by norm_num)]

open Plonky3Lean.Spec.Blake3 in
/-- The G steps of the first n rounds compute n rounds of the specification. -/
theorem gfold_rounds (s0 blk : List (BitVec 32)) (hs : s0.length = 16) {n : ℕ} :
    gfold (fun i => blk.getD i 0) ((List.range n).flatMap fun r => (List.range 8).map fun g => (r, g))
      (fun i => s0.getD i 0) = fun i => (rounds n s0 blk).getD i 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [show List.range (n + 1) = List.range n ++ [n] from List.range_succ, List.flatMap_append,
      gfold_append, ih]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    rw [gfold_round, rounds_succ]
    funext i
    rw [round_getD _ _ (length_rounds _ _ _ hs)]
    rw [roundF_congr _ (m' := fun j => (Spec.Blake3.permute^[n] blk).getD j 0) fun j hj => by
      rw [msgIdx_eq, Plonky3Lean.Proofs.Blake3.permute_iter_getD _ _ _ hj]]

/-! ## Reading words -/

omit [Field F] in
theorem read_word_foldlM [Field F] [DecidableEq F] {f : ℕ → F} {w : Word} (h : BitsRep f w) (n : ℕ)
    (hn : n ≤ 32) : ∃ x : Word, (List.range n).foldlM (fun word i =>
      if f i = 0 ∨ f i = 1 then some (word ||| (BitVec.ofBool (f i = 1)).setWidth 32 <<< i) else none)
      (0 : Word) = some x ∧ ∀ j, x.getLsbD j = (decide (j < n) && w.getLsbD j) := by
  induction n with
  | zero => exact ⟨0, rfl, fun j => by simp⟩
  | succ n ih =>
    obtain ⟨x, hx, hbits⟩ := ih (by omega)
    have hb := h n (by omega)
    refine ⟨x ||| (BitVec.ofBool (f n = 1)).setWidth 32 <<< n, ?_, fun j => ?_⟩
    · rw [List.range_succ, List.foldlM_append, hx]
      simp only [List.foldlM_cons, List.foldlM_nil, Option.bind_eq_bind, Option.bind_some]
      have hc : f n = 0 ∨ f n = 1 := by rw [hb]; cases w.getLsbD n <;> simp [bitF]
      simp only [hc, ↓reduceIte]; rfl
    · rw [BitVec.getLsbD_or, hbits, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth]
      rw [hb]
      by_cases hj : j < n
      · simp [hj, show j < n + 1 by omega]
      · by_cases hjn : j = n
        · subst hjn; cases w.getLsbD j <;> simp [bitF, show j < 32 by omega]
        · simp [hj, show ¬ j < n + 1 by omega, show j - n ≠ 0 by omega]

/-- Cells holding the bits of a word read as that word. -/
theorem read_word_eq [DecidableEq F] {f : ℕ → F} {w : Word} (h : BitsRep f w) : read_word f = some w := by
  obtain ⟨x, hx, hbits⟩ := read_word_foldlM h 32 le_rfl
  rw [read_word, hx]
  congr 1
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  rw [hbits, decide_eq_true hj, Bool.true_and]

variable (h2 : (2 : F) = 0)
include h2

/-- A G step whose constraints hold maps a state holding σ to one holding its quarter round.

Its witness columns hold the generator's words. -/
theorem step_rep (env : Var → F) (L : AirLayout) {st : State F} {σ : ℕ → Word} (hst : StB st σ)
    {ia ib ic id : ℕ} (ha : ia < 4) (hb : ib < 4) (hc : ic < 4) (hd : id < 4)
    {mx my c1 d1 b1 c2 d2 b2 : ℕ → F} {wx wy : Word} (hx : BitsRep mx wx) (hy : BitsRep my wy)
    (h : GB (st.a ia) (st.b ib) (st.c ic) (st.d id) mx my c1 d1 b1 c2 d2 b2) (s : Prop) :
    let r := verifiable_half_round (σ ia) (σ (4 + ib)) (σ (8 + ic)) (σ (12 + id)) wx false
    let r' := verifiable_half_round r.1 r.2.1 r.2.2.1 r.2.2.2 wy true
    StB (eval_g (propBuilder env L) s st ia ib ic id mx my c1 d1 b1 c2 d2 b2).2
        (gF σ ia (4 + ib) (8 + ic) (12 + id) wx wy) ∧
      BitsRep d1 r.2.2.2 ∧ BitsRep b1 r.2.1 ∧ BitsRep d2 r'.2.2.2 ∧ BitsRep b2 r'.2.1 := by
  obtain ⟨-, hb0, -, -⟩ := hst ib hb
  obtain ⟨ha0, -, -, -⟩ := hst ia ha
  obtain ⟨-, -, hc0, -⟩ := hst ic hc
  obtain ⟨-, -, -, hd0⟩ := hst id hd
  obtain ⟨hd1, hb1, hd2, hb2, hA2, hC2⟩ := gB_sound h2 ha0 hb0 hc0 hd0 hx hy h
  refine ⟨fun j hj => ?_, hd1, hb1, hd2, hb2⟩
  obtain ⟨e0, e1, e2, e3⟩ := hst j hj
  simp only [eval_g, pb_ops, gF_apply]
  refine ⟨?_, ?_, ?_, ?_⟩
  · by_cases hj' : j = ia
    · subst hj'; simpa [Function.update_apply, show ¬ j = 12 + id by omega, show ¬ j = 8 + ic by omega,
        show ¬ j = 4 + ib by omega] using hA2
    · simpa [Function.update_apply, hj', show ¬ j = 12 + id by omega, show ¬ j = 8 + ic by omega,
        show ¬ j = 4 + ib by omega] using e0
  · by_cases hj' : j = ib
    · subst hj'; simpa [Function.update_apply, show ¬ 4 + j = 12 + id by omega,
        show ¬ 4 + j = 8 + ic by omega] using hb2
    · simpa [Function.update_apply, hj', show ¬ 4 + j = 12 + id by omega, show ¬ 4 + j = 8 + ic by omega,
        show ¬ 4 + j = ia by omega] using e1
  · by_cases hj' : j = ic
    · subst hj'; simpa [Function.update_apply, show ¬ 8 + j = 12 + id by omega] using hC2
    · simpa [Function.update_apply, hj', show ¬ 8 + j = 12 + id by omega, show ¬ 8 + j = 4 + ib by omega,
        show ¬ 8 + j = ia by omega] using e2
  · by_cases hj' : j = id
    · subst hj'; simpa [Function.update_apply] using hd2
    · simpa [Function.update_apply, hj', show ¬ 12 + j = 8 + ic by omega,
        show ¬ 12 + j = 4 + ib by omega, show ¬ 12 + j = ia by omega] using e3

/-- Along a list of G steps whose constraints hold, the states hold the quarter rounds of the specification. -/
theorem sched_sound (env : Var → F) (L : AirLayout) {blk : ℕ → Word}
    (hblk : ∀ i < 16, BitsRep (fun k => rowOf env L 0 (col.block i k)) (blk i)) :
    ∀ (l : List (ℕ × ℕ)), (∀ rg ∈ l, rg.2 < 8) → ∀ {st : State F} {σ : ℕ → Word}, StB st σ →
      checksP (fun rg : ℕ × ℕ => g_step (propBuilder env L) (rowOf env L 0) rg.1 rg.2) l st →
      StB (l.foldl (fun acc rg => g_step (propBuilder env L) (rowOf env L 0) rg.1 rg.2 acc) (True, st)).2
        (gfold blk l σ) := by
  intro l hl
  induction l with
  | nil => intro st σ hst _; exact hst
  | cons rg l ih =>
    intro st σ hst hchk
    obtain ⟨hg, hrest⟩ := hchk
    have hg8 := hl rg (by simp)
    have hm : ∀ t < 2, msgIdx rg.1 (2 * rg.2 + t) < 16 := fun t ht => by
      rw [msgIdx_eq]; exact Plonky3Lean.Proofs.Blake3.permPow_lt _ _ (by omega)
    simp only [g_step, prop_eval_g, true_and] at hg
    have hstep := (step_rep h2 env L hst (slot_lt _ _) (slot_lt _ _) (slot_lt _ _) (slot_lt _ _)
      (hblk _ (hm 0 (by norm_num))) (hblk _ (hm 1 (by norm_num))) hg True).1
    rw [List.foldl_cons]
    have e : g_step (propBuilder env L) (rowOf env L 0) rg.1 rg.2 (True, st) =
        (True, (g_step (propBuilder env L) (rowOf env L 0) rg.1 rg.2 (True, st)).2) := by
      refine Prod.ext ?_ rfl
      simp only [g_step, prop_eval_g, true_and]
      exact propext ⟨fun _ => trivial, fun _ => hg⟩
    rw [e]
    exact ih (fun rg' h => hl rg' (by simp [h])) hstep hrest

end Plonky3Lean.Proofs.Blake3Air.Binary
