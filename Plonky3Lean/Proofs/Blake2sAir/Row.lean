module

public import Plonky3Lean.Proofs.Blake2sAir.Parametric
public import Plonky3Lean.Proofs.KeccakAir.Row

@[expose] public section

/-!
# The constraints of one row of the BLAKE2s AIR

On the row builder, the evaluation is a conjunction:

- the input booleanity, when the AIR states it
- for each G step in order, its two three-word additions and its two two-word additions.

Each G step reads the working state that the steps before it leave.

So the conjunction is written as a chain along the states.
-/

set_option linter.unusedSectionVars false

namespace Plonky3Lean.Proofs.Blake2sAir

open p3_air.builder.mirror p3_air.air.mirror p3_blake2s_air.mirror Plonky3Lean.Spec.Air
open Plonky3Lean.Proofs.KeccakAir (propBuilder fieldOps rowOf foldl_and)

variable {F : Type} [Field F]

/-! ## Chains of steps -/

/-- The conditions of a run of steps: each step's condition, on the state the steps before it leave. -/
def Chain {σ α : Type} (C : σ → α → Prop) (T : σ → α → σ) : List α → σ → Prop
  | [], _ => True
  | a :: l, st => C st a ∧ Chain C T l (T st a)

/-- A fold whose steps conjoin a condition and move the state is a chain. -/
theorem foldl_pair {σ α : Type} {f : Prop × σ → α → Prop × σ} {C : σ → α → Prop} {T : σ → α → σ}
    (hf : ∀ s st a, f (s, st) a = (s ∧ C st a, T st a)) (l : List α) (s : Prop) (st : σ) :
    l.foldl f (s, st) = (s ∧ Chain C T l st, l.foldl T st) := by
  induction l generalizing s st with
  | nil => simp [Chain]
  | cons a l ih => rw [List.foldl_cons, hf, ih]; simp [Chain, and_assoc]

/-- An invariant that every step keeps along a chain holds at its end. -/
theorem chain_inv {σ τ α : Type} {C : σ → α → Prop} {T : σ → α → σ} {U : τ → α → τ}
    {I : σ → τ → Prop} (hI : ∀ a st v, C st a → I st v → I (T st a) (U v a)) :
    ∀ (l : List α) (st : σ) (v : τ), Chain C T l st → I st v → I (l.foldl T st) (l.foldl U v)
  | [], _, _, _, h => h
  | a :: l, st, v, hc, h => chain_inv hI l _ _ hc.2 (hI a st v hc.1 h)

/-- Along a chain that keeps an invariant, every step's condition holds on some state of the invariant. -/
theorem chain_each {σ τ α : Type} {C : σ → α → Prop} {T : σ → α → σ} {U : τ → α → τ}
    {I : σ → τ → Prop} (hI : ∀ a st v, C st a → I st v → I (T st a) (U v a)) :
    ∀ (l : List α) (st : σ) (v : τ), Chain C T l st → I st v → ∀ a ∈ l, ∃ st' v', I st' v' ∧ C st' a
  | [], _, _, _, _, _, ha => absurd ha List.not_mem_nil
  | b :: l, st, v, hc, h, a, ha => by
    rcases List.mem_cons.mp ha with rfl | ha
    · exact ⟨st, v, h, hc.1⟩
    · exact chain_each hI l _ _ hc.2 (hI b st v hc.1 h) a ha

/-! ## The additions -/

/-- The constraints of a two-word addition with its carries read off the sum. -/
def Add2Ok (x y sum : ℕ → F) : Prop :=
  sum 0 + x 0 + y 0 = 0 ∧ ∀ i ∈ List.range 31, maj fieldOps (x i) (y i) (sum i + x i + y i) +
    (sum (i + 1) + x (i + 1) + y (i + 1)) = 0

/-- The bits of `x + y` with the carries `c` into bits 1 to 31. -/
def tOf (x y c : ℕ → F) : ℕ → F := fun i => if i = 0 then x 0 + y 0 else x i + y i + c (i - 1)

/-- The constraints of a three-word addition with the carries of its first addition stored. -/
def Add3Ok (x y z c sum : ℕ → F) : Prop :=
  (x 0 * y 0 + c 0 = 0 ∧ ∀ i ∈ List.range' 1 30, maj fieldOps (x i) (y i) (c (i - 1)) + c i = 0) ∧
    Add2Ok (tOf x y c) z sum

theorem fo_add (a b : F) : fieldOps.add a b = a + b := rfl
theorem fo_mul (a b : F) : fieldOps.mul a b = a * b := rfl
theorem fo_sub (a b : F) : fieldOps.sub a b = a - b := rfl
theorem fo_const (a : F) : fieldOps.const a = a := rfl

section pb

variable (env : Var → F) (L : AirLayout)

theorem add2_pb (s : Prop) (x y sum : ℕ → F) :
    add2 (propBuilder env L) s x y sum = (s ∧ Add2Ok x y sum) := by
  simp only [add2, Plonky3Lean.Proofs.KeccakAir.pb_assert_zero,
    Plonky3Lean.Proofs.KeccakAir.propBuilder_ops, foldl_and, Add2Ok, and_assoc, fo_add]

theorem add3_pb (s : Prop) (x y z c sum : ℕ → F) :
    add3 (propBuilder env L) s x y z c sum = (s ∧ Add3Ok x y z c sum) := by
  simp only [add3, add2_pb, Plonky3Lean.Proofs.KeccakAir.pb_assert_zero,
    Plonky3Lean.Proofs.KeccakAir.propBuilder_ops, foldl_and, Add3Ok, and_assoc, fo_add, fo_mul]
  rfl

/-- The constraints of one G step, on the state it reads. -/
def GOk (st : State F) (slots : List ℕ) (mx my : ℕ → F) (g : Blake2sBinaryGCols F) : Prop :=
  Add3Ok (st.a (slots.getD 0 0)) (st.b (slots.getD 1 0)) mx g.add1_carries
      (xor_rotl fieldOps (st.d (slots.getD 3 0)) g.d1 16) ∧
    Add2Ok (st.c (slots.getD 2 0)) g.d1 (xor_rotl_var fieldOps (st.b (slots.getD 1 0)) g.b1 12) ∧
    Add3Ok (xor_rotl fieldOps (st.d (slots.getD 3 0)) g.d1 16) g.b1 my g.add2_carries
      (xor_rotl_var fieldOps g.d1 g.d2 8) ∧
    Add2Ok (xor_rotl_var fieldOps (st.b (slots.getD 1 0)) g.b1 12) g.d2
      (xor_rotl_var fieldOps g.b1 g.b2 7)

/-- The state one G step leaves. -/
def gNext (st : State F) (slots : List ℕ) (g : Blake2sBinaryGCols F) : State F :=
  { a := Function.update st.a (slots.getD 0 0) (xor_rotl_var fieldOps g.d1 g.d2 8)
    b := Function.update st.b (slots.getD 1 0) g.b2
    c := Function.update st.c (slots.getD 2 0) (xor_rotl_var fieldOps g.b1 g.b2 7)
    d := Function.update st.d (slots.getD 3 0) g.d2 }

theorem eval_g_pb (s : Prop) (st : State F) (slots : List ℕ) (mx my : ℕ → F) (g : Blake2sBinaryGCols F) :
    eval_g (propBuilder env L) s st slots mx my g = (s ∧ GOk st slots mx my g, gNext st slots g) := by
  simp only [eval_g, add2_pb, add3_pb, GOk, gNext, Plonky3Lean.Proofs.KeccakAir.propBuilder_ops,
    and_assoc]

end pb

/-! ## The row -/

section row

variable (loc : ℕ → F)

/-- The working state before the rounds, as the evaluation builds it from a row. -/
def initState : State F :=
  { a := fun i b => loc (col.chaining_value i b)
    b := fun i b => loc (col.chaining_value (4 + i) b)
    c := fun i bit => u32_to_bits_le (IV.getD i 0) bit
    d := fun i =>
      let iv : ℕ → F := fun bit => u32_to_bits_le (IV.getD (4 + i) 0) bit
      match ([fun b => loc (col.counter_low b), fun b => loc (col.counter_high b),
          fun _ => loc col.last_block] : List (ℕ → F))[i]? with
      | none => iv
      | some word => fun bit => iv bit + word bit }

/-- The witness columns of G step `g` of round `r`. -/
def gcolsOf (r g : ℕ) : Blake2sBinaryGCols F :=
  ⟨fun c => loc (col.add1_carries r g c), fun b => loc (col.d1 r g b), fun b => loc (col.b1 r g b),
    fun c => loc (col.add2_carries r g c), fun b => loc (col.d2 r g b), fun b => loc (col.b2 r g b)⟩

/-- Message word `k` of the row. -/
def msg (k : ℕ) : ℕ → F := fun b => loc (col.block k b)

/-- The constraints of G step `g` of round `r`. -/
def CStep (r : ℕ) (st : State F) (g : ℕ) : Prop :=
  GOk st (G_SCHEDULE.getD g []) (msg loc ((SIGMA.getD r []).getD (2 * g) 0))
    (msg loc ((SIGMA.getD r []).getD (2 * g + 1) 0)) (gcolsOf loc r g)

/-- The state G step `g` of round `r` leaves. -/
def TStep (r : ℕ) (st : State F) (g : ℕ) : State F := gNext st (G_SCHEDULE.getD g []) (gcolsOf loc r g)

/-- The constraints of round `r`. -/
def CRound (st : State F) (r : ℕ) : Prop := Chain (CStep loc r) (TStep loc r) (List.range G_PER_ROUND) st

/-- The state round `r` leaves. -/
def TRound (st : State F) (r : ℕ) : State F := (List.range G_PER_ROUND).foldl (TStep loc r) st

/-- The input cells are bits. -/
def BoolOk : Prop :=
  (∀ i < 8, ∀ b < 32, loc (col.chaining_value i b) * (loc (col.chaining_value i b) - 1) = 0) ∧
  (∀ i < 16, ∀ b < 32, loc (col.block i b) * (loc (col.block i b) - 1) = 0) ∧
  (∀ b < 32, loc (col.counter_low b) * (loc (col.counter_low b) - 1) = 0) ∧
  (∀ b < 32, loc (col.counter_high b) * (loc (col.counter_high b) - 1) = 0) ∧
  loc col.last_block * (loc col.last_block - 1) = 0

end row

/-- On the row builder, the evaluation is the booleanity, when stated, and the chain of G steps. -/
theorem eval_iff (cb : Bool) (env : Var → F) (L : AirLayout) :
    eval cb (propBuilder env L) True ↔
      (cb = true → BoolOk (rowOf env L 0)) ∧
        Chain (CRound (rowOf env L 0)) (TRound (rowOf env L 0)) (List.range NUM_ROUNDS)
          (initState (rowOf env L 0)) := by
  have hround : ∀ (r : ℕ) (s : Prop) (st : State F),
      (List.range G_PER_ROUND).foldl (fun (acc : Prop × State F) g =>
        eval_g (propBuilder env L) acc.1 acc.2 (G_SCHEDULE.getD g []) (msg (rowOf env L 0)
          ((SIGMA.getD r []).getD (2 * g) 0)) (msg (rowOf env L 0) ((SIGMA.getD r []).getD (2 * g + 1) 0))
          (gcolsOf (rowOf env L 0) r g)) (s, st) =
        (s ∧ CRound (rowOf env L 0) st r, TRound (rowOf env L 0) st r) := fun r s st =>
    foldl_pair (fun s st g => eval_g_pb env L s st _ _ _ _) _ s st
  simp only [eval]
  rw [foldl_pair (fun s st r => hround r s st)]
  refine and_congr ?_ Iff.rfl
  cases cb
  · simp
  · simp only [ite_true, AirBuilder.assert_bool, AirBuilder.assert_bools, AirBuilder.assert_zeros,
      AirBuilder.bool_check, Plonky3Lean.Proofs.KeccakAir.pb_assert_zero,
      Plonky3Lean.Proofs.KeccakAir.pb_mul, Plonky3Lean.Proofs.KeccakAir.pb_sub,
      Plonky3Lean.Proofs.KeccakAir.pb_const, Plonky3Lean.Proofs.KeccakAir.pb_current, List.foldl_map,
      foldl_and, true_and, List.mem_append, List.mem_map, List.mem_range, List.mem_cons,
      List.mem_nil_iff, or_false, forall_eq, forall_exists_index, and_imp,
      forall_apply_eq_imp_iff₂, or_imp, forall_and, BoolOk, and_assoc, true_implies]

end Plonky3Lean.Proofs.Blake2sAir
