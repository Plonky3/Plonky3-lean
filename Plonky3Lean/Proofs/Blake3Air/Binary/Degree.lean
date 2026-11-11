module

public import Plonky3Lean.Proofs.Blake3Air.Degree
public import Plonky3Lean.Proofs.KeccakAir.Binary.Degree
public import Mathlib.Algebra.Field.ZMod

@[expose] public section

/-!
# The constraint degrees of the characteristic-2 BLAKE3 AIR

Every symbolic constraint has degree multiple at most 2, the AIR's own hint, and reads no selector.

The bounding builder checks this over GF(2), one G step at a time.

The AIR asserts exactly the number of constraints it reports.
-/

set_option linter.unusedSectionVars false

namespace Plonky3Lean.Proofs.Blake3Air.Binary

open p3_air.symbolic.mirror p3_air.builder.mirror p3_air.air.mirror p3_blake3_air.mirror
open p3_blake3_air.mirror.binary Plonky3Lean.Proofs.Air Plonky3Lean.Proofs.KeccakAir
open Plonky3Lean.Proofs.Blake3Air

/-! ## Steps that carry a state -/

/-- A step of the bounding builder's run that also carries a state.

From b && s it reaches b && its run from s.

The state it reaches does not depend on s. -/
def PLin {X : Type} (f : Bool × X → Bool × X) : Prop :=
  ∀ b s x, f (b && s, x) = (b && (f (s, x)).1, (f (s, x)).2)

/-- The checks of a list of state-carrying steps, each from true and from the state its predecessors reach. -/
def checks {α X : Type} (g : α → Bool × X → Bool × X) : List α → X → Bool
  | [], _ => true
  | a :: l, x => (g a (true, x)).1 && checks g l (g a (true, x)).2

theorem foldl_plin {α X : Type} (g : α → Bool × X → Bool × X) (hg : ∀ a, PLin (g a)) (l : List α)
    (s : Bool) (x : X) : (l.foldl (fun acc a => g a acc) (s, x)).1 = (s && checks g l x) := by
  induction l generalizing s x with
  | nil => simp [checks]
  | cons a l ih =>
    rw [List.foldl_cons, show g a (s, x) = g a (s && true, x) by rw [Bool.and_true], hg, ih]
    simp [checks, Bool.and_assoc]

variable {F : Type} [Field F] [DecidableEq F]

/-- The bounding builder of the characteristic-2 AIR. -/
abbrev TBB (F : Type) [Field F] (cb : Bool) : AirBuilder F (ℕ × ℕ) Bool :=
  topBuilderD 2 (AirLayout.from_air (binaryAir (F := F) cb))

/-- The row the bounding builder reads. -/
abbrev TLB (F : Type) [Field F] (cb : Bool) : ℕ → ℕ × ℕ :=
  fun i => ((TBB F cb).main true).current.getD i ((TBB F cb).const 0)

theorem plin_g_step (cb : Bool) (r g : ℕ) : PLin (g_step (TBB F cb) (TLB F cb) r g) := by
  intro b s x
  have h := rel_g_step (builderRel_and (F := F) 2 (AirLayout.from_air (binaryAir (F := F) cb)) b)
    (loc₁ := TLB F cb) (loc₂ := TLB F cb) (fun _ => rfl) r g (a₁ := (b && s, x)) (a₂ := (s, x))
    ⟨rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩
  obtain ⟨h1, ha, hb, hc, hd⟩ := h
  have key : ∀ y z : State (ℕ × ℕ), StateRel (R := Eq) y z → y = z := by
    rintro ⟨⟩ ⟨⟩ ⟨ha, hb, hc, hd⟩
    simp only [State.mk.injEq]
    exact ⟨funext₂ ha, funext₂ hb, funext₂ hc, funext₂ hd⟩
  exact Prod.ext h1 (key _ _ ⟨ha, hb, hc, hd⟩)

/-- The G steps in order: round r, step g. -/
def schedule : List (ℕ × ℕ) := (List.range 7).flatMap fun r => (List.range 8).map fun g => (r, g)

theorem rounds_fst (cb : Bool) (s : Bool) (x : State (ℕ × ℕ)) :
    (rounds (TBB F cb) (TLB F cb) (s, x)).1 =
      (s && checks (fun rg : ℕ × ℕ => g_step (TBB F cb) (TLB F cb) rg.1 rg.2) schedule x) := by
  rw [← foldl_plin (fun rg : ℕ × ℕ => g_step (TBB F cb) (TLB F cb) rg.1 rg.2)
    (fun rg => plin_g_step cb rg.1 rg.2) schedule s x]
  rw [schedule, List.foldl_flatMap]; simp only [List.foldl_map]; rfl

/-- The bounding builder accepts the characteristic-2 AIR with the bound 2. -/
abbrev TopOkB (F : Type) [Field F] (cb : Bool) : Prop :=
  (binaryAir (F := F) cb).eval (TBB F cb) true = true

theorem top_of_checks (cb : Bool)
    (hi : (if cb then binary.assert_inputs (TBB F cb) (TLB F cb) true else true) = true)
    (hc : checks (fun rg : ℕ × ℕ => g_step (TBB F cb) (TLB F cb) rg.1 rg.2) schedule
      (initial_state (TBB F cb) (TLB F cb)) = true) : TopOkB F cb := by
  have he : (binaryAir (F := F) cb).eval (TBB F cb) true =
      (rounds (TBB F cb) (TLB F cb) (if cb then binary.assert_inputs (TBB F cb) (TLB F cb) true else true,
        initial_state (TBB F cb) (TLB F cb))).1 := by simp only [binaryAir, binary.eval]
  rw [TopOkB, he, rounds_fst, hi, hc, Bool.and_true]

theorem TLB_eq (cb : Bool) :
    TLB F cb = fun i => if i < NUM_BLAKE3_BINARY_COLS then (1, 0) else (0, 0) := by
  funext i
  simp only [TLB, TBB, topBuilderD, getD_map_range_const, AirLayout.from_air, binaryAir]

/-- Rewrite the bounding builder's row to a closed form and evaluate. -/
macro "bin_tac" : tactic => `(tactic| (
  simp only [TLB_eq]
  decide +kernel))

theorem top_gf2_true : TopOkB (ZMod 2) true := top_of_checks _ (by bin_tac) (by bin_tac)

theorem top_gf2_false : TopOkB (ZMod 2) false := top_of_checks _ (by bin_tac) (by bin_tac)

theorem top_gf2 (cb : Bool) : TopOkB (ZMod 2) cb := by
  cases cb
  exacts [top_gf2_false, top_gf2_true]

end Plonky3Lean.Proofs.Blake3Air.Binary

/-! ## The constraint count -/

namespace Plonky3Lean.Proofs.Blake3Air.Binary

open p3_air.symbolic.mirror p3_air.builder.mirror p3_air.air.mirror p3_blake3_air.mirror
open p3_blake3_air.mirror.binary Plonky3Lean.Proofs.Air Plonky3Lean.Proofs.KeccakAir

variable {F : Type} [Field F] [DecidableEq F]

theorem foldl_succ {α : Type} (l : List α) (s : ℕ) : l.foldl (fun s _ => s + 1) s = s + l.length := by
  induction l generalizing s with
  | nil => rfl
  | cons a l ih => rw [List.foldl_cons, ih]; simp; omega

theorem foldl_add {α : Type} (l : List α) (c s : ℕ) : l.foldl (fun s _ => s + c) s = s + c * l.length := by
  induction l generalizing s with
  | nil => simp
  | cons a l ih => rw [List.foldl_cons, ih]; simp; ring

section count

variable (L : AirLayout)

theorem count_add2 (s : ℕ) (x y z : ℕ → Unit) :
    binary.add2 (KeccakAir.Binary.countBuilder (F := F) L) s x y z = s + 32 := by
  simp only [binary.add2, KeccakAir.Binary.countBuilder, foldl_succ, List.length_range]

theorem count_add3 (s : ℕ) (x y z c w : ℕ → Unit) :
    binary.add3 (KeccakAir.Binary.countBuilder (F := F) L) s x y z c w = s + 63 := by
  unfold binary.add3
  rw [count_add2]
  simp only [KeccakAir.Binary.countBuilder, foldl_succ, List.length_range]

theorem count_g_step (loc : ℕ → Unit) (r g : ℕ) (s : ℕ) (x : State Unit) :
    (g_step (KeccakAir.Binary.countBuilder (F := F) L) loc r g (s, x)).1 = s + 190 := by
  simp only [g_step, eval_g, count_add2, count_add3]

theorem count_rounds (loc : ℕ → Unit) (s : ℕ) (x : State Unit) :
    (rounds (KeccakAir.Binary.countBuilder (F := F) L) loc (s, x)).1 = s + 10640 := by
  have h : ∀ (l : List ℕ) (r : ℕ) (acc : ℕ × State Unit), (l.foldl (fun acc g =>
      g_step (KeccakAir.Binary.countBuilder (F := F) L) loc r g acc) acc).1 = acc.1 + 190 * l.length := by
    intro l r
    induction l with
    | nil => intro acc; simp
    | cons g l ih =>
      intro acc
      rw [List.foldl_cons, ih, show acc = (acc.1, acc.2) from rfl, count_g_step]
      simp; ring
  have h' : ∀ (l : List ℕ) (acc : ℕ × State Unit), (l.foldl (fun acc r => (List.range G_PER_ROUND).foldl
      (fun acc g => g_step (KeccakAir.Binary.countBuilder (F := F) L) loc r g acc) acc) acc).1 =
      acc.1 + 1520 * l.length := by
    intro l
    induction l with
    | nil => intro acc; simp
    | cons r l ih =>
      intro acc
      rw [List.foldl_cons, ih, h]
      simp [G_PER_ROUND]; ring
  simp only [rounds, h', NUM_ROUNDS, List.length_range]

end count

/-- The AIR asserts exactly the number of constraints it reports, in every field, with or without the booleanity. -/
theorem num_constraints_eq (cb : Bool) :
    some ((binaryAir (F := F) cb).eval
        (symbolicBuilder (AirLayout.from_air (binaryAir (F := F) cb))) []).length =
      binary.num_constraints cb := by
  rw [KeccakAir.Binary.length_constraints (F := F)]
  simp only [binaryAir]
  unfold binary.eval
  rw [count_rounds]
  cases cb
  · simp [binary.num_constraints, NUM_G_CONSTRAINTS, CONSTRAINTS_PER_G, NUM_ROUNDS, G_PER_ROUND]
  · simp only [ite_true, binary.assert_inputs, AirBuilder.assert_bools, AirBuilder.assert_zeros,
      KeccakAir.Binary.countBuilder, foldl_succ, List.length_map, List.length_range, foldl_add]
    simp [binary.num_constraints, NUM_INPUT_BITS, NUM_INPUT_WORDS, NUM_G_CONSTRAINTS, CONSTRAINTS_PER_G,
      NUM_ROUNDS, G_PER_ROUND]

end Plonky3Lean.Proofs.Blake3Air.Binary
