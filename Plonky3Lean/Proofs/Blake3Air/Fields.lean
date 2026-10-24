module

public import Plonky3Lean.Proofs.Blake3Air.Degree
public import CompPoly.Fields.BabyBear.Basic
public import CompPoly.Fields.KoalaBear.Basic
public import CompPoly.Fields.Goldilocks.Basic
public import CompPoly.Fields.Mersenne31.Basic

@[expose] public section

/-!
# The prime-field BLAKE3 AIR at BabyBear, KoalaBear, Goldilocks and Mersenne31

Over each field, the bounding builder accepts the AIR.

So its constraint degrees are at most 3, and no constraint reads a selector.

The run is checked step by step, from the input booleanity to the output checks.

Each of the four fields has characteristic above 3 * 2^16, which soundness needs.
-/

set_option linter.unusedSectionVars false

namespace Plonky3Lean.Proofs.Blake3Air

open p3_air.builder.mirror p3_air.air.mirror p3_blake3_air.mirror Plonky3Lean.Proofs.KeccakAir

variable {F : Type} [Field F] [DecidableEq F]

/-- The bounding builder accepts the prime-field AIR with the bound 3. -/
abbrev TopOk (F : Type) [Field F] : Prop :=
  (blake3Air (F := F)).eval (topBuilderD 3 (AirLayout.from_air (blake3Air (F := F)))) true = true

/-- The bounding builder of the prime-field AIR. -/
abbrev TB (F : Type) [Field F] : AirBuilder F (ℕ × ℕ) Bool :=
  topBuilderD 3 (AirLayout.from_air (blake3Air (F := F)))

/-- The row the bounding builder reads. -/
abbrev TL (F : Type) [Field F] : ℕ → ℕ × ℕ := fun i => ((TB F).main true).current.getD i ((TB F).const 0)

theorem foldl_lin_true {α : Type} {g : α → Bool → Bool} (l : List α) (hg : ∀ a ∈ l, Lin (g a))
    (ht : ∀ a ∈ l, g a true = true) (s : Bool) : l.foldl (fun s a => g a s) s = s := by
  induction l generalizing s with
  | nil => rfl
  | cons a l ih =>
    rw [List.foldl_cons, (hg a (by simp)).eq, ht a (by simp), Bool.and_true]
    exact ih (fun a h => hg a (by simp [h])) (fun a h => ht a (by simp [h])) s

section lin

theorem lin_round (r : ℕ) : Lin fun s => verify_round (TB F) s (round_input (TL F) r)
    (fullRoundAt (TL F) r) (permute^[r] (m_values (TB F) (TL F))) := fun b _ =>
  rel_verify_round (builderRel_and 3 _ b)
    (by unfold round_input; split_ifs <;> exact ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩)
    (fun _ => rfl) r (fun _ _ => rfl) rfl

theorem lin_inputs : Lin (assert_inputs (TB F) (TL F)) := fun b _ =>
  rel_assert_inputs (builderRel_and 3 _ b) (fun _ => rfl) rfl
theorem lin_row0 : Lin (assert_initial_row0 (TB F) (TL F)) := fun b _ =>
  rel_assert_initial_row0 (builderRel_and 3 _ b) (fun _ => rfl) rfl
theorem lin_row2 : Lin (assert_initial_row2 (TB F) (TL F)) := fun b _ =>
  rel_assert_initial_row2 (builderRel_and 3 _ b) (fun _ => rfl) rfl
theorem lin_rounds : Lin (verify_rounds (TB F) (TL F)) := fun b _ =>
  rel_verify_rounds (builderRel_and 3 _ b) (fun _ => rfl) rfl
theorem lin_helpers : Lin (assert_helpers (TB F) (TL F)) := fun b _ =>
  rel_assert_helpers (builderRel_and 3 _ b) (fun _ => rfl) rfl
theorem lin_outputs_bool : Lin (assert_outputs_bool (TB F) (TL F)) := fun b _ =>
  rel_assert_outputs_bool (builderRel_and 3 _ b) (fun _ => rfl) rfl
theorem lin_output_row0 : Lin (assert_output_row0 (TB F) (TL F)) := fun b _ =>
  rel_assert_output_row0 (builderRel_and 3 _ b) (fun _ => rfl) rfl
theorem lin_output_xor (q : ℕ) (x y : ℕ → ℕ → ℕ × ℕ) :
    Lin (assert_output_xor (TB F) (TL F) q x y) := fun b _ =>
  rel_assert_output_xor (builderRel_and 3 _ b) rfl q (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl)

/-- The bounding builder accepts the AIR when it accepts each step from true. -/
theorem top_of_steps
    (h1 : assert_inputs (TB F) (TL F) true = true)
    (h2 : assert_initial_row0 (TB F) (TL F) true = true)
    (h3 : assert_initial_row2 (TB F) (TL F) true = true)
    (hr : ∀ r ∈ List.range 7, verify_round (TB F) true (round_input (TL F) r) (fullRoundAt (TL F) r)
      (permute^[r] (m_values (TB F) (TL F))) = true)
    (h4 : assert_helpers (TB F) (TL F) true = true)
    (h5 : assert_outputs_bool (TB F) (TL F) true = true)
    (h6 : assert_output_row0 (TB F) (TL F) true = true)
    (h7 : assert_output_xor (TB F) (TL F) 1 (final (TL F)).row1 (final (TL F)).row3 true = true)
    (h8 : assert_output_xor (TB F) (TL F) 2 (fun j k => TL F (col.chaining_values 0 j k))
      (fun j k => TL F (col.final_round_helpers j k)) true = true)
    (h9 : assert_output_xor (TB F) (TL F) 3 (fun j k => TL F (col.chaining_values 1 j k))
      (final (TL F)).row3 true = true) :
    TopOk F := by
  have he : (blake3Air (F := F)).eval (TB F) true =
      assert_output_xor (TB F) (TL F) 3 (fun j k => TL F (col.chaining_values 1 j k)) (final (TL F)).row3
      (assert_output_xor (TB F) (TL F) 2 (fun j k => TL F (col.chaining_values 0 j k))
        (fun j k => TL F (col.final_round_helpers j k))
      (assert_output_xor (TB F) (TL F) 1 (final (TL F)).row1 (final (TL F)).row3
      (assert_output_row0 (TB F) (TL F) (assert_outputs_bool (TB F) (TL F) (assert_helpers (TB F) (TL F)
      (verify_rounds (TB F) (TL F) (assert_initial_row2 (TB F) (TL F) (assert_initial_row0 (TB F) (TL F)
      (assert_inputs (TB F) (TL F) true))))))))) := by simp only [blake3Air, eval]
  rw [TopOk, he, (lin_output_xor 3 _ _).eq, (lin_output_xor 2 _ _).eq, (lin_output_xor 1 _ _).eq,
    lin_output_row0.eq, lin_outputs_bool.eq, lin_helpers.eq, lin_rounds.eq, lin_row2.eq, lin_row0.eq,
    h1, h2, h3, h4, h5, h6, h7, h8, h9]
  simp only [verify_rounds, Bool.and_true, Bool.true_and]
  exact foldl_lin_true _ (fun r _ => lin_round r) hr true

end lin

/-- Unfold one step of the bounding builder's run to a closed computation and evaluate it. -/
macro "step_tac" : tactic => `(tactic| (
  simp only [TB, TL, assert_inputs, assert_initial_row0, assert_initial_row2, assert_helpers,
    assert_outputs_bool, assert_output_row0, assert_output_xor, verify_round, round_input,
    initial_state, initial_row_3, m_values, final, fullRoundAt, stateAt, topBuilderD,
    getD_map_range_const, AirLayout.from_air, blake3Air]
  decide +kernel))

namespace babyBear
theorem inputs : assert_inputs (TB BabyBear.Field) (TL BabyBear.Field) true = true := by step_tac
theorem row0 : assert_initial_row0 (TB BabyBear.Field) (TL BabyBear.Field) true = true := by step_tac
theorem row2 : assert_initial_row2 (TB BabyBear.Field) (TL BabyBear.Field) true = true := by step_tac
theorem helpers : assert_helpers (TB BabyBear.Field) (TL BabyBear.Field) true = true := by step_tac
theorem outputs_bool : assert_outputs_bool (TB BabyBear.Field) (TL BabyBear.Field) true = true := by step_tac
theorem output_row0 : assert_output_row0 (TB BabyBear.Field) (TL BabyBear.Field) true = true := by step_tac
theorem xor1 : assert_output_xor (TB BabyBear.Field) (TL BabyBear.Field) 1 (final (TL BabyBear.Field)).row1 (final (TL BabyBear.Field)).row3 true = true := by step_tac
theorem xor2 : assert_output_xor (TB BabyBear.Field) (TL BabyBear.Field) 2 (fun j k => (TL BabyBear.Field) (col.chaining_values 0 j k))
    (fun j k => (TL BabyBear.Field) (col.final_round_helpers j k)) true = true := by step_tac
theorem xor3 : assert_output_xor (TB BabyBear.Field) (TL BabyBear.Field) 3 (fun j k => (TL BabyBear.Field) (col.chaining_values 1 j k)) (final (TL BabyBear.Field)).row3 true = true := by step_tac
theorem round0 : verify_round (TB BabyBear.Field) true (round_input (TL BabyBear.Field) 0) (fullRoundAt (TL BabyBear.Field) 0)
    (permute^[0] (m_values (TB BabyBear.Field) (TL BabyBear.Field))) = true := by step_tac
theorem round1 : verify_round (TB BabyBear.Field) true (round_input (TL BabyBear.Field) 1) (fullRoundAt (TL BabyBear.Field) 1)
    (permute^[1] (m_values (TB BabyBear.Field) (TL BabyBear.Field))) = true := by step_tac
theorem round2 : verify_round (TB BabyBear.Field) true (round_input (TL BabyBear.Field) 2) (fullRoundAt (TL BabyBear.Field) 2)
    (permute^[2] (m_values (TB BabyBear.Field) (TL BabyBear.Field))) = true := by step_tac
theorem round3 : verify_round (TB BabyBear.Field) true (round_input (TL BabyBear.Field) 3) (fullRoundAt (TL BabyBear.Field) 3)
    (permute^[3] (m_values (TB BabyBear.Field) (TL BabyBear.Field))) = true := by step_tac
theorem round4 : verify_round (TB BabyBear.Field) true (round_input (TL BabyBear.Field) 4) (fullRoundAt (TL BabyBear.Field) 4)
    (permute^[4] (m_values (TB BabyBear.Field) (TL BabyBear.Field))) = true := by step_tac
theorem round5 : verify_round (TB BabyBear.Field) true (round_input (TL BabyBear.Field) 5) (fullRoundAt (TL BabyBear.Field) 5)
    (permute^[5] (m_values (TB BabyBear.Field) (TL BabyBear.Field))) = true := by step_tac
theorem round6 : verify_round (TB BabyBear.Field) true (round_input (TL BabyBear.Field) 6) (fullRoundAt (TL BabyBear.Field) 6)
    (permute^[6] (m_values (TB BabyBear.Field) (TL BabyBear.Field))) = true := by step_tac
theorem round (r : ℕ) (hr : r < 7) : verify_round (TB BabyBear.Field) true (round_input (TL BabyBear.Field) r) (fullRoundAt (TL BabyBear.Field) r)
    (permute^[r] (m_values (TB BabyBear.Field) (TL BabyBear.Field))) = true := by
  interval_cases r
  exacts [round0, round1, round2, round3, round4, round5, round6]

end babyBear

theorem top_babyBear : TopOk BabyBear.Field :=
  top_of_steps babyBear.inputs babyBear.row0 babyBear.row2 (fun r hr => babyBear.round r (List.mem_range.mp hr))
    babyBear.helpers babyBear.outputs_bool babyBear.output_row0 babyBear.xor1 babyBear.xor2 babyBear.xor3

namespace koalaBear
theorem inputs : assert_inputs (TB KoalaBear.Field) (TL KoalaBear.Field) true = true := by step_tac
theorem row0 : assert_initial_row0 (TB KoalaBear.Field) (TL KoalaBear.Field) true = true := by step_tac
theorem row2 : assert_initial_row2 (TB KoalaBear.Field) (TL KoalaBear.Field) true = true := by step_tac
theorem helpers : assert_helpers (TB KoalaBear.Field) (TL KoalaBear.Field) true = true := by step_tac
theorem outputs_bool : assert_outputs_bool (TB KoalaBear.Field) (TL KoalaBear.Field) true = true := by step_tac
theorem output_row0 : assert_output_row0 (TB KoalaBear.Field) (TL KoalaBear.Field) true = true := by step_tac
theorem xor1 : assert_output_xor (TB KoalaBear.Field) (TL KoalaBear.Field) 1 (final (TL KoalaBear.Field)).row1 (final (TL KoalaBear.Field)).row3 true = true := by step_tac
theorem xor2 : assert_output_xor (TB KoalaBear.Field) (TL KoalaBear.Field) 2 (fun j k => (TL KoalaBear.Field) (col.chaining_values 0 j k))
    (fun j k => (TL KoalaBear.Field) (col.final_round_helpers j k)) true = true := by step_tac
theorem xor3 : assert_output_xor (TB KoalaBear.Field) (TL KoalaBear.Field) 3 (fun j k => (TL KoalaBear.Field) (col.chaining_values 1 j k)) (final (TL KoalaBear.Field)).row3 true = true := by step_tac
theorem round0 : verify_round (TB KoalaBear.Field) true (round_input (TL KoalaBear.Field) 0) (fullRoundAt (TL KoalaBear.Field) 0)
    (permute^[0] (m_values (TB KoalaBear.Field) (TL KoalaBear.Field))) = true := by step_tac
theorem round1 : verify_round (TB KoalaBear.Field) true (round_input (TL KoalaBear.Field) 1) (fullRoundAt (TL KoalaBear.Field) 1)
    (permute^[1] (m_values (TB KoalaBear.Field) (TL KoalaBear.Field))) = true := by step_tac
theorem round2 : verify_round (TB KoalaBear.Field) true (round_input (TL KoalaBear.Field) 2) (fullRoundAt (TL KoalaBear.Field) 2)
    (permute^[2] (m_values (TB KoalaBear.Field) (TL KoalaBear.Field))) = true := by step_tac
theorem round3 : verify_round (TB KoalaBear.Field) true (round_input (TL KoalaBear.Field) 3) (fullRoundAt (TL KoalaBear.Field) 3)
    (permute^[3] (m_values (TB KoalaBear.Field) (TL KoalaBear.Field))) = true := by step_tac
theorem round4 : verify_round (TB KoalaBear.Field) true (round_input (TL KoalaBear.Field) 4) (fullRoundAt (TL KoalaBear.Field) 4)
    (permute^[4] (m_values (TB KoalaBear.Field) (TL KoalaBear.Field))) = true := by step_tac
theorem round5 : verify_round (TB KoalaBear.Field) true (round_input (TL KoalaBear.Field) 5) (fullRoundAt (TL KoalaBear.Field) 5)
    (permute^[5] (m_values (TB KoalaBear.Field) (TL KoalaBear.Field))) = true := by step_tac
theorem round6 : verify_round (TB KoalaBear.Field) true (round_input (TL KoalaBear.Field) 6) (fullRoundAt (TL KoalaBear.Field) 6)
    (permute^[6] (m_values (TB KoalaBear.Field) (TL KoalaBear.Field))) = true := by step_tac
theorem round (r : ℕ) (hr : r < 7) : verify_round (TB KoalaBear.Field) true (round_input (TL KoalaBear.Field) r) (fullRoundAt (TL KoalaBear.Field) r)
    (permute^[r] (m_values (TB KoalaBear.Field) (TL KoalaBear.Field))) = true := by
  interval_cases r
  exacts [round0, round1, round2, round3, round4, round5, round6]

end koalaBear

theorem top_koalaBear : TopOk KoalaBear.Field :=
  top_of_steps koalaBear.inputs koalaBear.row0 koalaBear.row2 (fun r hr => koalaBear.round r (List.mem_range.mp hr))
    koalaBear.helpers koalaBear.outputs_bool koalaBear.output_row0 koalaBear.xor1 koalaBear.xor2 koalaBear.xor3

namespace goldilocks
theorem inputs : assert_inputs (TB Goldilocks.Field) (TL Goldilocks.Field) true = true := by step_tac
theorem row0 : assert_initial_row0 (TB Goldilocks.Field) (TL Goldilocks.Field) true = true := by step_tac
theorem row2 : assert_initial_row2 (TB Goldilocks.Field) (TL Goldilocks.Field) true = true := by step_tac
theorem helpers : assert_helpers (TB Goldilocks.Field) (TL Goldilocks.Field) true = true := by step_tac
theorem outputs_bool : assert_outputs_bool (TB Goldilocks.Field) (TL Goldilocks.Field) true = true := by step_tac
theorem output_row0 : assert_output_row0 (TB Goldilocks.Field) (TL Goldilocks.Field) true = true := by step_tac
theorem xor1 : assert_output_xor (TB Goldilocks.Field) (TL Goldilocks.Field) 1 (final (TL Goldilocks.Field)).row1 (final (TL Goldilocks.Field)).row3 true = true := by step_tac
theorem xor2 : assert_output_xor (TB Goldilocks.Field) (TL Goldilocks.Field) 2 (fun j k => (TL Goldilocks.Field) (col.chaining_values 0 j k))
    (fun j k => (TL Goldilocks.Field) (col.final_round_helpers j k)) true = true := by step_tac
theorem xor3 : assert_output_xor (TB Goldilocks.Field) (TL Goldilocks.Field) 3 (fun j k => (TL Goldilocks.Field) (col.chaining_values 1 j k)) (final (TL Goldilocks.Field)).row3 true = true := by step_tac
theorem round0 : verify_round (TB Goldilocks.Field) true (round_input (TL Goldilocks.Field) 0) (fullRoundAt (TL Goldilocks.Field) 0)
    (permute^[0] (m_values (TB Goldilocks.Field) (TL Goldilocks.Field))) = true := by step_tac
theorem round1 : verify_round (TB Goldilocks.Field) true (round_input (TL Goldilocks.Field) 1) (fullRoundAt (TL Goldilocks.Field) 1)
    (permute^[1] (m_values (TB Goldilocks.Field) (TL Goldilocks.Field))) = true := by step_tac
theorem round2 : verify_round (TB Goldilocks.Field) true (round_input (TL Goldilocks.Field) 2) (fullRoundAt (TL Goldilocks.Field) 2)
    (permute^[2] (m_values (TB Goldilocks.Field) (TL Goldilocks.Field))) = true := by step_tac
theorem round3 : verify_round (TB Goldilocks.Field) true (round_input (TL Goldilocks.Field) 3) (fullRoundAt (TL Goldilocks.Field) 3)
    (permute^[3] (m_values (TB Goldilocks.Field) (TL Goldilocks.Field))) = true := by step_tac
theorem round4 : verify_round (TB Goldilocks.Field) true (round_input (TL Goldilocks.Field) 4) (fullRoundAt (TL Goldilocks.Field) 4)
    (permute^[4] (m_values (TB Goldilocks.Field) (TL Goldilocks.Field))) = true := by step_tac
theorem round5 : verify_round (TB Goldilocks.Field) true (round_input (TL Goldilocks.Field) 5) (fullRoundAt (TL Goldilocks.Field) 5)
    (permute^[5] (m_values (TB Goldilocks.Field) (TL Goldilocks.Field))) = true := by step_tac
theorem round6 : verify_round (TB Goldilocks.Field) true (round_input (TL Goldilocks.Field) 6) (fullRoundAt (TL Goldilocks.Field) 6)
    (permute^[6] (m_values (TB Goldilocks.Field) (TL Goldilocks.Field))) = true := by step_tac
theorem round (r : ℕ) (hr : r < 7) : verify_round (TB Goldilocks.Field) true (round_input (TL Goldilocks.Field) r) (fullRoundAt (TL Goldilocks.Field) r)
    (permute^[r] (m_values (TB Goldilocks.Field) (TL Goldilocks.Field))) = true := by
  interval_cases r
  exacts [round0, round1, round2, round3, round4, round5, round6]

end goldilocks

theorem top_goldilocks : TopOk Goldilocks.Field :=
  top_of_steps goldilocks.inputs goldilocks.row0 goldilocks.row2 (fun r hr => goldilocks.round r (List.mem_range.mp hr))
    goldilocks.helpers goldilocks.outputs_bool goldilocks.output_row0 goldilocks.xor1 goldilocks.xor2 goldilocks.xor3

namespace mersenne31
theorem inputs : assert_inputs (TB Mersenne31.Field) (TL Mersenne31.Field) true = true := by step_tac
theorem row0 : assert_initial_row0 (TB Mersenne31.Field) (TL Mersenne31.Field) true = true := by step_tac
theorem row2 : assert_initial_row2 (TB Mersenne31.Field) (TL Mersenne31.Field) true = true := by step_tac
theorem helpers : assert_helpers (TB Mersenne31.Field) (TL Mersenne31.Field) true = true := by step_tac
theorem outputs_bool : assert_outputs_bool (TB Mersenne31.Field) (TL Mersenne31.Field) true = true := by step_tac
theorem output_row0 : assert_output_row0 (TB Mersenne31.Field) (TL Mersenne31.Field) true = true := by step_tac
theorem xor1 : assert_output_xor (TB Mersenne31.Field) (TL Mersenne31.Field) 1 (final (TL Mersenne31.Field)).row1 (final (TL Mersenne31.Field)).row3 true = true := by step_tac
theorem xor2 : assert_output_xor (TB Mersenne31.Field) (TL Mersenne31.Field) 2 (fun j k => (TL Mersenne31.Field) (col.chaining_values 0 j k))
    (fun j k => (TL Mersenne31.Field) (col.final_round_helpers j k)) true = true := by step_tac
theorem xor3 : assert_output_xor (TB Mersenne31.Field) (TL Mersenne31.Field) 3 (fun j k => (TL Mersenne31.Field) (col.chaining_values 1 j k)) (final (TL Mersenne31.Field)).row3 true = true := by step_tac
theorem round0 : verify_round (TB Mersenne31.Field) true (round_input (TL Mersenne31.Field) 0) (fullRoundAt (TL Mersenne31.Field) 0)
    (permute^[0] (m_values (TB Mersenne31.Field) (TL Mersenne31.Field))) = true := by step_tac
theorem round1 : verify_round (TB Mersenne31.Field) true (round_input (TL Mersenne31.Field) 1) (fullRoundAt (TL Mersenne31.Field) 1)
    (permute^[1] (m_values (TB Mersenne31.Field) (TL Mersenne31.Field))) = true := by step_tac
theorem round2 : verify_round (TB Mersenne31.Field) true (round_input (TL Mersenne31.Field) 2) (fullRoundAt (TL Mersenne31.Field) 2)
    (permute^[2] (m_values (TB Mersenne31.Field) (TL Mersenne31.Field))) = true := by step_tac
theorem round3 : verify_round (TB Mersenne31.Field) true (round_input (TL Mersenne31.Field) 3) (fullRoundAt (TL Mersenne31.Field) 3)
    (permute^[3] (m_values (TB Mersenne31.Field) (TL Mersenne31.Field))) = true := by step_tac
theorem round4 : verify_round (TB Mersenne31.Field) true (round_input (TL Mersenne31.Field) 4) (fullRoundAt (TL Mersenne31.Field) 4)
    (permute^[4] (m_values (TB Mersenne31.Field) (TL Mersenne31.Field))) = true := by step_tac
theorem round5 : verify_round (TB Mersenne31.Field) true (round_input (TL Mersenne31.Field) 5) (fullRoundAt (TL Mersenne31.Field) 5)
    (permute^[5] (m_values (TB Mersenne31.Field) (TL Mersenne31.Field))) = true := by step_tac
theorem round6 : verify_round (TB Mersenne31.Field) true (round_input (TL Mersenne31.Field) 6) (fullRoundAt (TL Mersenne31.Field) 6)
    (permute^[6] (m_values (TB Mersenne31.Field) (TL Mersenne31.Field))) = true := by step_tac
theorem round (r : ℕ) (hr : r < 7) : verify_round (TB Mersenne31.Field) true (round_input (TL Mersenne31.Field) r) (fullRoundAt (TL Mersenne31.Field) r)
    (permute^[r] (m_values (TB Mersenne31.Field) (TL Mersenne31.Field))) = true := by
  interval_cases r
  exacts [round0, round1, round2, round3, round4, round5, round6]

end mersenne31

theorem top_mersenne31 : TopOk Mersenne31.Field :=
  top_of_steps mersenne31.inputs mersenne31.row0 mersenne31.row2 (fun r hr => mersenne31.round r (List.mem_range.mp hr))
    mersenne31.helpers mersenne31.outputs_bool mersenne31.output_row0 mersenne31.xor1 mersenne31.xor2 mersenne31.xor3

theorem ringChar_babyBear : 3 * 2 ^ 16 < ringChar BabyBear.Field := by
  rw [ZMod.ringChar_zmod_n]; decide

theorem ringChar_koalaBear : 3 * 2 ^ 16 < ringChar KoalaBear.Field := by
  rw [ZMod.ringChar_zmod_n]; decide

theorem ringChar_goldilocks : 3 * 2 ^ 16 < ringChar Goldilocks.Field := by
  rw [ZMod.ringChar_zmod_n]; decide

theorem ringChar_mersenne31 : 3 * 2 ^ 16 < ringChar Mersenne31.Field := by
  rw [ZMod.ringChar_zmod_n]; decide

end Plonky3Lean.Proofs.Blake3Air
