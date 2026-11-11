module

public import Plonky3Lean.Proofs.Blake3Air.Parametric
public import Plonky3Lean.Proofs.KeccakAir.Row

@[expose] public section

/-!
# The constraints of one row of the prime-field BLAKE3 AIR

The row builder evaluates the AIR at one row and conjoins what it asserts.

On a parametric AIR, a trace satisfies the constraints exactly when that conjunction holds on every row.

Here the conjunction is written out step by step.
-/

set_option linter.unusedSectionVars false

namespace Plonky3Lean.Proofs.Blake3Air

open p3_air.builder.mirror p3_air.air.mirror p3_blake3_air.mirror Plonky3Lean.Spec.Air
open Plonky3Lean.Proofs.Air Plonky3Lean.Proofs.KeccakAir

variable {F : Type} [Field F]

/-! ## The word helpers, as equations -/

/-- The constraints of a = b + c + d mod 2^32 on limbs.

The difference is 0, -2^32 or -2^33, and its low limb part is 0, -2^16 or -2^17. -/
def Add3C (a b c d : ℕ → F) : Prop :=
  ((a 0 - b 0 - c 0 - d 0 + (a 1 - b 1 - c 1 - d 1) * 2 ^ 16 = 0 ∨
      a 0 - b 0 - c 0 - d 0 + (a 1 - b 1 - c 1 - d 1) * 2 ^ 16 + 65536 * 65536 = 0) ∨
    a 0 - b 0 - c 0 - d 0 + (a 1 - b 1 - c 1 - d 1) * 2 ^ 16 + (65536 * 65536 + 65536 * 65536) = 0) ∧
  ((a 0 - b 0 - c 0 - d 0 = 0 ∨ a 0 - b 0 - c 0 - d 0 + 65536 = 0) ∨
    a 0 - b 0 - c 0 - d 0 + (65536 + 65536) = 0)

/-- The constraints of a = b + c mod 2^32 on limbs. -/
def Add2C (a b c : ℕ → F) : Prop :=
  (a 0 - b 0 - c 0 + (a 1 - b 1 - c 1) * 2 ^ 16 = 0 ∨
      a 0 - b 0 - c 0 + (a 1 - b 1 - c 1) * 2 ^ 16 + 65536 * 65536 = 0) ∧
    (a 0 - b 0 - c 0 = 0 ∨ a 0 - b 0 - c 0 + 65536 = 0)

/-- The constraints of a = b xor (c <<< shift), with c boolean. -/
def XorC (a b c : ℕ → F) (shift : ℕ) : Prop :=
  (∀ k < 32, c k * (c k - 1) = 0) ∧
    a 0 - pack_bits_le fieldOps ((List.range 16).map fun i =>
      p3_keccak_air.mirror.xor fieldOps (b i) (c ((32 + i - shift) % 32))) = 0 ∧
    a 1 - pack_bits_le fieldOps ((List.range 16).map fun i =>
      p3_keccak_air.mirror.xor fieldOps (b (16 + i)) (c ((32 + (i + 16) - shift) % 32))) = 0

/-- The two limbs of a word given as bits. -/
def limbs (bits : ℕ → F) : ℕ → F := fun l => if l = 0 then low16 fieldOps bits else high16 fieldOps bits

/-- The constraints of a quarter round. -/
structure QRC (t : QuarterRound F F) : Prop where
  add1 : Add3C t.a_prime t.a (limbs t.b) t.m_two_i
  xor1 : XorC t.a_prime t.d t.d_prime 16
  add2 : Add2C t.c_prime t.c (limbs t.d_prime)
  xor2 : XorC t.c_prime t.b t.b_prime 12
  add3 : Add3C t.a_output t.a_prime (limbs t.b_prime) t.m_two_i_plus_one
  xor3 : XorC t.a_output t.d_prime t.d_output 8
  add4 : Add2C t.c_output t.c_prime (limbs t.d_output)
  xor4 : XorC t.c_output t.b_prime t.b_output 7

section ops

variable (env : Var → F) (L : AirLayout) (s : Prop)

theorem pb_ops : (propBuilder env L).toExprOps = fieldOps := rfl

theorem fo_sub (a b : F) : fieldOps.sub a b = a - b := rfl
theorem fo_add (a b : F) : fieldOps.add a b = a + b := rfl
theorem fo_mul (a b : F) : fieldOps.mul a b = a * b := rfl

theorem prop_add3 (a b c d : ℕ → F) : add3 (propBuilder env L) s a b c d = (s ∧ Add3C a b c d) := by
  simp [add3, Add3C, AirBuilder.assert_zeros, mul_2exp, propBuilder, and_assoc]

theorem prop_add2 (a b c : ℕ → F) : add2 (propBuilder env L) s a b c = (s ∧ Add2C a b c) := by
  simp [add2, Add2C, AirBuilder.assert_zeros, mul_2exp, propBuilder, and_assoc]

theorem prop_xor (a b c : ℕ → F) (shift : ℕ) :
    xor_32_shift (propBuilder env L) s a b c shift = (s ∧ XorC a b c shift) := by
  simp [xor_32_shift, XorC, AirBuilder.assert_zeros, AirBuilder.assert_bools, AirBuilder.bool_check,
    propBuilder, foldl_and, and_assoc, fieldOps]

theorem prop_quarter_round (t : QuarterRound F F) :
    quarter_round_function (propBuilder env L) s t = (s ∧ QRC t) := by
  simp only [quarter_round_function, prop_add3, prop_add2, prop_xor, pb_ops]
  apply propext
  constructor
  · rintro ⟨⟨⟨⟨⟨⟨⟨⟨hs, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩
    exact ⟨hs, h1, h2, h3, h4, h5, h6, h7, h8⟩
  · rintro ⟨hs, h1, h2, h3, h4, h5, h6, h7, h8⟩
    exact ⟨⟨⟨⟨⟨⟨⟨⟨hs, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩

theorem prop_verify_round (input : Blake3State F) (rd : FullRound F) (m : ℕ → ℕ → F) :
    verify_round (propBuilder env L) s input rd m =
      ((s ∧ ∀ i ∈ List.range 4, QRC (full_round_to_column_quarter_round input rd m i)) ∧
        ∀ i ∈ List.range 4, QRC (full_round_to_diagonal_quarter_round rd m i)) := by
  simp only [verify_round, prop_quarter_round, foldl_and]

variable (loc : ℕ → F)

theorem prop_inputs : assert_inputs (propBuilder env L) loc s =
    (s ∧ ∀ elem ∈ (List.range 16).map (fun i k => loc (col.inputs i k)) ++
      (List.range 4).map (fun j k => loc (col.chaining_values 0 j k)) ++
      (List.range 4).map (fun j k => loc (col.chaining_values 1 j k)) ++
      (List.range 4).map (initial_row_3 loc), ∀ k ∈ List.range 32, elem k * (elem k - 1) = 0) := by
  simp only [assert_inputs, AirBuilder.assert_bool, AirBuilder.bool_check, pb_assert_zero, pb_mul,
    pb_sub, pb_const, foldl_and]

theorem prop_row0 : assert_initial_row0 (propBuilder env L) loc s =
    (s ∧ ∀ j ∈ List.range 4,
      low16 fieldOps (fun k => loc (col.chaining_values 0 j k)) - loc (col.initial_row0 j 0) = 0 ∧
      high16 fieldOps (fun k => loc (col.chaining_values 0 j k)) - loc (col.initial_row0 j 1) = 0) := by
  simp only [assert_initial_row0, AirBuilder.assert_eq, pb_assert_zero, pb_ops, fo_sub, and_assoc,
    foldl_and]

theorem prop_row2 : assert_initial_row2 (propBuilder env L) loc s =
    (s ∧ ∀ j ∈ List.range 4, loc (col.initial_row2 j 0) - (ivHalf j 0 : F) = 0 ∧
      loc (col.initial_row2 j 1) - (ivHalf j 1 : F) = 0) := by
  simp only [assert_initial_row2, AirBuilder.assert_eq, pb_assert_zero, pb_sub, pb_const, and_assoc,
    foldl_and]

theorem prop_rounds : verify_rounds (propBuilder env L) loc s =
    (s ∧ ∀ r ∈ List.range 7,
      (∀ i ∈ List.range 4, QRC (full_round_to_column_quarter_round (round_input loc r)
        (fullRoundAt loc r) (permute^[r] (m_values (propBuilder env L) loc)) i)) ∧
      ∀ i ∈ List.range 4, QRC (full_round_to_diagonal_quarter_round (fullRoundAt loc r)
        (permute^[r] (m_values (propBuilder env L) loc)) i)) := by
  simp only [verify_rounds, prop_verify_round, and_assoc, foldl_and]

theorem prop_helpers : assert_helpers (propBuilder env L) loc s =
    (s ∧ ∀ j ∈ List.range 4,
      low16 fieldOps (fun k => loc (col.final_round_helpers j k)) - (final loc).row2 j 0 = 0 ∧
      high16 fieldOps (fun k => loc (col.final_round_helpers j k)) - (final loc).row2 j 1 = 0) := by
  simp only [assert_helpers, AirBuilder.assert_eq, pb_assert_zero, pb_ops, fo_sub, and_assoc, foldl_and]

theorem prop_outputs_bool : assert_outputs_bool (propBuilder env L) loc s =
    (s ∧ ∀ j ∈ List.range 4, ∀ k ∈ List.range 32,
      loc (col.outputs 0 j k) * (loc (col.outputs 0 j k) - 1) = 0) := by
  simp only [assert_outputs_bool, AirBuilder.assert_bool, AirBuilder.bool_check, pb_assert_zero,
    pb_mul, pb_sub, pb_const, foldl_and]

theorem prop_output_row0 : assert_output_row0 (propBuilder env L) loc s =
    (s ∧ ∀ j ∈ List.range 4, XorC ((final loc).row0 j) (fun k => loc (col.outputs 0 j k))
      (fun k => loc (col.final_round_helpers j k)) 0) := by
  simp only [assert_output_row0, prop_xor, foldl_and]

theorem prop_output_xor (q : ℕ) (x y : ℕ → ℕ → F) : assert_output_xor (propBuilder env L) loc q x y s =
    (s ∧ ∀ j ∈ List.range 4, ∀ k ∈ List.range 32,
      loc (col.outputs q j k) - p3_keccak_air.mirror.xor fieldOps (x j k) (y j k) = 0) := by
  simp only [assert_output_xor, AirBuilder.assert_eq, pb_assert_zero, pb_ops, fo_sub, foldl_and]

theorem m_values_pb : m_values (propBuilder env L) loc = fun i => limbs fun k => loc (col.inputs i k) :=
  rfl

end ops

/-- The constraints of the prime-field BLAKE3 AIR on one row. -/
structure RowSpec (loc : ℕ → F) : Prop where
  inputs : ∀ elem ∈ (List.range 16).map (fun i k => loc (col.inputs i k)) ++
      (List.range 4).map (fun j k => loc (col.chaining_values 0 j k)) ++
      (List.range 4).map (fun j k => loc (col.chaining_values 1 j k)) ++
      (List.range 4).map (initial_row_3 loc), ∀ k ∈ List.range 32, elem k * (elem k - 1) = 0
  row0 : ∀ j ∈ List.range 4,
    low16 fieldOps (fun k => loc (col.chaining_values 0 j k)) - loc (col.initial_row0 j 0) = 0 ∧
    high16 fieldOps (fun k => loc (col.chaining_values 0 j k)) - loc (col.initial_row0 j 1) = 0
  row2 : ∀ j ∈ List.range 4, loc (col.initial_row2 j 0) - (ivHalf j 0 : F) = 0 ∧
    loc (col.initial_row2 j 1) - (ivHalf j 1 : F) = 0
  rounds : ∀ r ∈ List.range 7,
    (∀ i ∈ List.range 4, QRC (full_round_to_column_quarter_round (round_input loc r)
      (fullRoundAt loc r) (permute^[r] fun i => limbs fun k => loc (col.inputs i k)) i)) ∧
    ∀ i ∈ List.range 4, QRC (full_round_to_diagonal_quarter_round (fullRoundAt loc r)
      (permute^[r] fun i => limbs fun k => loc (col.inputs i k)) i)
  helpers : ∀ j ∈ List.range 4,
    low16 fieldOps (fun k => loc (col.final_round_helpers j k)) - (final loc).row2 j 0 = 0 ∧
    high16 fieldOps (fun k => loc (col.final_round_helpers j k)) - (final loc).row2 j 1 = 0
  outputs_bool : ∀ j ∈ List.range 4, ∀ k ∈ List.range 32,
    loc (col.outputs 0 j k) * (loc (col.outputs 0 j k) - 1) = 0
  output_row0 : ∀ j ∈ List.range 4, XorC ((final loc).row0 j) (fun k => loc (col.outputs 0 j k))
    (fun k => loc (col.final_round_helpers j k)) 0
  output1 : ∀ j ∈ List.range 4, ∀ k ∈ List.range 32,
    loc (col.outputs 1 j k) - p3_keccak_air.mirror.xor fieldOps ((final loc).row1 j k) ((final loc).row3 j k) = 0
  output2 : ∀ j ∈ List.range 4, ∀ k ∈ List.range 32,
    loc (col.outputs 2 j k) - p3_keccak_air.mirror.xor fieldOps (loc (col.chaining_values 0 j k))
      (loc (col.final_round_helpers j k)) = 0
  output3 : ∀ j ∈ List.range 4, ∀ k ∈ List.range 32,
    loc (col.outputs 3 j k) - p3_keccak_air.mirror.xor fieldOps (loc (col.chaining_values 1 j k))
      ((final loc).row3 j k) = 0

/-- The row builder accepts a row exactly when its row constraints hold. -/
theorem eval_iff (env : Var → F) (L : AirLayout) :
    eval (propBuilder env L) True ↔ RowSpec (rowOf env L 0) := by
  simp only [eval, prop_inputs, prop_row0, prop_row2, prop_rounds, prop_helpers, prop_outputs_bool,
    prop_output_row0, prop_output_xor, m_values_pb, pb_current, pb_const, true_and]
  constructor
  · rintro ⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩
    exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  · rintro ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
    exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩

end Plonky3Lean.Proofs.Blake3Air
