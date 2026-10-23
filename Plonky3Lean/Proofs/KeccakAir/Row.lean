module

public import Plonky3Lean.Proofs.KeccakAir.Parametric
public import Plonky3Lean.Spec.Air

@[expose] public section

/-!
# The constraints of one row

A builder can evaluate an AIR at one row and conjoin what it asserts.

On a parametric AIR, a trace satisfies the constraint polynomials exactly when that conjunction holds on every row.

For the Keccak-f AIR, the conjunction is written out loop by loop.
-/

set_option linter.unusedSectionVars false

namespace Plonky3Lean.Proofs.KeccakAir

open p3_air.builder.mirror p3_air.air.mirror p3_keccak_air.mirror Plonky3Lean.Spec.Air
open Plonky3Lean.Proofs.Air

variable {F : Type} [Field F]

/-- The builder of one row: the values of the variables, and the conjunction of the assertions. -/
def propBuilder (env : Var → F) (layout : AirLayout) : AirBuilder F F Prop where
  add := (· + ·)
  sub := (· - ·)
  mul := (· * ·)
  neg := (- ·)
  const := id
  main _ := ⟨(List.range layout.main_width).map (env <| .main 0 ·),
    (List.range layout.main_width).map (env <| .main 1 ·)⟩
  preprocessed _ := ⟨(List.range layout.preprocessed_width).map (env <| .prep 0 ·),
    (List.range layout.preprocessed_width).map (env <| .prep 1 ·)⟩
  is_first_row _ := env .isFirstRow
  is_last_row _ := env .isLastRow
  is_transition _ := env .isTransition
  assert_zero s x := s ∧ x = 0
  public_values _ := (List.range layout.num_public_values).map (env <| .pub ·)
  periodic_values _ := (List.range layout.num_periodic_columns).map (env <| .periodic ·)

theorem forall₂_map_same {α β γ : Type _} {R : β → γ → Prop} {f : α → β} {g : α → γ} (l : List α)
    (h : ∀ x, R (f x) (g x)) : List.Forall₂ R (l.map f) (l.map g) :=
  Plonky3Lean.Proofs.Air.forall₂_map_map fun x _ => h x

/-- The polynomial builder and the row builder are related by evaluation. -/
theorem builderRel_poly_prop (env : Var → F) (layout : AirLayout) :
    BuilderRel (polyBuilder layout) (propBuilder env layout)
      (fun p v => MvPolynomial.eval env p = v)
      (fun ps P => P ↔ ∀ c ∈ ps, MvPolynomial.eval env c = 0) where
  add h h' := by subst h h'; simp [polyBuilder, propBuilder]
  sub h h' := by subst h h'; simp [polyBuilder, propBuilder]
  mul h h' := by subst h h'; simp [polyBuilder, propBuilder]
  neg h := by subst h; simp [polyBuilder, propBuilder]
  const c := by simp [polyBuilder, propBuilder]
  main_current _ := forall₂_map_same _ fun _ => MvPolynomial.eval_X _
  main_next _ := forall₂_map_same _ fun _ => MvPolynomial.eval_X _
  preprocessed_current _ := forall₂_map_same _ fun _ => MvPolynomial.eval_X _
  preprocessed_next _ := forall₂_map_same _ fun _ => MvPolynomial.eval_X _
  public_values _ := forall₂_map_same _ fun _ => MvPolynomial.eval_X _
  periodic_values _ := forall₂_map_same _ fun _ => MvPolynomial.eval_X _
  is_first_row _ := MvPolynomial.eval_X _
  is_last_row _ := MvPolynomial.eval_X _
  is_transition _ := MvPolynomial.eval_X _
  assert_zero h h' := by
    subst h'
    simp [polyBuilder, propBuilder, h, or_imp, forall_and]
  window := rfl

/-- A trace satisfies a parametric AIR exactly when the row builder's conjunction holds on every row. -/
theorem satisfies_iff_rows (air : Air F) (T : Instance F) :
    Satisfies (constraints air) T ↔
      ∀ i < T.height, air.eval (propBuilder (rowEnv T i) (AirLayout.from_air air)) True := by
  unfold Satisfies
  refine forall₂_congr fun i _ => ?_
  exact (air.parametric _ _ _ _ (builderRel_poly_prop (rowEnv T i) _) [] True (by simp)).symm

theorem foldl_and {α : Type _} (l : List α) (P : α → Prop) (s : Prop) :
    l.foldl (fun s a => s ∧ P a) s = (s ∧ ∀ a ∈ l, P a) := by
  induction l generalizing s with
  | nil => simp
  | cons a l ih => rw [List.foldl_cons, ih]; simp [and_assoc]

/-- The field's own operations. -/
def fieldOps : ExprOps F F := ⟨(· + ·), (· - ·), (· * ·), (- ·), id⟩

theorem propBuilder_ops (env : Var → F) (L : AirLayout) : (propBuilder env L).toExprOps = fieldOps :=
  rfl

/-- Row `o` of the window the row builder holds, with 0 past its width. -/
def rowOf (env : Var → F) (L : AirLayout) (o : Fin 2) (i : ℕ) : F :=
  ((List.range L.main_width).map (fun c => env (.main o c))).getD i 0

section steps

variable (env : Var → F) (L : AirLayout) (loc nxt : ℕ → F) (c : F) (s : Prop)

theorem prop_round_flags : eval_round_flags (propBuilder env L) s =
    (((s ∧ env .isFirstRow * (rowOf env L 0 (col.step_flags 0) - 1) = 0) ∧
      ∀ i < 23, env .isFirstRow * rowOf env L 0 (col.step_flags (i + 1)) = 0) ∧
      ∀ i < 24, env .isTransition *
        (rowOf env L 0 (col.step_flags i) - rowOf env L 1 (col.step_flags ((i + 1) % 24))) = 0) := by
  simp [eval_round_flags, AirBuilder.assert_zeros, AirBuilder.assert_one, AirBuilder.when,
    AirBuilder.when_first_row, AirBuilder.when_transition, propBuilder, foldl_and, rowOf, NUM_ROUNDS]

theorem prop_first_step : assert_first_step (propBuilder env L) loc c s =
    (s ∧ ∀ y < 5, ∀ x < 5, ∀ limb < 4, c * (loc (col.preimage y x limb) - loc (col.a y x limb)) = 0) := by
  simp [assert_first_step, AirBuilder.assert_zeros, AirBuilder.when, propBuilder, foldl_and, U64_LIMBS]

theorem prop_preimage_carry : assert_preimage_carry (propBuilder env L) loc nxt c s =
    (s ∧ ∀ y < 5, ∀ x < 5, ∀ limb < 4,
      c * (loc (col.preimage y x limb) - nxt (col.preimage y x limb)) = 0) := by
  simp [assert_preimage_carry, AirBuilder.assert_zeros, AirBuilder.when, propBuilder, foldl_and,
    U64_LIMBS]

theorem prop_export : assert_export (propBuilder env L) loc c s =
    ((s ∧ loc col.export_ * (loc col.export_ - 1) = 0) ∧ c * loc col.export_ = 0) := by
  simp [assert_export, AirBuilder.assert_bool, AirBuilder.bool_check, AirBuilder.when, propBuilder]

theorem prop_c_prime : assert_c_prime (propBuilder env L) loc s =
    (s ∧ ∀ x < 5, (∀ z < 64, loc (col.c x z) * (loc (col.c x z) - 1) = 0) ∧
      ∀ z < 64, loc (col.c_prime x z) - xor3 fieldOps (loc (col.c x z)) (loc (col.c ((x + 4) % 5) z))
        (loc (col.c ((x + 1) % 5) ((z + 63) % 64))) = 0) := by
  simp [assert_c_prime, AirBuilder.assert_zeros, AirBuilder.assert_bools, AirBuilder.bool_check,
    propBuilder, fieldOps, foldl_and]

theorem prop_a_limbs : assert_a_limbs (propBuilder env L) loc s =
    (s ∧ ∀ x < 5, ∀ y < 5, (∀ z < 64, loc (col.a_prime y x z) * (loc (col.a_prime y x z) - 1) = 0) ∧
      ∀ limb < 4, limbOf fieldOps (fun z => xor fieldOps (loc (col.a_prime y x z))
        (xor fieldOps (loc (col.c x z)) (loc (col.c_prime x z)))) limb - loc (col.a y x limb) = 0) := by
  simp [assert_a_limbs, AirBuilder.assert_zeros, AirBuilder.assert_bools, AirBuilder.bool_check,
    propBuilder, fieldOps, foldl_and, U64_LIMBS]

theorem prop_parity : assert_parity (propBuilder env L) loc s =
    (s ∧ ∀ x < 5, ∀ z < 64,
      let diff := sum fieldOps ((List.range 5).map fun y => loc (col.a_prime y x z)) -
        loc (col.c_prime x z)
      diff * (diff - 2) * (diff - (2 + 2)) = 0) := by
  simp [assert_parity, AirBuilder.assert_zeros, double, propBuilder, fieldOps, foldl_and]

theorem prop_chi : assert_chi (propBuilder env L) loc s =
    (s ∧ ∀ y < 5, ∀ x < 5, ∀ limb < 4,
      limbOf fieldOps (fun z => xor fieldOps (andn fieldOps (b loc ((x + 1) % 5) y z)
        (b loc ((x + 2) % 5) y z)) (b loc x y z)) limb - loc (col.a_prime_prime y x limb) = 0) := by
  simp [assert_chi, AirBuilder.assert_zeros, propBuilder, fieldOps, foldl_and, U64_LIMBS]

theorem prop_a_prime_prime_0_0 : assert_a_prime_prime_0_0 (propBuilder env L) loc s =
    ((s ∧ ∀ z < 64, loc (col.a_prime_prime_0_0_bits z) *
        (loc (col.a_prime_prime_0_0_bits z) - 1) = 0) ∧
      ∀ limb < 4, limbOf fieldOps (fun z => loc (col.a_prime_prime_0_0_bits z)) limb -
        loc (col.a_prime_prime 0 0 limb) = 0) := by
  simp [assert_a_prime_prime_0_0, AirBuilder.assert_zeros, AirBuilder.assert_bools,
    AirBuilder.bool_check, propBuilder, fieldOps, foldl_and, U64_LIMBS]

theorem prop_iota : assert_iota (propBuilder env L) loc s =
    (s ∧ ∀ limb < 4, limbOf fieldOps (fun i => xor fieldOps (sum fieldOps
        (((List.range 24).filter fun r => rcBit r i ≠ 0).map fun r => loc (col.step_flags r)))
        (loc (col.a_prime_prime_0_0_bits i))) limb -
      loc (col.a_prime_prime_prime_0_0_limbs limb) = 0) := by
  simp [assert_iota, AirBuilder.assert_zeros, propBuilder, fieldOps, foldl_and, U64_LIMBS,
    NUM_ROUNDS]

theorem prop_output : assert_output (propBuilder env L) loc nxt c s =
    (s ∧ ∀ x < 5, ∀ y < 5, ∀ limb < 4,
      c * (a_prime_prime_prime loc y x limb - nxt (col.a y x limb)) = 0) := by
  simp [assert_output, AirBuilder.assert_zeros, AirBuilder.when, propBuilder, foldl_and, U64_LIMBS]

end steps

/-- The constraints of the Keccak-f AIR on one row, given the current row, the next row and the two selectors. -/
structure RowSpec (loc nxt : ℕ → F) (first trans : F) : Prop where
  first_flag : first * (loc (col.step_flags 0) - 1) = 0
  first_zero : ∀ i < 23, first * loc (col.step_flags (i + 1)) = 0
  rotate : ∀ i < 24, trans * (loc (col.step_flags i) - nxt (col.step_flags ((i + 1) % 24))) = 0
  first_step : ∀ y < 5, ∀ x < 5, ∀ limb < 4,
    loc (col.step_flags 0) * (loc (col.preimage y x limb) - loc (col.a y x limb)) = 0
  carry : ∀ y < 5, ∀ x < 5, ∀ limb < 4, trans * (1 - loc (col.step_flags 23)) *
    (loc (col.preimage y x limb) - nxt (col.preimage y x limb)) = 0
  export_bool : loc col.export_ * (loc col.export_ - 1) = 0
  export_final : (1 - loc (col.step_flags 23)) * loc col.export_ = 0
  c_prime : ∀ x < 5, (∀ z < 64, loc (col.c x z) * (loc (col.c x z) - 1) = 0) ∧
    ∀ z < 64, loc (col.c_prime x z) - xor3 fieldOps (loc (col.c x z)) (loc (col.c ((x + 4) % 5) z))
      (loc (col.c ((x + 1) % 5) ((z + 63) % 64))) = 0
  a_limbs : ∀ x < 5, ∀ y < 5,
    (∀ z < 64, loc (col.a_prime y x z) * (loc (col.a_prime y x z) - 1) = 0) ∧
    ∀ limb < 4, limbOf fieldOps (fun z => xor fieldOps (loc (col.a_prime y x z))
      (xor fieldOps (loc (col.c x z)) (loc (col.c_prime x z)))) limb - loc (col.a y x limb) = 0
  parity : ∀ x < 5, ∀ z < 64,
    let diff := sum fieldOps ((List.range 5).map fun y => loc (col.a_prime y x z)) -
      loc (col.c_prime x z)
    diff * (diff - 2) * (diff - (2 + 2)) = 0
  chi : ∀ y < 5, ∀ x < 5, ∀ limb < 4,
    limbOf fieldOps (fun z => xor fieldOps (andn fieldOps (b loc ((x + 1) % 5) y z)
      (b loc ((x + 2) % 5) y z)) (b loc x y z)) limb - loc (col.a_prime_prime y x limb) = 0
  bits_bool : ∀ z < 64,
    loc (col.a_prime_prime_0_0_bits z) * (loc (col.a_prime_prime_0_0_bits z) - 1) = 0
  bits_limb : ∀ limb < 4, limbOf fieldOps (fun z => loc (col.a_prime_prime_0_0_bits z)) limb -
    loc (col.a_prime_prime 0 0 limb) = 0
  iota : ∀ limb < 4, limbOf fieldOps (fun i => xor fieldOps (sum fieldOps
      (((List.range 24).filter fun r => rcBit r i ≠ 0).map fun r => loc (col.step_flags r)))
      (loc (col.a_prime_prime_0_0_bits i))) limb - loc (col.a_prime_prime_prime_0_0_limbs limb) = 0
  output : ∀ x < 5, ∀ y < 5, ∀ limb < 4, trans * (1 - loc (col.step_flags 23)) *
    (a_prime_prime_prime loc y x limb - nxt (col.a y x limb)) = 0

/-- The row builder accepts a row of the Keccak-f AIR exactly when its row constraints hold. -/
theorem eval_iff (env : Var → F) (L : AirLayout) :
    eval (propBuilder env L) True ↔
      RowSpec (rowOf env L 0) (rowOf env L 1) (env .isFirstRow) (env .isTransition) := by
  simp only [eval, prop_round_flags, prop_first_step, prop_preimage_carry, prop_export, prop_c_prime,
    prop_a_limbs, prop_parity, prop_chi, prop_a_prime_prime_0_0, prop_iota, prop_output, true_and,
    and_assoc]
  constructor
  · rintro ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩
    exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩
  · rintro ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩
    exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩

end Plonky3Lean.Proofs.KeccakAir
