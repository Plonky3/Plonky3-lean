module

public import Plonky3Lean.Proofs.KeccakAir.Binary.Parametric
public import Plonky3Lean.Proofs.KeccakAir.Degree
public import Mathlib.Algebra.Field.ZMod

@[expose] public section

/-!
# The constraint degrees of the characteristic-2 Keccak-f AIR

Every symbolic constraint has degree multiple at most 3, the AIR's own hint.

It also has at most one transition selector along a product.

The bounding builder checks this over GF(2).
-/

set_option linter.unusedSectionVars false

namespace Plonky3Lean.Proofs.KeccakAir.Binary

open p3_air.symbolic.mirror p3_air.builder.mirror p3_air.air.mirror p3_keccak_air.mirror
open p3_keccak_air.mirror.binary Plonky3Lean.Proofs.Air Plonky3Lean.Proofs.KeccakAir

/-- The bounding builder accepts the characteristic-2 AIR over the field. -/
abbrev TopOkB (F : Type) [Field F] (cb : Bool) : Prop :=
  (binaryAir (F := F) cb).eval (topBuilder (AirLayout.from_air (binaryAir (F := F) cb))) true = true

theorem top_binary_gf2 (cb : Bool) : TopOkB (ZMod 2) cb := by
  cases cb <;>
  · simp only [TopOkB, binaryAir, binary.eval, topBuilder, getD_map_const, AirLayout.from_air]
    decide +kernel

variable {F : Type} [Field F] [DecidableEq F]

/-- Every symbolic constraint has degree multiple at most 3.

It also has at most one transition selector along a product. -/
theorem binary_constraints_bounded {cb : Bool} (htop : TopOkB F cb) :
    ∀ e ∈ (binaryAir (F := F) cb).eval (symbolicBuilder (AirLayout.from_air (binaryAir (F := F) cb))) [],
      e.degree_multiple ≤ 3 ∧ transitionCount e ≤ 1 :=
  bounded_of_top _ htop

/-! ## The constraint count -/

/-- A builder that counts the assertions. -/
def countBuilder (layout : AirLayout) : AirBuilder F Unit ℕ where
  add _ _ := ()
  sub _ _ := ()
  mul _ _ := ()
  neg _ := ()
  const _ := ()
  main _ := ⟨(List.range layout.main_width).map fun _ => (), (List.range layout.main_width).map fun _ => ()⟩
  preprocessed _ := ⟨(List.range layout.preprocessed_width).map fun _ => (),
    (List.range layout.preprocessed_width).map fun _ => ()⟩
  is_first_row _ := ()
  is_last_row _ := ()
  is_transition _ := ()
  assert_zero s _ := s + 1
  public_values _ := (List.range layout.num_public_values).map fun _ => ()
  periodic_values _ := (List.range layout.num_periodic_columns).map fun _ => ()

theorem builderRel_count (layout : AirLayout) :
    BuilderRel (symbolicBuilder (F := F) layout) (countBuilder layout) (fun _ _ => True)
      (fun s n => s.length = n) where
  add _ _ := trivial
  sub _ _ := trivial
  mul _ _ := trivial
  neg _ := trivial
  const _ := trivial
  main_current _ := forall₂_map_map fun _ _ => trivial
  main_next _ := forall₂_map_map fun _ _ => trivial
  preprocessed_current _ := forall₂_map_map fun _ _ => trivial
  preprocessed_next _ := forall₂_map_map fun _ _ => trivial
  public_values _ := forall₂_map_map fun _ _ => trivial
  periodic_values _ := forall₂_map_map fun _ _ => trivial
  is_first_row _ := trivial
  is_last_row _ := trivial
  is_transition _ := trivial
  assert_zero h _ := by simp [symbolicBuilder, countBuilder, h]
  window := rfl

/-- The number of symbolic constraints is what the counting builder counts. -/
theorem length_constraints (air : Air F) :
    (air.eval (symbolicBuilder (AirLayout.from_air air)) []).length =
      air.eval (countBuilder (AirLayout.from_air air)) 0 :=
  air.parametric _ _ _ _ (builderRel_count _) [] 0 rfl

/-- Over GF(2), the AIR asserts exactly the number of constraints it reports. -/
theorem count_binary_gf2 (cb : Bool) :
    some ((binaryAir (F := ZMod 2) cb).eval
        (symbolicBuilder (AirLayout.from_air (binaryAir (F := ZMod 2) cb))) []).length =
      binary.num_constraints cb := by
  rw [length_constraints]
  cases cb <;>
  · simp only [binaryAir, binary.eval, countBuilder, getD_map_const, AirLayout.from_air]
    decide +kernel

end Plonky3Lean.Proofs.KeccakAir.Binary
