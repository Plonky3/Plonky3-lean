module

public import Plonky3Lean.Proofs.KeccakAir.Binary.Parametric
public import Plonky3Lean.Proofs.KeccakAir.Degree
public import Mathlib.Algebra.Field.ZMod

@[expose] public section

/-!
# The constraint degrees of the characteristic-2 Keccak-f AIR

Every symbolic constraint has degree multiple at most 3, the AIR's own hint, and at most one transition selector along a product.

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

/-- Every symbolic constraint has degree multiple at most 3 and at most one transition selector along a product. -/
theorem binary_constraints_bounded {cb : Bool} (htop : TopOkB F cb) :
    ∀ e ∈ (binaryAir (F := F) cb).eval (symbolicBuilder (AirLayout.from_air (binaryAir (F := F) cb))) [],
      e.degree_multiple ≤ 3 ∧ transitionCount e ≤ 1 :=
  bounded_of_top _ htop

end Plonky3Lean.Proofs.KeccakAir.Binary
