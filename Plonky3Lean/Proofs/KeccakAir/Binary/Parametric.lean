module

public import Plonky3Lean.Proofs.KeccakAir.Parametric

@[expose] public section

/-!
# The characteristic-2 Keccak-f AIR is parametric

The transcribed evaluation maps related builders and related states to related states.

That makes it an AIR in the sense of the p3-air model, with 1625 main columns and the degree hint 3.
-/

set_option linter.unusedSectionVars false

namespace Plonky3Lean.Proofs.KeccakAir.Binary

open p3_air.builder.mirror p3_air.air.mirror p3_keccak_air.mirror p3_keccak_air.mirror.binary
open Plonky3Lean.Proofs.KeccakAir

variable {F : Type} [Field F]

theorem eval_parametric (cb : Bool) : IsParametric (binary.eval (F := F) cb) := by
  intro E₁ S₁ E₂ S₂ B₁ B₂ R Q h s₁ s₂ hs
  simp only [binary.eval, rho_pi_source, AirBuilder.assert_bools, AirBuilder.assert_one,
    AirBuilder.bool_check, AirBuilder.when_first_row, List.map_map, Function.comp_def]
  rel_tac

/-- The characteristic-2 Keccak-f AIR, with or without the state booleanity. -/
def binaryAir (cb : Bool) : Air F where
  width := NUM_KECCAK_BINARY_COLS
  max_constraint_degree := some 3
  eval := binary.eval cb
  parametric := eval_parametric cb

end Plonky3Lean.Proofs.KeccakAir.Binary
