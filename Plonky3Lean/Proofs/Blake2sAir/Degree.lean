module

public import Plonky3Lean.Proofs.Blake2sAir.Parametric
public import Plonky3Lean.Proofs.Sha256Air.Degree

@[expose] public section

/-!
# The constraint degrees of the BLAKE2s AIR

A builder over pairs of naturals bounds the degree multiple and the transition count of every constraint.

- Every constraint has degree multiple at most 2, the declared bound.
- No constraint reads a transition selector.
- The AIR asserts exactly the number of constraints it reports: 16033 with the booleanity, 15200 without.

The bounding builder checks this by evaluation over GF(2).
-/

set_option linter.unusedSectionVars false

namespace Plonky3Lean.Proofs.Blake2sAir

open p3_air.symbolic.mirror p3_air.builder.mirror p3_air.air.mirror p3_blake2s_air.mirror
open Plonky3Lean.Proofs.Air SymbolicExpr
open Plonky3Lean.Proofs.Sha256Air (topBuilder bounded_of_top getD_map_const')
open Plonky3Lean.Proofs.KeccakAir (getD_map_const)
open Plonky3Lean.Proofs.KeccakAir.Binary (length_constraints countBuilder)

variable {F : Type} [Field F] [DecidableEq F]

/-- The bounding builder accepts the AIR at degree 2. -/
abbrev TopOk (F : Type) [Field F] (cb : Bool) : Prop :=
  (blake2sAir (F := F) cb).eval (topBuilder 2 (AirLayout.from_air (blake2sAir (F := F) cb))) true = true

theorem top_gf2 (cb : Bool) : TopOk (ZMod 2) cb := by
  cases cb <;>
  · simp only [TopOk, blake2sAir, eval, eval_g, add2, add3, topBuilder, getD_map_const', List.length_range,
      AirLayout.from_air]
    decide +kernel

/-- Each constraint has degree multiple at most 2, and no transition selector. -/
theorem constraints_bounded {cb : Bool} (htop : TopOk F cb) :
    ∀ e ∈ (blake2sAir (F := F) cb).eval (symbolicBuilder (AirLayout.from_air (blake2sAir (F := F) cb))) [],
      e.degree_multiple ≤ 2 ∧ transitionCount e = 0 :=
  bounded_of_top _ htop

/-- Over GF(2), the AIR asserts exactly the number of constraints it reports. -/
theorem num_constraints_eq (cb : Bool) :
    some ((blake2sAir (F := ZMod 2) cb).eval
        (symbolicBuilder (AirLayout.from_air (blake2sAir (F := ZMod 2) cb))) []).length =
      num_constraints cb := by
  rw [length_constraints]
  cases cb <;>
  · simp only [blake2sAir, eval, eval_g, add2, add3, countBuilder, getD_map_const, AirLayout.from_air]
    decide +kernel

end Plonky3Lean.Proofs.Blake2sAir
