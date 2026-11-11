module

public import Plonky3Lean.Proofs.KeccakAir.Binary.Parametric
public import Plonky3Lean.Proofs.KeccakAir.Row

@[expose] public section

/-!
# The constraints of one row of the characteristic-2 AIR

The row builder's conjunction for the characteristic-2 AIR, written out.
-/

set_option linter.unusedSectionVars false

namespace Plonky3Lean.Proofs.KeccakAir.Binary

open p3_air.builder.mirror p3_air.air.mirror p3_keccak_air.mirror p3_keccak_air.mirror.binary
open Plonky3Lean.Spec.Air Plonky3Lean.Proofs.KeccakAir

variable {F : Type} [Field F]

section helpers

variable (loc : ℕ → F)

/-- The column sums C[x][z]. -/
def colC (x z : ℕ) : F := sum fieldOps ((List.range 5).map fun y => loc (binary.col.a y x z))

/-- A'[y][x][z] = A[y][x][z] + C[x - 1][z] + C[x + 1][z - 1]. -/
def colA' (y x z : ℕ) : F :=
  colC loc ((x + 4) % 5) z + colC loc ((x + 1) % 5) ((z + 63) % 64) + loc (binary.col.a y x z)

/-- Bit z of B[x][y], read from A'. -/
def colB (x y z : ℕ) : F :=
  colA' loc x ((x + 3 * y) % 5) ((z + 64 - rOf ((x + 3 * y) % 5) x) % 64)

/-- The round map's value at bit z of lane (x, y): chi plus the next state, gated, plus the round constant. -/
def roundExpr (nxt : ℕ → F) (x y z : ℕ) : F :=
  let chi := colB loc x y z + (1 + colB loc ((x + 1) % 5) y z) * colB loc ((x + 2) % 5) y z
  let round_map := (1 + loc (col.round_flags 24)) * (chi + nxt (binary.col.a y x z))
  if x = 0 ∧ y = 0 then
    round_map + sum fieldOps (((List.range 24).filter fun r => rcBit r z ≠ 0).map fun r =>
      loc (col.round_flags r))
  else round_map

end helpers

/-- The constraints of the characteristic-2 AIR on one row. -/
structure RowSpecB (cb : Bool) (loc nxt : ℕ → F) (first : F) : Prop where
  first_flag : first * (loc (col.round_flags 0) - 1) = 0
  first_zero : ∀ i < 24, first * loc (col.round_flags (i + 1)) = 0
  step : ∀ r < 23, nxt (col.round_flags (r + 1)) + loc (col.round_flags r) = 0
  wrap : nxt (col.round_flags 0) + nxt (col.round_flags 24) + loc (col.round_flags 23) +
    loc (col.round_flags 24) = 0
  excl : loc (col.round_flags 0) * loc (col.round_flags 24) = 0
  bools : cb = true → ∀ y < 5, ∀ x < 5, ∀ z < 64, loc (binary.col.a y x z) * (loc (binary.col.a y x z) - 1) = 0
  round : ∀ y < 5, ∀ x < 5, ∀ z < 64, roundExpr loc nxt x y z = 0

/-- The row builder accepts a row of the characteristic-2 AIR exactly when its row constraints hold. -/
theorem eval_iff (cb : Bool) (env : Var → F) (L : AirLayout) :
    binary.eval cb (propBuilder env L) True ↔
      RowSpecB cb (rowOf env L 0) (rowOf env L 1) (env .isFirstRow) := by
  cases cb <;>
  simp only [binary.eval, AirBuilder.assert_zeros, AirBuilder.assert_bools, AirBuilder.assert_one,
    AirBuilder.bool_check, AirBuilder.when_first_row, AirBuilder.when, List.foldl_map,
    pb_assert_zero, pb_first, propBuilder_ops,
    foldl_and, Bool.false_eq_true, ↓reduceIte, true_and, and_assoc, List.mem_range] <;>
  constructor
  · rintro ⟨h1, h2, h3, h4, h5, h6⟩
    exact ⟨h1, h2, h3, h4, h5, fun h => absurd h (by simp), h6⟩
  · rintro ⟨h1, h2, h3, h4, h5, -, h6⟩
    exact ⟨h1, h2, h3, h4, h5, h6⟩
  · rintro ⟨h1, h2, h3, h4, h5, h6, h7⟩
    exact ⟨h1, h2, h3, h4, h5, fun _ => h6, h7⟩
  · rintro ⟨h1, h2, h3, h4, h5, h6, h7⟩
    exact ⟨h1, h2, h3, h4, h5, h6 rfl, h7⟩

end Plonky3Lean.Proofs.KeccakAir.Binary
