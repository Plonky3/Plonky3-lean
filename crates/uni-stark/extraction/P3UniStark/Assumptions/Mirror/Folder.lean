/-
Transcriptions of the constraint folders and of the alpha-power layout they share.

These do not extract.
They are generic over the configuration and the field traits, which aeneas rejects.

Each definition transcribes one Rust item, named in the crate's mirror entries.

What a transcription abstracts, beyond the builder transcriptions of p3-air:

* the base field F and the challenge field K are mathlib fields, with K an F-algebra
* the basis of K over F that Rust fixes is a parameter
* a packed value is one lane, since every lane runs the same operations on its own row
* the AIR emits base constraints only, as p3-air's transcribed AIR does
* so the extension streams are empty
* the debug-only constraint counter is dropped
* a panic is none.

The order of operations is kept.
-/
module

public import P3Air
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.Algebra.Algebra.Basic

@[expose] public section

namespace p3_uni_stark.folder.mirror

open p3_air.builder.mirror p3_air.air.mirror p3_air.symbolic.mirror

variable {F K : Type} [Field F] [DecidableEq F] [Field K] [Algebra F K]

/-- The global indices of the base and the extension constraints, in emission order. -/
structure ConstraintLayout where
  base_indices : List ℕ
  ext_indices : List ℕ

/-- The number of constraints. -/
def ConstraintLayout.total_constraints (l : ConstraintLayout) : ℕ :=
  l.base_indices.length + l.ext_indices.length

/-- The powers alpha^(m - 1 - i) of the m constraints, split by stream.

Base power j is transposed into its D coordinates in the basis, coordinate d first. -/
noncomputable def ConstraintLayout.decompose_alpha {D : ℕ} (B : Module.Basis (Fin D) F K)
    (l : ConstraintLayout) (α : K) : List (List F) × List K :=
  let total := l.total_constraints
  let alpha_powers := ((List.range total).map (α ^ ·)).reverse
  ((List.finRange D).map fun d => l.base_indices.map fun idx => B.repr (alpha_powers.getD idx 0) d,
    l.ext_indices.map fun idx => alpha_powers.getD idx 0)

/-- The symbolic builder's layout: every constraint of the transcribed AIR is a base constraint. -/
def get_constraint_layout (air : Air F) (layout : AirLayout) : Except String ConstraintLayout := do
  layout.validate_against_air air
  let cs := air.eval (symbolicBuilder layout) []
  pure ⟨List.range cs.length, []⟩

/-- The linear combination sum_i c_i v_i.

It asserts that both lists have the same length. -/
def batched_linear_combination {R A : Type} [CommRing R] [AddCommMonoid A] [Module R A]
    (values : List A) (coeffs : List R) : Option A :=
  if values.length = coeffs.length then some ((values.zip coeffs).map fun p => p.2 • p.1).sum
  else none

/-- The prover's folder on one row.

It holds the row's values, and a state that collects each asserted base constraint. -/
def proverFolder (main preprocessed : RowWindow F) (public_values periodic_values : List F)
    (is_first_row is_last_row is_transition : F) : AirBuilder F F (List F) where
  add := (· + ·)
  sub := (· - ·)
  mul := (· * ·)
  neg := (- ·)
  const := id
  main _ := main
  preprocessed _ := preprocessed
  is_first_row _ := is_first_row
  is_last_row _ := is_last_row
  is_transition _ := is_transition
  assert_zero s x := s ++ [x]
  public_values _ := public_values
  periodic_values _ := periodic_values

/-- The prover's combination of the constraints.

It takes one base dot product per basis coordinate, assembled in the basis.
It adds the extension dot product. -/
noncomputable def finalize_constraints {D : ℕ} (B : Module.Basis (Fin D) F K)
    (base_alpha_powers : List (List F)) (ext_alpha_powers : List K)
    (base_constraints : List F) (ext_constraints : List K) : Option K := do
  let coeffs ← (List.range D).mapM fun d =>
    batched_linear_combination base_constraints (base_alpha_powers.getD d [])
  let acc := ∑ d : Fin D, coeffs.getD d 0 • B d
  let ext ← batched_linear_combination ext_constraints ext_alpha_powers
  pure (acc + ext)

/-- The verifier's folder at the out-of-domain point.

It holds the opened values, and an accumulator.
Each assertion x updates the accumulator to acc alpha + x. -/
def verifierFolder (main preprocessed : RowWindow K) (public_values : List F)
    (periodic_values : List K) (is_first_row is_last_row is_transition alpha : K) :
    AirBuilder F K K where
  add := (· + ·)
  sub := (· - ·)
  mul := (· * ·)
  neg := (- ·)
  const := algebraMap F K
  main _ := main
  preprocessed _ := preprocessed
  is_first_row _ := is_first_row
  is_last_row _ := is_last_row
  is_transition _ := is_transition
  assert_zero acc x := acc * alpha + x
  public_values _ := public_values.map (algebraMap F K)
  periodic_values _ := periodic_values

end p3_uni_stark.folder.mirror
