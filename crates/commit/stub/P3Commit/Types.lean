/-
The data types of the opening claims, and the matrix the transcriptions are written in.

A row-major matrix is its height, its width and its entries.
-/
module

public import Mathlib.Data.Fin.Basic

@[expose] public section

namespace p3_commit.pcs.univariate.mirror

/-- A matrix: its height, its width, and its entries, row by row. -/
structure Mat (K : Type _) where
  height : ℕ
  width : ℕ
  entry : ℕ → Fin width → K

/-- Claimed values of every column at one point. -/
structure PointOpening (K : Type _) where
  point : K
  values : List K

/-- The points opened in one matrix, with its domain. -/
structure MatrixOpening (K D : Type _) where
  domain : D
  points : List (PointOpening K)

/-- The claims for one commitment, matrix by matrix. -/
structure CommitmentOpening (K C D : Type _) where
  commitment : C
  matrices : List (MatrixOpening K D)

end p3_commit.pcs.univariate.mirror
