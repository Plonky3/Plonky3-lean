/-
Transcriptions of the domain of p3-binary-dft: its points, their steps, and the subspace polynomials.
-/
module

public import P3BinaryDft.Model

@[expose] public section

namespace p3_binary_dft.domain.mirror

open p3_binary_dft.mirror

variable {F : Type _} [Field F]

/-- The loop of the domain point: add the basis vector of every set bit of the index, lowest first. -/
def domain_point.loop (L : Level F) (point : F) (remaining r : ℕ) : Option F :=
  if remaining = 0 then some point
  else do
    let point ← if remaining % 2 = 1 then (L.cantorBasis r).map (point + ·) else some point
    domain_point.loop L point (remaining / 2) (r + 1)
termination_by remaining
decreasing_by omega

/-- The point of the domain at an index. -/
def domain_point (L : Level F) (index : ℕ) : Option F := domain_point.loop L 0 index 0

/-- The steps between consecutive even domain points: entry r adds basis vector r + 1 to entry r - 1. -/
def domain_point_steps (L : Level F) (count : ℕ) : Option (List F) :=
  ((List.range count).foldlM (fun (acc : F × List F) r => do
      let point := acc.1 + (← L.cantorBasis (r + 1))
      pure (point, acc.2 ++ [point])) (0, [])).map (fun p : F × List F => p.2)

/-- The subspace polynomial: j rounds of value <- value^2 + value. -/
def subspace_polynomial (j : ℕ) (x : F) : F :=
  (List.range j).foldl (fun value _ => value ^ 2 + value) x

end p3_binary_dft.domain.mirror
