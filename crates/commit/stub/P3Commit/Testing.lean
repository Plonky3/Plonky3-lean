/-
Transcriptions of the trivial polynomial commitment scheme: its commitment is the coefficients.

What a transcription abstracts, beyond the model of the coset's polynomial space:

- the base field and the challenge field are one mathlib field K
- a matrix is its height, width and entries
- a commitment is each coefficient matrix's flat row-major values
- the transform backend's inverse transform and coset transform are parameters of p3-dft's shape
- the challenger is untouched by both open and verify, so it is left out
- verification returns some true for success, some false for an error, and none for a panic
- a debug assertion is checked, as in a debug build.

Loops, branches, early returns and the order of checks are kept.
-/
module

public import P3Commit.Domain
public import P3Commit.Types

@[expose] public section

namespace p3_commit.testing.mirror

open p3_dft.mirror p3_field.coset.mirror p3_commit.domain.mirror p3_commit.pcs.univariate.mirror

variable {K : Type _} [Field K] [DecidableEq K] (G : Gen K)

/-- The degree bound of the trivial scheme, as its base-2 logarithm. -/
structure TrivialPcs where
  log_n : ℕ

/-- A matrix's values in row-major order. -/
def flatValues (m : Mat K) : List K :=
  (List.range m.height).flatMap fun r => (List.finRange m.width).map (m.entry r)

/-- A row-major vector read as a matrix of the given width.

Its height is the length over the width, zero for width zero. -/
def ofFlat (values : List K) (width : ℕ) : Mat K :=
  ⟨if width = 0 then 0 else values.length / width, width, fun r c => values.getD (r * width + c.val) 0⟩

/-- Evaluate every column at x by Horner's rule, from the last row down. -/
def eval_coeffs_at_pt (coeffs : Mat K) (x : K) : List K :=
  let acc := (List.range coeffs.height).reverse.foldl
    (fun (acc : Fin coeffs.width → K) r => fun c => acc c * x + coeffs.entry r c) fun _ => 0
  (List.finRange coeffs.width).map acc

/-- The natural domain of a degree: the subgroup of that order.

The order must be a power of two the table covers. -/
def natural_domain_for_degree (degree : ℕ) : Option (Coset G) := do
  let l ← log2Strict degree
  TwoAdicMultiplicativeCoset.new 1 l

/-- Commit.

Each evaluation matrix goes through the inverse transform, and row r is scaled by shift^(-r).

The domain must be at least the degree bound, and its size the matrix height. -/
def TrivialPcs.commit (idft : (w : ℕ) → ℕ → (ℕ → Fin w → K) → Option (ℕ → Fin w → K))
    (pcs : TrivialPcs) (evaluations : List (Coset G × Mat K)) :
    Option (List (List K) × List (Mat K)) := do
  let coeffs ← evaluations.mapM fun de =>
    if de.1.log_size < pcs.log_n then none
    else if Coset.size G de.1 ≠ de.2.height then none
    else do
      let c ← idft de.2.width de.2.height de.2.entry
      pure (⟨de.2.height, de.2.width, fun r col => c r col * de.1.shift⁻¹ ^ r⟩ : Mat K)
  pure (coeffs.map flatValues, coeffs)

/-- Open: every matrix of every round at its points, by Horner's rule.

A round must supply one point list per matrix. -/
def TrivialPcs.open (rounds : List (List (Mat K) × List (List K))) :
    Option (List (List (List (List K)))) :=
  rounds.mapM fun r =>
    if r.1.length ≠ r.2.length then none
    else some ((r.1.zip r.2).map fun cp => cp.2.map (eval_coeffs_at_pt cp.1))

/-- Check one matrix's claims.

The width is the length over the domain size, which must divide exactly.

Every claimed point must match. -/
def checkMatrix (cv : List K × MatrixOpening K (Coset G)) : Option Unit :=
  let width := cv.1.length / Coset.size G cv.2.domain
  if width * Coset.size G cv.2.domain ≠ cv.1.length then none
  else
    let coeffs := ofFlat cv.1 width
    cv.2.points.forM fun p => if eval_coeffs_at_pt coeffs p.point = p.values then some () else none

/-- Verify, round by round.

A round whose matrix count differs from the commitment's is an error.

A wrong value panics. -/
def TrivialPcs.verify : List (CommitmentOpening K (List (List K)) (Coset G)) → Option Bool
  | [] => some true
  | r :: rs =>
    if r.commitment.length ≠ r.matrices.length then some false
    else ((r.commitment.zip r.matrices).forM (checkMatrix G)).bind fun _ => TrivialPcs.verify rs

/-- The evaluations of a committed matrix on a domain.

Pad the coefficients by a factor 2^(log_size - log_n), then take the coset transform. -/
def TrivialPcs.get_evaluations_on_domain
    (coset_dft : (w : ℕ) → ℕ → K → (ℕ → Fin w → K) → Option (ℕ → Fin w → K))
    (pcs : TrivialPcs) (prover_data : List (Mat K)) (idx : ℕ) (domain : Coset G) :
    Option (Mat K) := do
  let coeffs ← prover_data[idx]?
  if domain.log_size < pcs.log_n then none
  else
    let len := coeffs.height * coeffs.width * 2 ^ (domain.log_size - pcs.log_n)
    let height := if coeffs.width = 0 then 0 else len / coeffs.width
    let padded : ℕ → Fin coeffs.width → K := fun r c => if r < coeffs.height then coeffs.entry r c else 0
    let evals ← coset_dft coeffs.width height domain.shift padded
    pure ⟨height, coeffs.width, evals⟩

end p3_commit.testing.mirror
