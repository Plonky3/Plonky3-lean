/-
Transcriptions of the univariate scheme trait's default methods.

What a transcription abstracts, beyond the model of the coset's polynomial space:

- a scheme's required methods are parameters
- a matrix is its height, width and entries
- a panic is none.

The order of operations is kept.
-/
module

public import P3Commit.Domain
public import P3Commit.Types

@[expose] public section

namespace p3_commit.pcs.univariate.mirror

open p3_dft.mirror p3_field.coset.mirror p3_commit.domain.mirror

variable {K : Type _} [Field K] [DecidableEq K] (G : Gen K)

/-- The default preprocessing commit: the ordinary commit. -/
def commit_preprocessing {α : Type _} (commit : List (Coset G × Mat K) → α)
    (evaluations : List (Coset G × Mat K)) : α :=
  commit evaluations

/-- The default quotient commit.

Split the evaluations and the domain into chunks, extend each chunk, and commit the extensions. -/
def commit_quotient {α : Type _}
    (get_quotient_ldes : List (Coset G × Mat K) → ℕ → Option (List (Mat K)))
    (commit_ldes : List (Mat K) → Option α) (quotient_domain : Coset G) (evals : Mat K)
    (num_chunks : ℕ) : Option α := do
  let quotient_sub_evaluations ← Coset.split_evals G quotient_domain num_chunks evals.height
    evals.entry
  let quotient_sub_domains ← Coset.split_domains G quotient_domain num_chunks
  let ldes ← get_quotient_ldes ((quotient_sub_domains.zip quotient_sub_evaluations).map fun de =>
    (de.1, ⟨evals.height / num_chunks, evals.width, de.2⟩)) num_chunks
  commit_ldes ldes

/-- The default evaluations without randomization: the ordinary evaluations. -/
def get_evaluations_on_domain_no_random {PD α : Type _}
    (get_evaluations_on_domain : PD → ℕ → Coset G → α) (prover_data : PD) (idx : ℕ)
    (domain : Coset G) : α :=
  get_evaluations_on_domain prover_data idx domain

/-- The default opening with preprocessing.

It asserts the scheme is not hiding, then opens as usual. -/
def open_with_preprocessing {R C α : Type _} (zk : Bool) (open_ : R → C → α) (requests : R)
    (challenger : C) (_preprocessed : Option ℕ) : Option α :=
  if zk then none else some (open_ requests challenger)

/-- The default verification with preprocessing: the ordinary verification, whatever the index. -/
def verify_with_preprocessing {R P C α : Type _} (verify : R → P → C → α) (rounds : R) (proof : P)
    (challenger : C) (_preprocessed : Option ℕ) : α :=
  verify rounds proof challenger

/-- The default randomization commitment: none. -/
def get_opt_randomization_poly_commitment {α : Type _} : Option (Option α) := some none

end p3_commit.pcs.univariate.mirror
