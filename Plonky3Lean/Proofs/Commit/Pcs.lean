module

public import P3Commit.Pcs
public import Plonky3Lean.Proofs.Commit.Trivial

@[expose] public section

/-!
# p3-commit: the scheme contract's consequences and the trait defaults

Binding follows from soundness: two accepted openings of one column at one point agree.

The default quotient commit hands the extension step chunk i of the quotient domain with the quotient's values on that chunk.
-/

open Polynomial Finset
open p3_commit.pcs.univariate.mirror p3_commit.domain.mirror p3_field.coset.mirror p3_dft.mirror
open Plonky3Lean.Spec.Commit Plonky3Lean.Proofs.Dft

namespace Plonky3Lean.Proofs.Commit

set_option linter.unusedSectionVars false

/-- Binding: two accepted claims about one commitment, matrix, domain and point carry the same values, unless Broken. -/
theorem UnivariatePcs.Contract.binding {K : Type _} [Field K] {pcs : UnivariatePcs K}
    (C : pcs.Contract) {cl₁ cl₂ : List (CommitmentOpening K pcs.Commitment pcs.Domain)}
    {pf₁ pf₂ : pcs.Proof} {ch₁ ch₂ b₁ b₂ : pcs.Challenger}
    (h₁ : pcs.verify cl₁ pf₁ ch₁ = some (true, b₁)) (h₂ : pcs.verify cl₂ pf₂ ch₂ = some (true, b₂))
    {o₁ o₂ : CommitmentOpening K pcs.Commitment pcs.Domain} (ho₁ : o₁ ∈ cl₁) (ho₂ : o₂ ∈ cl₂)
    (hcm : o₁.commitment = o₂.commitment) {m : ℕ} (hm₁ : m < o₁.matrices.length)
    (hm₂ : m < o₂.matrices.length) (hd : o₁.matrices[m].domain = o₂.matrices[m].domain)
    {p₁ p₂ : PointOpening K} (hp₁ : p₁ ∈ o₁.matrices[m].points) (hp₂ : p₂ ∈ o₂.matrices[m].points)
    (hz : p₁.point = p₂.point) : p₁.values = p₂.values ∨ C.Broken o₁.commitment := by
  rcases C.soundness _ _ _ _ h₁ o₁ ho₁ m hm₁ p₁ hp₁ with e₁ | b
  · rcases C.soundness _ _ _ _ h₂ o₂ ho₂ m hm₂ p₂ hp₂ with e₂ | b
    · left; rw [e₁, e₂, hcm, hd, hz]
    · right; rwa [hcm]
  · exact Or.inr b

section defaults

variable {K : Type _} [Field K] [DecidableEq K] (G : Gen K)

/-- The default quotient commit extends chunk i of a quotient domain of order 2^k, split into 2^l, with the values at its points i + 2^l j. -/
theorem commit_quotient_eq (hV : GenValid G) {α : Type _}
    (get_quotient_ldes : List (Coset G × Mat K) → ℕ → Option (List (Mat K)))
    (commit_ldes : List (Mat K) → Option α) (qd : Coset G) (evals : Mat K)
    (hh : evals.height = Coset.size G qd) {l : ℕ} (hl : l ≤ qd.log_size) :
    commit_quotient G get_quotient_ldes commit_ldes qd evals (2 ^ l) =
      (get_quotient_ldes ((List.range (2 ^ l)).map fun i => (chunk G hV qd l i,
        (⟨2 ^ (qd.log_size - l), evals.width, fun j =>
          if j < 2 ^ (qd.log_size - l) then evals.entry (i + 2 ^ l * j) else 0⟩ : Mat K))) (2 ^ l)).bind
        commit_ldes := by
  have hdiv : evals.height / 2 ^ l = 2 ^ (qd.log_size - l) := by
    rw [hh, size_eq, Nat.pow_div hl (by norm_num)]
  simp only [commit_quotient, hh, split_evals_eq G qd hl, split_domains_eq G hV qd hl,
    Option.bind_eq_bind, Option.bind_some]
  have hz : ∀ L : List ℕ, L.zip L = L.map fun x => (x, x) := fun L => by
    induction L <;> simp_all
  rw [← hh, hdiv, List.zip_map_left, List.zip_map_right, hz, List.map_map, List.map_map,
    List.map_map]
  rfl

/-- The default opening with preprocessing panics on a hiding scheme and opens as usual otherwise. -/
theorem open_with_preprocessing_eq {R C α : Type _} (zk : Bool) (open_ : R → C → α) (r : R) (c : C)
    (p : Option ℕ) : open_with_preprocessing zk open_ r c p = if zk then none else some (open_ r c) :=
  rfl

end defaults

end Plonky3Lean.Proofs.Commit
