module

public import Plonky3Lean.Proofs.Whir.Complete

@[expose] public section

/-!
# The round constraint is Construction 5.1's update

The verifier batches a round's out-of-domain claims, then its shift-query claims.

It uses the powers gamma, gamma^2 and so on.

Its claim is the paper's claim update, check 2(c).

Its weight is the paper's weight update, step 2(e).
-/

namespace Plonky3Lean.Proofs.Whir

open Finset Plonky3Lean.Spec.MultilinearUtil Plonky3Lean.Spec.Whir Plonky3Lean.Proofs.MultilinearUtil
open p3_sumcheck.constraints.mirror p3_multilinear_util.point.mirror

set_option linter.unusedSectionVars false

variable {F EF : Type _} [Field F] [Field EF] [Algebra F EF]

theorem powers_succ (γ : EF) (s m : ℕ) : powers γ s (m + 1) = γ ^ s :: powers γ (s + 1) m := by
  simp only [powers, List.range_succ_eq_map, List.map_cons, List.map_map, add_zero]
  congr 1
  exact List.map_congr_left fun j _ => by
    simp only [Function.comp_apply, Nat.succ_eq_add_one]; ring_nf

theorem dot_powers (γ : EF) : ∀ (l : List EF) (s m : ℕ), l.length = m →
    dot l (powers γ s m) = ∑ j ∈ range m, γ ^ (s + j) * l.getD j 0
  | [], _, _, h => by subst h; simp [dot, powers]
  | a :: l, s, m, h => by
    subst h
    rw [List.length_cons, powers_succ, sum_range_succ']
    have ih := dot_powers γ l (s + 1) l.length rfl
    simp only [dot, List.zipWith_cons_cons, List.sum_cons] at ih ⊢
    rw [ih, List.getD_cons_zero, add_zero, add_comm]
    congr 1
    · exact sum_congr rfl fun j _ => by rw [List.getD_cons_succ, show s + (j + 1) = s + 1 + j by omega]
    · ring

/-- The round constraint's claim is the claim update of Construction 5.1.

It puts gamma^(j+1) on the j-th out-of-domain answer, then gamma^(s+j+1) on the j-th query answer. -/
theorem round_combine_evals (σ γ : EF) (nv : ℕ) (pts : List (List EF)) (ys : List EF) (vars : List F)
    (vs : List EF) (hp : pts.length = ys.length) (hv : vars.length = vs.length) :
    (⟨nv, [.Eq ⟨nv, pts, ys⟩, .Select ⟨nv, vars, vs⟩], γ, 1⟩ : Constraint F EF).combine_evals σ =
      nextClaim σ γ ys vs := by
  rw [Constraint.combine_evals_eq _ _ (by
    simp only [List.mem_cons, List.mem_nil_iff, or_false]; rintro _ (rfl | rfl) <;> assumption)]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, Statements.evals, List.length_append,
    powers_add]
  rw [dot_append (length_powers _ _ _).symm, dot_powers γ _ _ _ rfl, dot_powers γ _ _ _ rfl, nextClaim, add_assoc]
  congr 2
  · exact sum_congr rfl fun j _ => by rw [add_comm 1 j]
  · exact sum_congr rfl fun j _ => by rw [show 1 + ys.length + j = ys.length + j + 1 by omega]

/-- Add the round constraint's weight to the restricted previous weight.

The sum is the weight update of Construction 5.1, with the out-of-domain points expanded to pow(z, n). -/
theorem round_weight (w : List EF → EF) (r : List EF) (γ : EF) (n : ℕ) (zs : List EF) (vars : List F)
    (vs : List EF) (hv : vars.length = vs.length) (x : List EF) :
    w (r ++ x) + weightAt (⟨n, [.Eq ⟨n, zs.map (Point.expand_from_univariate · n), zs.map fun _ => 0⟩,
      .Select ⟨n, vars, vs⟩], γ, 1⟩ : Constraint F EF) x =
      nextWeight w r γ zs (vars.map (algebraMap F EF)) n x := by
  simp only [weightAt, nextWeight, List.flatMap_cons, List.flatMap_nil, List.append_nil, Statements.weights,
    Statements.evals, List.length_append, List.length_map, powers_add, add_assoc]
  rw [dot_append (by simp), ← hv, dot_powers γ _ _ _ (by simp), dot_powers γ _ _ _ (by simp)]
  congr 2
  · refine sum_congr rfl fun j hj => ?_
    rw [add_comm 1 j]
    simp [List.getD_eq_getElem?_getD, mem_range.mp hj, expand_from_univariate_eq, pow]
  · refine sum_congr rfl fun j hj => ?_
    rw [show 1 + zs.length + j = zs.length + (j + 1) by omega]
    simp [List.getD_eq_getElem?_getD, mem_range.mp hj]

end Plonky3Lean.Proofs.Whir
