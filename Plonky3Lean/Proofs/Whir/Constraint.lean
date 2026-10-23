module

public import Plonky3Lean.Proofs.Whir.Weights
public import Plonky3Lean.Proofs.MultilinearUtil.PointForms

@[expose] public section

/-!
# Batched constraints

A constraint batches its claims s_0, s_1, ... with the powers gamma^p, gamma^(p+1), ..., p its initial power.

The groups follow each other: the claims of a group take the powers after those of the groups before it.

```text
    claim:   sigma + sum_i gamma^(p + i) s_i
    weight:  sum_i gamma^(p + i) w_i(y)
```
-/

namespace Plonky3Lean.Proofs.Whir

open Finset Plonky3Lean.Spec.MultilinearUtil Plonky3Lean.Spec.Whir Plonky3Lean.Proofs.MultilinearUtil
open p3_sumcheck.constraints.mirror p3_multilinear_util.point.mirror

set_option linter.unusedSectionVars false

variable {F EF : Type _} [Field F] [Field EF] [Algebra F EF]

theorem powers_add (γ : EF) (s m n : ℕ) : powers γ s (m + n) = powers γ s m ++ powers γ (s + m) n := by
  simp [powers, List.range_add, add_assoc]

@[simp] theorem length_powers (γ : EF) (s n : ℕ) : (powers γ s n).length = n := by simp [powers]

theorem dot_append {a b c d : List EF} (h : a.length = c.length) : dot (a ++ b) (c ++ d) = dot a c + dot b d := by
  simp [dot, List.zipWith_append h]

/-- The claimed values of a group. -/
def _root_.p3_sumcheck.constraints.mirror.Statements.evals : Statements F EF → List EF
  | .Eq s => s.evaluations
  | .Select s => s.evaluations

/-- A group is well formed when it has one claimed value per point. -/
def _root_.p3_sumcheck.constraints.mirror.Statements.WF : Statements F EF → Prop
  | .Eq s => s.points.length = s.evaluations.length
  | .Select s => s.vars.length = s.evaluations.length

theorem _root_.p3_sumcheck.constraints.mirror.Statements.len_eq_of_WF {s : Statements F EF} (h : s.WF) :
    s.len = s.evals.length := by
  cases s <;> simp_all [Statements.WF, Statements.len, Statements.evals, EqStatement.len, SelectStatement.len]

theorem _root_.p3_sumcheck.constraints.mirror.Statements.combine_evals_eq (s : Statements F EF) (σ γ : EF)
    (shift : ℕ) :
    s.combine_evals σ γ shift = σ + dot s.evals (powers γ shift s.evals.length) := by
  cases s <;> rfl

theorem foldl_combine (γ : EF) : ∀ (l : List (Statements F EF)) (σ : EF) (shift : ℕ), (∀ s ∈ l, s.WF) →
    l.foldl (fun (acc : EF × ℕ) s => (s.combine_evals acc.1 γ acc.2, acc.2 + s.len)) (σ, shift) =
      (σ + dot (l.flatMap Statements.evals) (powers γ shift (l.flatMap Statements.evals).length),
        shift + (l.flatMap Statements.evals).length)
  | [], σ, shift, _ => by simp [dot]
  | s :: l, σ, shift, h => by
    rw [List.foldl_cons, Statements.combine_evals_eq, Statements.len_eq_of_WF (h s (by simp)),
      foldl_combine γ l _ _ fun t ht => h t (by simp [ht])]
    simp only [List.flatMap_cons, List.length_append, powers_add, dot_append (length_powers _ _ _).symm,
      add_assoc]

/-- combine_evals: the claim plus every claimed value against its power, the groups in order. -/
theorem _root_.p3_sumcheck.constraints.mirror.Constraint.combine_evals_eq (c : Constraint F EF) (σ : EF)
    (h : ∀ s ∈ c.statements, s.WF) :
    c.combine_evals σ = σ + dot (c.statements.flatMap Statements.evals)
      (powers c.challenge c.initial_power (c.statements.flatMap Statements.evals).length) := by
  rw [Constraint.combine_evals, foldl_combine c.challenge _ _ _ h]

/-- The weights of a group at y: eq(z, y) for an equality point, the selector of its powers for a scalar point. -/
def _root_.p3_sumcheck.constraints.mirror.Statements.weights (y : List EF) : Statements F EF → List EF
  | .Eq s => s.points.map fun p => eq p y
  | .Select s => s.vars.map fun v => sel (algebraMap F EF v) y

/-- Every equality point of the group has as many coordinates as y. -/
def _root_.p3_sumcheck.constraints.mirror.Statements.Fits (y : List EF) : Statements F EF → Prop
  | .Eq s => ∀ p ∈ s.points, p.length = y.length
  | .Select _ => True

theorem mapM_eval_eq : ∀ (ps : List (List EF)) (y : List EF), (∀ p ∈ ps, p.length = y.length) →
    ps.mapM (fun p => Point.eval_eq p y) = some (ps.map fun p => eq p y)
  | [], _, _ => rfl
  | q :: qs, y, h => by
    have hq := eval_eq_eq (F := EF) (h q (by simp))
    rw [Algebra.algebraMap_self, RingHom.coe_id, List.map_id] at hq
    simp [List.mapM_cons, hq, mapM_eval_eq qs y fun t ht => h t (by simp [ht])]

theorem _root_.p3_sumcheck.constraints.mirror.Statements.weights_at_eq {s : Statements F EF} {y : List EF}
    (h : s.Fits y) : s.weights_at y = some (s.weights y) := by
  cases s with
  | Eq s =>
    simp only [Statements.weights_at, EqStatement.weights_at, Statements.weights]
    exact mapM_eval_eq _ y h
  | Select s =>
    simp only [Statements.weights_at, SelectStatement.weights_at, Statements.weights, eval_select_eq,
      sel_eq_mle]

theorem _root_.p3_sumcheck.constraints.mirror.Statements.length_weights {s : Statements F EF} (y : List EF)
    (h : s.WF) : (s.weights y).length = s.evals.length := by
  cases s <;> simpa [Statements.weights, Statements.evals, Statements.WF] using h

theorem foldlM_value (γ : EF) (p : ℕ) (y : List EF) : ∀ (l : List (Statements F EF)) (a : EF) (shift : ℕ),
    (∀ s ∈ l, s.WF ∧ s.Fits y) →
    l.foldlM (fun (acc : EF × ℕ) (s : Statements F EF) => do
      let w ← s.weights_at y
      pure (acc.1 + dot w (powers γ (p + acc.2) w.length), acc.2 + s.len)) (a, shift) =
      some (a + dot (l.flatMap (Statements.weights y)) (powers γ (p + shift) (l.flatMap Statements.evals).length),
        shift + (l.flatMap Statements.evals).length)
  | [], a, shift, _ => by simp [dot]
  | s :: l, a, shift, h => by
    obtain ⟨hw, hf⟩ := h s (by simp)
    rw [List.foldlM_cons, Statements.weights_at_eq hf]
    simp only [Option.bind_eq_bind, Option.pure_def, Option.bind_some]
    have ih := foldlM_value γ p y l
    simp only [Option.bind_eq_bind, Option.pure_def] at ih
    rw [Statements.length_weights y hw, Statements.len_eq_of_WF hw, ih _ _ fun t ht => h t (by simp [ht])]
    simp only [List.flatMap_cons, List.length_append, powers_add, add_assoc]
    rw [dot_append (by rw [length_powers, Statements.length_weights y hw])]

/-- A constraint's weight at y: every point's weight against its power, the groups in order. -/
theorem constraintValue_eq (c : Constraint F EF) (y : List EF) (h : ∀ s ∈ c.statements, s.WF ∧ s.Fits y) :
    constraintValue c y = some (dot (c.statements.flatMap (Statements.weights y))
      (powers c.challenge c.initial_power (c.statements.flatMap Statements.evals).length)) := by
  rw [constraintValue, foldlM_value c.challenge c.initial_power y _ _ _ h]
  simp

/-- The closed form of one constraint's weight at y. -/
def weightAt (c : Constraint F EF) (y : List EF) : EF :=
  dot (c.statements.flatMap (Statements.weights y))
    (powers c.challenge c.initial_power (c.statements.flatMap Statements.evals).length)

/-- The constraint is well formed and its points fit the last num_variables coordinates of r. -/
def FitsEnd (r : List EF) (c : Constraint F EF) : Prop :=
  c.num_variables ≤ r.length ∧ ∀ s ∈ c.statements, s.WF ∧ s.Fits (r.drop (r.length - c.num_variables))

theorem mapM_prefix (r : List EF) : ∀ (cs : List (Constraint F EF)), (∀ c ∈ cs, FitsEnd r c) →
    cs.mapM (fun c => (subpoint r.reverse c.num_variables).bind fun sub => constraintValue c sub.reverse) =
      some (cs.map fun c => weightAt c (r.drop (r.length - c.num_variables)))
  | [], _ => rfl
  | c :: cs, h => by
    obtain ⟨hn, hs⟩ := h c (by simp)
    have hsub : subpoint r.reverse c.num_variables = some (r.drop (r.length - c.num_variables)).reverse := by
      simp [subpoint, hn, List.take_reverse]
    simp only [List.mapM_cons, hsub, Option.bind_eq_bind, Option.bind_some, List.reverse_reverse,
      constraintValue_eq c _ hs, mapM_prefix r cs fun t ht => h t (by simp [ht]), List.map_cons]
    rfl

/-- eval_constraints_poly with prefix binding: the sum of each constraint's weight at the last num_variables coordinates of the point. -/
theorem eval_constraints_poly_prefix (r : List EF) (cs : List (Constraint F EF)) (h : ∀ c ∈ cs, FitsEnd r c) :
    VariableOrder.Prefix.eval_constraints_poly cs r =
      some (cs.map fun c => weightAt c (r.drop (r.length - c.num_variables))).sum := by
  simp only [VariableOrder.eval_constraints_poly, Option.bind_eq_bind, mapM_prefix r cs h]
  rfl

end Plonky3Lean.Proofs.Whir
