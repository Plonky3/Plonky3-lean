module

public import Plonky3Lean.Proofs.Air.Symbolic

@[expose] public section

/-!
# Virtual columns

A virtual column is a constant plus weighted columns of a preprocessed row and a main row.

In a commutative ring it evaluates to that affine combination when every column is in range.

Otherwise it panics.

On the symbolic builder it denotes the same combination of the polynomial variables.
-/

set_option linter.unusedSectionVars false

namespace Plonky3Lean.Proofs.Air

open p3_air.symbolic.mirror p3_air.builder.mirror Plonky3Lean.Spec.Air

variable {F : Type _} [Field F] [DecidableEq F]

/-- The ring operations of R and the embedding of F, as a builder's expression algebra. -/
def ringOps (R : Type _) [CommRing R] [Algebra F R] : ExprOps F R :=
  ⟨(· + ·), (· - ·), (· * ·), (- ·), algebraMap F R⟩

theorem foldlM_apply {R V : Type _} [CommRing R] [Algebra F R] (into : V → R)
    (preprocessed main : List V) (val : PairCol → V) (cws : List (PairCol × F))
    (h : ∀ cw ∈ cws, cw.1.get preprocessed main = some (val cw.1)) (acc : R) :
    cws.foldlM (fun acc (cw : PairCol × F) => do
        let v ← cw.1.get preprocessed main
        pure ((ringOps (F := F) R).add acc ((ringOps (F := F) R).mul (into v) ((ringOps (F := F) R).const cw.2)))) acc =
      some (acc + (cws.map fun (cw : PairCol × F) => into (val cw.1) * algebraMap F R cw.2).sum) := by
  induction cws generalizing acc with
  | nil => simp
  | cons cw cws ih =>
    simp only [List.mem_cons, forall_eq_or_imp] at h
    have ih' := ih h.2 ((ringOps (F := F) R).add acc
      ((ringOps (F := F) R).mul (into (val cw.1)) ((ringOps (F := F) R).const cw.2)))
    simp only [Option.bind_eq_bind] at ih'
    simp only [List.foldlM_cons, h.1, Option.bind_eq_bind, Option.bind_some]
    rw [show (pure _ : Option R) = some _ from rfl, Option.bind_some, ih']
    simp [ringOps, add_assoc]

/-- A virtual column with every column in range evaluates to its constant plus the weighted columns. -/
theorem apply_eq {R V : Type _} [CommRing R] [Algebra F R] (into : V → R) (vc : VirtualPairCol F)
    (preprocessed main : List V) (val : PairCol → V)
    (h : ∀ cw ∈ vc.column_weights, cw.1.get preprocessed main = some (val cw.1)) :
    vc.apply (ringOps (F := F) R) into preprocessed main =
      some (algebraMap F R vc.constant +
        (vc.column_weights.map fun cw => into (val cw.1) * algebraMap F R cw.2).sum) :=
  foldlM_apply into preprocessed main val vc.column_weights h _

theorem foldlM_apply_none {R V : Type _} [CommRing R] [Algebra F R] (into : V → R)
    (preprocessed main : List V) (cws : List (PairCol × F))
    (h : ∃ cw ∈ cws, cw.1.get preprocessed main = none) (acc : R) :
    cws.foldlM (fun acc (cw : PairCol × F) => do
        let v ← cw.1.get preprocessed main
        pure ((ringOps (F := F) R).add acc ((ringOps (F := F) R).mul (into v) ((ringOps (F := F) R).const cw.2)))) acc =
      none := by
  induction cws generalizing acc with
  | nil => simp at h
  | cons cw cws ih =>
    simp only [List.mem_cons, exists_eq_or_imp] at h
    rcases hc : cw.1.get preprocessed main with _ | v
    · simp [hc]
    · rw [hc] at h
      simp only [reduceCtorEq, false_or] at h
      have ih' := ih h ((ringOps (F := F) R).add acc
        ((ringOps (F := F) R).mul (into v) ((ringOps (F := F) R).const cw.2)))
      simp only [Option.bind_eq_bind] at ih'
      simp only [List.foldlM_cons, hc, Option.bind_eq_bind, Option.bind_some]
      rw [show (pure _ : Option R) = some _ from rfl, Option.bind_some, ih']

/-- A virtual column with a column out of range panics. -/
theorem apply_eq_none {R V : Type _} [CommRing R] [Algebra F R] (into : V → R)
    (vc : VirtualPairCol F) (preprocessed main : List V)
    (h : ∃ cw ∈ vc.column_weights, cw.1.get preprocessed main = none) :
    vc.apply (ringOps (F := F) R) into preprocessed main = none :=
  foldlM_apply_none into preprocessed main vc.column_weights h _

end Plonky3Lean.Proofs.Air
