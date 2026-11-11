module

public import Plonky3Lean.Proofs.Air.Degree
public import Plonky3Lean.Proofs.Air.Semantics
public import CompPoly.Fields.BabyBear.Basic

@[expose] public section

/-!
# An AIR with two transition factors

The AIR asserts a^2 = b on transition rows, through the transition filter applied twice.

The pinned quotient sizing gives it one quotient chunk, from its degree multiple 2.

Its constraint polynomial can have degree 2n, which one chunk of n coefficients cannot hold.

So an honest prover's quotient does not fit, and verification of an honest proof fails.
-/

set_option linter.unusedSectionVars false

namespace Plonky3Lean.Proofs.Air

open p3_air.symbolic.mirror p3_air.builder.mirror p3_air.air.mirror Plonky3Lean.Spec.Air
open SymbolicExpr

variable {F : Type} [Field F] [DecidableEq F]

/-- The transition selector, and the first two main columns of the current row. -/
abbrev symT : SymbolicExpression F := .Leaf .IsTransition
abbrev symA : SymbolicExpression F := .Leaf (.Variable ⟨.Main 0, 0⟩)
abbrev symB : SymbolicExpression F := .Leaf (.Variable ⟨.Main 0, 1⟩)

/-- The evaluation: read a and b from the current row, and assert a^2 - b through two transition filters. -/
def squareEval : AirEval F := fun {_ _} B s =>
  match (B.main s).current with
  | a :: b :: _ => ((B.when_transition s).when_transition s).assert_eq s (B.mul a a) b
  | _ => s

theorem squareEval_parametric : IsParametric (squareEval (F := F)) := by
  intro E₁ S₁ E₂ S₂ B₁ B₂ R Q h s₁ s₂ hs
  have hm := h.main_current hs
  unfold squareEval
  beta_reduce
  generalize (B₁.main s₁).current = l₁ at hm ⊢
  generalize (B₂.main s₂).current = l₂ at hm ⊢
  rcases hm with _ | ⟨ha, _ | ⟨hb, -⟩⟩
  · exact hs
  · exact hs
  · exact h.assert_zero hs (h.mul (h.is_transition hs) (h.mul (h.is_transition hs)
      (h.sub (h.mul ha ha) hb)))

/-- The AIR: two main columns and the nested transition constraint. -/
def squareAir : Air F where
  width := 2
  eval := squareEval
  parametric := squareEval_parametric

/-- Its one symbolic constraint: T (T (a a - b)). -/
theorem squareAir_constraints :
    (squareAir (F := F)).eval (symbolicBuilder (AirLayout.from_air (squareAir (F := F)))) [] =
      [.Mul symT (.Mul symT (.Sub (.Mul symA symA 2) symB 2) 2) 2] := rfl

/-- Its largest constraint degree is the degree multiple 2. -/
theorem squareAir_max_degree (n : ℕ) :
    get_max_constraint_degree (squareAir (F := F)) (AirLayout.from_air (squareAir (F := F))) n = .ok 2 := rfl

/-- The quotient sizing gives 2^0 = 1 chunk. -/
theorem squareAir_log_quotient_degree (n : ℕ) :
    get_log_quotient_degree (squareAir (F := F)) (AirLayout.from_air (squareAir (F := F))) n 0 = .ok 0 := rfl

/-- Its constraint has two transition selectors along a product. -/
theorem squareAir_transitionCount :
    transitionCount (.Mul symT (.Mul symT (.Sub (.Mul symA symA 2) symB 2) 2) 2 :
      SymbolicExpression F) = 2 := rfl

/-- An assignment within the degree bounds: X for the transition selector, X^(n-1) for column a. -/
noncomputable def sigmaSquare (n : ℕ) : Var → Polynomial F := fun v =>
  if v = .isTransition then .X
  else if v = .main 0 0 then .X ^ (n - 1) else 0

theorem degreeBounds_sigmaSquare (n : ℕ) (periods : List ℕ) :
    DegreeBounds (sigmaSquare (F := F) n) n periods where
  main o c := by unfold sigmaSquare; split_ifs <;> simp_all
  prep o c := by simp [sigmaSquare]
  pub j := by simp [sigmaSquare]
  periodic j p _ _ _ := by simp [sigmaSquare]
  periodic_default j := by simp [sigmaSquare]
  isFirstRow := by simp [sigmaSquare]
  isLastRow := by simp [sigmaSquare]
  isTransition := by simp [sigmaSquare]

/-- The constraint polynomial under that assignment is X^(2n). -/
theorem natDegree_squareAir (hn : 1 ≤ n) :
    (constraintPoly (sigmaSquare (F := F) n)
      (toPoly (.Mul symT (.Mul symT (.Sub (.Mul symA symA 2) symB 2) 2) 2))).natDegree =
      2 * n := by
  rw [constraintPoly_toPoly]
  simp only [denote, leafPoly, varPoly, MvPolynomial.aeval_X, sigmaSquare]
  simp
  omega

/-- The single quotient chunk the sizing gives cannot hold that polynomial, on any trace length. -/
theorem squareAir_quotient_overflows (hn : 1 ≤ n) :
    ¬ FitsChunks n (2 ^ 0) (constraintPoly (sigmaSquare (F := F) n)
      (toPoly (.Mul symT (.Mul symT (.Sub (.Mul symA symA 2) symB 2) 2) 2))) := by
  rw [FitsChunks, natDegree_squareAir hn]
  omega

end Plonky3Lean.Proofs.Air
