/-
Transcriptions of constraints/mod.rs and the equality and selector statements of constraints/statement/.

A selector statement holds scalar points only, the case of two-adic domains.

The successor statement is not transcribed.
-/
module

public import P3MultilinearUtil.Point

@[expose] public section

namespace p3_sumcheck.constraints.mirror

open p3_multilinear_util.point.mirror

variable {F EF : Type _} [Field F] [Field EF] [Algebra F EF]

/-- The challenge powers gamma^shift, gamma^(shift + 1), ..., n of them. -/
def powers (gamma : EF) (shift n : ℕ) : List EF := (List.range n).map fun i => gamma ^ (shift + i)

/-- dot_product: the sum of the pairwise products, up to the shorter list. -/
def dot (a b : List EF) : EF := (List.zipWith (· * ·) a b).sum

/-- EqStatement: claims p(z_i) = s_i at points of num_variables coordinates. -/
structure EqStatement (EF : Type _) where
  num_variables : ℕ
  points : List (List EF)
  evaluations : List EF

/-- SelectStatement: claims sum_b p(b) z_i^b = s_i.

The points z_i are scalars of the base field. -/
structure SelectStatement (F EF : Type _) where
  num_variables : ℕ
  vars : List F
  evaluations : List EF

/-- EqStatement::len: the number of points. -/
def EqStatement.len (s : EqStatement EF) : ℕ := s.points.length

/-- SelectStatement::len: the number of claimed evaluations. -/
def SelectStatement.len (s : SelectStatement F EF) : ℕ := s.evaluations.length

/-- EqStatement::combine_evals: add sum_i gamma^(shift + i) s_i. -/
def EqStatement.combine_evals (s : EqStatement EF) (claimed gamma : EF) (shift : ℕ) : EF :=
  claimed + dot s.evaluations (powers gamma shift s.evaluations.length)

/-- SelectStatement::combine_evals: add sum_i gamma^(shift + i) s_i.

It uses one power per claimed evaluation. -/
def SelectStatement.combine_evals (s : SelectStatement F EF) (claimed gamma : EF) (shift : ℕ) : EF :=
  claimed + dot s.evaluations (powers gamma shift s.len)

/-- EqStatement::weights_at: eq(z_i, x) for each point.

It asserts equal lengths. -/
def EqStatement.weights_at (s : EqStatement EF) (row : List EF) : Option (List EF) :=
  s.points.mapM fun p => Point.eval_eq p row

/-- SelectStatement::weights_at: the selector of each scalar point at x. -/
def SelectStatement.weights_at (s : SelectStatement F EF) (row : List EF) : List EF :=
  s.vars.map fun v => Point.eval_select v row

/-- Horner's rule: c_0 + x (c_1 + x (c_2 + ...)).

It evaluates the univariate polynomial with coefficients c at x. -/
def horner (c : List EF) (x : EF) : EF := c.foldr (fun a acc => a + x * acc) 0

/-- SelectStatement::verify: each claimed value matches the polynomial at its point.

The polynomial is given by its coefficient table. -/
def SelectStatement.verify [DecidableEq EF] (s : SelectStatement F EF) (poly : List EF) : Bool :=
  (s.vars.zip s.evaluations).all fun ve => horner poly (algebraMap F EF ve.1) == ve.2

/-- A statement group of a constraint. -/
inductive Statements (F EF : Type _) where
  | Eq (s : EqStatement EF)
  | Select (s : SelectStatement F EF)

/-- Statements::num_variables. -/
def Statements.num_variables : Statements F EF → ℕ
  | .Eq s => s.num_variables
  | .Select s => s.num_variables

/-- Statements::len. -/
def Statements.len : Statements F EF → ℕ
  | .Eq s => s.len
  | .Select s => s.len

/-- Statements::combine_evals. -/
def Statements.combine_evals : Statements F EF → EF → EF → ℕ → EF
  | .Eq s => s.combine_evals
  | .Select s => s.combine_evals

/-- The weights of a statement group at a point, which panics on a point of another length. -/
def Statements.weights_at : Statements F EF → List EF → Option (List EF)
  | .Eq s, row => s.weights_at row
  | .Select s, row => some (s.weights_at row)

/-- Constraint: statement groups batched by the powers of one challenge.

The powers start at an initial exponent. -/
structure Constraint (F EF : Type _) where
  num_variables : ℕ
  statements : List (Statements F EF)
  challenge : EF
  initial_power : ℕ

/-- Constraint::new, which asserts every group has the constraint's variable count. -/
def Constraint.new (challenge : EF) (num_variables : ℕ) (statements : List (Statements F EF)) :
    Option (Constraint F EF) :=
  if statements.all (·.num_variables == num_variables) then some ⟨num_variables, statements, challenge, 0⟩
  else none

/-- Constraint::new_with_existing_claim: the same, with the powers starting at 1. -/
def Constraint.new_with_existing_claim (challenge : EF) (num_variables : ℕ)
    (statements : List (Statements F EF)) : Option (Constraint F EF) :=
  (Constraint.new challenge num_variables statements).map fun c => { c with initial_power := 1 }

/-- Constraint::combine_evals: each group adds its claims.

Its powers continue from the previous group's. -/
def Constraint.combine_evals (c : Constraint F EF) (claimed : EF) : EF :=
  (c.statements.foldl (fun (acc : EF × ℕ) s =>
    (s.combine_evals acc.1 c.challenge acc.2, acc.2 + s.len)) (claimed, c.initial_power)).1

/-- How the folding randomness binds the variables. -/
inductive VariableOrder where
  | Prefix
  | Suffix

/-- Point::get_subpoint_over_range(..n), which panics past the end. -/
def subpoint (p : List EF) (n : ℕ) : Option (List EF) := if n ≤ p.length then some (p.take n) else none

/-- One constraint's term of eval_constraints_poly.

Each group's weights are dotted against the powers after the previous groups. -/
def constraintValue (c : Constraint F EF) (local_challenge : List EF) : Option EF :=
  (c.statements.foldlM (fun (acc : EF × ℕ) (s : Statements F EF) => do
    let w ← s.weights_at local_challenge
    pure (acc.1 + dot w (powers c.challenge (c.initial_power + acc.2) w.length), acc.2 + s.len))
    (0, 0)).map Prod.fst

/-- VariableOrder::eval_constraints_poly: the batched weight of every constraint.

Each is read at the end of the point it was formed before. -/
def VariableOrder.eval_constraints_poly (order : VariableOrder) (constraints : List (Constraint F EF))
    (challenge : List EF) : Option EF := do
  let reversed := challenge.reverse
  let vals ← constraints.mapM fun c => do
    let sub ← subpoint reversed c.num_variables
    let local_challenge := match order with
      | .Prefix => sub.reverse
      | .Suffix => sub
    constraintValue c local_challenge
  pure vals.sum

end p3_sumcheck.constraints.mirror
