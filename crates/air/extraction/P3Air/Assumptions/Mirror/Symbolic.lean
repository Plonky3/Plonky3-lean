/-
Transcriptions of the symbolic expressions: leaves, nodes, the simplifying operators and the degree walks.

These do not extract: they are generic over the field traits, which aeneas rejects.

Each definition transcribes one Rust item, named in the crate's mirror entries.

What a transcription abstracts:

* the field is a mathlib field F, and the extension field a type EF with a partial map back to F;
* a word is a natural number;
* a shared child is a child, and the memoised walk is the plain recursion it caches;
* the leaf trait is a class with the same items.

Branches and the order of checks are kept.
-/
module

public import Mathlib.Algebra.Field.Basic

@[expose] public section

namespace p3_air.symbolic.mirror

/-- Where a base variable lives: a trace column at a row offset, a periodic column, or a public value. -/
inductive BaseEntry where
  | Preprocessed (offset : ℕ)
  | Main (offset : ℕ)
  | Periodic
  | Public
  deriving DecidableEq

/-- Where an extension variable lives: a permutation column at a row offset, a challenge, or a permutation value. -/
inductive ExtEntry where
  | Permutation (offset : ℕ)
  | Challenge
  | PermutationValue
  deriving DecidableEq

/-- A base variable: an entry and an index into it. -/
structure SymbolicVariable where
  entry : BaseEntry
  index : ℕ
  deriving DecidableEq

/-- An extension variable: an entry and an index into it. -/
structure SymbolicVariableExt where
  entry : ExtEntry
  index : ℕ
  deriving DecidableEq

/-- Trace columns and periodic columns count 1, public values 0. -/
def SymbolicVariable.degree_multiple (v : SymbolicVariable) : ℕ :=
  match v.entry with
  | .Preprocessed _ | .Main _ | .Periodic => 1
  | .Public => 0

/-- The degree as a polynomial on a trace of the given length.

A trace column has degree n - 1.

A periodic column of period p has degree n - n / p, with p clamped to n and a missing period read as n. -/
def SymbolicVariable.poly_degree (v : SymbolicVariable) (trace_len : ℕ)
    (periodic_periods : List ℕ) : ℕ :=
  match v.entry with
  | .Preprocessed _ | .Main _ => trace_len - 1
  | .Periodic =>
    let period := min (periodic_periods[v.index]?.getD trace_len) trace_len
    match period with
    | 0 => trace_len - 1
    | p => trace_len - trace_len / p
  | .Public => 0

/-- Permutation columns count 1, challenges and permutation values 0. -/
def SymbolicVariableExt.degree_multiple (v : SymbolicVariableExt) : ℕ :=
  match v.entry with
  | .Permutation _ => 1
  | .Challenge | .PermutationValue => 0

/-- A permutation column has degree n - 1, the rest degree 0. -/
def SymbolicVariableExt.poly_degree (v : SymbolicVariableExt) (trace_len : ℕ) : ℕ :=
  match v.entry with
  | .Permutation _ => trace_len - 1
  | .Challenge | .PermutationValue => 0

/-- An expression tree: leaves, and four nodes that cache their degree multiple. -/
inductive SymbolicExpr (A : Type _) where
  | Leaf (a : A)
  | Add (x y : SymbolicExpr A) (degree_multiple : ℕ)
  | Sub (x y : SymbolicExpr A) (degree_multiple : ℕ)
  | Neg (x : SymbolicExpr A) (degree_multiple : ℕ)
  | Mul (x y : SymbolicExpr A) (degree_multiple : ℕ)

/-- The leaf trait: degrees, and the constants a leaf can hold. -/
class SymLeaf (A : Type _) (F : outParam (Type _)) where
  degree_multiple : A → ℕ
  degree_multiple_with_transition : A → ℕ → ℕ
  poly_degree : A → ℕ → List ℕ → ℕ
  as_const : A → Option F
  from_const : F → A

namespace SymbolicExpr

variable {A F : Type _} [SymLeaf A F] [Field F] [DecidableEq F]

/-- The cached degree multiple, or the leaf's own. -/
def degree_multiple : SymbolicExpr A → ℕ
  | Leaf a => SymLeaf.degree_multiple a
  | Add _ _ d | Sub _ _ d | Neg _ d | Mul _ _ d => d

/-- The walk shared by the degree functions: max over sums, sum over products. -/
def degree_with (leaf_degree : A → ℕ) : SymbolicExpr A → ℕ
  | Leaf a => leaf_degree a
  | Add x y _ | Sub x y _ => max (x.degree_with leaf_degree) (y.degree_with leaf_degree)
  | Neg x _ => x.degree_with leaf_degree
  | Mul x y _ => x.degree_with leaf_degree + y.degree_with leaf_degree

/-- The degree multiple with each transition selector at the given degree, or the cached one for 0. -/
def degree_multiple_with_transition (e : SymbolicExpr A) (transition_degree : ℕ) : ℕ :=
  if transition_degree = 0 then e.degree_multiple
  else e.degree_with (SymLeaf.degree_multiple_with_transition · transition_degree)

/-- The degree as a polynomial on a trace of the given length. -/
def poly_degree (e : SymbolicExpr A) (trace_len : ℕ) (periodic_periods : List ℕ) : ℕ :=
  e.degree_with (SymLeaf.poly_degree · trace_len periodic_periods)

/-- The constant a leaf holds, none for a node. -/
def as_const : SymbolicExpr A → Option F
  | Leaf a => SymLeaf.as_const a
  | _ => none

/-- Addition: folds two constants, drops a zero, else a node. -/
def sym_add (x y : SymbolicExpr A) : SymbolicExpr A :=
  match x.as_const, y.as_const with
  | some a, some b => Leaf (SymLeaf.from_const (a + b))
  | _, _ =>
    if x.as_const.any (· = 0) then y
    else if y.as_const.any (· = 0) then x
    else Add x y (max x.degree_multiple y.degree_multiple)

/-- Negation: folds a constant, else a node. -/
def sym_neg (x : SymbolicExpr A) : SymbolicExpr A :=
  match x.as_const with
  | some c => Leaf (SymLeaf.from_const (-c))
  | none => Neg x x.degree_multiple

/-- Subtraction: folds two constants, turns 0 - y into -y, drops a zero subtrahend, else a node. -/
def sym_sub (x y : SymbolicExpr A) : SymbolicExpr A :=
  match x.as_const, y.as_const with
  | some a, some b => Leaf (SymLeaf.from_const (a - b))
  | _, _ =>
    if x.as_const.any (· = 0) then y.sym_neg
    else if y.as_const.any (· = 0) then x
    else Sub x y (max x.degree_multiple y.degree_multiple)

/-- Multiplication: folds two constants, absorbs a zero, drops a one, else a node. -/
def sym_mul (x y : SymbolicExpr A) : SymbolicExpr A :=
  match x.as_const, y.as_const with
  | some a, some b => Leaf (SymLeaf.from_const (a * b))
  | _, _ =>
    if x.as_const.any (· = 0) || y.as_const.any (· = 0) then Leaf (SymLeaf.from_const 0)
    else if x.as_const.any (· = 1) then y
    else if y.as_const.any (· = 1) then x
    else Mul x y (x.degree_multiple + y.degree_multiple)

/-- The constant c as an expression, the embedding behind ZERO, ONE and from_prime_subfield. -/
def const (c : F) : SymbolicExpr A := Leaf (SymLeaf.from_const c)

end SymbolicExpr

/-- A base leaf: a variable, one of the three selectors, or a constant. -/
inductive BaseLeaf (F : Type _) where
  | Variable (v : SymbolicVariable)
  | IsFirstRow
  | IsLastRow
  | IsTransition
  | Constant (c : F)

/-- Base-field symbolic expressions. -/
abbrev SymbolicExpression (F : Type _) := SymbolicExpr (BaseLeaf F)

/-- The base leaf trait.

* A variable has its own degrees.
* The boundary selectors count 1 and have degree n - 1.
* The transition selector counts 0, or the given transition degree, and has degree 1.
* A constant counts 0. -/
instance instSymLeafBaseLeaf {F : Type _} : SymLeaf (BaseLeaf F) F where
  degree_multiple
    | .Variable v => v.degree_multiple
    | .IsFirstRow | .IsLastRow => 1
    | .IsTransition | .Constant _ => 0
  degree_multiple_with_transition l t :=
    match l with
    | .IsTransition => t
    | .Variable v => v.degree_multiple
    | .IsFirstRow | .IsLastRow => 1
    | .Constant _ => 0
  poly_degree l trace_len periodic_periods :=
    match l with
    | .Variable v => v.poly_degree trace_len periodic_periods
    | .IsFirstRow | .IsLastRow => trace_len - 1
    | .IsTransition => 1
    | .Constant _ => 0
  as_const
    | .Constant c => some c
    | _ => none
  from_const := .Constant

/-- An extension field with the test for lying in the base field and the coordinate that then holds the value. -/
class InBase (F EF : Type _) where
  as_base : EF → Option F

/-- An extension leaf: a base expression, an extension variable, or an extension constant. -/
inductive ExtLeaf (F EF : Type _) where
  | Base (e : SymbolicExpression F)
  | ExtVariable (v : SymbolicVariableExt)
  | ExtConstant (c : EF)

/-- Extension-field symbolic expressions. -/
abbrev SymbolicExpressionExt (F EF : Type _) := SymbolicExpr (ExtLeaf F EF)

/-- The extension leaf trait.

* A base expression has its own degrees, and holds a constant when it is a constant leaf.
* An extension variable has its own degrees.
* An extension constant counts 0, and holds a base constant when it lies in the base field. -/
instance instSymLeafExtLeaf {F EF : Type _} [InBase F EF] : SymLeaf (ExtLeaf F EF) F where
  degree_multiple
    | .Base e => e.degree_multiple
    | .ExtVariable v => v.degree_multiple
    | .ExtConstant _ => 0
  degree_multiple_with_transition l t :=
    match l with
    | .Base e => e.degree_multiple_with_transition t
    | .ExtVariable v => v.degree_multiple
    | .ExtConstant _ => 0
  poly_degree l trace_len periodic_periods :=
    match l with
    | .Base e => e.poly_degree trace_len periodic_periods
    | .ExtVariable v => v.poly_degree trace_len
    | .ExtConstant _ => 0
  as_const
    | .Base (.Leaf (.Constant c)) => some c
    | .ExtConstant ef => InBase.as_base ef
    | _ => none
  from_const c := .Base (.Leaf (.Constant c))

/-- The base expression behind an extension expression with no extension leaf, nodes and caches kept. -/
def SymbolicExpressionExt.to_base {F EF : Type _} :
    SymbolicExpressionExt F EF → Option (SymbolicExpression F)
  | .Leaf (.Base e) => some e
  | .Leaf (.ExtVariable _) | .Leaf (.ExtConstant _) => none
  | .Add x y d => do pure (.Add (← to_base x) (← to_base y) d)
  | .Sub x y d => do pure (.Sub (← to_base x) (← to_base y) d)
  | .Neg x d => do pure (.Neg (← to_base x) d)
  | .Mul x y d => do pure (.Mul (← to_base x) (← to_base y) d)

end p3_air.symbolic.mirror
