/-
Transcriptions of the AIR traits, the symbolic builder, the constraint degree, and the debug constraint checker.

These do not extract: they are generic over the field traits and over the builder, which aeneas rejects.

Each definition transcribes one Rust item, named in the crate's mirror entries.

What a transcription abstracts, beyond the builder transcriptions:

* an AIR's evaluation is a function generic in the builder's expression and state types;
* Rust makes such a function parametric, so it relates related builders; here that is a field the AIR proves;
* a row-major matrix is its width and its values, and its height is the number of whole rows;
* a symbolic window of width 0 is read as two empty rows, where the pinned Rust panics (upstream #2490 removed the panic);
* a constraint label is dropped, since the plain assertion passes an empty name;
* a panic is an error message.

Loops, branches and the order of checks are kept.
-/
module

public import P3Air.Assumptions.Mirror.Builder
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Data.Nat.Log
public import Mathlib.Data.Nat.Size

@[expose] public section

namespace p3_air.air.mirror

open p3_air.symbolic.mirror p3_air.builder.mirror

/-! ## Matrices and boundary cells -/

/-- A row-major matrix: its width and its values. -/
structure Mat (T : Type _) where
  width : ℕ
  values : List T

namespace Mat

variable {T : Type _}

/-- The number of whole rows, 0 for width 0. -/
def height (m : Mat T) : ℕ := if m.width = 0 then 0 else m.values.length / m.width

/-- Row r: the width values from position r w. -/
def row (m : Mat T) (r : ℕ) : List T := (m.values.drop (r * m.width)).take m.width

/-- The entry at (r, c), none outside the matrix. -/
def get (m : Mat T) (r c : ℕ) : Option T :=
  if r < m.height ∧ c < m.width then m.values[r * m.width + c]? else none

end Mat

/-- The end of the trace a boundary cell sits on. -/
inductive BoundaryEnd where
  | First
  | Last
  deriving DecidableEq

/-- A main-trace cell whose value is a public input. -/
structure BoundaryPublic where
  column : ℕ
  «end» : BoundaryEnd
  public_value : ℕ
  deriving DecidableEq

/-- The row of a boundary cell: 0 or height - 1, and a panic for height 0. -/
def BoundaryPublic.row (cell : BoundaryPublic) (height : ℕ) : Option ℕ :=
  if height > 0 then
    match cell.end with
    | .First => some 0
    | .Last => some (height - 1)
  else none

/-- Why a boundary declaration is rejected. -/
inductive BoundaryIoError where
  | ColumnOutOfRange (column width : ℕ)
  | PublicValueOutOfRange (index num_public_values : ℕ)
  | DuplicateCell (column : ℕ) (e : BoundaryEnd)
  deriving DecidableEq

/-- Check each cell in order: column in range, public value in range, and no earlier cell on the same column and end. -/
def validate (cells : List BoundaryPublic) (width num_public_values : ℕ) :
    Except BoundaryIoError Unit :=
  cells.zipIdx.forM fun (cell, index) => do
    if cell.column ≥ width then throw (.ColumnOutOfRange cell.column width)
    if cell.public_value ≥ num_public_values then
      throw (.PublicValueOutOfRange cell.public_value num_public_values)
    if (cells.take index).any (fun earlier => earlier.column = cell.column ∧ earlier.end = cell.end) then
      throw (.DuplicateCell cell.column cell.end)

/-! ## AIRs -/

/-- The evaluation of an AIR: a program over any builder, from a state to a state. -/
abbrev AirEval (F : Type) := ∀ {E S : Type}, AirBuilder F E S → S → S

/-- Two builders whose expressions are related by R and whose states are related by Q.

* The operations map related arguments to related results, and constants to related constants.
* The windows, public values and periodic values of related states are related entrywise.
* The selectors of related states are related.
* Asserting related expressions from related states gives related states.
* The arities agree. -/
structure BuilderRel {F E₁ S₁ E₂ S₂ : Type} (B₁ : AirBuilder F E₁ S₁) (B₂ : AirBuilder F E₂ S₂)
    (R : E₁ → E₂ → Prop) (Q : S₁ → S₂ → Prop) : Prop where
  add : ∀ {a b a' b'}, R a b → R a' b' → R (B₁.add a a') (B₂.add b b')
  sub : ∀ {a b a' b'}, R a b → R a' b' → R (B₁.sub a a') (B₂.sub b b')
  mul : ∀ {a b a' b'}, R a b → R a' b' → R (B₁.mul a a') (B₂.mul b b')
  neg : ∀ {a b}, R a b → R (B₁.neg a) (B₂.neg b)
  const : ∀ c, R (B₁.const c) (B₂.const c)
  main_current : ∀ {s₁ s₂}, Q s₁ s₂ → List.Forall₂ R (B₁.main s₁).current (B₂.main s₂).current
  main_next : ∀ {s₁ s₂}, Q s₁ s₂ → List.Forall₂ R (B₁.main s₁).next (B₂.main s₂).next
  preprocessed_current : ∀ {s₁ s₂}, Q s₁ s₂ →
    List.Forall₂ R (B₁.preprocessed s₁).current (B₂.preprocessed s₂).current
  preprocessed_next : ∀ {s₁ s₂}, Q s₁ s₂ →
    List.Forall₂ R (B₁.preprocessed s₁).next (B₂.preprocessed s₂).next
  public_values : ∀ {s₁ s₂}, Q s₁ s₂ → List.Forall₂ R (B₁.public_values s₁) (B₂.public_values s₂)
  periodic_values : ∀ {s₁ s₂}, Q s₁ s₂ →
    List.Forall₂ R (B₁.periodic_values s₁) (B₂.periodic_values s₂)
  is_first_row : ∀ {s₁ s₂}, Q s₁ s₂ → R (B₁.is_first_row s₁) (B₂.is_first_row s₂)
  is_last_row : ∀ {s₁ s₂}, Q s₁ s₂ → R (B₁.is_last_row s₁) (B₂.is_last_row s₂)
  is_transition : ∀ {s₁ s₂}, Q s₁ s₂ → R (B₁.is_transition s₁) (B₂.is_transition s₂)
  assert_zero : ∀ {s₁ s₂ a b}, Q s₁ s₂ → R a b → Q (B₁.assert_zero s₁ a) (B₂.assert_zero s₂ b)
  window : B₁.window = B₂.window

/-- An evaluation that maps related builders and related states to related states. -/
def IsParametric {F : Type} (eval : AirEval F) : Prop :=
  ∀ {E₁ S₁ E₂ S₂ : Type} (B₁ : AirBuilder F E₁ S₁) (B₂ : AirBuilder F E₂ S₂)
    (R : E₁ → E₂ → Prop) (Q : S₁ → S₂ → Prop), BuilderRel B₁ B₂ R Q →
    ∀ s₁ s₂, Q s₁ s₂ → Q (eval B₁ s₁) (eval B₂ s₂)

/-- An AIR: the base-AIR items the checker and the symbolic builder read, and its evaluation. -/
structure Air (F : Type) where
  width : ℕ
  preprocessed_trace : Option (Mat F) := none
  preprocessed_width : ℕ := 0
  periodic_columns : List (List F) := []
  num_periodic_columns : ℕ := 0
  num_public_values : ℕ := 0
  public_boundary_io : List BoundaryPublic := []
  max_constraint_degree : Option ℕ := none
  eval : AirEval F
  parametric : IsParametric eval

/-- The periodic values at a row: entry r mod len of each periodic column. -/
def Air.periodic_values {F : Type} [Inhabited F] (air : Air F) (row_index : ℕ) : List F :=
  air.periodic_columns.map fun col => col[row_index % col.length]!

/-! ## Resolving a symbolic expression against a builder -/

variable {F : Type} [Field F] [DecidableEq F]

/-- The value of a symbolic expression in a builder's algebra, leaf by leaf.

A row offset other than 0 or 1, or an index out of range, panics. -/
def resolve {E S : Type} (B : AirBuilder F E S) (s : S) : SymbolicExpression F → Option E
  | .Leaf (.Variable v) =>
    match v.entry with
    | .Main offset =>
      match offset with
      | 0 => (B.main s).current[v.index]?
      | 1 => (B.main s).next[v.index]?
      | _ => none
    | .Preprocessed offset =>
      match offset with
      | 0 => (B.preprocessed s).current[v.index]?
      | 1 => (B.preprocessed s).next[v.index]?
      | _ => none
    | .Public => (B.public_values s)[v.index]?
    | .Periodic => (B.periodic_values s)[v.index]?
  | .Leaf .IsFirstRow => some (B.is_first_row s)
  | .Leaf .IsLastRow => some (B.is_last_row s)
  | .Leaf .IsTransition => B.is_transition_window s 2
  | .Leaf (.Constant c) => some (B.const c)
  | .Add x y _ => do pure (B.add (← resolve B s x) (← resolve B s y))
  | .Sub x y _ => do pure (B.sub (← resolve B s x) (← resolve B s y))
  | .Neg x _ => do pure (B.neg (← resolve B s x))
  | .Mul x y _ => do pure (B.mul (← resolve B s x) (← resolve B s y))

/-! ## The symbolic builder -/

/-- The widths and counts a symbolic builder is sized by. -/
structure AirLayout where
  preprocessed_width : ℕ := 0
  main_width : ℕ := 0
  num_public_values : ℕ := 0
  permutation_width : ℕ := 0
  num_permutation_challenges : ℕ := 0
  num_permutation_values : ℕ := 0
  num_periodic_columns : ℕ := 0

/-- The layout the AIR's own items give. -/
def AirLayout.from_air (air : Air F) : AirLayout where
  preprocessed_width := air.preprocessed_width
  main_width := air.width
  num_public_values := air.num_public_values
  num_periodic_columns := air.num_periodic_columns

/-- The main width, public values and periodic columns must match the AIR. -/
def AirLayout.validate_against_air (layout : AirLayout) (air : Air F) : Except String Unit := do
  if layout.main_width ≠ air.width then throw "AirLayout main_width does not match AIR width"
  if layout.num_public_values ≠ air.num_public_values then
    throw "AirLayout num_public_values does not match AIR"
  if layout.num_periodic_columns ≠ air.num_periodic_columns then
    throw "AirLayout num_periodic_columns does not match AIR"

/-- The variables of one row offset of a trace of the given width. -/
def windowRow (entry : ℕ → BaseEntry) (offset width : ℕ) : List (SymbolicExpression F) :=
  (List.range width).map fun index => .Leaf (.Variable ⟨entry offset, index⟩)

/-- The symbolic builder: variables for every cell of the window, and a state that records each asserted expression. -/
def symbolicBuilder (layout : AirLayout) :
    AirBuilder F (SymbolicExpression F) (List (SymbolicExpression F)) where
  add := SymbolicExpr.sym_add
  sub := SymbolicExpr.sym_sub
  mul := SymbolicExpr.sym_mul
  neg := SymbolicExpr.sym_neg
  const := SymbolicExpr.const
  main _ := ⟨windowRow .Main 0 layout.main_width, windowRow .Main 1 layout.main_width⟩
  preprocessed _ := ⟨windowRow .Preprocessed 0 layout.preprocessed_width,
    windowRow .Preprocessed 1 layout.preprocessed_width⟩
  is_first_row _ := .Leaf .IsFirstRow
  is_last_row _ := .Leaf .IsLastRow
  is_transition _ := .Leaf .IsTransition
  assert_zero s x := s ++ [x]
  public_values _ := (List.range layout.num_public_values).map fun i => .Leaf (.Variable ⟨.Public, i⟩)
  periodic_values _ :=
    (List.range layout.num_periodic_columns).map fun i => .Leaf (.Variable ⟨.Periodic, i⟩)

/-- Validate the layout, evaluate the AIR on a fresh symbolic builder, and return what it asserted. -/
def get_symbolic_constraints (air : Air F) (layout : AirLayout) :
    Except String (List (SymbolicExpression F)) := do
  layout.validate_against_air air
  pure (air.eval (symbolicBuilder layout) [])

/-- The least d with poly_degree <= d (n - 1) + 1, dividing by 1 for n <= 1. -/
def constraint_degree_from_poly_degree (poly_degree trace_len : ℕ) : ℕ :=
  if poly_degree = 0 then 0
  else
    let denom := if trace_len > 1 then trace_len - 1 else 1
    (poly_degree - 1 + denom - 1) / denom

/-- The largest constraint degree.

Without periodic columns it is the largest cached degree multiple.

Otherwise it converts the largest polynomial degree. -/
def get_max_constraint_degree (air : Air F) (layout : AirLayout) (trace_len : ℕ) :
    Except String ℕ := do
  let base_constraints ← get_symbolic_constraints air layout
  if layout.num_periodic_columns = 0 then
    pure ((base_constraints.map SymbolicExpr.degree_multiple).foldr max 0)
  else
    let periodic_periods := air.periodic_columns.map List.length
    let base_degree :=
      (base_constraints.map (SymbolicExpr.poly_degree · trace_len periodic_periods)).foldr max 0
    pure (constraint_degree_from_poly_degree base_degree trace_len)

/-- ceil(log_2 n): the bit length of n - 1, which is 64 minus its leading zeros. -/
def log2_ceil_usize (n : ℕ) : ℕ := Nat.size (n - 1)

/-- log_2 of the quotient chunk count: the degree plus the ZK flag, padded to 2, minus 1, rounded up to a power of two.

The flag must be 0 or 1. -/
def get_log_quotient_degree (air : Air F) (layout : AirLayout) (trace_len is_zk : ℕ) :
    Except String ℕ := do
  if is_zk > 1 then throw "is_zk must be either 0 or 1"
  let degree := max (← get_max_constraint_degree air layout trace_len)
    (air.max_constraint_degree.getD 0)
  let constraint_degree := max (degree + is_zk) 2
  pure (log2_ceil_usize (constraint_degree - 1))

/-! ## The debug constraint checker -/

/-- A failed constraint: its row and its index within the row. -/
structure ConstraintFailure where
  row : ℕ
  constraint : ℕ
  deriving DecidableEq

/-- The debug builder's state: the row, the next constraint index, and the failures so far. -/
structure DebugState where
  row_index : ℕ
  constraint_index : ℕ
  failures : List ConstraintFailure

/-- A fresh debug state at a row. -/
def DebugState.new (row_index : ℕ) : DebugState := ⟨row_index, 0, []⟩

/-- Record a failure when the value is nonzero, then advance the constraint index. -/
def DebugState.assert_zero {T : Type _} [Zero T] [DecidableEq T] (s : DebugState) (x : T) :
    DebugState :=
  let failures :=
    if x ≠ 0 then s.failures ++ [⟨s.row_index, s.constraint_index⟩] else s.failures
  { s with failures, constraint_index := s.constraint_index + 1 }

/-- The debug builder at one row: concrete windows, public values, selectors and periodic values. -/
def debugBuilder (main preprocessed : RowWindow F) (public_values : List F)
    (is_first_row is_last_row is_transition : F) (periodic_row : List F) :
    AirBuilder F F DebugState where
  add := (· + ·)
  sub := (· - ·)
  mul := (· * ·)
  neg := (- ·)
  const := id
  main _ := main
  preprocessed _ := preprocessed
  is_first_row _ := is_first_row
  is_last_row _ := is_last_row
  is_transition _ := is_transition
  assert_zero := DebugState.assert_zero
  public_values _ := public_values
  periodic_values _ := periodic_row

/-- The debug builder with extension assertions: an extension value times a base condition embeds the condition. -/
def debugExtBuilder {EF : Type} [Field EF] [Algebra F EF] [DecidableEq EF]
    (main preprocessed : RowWindow F) (public_values : List F)
    (is_first_row is_last_row is_transition : F) (periodic_row : List F) :
    ExtensionBuilder F F EF DebugState where
  toAirBuilder := debugBuilder main preprocessed public_values is_first_row is_last_row
    is_transition periodic_row
  ext_sub := (· - ·)
  ext_mul_expr x c := x * algebraMap F EF c
  ext_one := 1
  assert_zero_ext := DebugState.assert_zero

/-- Every periodic column must have power-of-two length dividing the height. -/
def assert_periodic_column_shapes (air : Air F) (height : ℕ) : Except String Unit :=
  air.periodic_columns.forM fun column => do
    if ¬ (column.length ≠ 0 ∧ 2 ^ Nat.log 2 column.length = column.length) then
      throw "periodic column length is not a power of two"
    if height % column.length ≠ 0 then
      throw "periodic column length does not divide the trace height"

/-- The boundary cells whose trace value differs from their public value, with their rows.

An invalid declaration panics, and so does a cell on a trace of height 0. -/
def boundary_io_mismatches (air : Air F) (main : Mat F) (public_values : List F) :
    Except String (List (ℕ × ℕ)) := do
  match validate air.public_boundary_io main.width public_values.length with
  | .error _ => throw "invalid boundary declaration"
  | .ok () => pure ()
  let height := main.height
  let rows ← air.public_boundary_io.zipIdx.mapM fun (cell, index) => do
    let some row := cell.row height | throw "a boundary cell needs at least one trace row"
    let some value := main.get row cell.column | throw "row and column checked in range"
    let some expected := public_values[cell.public_value]? | throw "index out of bounds"
    pure (if value ≠ expected then some (index, row) else none)
  pure rows.reduceOption

/-- The two-row windows of a matrix at row r: row r and row r + 1 mod the height. -/
def rowPair (m : Mat F) (row_index height : ℕ) : RowWindow F :=
  ⟨m.row row_index, m.row ((row_index + 1) % height)⟩

/-- The debug builder of a trace at a row.

The selectors are 1 on the first row, 1 on the last row, and 1 off the last row. -/
def rowBuilder [Inhabited F] (air : Air F) (main : Mat F) (public_values : List F)
    (row_index : ℕ) : AirBuilder F F DebugState :=
  let height := main.height
  let preprocessed := match air.preprocessed_trace with
    | some prep => rowPair prep row_index height
    | none => ⟨[], []⟩
  debugBuilder (rowPair main row_index height) preprocessed public_values
    (if row_index = 0 then 1 else 0) (if row_index = height - 1 then 1 else 0)
    (if row_index ≠ height - 1 then 1 else 0) (air.periodic_values row_index)

/-- The debug check: the preprocessed height must match, the periodic shapes must be valid, every boundary cell must hold its public value, and every row must assert only zeros.

Each violation panics. -/
def check_constraints [Inhabited F] (air : Air F) (main : Mat F) (public_values : List F) :
    Except String Unit := do
  let height := main.height
  if let some prep := air.preprocessed_trace then
    if prep.height ≠ height then throw "preprocessed trace height does not match"
  assert_periodic_column_shapes air height
  if (← boundary_io_mismatches air main public_values) ≠ [] then
    throw "boundary-IO cell does not hold its public value"
  (List.range height).forM fun row_index => do
    let builder := (air.eval (rowBuilder air main public_values row_index)
      (DebugState.new row_index))
    if builder.failures ≠ [] then throw "constraints not satisfied"

end p3_air.air.mirror
