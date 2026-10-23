/-
Transcriptions of the builder traits: their required items, their provided methods, and the filtered builder.

These do not extract: the traits carry associated types bounded by the field traits, which aeneas rejects.

Each definition transcribes one Rust item, named in the crate's mirror entries.

What a transcription abstracts:

* a builder is a record of its trait items over its state, and a mutable borrow is a returned state;
* the expression type is an arbitrary type with the ring operations and the embedding of constants, and no laws;
* a variable, a public value and a periodic value are read as expressions, which is what every arithmetic operation on them does first;
* a window is its current row and its next row;
* a panic is none.

Loops, branches and the order of operations are kept.
-/
module

public import P3Air.Assumptions.Mirror.Symbolic

@[expose] public section

namespace p3_air.builder.mirror

/-- A two-row window: the current row and the next row. -/
structure RowWindow (T : Type _) where
  current : List T
  next : List T

/-- The expression algebra of a builder: ring operations and the embedding of field constants. -/
structure ExprOps (F E : Type _) where
  add : E → E → E
  sub : E → E → E
  mul : E → E → E
  neg : E → E
  const : F → E

/-- The required items of the builder trait, over the builder's state S.

The window arity is 2 unless the builder says otherwise. -/
structure AirBuilder (F E S : Type _) extends ExprOps F E where
  main : S → RowWindow E
  preprocessed : S → RowWindow E
  is_first_row : S → E
  is_last_row : S → E
  is_transition : S → E
  assert_zero : S → E → S
  public_values : S → List E
  periodic_values : S → List E
  window : ℕ := 2

namespace AirBuilder

variable {F E S : Type _} [Zero F] [One F] (B : AirBuilder F E S)

/-- The transition selector for a window of the given size, which must not exceed the arity. -/
def is_transition_window (s : S) (size : ℕ) : Option E :=
  if size ≤ B.window then some (B.is_transition s) else none

/-- The builder seen through a condition: every asserted expression is multiplied by it first.

The filtered builder keeps the default arity 2. -/
def when (condition : E) : AirBuilder F E S :=
  { B with assert_zero := fun s x => B.assert_zero s (B.mul condition x), window := 2 }

/-- The builder seen through x - y, so that constraints apply where x and y differ. -/
def when_ne (x y : E) : AirBuilder F E S := B.when (B.sub x y)

/-- The builder seen through the first-row selector. -/
def when_first_row (s : S) : AirBuilder F E S := B.when (B.is_first_row s)

/-- The builder seen through the last-row selector. -/
def when_last_row (s : S) : AirBuilder F E S := B.when (B.is_last_row s)

/-- The builder seen through the transition selector. -/
def when_transition (s : S) : AirBuilder F E S := B.when (B.is_transition s)

/-- The builder seen through the transition selector of a window, which must fit the arity. -/
def when_transition_window (s : S) (size : ℕ) : Option (AirBuilder F E S) :=
  (B.is_transition_window s size).map B.when

/-- Assert each expression of an array, in order. -/
def assert_zeros (s : S) (xs : List E) : S := xs.foldl B.assert_zero s

/-- x (x - 1), which vanishes exactly on 0 and 1 in a field. -/
def bool_check (x : E) : E := B.mul x (B.sub x (B.const 1))

/-- Assert that each expression of an array is boolean. -/
def assert_bools (s : S) (xs : List E) : S := B.assert_zeros s (xs.map B.bool_check)

/-- Assert x - 1. -/
def assert_one (s : S) (x : E) : S := B.assert_zero s (B.sub x (B.const 1))

/-- Assert x - y. -/
def assert_eq (s : S) (x y : E) : S := B.assert_zero s (B.sub x y)

/-- Assert the differences of two arrays of one length, entry by entry. -/
def assert_eq_arrays (s : S) (lhs rhs : List E) : S :=
  B.assert_zeros s (List.zipWith B.sub lhs rhs)

/-- Assert x (x - 1). -/
def assert_bool (s : S) (x : E) : S := B.assert_zero s (B.bool_check x)

end AirBuilder

/-- The extension builder: an extension expression type, its operations, and its own assertion. -/
structure ExtensionBuilder (F E EE S : Type _) extends AirBuilder F E S where
  ext_sub : EE → EE → EE
  ext_mul_expr : EE → E → EE
  ext_one : EE
  assert_zero_ext : S → EE → S

namespace ExtensionBuilder

variable {F E EE S : Type _} [Zero F] [One F] (B : ExtensionBuilder F E EE S)

/-- Assert each extension expression of an array, in order. -/
def assert_zeros_ext (s : S) (xs : List EE) : S := xs.foldl B.assert_zero_ext s

/-- Assert x - y in the extension. -/
def assert_eq_ext (s : S) (x y : EE) : S := B.assert_zero_ext s (B.ext_sub x y)

/-- Assert x - 1 in the extension. -/
def assert_one_ext (s : S) (x : EE) : S := B.assert_eq_ext s x B.ext_one

/-- The filtered builder over an extension builder: an extension expression is multiplied by the condition on its right. -/
def when (condition : E) : ExtensionBuilder F E EE S :=
  { B with
    toAirBuilder := B.toAirBuilder.when condition
    assert_zero_ext := fun s x => B.assert_zero_ext s (B.ext_mul_expr x condition) }

end ExtensionBuilder

/-- A linear combination of columns read from a preprocessed row and a main row. -/
inductive PairCol where
  | Preprocessed (i : ℕ)
  | Main (i : ℕ)

/-- The entry a column names, which panics when out of range. -/
def PairCol.get {T : Type _} (c : PairCol) (preprocessed main : List T) : Option T :=
  match c with
  | .Preprocessed i => preprocessed[i]?
  | .Main i => main[i]?

/-- A constant plus weighted columns. -/
structure VirtualPairCol (F : Type _) where
  column_weights : List (PairCol × F)
  constant : F

namespace VirtualPairCol

variable {F : Type _} [Zero F] [One F] [Neg F]

/-- The combination with the given weights and constant. -/
def new (column_weights : List (PairCol × F)) (constant : F) : VirtualPairCol F :=
  ⟨column_weights, constant⟩

/-- Weighted preprocessed columns. -/
def new_preprocessed (column_weights : List (ℕ × F)) (constant : F) : VirtualPairCol F :=
  new (column_weights.map fun (i, w) => (.Preprocessed i, w)) constant

/-- Weighted main columns. -/
def new_main (column_weights : List (ℕ × F)) (constant : F) : VirtualPairCol F :=
  new (column_weights.map fun (i, w) => (.Main i, w)) constant

/-- A constant, with no column. -/
def constant' (x : F) : VirtualPairCol F := ⟨[], x⟩

/-- One column with weight 1. -/
def single (column : PairCol) : VirtualPairCol F := ⟨[(column, 1)], 0⟩

/-- One preprocessed column. -/
def single_preprocessed (column : ℕ) : VirtualPairCol F := single (.Preprocessed column)

/-- One main column. -/
def single_main (column : ℕ) : VirtualPairCol F := single (.Main column)

/-- The sum of main columns. -/
def sum_main (columns : List ℕ) : VirtualPairCol F := new_main (columns.map (·, 1)) 0

/-- The sum of preprocessed columns. -/
def sum_preprocessed (columns : List ℕ) : VirtualPairCol F :=
  new_preprocessed (columns.map (·, 1)) 0

/-- Preprocessed column a minus preprocessed column b. -/
def diff_preprocessed (a_col b_col : ℕ) : VirtualPairCol F :=
  new_preprocessed [(a_col, 1), (b_col, -1)] 0

/-- Main column a minus main column b. -/
def diff_main (a_col b_col : ℕ) : VirtualPairCol F := new_main [(a_col, 1), (b_col, -1)] 0

/-- The value on a row pair: a fold from the constant, adding each column times its weight. -/
def apply {E V : Type _} (ops : p3_air.builder.mirror.ExprOps F E) (into : V → E)
    (vc : VirtualPairCol F) (preprocessed main : List V) : Option E :=
  vc.column_weights.foldlM
    (fun acc (cw : PairCol × F) => do
      let v ← cw.1.get preprocessed main
      pure (ops.add acc (ops.mul (into v) (ops.const cw.2))))
    (ops.const vc.constant)

end VirtualPairCol

end p3_air.builder.mirror
