module

public import Plonky3Lean.Proofs.Air.Examples
public import Plonky3Lean.Proofs.Air.Extracted
public import Plonky3Lean.Proofs.Air.SymbolicExt
public import Plonky3Lean.Proofs.Air.VirtualColumn
public import Plonky3Lean.Proofs.Air.NextRow

@[expose] public section

/-!
# p3-air: claims

The integer helpers are extracted.

The builders, the symbolic expressions and the debug checker are transcribed over a field F.

An AIR's evaluation is a function generic in the builder.

It is parametric: related builders give related results.

Every Rust evaluation generic in the builder is parametric in this way.

The constraint polynomials of an AIR are what its evaluation asserts.

They live in the polynomial ring over the variables of a row.

A trace satisfies an AIR when every constraint polynomial vanishes on every row:

```text
    row i of n:   next row      = row (i + 1) mod n
                  is_first_row  = [i = 0]
                  is_last_row   = [i = n - 1]
                  is_transition = [i != n - 1]
```

The degree claims substitute univariate polynomials for the variables:

```text
    trace column, boundary selector   degree <= n - 1
    transition selector               degree <= 1
    periodic column of period p | n   degree <= n - n/p
    public value                      constant
```

A quotient of c chunks of n coefficients holds a constraint polynomial C when deg C < (c + 1) n.

The instances at BabyBear and its quartic extension use CompPoly's fields.
-/

open p3_air.symbolic.mirror p3_air.builder.mirror p3_air.air.mirror Plonky3Lean.Spec.Air
open Plonky3Lean.Proofs.Air

set_option linter.unusedSectionVars false

namespace Plonky3Lean.Claims.Air

variable {F : Type} [Field F] [DecidableEq F]

/-! ## AIR semantics -/

/-- Restricting constraints by selectors describes the same traces as restricting them to rows.

The row domains are every row, row 0, row n - 1, or the rows with a successor. -/
theorem selector_form_iff_domain_form (C : List (Constraint F)) (T : Instance F) :
    Satisfies (C.map fun c => c.domain.selector * c.poly) T ↔ SatisfiesOn C T :=
  satisfies_selector_iff C T

/-- On a trace of one row, a transition constraint asks nothing. -/
theorem transition_vacuous_height_one (p : MvPolynomial Var F) (T : Instance F)
    (h : T.height = 1) : SatisfiesOn [⟨.transition, p⟩] T :=
  transition_vacuous_of_height_one p T h

/-- On a trace of no rows, every constraint holds, even a nonzero constant. -/
theorem satisfies_height_zero (C : List (MvPolynomial Var F)) (T : Instance F)
    (h : T.height = 0) : Satisfies C T :=
  satisfies_of_height_zero C T h

/-- A nonzero constant constraint fails on every trace with a row. -/
theorem const_constraint_fails {c : F} (hc : c ≠ 0) (T : Instance F) (h : 0 < T.height) :
    ¬ Satisfies [MvPolynomial.C c] T :=
  not_satisfies_const hc T h

/-- The next row of the last row is row 0. -/
theorem next_row_of_last_row (T : Instance F) (h : 0 < T.height) (c : ℕ) :
    rowEnv T (T.height - 1) (.main 1 c) = T.main 0 c :=
  rowEnv_next_last T h c

/-! ## The debug checker -/

variable [Inhabited F]

/-- The debug checker accepts exactly when four conditions hold.

The trace, the preprocessed trace, the public values and the periodic columns have the AIR's widths.

The conditions are:

- the preprocessed height matches
- every periodic column has a power-of-two length dividing the height
- every boundary cell holds its public value
- every constraint polynomial vanishes on every row. -/
theorem check_constraints_ok_iff {air : Air F} {M : Mat F} {pv : List F} (hs : Shapes air M pv) :
    check_constraints air M pv = .ok () ↔
      PrepHeight air M ∧ PeriodicShapes air M.height ∧
        boundary_io_mismatches air M pv = .ok [] ∧ Satisfies (constraints air) (instOf air M pv) :=
  Proofs.Air.check_constraints_ok_iff hs

/-- At row i, the debug builder asserts the constraint polynomials evaluated on row i, in order. -/
theorem debug_row_asserts {air : Air F} {M : Mat F} {pv : List F} (hs : Shapes air M pv)
    (hp : PrepHeight air M) {i : ℕ} (hi : i < M.height) :
    air.eval (rowBuilder air M pv i) (DebugState.new i) =
      (constraints air).foldl
        (fun s c => s.assert_zero (MvPolynomial.eval (rowEnv (instOf air M pv) i) c))
        (DebugState.new i) := by
  rw [eval_rowBuilder hs hp hi, assertAll, List.foldl_map]

/-! ## The builder combinators on the debug builder -/

section combinators

variable (main preprocessed : RowWindow F) (pv : List F) (first last trans : F)
  (periodic : List F) (s : DebugState)

/-- The debug builder records a failure exactly for a nonzero value. -/
theorem assert_zero_accepts (x : F) :
    ((debugBuilder main preprocessed pv first last trans periodic).assert_zero s x).failures =
      s.failures ↔ x = 0 :=
  dbg_assert_zero main preprocessed pv first last trans periodic s x

/-- Through a condition c, it accepts x exactly when c = 0 or x = 0. -/
theorem when_accepts (c x : F) :
    (((debugBuilder main preprocessed pv first last trans periodic).when c).assert_zero s
      x).failures = s.failures ↔ c = 0 ∨ x = 0 :=
  dbg_when main preprocessed pv first last trans periodic s c x

/-- Through two conditions, it accepts x exactly when one of them or x is zero. -/
theorem when_when_accepts (c d x : F) :
    ((((debugBuilder main preprocessed pv first last trans periodic).when c).when d).assert_zero
      s x).failures = s.failures ↔ c = 0 ∨ d = 0 ∨ x = 0 :=
  dbg_when_when main preprocessed pv first last trans periodic s c d x

/-- Where a and b differ, it asks x = 0. -/
theorem when_ne_accepts (a b x : F) :
    (((debugBuilder main preprocessed pv first last trans periodic).when_ne a b).assert_zero s
      x).failures = s.failures ↔ (a ≠ b → x = 0) :=
  dbg_when_ne main preprocessed pv first last trans periodic s a b x

/-- It accepts x = y exactly when it holds. -/
theorem assert_eq_accepts (x y : F) :
    ((debugBuilder main preprocessed pv first last trans periodic).assert_eq s x y).failures =
      s.failures ↔ x = y :=
  dbg_assert_eq main preprocessed pv first last trans periodic s x y

/-- It accepts x = 1 exactly when it holds. -/
theorem assert_one_accepts (x : F) :
    ((debugBuilder main preprocessed pv first last trans periodic).assert_one s x).failures =
      s.failures ↔ x = 1 :=
  dbg_assert_one main preprocessed pv first last trans periodic s x

/-- It accepts x as boolean exactly when x is 0 or 1. -/
theorem assert_bool_accepts (x : F) :
    ((debugBuilder main preprocessed pv first last trans periodic).assert_bool s x).failures =
      s.failures ↔ x = 0 ∨ x = 1 :=
  dbg_assert_bool main preprocessed pv first last trans periodic s x

/-- It accepts an array exactly when every entry is zero. -/
theorem assert_zeros_accepts (xs : List F) :
    ((debugBuilder main preprocessed pv first last trans periodic).assert_zeros s xs).failures =
      s.failures ↔ ∀ x ∈ xs, x = 0 :=
  dbg_assert_zeros main preprocessed pv first last trans periodic s xs

/-- Resolving an in-scope symbolic expression evaluates its polynomial at the builder's values. -/
theorem resolve_eval (e : SymbolicExpression F) (he : InScope main preprocessed pv periodic e) :
    resolve (debugBuilder main preprocessed pv first last trans periodic) s e =
      some (MvPolynomial.eval (windowEnv main preprocessed pv first last trans periodic)
        (toPoly e)) :=
  resolve_debugBuilder main preprocessed pv first last trans periodic s e he

end combinators

section rows

variable (air : Air F) (M : Mat F) (pv : List F) (s : DebugState)

/-- On row i of the check, the first-row filter asks x = 0 on row 0 only. -/
theorem when_first_row_accepts (i : ℕ) (x : F) :
    (((rowBuilder air M pv i).when_first_row s).assert_zero s x).failures = s.failures ↔
      (i = 0 → x = 0) :=
  row_when_first_row air M pv s i x

/-- On row i of the check, the last-row filter asks x = 0 on row n - 1 only. -/
theorem when_last_row_accepts (i : ℕ) (x : F) :
    (((rowBuilder air M pv i).when_last_row s).assert_zero s x).failures = s.failures ↔
      (i = M.height - 1 → x = 0) :=
  row_when_last_row air M pv s i x

/-- On row i of the check, the transition filter asks x = 0 on every row but n - 1. -/
theorem when_transition_accepts (i : ℕ) (x : F) :
    (((rowBuilder air M pv i).when_transition s).assert_zero s x).failures = s.failures ↔
      (i ≠ M.height - 1 → x = 0) :=
  row_when_transition air M pv s i x

/-- A transition window of size at most 2 is the transition selector, and a larger one panics. -/
theorem transition_window (i size : ℕ) :
    (rowBuilder air M pv i).is_transition_window s size =
      if size ≤ 2 then some (if i ≠ M.height - 1 then 1 else 0) else none :=
  row_is_transition_window air M pv s i size

end rows

/-! ## Extension assertions at BabyBear and its quartic extension -/

section babybear

variable (main preprocessed : RowWindow BabyBear.Field) (pv : List BabyBear.Field)
  (first last trans : BabyBear.Field) (periodic : List BabyBear.Field) (s : DebugState)

/-- The debug builder accepts an extension value exactly when it is zero. -/
theorem bb_assert_zero_ext (x : BabyBear.Ext4) :
    ((debugExtBuilder main preprocessed pv first last trans periodic).assert_zero_ext s
      x).failures = s.failures ↔ x = 0 :=
  dbgExt_assert_zero_ext main preprocessed pv first last trans periodic s x

/-- Through a base condition c, it accepts an extension value x exactly when c = 0 or x = 0. -/
theorem bb_when_ext (c : BabyBear.Field) (x : BabyBear.Ext4) :
    (((debugExtBuilder main preprocessed pv first last trans periodic).when c).assert_zero_ext s
      x).failures = s.failures ↔ c = 0 ∨ x = 0 :=
  dbgExt_when main preprocessed pv first last trans periodic s c x

/-- It accepts x = y in the extension exactly when it holds. -/
theorem bb_assert_eq_ext (x y : BabyBear.Ext4) :
    ((debugExtBuilder main preprocessed pv first last trans periodic).assert_eq_ext s x
      y).failures = s.failures ↔ x = y :=
  dbgExt_assert_eq_ext main preprocessed pv first last trans periodic s x y

/-- It accepts x = 1 in the extension exactly when it holds. -/
theorem bb_assert_one_ext (x : BabyBear.Ext4) :
    ((debugExtBuilder main preprocessed pv first last trans periodic).assert_one_ext s
      x).failures = s.failures ↔ x = 1 :=
  dbgExt_assert_one_ext main preprocessed pv first last trans periodic s x

end babybear

/-! ## Symbolic expressions -/

/-- Addition denotes addition, whichever simplification fires. -/
theorem sym_add_denotes (x y : SymbolicExpression F) :
    toPoly (x.sym_add y) = toPoly x + toPoly y :=
  Proofs.Air.SymbolicExpr.denote_sym_add leafDen_leafPoly x y

/-- Subtraction denotes subtraction, whichever simplification fires. -/
theorem sym_sub_denotes (x y : SymbolicExpression F) :
    toPoly (x.sym_sub y) = toPoly x - toPoly y :=
  Proofs.Air.SymbolicExpr.denote_sym_sub leafDen_leafPoly x y

/-- Multiplication denotes multiplication, whichever simplification fires. -/
theorem sym_mul_denotes (x y : SymbolicExpression F) :
    toPoly (x.sym_mul y) = toPoly x * toPoly y :=
  Proofs.Air.SymbolicExpr.denote_sym_mul leafDen_leafPoly x y

/-- Negation denotes negation. -/
theorem sym_neg_denotes (x : SymbolicExpression F) : toPoly x.sym_neg = -toPoly x :=
  Proofs.Air.SymbolicExpr.denote_sym_neg leafDen_leafPoly x

/-- Over BabyBear and its quartic extension, extension addition denotes addition. -/
theorem bb_ext_sym_add_denotes (x y : SymbolicExpressionExt BabyBear.Field BabyBear.Ext4) :
    toPolyExt (x.sym_add y) = toPolyExt x + toPolyExt y :=
  Proofs.Air.SymbolicExpr.denote_sym_add (leafDen_extLeafPoly lawfulInBase_babyBear) x y

/-- Over BabyBear and its quartic extension, extension subtraction denotes subtraction. -/
theorem bb_ext_sym_sub_denotes (x y : SymbolicExpressionExt BabyBear.Field BabyBear.Ext4) :
    toPolyExt (x.sym_sub y) = toPolyExt x - toPolyExt y :=
  Proofs.Air.SymbolicExpr.denote_sym_sub (leafDen_extLeafPoly lawfulInBase_babyBear) x y

/-- Over BabyBear and its quartic extension, extension multiplication denotes multiplication. -/
theorem bb_ext_sym_mul_denotes (x y : SymbolicExpressionExt BabyBear.Field BabyBear.Ext4) :
    toPolyExt (x.sym_mul y) = toPolyExt x * toPolyExt y :=
  Proofs.Air.SymbolicExpr.denote_sym_mul (leafDen_extLeafPoly lawfulInBase_babyBear) x y

/-- An extension expression with no extension leaf denotes its base expression. -/
theorem to_base_denotes {EF : Type} [Field EF] [Algebra F EF] [InBase F EF]
    {e : SymbolicExpressionExt F EF} {b : SymbolicExpression F}
    (h : SymbolicExpressionExt.to_base e = some b) :
    toPolyExt e = MvPolynomial.rename Sum.inl (MvPolynomial.map (algebraMap F EF) (toPoly b)) :=
  toPolyExt_of_to_base h

/-- The symbolic constraints of an AIR denote its constraint polynomials. -/
theorem symbolic_constraints_denote (air : Air F) :
    (get_symbolic_constraints air (AirLayout.from_air air)).map (·.map toPoly) =
      .ok (constraints air) :=
  get_symbolic_constraints_toPoly air

/-- Every symbolic constraint caches the degree multiple its children determine. -/
theorem symbolic_constraints_cache (air : Air F) (layout : AirLayout) :
    ∀ c ∈ air.eval (symbolicBuilder layout) [],
      c.degree_multiple = c.degree_with SymLeaf.degree_multiple :=
  fun c hc => (symbolic_wf air layout c hc).degree_multiple_eq

/-! ## Degrees -/

/-- When the periods divide n, the degree walk bounds the degree of the constraint polynomial. -/
theorem poly_degree_bound {σ : Var → Polynomial F} {n : ℕ} {periods : List ℕ}
    (hσ : DegreeBounds σ n periods)
    (hp : ∀ j p : ℕ, periods[j]? = some p → 0 < p → p < n → p ∣ n) (e : SymbolicExpression F) :
    (constraintPoly σ (toPoly e)).natDegree ≤ e.poly_degree n periods :=
  natDegree_le_poly_degree hσ hp e

/-- A well-formed expression of degree multiple d has polynomial degree at most d (n - 1) + t.

Here t counts its transition selectors along a product. -/
theorem degree_multiple_bound {e : SymbolicExpression F} (he : SymbolicExpr.WF e) (n : ℕ)
    (periods : List ℕ) :
    e.poly_degree n periods ≤ e.degree_multiple * (n - 1) + transitionCount e :=
  poly_degree_le_degree_multiple he

/-- Over BabyBear's quartic extension, the degree walk bounds an extension constraint polynomial. -/
theorem bb_ext_poly_degree_bound
    {σ : Var ⊕ SymbolicVariableExt → Polynomial BabyBear.Ext4} {n : ℕ} {periods : List ℕ}
    (hσ : ExtDegreeBounds σ n periods)
    (hp : ∀ j p : ℕ, periods[j]? = some p → 0 < p → p < n → p ∣ n)
    (e : SymbolicExpressionExt BabyBear.Field BabyBear.Ext4) :
    (MvPolynomial.aeval σ (toPolyExt e)).natDegree ≤ e.poly_degree n periods :=
  natDegree_ext_le_poly_degree hσ hp e

/-- A periodic column of period p dividing n, f(X^(n/p)) with deg f < p, has degree at most n - n/p. -/
theorem periodic_degree {K : Type} [Field K] {f : Polynomial K} {n p : ℕ} (hp : p ∣ n)
    (hf : f.natDegree < p) : (f.comp (Polynomial.X ^ (n / p))).natDegree ≤ n - n / p :=
  natDegree_periodic_comp_le hp hf

/-- For n >= 2, the constraint degree of a polynomial degree D is the least d with D <= d (n - 1) + 1. -/
theorem constraint_degree_least (D : ℕ) {n : ℕ} (hn : 2 ≤ n) :
    D ≤ constraint_degree_from_poly_degree D n * (n - 1) + 1 ∧
      ∀ d, D ≤ d * (n - 1) + 1 → constraint_degree_from_poly_degree D n ≤ d :=
  ⟨le_constraint_degree_from_poly_degree D hn, fun _ => constraint_degree_from_poly_degree_le hn⟩

/-! ## Quotient chunks -/

/-- The quotient chunk count is 2^(ceil(log_2(max(d + z, 2) - 1)) + z).

It is 2^z times the least power of two at least max(d + z, 2) - 1, as p3-security assumes. -/
theorem num_quotient_chunks (d z : ℕ) :
    2 ^ (log2_ceil_usize (max (d + z) 2 - 1) + z) =
      2 ^ z * 2 ^ log2_ceil_usize (max (d + z) 2 - 1) ∧
    max (d + z) 2 - 1 ≤ 2 ^ log2_ceil_usize (max (d + z) 2 - 1) ∧
    ∀ k, max (d + z) 2 - 1 ≤ 2 ^ k → log2_ceil_usize (max (d + z) 2 - 1) ≤ k :=
  num_quotient_chunks_eq d z

/-- With periodic columns and n >= 2, every constraint polynomial fits the sized quotient chunks. -/
theorem quotient_fits_with_periodic {air : Air F} {σ : Var → Polynomial F} {n L : ℕ} (hn : 2 ≤ n)
    (hper : (AirLayout.from_air air).num_periodic_columns ≠ 0)
    (h : get_log_quotient_degree air (AirLayout.from_air air) n 0 = .ok L)
    (hσ : DegreeBounds σ n (air.periodic_columns.map List.length))
    (hp : ∀ j p : ℕ, (air.periodic_columns.map List.length)[j]? = some p → 0 < p → p < n →
      p ∣ n) :
    ∀ e ∈ air.eval (symbolicBuilder (AirLayout.from_air air)) [],
      FitsChunks n (2 ^ L) (constraintPoly σ (toPoly e)) :=
  quotient_fits_periodic hn hper h hσ hp

/-- Without periodic columns, every constraint polynomial fits the sized quotient chunks.

This needs at most one transition selector along a product in each constraint. -/
theorem quotient_fits_one_transition {air : Air F} {σ : Var → Polynomial F} {n L : ℕ}
    {periods : List ℕ} (hn : 1 ≤ n)
    (hper : (AirLayout.from_air air).num_periodic_columns = 0)
    (h : get_log_quotient_degree air (AirLayout.from_air air) n 0 = .ok L)
    (hσ : DegreeBounds σ n periods)
    (hp : ∀ j p : ℕ, periods[j]? = some p → 0 < p → p < n → p ∣ n)
    (ht : ∀ e ∈ air.eval (symbolicBuilder (AirLayout.from_air air)) [], transitionCount e ≤ 1) :
    ∀ e ∈ air.eval (symbolicBuilder (AirLayout.from_air air)) [],
      FitsChunks n (2 ^ L) (constraintPoly σ (toPoly e)) :=
  quotient_fits_fast hn hper h hσ hp ht

/-- Two transition filters can overflow the quotient chunks.

An AIR asserting a^2 = b through two transition filters gets one quotient chunk.

Yet its constraint polynomial reaches degree 2n within the degree bounds.

One chunk of n coefficients cannot hold it. -/
theorem two_transitions_overflow {n : ℕ} (hn : 1 ≤ n) :
    get_log_quotient_degree (squareAir (F := F)) (AirLayout.from_air (squareAir (F := F))) n 0 =
        .ok 0 ∧
      (squareAir (F := F)).eval (symbolicBuilder (AirLayout.from_air (squareAir (F := F)))) [] =
        [.Mul symT (.Mul symT (.Sub (.Mul symA symA 2) symB 2) 2) 2] ∧
      DegreeBounds (sigmaSquare (F := F) n) n [] ∧
      ¬ FitsChunks n (2 ^ 0) (constraintPoly (sigmaSquare (F := F) n)
        (toPoly (.Mul symT (.Mul symT (.Sub (.Mul symA symA 2) symB 2) 2) 2))) :=
  ⟨squareAir_log_quotient_degree n, squareAir_constraints, degreeBounds_sigmaSquare n [],
    squareAir_quotient_overflows hn⟩

/-! ## Virtual columns -/

/-- A virtual column with every column in range evaluates to its constant plus the weighted columns.

This holds in any commutative F-algebra. -/
theorem virtual_column_apply {R V : Type} [CommRing R] [Algebra F R] (into : V → R)
    (vc : VirtualPairCol F) (preprocessed main : List V) (val : PairCol → V)
    (h : ∀ cw ∈ vc.column_weights, cw.1.get preprocessed main = some (val cw.1)) :
    vc.apply (ringOps R) into preprocessed main =
      some (algebraMap F R vc.constant +
        (vc.column_weights.map fun cw => into (val cw.1) * algebraMap F R cw.2).sum) :=
  apply_eq into vc preprocessed main val h

/-- A virtual column with a column out of range panics. -/
theorem virtual_column_panics {R V : Type} [CommRing R] [Algebra F R] (into : V → R)
    (vc : VirtualPairCol F) (preprocessed main : List V)
    (h : ∃ cw ∈ vc.column_weights, cw.1.get preprocessed main = none) :
    vc.apply (ringOps R) into preprocessed main = none :=
  apply_eq_none into vc preprocessed main h

/-! ## Boundary cells -/

/-- The declaration check accepts column 0 bound on both the first and the last row.

On a one-row trace, both bindings name the same cell. -/
theorem boundary_first_last_one_row :
    validate [⟨0, .First, 0⟩, ⟨0, .Last, 1⟩] 1 2 = .ok () ∧
      BoundaryPublic.row ⟨0, .First, 0⟩ 1 = BoundaryPublic.row ⟨0, .Last, 1⟩ 1 :=
  ⟨validate_first_last_same_column, row_first_last_height_one 0 0 1⟩

/-! ## The extracted helpers -/

section extracted

open Aeneas Aeneas.Std CoreModels p3_air Proofs.Air.Extracted

/-- On a trace with rows, the row of a boundary cell is 0 for the first end and height - 1 for the last. -/
theorem boundary_row (cell : boundary.BoundaryPublic) (height : Std.Usize) (h : 0 < height.val) :
    boundary.BoundaryPublic.row cell height ⦃ r =>
      r.val = match cell.end with
        | .First => 0
        | .Last => height.val - 1 ⦄ :=
  row_spec cell height h

/-- On an empty trace, the row of a boundary cell panics. -/
theorem boundary_row_panics (cell : boundary.BoundaryPublic) (height : Std.Usize)
    (h : height.val = 0) : boundary.BoundaryPublic.row cell height = .fail .panic :=
  row_panics cell height h

/-- Converting a polynomial degree to a constraint degree never panics and matches its transcription. -/
theorem constraint_degree_from_poly_degree_extracted (pd n : Std.Usize) :
    symbolic.builder.constraint_degree_from_poly_degree pd n ⦃ d =>
      d.val = p3_air.air.mirror.constraint_degree_from_poly_degree pd.val n.val ⦄ :=
  constraint_degree_from_poly_degree_spec pd n

/-- A base variable's degree multiple never panics and matches its transcription. -/
theorem variable_degree_multiple {G : Type} (v : symbolic.variable.SymbolicVariable G) :
    symbolic.variable.SymbolicVariable.degree_multiple v ⦃ d =>
      d.val = (varOf v).degree_multiple ⦄ :=
  degree_multiple_spec v

/-- A base variable's polynomial degree never panics and matches its transcription. -/
theorem variable_poly_degree {G : Type} (v : symbolic.variable.SymbolicVariable G) (n : Std.Usize)
    (periods : Slice Std.Usize) :
    symbolic.variable.SymbolicVariable.poly_degree v n periods ⦃ d =>
      d.val = (varOf v).poly_degree n.val (periods.val.map (·.val)) ⦄ :=
  poly_degree_spec v n periods

/-- An extension variable's degree multiple never panics and matches its transcription. -/
theorem ext_variable_degree_multiple {G EG : Type}
    (v : symbolic.variable.SymbolicVariableExt G EG) :
    symbolic.variable.SymbolicVariableExt.degree_multiple v ⦃ d =>
      d.val = (varExtOf v).degree_multiple ⦄ :=
  ext_degree_multiple_spec v

/-- An extension variable's polynomial degree never panics and matches its transcription. -/
theorem ext_variable_poly_degree {G EG : Type} (v : symbolic.variable.SymbolicVariableExt G EG)
    (n : Std.Usize) :
    symbolic.variable.SymbolicVariableExt.poly_degree v n ⦃ d =>
      d.val = (varExtOf v).poly_degree n.val ⦄ :=
  ext_poly_degree_spec v n

/-- The duplicate scan of the declaration check never panics.

It reports whether an earlier cell has the same column and end. -/
theorem boundary_duplicate_scan (c : boundary.validate.closure) (l : List boundary.BoundaryPublic)
    (s : CoreModels.core.slice.iter.Iter boundary.BoundaryPublic)
    (hs : (show Slice boundary.BoundaryPublic from s).val = l) :
    ∃ it, core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.any
      boundary.validate.closure.Insts.CoreOpsFunctionFnMutTupleShared1BoundaryPublicBool s c =
      .ok (l.any fun e => decide (e.column = c.column ∧ e.end = c.end), it) :=
  any_spec c l s hs

end extracted

section nextRow

/-- **Unread rows do not matter.**

Drop the next row of the main trace, of the preprocessed trace, or of both.

Take an AIR whose symbolic constraints never read a dropped row.

Take two assignments that agree on every variable outside the dropped rows.

Then every constraint polynomial has the same value at both. -/
theorem next_row_unread : type_of% @Plonky3Lean.Proofs.Air.constraints_congr :=
  @Plonky3Lean.Proofs.Air.constraints_congr

end nextRow

end Plonky3Lean.Claims.Air
