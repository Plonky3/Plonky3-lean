module

public import P3Air
public import Plonky3Lean.Proofs.Air.Degree
public import Plonky3Lean.Proofs.Matrix.Views
public import Plonky3Lean.Lib

@[expose] public section

/-!
# The extracted integer helpers

The extracted boundary row, degree conversion and variable degrees never panic outside the documented case.

Each agrees with its transcription, so the theorems about the transcriptions hold of the extracted code.
-/

namespace Plonky3Lean.Proofs.Air.Extracted

open Aeneas Aeneas.Std CoreModels
open p3_air

/-! ## Boundary rows -/

/-- On a trace with rows, the row of a boundary cell is 0 for the first end and height - 1 for the last. -/
theorem row_spec (cell : boundary.BoundaryPublic) (height : Std.Usize) (h : 0 < height.val) :
    boundary.BoundaryPublic.row cell height ⦃ r =>
      r.val = match cell.end with
        | .First => 0
        | .Last => height.val - 1 ⦄ := by
  unfold boundary.BoundaryPublic.row
  have : height > 0#usize := by scalar_tac
  simp only [massert, this, ↓reduceIte]
  cases cell.end <;> step*

/-- On an empty trace, the row of a boundary cell panics. -/
theorem row_panics (cell : boundary.BoundaryPublic) (height : Std.Usize) (h : height.val = 0) :
    boundary.BoundaryPublic.row cell height = .fail .panic := by
  unfold boundary.BoundaryPublic.row
  have : ¬ height > 0#usize := by scalar_tac
  simp [massert, this]

/-! ## Constraint degree of a polynomial degree -/

/-- The extracted conversion never panics and returns its transcription. -/
theorem constraint_degree_from_poly_degree_spec (pd n : Std.Usize) :
    symbolic.builder.constraint_degree_from_poly_degree pd n ⦃ d =>
      d.val = p3_air.air.mirror.constraint_degree_from_poly_degree pd.val n.val ⦄ := by
  unfold symbolic.builder.constraint_degree_from_poly_degree
    p3_air.air.mirror.constraint_degree_from_poly_degree
  by_cases h0 : pd = 0#usize
  · simp [h0]
  · have hpd : pd.val ≠ 0 := by scalar_tac
    simp only [h0, hpd, ↓reduceIte]
    by_cases hn : n > 1#usize
    · have hn' : n.val > 1 := by scalar_tac
      simp only [hn, hn', ↓reduceIte]
      step*
      refine WP.spec_mono (Plonky3Lean.Proofs.Matrix.div_ceil_eq i denom (by scalar_tac)) fun d hd => ?_
      rw [hd, i_post, denom_post]
    · have hn' : ¬ n.val > 1 := by scalar_tac
      simp only [hn, hn', ↓reduceIte]
      step*
      refine WP.spec_mono (Plonky3Lean.Proofs.Matrix.div_ceil_eq i 1#usize (by scalar_tac)) fun d hd => ?_
      rw [hd, i_post]
      rfl

/-! ## Degrees of a variable -/

theorem sub_one_toNat (n : Std.Usize) :
    (⟨BitVec.ofNat _ (n.val - 1)⟩ : Std.Usize).val = n.val - 1 := by
  show (BitVec.ofNat _ (n.val - 1)).toNat = _
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
  have := n.hBounds
  omega

/-- An extracted base entry, with its offset read as a natural number. -/
def entryOf : symbolic.variable.BaseEntry → p3_air.symbolic.mirror.BaseEntry
  | .Preprocessed o => .Preprocessed o.val
  | .Main o => .Main o.val
  | .Periodic => .Periodic
  | .Public => .Public

/-- An extracted base variable, with its index read as a natural number. -/
def varOf {F : Type} (v : symbolic.variable.SymbolicVariable F) :
    p3_air.symbolic.mirror.SymbolicVariable :=
  ⟨entryOf v.entry, v.index.val⟩

/-- The extracted degree multiple never panics and returns its transcription. -/
theorem degree_multiple_spec {F : Type} (v : symbolic.variable.SymbolicVariable F) :
    symbolic.variable.SymbolicVariable.degree_multiple v ⦃ d =>
      d.val = (varOf v).degree_multiple ⦄ := by
  unfold symbolic.variable.SymbolicVariable.degree_multiple
  rcases v with ⟨e, i, _⟩
  cases e <;> simp [varOf, entryOf, p3_air.symbolic.mirror.SymbolicVariable.degree_multiple]

/-- The periodic arm: clamp the period to n, then n - 1 for period 0, else n - n / period. -/
theorem periodic_tail_spec (a n : Std.Usize) :
    (do
      let period ← core.Usize.Insts.CoreCmpOrd.min a n
      match period.val with
      | 0 => RustM.ok (⟨BitVec.ofNat _ (n.val - (1#usize : Std.Usize).val)⟩ : Std.Usize)
      | _ => do
        let i1 ← n / period
        n - i1) ⦃ d =>
      d.val = match min a.val n.val with
        | 0 => n.val - 1
        | p => n.val - n.val / p ⦄ := by
  obtain ⟨r, hr, hrv⟩ := Plonky3Lean.Lib.spec_imp_exists
    (Plonky3Lean.Lib.core.Usize.Insts.CoreCmpOrd.min.spec a n)
  rw [hr, bind_ok, ← hrv]
  split
  · simp only [WP.spec_ok]
    exact sub_one_toNat n
  · rename_i h
    have := Nat.div_le_self n.val r.val
    step*

/-- The extracted polynomial degree never panics and returns its transcription. -/
theorem poly_degree_spec {F : Type} (v : symbolic.variable.SymbolicVariable F) (n : Std.Usize)
    (periods : Slice Std.Usize) :
    symbolic.variable.SymbolicVariable.poly_degree v n periods ⦃ d =>
      d.val = (varOf v).poly_degree n.val (periods.val.map (·.val)) ⦄ := by
  unfold symbolic.variable.SymbolicVariable.poly_degree
  rcases v with ⟨e, i, _⟩
  cases e
  all_goals simp only [varOf, entryOf, p3_air.symbolic.mirror.SymbolicVariable.poly_degree,
      core.num.Usize.saturating_sub_exposed, WP.spec_ok]
  · exact sub_one_toNat n
  · exact sub_one_toNat n
  · rw [Plonky3Lean.Lib.slice_get_usize_eq, bind_ok]
    simp only [core.option.OptionShared0T.copied, bind_ok]
    rw [List.getElem?_map]
    rcases h : periods.val[i.val]? with _ | p <;>
      simp only [CoreModels.core.option.Option.unwrap_or, bind_ok, Option.map_none,
        Option.map_some, Option.getD_none, Option.getD_some]
    · exact periodic_tail_spec n n
    · exact periodic_tail_spec p n
  · simp

/-- An extracted extension variable, with its offset and index read as natural numbers. -/
def varExtOf {F EF : Type} (v : symbolic.variable.SymbolicVariableExt F EF) :
    p3_air.symbolic.mirror.SymbolicVariableExt :=
  ⟨match v.entry with
    | .Permutation o => .Permutation o.val
    | .Challenge => .Challenge
    | .PermutationValue => .PermutationValue, v.index.val⟩

/-- The extracted degree multiple of an extension variable never panics and returns its transcription. -/
theorem ext_degree_multiple_spec {F EF : Type} (v : symbolic.variable.SymbolicVariableExt F EF) :
    symbolic.variable.SymbolicVariableExt.degree_multiple v ⦃ d =>
      d.val = (varExtOf v).degree_multiple ⦄ := by
  unfold symbolic.variable.SymbolicVariableExt.degree_multiple
  rcases v with ⟨e, i, _⟩
  cases e <;> simp [varExtOf, p3_air.symbolic.mirror.SymbolicVariableExt.degree_multiple]

/-- The extracted polynomial degree of an extension variable never panics and returns its transcription. -/
theorem ext_poly_degree_spec {F EF : Type} (v : symbolic.variable.SymbolicVariableExt F EF)
    (n : Std.Usize) :
    symbolic.variable.SymbolicVariableExt.poly_degree v n ⦃ d =>
      d.val = (varExtOf v).poly_degree n.val ⦄ := by
  unfold symbolic.variable.SymbolicVariableExt.poly_degree
  rcases v with ⟨e, i, _⟩
  cases e
  · simpa [varExtOf, p3_air.symbolic.mirror.SymbolicVariableExt.poly_degree,
      core.num.Usize.saturating_sub_exposed] using sub_one_toNat n
  all_goals simp [varExtOf, p3_air.symbolic.mirror.SymbolicVariableExt.poly_degree]

/-! ## Boundary declarations -/

deriving instance DecidableEq for boundary.BoundaryEnd

theorem end_eq_spec (a b : boundary.BoundaryEnd) :
    boundary.BoundaryEnd.Insts.CoreCmpPartialEqBoundaryEnd.eq a b = .ok (decide (a = b)) := by
  cases a <;> cases b <;> simp [boundary.BoundaryEnd.Insts.CoreCmpPartialEqBoundaryEnd.eq,
    boundary.BoundaryEnd.read_discriminant]

/-- The duplicate test: whether an earlier cell has the same column and end. -/
def sameCell (c e : boundary.BoundaryPublic) : Bool := decide (e.column = c.column ∧ e.end = c.end)

theorem call_mut_spec (c : boundary.validate.closure) (a : boundary.BoundaryPublic) :
    boundary.validate.closure.Insts.CoreOpsFunctionFnMutTupleShared1BoundaryPublicBool.call_mut c a =
      .ok (sameCell c a, c) := by
  unfold boundary.validate.closure.Insts.CoreOpsFunctionFnMutTupleShared1BoundaryPublicBool.call_mut
  by_cases h : a.column = c.column <;> simp [h, end_eq_spec, sameCell]

/-- The duplicate scan of the extracted declaration check never panics, and reports whether some cell has the given column and end. -/
theorem any_spec (c : boundary.validate.closure) (l : List boundary.BoundaryPublic) :
    ∀ s : CoreModels.core.slice.iter.Iter boundary.BoundaryPublic,
    (show Slice boundary.BoundaryPublic from s).val = l →
    ∃ it, core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.any
      boundary.validate.closure.Insts.CoreOpsFunctionFnMutTupleShared1BoundaryPublicBool
      s c = .ok (l.any (sameCell c), it) := by
  simp only [CoreModels.core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.any,
    core.iter.traits.iterator.Iterator.any.default, core.iter.traits.iterator.iter_any]
  induction l with
  | nil =>
    intro s hs
    refine ⟨s, ?_⟩
    unfold core.iter.traits.iterator.iter_any_loop
    rw [loop]
    have : s.len = 0#usize := by scalar_tac
    simp [core.iter.traits.iterator.iter_any_loop.body,
      core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.next,
      rust_primitives.sequence.seq_len, this]
  | cons a l ih =>
    intro s hs
    obtain ⟨s', hrem, hs'⟩ : ∃ s' : CoreModels.core.slice.iter.Iter boundary.BoundaryPublic,
        rust_primitives.sequence.seq_remove s 0#usize = .ok (a, s') ∧
          (show Slice boundary.BoundaryPublic from s').val = l :=
      Plonky3Lean.Lib.seq_remove_head s a l hs
    unfold core.iter.traits.iterator.iter_any_loop
    rw [loop]
    have : s.len ≠ 0#usize := by scalar_tac
    simp [core.iter.traits.iterator.iter_any_loop.body,
      core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.next,
      rust_primitives.sequence.seq_len, this, hrem, call_mut_spec]
    by_cases hc : sameCell c a
    · simp [hc]
    · obtain ⟨it, hit⟩ := ih s' hs'
      refine ⟨it, ?_⟩
      unfold core.iter.traits.iterator.iter_any_loop at hit
      simp [core.iter.traits.iterator.iter_any_loop.body,
        core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.next,
        rust_primitives.sequence.seq_len, call_mut_spec] at hit
      simpa [hc] using hit

end Plonky3Lean.Proofs.Air.Extracted
