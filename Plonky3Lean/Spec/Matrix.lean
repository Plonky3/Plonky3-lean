module

public import Mathlib.Data.Matrix.ColumnRowPartitioned
public import Mathlib.Logic.Equiv.Fin.Basic
public import P3Matrix

@[expose] public section

/-!
# Matrices, as p3-matrix stores and views them

A matrix is a function of the row and the column.

Each storage and view of p3-matrix is read as one, so that later crates can reuse these objects.

A row-major buffer l of width w holds floor(|l| / w) rows of w entries, entry (r, c) at index r w + c.

```text
    l = [a, b, c, d, e],  w = 2:     | a b |
                                     | c d |     e belongs to no row
```
-/

namespace Plonky3Lean.Spec.Matrix

/-- A matrix with h rows and w columns. -/
abbrev Mat (h w : ℕ) (T : Type _) := Matrix (Fin h) (Fin w) T

variable {T : Type _}

/-- Entry (r, c) when r < h and c < w, and nothing otherwise. -/
def get? {h w : ℕ} (M : Mat h w T) (r c : ℕ) : Option T :=
  if hr : r < h then if hc : c < w then some (M ⟨r, hr⟩ ⟨c, hc⟩) else none else none

/-- The matrix a row-major buffer of width w holds.

It has floor(|l| / w) rows, and none at width 0. -/
def rowMajor (l : List T) (w : ℕ) : Mat (l.length / w) w T :=
  Matrix.of fun r c => l[r.val * w + c.val]'(by
    have hr := r.isLt
    have hc := c.isLt
    have hw : 0 < w := by omega
    have : (r.val + 1) * w ≤ l.length := by
      have := (Nat.le_div_iff_mul_le hw).mp (Nat.succ_le_of_lt hr); simpa using this
    nlinarith)

/-- The same matrix, with its row count rewritten along an equality. -/
def castRows {h h' w : ℕ} (M : Mat h w T) (hh : h = h') : Mat h' w T :=
  Matrix.of fun r c => M (Fin.cast hh.symm r) c

/-- The same matrix, with its column count rewritten along an equality. -/
def castCols {h w w' : ℕ} (M : Mat h w T) (hw : w = w') : Mat h w' T :=
  Matrix.of fun r c => M r (Fin.cast hw.symm c)

/-- The reversal of the k low bits of i.

For j < k, bit j of the result is bit k - 1 - j of i.

Bits of i at position k and above are dropped.

```text
    k = 3:   i = 0b011  ->  0b110
```
-/
def bitRev : ℕ → ℕ → ℕ
  | 0, _ => 0
  | k + 1, i => (i % 2) * 2 ^ k + bitRev k (i / 2)

/-- The rows in bit-reversed order: row r is row rev_k(r).

The reduction modulo 2^k changes nothing, and only keeps the index in range by construction. -/
def bitRevRows {k w : ℕ} (M : Mat (2 ^ k) w T) : Mat (2 ^ k) w T :=
  Matrix.of fun r c => M ⟨bitRev k r.val % 2 ^ k, Nat.mod_lt _ (by positivity)⟩ c

/-- The number of rows o, o + s, o + 2 s, ... below h.

It is ceil((h - o) / s), and 0 for s = 0. -/
def stridedHeight (h stride offset : ℕ) : ℕ := (h - offset + stride - 1) / stride

/-- Rows o, o + s, o + 2 s, ... of a matrix. -/
def stridedRows {h w : ℕ} (M : Mat h w T) (stride offset : ℕ) :
    Mat (stridedHeight h stride offset) w T :=
  Matrix.of fun r c => M ⟨offset + r.val * stride, by
    have hr := r.isLt
    unfold stridedHeight at hr
    have hs : 0 < stride := by
      rcases Nat.eq_zero_or_pos stride with h0 | h0
      · simp [h0] at hr
      · exact h0
    have := (Nat.le_div_iff_mul_le hs).mp (Nat.succ_le_of_lt hr)
    have : r.val * stride + stride ≤ h - offset + stride - 1 := by nlinarith
    omega⟩ c

/-- Columns s to e - 1 of a matrix. -/
def colRange {h w : ℕ} (M : Mat h w T) (s e : ℕ) (he : e ≤ w) : Mat h (e - s) T :=
  Matrix.of fun r c => M r ⟨s + c.val, by have := c.isLt; omega⟩

/-- One matrix above another. -/
def vstack {h₁ h₂ w : ℕ} (A : Mat h₁ w T) (B : Mat h₂ w T) : Mat (h₁ + h₂) w T :=
  (Matrix.fromRows A B).submatrix finSumFinEquiv.symm id

/-- One matrix left of another. -/
def hstack {h w₁ w₂ : ℕ} (A : Mat h w₁ T) (B : Mat h w₂ T) : Mat h (w₁ + w₂) T :=
  (Matrix.fromCols A B).submatrix id finSumFinEquiv.symm

/-- A matrix with two rows exchanged. -/
def swapRows {h w : ℕ} (M : Mat h w T) (i j : Fin h) : Mat h w T :=
  M.submatrix (Equiv.swap i j) id

/-- A matrix above rows of a fill value, up to a larger height. -/
def padRows {h w : ℕ} (M : Mat h w T) (h' : ℕ) (fill : T) : Mat h' w T :=
  Matrix.of fun r c => if hr : r.val < h then M ⟨r.val, hr⟩ c else fill

/-- A matrix left of columns of a fill value, up to a larger width. -/
def padCols {h w : ℕ} (M : Mat h w T) (w' : ℕ) (fill : T) : Mat h w' T :=
  Matrix.of fun r c => if hc : c.val < w then M r ⟨c.val, hc⟩ else fill

/-! ## Reading the model -/

/-- The elements of a vector, which the model stores as a slice. -/
def vecList (v : CoreModels.alloc.vec.Vec T) : List T := (v : Aeneas.Std.Slice T).val

open p3_matrix in
/-- The matrix a dense matrix holds: its buffer, read row-major at its width. -/
def dense (m : dense.DenseMatrix T (CoreModels.alloc.vec.Vec T)) :
    Mat ((vecList m.values).length / m.width.val) m.width.val T :=
  rowMajor (vecList m.values) m.width.val

/-! ## The model's instances

Names for the instances the claims use.

They specify nothing. -/

section instances
open p3_matrix
open Aeneas.Std hiding namespace core alloc
open CoreModels

variable {T : Type}

/-- Vector storage. -/
abbrev VS (cl : core.clone.Clone T) := alloc.vec.Vec.Insts.P3_matrixDenseDenseStorage cl

/-- A clone that returns its argument, as every copyable type's does. -/
def LawfulClone (cl : core.clone.Clone T) : Prop := ∀ x, cl.clone x = Aeneas.Std.RustM.ok x

/-- The dense matrix over vector storage. -/
abbrev DI (cl : core.clone.Clone T) := dense.DenseMatrix.Insts.P3_matrixMatrix cl (VS cl)

/-- A bit-reversed view of a dense matrix. -/
abbrev BI (cl : core.clone.Clone T) :=
  row_index_mapped.RowIndexMappedView.Insts.P3_matrixMatrix cl
    bitrev.BitReversalPerm.Insts.P3_matrixRow_index_mappedRowIndexMap (DI cl)

/-- A strided view of a dense matrix. -/
abbrev SI (cl : core.clone.Clone T) :=
  row_index_mapped.RowIndexMappedView.Insts.P3_matrixMatrix cl
    strided.VerticallyStridedRowIndexMap.Insts.P3_matrixRow_index_mappedRowIndexMap (DI cl)

/-- A column range of a dense matrix. -/
abbrev TI (cl : core.clone.Clone T) :=
  horizontally_truncated.HorizontallyTruncated.Insts.P3_matrixMatrix cl (DI cl)

/-- Two dense matrices stacked vertically. -/
abbrev VI (cl : core.clone.Clone T) := stack.VerticalPair.Insts.P3_matrixMatrix cl (DI cl) (DI cl)

/-- Two dense matrices side by side. -/
abbrev HI (cl : core.clone.Clone T) :=
  stack.HorizontalPair.Insts.P3_matrixMatrix cl (DI cl) (DI cl)

end instances

end Plonky3Lean.Spec.Matrix
