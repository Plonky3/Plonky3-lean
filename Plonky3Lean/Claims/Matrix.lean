module

public import Plonky3Lean.Proofs.Matrix.Unsound
public import Plonky3Lean.Proofs.Matrix.Interpolation

@[expose] public section

/-!
# p3-matrix: claims

The dense matrix and its views, generic over the element type, and the interpolation routines.

A matrix is read as a function of the row and the column.

A dense buffer of length len and width w holds floor(len / w) rows, and none at width 0.

The extracted model checks arithmetic, as a debug build does, so an overflow panics.

Element access clones, and the claims assume a clone that returns its argument.

rev_k(i) reverses the k low bits of i.

The interpolation routines are transcriptions over a field K, not extractions.

Rows given in the base field are read in K through its embedding.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open p3_matrix
open Plonky3Lean.Spec.Matrix

namespace Plonky3Lean.Claims.Matrix

variable {T : Type}

/-! ## Dense storage -/

/-- The height is floor(len / w), and 0 at width 0.

It never panics. -/
theorem dense.height (cl : core.clone.Clone T) (m : dense.DenseMatrix T (alloc.vec.Vec T)) :
    dense.DenseMatrix.Insts.P3_matrixMatrix.height cl (VS cl) m ⦃ h =>
      h.val = (vecList m.values).length / m.width.val ⦄ :=
  Proofs.Matrix.height_eq cl m

/-- Reading entry (r, c) returns that entry, or nothing outside the shape.

It never panics, for any buffer and width.

This includes a buffer with a partial last row, which a release build or a write to the public width can create. -/
theorem dense.get (cl : core.clone.Clone T) (hcl : LawfulClone cl)
    (m : dense.DenseMatrix T (alloc.vec.Vec T)) (r c : Std.Usize) :
    Matrix.get.default (DI cl) m r c ⦃ o => o = get? (dense m) r.val c.val ⦄ :=
  Proofs.Matrix.get_eq cl hcl m r c

/-- The unchecked read of (r, c) returns element r w + c when it lies in the buffer. -/
theorem dense.get_unchecked (cl : core.clone.Clone T) (hcl : LawfulClone cl)
    (m : dense.DenseMatrix T (alloc.vec.Vec T)) (r c : Std.Usize)
    (h : r.val * m.width.val + c.val < (vecList m.values).length) :
    dense.DenseMatrix.Insts.P3_matrixMatrix.get_unchecked cl (VS cl) m r c ⦃ x =>
      x = (vecList m.values)[r.val * m.width.val + c.val] ⦄ :=
  Proofs.Matrix.get_unchecked_eq cl hcl m r c h

/-- Past the buffer, the unchecked read fails in the model.

In Rust it is an out-of-bounds read. -/
theorem dense.get_unchecked.out_of_bounds (cl : core.clone.Clone T)
    (m : dense.DenseMatrix T (alloc.vec.Vec T)) (r c : Std.Usize)
    (h : (vecList m.values).length ≤ r.val * m.width.val + c.val)
    (hmax : r.val * m.width.val + c.val ≤ UScalar.max .Usize) :
    dense.DenseMatrix.Insts.P3_matrixMatrix.get_unchecked cl (VS cl) m r c = .fail .panic :=
  Proofs.Matrix.get_unchecked_oob cl m r c h hmax

/-- The constructor panics, by a debug assertion, exactly when w does not divide len.

Width 0 divides only 0.

A release build skips the check. -/
theorem dense.new (cl : core.clone.Clone T) (values : alloc.vec.Vec T) (width : Std.Usize) :
    dense.DenseMatrix.new cl (VS cl) values width =
      if (width.val = 0 ∧ (vecList values).length = 0) ∨
          (width.val ≠ 0 ∧ (vecList values).length % width.val = 0)
      then .ok { values, width, _phantom := () } else .fail .panic :=
  Proofs.Matrix.new_eq cl values width

/-! ## Bit-reversed rows -/

/-- Viewing a matrix of height 2^k in bit-reversed order keeps the matrix and records k. -/
theorem bitrev.new_view (cl : core.clone.Clone T) (m : dense.DenseMatrix T (alloc.vec.Vec T))
    {k : ℕ} (hk : k < UScalarTy.Usize.numBits)
    (hm : (vecList m.values).length / m.width.val = 2 ^ k) :
    bitrev.BitReversalPerm.new_view cl (DI cl) m ⦃ v =>
      v.inner = m ∧ v.index_map.log_height.val = k ⦄ :=
  Proofs.Matrix.bitrev_view_eq cl m hk hm

/-- The bit-reversed view panics unless the height is a power of two.

Height 0 panics too, although the slice routine accepts an empty slice. -/
theorem bitrev.new_view.panics (cl : core.clone.Clone T) (m : dense.DenseMatrix T (alloc.vec.Vec T))
    (hm : ∀ k, (vecList m.values).length / m.width.val ≠ 2 ^ k) :
    bitrev.BitReversalPerm.new_view cl (DI cl) m = .fail .panic :=
  Proofs.Matrix.bitrev_view_panics cl m hm

/-- A bit-reversed view over 2^k rows has row r equal to inner row rev_k(r).

The view's constructor sets up the 2^k rows. -/
theorem bitrev.get (cl : core.clone.Clone T) (hcl : LawfulClone cl)
    (v : row_index_mapped.RowIndexMappedView bitrev.BitReversalPerm
      (dense.DenseMatrix T (alloc.vec.Vec T)))
    (hk : v.index_map.log_height.val < UScalarTy.Usize.numBits)
    (hinner : (vecList v.inner.values).length / v.inner.width.val = 2 ^ v.index_map.log_height.val)
    (r c : Std.Usize) :
    Matrix.get.default (BI cl) v r c ⦃ o =>
      o = get? (bitRevRows (castRows (dense v.inner) hinner)) r.val c.val ⦄ :=
  Proofs.Matrix.bitrev_get_eq cl hcl v hk hinner r c

/-- Viewing rows bit-reversed twice gives the matrix back. -/
theorem bitRevRows_bitRevRows {k w : ℕ} (M : Mat (2 ^ k) w T) : bitRevRows (bitRevRows M) = M :=
  Proofs.Matrix.bitRevRows_bitRevRows M

/-- The identity behind bit-reversed zero padding.

Bit-reverse 2^n rows, append zero rows up to 2^(n + k), and bit-reverse again.

Row i of the input lands at row i 2^k, and every other row is zero.

```text
    n = 1, k = 1:   [a, b]  ->  [a, b, 0, 0]  ->  [a, 0, b, 0]
``` -/
theorem bit_reversed_zero_pad.identity [Zero T] {n k w : ℕ} (M : Mat (2 ^ n) w T) :
    bitRevRows (k := n + k) (padRows (bitRevRows M) (2 ^ (n + k)) 0) =
      Matrix.of fun i c => if _ : 2 ^ k ∣ i.val then M ⟨i.val / 2 ^ k, by
        have h1 : i.val < 2 ^ n * 2 ^ k := by rw [← pow_add]; exact i.isLt
        exact Nat.div_lt_of_lt_mul (by rw [mul_comm]; exact h1)⟩ c else 0 :=
  Proofs.Matrix.bitRevRows_padRows_bitRevRows M

/-- Reversing k bits twice is the identity on [0, 2^k). -/
theorem bitRev_bitRev {k i : ℕ} (hi : i < 2 ^ k) : bitRev k (bitRev k i) = i :=
  Proofs.Matrix.bitRev_bitRev hi

/-! ## p3-util's bit helpers -/

/-- The strict base-2 logarithm of 2^k is k. -/
theorem log2_strict_usize (n : Std.Usize) {k : ℕ} (hk : k < UScalarTy.Usize.numBits)
    (hn : n.val = 2 ^ k) : p3_util.log2_strict_usize n ⦃ r => r.val = k ⦄ :=
  Proofs.Matrix.log2_strict_usize_two_pow hk n hn

/-- The strict base-2 logarithm panics unless its input is a power of two.

This includes the input 0. -/
theorem log2_strict_usize.panics (n : Std.Usize) (hn : ∀ k, n.val ≠ 2 ^ k) :
    p3_util.log2_strict_usize n = .fail .panic :=
  Proofs.Matrix.log2_strict_usize_panics n hn

/-- Reversing the k low bits of x, for x < 2^k and k at most the word size, gives rev_k(x). -/
theorem reverse_bits_len (x k : Std.Usize) (hk : k.val ≤ UScalarTy.Usize.numBits)
    (hx : x.val < 2 ^ k.val) : p3_util.reverse_bits_len x k ⦃ y => y.val = bitRev k.val x.val ⦄ :=
  Proofs.Matrix.reverse_bits_len_eq x k hk hx

/-! ## Strided rows -/

/-- A strided view with stride s > 0 and offset o keeps the matrix.

It records ceil((h - o) / s) rows, and 0 when o >= h. -/
theorem strided.new_view (cl : core.clone.Clone T) (m : dense.DenseMatrix T (alloc.vec.Vec T))
    (stride offset : Std.Usize) (hs : 0 < stride.val) :
    Matrix.vertically_strided.default (DI cl) m stride offset ⦃ v => v.inner = m ∧
      v.index_map.stride = stride ∧ v.index_map.offset = offset ∧
      v.index_map.height.val =
        stridedHeight ((vecList m.values).length / m.width.val) stride.val offset.val ⦄ :=
  Proofs.Matrix.strided_view_eq cl m stride offset hs

/-- A strided view with stride 0 panics. -/
theorem strided.new_view.panics (cl : core.clone.Clone T) (m : dense.DenseMatrix T (alloc.vec.Vec T))
    (offset : Std.Usize) : Matrix.vertically_strided.default (DI cl) m 0#usize offset = .fail .panic :=
  Proofs.Matrix.strided_view_panics cl m offset

/-- A strided view with that height reads rows o, o + s, o + 2 s, and so on. -/
theorem strided.get (cl : core.clone.Clone T) (hcl : LawfulClone cl)
    (v : row_index_mapped.RowIndexMappedView strided.VerticallyStridedRowIndexMap
      (dense.DenseMatrix T (alloc.vec.Vec T)))
    (hv : v.index_map.height.val = stridedHeight ((vecList v.inner.values).length / v.inner.width.val)
      v.index_map.stride.val v.index_map.offset.val)
    (r c : Std.Usize) :
    Matrix.get.default (SI cl) v r c ⦃ o => o = get? (castRows (stridedRows (dense v.inner)
      v.index_map.stride.val v.index_map.offset.val) hv.symm) r.val c.val ⦄ :=
  Proofs.Matrix.strided_get_eq cl hcl v hv r c

/-! ## A column range -/

/-- A column range s..e is accepted exactly when s <= e <= w. -/
theorem truncated.new_with_range (cl : core.clone.Clone T)
    (m : dense.DenseMatrix T (alloc.vec.Vec T)) (rg : core.ops.range.Range Std.Usize) :
    horizontally_truncated.HorizontallyTruncated.new_with_range (DI cl) cl m rg ⦃ o =>
      o = if rg.start.val ≤ rg.end.val ∧ rg.end.val ≤ m.width.val then
        core.option.Option.Some { inner := m, column_range := rg, _phantom := () }
      else core.option.Option.None ⦄ :=
  Proofs.Matrix.truncated_new_with_range_eq cl m rg

/-- A column range s..e with e <= w reads columns s to e - 1. -/
theorem truncated.get (cl : core.clone.Clone T) (hcl : LawfulClone cl)
    (v : horizontally_truncated.HorizontallyTruncated T (dense.DenseMatrix T (alloc.vec.Vec T)))
    (he : v.column_range.end.val ≤ v.inner.width.val) (r c : Std.Usize) :
    Matrix.get.default (TI cl) v r c ⦃ o => o = get? (colRange (dense v.inner)
      v.column_range.start.val v.column_range.end.val he) r.val c.val ⦄ :=
  Proofs.Matrix.truncated_get_eq cl hcl v he r c

/-! ## Stacking -/

/-- Stacking two matrices vertically panics exactly when their widths differ. -/
theorem vpair.new (cl : core.clone.Clone T) (top bottom : dense.DenseMatrix T (alloc.vec.Vec T)) :
    stack.VerticalPair.new cl (DI cl) (DI cl) top bottom =
      if top.width = bottom.width then .ok { top, bottom } else .fail .panic :=
  Proofs.Matrix.vpair_new_eq cl top bottom

/-- Placing two matrices side by side panics exactly when their heights differ. -/
theorem hpair.new (cl : core.clone.Clone T) (left right : dense.DenseMatrix T (alloc.vec.Vec T)) :
    stack.HorizontalPair.new cl (DI cl) (DI cl) left right =
      if (vecList left.values).length / left.width.val =
        (vecList right.values).length / right.width.val then .ok { left, right }
      else .fail .panic :=
  Proofs.Matrix.hpair_new_eq cl left right

/-- A vertical pair of equal widths is the top matrix above the bottom one. -/
theorem vpair.get (cl : core.clone.Clone T) (hcl : LawfulClone cl)
    (v : stack.VerticalPair (dense.DenseMatrix T (alloc.vec.Vec T))
      (dense.DenseMatrix T (alloc.vec.Vec T)))
    (hw : v.bottom.width.val = v.top.width.val)
    (hsum : (vecList v.top.values).length / v.top.width.val +
      (vecList v.bottom.values).length / v.bottom.width.val ≤ Usize.max) (r c : Std.Usize) :
    Matrix.get.default (VI cl) v r c ⦃ o =>
      o = get? (vstack (dense v.top) (castCols (dense v.bottom) hw)) r.val c.val ⦄ :=
  Proofs.Matrix.vpair_get_eq cl hcl v hw hsum r c

/-- A vertical pair whose heights sum past the word size never returns a height in the model. -/
theorem vpair.height.overflow (cl : core.clone.Clone T)
    (v : stack.VerticalPair (dense.DenseMatrix T (alloc.vec.Vec T))
      (dense.DenseMatrix T (alloc.vec.Vec T)))
    (hsum : Usize.max < (vecList v.top.values).length / v.top.width.val +
      (vecList v.bottom.values).length / v.bottom.width.val) :
    ∀ x, (VI cl).height v ≠ .ok x :=
  Proofs.Matrix.vpair_height_overflow cl v hsum

/-- A horizontal pair of equal heights is the left matrix beside the right one. -/
theorem hpair.get (cl : core.clone.Clone T) (hcl : LawfulClone cl)
    (v : stack.HorizontalPair (dense.DenseMatrix T (alloc.vec.Vec T))
      (dense.DenseMatrix T (alloc.vec.Vec T)))
    (hh : (vecList v.right.values).length / v.right.width.val =
      (vecList v.left.values).length / v.left.width.val)
    (hsum : v.left.width.val + v.right.width.val ≤ Usize.max) (r c : Std.Usize) :
    Matrix.get.default (HI cl) v r c ⦃ o =>
      o = get? (hstack (dense v.left) (castRows (dense v.right) hh)) r.val c.val ⦄ :=
  Proofs.Matrix.hpair_get_eq cl hcl v hh hsum r c

/-! ## Undefined behaviour from safe code

The views' fields are public, and a safe read does not re-check the invariants their constructors set up.

Each claim builds such a view, and reads an entry that passes the read's bound check.

The read then calls the inner unchecked read out of bounds.

That fails in the model, and is undefined behaviour in Rust. -/

/-- A vertical pair built directly, with a bottom narrower than its top.

Reading the last row at the bottom's width reads past the bottom's buffer. -/
theorem vpair.get.unsound (cl : core.clone.Clone T)
    (v : stack.VerticalPair (dense.DenseMatrix T (alloc.vec.Vec T))
      (dense.DenseMatrix T (alloc.vec.Vec T)))
    (hb : (vecList v.bottom.values).length = hB * v.bottom.width.val) (hB1 : 1 ≤ hB)
    (hwb : 0 < v.bottom.width.val) (hw : v.bottom.width.val < v.top.width.val)
    (hsum : (vecList v.top.values).length / v.top.width.val + hB ≤ Usize.max)
    (r c : Std.Usize) (hr : r.val = (vecList v.top.values).length / v.top.width.val + hB - 1)
    (hc : c.val = v.bottom.width.val) :
    Matrix.get.default (VI cl) v r c = .fail .panic :=
  Proofs.Matrix.vpair_get_oob cl v hb hB1 hwb hw hsum r c hr hc

/-- A horizontal pair built directly, with a right half shorter than its left.

Reading the right half's missing row reads past its buffer. -/
theorem hpair.get.unsound (cl : core.clone.Clone T)
    (v : stack.HorizontalPair (dense.DenseMatrix T (alloc.vec.Vec T))
      (dense.DenseMatrix T (alloc.vec.Vec T)))
    (hR : (vecList v.right.values).length = hr * v.right.width.val) (hwr : 0 < v.right.width.val)
    (hlt : hr < (vecList v.left.values).length / v.left.width.val)
    (hsum : v.left.width.val + v.right.width.val ≤ Usize.max)
    (r c : Std.Usize) (hrv : r.val = hr) (hcv : c.val = v.left.width.val) :
    Matrix.get.default (HI cl) v r c = .fail .panic :=
  Proofs.Matrix.hpair_get_oob cl v hR hwr hlt hsum r c hrv hcv

/-- A bit-reversed view whose inner matrix was replaced by one with fewer than 2^k rows.

Row 2^k - 1 maps to inner row 2^k - 1, past the buffer. -/
theorem bitrev.get.unsound (cl : core.clone.Clone T)
    (v : row_index_mapped.RowIndexMappedView bitrev.BitReversalPerm
      (dense.DenseMatrix T (alloc.vec.Vec T)))
    (hk : v.index_map.log_height.val < UScalarTy.Usize.numBits)
    (hI : (vecList v.inner.values).length = hi * v.inner.width.val) (hwi : 0 < v.inner.width.val)
    (hlt : hi < 2 ^ v.index_map.log_height.val)
    (hmax : (2 ^ v.index_map.log_height.val - 1) * v.inner.width.val ≤ UScalar.max .Usize)
    (r c : Std.Usize) (hrv : r.val = 2 ^ v.index_map.log_height.val - 1) (hcv : c.val = 0) :
    Matrix.get.default (BI cl) v r c = .fail .panic :=
  Proofs.Matrix.bitrev_get_oob cl v hk hI hwi hlt hmax r c hrv hcv

/-- A strided view whose row map was taken from a view of a taller matrix.

Row 0 maps to inner row o, at or past the end of the buffer. -/
theorem strided.get.unsound (cl : core.clone.Clone T)
    (v : row_index_mapped.RowIndexMappedView strided.VerticallyStridedRowIndexMap
      (dense.DenseMatrix T (alloc.vec.Vec T)))
    (hI : (vecList v.inner.values).length = hi * v.inner.width.val) (hwi : 0 < v.inner.width.val)
    (hh : 0 < v.index_map.height.val) (hoff : hi ≤ v.index_map.offset.val)
    (hmax : v.index_map.offset.val * v.inner.width.val ≤ UScalar.max .Usize)
    (r c : Std.Usize) (hrv : r.val = 0) (hcv : c.val = 0) :
    Matrix.get.default (SI cl) v r c = .fail .panic :=
  Proofs.Matrix.strided_get_oob cl v hI hwi hh hoff hmax r c hrv hcv

/-! ## Interpolation, transcribed

The coset is g H, with H the subgroup of order N = 2^k generated by omega.

The evaluation domain is the points x_i, and P_c is the Lagrange interpolant of column c. -/

section interpolation

open Polynomial Finset Lagrange
open p3_matrix.interpolation.mirror

variable {K : Type _} [Field K] [DecidableEq K]

/-- Coset interpolation evaluates the interpolant of each column at z, for every z.

This covers a point on the coset, the point 0, and every other point.

A zero shift panics. -/
theorem interpolate_coset.spec {ω g z : K} {k w : ℕ} (hω : IsPrimitiveRoot ω (2 ^ k))
    (hN : (2 : K) ≠ 0) (M : Fin (2 ^ k) → Fin w → K) :
    interpolate_coset k ω g z M = if g = 0 then none else
      some fun c => eval z (interpolate univ (fun i : Fin (2 ^ k) => g * ω ^ i.val)
        fun i => M i c) :=
  Proofs.Matrix.Interp.interpolate_coset_eq hω hN M

/-- Any polynomial of degree below 2^k that matches column c on the coset gives the same value at z. -/
theorem interpolate_coset.unique {ω g z : K} {k w : ℕ} (hω : IsPrimitiveRoot ω (2 ^ k))
    (hN : (2 : K) ≠ 0) (hg : g ≠ 0) (M : Fin (2 ^ k) → Fin w → K) (P : Fin w → K[X])
    (hP : ∀ c, (P c).degree < (2 ^ k : ℕ))
    (hPe : ∀ c i, (P c).eval (g * ω ^ (i : Fin (2 ^ k)).val) = M i c) :
    interpolate_coset k ω g z M = some fun c => (P c).eval z :=
  Proofs.Matrix.Interp.interpolate_coset_unique hω hN hg M P hP hPe

/-- The precomputed coset path at z = 0 returns zero in every column, whatever the weights.

Only a debug assertion rejects that point, so a release build returns zeros instead of the column means. -/
theorem interpolate_coset_with_precomputation.at_zero {k w : ℕ} (M : Fin (2 ^ k) → Fin w → K)
    (g : K) (adj : Fin (2 ^ k) → K) :
    interpolate_coset_with_precomputation k M g 0 adj =
      if g ^ 2 ^ k * (2 ^ k : K) = 0 then none else some fun _ => 0 :=
  Proofs.Matrix.Interp.interpolate_coset_with_precomputation_zero M g adj

/-- The barycentric weights are 1 / prod_{j != i} (x_i - x_j), and two equal points give none. -/
theorem barycentric_weights.spec {n : ℕ} (x : Fin n → K) :
    barycentric_weights x =
      if Function.Injective x then some fun i => nodalWeight univ x i else none :=
  Proofs.Matrix.Interp.barycentric_weights_eq x

/-- Interpolation at an arbitrary point evaluates the interpolant of each column at z.

Two equal points give none, and no points give zero. -/
theorem interpolate_arbitrary_point.spec {n w : ℕ} (M : Fin n → Fin w → K) (x : Fin n → K) (z : K) :
    interpolate_arbitrary_point M x z = if Function.Injective x then
      some fun c => eval z (interpolate univ x fun i => M i c) else none :=
  Proofs.Matrix.Interp.interpolate_arbitrary_point_eq M x z

/-- Newton's recovery returns the coefficients of each column's interpolant, and none on equal points. -/
theorem recover_coefficients.spec {n w : ℕ} (M : Fin n → Fin w → K) (x : Fin n → K) :
    recover_coefficients M x = if Function.Injective x then
      some fun i c => (interpolate univ x fun m => M m c).coeff i.val else none :=
  Proofs.Matrix.Interp.recover_coefficients_eq M x

/-- Lagrange interpolation from pairs returns the interpolant's coefficients, and none on equal x. -/
theorem interpolate_lagrange.spec {n : ℕ} (pts : Fin n → K × K) :
    interpolate_lagrange pts = if Function.Injective (fun i => (pts i).1) then
      some fun i => (interpolate univ (fun i => (pts i).1) fun m => (pts m).2).coeff i.val
    else none :=
  Proofs.Matrix.Interp.interpolate_lagrange_eq pts

end interpolation

/-! ## Bit reversal in place, transcribed -/

section swaps

open p3_matrix.util.mirror

variable {R : Type _} {h : ℕ}

/-- Swapping row i with row rev(i) whenever i < rev(i) puts row rev(r) at row r, for an involution rev. -/
theorem reverse_matrix_index_bits.spec (rev : Fin h → Fin h) (hrev : ∀ i, rev (rev i) = i)
    (rows : Fin h → R) : reverse_matrix_index_bits rev rows = fun r => rows (rev r) :=
  Proofs.Matrix.BitRevSwap.reverse_matrix_index_bits_eq rev hrev rows

/-- Two swaps started from different rows touch four different rows.

So the parallel swaps never alias a row. -/
theorem reverse_matrix_index_bits.disjoint (rev : Fin h → Fin h) (hrev : ∀ i, rev (rev i) = i)
    (i i' : Fin h) (hi : i < rev i) (hi' : i' < rev i') (hne : i ≠ i') :
    i ≠ rev i' ∧ rev i ≠ i' ∧ rev i ≠ rev i' :=
  Proofs.Matrix.BitRevSwap.swaps_disjoint rev hrev i i' hi hi' hne

end swaps

/-! ## The flattened extension view, transcribed

Each extension element has D coordinates in the base field. -/

section flat

open p3_matrix.extension.mirror

variable {F EF : Type _} [Inhabited F]

/-- A run of the flat row is the slice [start, end) of the row's coordinates laid end to end. -/
theorem flat.row_subseq (D : ℕ) (coords : EF → List F) (hc : ∀ a, (coords a).length = D)
    (hD : 0 < D) (row : List EF) (start stop : ℕ) :
    flat_row_subseq D coords row start stop =
      ((row.flatMap coords).drop start).take (stop - start) :=
  Proofs.Matrix.Flat.flat_row_subseq_eq D coords hc hD row start stop

/-- Column c of the flat view is in range exactly when element c / D and coordinate c mod D are. -/
theorem flat.index (D : ℕ) {w c : ℕ} (hD : 0 < D) : c < w * D ↔ c / D < w ∧ c % D < D :=
  Proofs.Matrix.Flat.flat_index_contract D hD

end flat

end Plonky3Lean.Claims.Matrix
