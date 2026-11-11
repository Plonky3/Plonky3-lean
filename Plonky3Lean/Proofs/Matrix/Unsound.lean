module

public import Plonky3Lean.Proofs.Matrix.Views

@[expose] public section

/-!
# p3-matrix: safe code that reads out of bounds

The views' fields are public, and a safe read does not re-check the invariant a constructor checked.

Such a view passes the read's bound check, then reads the inner matrix out of bounds.

The model fails there, and Rust has undefined behaviour.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM
open Plonky3Lean.Lib Plonky3Lean.Spec.Matrix
open p3_matrix

namespace Plonky3Lean.Proofs.Matrix

variable {T : Type}

/-- The safe read calls the unchecked read once both bound checks pass. -/
theorem get_default_reaches {Self : Type} (MI : Matrix Self T) (x : Self) (H W r c : Std.Usize)
    (hH : MI.height x = ok H) (hW : MI.width x = ok W) (hr : r.val < H.val) (hc : c.val < W.val)
    (hu : MI.get_unchecked x r c = fail .panic) : Matrix.get.default MI x r c = fail .panic := by
  unfold Matrix.get.default
  have hr' : r < H := by scalar_tac
  have hc' : c < W := by scalar_tac
  rw [hH, bind_ok]
  simp only [hr', ite_true, hW, bind_ok, hc', decide_true, core.bool.Bool.then,
    Matrix.get.closure.Insts.CoreOpsFunctionFnOnceTupleT.call_once]
  change (MI.get_unchecked x r c >>= fun x => ok (core.option.Option.Some x)) = _
  rw [hu]; simp

/-- A vertical pair built directly, with a bottom narrower than its top.

Reading the last row at the bottom's width reads past the bottom's buffer. -/
theorem vpair_get_oob (cl : core.clone.Clone T)
    (v : stack.VerticalPair (dense.DenseMatrix T (alloc.vec.Vec T))
      (dense.DenseMatrix T (alloc.vec.Vec T)))
    (hb : (vecList v.bottom.values).length = hB * v.bottom.width.val) (hB1 : 1 ≤ hB)
    (hwb : 0 < v.bottom.width.val) (hw : v.bottom.width.val < v.top.width.val)
    (hsum : (vecList v.top.values).length / v.top.width.val + hB ≤ Usize.max)
    (r c : Std.Usize) (hr : r.val = (vecList v.top.values).length / v.top.width.val + hB - 1)
    (hc : c.val = v.bottom.width.val) :
    Matrix.get.default (VI cl) v r c = fail .panic := by
  have hHb : (vecList v.bottom.values).length / v.bottom.width.val = hB := by
    rw [hb, Nat.mul_div_cancel _ hwb]
  obtain ⟨H, hH, hHv⟩ := spec_imp_exists (vpair_height_eq cl v (by rw [hHb]; exact hsum))
  have hrH : r.val < H.val := by
    rw [hHb] at hHv; rw [hHv, hr]
    generalize (vecList v.top.values).length / v.top.width.val = A
    omega
  have hcW : c.val < v.top.width.val := by rw [hc]; exact hw
  refine get_default_reaches (VI cl) v H v.top.width r c hH rfl hrH hcW ?_
  rw [VI_get_unchecked]
  unfold stack.VerticalPair.Insts.P3_matrixMatrix.get_unchecked
  obtain ⟨H1, h1, h1v⟩ := spec_imp_exists (height_eq cl v.top)
  have e1 : (DI cl).height v.top = ok H1 := h1
  have hr1 : ¬ r < H1 := by scalar_tac
  rw [e1, bind_ok]
  simp only [hr1, ite_false]
  obtain ⟨i, hi, hiv⟩ := spec_imp_exists (UScalar.sub_bv_spec (x := r) (y := H1) (by scalar_tac))
  rw [hi, bind_ok]
  have hi' : i.val = hB - 1 := by rw [hiv.1, hr, h1v]; omega
  obtain ⟨k, rfl⟩ : ∃ k, hB = k + 1 := ⟨hB - 1, by omega⟩
  have hidx : i.val * v.bottom.width.val + c.val = (k + 1) * v.bottom.width.val := by
    rw [hi', hc]; simp; ring
  exact get_unchecked_oob cl v.bottom i c (by rw [hidx, hb])
    (by have := (vs v.bottom.values).property; simp only [vs_val] at this
        rw [hidx, ← hb]; scalar_tac)

/-- A horizontal pair built directly, with a right half shorter than its left.

Reading the right half's missing row reads past its buffer. -/
theorem hpair_get_oob (cl : core.clone.Clone T)
    (v : stack.HorizontalPair (dense.DenseMatrix T (alloc.vec.Vec T))
      (dense.DenseMatrix T (alloc.vec.Vec T)))
    (hR : (vecList v.right.values).length = hr * v.right.width.val) (hwr : 0 < v.right.width.val)
    (hlt : hr < (vecList v.left.values).length / v.left.width.val)
    (hsum : v.left.width.val + v.right.width.val ≤ Usize.max)
    (r c : Std.Usize) (hrv : r.val = hr) (hcv : c.val = v.left.width.val) :
    Matrix.get.default (HI cl) v r c = fail .panic := by
  obtain ⟨W, hW, hWv⟩ := spec_imp_exists (hpair_width_eq cl v hsum)
  obtain ⟨H, hH, hHv⟩ := spec_imp_exists (height_eq cl v.left)
  refine get_default_reaches (HI cl) v H W r c hH hW (by omega) (by omega) ?_
  rw [HI_get_unchecked]
  unfold stack.HorizontalPair.Insts.P3_matrixMatrix.get_unchecked
  have e1 : (DI cl).width v.left = ok v.left.width := rfl
  have hc1 : ¬ c < v.left.width := by scalar_tac
  rw [e1, bind_ok]
  simp only [hc1, ite_false]
  obtain ⟨i, hi, hiv⟩ := spec_imp_exists (UScalar.sub_bv_spec (x := c) (y := v.left.width)
    (by scalar_tac))
  rw [hi, bind_ok]
  have hi0 : i.val = 0 := by rw [hiv.1, hcv]; simp
  have hidx : r.val * v.right.width.val + i.val = (vecList v.right.values).length := by
    rw [hi0, hrv, hR]; simp
  exact get_unchecked_oob cl v.right r i (by rw [hidx])
    (by have := (vs v.right.values).property; simp only [vs_val] at this
        rw [hidx]; scalar_tac)

theorem bitRev_all_ones (k : ℕ) : bitRev k (2 ^ k - 1) = 2 ^ k - 1 := by
  apply Nat.eq_of_testBit_eq; intro j
  rw [testBit_bitRev, Nat.testBit_two_pow_sub_one, Nat.testBit_two_pow_sub_one]
  by_cases hj : j < k <;> simp [hj]; omega

/-- A bit-reversed view whose inner matrix has fewer than 2^k rows.

Row 2^k - 1 maps to inner row 2^k - 1, past the buffer. -/
theorem bitrev_get_oob (cl : core.clone.Clone T)
    (v : row_index_mapped.RowIndexMappedView bitrev.BitReversalPerm
      (dense.DenseMatrix T (alloc.vec.Vec T)))
    (hk : v.index_map.log_height.val < UScalarTy.Usize.numBits)
    (hI : (vecList v.inner.values).length = hi * v.inner.width.val) (hwi : 0 < v.inner.width.val)
    (hlt : hi < 2 ^ v.index_map.log_height.val)
    (hmax : (2 ^ v.index_map.log_height.val - 1) * v.inner.width.val ≤ UScalar.max .Usize)
    (r c : Std.Usize) (hrv : r.val = 2 ^ v.index_map.log_height.val - 1) (hcv : c.val = 0) :
    Matrix.get.default (BI cl) v r c = fail .panic := by
  obtain ⟨H, hH, hHv⟩ := spec_imp_exists (bitrev_height_eq cl v hk)
  have hpos : 0 < 2 ^ v.index_map.log_height.val := by positivity
  refine get_default_reaches (BI cl) v H v.inner.width r c hH rfl (by omega) (by omega) ?_
  rw [BI_get_unchecked]
  unfold row_index_mapped.RowIndexMappedView.Insts.P3_matrixMatrix.get_unchecked
  simp only [bitrev.BitReversalPerm.Insts.P3_matrixRow_index_mappedRowIndexMap.map_row_index]
  obtain ⟨y, hy, hyv⟩ := spec_imp_exists (reverse_bits_len_eq r v.index_map.log_height (by omega)
    (by omega))
  rw [hy, bind_ok]
  rw [hrv, bitRev_all_ones] at hyv
  have hle : hi ≤ 2 ^ v.index_map.log_height.val - 1 := by omega
  exact get_unchecked_oob cl v.inner y c
    (by rw [hyv, hcv, hI, Nat.add_zero]; exact Nat.mul_le_mul_right _ hle)
    (by rw [hyv, hcv]; simpa using hmax)

/-- A strided view whose row map points past its inner matrix.

Row 0 maps to inner row o, at or past the end of the buffer. -/
theorem strided_get_oob (cl : core.clone.Clone T)
    (v : row_index_mapped.RowIndexMappedView strided.VerticallyStridedRowIndexMap
      (dense.DenseMatrix T (alloc.vec.Vec T)))
    (hI : (vecList v.inner.values).length = hi * v.inner.width.val) (hwi : 0 < v.inner.width.val)
    (hh : 0 < v.index_map.height.val) (hoff : hi ≤ v.index_map.offset.val)
    (hmax : v.index_map.offset.val * v.inner.width.val ≤ UScalar.max .Usize)
    (r c : Std.Usize) (hrv : r.val = 0) (hcv : c.val = 0) :
    Matrix.get.default (SI cl) v r c = fail .panic := by
  refine get_default_reaches (SI cl) v v.index_map.height v.inner.width r c rfl rfl (by omega)
    (by omega) ?_
  rw [SI_get_unchecked]
  unfold row_index_mapped.RowIndexMappedView.Insts.P3_matrixMatrix.get_unchecked
  simp only [strided.VerticallyStridedRowIndexMap.Insts.P3_matrixRow_index_mappedRowIndexMap.map_row_index]
  obtain ⟨x, hx, hxv⟩ := spec_imp_exists (UScalar.mul_spec (x := r) (y := v.index_map.stride)
    (by rw [hrv]; simp))
  rw [hx, bind_ok]
  obtain ⟨y, hy, hyv, -⟩ := spec_imp_exists (UScalar.add_bv_spec (x := x) (y := v.index_map.offset)
    (by rw [hxv, hrv]; simp; scalar_tac))
  rw [hy, bind_ok]
  have hyv' : y.val = v.index_map.offset.val := by rw [hyv, hxv, hrv]; simp
  exact get_unchecked_oob cl v.inner y c
    (by rw [hyv', hcv, hI, Nat.add_zero]; exact Nat.mul_le_mul_right _ hoff)
    (by rw [hyv', hcv]; simpa using hmax)

end Plonky3Lean.Proofs.Matrix
