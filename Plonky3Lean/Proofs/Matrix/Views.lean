module

public import Plonky3Lean.Proofs.Matrix.Dense
public import Plonky3Lean.Proofs.Matrix.Log2

@[expose] public section

/-!
# p3-matrix: the views

Each view over a dense matrix, against the operation on matrices it stands for.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM
open Plonky3Lean.Lib Plonky3Lean.Spec.Matrix
open p3_matrix

namespace Plonky3Lean.Proofs.Matrix

variable {T : Type}

/-! ## Bit-reversed rows -/

theorem BI_get_unchecked (cl : core.clone.Clone T) :
    (BI cl).get_unchecked = row_index_mapped.RowIndexMappedView.Insts.P3_matrixMatrix.get_unchecked cl
      bitrev.BitReversalPerm.Insts.P3_matrixRow_index_mappedRowIndexMap (DI cl) := rfl

theorem DI_get_unchecked (cl : core.clone.Clone T) :
    (DI cl).get_unchecked = dense.DenseMatrix.Insts.P3_matrixMatrix.get_unchecked cl (VS cl) := rfl

theorem bitrev_height_eq (cl : core.clone.Clone T)
    (v : row_index_mapped.RowIndexMappedView bitrev.BitReversalPerm
      (dense.DenseMatrix T (alloc.vec.Vec T)))
    (hk : v.index_map.log_height.val < UScalarTy.Usize.numBits) :
    row_index_mapped.RowIndexMappedView.Insts.P3_matrixMatrix.height cl
      bitrev.BitReversalPerm.Insts.P3_matrixRow_index_mappedRowIndexMap (DI cl) v ⦃ h =>
        h.val = 2 ^ v.index_map.log_height.val ⦄ := by
  unfold row_index_mapped.RowIndexMappedView.Insts.P3_matrixMatrix.height
  simp only [bitrev.BitReversalPerm.Insts.P3_matrixRow_index_mappedRowIndexMap.height]
  step*
  rw [h_post, Nat.one_shiftLeft, Nat.mod_eq_of_lt]
  have : Usize.size = 2 ^ System.Platform.numBits := by simp [Usize.size, Usize.numBits]
  rw [this]; exact Nat.pow_lt_pow_right (by norm_num) hk

/-- A bit-reversed view over 2^k rows is its inner matrix with rows in bit-reversed order. -/
theorem bitrev_get_eq (cl : core.clone.Clone T) (hcl : LawfulClone cl)
    (v : row_index_mapped.RowIndexMappedView bitrev.BitReversalPerm
      (dense.DenseMatrix T (alloc.vec.Vec T)))
    (hk : v.index_map.log_height.val < UScalarTy.Usize.numBits)
    (hinner : (vecList v.inner.values).length / v.inner.width.val = 2 ^ v.index_map.log_height.val)
    (r c : Std.Usize) :
    Matrix.get.default (BI cl) v r c ⦃ o =>
      o = get? (bitRevRows (castRows (dense v.inner) hinner)) r.val c.val ⦄ := by
  obtain ⟨H, hH, hHv⟩ := spec_imp_exists (bitrev_height_eq cl v hk)
  refine get_default_spec (BI cl) v _ H v.inner.width hH hHv rfl rfl ?_ r c
  intro r c hr hc
  rw [BI_get_unchecked]
  unfold row_index_mapped.RowIndexMappedView.Insts.P3_matrixMatrix.get_unchecked
  simp only [bitrev.BitReversalPerm.Insts.P3_matrixRow_index_mappedRowIndexMap.map_row_index]
  have hrb := reverse_bits_len_eq r v.index_map.log_height (by omega) hr
  obtain ⟨y, hy, hyv⟩ := spec_imp_exists hrb
  rw [hy, bind_ok]
  have hylt : y.val < 2 ^ v.index_map.log_height.val := hyv ▸ bitRev_lt _ _
  have hidx : y.val * v.inner.width.val + c.val < (vecList v.inner.values).length := by
    have hw : 0 < v.inner.width.val := by omega
    rw [← hinner] at hylt
    have := (Nat.le_div_iff_mul_le hw).mp (Nat.succ_le_of_lt hylt); nlinarith
  have := get_unchecked_eq cl hcl v.inner y c hidx
  refine WP.spec_mono this ?_
  intro x hx
  simp [hx, bitRevRows, castRows, dense, rowMajor, hyv, Nat.mod_eq_of_lt (bitRev_lt _ _)]

/-- Viewing a matrix of height 2^k bit-reversed keeps the matrix and records k. -/
theorem bitrev_view_eq (cl : core.clone.Clone T) (m : dense.DenseMatrix T (alloc.vec.Vec T))
    {k : ℕ} (hk : k < UScalarTy.Usize.numBits)
    (hm : (vecList m.values).length / m.width.val = 2 ^ k) :
    hax_roots.bitrev_view cl m ⦃ v => v.inner = m ∧ v.index_map.log_height.val = k ⦄ := by
  unfold hax_roots.bitrev_view bitrev.BitReversalPerm.new_view
  obtain ⟨H, hH, hHv⟩ := spec_imp_exists (height_eq cl m)
  have : (DI cl).height m = ok H := hH
  rw [this, bind_ok]
  obtain ⟨K, hK, hKv⟩ := spec_imp_exists (log2_strict_usize_two_pow hk H (hHv.trans hm))
  rw [hK, bind_ok]
  simp [hKv]

/-- The bit-reversed view panics unless the height is a power of two, 0 included. -/
theorem bitrev_view_panics (cl : core.clone.Clone T) (m : dense.DenseMatrix T (alloc.vec.Vec T))
    (hm : ∀ k, (vecList m.values).length / m.width.val ≠ 2 ^ k) :
    hax_roots.bitrev_view cl m = fail .panic := by
  unfold hax_roots.bitrev_view bitrev.BitReversalPerm.new_view
  obtain ⟨H, hH, hHv⟩ := spec_imp_exists (height_eq cl m)
  have : (DI cl).height m = ok H := hH
  rw [this, bind_ok, log2_strict_usize_panics H (fun k h => hm k (hHv ▸ h))]
  simp

/-! ## Strided rows -/

theorem ceil_div_eq (n s : ℕ) (hs : 0 < s) :
    (n + s - 1) / s = n / s + (if n % s > 0 then 1 else 0) := by
  have h := Nat.div_add_mod n s
  have hr := Nat.mod_lt n hs
  have hP : (n / s) * s = s * (n / s) := Nat.mul_comm _ _
  split_ifs with h0
  · apply Nat.div_eq_of_lt_le
    · rw [Nat.add_mul, one_mul]; omega
    · rw [Nat.add_mul, Nat.add_mul, one_mul]; omega
  · apply Nat.div_eq_of_lt_le
    · rw [Nat.add_zero]; omega
    · rw [Nat.add_zero, Nat.add_mul, one_mul]; omega

theorem div_ceil_eq (n s : Std.Usize) (hs : 0 < s.val) :
    core.num.Usize.div_ceil n s ⦃ d => d.val = (n.val + s.val - 1) / s.val ⦄ := by
  unfold core.num.Usize.div_ceil
  have hmax := n.hBounds
  step*
  · have hr : 0 < r.val := by scalar_tac
    have hs2 : 2 ≤ s.val := by
      by_contra h
      have : s.val = 1 := by omega
      rw [r_post, this, Nat.mod_one] at hr; omega
    have : n.val / s.val ≤ n.val / 2 := Nat.div_le_div_left hs2 (by norm_num)
    simp only [Usize.max] at *; scalar_tac
  · have hr : 0 < n.val % s.val := by scalar_tac
    rw [ceil_div_eq _ _ hs]; simp only [hr, ite_true]; scalar_tac
  · have hr : n.val % s.val = 0 := by scalar_tac
    rw [ceil_div_eq _ _ hs]; simp only [hr]; simp; scalar_tac

theorem SI_get_unchecked (cl : core.clone.Clone T) :
    (SI cl).get_unchecked = row_index_mapped.RowIndexMappedView.Insts.P3_matrixMatrix.get_unchecked cl
      strided.VerticallyStridedRowIndexMap.Insts.P3_matrixRow_index_mappedRowIndexMap (DI cl) := rfl

/-- A strided view with stride s > 0 and offset o records ceil((h - o) / s) rows. -/
theorem strided_view_eq (cl : core.clone.Clone T) (m : dense.DenseMatrix T (alloc.vec.Vec T))
    (stride offset : Std.Usize) (hs : 0 < stride.val) :
    hax_roots.strided_view cl m stride offset ⦃ v => v.inner = m ∧
      v.index_map.stride = stride ∧ v.index_map.offset = offset ∧
      v.index_map.height.val =
        stridedHeight ((vecList m.values).length / m.width.val) stride.val offset.val ⦄ := by
  unfold hax_roots.strided_view Matrix.vertically_strided.default
    strided.VerticallyStridedRowIndexMap.new_view
  obtain ⟨H, hH, hHv⟩ := spec_imp_exists (height_eq cl m)
  have : (DI cl).height m = ok H := hH
  rw [this, bind_ok]
  simp only [core.num.Usize.saturating_sub_exposed, bind_ok]
  obtain ⟨d, hd, hdv⟩ := spec_imp_exists (div_ceil_eq ⟨BitVec.ofNat _ (H.val - offset.val)⟩ stride hs)
  rw [hd, bind_ok]
  simp only [WP.spec_ok, true_and]
  rw [hdv, stridedHeight, ← hHv]
  congr 3
  show (BitVec.ofNat _ (H.val - offset.val)).toNat = _
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
  have := H.hBounds; omega

/-- A strided view with stride 0 panics, since its height divides by the stride. -/
theorem strided_view_panics (cl : core.clone.Clone T) (m : dense.DenseMatrix T (alloc.vec.Vec T))
    (offset : Std.Usize) : hax_roots.strided_view cl m 0#usize offset = fail .panic := by
  unfold hax_roots.strided_view Matrix.vertically_strided.default
    strided.VerticallyStridedRowIndexMap.new_view
  obtain ⟨H, hH, hHv⟩ := spec_imp_exists (height_eq cl m)
  have : (DI cl).height m = ok H := hH
  rw [this, bind_ok]
  simp [core.num.Usize.saturating_sub_exposed, core.num.Usize.div_ceil, HDiv.hDiv, UScalar.div]

/-- A strided view with that height reads rows o, o + s, o + 2 s, and so on. -/
theorem strided_get_eq (cl : core.clone.Clone T) (hcl : LawfulClone cl)
    (v : row_index_mapped.RowIndexMappedView strided.VerticallyStridedRowIndexMap
      (dense.DenseMatrix T (alloc.vec.Vec T)))
    (hv : v.index_map.height.val = stridedHeight ((vecList v.inner.values).length / v.inner.width.val)
      v.index_map.stride.val v.index_map.offset.val)
    (r c : Std.Usize) :
    Matrix.get.default (SI cl) v r c ⦃ o => o = get? (castRows (stridedRows (dense v.inner)
      v.index_map.stride.val v.index_map.offset.val) hv.symm) r.val c.val ⦄ := by
  refine get_default_spec (SI cl) v _ v.index_map.height v.inner.width rfl rfl rfl rfl ?_ r c
  intro r c hr hc
  rw [SI_get_unchecked]
  unfold row_index_mapped.RowIndexMappedView.Insts.P3_matrixMatrix.get_unchecked
  simp only [strided.VerticallyStridedRowIndexMap.Insts.P3_matrixRow_index_mappedRowIndexMap.map_row_index]
  have hlt : v.index_map.offset.val + r.val * v.index_map.stride.val <
      (vecList v.inner.values).length / v.inner.width.val := by
    have hr' : r.val < stridedHeight _ _ _ := hv ▸ hr
    unfold stridedHeight at hr'
    have hs : 0 < v.index_map.stride.val := by
      rcases Nat.eq_zero_or_pos v.index_map.stride.val with h0 | h0
      · simp [h0] at hr'
      · exact h0
    have h1 := (Nat.le_div_iff_mul_le hs).mp (Nat.succ_le_of_lt hr')
    rw [Nat.succ_mul] at h1
    omega
  have hlen : (vecList v.inner.values).length ≤ Usize.max := (vs v.inner.values).property
  have hdiv : (vecList v.inner.values).length / v.inner.width.val ≤ (vecList v.inner.values).length :=
    Nat.div_le_self _ _
  step*
  have hidx : i.val * v.inner.width.val + c.val < (vecList v.inner.values).length := by
    have hw : 0 < v.inner.width.val := by omega
    have h1 : i.val < (vecList v.inner.values).length / v.inner.width.val := by scalar_tac
    have := (Nat.le_div_iff_mul_le hw).mp (Nat.succ_le_of_lt h1); nlinarith
  refine WP.spec_mono (get_unchecked_eq cl hcl v.inner i c hidx) ?_
  intro x hx
  simp only [hx, castRows, stridedRows, dense, rowMajor, Matrix.of_apply, Fin.cast_mk]
  congr 2; rw [i_post, x_post]; ring

/-! ## A column range -/

theorem TI_get_unchecked (cl : core.clone.Clone T) :
    (TI cl).get_unchecked =
      horizontally_truncated.HorizontallyTruncated.Insts.P3_matrixMatrix.get_unchecked cl (DI cl) :=
  rfl

theorem truncated_width_eq (cl : core.clone.Clone T)
    (v : horizontally_truncated.HorizontallyTruncated T (dense.DenseMatrix T (alloc.vec.Vec T))) :
    (TI cl).width v ⦃ w => w.val = v.column_range.end.val - v.column_range.start.val ⦄ := by
  show horizontally_truncated.HorizontallyTruncated.Insts.P3_matrixMatrix.width cl (DI cl) v ⦃ _ ⦄
  unfold horizontally_truncated.HorizontallyTruncated.Insts.P3_matrixMatrix.width
  simp only [core.iter.traits.exact_size.ExactSizeIterator.len.default,
    core.ops.range.RangeUsize.Insts.CoreIterTraitsExact_sizeExactSizeIteratorUsize, WP.spec_ok]
  show (BitVec.ofNat _ (v.column_range.end.val - v.column_range.start.val)).toNat = _
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
  have := v.column_range.end.hBounds; omega

/-- A column range s..e with e <= w reads columns s to e - 1. -/
theorem truncated_get_eq (cl : core.clone.Clone T) (hcl : LawfulClone cl)
    (v : horizontally_truncated.HorizontallyTruncated T (dense.DenseMatrix T (alloc.vec.Vec T)))
    (he : v.column_range.end.val ≤ v.inner.width.val) (r c : Std.Usize) :
    Matrix.get.default (TI cl) v r c ⦃ o => o = get? (colRange (dense v.inner)
      v.column_range.start.val v.column_range.end.val he) r.val c.val ⦄ := by
  obtain ⟨W, hW, hWv⟩ := spec_imp_exists (truncated_width_eq cl v)
  obtain ⟨H, hH, hHv⟩ := spec_imp_exists (height_eq cl v.inner)
  refine get_default_spec (TI cl) v _ H W hH hHv hW hWv ?_ r c
  intro r c hr hc
  rw [TI_get_unchecked]
  unfold horizontally_truncated.HorizontallyTruncated.Insts.P3_matrixMatrix.get_unchecked
  have := v.inner.width.hBounds
  step as ⟨i, i_post⟩
  · scalar_tac
  have hidx : r.val * v.inner.width.val + i.val < (vecList v.inner.values).length := by
    have hw : 0 < v.inner.width.val := by omega
    have hi : i.val < v.inner.width.val := by omega
    have := (Nat.le_div_iff_mul_le hw).mp (Nat.succ_le_of_lt hr); nlinarith
  refine WP.spec_mono (get_unchecked_eq cl hcl v.inner r i hidx) ?_
  intro x hx
  simp only [hx, colRange, dense, rowMajor, Matrix.of_apply]
  congr 2

/-! ## Stacking -/

section stack
variable {U : Type _}

theorem vstack_apply_lt {h₁ h₂ w : ℕ} (A : Mat h₁ w U) (B : Mat h₂ w U) (r : Fin (h₁ + h₂))
    (c : Fin w) (hr : r.val < h₁) : vstack A B r c = A ⟨r.val, hr⟩ c := by
  obtain ⟨r, hr'⟩ := r
  simp [vstack, Matrix.fromRows, finSumFinEquiv, Fin.addCases, hr]; rfl

theorem vstack_apply_ge {h₁ h₂ w : ℕ} (A : Mat h₁ w U) (B : Mat h₂ w U) (r : Fin (h₁ + h₂))
    (c : Fin w) (hr : h₁ ≤ r.val) : vstack A B r c = B ⟨r.val - h₁, by omega⟩ c := by
  obtain ⟨r, hr'⟩ := r
  simp [vstack, Matrix.fromRows, finSumFinEquiv, Fin.addCases, show ¬ r < h₁ by simpa using hr]
  rfl

theorem hstack_apply_lt {h w₁ w₂ : ℕ} (A : Mat h w₁ U) (B : Mat h w₂ U) (r : Fin h)
    (c : Fin (w₁ + w₂)) (hc : c.val < w₁) : hstack A B r c = A r ⟨c.val, hc⟩ := by
  obtain ⟨c, hc'⟩ := c
  simp [hstack, Matrix.fromCols, finSumFinEquiv, Fin.addCases, hc]

theorem hstack_apply_ge {h w₁ w₂ : ℕ} (A : Mat h w₁ U) (B : Mat h w₂ U) (r : Fin h)
    (c : Fin (w₁ + w₂)) (hc : w₁ ≤ c.val) : hstack A B r c = B r ⟨c.val - w₁, by omega⟩ := by
  obtain ⟨c, hc'⟩ := c
  simp [hstack, Matrix.fromCols, finSumFinEquiv, Fin.addCases, show ¬ c < w₁ by simpa using hc]

end stack

theorem vpair_height_eq (cl : core.clone.Clone T)
    (v : stack.VerticalPair (dense.DenseMatrix T (alloc.vec.Vec T))
      (dense.DenseMatrix T (alloc.vec.Vec T)))
    (hsum : (vecList v.top.values).length / v.top.width.val +
      (vecList v.bottom.values).length / v.bottom.width.val ≤ Usize.max) :
    (VI cl).height v ⦃ h => h.val = (vecList v.top.values).length / v.top.width.val +
      (vecList v.bottom.values).length / v.bottom.width.val ⦄ := by
  show stack.VerticalPair.Insts.P3_matrixMatrix.height cl (DI cl) (DI cl) v ⦃ _ ⦄
  unfold stack.VerticalPair.Insts.P3_matrixMatrix.height
  obtain ⟨H1, h1, h1v⟩ := spec_imp_exists (height_eq cl v.top)
  obtain ⟨H2, h2, h2v⟩ := spec_imp_exists (height_eq cl v.bottom)
  have e1 : (DI cl).height v.top = ok H1 := h1
  have e2 : (DI cl).height v.bottom = ok H2 := h2
  rw [e1, bind_ok, e2, bind_ok]
  step*

/-- A vertical pair whose heights sum past the word size never returns a height in the model. -/
theorem vpair_height_overflow (cl : core.clone.Clone T)
    (v : stack.VerticalPair (dense.DenseMatrix T (alloc.vec.Vec T))
      (dense.DenseMatrix T (alloc.vec.Vec T)))
    (hsum : Usize.max < (vecList v.top.values).length / v.top.width.val +
      (vecList v.bottom.values).length / v.bottom.width.val) :
    ∀ x, (VI cl).height v ≠ ok x := by
  intro x hx
  change stack.VerticalPair.Insts.P3_matrixMatrix.height cl (DI cl) (DI cl) v = _ at hx
  unfold stack.VerticalPair.Insts.P3_matrixMatrix.height at hx
  obtain ⟨H1, h1, h1v⟩ := spec_imp_exists (height_eq cl v.top)
  obtain ⟨H2, h2, h2v⟩ := spec_imp_exists (height_eq cl v.bottom)
  have e1 : (DI cl).height v.top = ok H1 := h1
  have e2 : (DI cl).height v.bottom = ok H2 := h2
  rw [e1, bind_ok, e2, bind_ok] at hx
  have := UScalar.add_equiv H1 H2
  rw [hx] at this
  simp at this
  have hmax : Usize.max = 2 ^ System.Platform.numBits - 1 := by
    simp [Usize.max, Usize.numBits]
  omega

theorem VI_get_unchecked (cl : core.clone.Clone T) :
    (VI cl).get_unchecked = stack.VerticalPair.Insts.P3_matrixMatrix.get_unchecked cl (DI cl) (DI cl) :=
  rfl

theorem HI_get_unchecked (cl : core.clone.Clone T) :
    (HI cl).get_unchecked =
      stack.HorizontalPair.Insts.P3_matrixMatrix.get_unchecked cl (DI cl) (DI cl) := rfl

/-- A vertical pair of equal widths is the top matrix above the bottom one. -/
theorem vpair_get_eq (cl : core.clone.Clone T) (hcl : LawfulClone cl)
    (v : stack.VerticalPair (dense.DenseMatrix T (alloc.vec.Vec T))
      (dense.DenseMatrix T (alloc.vec.Vec T)))
    (hw : v.bottom.width.val = v.top.width.val)
    (hsum : (vecList v.top.values).length / v.top.width.val +
      (vecList v.bottom.values).length / v.bottom.width.val ≤ Usize.max) (r c : Std.Usize) :
    Matrix.get.default (VI cl) v r c ⦃ o =>
      o = get? (vstack (dense v.top) (castCols (dense v.bottom) hw)) r.val c.val ⦄ := by
  obtain ⟨H, hH, hHv⟩ := spec_imp_exists (vpair_height_eq cl v hsum)
  refine get_default_spec (VI cl) v _ H v.top.width hH hHv rfl rfl ?_ r c
  intro r c hr hc
  rw [VI_get_unchecked]
  unfold stack.VerticalPair.Insts.P3_matrixMatrix.get_unchecked
  obtain ⟨H1, h1, h1v⟩ := spec_imp_exists (height_eq cl v.top)
  have e1 : (DI cl).height v.top = ok H1 := h1
  rw [e1, bind_ok]
  by_cases hr1 : r < H1
  · simp only [hr1, ite_true]
    have hr1' : r.val < (vecList v.top.values).length / v.top.width.val := by scalar_tac
    have hidx : r.val * v.top.width.val + c.val < (vecList v.top.values).length := by
      have hw0 : 0 < v.top.width.val := by omega
      have := (Nat.le_div_iff_mul_le hw0).mp (Nat.succ_le_of_lt hr1'); nlinarith
    refine WP.spec_mono (get_unchecked_eq cl hcl v.top r c hidx) ?_
    intro x hx
    rw [vstack_apply_lt _ _ _ _ hr1']
    simp [hx, dense, rowMajor]
  · simp only [hr1, ite_false]
    have hr1' : (vecList v.top.values).length / v.top.width.val ≤ r.val := by scalar_tac
    step as ⟨i, i_post⟩
    have hi : i.val < (vecList v.bottom.values).length / v.bottom.width.val := by omega
    have hidx : i.val * v.bottom.width.val + c.val < (vecList v.bottom.values).length := by
      have hw0 : 0 < v.bottom.width.val := by omega
      have := (Nat.le_div_iff_mul_le hw0).mp (Nat.succ_le_of_lt hi); nlinarith
    refine WP.spec_mono (get_unchecked_eq cl hcl v.bottom i c hidx) ?_
    intro x hx
    rw [vstack_apply_ge _ _ _ _ hr1']
    simp [hx, dense, rowMajor, castCols, i_post, h1v]

theorem hpair_width_eq (cl : core.clone.Clone T)
    (v : stack.HorizontalPair (dense.DenseMatrix T (alloc.vec.Vec T))
      (dense.DenseMatrix T (alloc.vec.Vec T)))
    (hsum : v.left.width.val + v.right.width.val ≤ Usize.max) :
    (HI cl).width v ⦃ w => w.val = v.left.width.val + v.right.width.val ⦄ := by
  show stack.HorizontalPair.Insts.P3_matrixMatrix.width cl (DI cl) (DI cl) v ⦃ _ ⦄
  unfold stack.HorizontalPair.Insts.P3_matrixMatrix.width
  have e1 : (DI cl).width v.left = ok v.left.width := rfl
  have e2 : (DI cl).width v.right = ok v.right.width := rfl
  rw [e1, bind_ok, e2, bind_ok]
  step*

/-- A horizontal pair of equal heights is the left matrix beside the right one. -/
theorem hpair_get_eq (cl : core.clone.Clone T) (hcl : LawfulClone cl)
    (v : stack.HorizontalPair (dense.DenseMatrix T (alloc.vec.Vec T))
      (dense.DenseMatrix T (alloc.vec.Vec T)))
    (hh : (vecList v.right.values).length / v.right.width.val =
      (vecList v.left.values).length / v.left.width.val)
    (hsum : v.left.width.val + v.right.width.val ≤ Usize.max) (r c : Std.Usize) :
    Matrix.get.default (HI cl) v r c ⦃ o =>
      o = get? (hstack (dense v.left) (castRows (dense v.right) hh)) r.val c.val ⦄ := by
  obtain ⟨W, hW, hWv⟩ := spec_imp_exists (hpair_width_eq cl v hsum)
  obtain ⟨H, hH, hHv⟩ := spec_imp_exists (height_eq cl v.left)
  refine get_default_spec (HI cl) v _ H W hH hHv hW hWv ?_ r c
  intro r c hr hc
  rw [HI_get_unchecked]
  unfold stack.HorizontalPair.Insts.P3_matrixMatrix.get_unchecked
  have e1 : (DI cl).width v.left = ok v.left.width := rfl
  rw [e1, bind_ok]
  by_cases hc1 : c < v.left.width
  · simp only [hc1, ite_true]
    have hc1' : c.val < v.left.width.val := by scalar_tac
    have hidx : r.val * v.left.width.val + c.val < (vecList v.left.values).length := by
      have := (Nat.le_div_iff_mul_le (by omega)).mp (Nat.succ_le_of_lt hr); nlinarith
    refine WP.spec_mono (get_unchecked_eq cl hcl v.left r c hidx) ?_
    intro x hx
    rw [hstack_apply_lt _ _ _ _ hc1']
    simp [hx, dense, rowMajor]
  · simp only [hc1, ite_false]
    have hc1' : v.left.width.val ≤ c.val := by scalar_tac
    step as ⟨i, i_post⟩
    have hr' : r.val < (vecList v.right.values).length / v.right.width.val := by omega
    have hidx : r.val * v.right.width.val + i.val < (vecList v.right.values).length := by
      have hi : i.val < v.right.width.val := by omega
      have := (Nat.le_div_iff_mul_le (by omega)).mp (Nat.succ_le_of_lt hr'); nlinarith
    refine WP.spec_mono (get_unchecked_eq cl hcl v.right r i hidx) ?_
    intro x hx
    rw [hstack_apply_ge _ _ _ _ hc1']
    simp [hx, dense, rowMajor, castRows, i_post]

/-! ## Constructors -/

/-- A column range s..e is accepted exactly when s <= e <= w. -/
theorem truncated_new_with_range_eq (cl : core.clone.Clone T)
    (m : dense.DenseMatrix T (alloc.vec.Vec T)) (rg : core.ops.range.Range Std.Usize) :
    horizontally_truncated.HorizontallyTruncated.new_with_range (DI cl) cl m rg ⦃ o =>
      o = if rg.start.val ≤ rg.end.val ∧ rg.end.val ≤ m.width.val then
        core.option.Option.Some { inner := m, column_range := rg, _phantom := () }
      else core.option.Option.None ⦄ := by
  unfold horizontally_truncated.HorizontallyTruncated.new_with_range
  have e : dense.DenseMatrix.Insts.P3_matrixMatrix.width cl (VS cl) m = ok m.width := rfl
  by_cases h1 : rg.start ≤ rg.end
  · have h1' : rg.start.val ≤ rg.end.val := by scalar_tac
    simp only [h1, ite_true, core.bool.Bool.then,
      horizontally_truncated.HorizontallyTruncated.new_with_range.closure.Insts.CoreOpsFunctionFnOnceTupleHorizontallyTruncated.call_once]
    by_cases h2 : rg.end ≤ m.width
    · have h2' : rg.end.val ≤ m.width.val := by scalar_tac
      simp [e, h1', h2']
    · have h2' : ¬ rg.end.val ≤ m.width.val := by scalar_tac
      simp [e, h2']
  · have h1' : ¬ rg.start.val ≤ rg.end.val := by scalar_tac
    simp [h1, h1', core.bool.Bool.then]

/-- Stacking vertically panics exactly when the widths differ. -/
theorem vpair_new_eq (cl : core.clone.Clone T) (top bottom : dense.DenseMatrix T (alloc.vec.Vec T)) :
    stack.VerticalPair.new cl (DI cl) (DI cl) top bottom =
      if top.width = bottom.width then ok { top, bottom } else fail .panic := by
  unfold stack.VerticalPair.new
  have e1 : (DI cl).width top = ok top.width := rfl
  have e2 : (DI cl).width bottom = ok bottom.width := rfl
  rw [e1, bind_ok, e2, bind_ok]
  by_cases h : top.width = bottom.width <;> simp [h, massert]

/-- Placing side by side panics exactly when the heights differ. -/
theorem hpair_new_eq (cl : core.clone.Clone T) (left right : dense.DenseMatrix T (alloc.vec.Vec T)) :
    stack.HorizontalPair.new cl (DI cl) (DI cl) left right =
      if (vecList left.values).length / left.width.val =
        (vecList right.values).length / right.width.val then ok { left, right }
      else fail .panic := by
  unfold stack.HorizontalPair.new
  obtain ⟨H1, h1, h1v⟩ := spec_imp_exists (height_eq cl left)
  obtain ⟨H2, h2, h2v⟩ := spec_imp_exists (height_eq cl right)
  have e1 : (DI cl).height left = ok H1 := h1
  have e2 : (DI cl).height right = ok H2 := h2
  rw [e1, bind_ok, e2, bind_ok]
  have : (H1 = H2) ↔ ((vecList left.values).length / left.width.val =
      (vecList right.values).length / right.width.val) := by
    rw [← h1v, ← h2v]; exact ⟨fun h => h ▸ rfl, fun h => UScalar.eq_of_val_eq h⟩
  by_cases h : H1 = H2 <;> simp [h, massert, this.mp, mt this.mpr]

end Plonky3Lean.Proofs.Matrix
