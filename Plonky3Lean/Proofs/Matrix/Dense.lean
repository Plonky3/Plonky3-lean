module

public import Plonky3Lean.Spec.Matrix
public import Plonky3Lean.Lib.Slice

@[expose] public section

/-!
# p3-matrix: the dense matrix

Shape and element access of the dense matrix over vector storage.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM
open Plonky3Lean.Lib Plonky3Lean.Spec.Matrix
open p3_matrix

namespace Plonky3Lean.Proofs.Matrix

variable {T : Type}

/-- A vector's elements, as the slice the model stores. -/
def vs (v : alloc.vec.Vec T) : Slice T := v

@[simp] theorem vs_val (v : alloc.vec.Vec T) : (vs v).val = vecList v := rfl

@[simp] theorem borrow_vec (v : alloc.vec.Vec T) :
    (alloc.vec.Vec.Insts.CoreBorrowBorrowSlice T).borrow v = ok (vs v) := rfl

@[simp] theorem slice_len_eq (s : Slice T) : core.slice.Slice.len s = ok (Slice.len s) := rfl

theorem height_eq (cl : core.clone.Clone T) (m : dense.DenseMatrix T (alloc.vec.Vec T)) :
    dense.DenseMatrix.Insts.P3_matrixMatrix.height cl (VS cl) m ⦃ h =>
      h.val = (vecList m.values).length / m.width.val ⦄ := by
  unfold dense.DenseMatrix.Insts.P3_matrixMatrix.height
  simp only [core.num.Usize.checked_div, borrow_vec, slice_len_eq, bind_ok]
  by_cases hw : m.width = 0#usize
  · simp [hw, core.option.Option.unwrap_or]
  · have hw' : m.width.val ≠ 0 := by intro h; exact hw (by scalar_tac)
    simp only [hw, ite_false]
    step*
    simp_all [core.option.Option.unwrap_or]


theorem get_unchecked_eq (cl : core.clone.Clone T) (hcl : LawfulClone cl)
    (m : dense.DenseMatrix T (alloc.vec.Vec T)) (r c : Std.Usize)
    (h : r.val * m.width.val + c.val < (vecList m.values).length) :
    dense.DenseMatrix.Insts.P3_matrixMatrix.get_unchecked cl (VS cl) m r c ⦃ x =>
      x = (vecList m.values)[r.val * m.width.val + c.val] ⦄ := by
  unfold dense.DenseMatrix.Insts.P3_matrixMatrix.get_unchecked
  simp only [borrow_vec, bind_ok, core.slice.Slice.get_unchecked,
    core.Usize.Insts.CoreSliceIndexSliceIndexSliceT.get_unchecked,
    rust_primitives.slice.slice_index]
  have := (vs m.values).property
  have hlen : (vs m.values).length = (vecList m.values).length := rfl
  step*
  rw [hcl]; simp [*]

/-- The provided safe read, given the height, the width and every in-range unchecked read.

It returns the entry inside the shape and nothing outside. -/
theorem get_default_spec {Self : Type} (MI : Matrix Self T) (x : Self) {h w : ℕ} (M : Mat h w T)
    (H W : Std.Usize) (hH : MI.height x = ok H) (hHv : H.val = h) (hW : MI.width x = ok W)
    (hWv : W.val = w)
    (hu : ∀ r c : Std.Usize, (hr : r.val < h) → (hc : c.val < w) →
      MI.get_unchecked x r c ⦃ y => y = M ⟨r.val, hr⟩ ⟨c.val, hc⟩ ⦄)
    (r c : Std.Usize) :
    Matrix.get.default MI x r c ⦃ o => o = get? M r.val c.val ⦄ := by
  unfold Matrix.get.default
  rw [hH, bind_ok]
  simp only [core.bool.Bool.then, Matrix.get.closure.Insts.CoreOpsFunctionFnOnceTupleT.call_once]
  by_cases hr : r < H
  · have hr' : r.val < h := by scalar_tac
    by_cases hc : c < W
    · have hc' : c.val < w := by scalar_tac
      simp only [hr, ite_true, hW, bind_ok, hc, decide_true]
      obtain ⟨y, hy, hyv⟩ := spec_imp_exists (hu r c hr' hc')
      change (MI.get_unchecked x r c >>= fun x => ok (core.option.Option.Some x)) ⦃ o =>
        o = get? M r.val c.val ⦄
      rw [hy, bind_tc_ok]
      simp [get?, hr', hc', hyv]
    · have : ¬ c.val < w := by scalar_tac
      have hc2 : ¬ c.val < W.val := by omega
      simp [hr, hW, hc2, get?, this]
  · have : ¬ r.val < h := by scalar_tac
    simp [hr, get?, this]

theorem get_eq (cl : core.clone.Clone T) (hcl : LawfulClone cl)
    (m : dense.DenseMatrix T (alloc.vec.Vec T)) (r c : Std.Usize) :
    Matrix.get.default (DI cl) m r c ⦃ o => o = get? (dense m) r.val c.val ⦄ := by
  obtain ⟨hv, hh, hval⟩ := spec_imp_exists (height_eq cl m)
  refine get_default_spec (DI cl) m (dense m) hv m.width hh hval rfl rfl ?_ r c
  intro r c hr hc
  have hidx : r.val * m.width.val + c.val < (vecList m.values).length := by
    have hw : 0 < m.width.val := by omega
    have := (Nat.le_div_iff_mul_le hw).mp (Nat.succ_le_of_lt hr); nlinarith
  exact get_unchecked_eq cl hcl m r c hidx

/-- Out of bounds, the unchecked read fails in the model.

In Rust it reads past the buffer, which is undefined behaviour. -/
theorem get_unchecked_oob (cl : core.clone.Clone T) (m : dense.DenseMatrix T (alloc.vec.Vec T))
    (r c : Std.Usize) (h : (vecList m.values).length ≤ r.val * m.width.val + c.val)
    (hmax : r.val * m.width.val + c.val ≤ UScalar.max .Usize) :
    dense.DenseMatrix.Insts.P3_matrixMatrix.get_unchecked cl (VS cl) m r c = fail .panic := by
  unfold dense.DenseMatrix.Insts.P3_matrixMatrix.get_unchecked
  simp only [borrow_vec, bind_ok, core.slice.Slice.get_unchecked,
    core.Usize.Insts.CoreSliceIndexSliceIndexSliceT.get_unchecked,
    rust_primitives.slice.slice_index]
  obtain ⟨i, hi, hiv⟩ := spec_imp_exists (UScalar.mul_spec (x := r) (y := m.width) (by omega))
  rw [hi, bind_ok]
  obtain ⟨j, hj, hjv, -⟩ := spec_imp_exists (UScalar.add_bv_spec (x := i) (y := c) (by omega))
  rw [hj, bind_ok]
  have : (vs m.values).length ≤ j.val := by
    show (vecList m.values).length ≤ _; omega
  simp [Slice.index_usize, List.getElem?_eq_none (by simpa using this)]

/-- The constructor's debug assertion panics unless the width divides the length.

Width 0 divides only 0. -/
theorem new_eq (cl : core.clone.Clone T) (values : alloc.vec.Vec T) (width : Std.Usize) :
    dense.DenseMatrix.new cl (VS cl) values width =
      if (width.val = 0 ∧ (vecList values).length = 0) ∨
          (width.val ≠ 0 ∧ (vecList values).length % width.val = 0)
      then ok { values, width, _phantom := () } else fail .panic := by
  unfold dense.DenseMatrix.new
  simp only [borrow_vec, slice_len_eq, bind_ok, core.num.Usize.is_multiple_of]
  by_cases hw : width = 0#usize
  · have hw' : width.val = 0 := by scalar_tac
    have : (Slice.len (vs values) = 0#usize) ↔ (vecList values).length = 0 := by
      constructor
      · intro h; have := congrArg UScalar.val h; simpa using this
      · intro h; apply UScalar.eq_of_val_eq; simpa using h
    by_cases hl : (vecList values).length = 0 <;> simp [hw, hl, this, massert]
  · have hw' : width.val ≠ 0 := by intro h; exact hw (by scalar_tac)
    simp only [hw, ite_false]
    obtain ⟨q, hq, hqv⟩ := spec_imp_exists (UScalar.rem_spec (x := Slice.len (vs values)) (y := width)
      (by scalar_tac))
    rw [hq, bind_ok]
    have : (q = 0#usize) ↔ (vecList values).length % width.val = 0 := by
      have hl : (Slice.len (vs values)).val = (vecList values).length := by simp
      constructor
      · intro h; have := congrArg UScalar.val h; rw [hqv, hl] at this; simpa using this
      · intro h; apply UScalar.eq_of_val_eq; rw [hqv, hl]; simpa using h
    by_cases hm : (vecList values).length % width.val = 0 <;> simp [hm, hw', this, massert]

end Plonky3Lean.Proofs.Matrix
