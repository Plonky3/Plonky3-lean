module

public import Plonky3Lean.Lib.Range

@[expose] public section

/-!
# Arrays and slices, as `CoreModels` builds and indexes them

`core::array::from_fn` with a closure that keeps its state is a map over the indices.

Indexing by `start..`, then `..end`, and converting the result to an array, take a sublist.
-/

open Aeneas Aeneas.Std CoreModels

namespace Plonky3Lean.Lib

theorem array_from_fn_go_eq {T F : Type} (inst : CoreModels.core.ops.function.FnMut F Std.Usize T)
    (c : F) (g : ℕ → T) (n : ℕ) (hg : ∀ k < n, inst.call_mut c (usz k) = .ok (g k, c)) :
    CoreModels.rust_primitives.slice.array_from_fn_go inst c n = .ok ((List.range n).map g, c) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [CoreModels.rust_primitives.slice.array_from_fn_go, ih (fun k hk => hg k (by omega)), bind_ok]
    rw [show (⟨BitVec.ofNat _ n⟩ : Std.Usize) = usz n from rfl, hg n (by omega), bind_ok]
    simp [List.range_succ]

theorem array_from_fn_eq {T F : Type} (N : Std.Usize)
    (inst : CoreModels.core.ops.function.FnMut F Std.Usize T) (c : F) (g : ℕ → T)
    (hg : ∀ k < N.val, inst.call_mut c (usz k) = .ok (g k, c)) :
    CoreModels.rust_primitives.slice.array_from_fn N inst c =
      .ok (Std.Array.from ((List.range N.val).map g) (by simp)) := by
  rw [CoreModels.rust_primitives.slice.array_from_fn, array_from_fn_go_eq inst c g _ hg, bind_ok]
  simp

theorem slice_index_eq {α : Type} (s : Slice α) (i : Std.Usize) (h : i.val < s.val.length) :
    Slice.index_usize s i = .ok (s.val[i.val]) := by
  simp only [Slice.index_usize]
  rw [show s[i]? = some (s.val[i.val]) from List.getElem?_eq_getElem h]

/-- A slice of length `N` converts to the array of its elements. -/
theorem try_from_eq {T : Type} [Inhabited T] (N : Std.Usize) (inst : CoreModels.core.marker.Copy T)
    (x : Slice T) (h : x.val.length = N.val) (hN : N.val < 2 ^ 32) :
    CoreModels.core.Array.Insts.CoreConvertTryFromShared0SliceTryFromSliceError.try_from N inst x =
      .ok (.Ok (Std.Array.from x.val h)) := by
  unfold CoreModels.core.Array.Insts.CoreConvertTryFromShared0SliceTryFromSliceError.try_from
  have hlen : Slice.len x = N := UScalar.eq_of_val_eq (by simpa using h)
  simp only [CoreModels.rust_primitives.slice.slice_length, bind_ok, hlen, ite_true]
  rw [array_from_fn_eq N _ x (fun k => x.val[k]!) (fun k hk => by
    simp only [CoreModels.core.convert.TryFromArrayShared0SliceTryFromSliceError.try_from.closure.Insts.CoreOpsFunctionFnMutTupleUsizeT.call_mut,
      CoreModels.rust_primitives.slice.slice_index]
    rw [slice_index_eq _ _ (by rw [usz_val (by omega)]; omega), bind_ok]
    simp [usz_val (show k < 2 ^ 32 by omega), List.getElem!_eq_getElem?_getD,
      List.getElem?_eq_getElem (show k < x.val.length by omega)])]
  rw [bind_ok]
  congr 2
  apply Std.Array.ext
  simp only [Std.Array.from_val]
  apply List.ext_getElem (by simp [h])
  intro i h1 h2
  simp [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem h2]

/-- `&a[start..]` of an array. -/
theorem index_rangeFrom_eq {T : Type} {N : Std.Usize} (a : Std.Array T N) (st : Std.Usize)
    (h : st.val ≤ a.val.length) :
    CoreModels.core.Array.Insts.CoreOpsIndexIndex.index
      (CoreModels.core.Slice.Insts.CoreOpsIndexIndex
        (CoreModels.core.ops.range.RangeFromUsize.Insts.CoreSliceIndexSliceIndexSliceSlice T))
      a { start := st } =
      .ok (Slice.from (a.val.slice st.val a.val.length) (by
        have := a.val.slice_length_le st.val a.val.length; have := a.property; scalar_tac)) := by
  simp only [CoreModels.core.Array.Insts.CoreOpsIndexIndex.index,
    CoreModels.core.array.Array.as_slice, CoreModels.rust_primitives.slice.array_as_slice,
    CoreModels.core.Slice.Insts.CoreOpsIndexIndex.index,
    CoreModels.core.ops.range.RangeFromUsize.Insts.CoreSliceIndexSliceIndexSliceSlice.get,
    CoreModels.rust_primitives.slice.slice_length, CoreModels.rust_primitives.slice.slice_slice,
    bind_ok]
  have hle : st ≤ Slice.len (Std.Array.to_slice a) := by
    rw [UScalar.le_equiv]; simpa [Std.Array.to_slice] using h
  simp only [hle, ite_true]
  have hN : st.val ≤ N.val := by simpa using h
  simp [Slice.subslice, Std.Array.to_slice, hN]

/-- `&s[..end]` of a slice. -/
theorem index_rangeTo_eq {T : Type} (sl : Slice T) (e : Std.Usize) (h : e.val ≤ sl.val.length) :
    CoreModels.core.Slice.Insts.CoreOpsIndexIndex.index
      (CoreModels.core.ops.range.RangeToUsize.Insts.CoreSliceIndexSliceIndexSliceSlice T)
      sl { «end» := e } =
      .ok (Slice.from (sl.val.slice 0 e.val) (by
        have := sl.val.slice_length_le 0 e.val; have := sl.property; scalar_tac)) := by
  simp only [CoreModels.core.Slice.Insts.CoreOpsIndexIndex.index,
    CoreModels.core.ops.range.RangeToUsize.Insts.CoreSliceIndexSliceIndexSliceSlice.get,
    CoreModels.rust_primitives.slice.slice_length, CoreModels.rust_primitives.slice.slice_slice,
    bind_ok]
  have hle : e ≤ Slice.len sl := by
    rw [UScalar.le_equiv]; simpa using h
  simp only [hle, ite_true]
  simp [Slice.subslice, h]

end Plonky3Lean.Lib
