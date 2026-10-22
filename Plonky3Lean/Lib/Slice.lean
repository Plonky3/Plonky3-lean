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

/-- `&s[start..]` of a slice. -/
theorem slice_index_rangeFrom_eq {T : Type} (sl : Slice T) (st : Std.Usize)
    (h : st.val ≤ sl.val.length) :
    CoreModels.core.Slice.Insts.CoreOpsIndexIndex.index
      (CoreModels.core.ops.range.RangeFromUsize.Insts.CoreSliceIndexSliceIndexSliceSlice T)
      sl { start := st } =
      .ok (Slice.from (sl.val.slice st.val sl.val.length) (by
        have := sl.val.slice_length_le st.val sl.val.length; have := sl.property; scalar_tac)) := by
  simp only [CoreModels.core.Slice.Insts.CoreOpsIndexIndex.index,
    CoreModels.core.ops.range.RangeFromUsize.Insts.CoreSliceIndexSliceIndexSliceSlice.get,
    CoreModels.rust_primitives.slice.slice_length, CoreModels.rust_primitives.slice.slice_slice,
    bind_ok]
  have hle : st ≤ Slice.len sl := by
    rw [UScalar.le_equiv]; simpa using h
  simp only [hle, ite_true]
  simp [Slice.subslice, h]

theorem slice_update_eq {α : Type} (s : Slice α) (i : Std.Usize) (x : α) (h : i.val < s.val.length) :
    Slice.update s i x = .ok (Slice.from (s.val.set i.val x) (by have := s.property; simp [*])) := by
  simp only [Slice.update]
  rw [List.getElem?_eq_getElem h]

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

theorem mapM_ok {α : Type} (f : α → RustM α) (hf : ∀ x, f x = .ok x) (l : List α) :
    l.mapM f = .ok l := by
  induction l with
  | nil => rfl
  | cons a l ih => simp only [List.mapM_cons, hf, ih, bind_tc_ok]; rfl

/-- Removing the head of a nonempty sequence. -/
theorem seq_remove_head {T : Type} (s : Slice T) (a : T) (rest : List T) (hs : s.val = a :: rest) :
    ∃ s' : Slice T, CoreModels.rust_primitives.sequence.seq_remove s 0#usize = .ok (a, s') ∧
      s'.val = rest := by
  simp only [CoreModels.rust_primitives.sequence.seq_remove]
  rw [dite_eq_left_of_eq_true (eq_true (by simp [hs]))]
  exact ⟨_, by congr 2; simp [hs], by simp [hs]⟩

/-- The closure of `core::array::repeat` hands out the next clone and keeps the rest. -/
theorem repeat_go_eq {T : Type} {N : Std.Usize} (cl : CoreModels.core.clone.Clone T) (v : T)
    (m : ℕ) (c : CoreModels.core.array.repeat.closure T N)
    (hc : Slice.val (α := T) c = List.replicate m v) :
    ∀ n ≤ m, ∃ c' : CoreModels.core.array.repeat.closure T N,
      CoreModels.rust_primitives.slice.array_from_fn_go
      (CoreModels.core.array.repeat.closure.Insts.CoreOpsFunctionFnMutTupleUsizeT N cl) c n =
      .ok (List.replicate n v, c') ∧ Slice.val (α := T) c' = List.replicate (m - n) v := by
  intro n
  induction n with
  | zero => intro _; exact ⟨c, rfl, by simpa using hc⟩
  | succ n ih =>
    intro hn
    obtain ⟨c', e, hc'⟩ := ih (by omega)
    obtain ⟨c'', e', hc''⟩ := seq_remove_head c' v (List.replicate (m - (n + 1)) v)
      (by rw [hc', show m - n = (m - (n + 1)) + 1 by omega, List.replicate_succ])
    refine ⟨c'', ?_, hc''⟩
    rw [CoreModels.rust_primitives.slice.array_from_fn_go, e, bind_ok]
    simp only [CoreModels.core.array.repeat.closure.Insts.CoreOpsFunctionFnMutTupleUsizeT.call_mut]
    rw [List.replicate_succ', e', bind_ok]
    exact bind_ok _ _

/-- `[v; N]`, for a type whose clone is the value itself. -/
theorem repeat_eq {T : Type} (N : Std.Usize) (cl : CoreModels.core.clone.Clone T) (v : T)
    (hcl : ∀ x, cl.clone x = .ok x) (hN : 0 < N.val) :
    CoreModels.core.array.repeat N cl v = .ok (Std.Array.from (List.replicate N.val v) (by simp)) := by
  unfold CoreModels.core.array.repeat CoreModels.rust_primitives.sequence.seq_create
  erw [ite_eq_right_of_eq_false _ _ (eq_false (by omega))]
  rw [mapM_ok _ hcl]
  have hmax : (List.replicate (N.val - 1) v ++ [v]).length ≤ Usize.max := by
    simp only [List.length_append, List.length_replicate, List.length_singleton]
    scalar_tac
  rw [show (RustM.ok (List.replicate (N.val - 1) v)).match = MatchResult.ok _ from rfl]
  dsimp only
  rw [dite_eq_left_of_eq_true (eq_true hmax)]
  erw [bind_ok]
  obtain ⟨c', e, -⟩ := repeat_go_eq (N := N) cl v N.val (Slice.from _ hmax)
    (by simp only [Slice.from_val]; rw [← List.replicate_succ', show N.val - 1 + 1 = N.val by omega])
    N.val le_rfl
  unfold CoreModels.rust_primitives.slice.array_from_fn
  rw [e, bind_ok, dite_eq_left_of_eq_true (eq_true (by simp))]

/-! ## Indexing and updating arrays -/

theorem index_usize_eq {α : Type} {n : Std.Usize} (v : Std.Array α n) (i : Std.Usize)
    (h : i.val < v.val.length) : Std.Array.index_usize v i = .ok (v.val[i.val]) := by
  simp only [Std.Array.index_usize]
  rw [show v[i]? = some (v.val[i.val]) from List.getElem?_eq_getElem h]

theorem update_eq {α : Type} {n : Std.Usize} (v : Std.Array α n) (i : Std.Usize) (x : α)
    (h : i.val < v.val.length) :
    Std.Array.update v i x = .ok (Std.Array.from (v.val.set i.val x) (by simp)) := by
  simp only [Std.Array.update]
  rw [show v[i]? = some (v.val[i.val]) from List.getElem?_eq_getElem h]

theorem index_make {α : Type} {n : Std.Usize} (l : List α) (h : l.length = n.val) (i : Std.Usize)
    (hi : i.val < l.length) : Std.Array.index_usize (Std.Array.make n l h) i = .ok (l[i.val]) := by
  rw [index_usize_eq _ _ (by simpa using hi)]
  simp

theorem update_make {α : Type} {n : Std.Usize} (l : List α) (h : l.length = n.val) (i : Std.Usize)
    (x : α) (hi : i.val < l.length) :
    Std.Array.update (Std.Array.make n l h) i x =
      .ok (Std.Array.make n (l.set i.val x) (by simpa using h)) := by
  rw [update_eq _ _ _ (by simpa using hi)]
  congr 1
  apply Std.Array.ext
  simp

theorem index_usize_eq' {α : Type} [Inhabited α] {n : Std.Usize} (v : Std.Array α n) (i : Std.Usize)
    (h : i.val < v.val.length) : Std.Array.index_usize v i = .ok (v.val[i.val]!) := by
  rw [index_usize_eq _ _ h]
  exact congrArg _ (getElem!_pos v.val i.val h).symm

theorem update_eq' {α : Type} {n : Std.Usize} (v : Std.Array α n) (i : Std.Usize) (x : α)
    (h : i.val < v.val.length) :
    Std.Array.update v i x = .ok (Std.Array.from (v.val.set i.val x) (by simp)) :=
  update_eq v i x h

end Plonky3Lean.Lib
