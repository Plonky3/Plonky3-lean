module

public import Plonky3Lean.Proofs.Symmetric.Sponge

@[expose] public section

/-!
# The compression functions
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open Plonky3Lean.Spec.Sponge

namespace Plonky3Lean.Proofs.Symmetric

theorem usize_mul_ok (x y : Std.Usize) (h : x.val * y.val ≤ Usize.max) :
    ∃ z, x * y = RustM.ok z ∧ z.val = x.val * y.val := by
  have : x * y ⦃ z => z.val = x.val * y.val ⦄ := by step*
  exact Lib.spec_imp_exists this

/-- `&mut a[lo..hi]` of an array: the subslice, and a write-back that splices a slice of the same length in. -/
theorem array_index_mut_range {T : Type} {W : Std.Usize} (pre : Std.Array T W) (lo hi : Std.Usize)
    (h1 : lo.val ≤ hi.val) (h2 : hi.val ≤ W.val) :
    ∃ (s : Slice T) (back : Slice T → Std.Array T W),
      core.Array.Insts.CoreOpsIndexIndexMut.index_mut
        (core.Slice.Insts.CoreOpsIndexIndexMut
          (core.ops.range.RangeUsize.Insts.CoreSliceIndexSliceIndexSliceSlice T))
        pre { start := lo, «end» := hi } = .ok (s, back) ∧
      s.val.length = hi.val - lo.val ∧
      ∀ s' : Slice T, s'.val.length = hi.val - lo.val →
        (back s').val = pre.val.take lo.val ++ s'.val ++ pre.val.drop hi.val := by
  have hW : pre.val.length = W.val := by simp
  have hsub : (Std.Array.to_slice pre).subslice { start := lo, «end» := hi } =
      .ok (Slice.from (pre.val.slice lo.val hi.val) (by
        have := pre.val.slice_length_le lo.val hi.val; have := pre.property; scalar_tac)) := by
    unfold Slice.subslice
    split_ifs with h
    · simp [Std.Array.to_slice]
    · exfalso; apply h; simp [Std.Array.to_slice]; omega
  simp only [core.Array.Insts.CoreOpsIndexIndexMut.index_mut, core.array.Array.as_mut_slice,
    rust_primitives.slice.array_as_mut_slice, core.Slice.Insts.CoreOpsIndexIndexMut.index_mut,
    core.ops.range.RangeUsize.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked_mut,
    rust_primitives.slice.slice_slice_mut, Std.Array.to_slice_mut]
  simp [hsub]
  refine ⟨by simp [List.slice]; omega, ?_⟩
  intro s' hs'
  simp only [List.setSlice!, hs', Nat.min_eq_left (show hi.val - lo.val ≤ pre.val.length - lo.val by
    omega), List.append_assoc]
  rw [List.take_of_length_le (l := s'.val) (by omega), show lo.val + (hi.val - lo.val) = hi.val by omega]

/-- `copy_from_slice` of a slice of the same length returns the source, for a type whose clone is the value itself. -/
theorem copy_from_slice_eq {T : Type} (copyInst : core.marker.Copy T)
    (hcl : ∀ x, copyInst.cloneCloneInst.clone x = .ok x) (dst src : Slice T)
    (h : dst.val.length = src.val.length) :
    core.slice.Slice.copy_from_slice copyInst dst src = .ok src := by
  have hm : src.val.mapM copyInst.cloneCloneInst.clone = .ok src.val := Lib.mapM_ok _ hcl _
  unfold core.slice.Slice.copy_from_slice rust_primitives.slice.slice_clone_from_slice
  rw [ite_eq_left_of_eq_true _ _ (eq_true (show dst.length = src.length from h))]
  split
  · rename_i cloned hc
    rw [RustM.match.isOk, hm] at hc
    have : cloned = src.val := RustM.ok_injective hc.symm
    subst this
    congr 1
    exact Slice.ext _ _ (Slice.from_val _ _)
  · rename_i e _ hc
    rw [hm, RustM.match.ok] at hc
    cases hc
  · rename_i hc
    rw [hm, RustM.match.ok] at hc
    cases hc

/-- The items of a list of arrays, in order. -/
def flatArrays {T : Type} {C : Std.Usize} (l : List (Std.Array T C)) : List T :=
  (l.map fun a => a.val).flatten

theorem flatArrays_length {T : Type} {C : Std.Usize} :
    ∀ l : List (Std.Array T C), (flatArrays l).length = l.length * C.val := by
  intro l
  induction l with
  | nil => simp [flatArrays]
  | cons a l ih =>
    simp only [flatArrays, List.map_cons, List.flatten_cons, List.length_append] at ih ⊢
    rw [ih]
    simp only [List.length_cons, Nat.succ_mul]
    have : a.val.length = C.val := by simp
    omega

/-- The state after writing the first `k` chunks into the zero state. -/
def truncPre {T : Type} {N CHUNK W : Std.Usize} (z : T) (input : Std.Array (Std.Array T CHUNK) N)
    (k : ℕ) (hk : k ≤ N.val) (hw : N.val * CHUNK.val ≤ W.val) : Std.Array T W :=
  Std.Array.from (flatArrays (input.val.take k) ++ (List.replicate W.val z).drop (k * CHUNK.val))
    (by
      have h1 := flatArrays_length (input.val.take k)
      have h2 : (input.val.take k).length = k := by simp; omega
      have h3 : k * CHUNK.val ≤ N.val * CHUNK.val := Nat.mul_le_mul_right _ hk
      simp only [List.length_append, List.length_drop, List.length_replicate, h1, h2]
      omega)

theorem truncPre_congr {T : Type} {N CHUNK W : Std.Usize} (z : T)
    (input : Std.Array (Std.Array T CHUNK) N) (hw : N.val * CHUNK.val ≤ W.val) (k k' : ℕ)
    (hk : k ≤ N.val) (hk' : k' ≤ N.val) (h : k = k') :
    truncPre z input k hk hw = truncPre z input k' hk' hw := by
  subst h; rfl

theorem trunc_loop {T : Type} {N CHUNK W : Std.Usize} (copyInst : core.marker.Copy T)
    (hcl : ∀ x, copyInst.cloneCloneInst.clone x = .ok x) (z : T)
    (input : Std.Array (Std.Array T CHUNK) N) (hw : N.val * CHUNK.val ≤ W.val) :
    p3_symmetric.compression.TruncatedPermutation.Insts.P3_symmetricCompressionPseudoCompressionFunctionArrayN.compress_loop
      copyInst { start := 0#usize, «end» := N } input
      (Std.Array.from (List.replicate W.val z) (by simp)) =
      .ok (truncPre z input N.val le_rfl hw) := by
  unfold p3_symmetric.compression.TruncatedPermutation.Insts.P3_symmetricCompressionPseudoCompressionFunctionArrayN.compress_loop
  let st : ℕ → core.ops.range.Range Std.Usize × Std.Array T W := fun k =>
    ({ start := Lib.usz k, «end» := N }, truncPre z input (min k N.val) (Nat.min_le_right _ _) hw)
  have h0 : st 0 = ({ start := 0#usize, «end» := N },
      Std.Array.from (List.replicate W.val z) (by simp)) := by
    simp only [st, Prod.mk.injEq]
    refine ⟨rfl, ?_⟩
    apply Std.Array.ext
    simp [truncPre, flatArrays]
  have key := Lib.loop_of_steps (fun x => match x with
    | (iter1, pre1) =>
      p3_symmetric.compression.TruncatedPermutation.Insts.P3_symmetricCompressionPseudoCompressionFunctionArrayN.compress_loop.body
        copyInst input iter1 pre1) st N.val (truncPre z input N.val le_rfl hw) ?_ ?_
  · rw [h0] at key
    exact key
  · intro k hk
    simp only [st]
    rw [truncPre_congr z input hw (min k N.val) k _ hk.le (Nat.min_eq_left hk.le),
      truncPre_congr z input hw (min (k + 1) N.val) (k + 1) _ hk (Nat.min_eq_left hk)]
    have hkv : (Lib.usz k).val = k := Lib.usz_val_le N hk.le
    have hkc : k * CHUNK.val ≤ W.val := le_trans (Nat.mul_le_mul_right _ hk.le) hw
    have hk1c : (k + 1) * CHUNK.val ≤ W.val := le_trans (Nat.mul_le_mul_right _ hk) hw
    obtain ⟨i1, e1, h1⟩ := usize_mul_ok (Lib.usz k) CHUNK (by
      rw [hkv]; have := W.hBounds; scalar_tac)
    obtain ⟨i2, e2, h2⟩ := usize_add_one (Lib.usz k) (by rw [hkv]; have := N.hBounds; scalar_tac)
    obtain ⟨i3, e3, h3⟩ := usize_mul_ok i2 CHUNK (by
      rw [h2, hkv]; have := W.hBounds; scalar_tac)
    simp only [p3_symmetric.compression.TruncatedPermutation.Insts.P3_symmetricCompressionPseudoCompressionFunctionArrayN.compress_loop.body]
    simp only [core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next, Lib.range_step k N hk]
    obtain ⟨sl, back, eb, hsl, hback⟩ := array_index_mut_range (truncPre z input k hk.le hw) i1 i3
      (by rw [h1, h3, h2, hkv]; exact Nat.mul_le_mul_right _ (by omega))
      (by rw [h3, h2, hkv]; exact hk1c)
    have hki : (Lib.usz k).val < input.val.length := by rw [hkv]; simp; omega
    have hlen : sl.val.length = (Std.Array.to_slice (input.val[(Lib.usz k).val])).val.length := by
      rw [hsl, h3, h2, h1]; simp [Std.Array.to_slice, Nat.succ_mul]
    simp [e1, e2, e3, eb, Lib.index_usize_eq _ _ hki, core.array.Array.as_slice,
      rust_primitives.slice.array_as_slice, copy_from_slice_eq copyInst hcl _ _ hlen]
    apply Std.Array.ext
    rw [hback _ (by rw [← hlen, hsl])]
    have hflen := flatArrays_length (input.val.take k)
    have htk : (input.val.take k).length = k := by simp; omega
    rw [htk] at hflen
    have hsucc : flatArrays (input.val.take (k + 1)) =
        flatArrays (input.val.take k) ++ (input.val[k]'(by simp; omega)).val := by
      simp only [flatArrays, List.map_take]
      rw [List.take_add_one, List.getElem?_map, List.getElem?_eq_getElem (by simp; omega)]
      simp
    have hi1 : i1.val = k * CHUNK.val := by rw [h1, hkv]
    have hi3 : i3.val = k * CHUNK.val + CHUNK.val := by rw [h3, h2, hkv, Nat.succ_mul]
    have hget : (input.val[(Lib.usz k).val]'hki) = input.val[k]'(by simp; omega) := by
      simp only [hkv]
    simp only [truncPre, Std.Array.from_val, Std.Array.to_slice, Slice.from_val, hi1, hi3, hsucc,
      hget, Nat.succ_mul]
    rw [List.take_left' hflen, List.drop_append, List.drop_eq_nil_of_le
      (show (flatArrays (input.val.take k)).length ≤ k * CHUNK.val + CHUNK.val by omega),
      List.nil_append,
      List.drop_drop, List.append_assoc, hflen]
    simp only [List.append_assoc, Nat.add_sub_cancel_left]
  · simp only [st]
    rw [truncPre_congr z input hw (min N.val N.val) N.val _ le_rfl (Nat.min_self _),
      show Lib.usz N.val = N from (Lib.eq_usz_le N le_rfl rfl).symm]
    simp [p3_symmetric.compression.TruncatedPermutation.Insts.P3_symmetricCompressionPseudoCompressionFunctionArrayN.compress_loop.body,
      core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next, Lib.range_stop]

/-- The truncated permutation writes the chunks side by side into the zero state, permutes, and keeps the first chunk; it never panics.

The hypotheses are what `TruncatedPermutation::new` checks, plus a permutation that computes `f` and plain-data `T`.
-/
theorem truncated_compress_eq {T P : Type} {N CHUNK W : Std.Usize}
    (copyInst : core.marker.Copy T) (defInst : core.default.Default T)
    (permInst : p3_symmetric.permutation.CryptographicPermutation P (Std.Array T W))
    (c : p3_symmetric.compression.TruncatedPermutation P N CHUNK W)
    (input : Std.Array (Std.Array T CHUNK) N) (f : List T → List T) (z : T)
    (hf : PermComputes permInst c.inner_permutation f) (hz : defInst.default = .ok z)
    (hcl : ∀ x, copyInst.cloneCloneInst.clone x = .ok x)
    (hn : 0 < N.val) (hc : 0 < CHUNK.val) (hw : CHUNK.val * N.val ≤ W.val) :
    ∃ out, p3_symmetric.compression.TruncatedPermutation.Insts.P3_symmetricCompressionPseudoCompressionFunctionArrayN.compress
        copyInst defInst permInst c input = .ok out ∧
      out.val = truncated f z W.val CHUNK.val (input.val.map fun a => a.val) := by
  have : Inhabited T := ⟨z⟩
  have hw' : N.val * CHUNK.val ≤ W.val := by rw [Nat.mul_comm]; exact hw
  have hcw : CHUNK.val ≤ W.val := le_trans (Nat.le_mul_of_pos_right _ hn) hw
  obtain ⟨s2, e2, hs2⟩ := hf.permute (truncPre z input N.val le_rfl hw')
  unfold p3_symmetric.compression.TruncatedPermutation.Insts.P3_symmetricCompressionPseudoCompressionFunctionArrayN.compress
  simp only [hz, bind_ok, Lib.repeat_eq W copyInst.cloneCloneInst z hcl (by omega),
    trunc_loop copyInst hcl z input hw', e2]
  refine ⟨_, squeeze_eq CHUNK copyInst s2 hcw, ?_⟩
  have hlen := flatArrays_length input.val
  have hN : input.val.length = N.val := by simp
  rw [hN] at hlen
  simp only [Std.Array.from_val, hs2, truncPre, List.take_of_length_le (le_of_eq hN), truncated]
  rw [List.drop_replicate]
  have : (input.val.map fun a => a.val).flatten = flatArrays input.val := rfl
  rw [this, hlen]

/-! ## The compression function built from a hasher -/

theorem vec_push_eq {T : Type} (v : alloc.vec.Vec T) (x : T) (h : v.val.length + 1 ≤ Usize.max) :
    ∃ v', alloc.vec.Vec.push v x = .ok v' ∧ v'.val = v.val ++ [x] := by
  have h' : (v.val ++ [x]).length ≤ Usize.max := by simpa using h
  refine ⟨Slice.from (v.val ++ [x]) h', ?_, Slice.from_val _ _⟩
  simp [alloc.vec.Vec.push, rust_primitives.sequence.seq_push, show v.val.length < Usize.max by omega]

theorem cfh_inner_unfold {T : Type} {CHUNK : Std.Usize} (it : core.array.iter.IntoIter T CHUNK)
    (items : alloc.vec.Vec T) :
    p3_symmetric.hax_reshaped.compress_from_hasher_loop0_loop0 it items =
      (do
        let r ← p3_symmetric.hax_reshaped.compress_from_hasher_loop0_loop0.body it items
        match r with
        | ControlFlow.cont (it', items') =>
          p3_symmetric.hax_reshaped.compress_from_hasher_loop0_loop0 it' items'
        | ControlFlow.done x => RustM.ok x) := by
  conv => lhs; rw [p3_symmetric.hax_reshaped.compress_from_hasher_loop0_loop0, loop]
  apply congrArg
  funext r
  rcases r with ⟨it', items'⟩ | x
  · rfl
  · rfl

theorem cfh_outer_unfold {T : Type} {N CHUNK : Std.Usize}
    (it : core.array.iter.IntoIter (Std.Array T CHUNK) N) (items : alloc.vec.Vec T) :
    p3_symmetric.hax_reshaped.compress_from_hasher_loop0 it items =
      (do
        let r ← p3_symmetric.hax_reshaped.compress_from_hasher_loop0.body it items
        match r with
        | ControlFlow.cont (it', items') =>
          p3_symmetric.hax_reshaped.compress_from_hasher_loop0 it' items'
        | ControlFlow.done x => RustM.ok x) := by
  conv => lhs; rw [p3_symmetric.hax_reshaped.compress_from_hasher_loop0, loop]
  apply congrArg
  funext r
  rcases r with ⟨it', items'⟩ | x
  · rfl
  · rfl

theorem cfh_inner_loop {T : Type} {CHUNK : Std.Usize} :
    ∀ (xs : List T) (it : core.array.iter.IntoIter T CHUNK) (items : alloc.vec.Vec T),
      Yields (core.array.iter.IntoIter.Insts.CoreIterTraitsIteratorIterator T CHUNK) it xs →
      items.val.length + xs.length ≤ Usize.max →
      ∃ items', p3_symmetric.hax_reshaped.compress_from_hasher_loop0_loop0 it items = .ok items' ∧
        items'.val = items.val ++ xs := by
  intro xs
  induction xs with
  | nil =>
    intro it items hit _
    obtain ⟨it', e⟩ := hit
    change core.array.iter.IntoIter.Insts.CoreIterTraitsIteratorIterator.next it = _ at e
    refine ⟨items, ?_, by simp⟩
    rw [cfh_inner_unfold]
    simp [p3_symmetric.hax_reshaped.compress_from_hasher_loop0_loop0.body, e]
  | cons x xs ih =>
    intro it items hit hlen
    obtain ⟨it', e, hit'⟩ := hit
    change core.array.iter.IntoIter.Insts.CoreIterTraitsIteratorIterator.next it = _ at e
    obtain ⟨v, ev, hv⟩ := vec_push_eq items x (by simp at hlen; omega)
    obtain ⟨items', e', h'⟩ := ih it' v hit' (by simp [hv] at hlen ⊢; omega)
    refine ⟨items', ?_, by rw [h', hv]; simp⟩
    rw [cfh_inner_unfold]
    simp [p3_symmetric.hax_reshaped.compress_from_hasher_loop0_loop0.body, e, ev, e']

theorem cfh_outer_loop {T : Type} {N CHUNK : Std.Usize} :
    ∀ (xs : List (Std.Array T CHUNK)) (it : core.array.iter.IntoIter (Std.Array T CHUNK) N)
      (items : alloc.vec.Vec T),
      Yields (core.array.iter.IntoIter.Insts.CoreIterTraitsIteratorIterator (Std.Array T CHUNK) N)
        it xs →
      items.val.length + (flatArrays xs).length ≤ Usize.max →
      ∃ items', p3_symmetric.hax_reshaped.compress_from_hasher_loop0 it items = .ok items' ∧
        items'.val = items.val ++ flatArrays xs := by
  intro xs
  induction xs with
  | nil =>
    intro it items hit _
    obtain ⟨it', e⟩ := hit
    change core.array.iter.IntoIter.Insts.CoreIterTraitsIteratorIterator.next it = _ at e
    refine ⟨items, ?_, by simp [flatArrays]⟩
    rw [cfh_outer_unfold]
    simp [p3_symmetric.hax_reshaped.compress_from_hasher_loop0.body, e]
  | cons a xs ih =>
    intro it items hit hlen
    obtain ⟨it', e, hit'⟩ := hit
    change core.array.iter.IntoIter.Insts.CoreIterTraitsIteratorIterator.next it = _ at e
    have hfl : flatArrays (a :: xs) = a.val ++ flatArrays xs := by simp [flatArrays]
    rw [hfl] at hlen
    obtain ⟨ia, eia, hia⟩ := array_into_iter_yields a
    obtain ⟨v, ev, hv⟩ := cfh_inner_loop a.val ia items hia (by simp at hlen ⊢; omega)
    obtain ⟨items', e', h'⟩ := ih it' v hit' (by rw [hv]; simp at hlen ⊢; omega)
    refine ⟨items', ?_, by rw [h', hv, hfl]; simp⟩
    rw [cfh_outer_unfold]
    simp [p3_symmetric.hax_reshaped.compress_from_hasher_loop0.body, e, eia, ev, e']

/-- The compression function built from a hasher hands the hasher the chunks' items in order, then returns its digest.

The hypothesis bounds the number of items by the largest vector length.
-/
theorem compress_from_hasher_eq {T H : Type} {N CHUNK : Std.Usize}
    (cloneInst : core.clone.Clone T)
    (hInst : p3_symmetric.hasher.CryptographicHasher H T (Std.Array T CHUNK))
    (c : p3_symmetric.compression.CompressionFunctionFromHasher H N CHUNK)
    (input : Std.Array (Std.Array T CHUNK) N) (hlen : N.val * CHUNK.val ≤ Usize.max) :
    ∃ items : alloc.vec.Vec T, items.val = flatArrays input.val ∧
      p3_symmetric.compression.CompressionFunctionFromHasher.Insts.P3_symmetricCompressionPseudoCompressionFunctionArrayN.compress
        cloneInst hInst c input =
      hInst.hash_iter (alloc.vec.Vec.Insts.CoreIterTraitsCollectIntoIteratorTIntoIter T) c.hasher
        items := by
  obtain ⟨it, eit, hit⟩ := array_into_iter_yields input
  have hfl := flatArrays_length input.val
  let v0 : alloc.vec.Vec T := Slice.new T
  have ev0 : alloc.vec.Vec.new T = .ok v0 := by
    simp [alloc.vec.Vec.new, rust_primitives.sequence.seq_empty, v0]
  have hnew : v0.val = [] := rfl
  have hN : input.val.length = N.val := by simp
  obtain ⟨items, e, h⟩ := cfh_outer_loop input.val it v0 hit (by
    rw [hfl, hnew, hN]; simpa using hlen)
  refine ⟨items, by rw [h, hnew]; rfl, ?_⟩
  simp only [p3_symmetric.compression.CompressionFunctionFromHasher.Insts.P3_symmetricCompressionPseudoCompressionFunctionArrayN.compress,
    p3_symmetric.hax_reshaped.compress_from_hasher, ev0, eit, bind_ok, e]

end Plonky3Lean.Proofs.Symmetric
