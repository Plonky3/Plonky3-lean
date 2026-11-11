module

public import P3Symmetric
public import Plonky3Lean.Proofs.Symmetric.Iter
public import Plonky3Lean.Proofs.Symmetric.Online

@[expose] public section

/-!
# The sponges, against the block-wise specification
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open Plonky3Lean.Spec.Sponge

namespace Plonky3Lean.Proofs.Symmetric

/-- The permutation `p`, through its dictionary, computes `f` and never panics. -/
structure PermComputes {P T : Type} {W : Std.Usize}
    (inst : p3_symmetric.permutation.CryptographicPermutation P (Std.Array T W)) (p : P)
    (f : List T → List T) : Prop where
  permute : ∀ s, ∃ s', inst.PermutationInst.permute p s = .ok s' ∧ s'.val = f s.val
  permute_mut : ∀ s, ∃ s', inst.PermutationInst.permute_mut p s = .ok s' ∧ s'.val = f s.val

theorem PermComputes.length {P T : Type} {W : Std.Usize}
    {inst : p3_symmetric.permutation.CryptographicPermutation P (Std.Array T W)} {p : P}
    {f : List T → List T} (h : PermComputes inst p f) (s : Std.Array T W) :
    (f s.val).length = W.val := by
  obtain ⟨s', _, hs'⟩ := h.permute s
  rw [← hs']
  simp

theorem usize_add_one (i : Std.Usize) (h : i.val + 1 ≤ Usize.max) :
    ∃ j, i + 1#usize = RustM.ok j ∧ j.val = i.val + 1 := by
  have : i + 1#usize ⦃ z => z.val = i.val + (1#usize : Std.Usize).val ⦄ := by step*
  obtain ⟨j, e1, h1⟩ := Lib.spec_imp_exists this
  exact ⟨j, e1, by simpa using h1⟩

theorem pf_loop_unfold {T P I J : Type} {W : Std.Usize} (RATE : Std.Usize)
    (defInst : core.default.Default T)
    (permInst : p3_symmetric.permutation.CryptographicPermutation P (Std.Array T W))
    (iterInst : core.iter.traits.collect.IntoIterator I T J) (p : P) (it : J)
    (state : Std.Array T W) (i : Std.Usize) :
    p3_symmetric.hax_reshaped.padding_free_hash_loop RATE defInst permInst iterInst it p state i =
      (do
        let r ← p3_symmetric.hax_reshaped.padding_free_hash_loop.body RATE defInst permInst iterInst
          p it state i
        match r with
        | ControlFlow.cont (it', state', i') =>
          p3_symmetric.hax_reshaped.padding_free_hash_loop RATE defInst permInst iterInst it' p
            state' i'
        | ControlFlow.done x => RustM.ok x) := by
  conv => lhs; rw [p3_symmetric.hax_reshaped.padding_free_hash_loop, loop]
  apply congrArg
  funext r
  rcases r with ⟨it', state', i'⟩ | x
  · rfl
  · rfl

theorem pf_loop {T P I J : Type} {W : Std.Usize} (RATE : Std.Usize)
    (defInst : core.default.Default T)
    (permInst : p3_symmetric.permutation.CryptographicPermutation P (Std.Array T W))
    (iterInst : core.iter.traits.collect.IntoIterator I T J) (p : P) (f : List T → List T)
    (hf : PermComputes permInst p f) (hrw : RATE.val ≤ W.val) :
    ∀ (xs : List T) (it : J), Yields iterInst.iteratorIteratorInst it xs →
      ∀ (state : Std.Array T W) (i : Std.Usize), i.val < RATE.val →
      ∃ (state' : Std.Array T W) (i' : Std.Usize),
        p3_symmetric.hax_reshaped.padding_free_hash_loop RATE defInst permInst iterInst it p
          state i = .ok (state', i') ∧
        (state'.val, i'.val) = xs.foldl (pfStep f RATE.val) (state.val, i.val) ∧
        i'.val < RATE.val := by
  intro xs
  induction xs with
  | nil =>
    intro it hit state i hi
    obtain ⟨it', e⟩ := hit
    refine ⟨state, i, ?_, rfl, hi⟩
    rw [pf_loop_unfold]
    simp [p3_symmetric.hax_reshaped.padding_free_hash_loop.body, e]
  | cons x xs ih =>
    intro it hit state i hi
    obtain ⟨it', e, hit'⟩ := hit
    have hiw : i.val < state.val.length := by simp; omega
    obtain ⟨j, ej, hj⟩ := usize_add_one i (by have := RATE.hBounds; scalar_tac)
    rw [pf_loop_unfold]
    simp only [p3_symmetric.hax_reshaped.padding_free_hash_loop.body, e,
      Std.Array.index_mut_usize, Lib.index_usize_eq _ _ hiw]
    simp only [bind_ok, ej]
    by_cases hjr : j = RATE
    · obtain ⟨s2, e2, hs2⟩ := hf.permute_mut (state.set i x)
      obtain ⟨st', i', e', h', hi'⟩ := ih it' hit' s2 0#usize (by simp; omega)
      refine ⟨st', i', ?_, ?_, hi'⟩
      · simp [hjr, e2, e']
      · rw [List.foldl_cons, h']
        have : i.val + 1 = RATE.val := by rw [← hj, hjr]
        simp [pfStep, this, hs2]
    · obtain ⟨st', i', e', h', hi'⟩ := ih it' hit' (state.set i x) j (by
        have : j.val ≠ RATE.val := fun h => hjr (UScalar.eq_of_val_eq h)
        omega)
      refine ⟨st', i', ?_, ?_, hi'⟩
      · simp [hjr, e']
      · rw [List.foldl_cons, h']
        have : i.val + 1 ≠ RATE.val := fun h => hjr (UScalar.eq_of_val_eq (by rw [hj, h]))
        simp [pfStep, this, hj]

/-- `&a[..end]` of an array. -/
theorem array_index_rangeTo_eq {T : Type} {N : Std.Usize} (a : Std.Array T N) (e : Std.Usize)
    (h : e.val ≤ N.val) :
    core.Array.Insts.CoreOpsIndexIndex.index
      (core.Slice.Insts.CoreOpsIndexIndex
        (core.ops.range.RangeToUsize.Insts.CoreSliceIndexSliceIndexSliceSlice T))
      a { «end» := e } =
      .ok (Slice.from (a.val.take e.val) (by
        have := a.property; simp only [List.length_take]; scalar_tac)) := by
  simp only [core.Array.Insts.CoreOpsIndexIndex.index, core.array.Array.as_slice,
    rust_primitives.slice.array_as_slice, bind_ok]
  rw [Lib.index_rangeTo_eq _ _ (by simpa [Std.Array.to_slice] using h)]
  congr 2
  simp [Std.Array.to_slice, List.slice]

/-- A slice of length `N` converts to the array of its elements, at any length. -/
theorem try_from_eq_le {T : Type} [Inhabited T] (N : Std.Usize) (inst : core.marker.Copy T)
    (x : Slice T) (h : x.val.length = N.val) :
    core.Array.Insts.CoreConvertTryFromShared0SliceTryFromSliceError.try_from N inst x =
      .ok (.Ok (Std.Array.from x.val h)) := by
  unfold core.Array.Insts.CoreConvertTryFromShared0SliceTryFromSliceError.try_from
  have hlen : Slice.len x = N := UScalar.eq_of_val_eq (by simpa using h)
  simp only [rust_primitives.slice.slice_length, bind_ok, hlen, ite_true]
  rw [Lib.array_from_fn_eq N _ x (fun k => x.val[k]!) (fun k hk => by
    simp only [core.convert.TryFromArrayShared0SliceTryFromSliceError.try_from.closure.Insts.CoreOpsFunctionFnMutTupleUsizeT.call_mut,
      rust_primitives.slice.slice_index]
    rw [Lib.slice_index_eq _ _ (by rw [Lib.usz_val_le N (by omega)]; omega), bind_ok]
    simp [Lib.usz_val_le N (show k ≤ N.val by omega), List.getElem!_eq_getElem?_getD,
      List.getElem?_eq_getElem (show k < x.val.length by omega)])]
  rw [bind_ok]
  congr 2
  apply Std.Array.ext
  simp only [Std.Array.from_val]
  apply List.ext_getElem (by simp [h])
  intro i h1 h2
  simp [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem h2]

/-- Squeezing: the first `OUT` cells of the state, as an array. -/
theorem squeeze_eq {T : Type} [Inhabited T] {W : Std.Usize} (OUT : Std.Usize)
    (copyInst : core.marker.Copy T) (st : Std.Array T W) (h : OUT.val ≤ W.val) :
    (do
      let s ← core.Array.Insts.CoreOpsIndexIndex.index
        (core.Slice.Insts.CoreOpsIndexIndex
          (core.ops.range.RangeToUsize.Insts.CoreSliceIndexSliceIndexSliceSlice T))
        st { «end» := OUT }
      let r ← core.Array.Insts.CoreConvertTryFromShared0SliceTryFromSliceError.try_from OUT
        copyInst s
      core.result.Result.unwrap core.array.TryFromSliceError.Insts.CoreFmtDebug r) =
      .ok (Std.Array.from (st.val.take OUT.val) (by simp; omega)) := by
  rw [array_index_rangeTo_eq st OUT h]
  simp only [bind_tc_ok]
  rw [try_from_eq_le OUT copyInst _ (by simp; omega)]
  simp only [bind_tc_ok, core.result.Result.unwrap]
  congr 1
  apply Std.Array.ext
  simp

/-- The padding-free sponge returns the block-wise specification on whatever its iterator yields, and never panics.

The hypotheses are what `PaddingFreeSponge::new` checks, plus a permutation that computes `f` and plain-data `T`.
-/
theorem padding_free_hash_eq {T P I J : Type} {W : Std.Usize} (RATE OUT : Std.Usize)
    (defInst : core.default.Default T) (copyInst : core.marker.Copy T)
    (permInst : p3_symmetric.permutation.CryptographicPermutation P (Std.Array T W))
    (iterInst : core.iter.traits.collect.IntoIterator I T J) (p : P) (input : I)
    (f : List T → List T) (z : T) (xs : List T)
    (hf : PermComputes permInst p f) (hz : defInst.default = .ok z)
    (hcl : ∀ x, copyInst.cloneCloneInst.clone x = .ok x)
    (hit : ∃ it, iterInst.into_iter input = .ok it ∧ Yields iterInst.iteratorIteratorInst it xs)
    (hr : 0 < RATE.val) (hrw : RATE.val < W.val) (hout : OUT.val ≤ W.val) :
    ∃ out, p3_symmetric.hax_reshaped.padding_free_hash RATE OUT defInst copyInst permInst iterInst
        p input = .ok out ∧ out.val = paddingFree f z W.val RATE.val OUT.val xs := by
  have : Inhabited T := ⟨z⟩
  obtain ⟨it, eit, hyit⟩ := hit
  obtain ⟨st, i, el, hl, hi⟩ := pf_loop RATE defInst permInst iterInst p f hf (by omega) xs it hyit
    (Std.Array.from (List.replicate W.val z) (by simp)) 0#usize (by simp; omega)
  have hlenf : ∀ s : List T, s.length = W.val → (f s).length = W.val := fun s hs => by
    simpa [Std.Array.from_val] using hf.length (Std.Array.from s hs)
  have hfin : pfFinish f (st.val, i.val) =
      (blocks RATE.val xs).foldl (absorb f) (List.replicate W.val z) := by
    rw [hl]
    simp only [Std.Array.from_val]
    rw [show (0#usize : Std.Usize).val = 0 from rfl]
    exact pfFinish_foldl f W.val RATE.val hr (by omega) hlenf xs _ (by simp)
  unfold p3_symmetric.hax_reshaped.padding_free_hash
  simp only [hz, bind_ok, Lib.repeat_eq W copyInst.cloneCloneInst z hcl (by omega), eit, el]
  by_cases hi0 : i = 0#usize
  · subst hi0
    simp
    refine ⟨_, squeeze_eq OUT copyInst st hout, ?_⟩
    simp only [pfFinish, ne_eq] at hfin
    simp [paddingFree, ← hfin]
  · obtain ⟨s2, e2, hs2⟩ := hf.permute_mut st
    have hi0' : i.val ≠ 0 := fun h => hi0 (UScalar.eq_of_val_eq (by simpa using h))
    simp [e2, hi0']
    refine ⟨_, squeeze_eq OUT copyInst s2 hout, ?_⟩
    have : i.val ≠ 0 := fun h => hi0 (UScalar.eq_of_val_eq (by simpa using h))
    simp only [pfFinish, this, ne_eq, not_false_eq_true, ite_true] at hfin
    simp [paddingFree, ← hfin, hs2]

/-! ## The 10-padded sponge -/

theorem p10_loop0_unfold {T P I J : Type} {W : Std.Usize} (RATE : Std.Usize)
    (defInst : core.default.Default T)
    (permInst : p3_symmetric.permutation.CryptographicPermutation P (Std.Array T W))
    (iterInst : core.iter.traits.collect.IntoIterator I T J) (p : P) (it : J)
    (state : Std.Array T W) (i : Std.Usize) (full : Bool) :
    p3_symmetric.hax_reshaped.pad10_hash_loop0 RATE defInst permInst iterInst it p state i full =
      (do
        let r ← p3_symmetric.hax_reshaped.pad10_hash_loop0.body RATE defInst permInst iterInst
          p it state i full
        match r with
        | ControlFlow.cont (it', state', i', full') =>
          p3_symmetric.hax_reshaped.pad10_hash_loop0 RATE defInst permInst iterInst it' p
            state' i' full'
        | ControlFlow.done x => RustM.ok x) := by
  conv => lhs; rw [p3_symmetric.hax_reshaped.pad10_hash_loop0, loop]
  apply congrArg
  funext r
  rcases r with ⟨it', state', i', full'⟩ | x
  · rfl
  · rfl

theorem p10_loop0 {T P I J : Type} {W : Std.Usize} (RATE : Std.Usize)
    (defInst : core.default.Default T)
    (permInst : p3_symmetric.permutation.CryptographicPermutation P (Std.Array T W))
    (iterInst : core.iter.traits.collect.IntoIterator I T J) (p : P) (f : List T → List T)
    (hf : PermComputes permInst p f) (hrw : RATE.val ≤ W.val) :
    ∀ (xs : List T) (it : J), Yields iterInst.iteratorIteratorInst it xs →
      ∀ (state : Std.Array T W) (i : Std.Usize) (full : Bool), i.val < RATE.val →
      ∃ (state' : Std.Array T W) (i' : Std.Usize) (full' : Bool),
        p3_symmetric.hax_reshaped.pad10_hash_loop0 RATE defInst permInst iterInst it p
          state i full = .ok (state', i', full') ∧
        (state'.val, i'.val, full') = xs.foldl (p10Step f RATE.val) (state.val, i.val, full) ∧
        i'.val < RATE.val := by
  intro xs
  induction xs with
  | nil =>
    intro it hit state i full hi
    obtain ⟨it', e⟩ := hit
    refine ⟨state, i, full, ?_, rfl, hi⟩
    rw [p10_loop0_unfold]
    simp [p3_symmetric.hax_reshaped.pad10_hash_loop0.body, e]
  | cons x xs ih =>
    intro it hit state i full hi
    obtain ⟨it', e, hit'⟩ := hit
    obtain ⟨j, ej, hj⟩ := usize_add_one i (by have := RATE.hBounds; scalar_tac)
    -- The state the item lands in, after a waiting full block is permuted.
    obtain ⟨st1, est1, hst1⟩ : ∃ st1 : Std.Array T W,
        (if full then do
            let s2 ← permInst.PermutationInst.permute_mut p state
            RustM.ok (s2, false)
          else RustM.ok (state, full)) = .ok (st1, false) ∧ st1.val = p10Pre f full state.val := by
      cases full
      · exact ⟨state, rfl, rfl⟩
      · obtain ⟨s2, e2, hs2⟩ := hf.permute_mut state
        exact ⟨s2, by simp [e2], hs2⟩
    have hiw : i.val < st1.val.length := by simp; omega
    rw [p10_loop0_unfold]
    simp only [p3_symmetric.hax_reshaped.pad10_hash_loop0.body, e]
    simp only [bind_ok]
    by_cases hjr : j = RATE
    · obtain ⟨st', i', full', e', h', hi'⟩ := ih it' hit' (st1.set i x) 0#usize true (by simp; omega)
      refine ⟨st', i', full', ?_, ?_, hi'⟩
      · simp [hjr, est1, Std.Array.index_mut_usize, Lib.index_usize_eq _ _ hiw, ej, e']
      · rw [List.foldl_cons, h']
        have : i.val + 1 = RATE.val := by rw [← hj, hjr]
        simp [p10Step, this, hst1]
    · obtain ⟨st', i', full', e', h', hi'⟩ := ih it' hit' (st1.set i x) j false (by
        have : j.val ≠ RATE.val := fun h => hjr (UScalar.eq_of_val_eq h)
        omega)
      refine ⟨st', i', full', ?_, ?_, hi'⟩
      · simp [hjr, est1, Std.Array.index_mut_usize, Lib.index_usize_eq _ _ hiw, ej, e']
      · rw [List.foldl_cons, h']
        have : i.val + 1 ≠ RATE.val := fun h => hjr (UScalar.eq_of_val_eq (by rw [hj, h]))
        simp [p10Step, this, hj, hst1]

theorem p10_loop1_unfold {T : Type} {W : Std.Usize} (RATE : Std.Usize) (t : T)
    (state : Std.Array T W) (j : Std.Usize) :
    p3_symmetric.hax_reshaped.pad10_hash_loop1 RATE t state j =
      (do
        let r ← p3_symmetric.hax_reshaped.pad10_hash_loop1.body RATE t state j
        match r with
        | ControlFlow.cont (state', j') => p3_symmetric.hax_reshaped.pad10_hash_loop1 RATE t state' j'
        | ControlFlow.done x => RustM.ok x) := by
  conv => lhs; rw [p3_symmetric.hax_reshaped.pad10_hash_loop1, loop]
  apply congrArg
  funext r
  rcases r with ⟨state', j'⟩ | x
  · rfl
  · rfl

/-- The zero fill after the sentinel: positions `j` up to `RATE` are overwritten with `t`. -/
theorem p10_loop1 {T : Type} {W : Std.Usize} (RATE : Std.Usize) (t : T) (hrw : RATE.val ≤ W.val) :
    ∀ (n : ℕ) (state : Std.Array T W) (j : Std.Usize), RATE.val - j.val = n → j.val ≤ RATE.val →
      ∃ state' : Std.Array T W,
        p3_symmetric.hax_reshaped.pad10_hash_loop1 RATE t state j = .ok state' ∧
        state'.val = state.val.take j.val ++ List.replicate (RATE.val - j.val) t ++
          state.val.drop RATE.val := by
  intro n
  induction n with
  | zero =>
    intro state j hn hj
    refine ⟨state, ?_, ?_⟩
    · rw [p3_symmetric.hax_reshaped.pad10_hash_loop1, loop]
      have : ¬ j < RATE := by scalar_tac
      simp [p3_symmetric.hax_reshaped.pad10_hash_loop1.body, this]
    · have : j.val = RATE.val := by omega
      rw [this, Nat.sub_self, List.replicate_zero, List.append_nil, List.take_append_drop]
  | succ n ih =>
    intro state j hn hj
    have hjr : j.val < RATE.val := by omega
    have hjw : j.val < state.val.length := by simp; omega
    obtain ⟨j', ej, hj'⟩ := usize_add_one j (by have := RATE.hBounds; scalar_tac)
    obtain ⟨st', e', h'⟩ := ih (Std.Array.from (state.val.set j.val t) (by simp)) j' (by omega)
      (by omega)
    refine ⟨st', ?_, ?_⟩
    · rw [p10_loop1_unfold]
      have : j < RATE := by scalar_tac
      simp only [p3_symmetric.hax_reshaped.pad10_hash_loop1.body, this, ite_true,
        Lib.update_eq _ _ _ hjw, bind_ok, ej]
      exact e'
    · rw [h', hj']
      simp only [Std.Array.from_val]
      apply List.ext_getElem (by simp; omega)
      intro k h1 h2
      simp only [List.getElem_append, List.getElem_take, List.getElem_drop, List.getElem_set,
        List.getElem_replicate, List.length_take, List.length_append, List.length_replicate,
        List.length_set]
      split_ifs <;> first | rfl | omega | (congr 1; omega)

/-- The 10-padded sponge returns the padded block-wise specification on whatever its iterator yields, and never panics.

The hypotheses are what `Pad10Sponge::new` checks, plus a permutation that computes `f`, a padding function that computes `d`, and plain-data `T`.
-/
theorem pad10_hash_eq {T P D I J : Type} {W : Std.Usize} (RATE OUT : Std.Usize)
    (defInst : core.default.Default T) (copyInst : core.marker.Copy T)
    (permInst : p3_symmetric.permutation.CryptographicPermutation P (Std.Array T W))
    (derInst : p3_symmetric.permutation.Derangement D T)
    (iterInst : core.iter.traits.collect.IntoIterator I T J) (p : P) (dp : D) (input : I)
    (f : List T → List T) (d : T → T) (z : T) (xs : List T)
    (hf : PermComputes permInst p f) (hd : ∀ x, derInst.PermutationInst.permute dp x = .ok (d x))
    (hz : defInst.default = .ok z)
    (hcl : ∀ x, copyInst.cloneCloneInst.clone x = .ok x)
    (hit : ∃ it, iterInst.into_iter input = .ok it ∧ Yields iterInst.iteratorIteratorInst it xs)
    (hr : 0 < RATE.val) (hrw : RATE.val < W.val) (hout : OUT.val ≤ W.val) :
    ∃ out, p3_symmetric.hax_reshaped.pad10_hash RATE OUT defInst copyInst permInst derInst iterInst
        p dp input = .ok out ∧ out.val = pad10 f d z W.val RATE.val OUT.val xs := by
  have : Inhabited T := ⟨z⟩
  obtain ⟨it, eit, hyit⟩ := hit
  obtain ⟨st, i, full, el, hl, hi⟩ := p10_loop0 RATE defInst permInst iterInst p f hf (by omega)
    xs it hyit (Std.Array.from (List.replicate W.val z) (by simp)) 0#usize false (by simp; omega)
  have hlenf : ∀ s : List T, s.length = W.val → (f s).length = W.val := fun s hs => by
    simpa [Std.Array.from_val] using hf.length (Std.Array.from s hs)
  have hfin : p10Finish f d z RATE.val (st.val, i.val, full) =
      p10Core f d z RATE.val (List.replicate W.val z) xs := by
    rw [hl]
    simp only [Std.Array.from_val]
    rw [show (0#usize : Std.Usize).val = 0 from rfl]
    exact p10Finish_foldl f d z W.val RATE.val hr (by omega) hlenf xs _ (by simp)
  unfold p3_symmetric.hax_reshaped.pad10_hash
  simp only [hz, bind_ok, Lib.repeat_eq W copyInst.cloneCloneInst z hcl (by omega), eit, el]
  have hrl : RATE.val < st.val.length := by simp; omega
  cases full
  · have hil : i.val < st.val.length := by simp; omega
    obtain ⟨j, ej, hj⟩ := usize_add_one i (by have := RATE.hBounds; scalar_tac)
    obtain ⟨st2, e2, h2⟩ := p10_loop1 (W := W) RATE z (by omega) (RATE.val - j.val)
      (Std.Array.from (st.val.set i.val (d z)) (by simp)) j rfl (by omega)
    obtain ⟨s3, e3, hs3⟩ := hf.permute_mut st2
    simp [hd, Lib.update_eq _ _ _ hil, ej, e2, e3]
    refine ⟨_, squeeze_eq OUT copyInst s3 hout, ?_⟩
    rw [pad10_eq_p10Core, ← hfin]
    simp only [Std.Array.from_val, p10Finish, Bool.false_eq_true, ite_false, hs3, h2, hj]
    congr 2
    apply List.ext_getElem (by simp; omega)
    intro k h1 h3
    simp only [List.length_take, List.length_append, List.length_replicate, List.length_set,
      List.length_drop, List.length_cons] at h1 h3
    simp only [List.getElem_append, List.getElem_take, List.getElem_drop, List.getElem_set,
      List.getElem_replicate, List.getElem_cons, List.length_take, List.length_append,
      List.length_replicate, List.length_set, List.length_cons]
    split_ifs <;> first | rfl | omega | (congr 1; omega)
  · obtain ⟨s3, e3, hs3⟩ := hf.permute_mut (Std.Array.from (st.val.set RATE.val (d st.val[RATE.val]))
      (by simp))
    simp [hd, Lib.index_usize_eq _ _ hrl, Lib.update_eq _ _ _ hrl, e3]
    refine ⟨_, squeeze_eq OUT copyInst s3 hout, ?_⟩
    rw [pad10_eq_p10Core, ← hfin]
    simp only [Std.Array.from_val, p10Finish, ite_true, hs3]
    rw [List.getD_eq_getElem _ _ hrl]

end Plonky3Lean.Proofs.Symmetric
