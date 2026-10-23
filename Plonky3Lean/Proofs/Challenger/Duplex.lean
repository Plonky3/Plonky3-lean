module

public import P3Challenger
public import Plonky3Lean.Proofs.Challenger.Machine
public import Plonky3Lean.Proofs.Symmetric.Compression

@[expose] public section

/-!
# The extracted duplex challenger computes the list machine

The extraction is generic over the field and the permutation.

The field enters through its trait dictionaries, and the proofs assume only what each member the code calls returns:

* `ZERO` is `0`, `from_u8 k` is `k`, and `+=` adds, in some `AddMonoidWithOne` structure on the field type;
* `clone` of a field element is the element itself;
* the permutation computes a function `f` on states and never panics.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open Plonky3Lean.Spec.Duplex Plonky3Lean.Proofs.Symmetric

namespace Plonky3Lean.Proofs.Challenger

/-- The members of `PrimeCharacteristicRing` the duplexing step calls compute `0`, the cast of a byte, and addition. -/
structure RingComputes {F : Type} [AddMonoidWithOne F] (inst : p3_field.field.PrimeCharacteristicRing F) :
    Prop where
  zero : inst.ZERO = .ok 0
  from_u8 : ∀ k : Std.U8, inst.from_u8 k = .ok (k.val : F)
  add_assign : ∀ a b : F, inst.coreopsarithAddAssignInst.add_assign a b = .ok (a + b)

/-- `clone` of a value is the value. -/
def CloneIsId {F : Type} (inst : core.marker.Copy F) : Prop := ∀ x, inst.cloneCloneInst.clone x = .ok x

theorem vec_drain_full {T : Type} (v : alloc.vec.Vec T) :
    ∃ d, alloc.vec.Vec.drain alloc.alloc.Global
      (core.ops.range.RangeFull.Insts.CoreOpsRangeRangeBounds Std.Usize) v () = .ok (d, Slice.from [] (by simp)) ∧
      d.1.val = v.val := by
  simp only [alloc.vec.Vec.drain, alloc.vec.Vec.len, rust_primitives.sequence.seq_len,
    core.slice.index.range, core.slice.index.try_range, core.slice.index.start_index,
    core.slice.index.end_index, core.ops.range.RangeFull.Insts.CoreOpsRangeRangeBounds.start_bound,
    core.ops.range.RangeFull.Insts.CoreOpsRangeRangeBounds.end_bound,
    rust_primitives.sequence.seq_drain, bind_ok]
  simp [Slice.len]
  exact ⟨(Slice.from (v : Slice T).val (v : Slice T).property, core.marker.PhantomData.mk), rfl, by simp⟩

theorem drain_next_nil {T A : Type} (d : alloc.vec.drain.Drain T A) (hs : d.1.val = []) :
    alloc.vec.drain.Drain.Insts.CoreIterTraitsIteratorIterator.next d = .ok (.None, d) := by
  obtain ⟨s, pd⟩ := d
  unfold alloc.vec.drain.Drain.Insts.CoreIterTraitsIteratorIterator.next
  simp only [rust_primitives.sequence.seq_len, bind_ok]
  show (if Slice.len s = 0#usize then _ else _) = _
  have h : Slice.len s = 0#usize := by apply UScalar.eq_of_val_eq; simp [Slice.len, hs]
  simp only [h, ↓reduceIte]

theorem drain_next_cons {T A : Type} (d : alloc.vec.drain.Drain T A) (x : T) (xs : List T)
    (hs : d.1.val = x :: xs) :
    ∃ d', alloc.vec.drain.Drain.Insts.CoreIterTraitsIteratorIterator.next d = .ok (.Some x, d') ∧
      d'.1.val = xs := by
  obtain ⟨s, pd⟩ := d
  obtain ⟨s', e, hs'⟩ := Lib.seq_remove_head s x xs hs
  refine ⟨(s', pd), ?_, hs'⟩
  unfold alloc.vec.drain.Drain.Insts.CoreIterTraitsIteratorIterator.next
  simp only [rust_primitives.sequence.seq_len, bind_ok]
  show (if Slice.len s = 0#usize then _ else _) = _
  have h : ¬ Slice.len s = 0#usize := by
    intro h; have := congrArg UScalar.val h; simp [Slice.len] at this; simp [hs] at this
  simp only [h, ↓reduceIte, e, bind_ok]
  rfl

theorem enumerate_next_some {I T : Type} (inst : core.iter.traits.iterator.Iterator I T) (it t : I)
    (c c' : Std.Usize) (x : T) (e : inst.next it = .ok (.Some x, t)) (ec : c + 1#usize = RustM.ok c') :
    core.iter.adapters.enumerate.Enumerate.Insts.CoreIterTraitsIteratorIteratorPairUsizeClause0_Item.next
      inst { iter := it, count := c } =
      .ok (.Some (c, x), (⟨t, c'⟩ : core.iter.adapters.enumerate.Enumerate I)) := by
  unfold core.iter.adapters.enumerate.Enumerate.Insts.CoreIterTraitsIteratorIteratorPairUsizeClause0_Item.next
  rw [e, bind_ok]
  show (do let i ← c + 1#usize
           RustM.ok (core.option.Option.Some (c, x),
             (⟨t, i⟩ : core.iter.adapters.enumerate.Enumerate I))) = _
  simp [ec]

theorem enumerate_next_none {I T : Type} (inst : core.iter.traits.iterator.Iterator I T) (it t : I)
    (c : Std.Usize) (e : inst.next it = .ok (.None, t)) :
    core.iter.adapters.enumerate.Enumerate.Insts.CoreIterTraitsIteratorIteratorPairUsizeClause0_Item.next
      inst { iter := it, count := c } =
      .ok (.None, (⟨t, c⟩ : core.iter.adapters.enumerate.Enumerate I)) := by
  unfold core.iter.adapters.enumerate.Enumerate.Insts.CoreIterTraitsIteratorIteratorPairUsizeClause0_Item.next
  rw [e, bind_ok]
  rfl

/-- Writing the drained inputs at positions `c, c + 1, ...` of the state. -/
theorem duplexing_loop_eq {F : Type} {W : Std.Usize} :
    ∀ (xs : List F) (d : alloc.vec.drain.Drain F alloc.alloc.Global) (c : Std.Usize) (a : Std.Array F W),
      d.1.val = xs → c.val + xs.length ≤ W.val →
      ∃ a', p3_challenger.duplex_challenger.DuplexChallenger.duplexing_loop
        { iter := d, count := c } a = .ok a' ∧
        a'.val = a.val.take c.val ++ xs ++ a.val.drop (c.val + xs.length) := by
  intro xs
  induction xs with
  | nil =>
    intro d c a hs hc
    refine ⟨a, ?_, by simp⟩
    rw [p3_challenger.duplex_challenger.DuplexChallenger.duplexing_loop, loop]
    simp [p3_challenger.duplex_challenger.DuplexChallenger.duplexing_loop.body,
      enumerate_next_none (alloc.vec.drain.Drain.Insts.CoreIterTraitsIteratorIterator F _) d d c
        (drain_next_nil d hs)]
  | cons x xs ih =>
    intro d c a hs hc
    obtain ⟨d', e, hd'⟩ := drain_next_cons d x xs hs
    simp only [List.length_cons] at hc
    obtain ⟨c', ec, hc'⟩ := usize_add_one c (by have := W.hBounds; scalar_tac)
    have hcw : c.val < a.val.length := by simp; omega
    obtain ⟨a', ea', ha'⟩ := ih d' c' (Std.Array.from (a.val.set c.val x) (by simp)) hd' (by omega)
    refine ⟨a', ?_, ?_⟩
    · rw [p3_challenger.duplex_challenger.DuplexChallenger.duplexing_loop, loop]
      simp [p3_challenger.duplex_challenger.DuplexChallenger.duplexing_loop.body,
        enumerate_next_some (alloc.vec.drain.Drain.Insts.CoreIterTraitsIteratorIterator F _) d d' c c' x
          e ec, bind_ok, Lib.update_eq a c x hcw]
      exact ea'
    · rw [ha', hc']
      have hv : (Std.Array.from ((a.val).set c.val x) (by simp) : Std.Array F W).val = a.val.set c.val x := by
        simp
      rw [hv, List.take_add_one, List.getElem?_set_self hcw, List.take_set_of_le (le_refl _),
        List.drop_set_of_lt (by omega)]
      simp [Nat.add_assoc, Nat.add_comm 1]

theorem slice_set_index {T : Type} (s : Slice T) (i : Std.Usize) (h : i.val < s.val.length) :
    Slice.set s i (s.val[i.val]) = s := by
  apply Slice.ext
  rw [Slice.set_val_eq]
  simp

theorem fill_loop_unfold {T : Type} (cl : core.clone.Clone T) (it : core.ops.range.Range Std.Usize)
    (s : Slice T) (v : T) :
    core.slice.Slice.fill_loop cl it s v = (do
      let r ← core.slice.Slice.fill_loop.body cl v it s
      match r with
      | ControlFlow.cont (it', s') => core.slice.Slice.fill_loop cl it' s' v
      | ControlFlow.done x => RustM.ok x) := by
  conv => lhs; rw [core.slice.Slice.fill_loop, loop]
  apply congrArg
  funext r
  rcases r with ⟨it', s'⟩ | x <;> rfl

theorem fill_loop_body_some {T : Type} (cl : core.clone.Clone T) (hcl : ∀ x, cl.clone x = .ok x) (v : T)
    (k k' last : Std.Usize) (s : Slice T)
    (ek : core.IteratorRange.next core.Usize.Insts.CoreIterRangeStep { start := k, «end» := last } =
      .ok (core.option.Option.Some k, { start := k', «end» := last }))
    (hkl : k.val < s.val.length) :
    core.slice.Slice.fill_loop.body cl v { start := k, «end» := last } s =
      .ok (.cont ({ start := k', «end» := last }, Slice.from (s.val.set k.val v) (by have := s.property; simp [*]))) := by
  simp only [core.slice.Slice.fill_loop.body, core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next]
  rw [ek, bind_ok]
  show (do
    let t ← cl.clone v
    let p ← s.index_mut_usize k
    let s2 ← (p.2 p.1).update k t
    RustM.ok (ControlFlow.cont ((⟨k', last⟩ : core.ops.range.Range Std.Usize), s2))) = _
  simp [hcl, Slice.index_mut_usize, Lib.slice_index_eq s k hkl, slice_set_index s k hkl,
    Lib.slice_update_eq s k v hkl]

theorem fill_loop_eq {T : Type} (cl : core.clone.Clone T) (hcl : ∀ x, cl.clone x = .ok x) (v : T)
    (last : Std.Usize) :
    ∀ (n : ℕ) (k : Std.Usize) (s : Slice T), k.val + n = last.val → last.val ≤ s.val.length →
      ∃ s', core.slice.Slice.fill_loop cl { start := k, «end» := last } s v = .ok s' ∧
        s'.val = s.val.take k.val ++ List.replicate n v ++ s.val.drop last.val := by
  intro n
  induction n with
  | zero =>
    intro k s hk hl
    refine ⟨s, ?_, ?_⟩
    · unfold core.slice.Slice.fill_loop
      rw [loop]
      simp [core.slice.Slice.fill_loop.body, Lib.range_next_none k last (by omega)]
    · simp only [List.replicate_zero, List.append_nil]
      rw [show last.val = k.val by omega, List.take_append_drop]
  | succ n ih =>
    intro k s hk hl
    obtain ⟨k', ek, hk'⟩ := Lib.range_next_some k last (by omega)
    have hkl : k.val < s.val.length := by omega
    obtain ⟨s', e', hs'⟩ := ih k' (Slice.from (s.val.set k.val v) (by have := s.property; simp [*]))
      (by omega) (by simp; omega)
    refine ⟨s', ?_, ?_⟩
    · rw [fill_loop_unfold, fill_loop_body_some cl hcl v k k' last s ek hkl, bind_ok]
      exact e'
    · have hv : (Slice.from (s.val.set k.val v) (by have := s.property; simp [*]) : Slice T).val =
          s.val.set k.val v := by simp
      rw [hs', hk', hv, List.take_add_one, List.getElem?_set_self hkl, List.take_set_of_le (le_refl _),
        List.drop_set_of_lt (by omega), List.replicate_succ]
      simp

/-- `fill` writes the value at every position, for a type whose clone is the value itself. -/
theorem fill_eq {T : Type} (cl : core.clone.Clone T) (hcl : ∀ x, cl.clone x = .ok x) (s : Slice T) (v : T) :
    ∃ s', core.slice.Slice.fill cl s v = .ok s' ∧ s'.val = List.replicate s.val.length v := by
  unfold core.slice.Slice.fill
  by_cases h0 : s.val.length = 0
  · refine ⟨s, ?_, by simp [List.length_eq_zero_iff.1 h0]⟩
    simp [core.slice.Slice.len, rust_primitives.slice.slice_length, Slice.len, h0]
  · have hl : 0 < s.val.length := Nat.pos_of_ne_zero h0
    obtain ⟨last, el, hlast⟩ : ∃ last : Std.Usize, Slice.len s - 1#usize = RustM.ok last ∧
        last.val = s.val.length - 1 := by
      have : Slice.len s - 1#usize ⦃ z => z.val = (Slice.len s).val - (1#usize : Std.Usize).val ⦄ := by
        step*
      obtain ⟨z, e, hz⟩ := Lib.spec_imp_exists this
      exact ⟨z, e, by simpa [Slice.len] using hz⟩
    obtain ⟨s1, e1, hs1⟩ := fill_loop_eq cl hcl v last last.val 0#usize s (by simp) (by omega)
    have hll : last.val < s1.val.length := by rw [hs1]; simp; omega
    refine ⟨Slice.from (s1.val.set last.val v) (by have := s1.property; simp [*]), ?_, ?_⟩
    · simp only [core.slice.Slice.len, rust_primitives.slice.slice_length, bind_ok]
      have hpos : s.len > 0#usize := by scalar_tac
      simp only [hpos, ↓reduceIte]
      rw [el, bind_ok, e1, bind_ok]
      show (do let p ← s1.index_mut_usize last; (p.2 p.1).update last v) = _
      simp [Slice.index_mut_usize, Lib.slice_index_eq s1 last hll, slice_set_index s1 last hll,
        Lib.slice_update_eq s1 last v hll]
    · have hv : (Slice.from (s1.val.set last.val v) (by have := s1.property; simp [*]) : Slice T).val =
          s1.val.set last.val v := by simp
      have hs1' : s1.val = List.replicate last.val v ++ s.val.drop last.val := by simpa using hs1
      have hlen1 : s1.val.length = s.val.length := by rw [hs1']; simp; omega
      rw [hv]
      apply List.ext_getElem (by simp [hlen1])
      intro i h1 h2
      rw [List.getElem_set, List.getElem_replicate]
      split_ifs with hi
      · rfl
      · simp only [List.length_set, hlen1] at h1
        simp only [hs1']
        rw [List.getElem_append_left (by simp; omega), List.getElem_replicate]

theorem extend_loop_unfold {T I : Type} (inst : core.iter.traits.iterator.Iterator I T)
    (v : alloc.vec.Vec T) (it : I) :
    alloc.vec.Vec.extend_loop inst v it = (do
      let r ← alloc.vec.Vec.extend_loop.body inst v it
      match r with
      | ControlFlow.cont (v', it') => alloc.vec.Vec.extend_loop inst v' it'
      | ControlFlow.done x => RustM.ok x) := by
  conv => lhs; rw [alloc.vec.Vec.extend_loop, loop]
  apply congrArg
  funext r
  rcases r with ⟨v', it'⟩ | x <;> rfl

/-- `Vec::extend` from an iterator that yields `xs` appends `xs`. -/
theorem extend_loop_eq {T I : Type} (inst : core.iter.traits.iterator.Iterator I T) :
    ∀ (xs : List T) (v : alloc.vec.Vec T) (it : I), Yields inst it xs →
      v.val.length + xs.length ≤ Usize.max →
      ∃ v', alloc.vec.Vec.extend_loop inst v it = .ok v' ∧ v'.val = v.val ++ xs := by
  intro xs
  induction xs with
  | nil =>
    intro v it ⟨it', e⟩ _
    refine ⟨v, ?_, by simp⟩
    rw [extend_loop_unfold]
    simp [alloc.vec.Vec.extend_loop.body, e]
  | cons x xs ih =>
    intro v it ⟨it', e, hy⟩ hl
    simp only [List.length_cons] at hl
    obtain ⟨v1, e1, hv1⟩ := vec_push_eq v x (by omega)
    obtain ⟨v', e', hv'⟩ := ih v1 it' hy (by rw [hv1]; simp; omega)
    refine ⟨v', ?_, by rw [hv', hv1]; simp⟩
    rw [extend_loop_unfold]
    simp [alloc.vec.Vec.extend_loop.body, e, e1, e']

/-- Extending a vector by a slice of plain data appends the slice. -/
theorem extend_slice_eq {T : Type} (copyInst : core.marker.Copy T) (v : alloc.vec.Vec T) (s : Slice T)
    (hl : v.val.length + s.val.length ≤ Usize.max) :
    ∃ v', alloc.vec.Vec.Insts.CoreIterTraitsCollectExtendSharedAT.extend copyInst
        (core.SharedASlice.Insts.CoreIterTraitsCollectIntoIteratorSharedATIter T) v s = .ok v' ∧
      v'.val = v.val ++ s.val := by
  obtain ⟨v', e, h⟩ := extend_loop_eq (core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT T)
    s.val v s (seq_next_yields _ (fun _ => rfl) s.val s rfl) hl
  refine ⟨v', ?_, h⟩
  simp only [alloc.vec.Vec.Insts.CoreIterTraitsCollectExtendSharedAT.extend,
    alloc.vec.Vec.Insts.CoreIterTraitsCollectExtend.extend,
    core.SharedASlice.Insts.CoreIterTraitsCollectIntoIteratorSharedATIter.into_iter,
    core.slice.Slice.iter, rust_primitives.sequence.seq_from_slice]
  rw [@Std.bind_ok (rust_primitives.sequence.Seq T) (core.slice.iter.Iter T) s,
    @Std.bind_ok (core.slice.iter.Iter T) (core.slice.iter.Iter T) s,
    @Std.bind_ok (core.slice.iter.Iter T) (alloc.vec.Vec T) s]
  exact e

theorem take_len_le_max {T : Type} {W : Std.Usize} (a : Std.Array T W) (k : ℕ) :
    (a.val.take k).length ≤ Usize.max := by
  have := a.property
  simp only [List.length_take]
  scalar_tac

/-- An empty vector, typed as a vector. -/
def vnil (T : Type) : alloc.vec.Vec T := Slice.new T

@[simp] theorem vnil_val (T : Type) : (vnil T).val = [] := rfl

/-- The list machine's view of an extracted duplex challenger. -/
def toSt {F P : Type} {W R : Std.Usize} (c : p3_challenger.duplex_challenger.DuplexChallenger F P W R) : St F :=
  ⟨c.sponge_state.val, c.input_buffer.val, c.output_buffer.val⟩

/-- The padded state, written as the code builds it: the inputs, then zeros up to the rate, then the length added to cell `r`. -/
theorem pad_as_built {F : Type} [AddMonoidWithOne F] (r : ℕ) (s σ : List F) (hσ : σ ≠ [])
    (hle : σ.length ≤ r) (hr : r < s.length) :
    let X := (σ ++ s.drop σ.length).take σ.length ++ List.replicate (r - σ.length) 0 ++
      (σ ++ s.drop σ.length).drop r
    X.set r (X.getD r 0 + (σ.length : F)) = pad r s σ := by
  intro X
  have h1 : (σ ++ s.drop σ.length).take σ.length = σ := by simp
  have h2 : (σ ++ s.drop σ.length).drop r = s.drop r := by
    rw [List.drop_append, List.drop_eq_nil_of_le (by omega), List.nil_append, List.drop_drop]
    congr 1
    omega
  have hX : X = σ ++ List.replicate (r - σ.length) 0 ++ s.drop r := by simp only [X, h1, h2]
  have hlen : (σ ++ List.replicate (r - σ.length) (0 : F)).length = r := by simp; omega
  have hd : s.drop r = s.getD r 0 :: s.drop (r + 1) := by
    rw [List.getD_eq_getElem _ _ hr, List.drop_eq_getElem_cons hr]
  rw [hX, List.getD_append_right _ _ _ _ (by rw [hlen]), hlen, Nat.sub_self, hd,
    List.set_append_right _ _ (by rw [hlen]), hlen, Nat.sub_self]
  simp [pad, hσ]

/-- The duplexing step returns the list machine's duplexing, and never panics, when at most `RATE` inputs are pending.

The hypotheses are the constructor's shape checks, the members the step calls, and a permutation that computes `f`. -/
theorem duplexing_eq {F P : Type} [AddMonoidWithOne F] {W R : Std.Usize}
    (copyInst : core.marker.Copy F)
    (permInst : p3_symmetric.permutation.CryptographicPermutation P (Std.Array F W))
    (ringInst : p3_field.field.PrimeCharacteristicRing F)
    (hcopy : CloneIsId copyInst) (hring : RingComputes ringInst) (f : List F → List F)
    (c : p3_challenger.duplex_challenger.DuplexChallenger F P W R)
    (hf : PermComputes permInst c.permutation f) (hRW : R.val < W.val) (h255 : R.val ≤ 255)
    (hin : c.input_buffer.val.length ≤ R.val) :
    ∃ c', p3_challenger.duplex_challenger.DuplexChallenger.duplexing copyInst permInst ringInst c = .ok c' ∧
      toSt c' = (toSt c).duplexing f R.val ∧ c'.permutation = c.permutation := by
  obtain ⟨d, ed, hd⟩ := vec_drain_full c.input_buffer
  have hlen : c.sponge_state.val.length = W.val := by simp
  obtain ⟨a, ea, ha⟩ := duplexing_loop_eq c.input_buffer.val d 0#usize c.sponge_state hd
    (by simp; omega)
  have hlenv : (Slice.len c.input_buffer).val = c.input_buffer.val.length := by simp [Slice.len]
  unfold p3_challenger.duplex_challenger.DuplexChallenger.duplexing
  -- The same program, with each pair read through its projections and each vector typed as one.
  show ∃ c', (do
    let n ← alloc.vec.Vec.len c.input_buffer
    massert (n ≤ R)
    let p ← alloc.vec.Vec.drain alloc.alloc.Global
      (core.ops.range.RangeFull.Insts.CoreOpsRangeRangeBounds Std.Usize) c.input_buffer ()
    let it ← core.iter.traits.iterator.Iterator.enumerate.default
      (alloc.vec.drain.Drain.Insts.CoreIterTraitsIteratorIterator F alloc.alloc.Global) p.1
    let a ← p3_challenger.duplex_challenger.DuplexChallenger.duplexing_loop it c.sponge_state
    let a1 ← if n > 0#usize then (do
        let q ← core.Array.Insts.CoreOpsIndexIndexMut.index_mut
          (core.Slice.Insts.CoreOpsIndexIndexMut
            (core.ops.range.RangeUsize.Insts.CoreSliceIndexSliceIndexSliceSlice F))
          a { start := n, «end» := R }
        let t ← ringInst.ZERO
        let s1 ← core.slice.Slice.fill copyInst.cloneCloneInst q.1 t
        let r ← Std.Array.index_mut_usize (q.2 s1) R
        let i ← lift (UScalar.cast .U8 n)
        let t2 ← ringInst.from_u8 i
        let t3 ← ringInst.coreopsarithAddAssignInst.add_assign r.1 t2
        RustM.ok (r.2 t3)) else RustM.ok a
    let a2 ← permInst.PermutationInst.permute_mut c.permutation a1
    let v1 ← alloc.vec.Vec.clear c.output_buffer
    let s ← core.Array.Insts.CoreOpsIndexIndex.index
      (core.Slice.Insts.CoreOpsIndexIndex
        (core.ops.range.RangeToUsize.Insts.CoreSliceIndexSliceIndexSliceSlice F)) a2 { «end» := R }
    let v2 ← alloc.vec.Vec.Insts.CoreIterTraitsCollectExtendSharedAT.extend copyInst
      (core.SharedASlice.Insts.CoreIterTraitsCollectIntoIteratorSharedATIter F) v1 s
    RustM.ok (p3_challenger.duplex_challenger.DuplexChallenger.mk a2 p.2 v2 c.permutation)) = RustM.ok c' ∧
      toSt c' = St.duplexing f R.val (toSt c) ∧ c'.permutation = c.permutation
  have hm : Slice.len (c.input_buffer : Slice F) ≤ R := by scalar_tac
  have hen : core.iter.traits.iterator.Iterator.enumerate.default
      (alloc.vec.drain.Drain.Insts.CoreIterTraitsIteratorIterator F alloc.alloc.Global) d =
      .ok { iter := d, count := 0#usize } := rfl
  simp only [alloc.vec.Vec.len, rust_primitives.sequence.seq_len, bind_ok, massert, hm, ↓reduceIte,
    ed, hen, ea]
  -- The clean output buffer, then the new rate copied into it.
  have hclear : alloc.vec.Vec.clear c.output_buffer = .ok (vnil F) := by
    simp [alloc.vec.Vec.clear, rust_primitives.sequence.seq_empty, vnil]
  by_cases hn : c.input_buffer.val = []
  · -- No input: a blank call permutes the state as it is.
    have hn0 : ¬ (Slice.len (c.input_buffer : Slice F) > 0#usize) := by
      intro h; have := (UScalar.lt_equiv _ _).1 h; simp [Slice.len, hn] at this
    have ha' : a = c.sponge_state := Std.Array.ext _ _ (by rw [ha]; simp [hn])
    obtain ⟨a2, ea2, ha2⟩ := hf.permute_mut c.sponge_state
    have hla2 : a2.val.length = W.val := by rw [ha2]; exact hf.length _
    obtain ⟨v2, ev2, hv2⟩ := extend_slice_eq copyInst (vnil F)
      (Slice.from (a2.val.take R.val) (take_len_le_max a2 R.val))
      (by simpa using take_len_le_max a2 R.val)
    refine ⟨⟨a2, Slice.from [] (Nat.zero_le _), v2, c.permutation⟩, ?_, ?_, rfl⟩
    · simp only [hn0, ↓reduceIte, bind_ok, ha', ea2, hclear,
        array_index_rangeTo_eq a2 R (by omega), ev2]
    · simp [toSt, St.duplexing, pad, hn, ha2, hv2]
  · -- An absorbing call: overwrite the rate, zero its tail, add the length to cell `RATE`, permute.
    set n := Slice.len (c.input_buffer : Slice F) with hndef
    have hnv : n.val = c.input_buffer.val.length := hlenv
    have hpos : n > 0#usize := by
      have : 0 < c.input_buffer.val.length := List.length_pos_of_ne_nil hn
      scalar_tac
    have hla : a.val.length = W.val := by simp
    obtain ⟨sl, back, eidx, hsl, hback⟩ := array_index_mut_range a n R (by omega) (by omega)
    obtain ⟨s1, es1, hs1⟩ := fill_eq copyInst.cloneCloneInst hcopy sl 0
    have hRb : R.val < (back s1).val.length := by simp; omega
    have hcast : (UScalar.cast .U8 n).val = c.input_buffer.val.length := by
      simp [UScalar.cast_val_eq]; omega
    set t3 : F := (back s1).val.getD R.val 0 + (c.input_buffer.val.length : F) with ht3
    have ht3' : (back s1).val[R.val] + (c.input_buffer.val.length : F) = t3 := by
      rw [ht3, List.getD_eq_getElem _ _ hRb]
    obtain ⟨a2, ea2, ha2⟩ := hf.permute_mut (Std.Array.set (back s1) R t3)
    have hla2 : a2.val.length = W.val := by rw [ha2]; exact hf.length _
    obtain ⟨v2, ev2, hv2⟩ := extend_slice_eq copyInst (vnil F)
      (Slice.from (a2.val.take R.val) (take_len_le_max a2 R.val))
      (by simpa using take_len_le_max a2 R.val)
    refine ⟨⟨a2, Slice.from [] (Nat.zero_le _), v2, c.permutation⟩, ?_, ?_, rfl⟩
    · simp only [hpos, ↓reduceIte, bind_ok, eidx, hring.zero, es1, Std.Array.index_mut_usize,
        Lib.index_usize_eq _ _ hRb, hring.from_u8, hring.add_assign, hclear]
      simp only [bind_tc_ok, bind_ok, lift, hcast, ht3', ea2, array_index_rangeTo_eq a2 R (by omega), ev2]
    · have hpad := pad_as_built R.val c.sponge_state.val c.input_buffer.val hn hin (by omega)
      have hbs := hback s1 (by rw [hs1, hsl]; simp)
      have hsetv : ((back s1).set R t3).val = pad R.val c.sponge_state.val c.input_buffer.val := by
        rw [← hpad, Std.Array.set_val_eq, ht3, hbs, hs1, hsl, ha, hnv,
          show ((0#usize : Std.Usize) : ℕ) = 0 from rfl, List.take_zero, List.nil_append, Nat.zero_add]
      simp [toSt, St.duplexing, hv2, ha2, hsetv]

end Plonky3Lean.Proofs.Challenger
