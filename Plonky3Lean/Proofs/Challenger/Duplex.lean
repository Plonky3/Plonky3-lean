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

end Plonky3Lean.Proofs.Challenger
