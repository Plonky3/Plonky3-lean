module

public import Plonky3Lean.Lib

@[expose] public section

/-!
# Iterators that yield a list

An iterator yields `xs` when calling `next` repeatedly returns the items of `xs` in order, then `None`.

Arrays and vectors, as CoreModels iterates them, yield their elements.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc

namespace Plonky3Lean.Proofs.Symmetric

/-- `it` run from `s` returns the items of `xs` in order, then `None`. -/
def Yields {I T : Type} (it : core.iter.traits.iterator.Iterator I T) : I → List T → Prop
  | s, [] => ∃ s', it.next s = .ok (.None, s')
  | s, x :: xs => ∃ s', it.next s = .ok (.Some x, s') ∧ Yields it s' xs

theorem seq_next_yields {T : Type} (next : rust_primitives.sequence.Seq T →
      RustM (core.option.Option T × rust_primitives.sequence.Seq T))
    (hnext : ∀ s : rust_primitives.sequence.Seq T, next s = (do
      let i ← rust_primitives.sequence.seq_len s
      if i = 0#usize then .ok (core.option.Option.None, s)
      else
        let (res, s') ← rust_primitives.sequence.seq_remove s 0#usize
        .ok (core.option.Option.Some res, s'))) :
    ∀ (xs : List T) (s : rust_primitives.sequence.Seq T), s.val = xs →
      Yields { next := next } s xs := by
  intro xs
  induction xs with
  | nil =>
    intro s hs
    refine ⟨s, ?_⟩
    show next s = _
    rw [hnext]
    have : Slice.len s = 0#usize := UScalar.eq_of_val_eq (by simp [hs])
    simp [rust_primitives.sequence.seq_len, this]
  | cons x xs ih =>
    intro s hs
    obtain ⟨s', e, hs'⟩ := Lib.seq_remove_head s x xs hs
    refine ⟨s', ?_, ih s' hs'⟩
    show next s = _
    rw [hnext]
    have : Slice.len s ≠ 0#usize := by
      intro h
      have := congrArg UScalar.val h
      simp [hs] at this
    simp [rust_primitives.sequence.seq_len, this, e]
    rfl

/-- An array's iterator yields its elements. -/
theorem array_into_iter_yields {T : Type} {N : Std.Usize} (a : Std.Array T N) :
    ∃ s, core.Array.Insts.CoreIterTraitsCollectIntoIteratorTIntoIter.into_iter a = .ok s ∧
      Yields (core.array.iter.IntoIter.Insts.CoreIterTraitsIteratorIterator T N) s a.val :=
  ⟨Std.Array.to_slice a, by
    simp [core.Array.Insts.CoreIterTraitsCollectIntoIteratorTIntoIter.into_iter,
      rust_primitives.sequence.seq_from_array],
    seq_next_yields _ (fun _ => rfl) a.val _ (by simp [Std.Array.to_slice])⟩

/-- A vector's iterator yields its elements. -/
theorem vec_into_iter_yields {T : Type} (v : alloc.vec.Vec T) :
    Yields (alloc.vec.into_iter.IntoIter.Insts.CoreIterTraitsIteratorIterator T) v v.val :=
  seq_next_yields _ (fun _ => rfl) v.val v rfl

end Plonky3Lean.Proofs.Symmetric
