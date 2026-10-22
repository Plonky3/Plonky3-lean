import Aeneas
import CoreModels

/-!
# Iterators

A fold over a `usize` range, as `CoreModels` runs it.
-/

open Aeneas Aeneas.Std CoreModels

namespace Plonky3Lean.Lib

theorem range_next_lt (i K : Std.Usize) (h : i.val < K.val) :
    ∃ i' : Std.Usize, core.IteratorRange.next core.Usize.Insts.CoreIterRangeStep
      { start := i, «end» := K } =
      .ok (core.option.Option.Some i, { start := i', «end» := K }) ∧ i'.val = i.val + 1 := by
  unfold core.IteratorRange.next
  simp [core.Usize.Insts.CoreCmpPartialOrdUsize, core.mkUPartialOrd, compare_lt_iff_lt.mpr h,
    core.Usize.Insts.CoreCloneClone.clone, core.Usize.Insts.CoreIterRangeStep.forward_checked,
    core.convert.TryFromUTInfallible.Blanket.try_from, core.convert.From.Blanket.from,
    core.num.Usize.checked_add]
  have hK := K.hBounds
  have e := UScalar.overflowing_add_eq i 1#usize
  have hmax : ¬ i.val + (1#usize : Std.Usize).val > UScalar.max .Usize := by
    simp only [UScalar.max] at hK ⊢
    have : (1#usize : Std.Usize).val = 1 := rfl
    omega
  rw [if_neg hmax] at e
  obtain ⟨e1, e2⟩ := e
  refine ⟨(UScalar.overflowing_add i 1#usize).1, ?_, by rw [e1]; rfl⟩
  simp only [CoreModels.core.num.Usize.overflowing_add,
    CoreModels.rust_primitives.arithmetic.overflowing_add_usize, bind_tc_ok]
  rw [show UScalar.overflowing_add i 1#usize = ((UScalar.overflowing_add i 1#usize).1, false) from
    Prod.ext rfl e2]
  rfl

theorem range_next_ge (i K : Std.Usize) (h : K.val ≤ i.val) :
    core.IteratorRange.next core.Usize.Insts.CoreIterRangeStep { start := i, «end» := K } =
      .ok (core.option.Option.None, { start := i, «end» := K }) := by
  unfold core.IteratorRange.next
  rcases Nat.lt_or_ge K.val i.val with h1 | h1
  · simp [core.Usize.Insts.CoreCmpPartialOrdUsize, core.mkUPartialOrd, compare_gt_iff_gt.mpr h1]
  · simp [core.Usize.Insts.CoreCmpPartialOrdUsize, core.mkUPartialOrd,
      compare_eq_iff_eq.mpr (show i.val = K.val by omega)]

/-- Folding a step that always succeeds over `start..end` iterates it `end - start` times. -/
theorem iter_fold_loop_range {B F : Type} (inst : CoreModels.core.ops.function.FnMut F (B × Std.Usize) B)
    (f : F) (g : B → B) (hstep : ∀ b i, inst.call_mut f (b, i) = .ok (g b, f)) :
    ∀ (n : ℕ) (i K : Std.Usize) (x : B), K.val - i.val = n →
      core.iter.traits.iterator.iter_fold_loop
        (core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator
          core.Usize.Insts.CoreIterRangeStep) inst { start := i, «end» := K } f x =
        .ok (g^[n] x) := by
  intro n
  induction n with
  | zero =>
    intro i K x hn
    unfold core.iter.traits.iterator.iter_fold_loop
    rw [loop]
    simp [core.iter.traits.iterator.iter_fold_loop.body,
      core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator, range_next_ge i K (by omega)]
  | succ n ih =>
    intro i K x hn
    obtain ⟨i', e, hi'⟩ := range_next_lt i K (by omega)
    unfold core.iter.traits.iterator.iter_fold_loop
    rw [loop]
    simp [core.iter.traits.iterator.iter_fold_loop.body,
      core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator, e, hstep]
    exact ih i' K (g x) (by omega)

end Plonky3Lean.Lib
