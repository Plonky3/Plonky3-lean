module

public import Aeneas
public import CoreModels

@[expose] public section

/-!
# Iterators

A fold over a `usize` range, and a map over an array, as `CoreModels` runs them.
-/

open Aeneas Aeneas.Std CoreModels Std.Do

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
  rw [ite_eq_right hmax] at e
  obtain ⟨e1, e2⟩ := e
  refine ⟨(UScalar.overflowing_add i 1#usize).1, ?_, by rw [e1]; rfl⟩
  simp only [CoreModels.core.num.Usize.overflowing_add,
    CoreModels.rust_primitives.arithmetic.overflowing_add_usize, Aeneas.Std.bind_ok]
  rw [show UScalar.overflowing_add i 1#usize = ((UScalar.overflowing_add i 1#usize).1, false) from
    Prod.ext rfl e2]
  dsimp only
  simp

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

/-- `array_map` with a closure that returns `g x` and keeps its state maps `g` over the array. -/
theorem array_map_eq {T U F : Type} {N : Std.Usize} (inst : CoreModels.core.ops.function.FnMut F T U)
    (a : Std.Array T N) (f : F) (g : T → U) (hg : ∀ x, inst.call_mut f x = .ok (g x, f)) :
    CoreModels.rust_primitives.slice.array_map inst a f =
      .ok (Std.Array.from (a.val.map g) (by simp)) := by
  have hpure : ∀ x ∈ a.val, ⦃ ⌜ True ⌝ ⦄ inst.call_mut f x ⦃ ⇓ r => ⌜ r.2 = f ⌝ ⦄ :=
    fun x _ => Aeneas.Std.triple_iff_exists_ok.2 ⟨_, hg x, rfl⟩
  obtain ⟨b, hb, hall⟩ := Aeneas.Std.triple_iff_exists_ok.1
    (CoreModels.rust_primitives.slice.array_map_spec inst a f hpure)
  rw [hb]
  congr 1
  apply Std.Array.ext
  rw [Std.Array.from_val]
  apply List.ext_getElem (by simp)
  intro i h1 h2
  obtain ⟨y, hy, hy1⟩ := Aeneas.Std.triple_iff_exists_ok.1 (hall i (by simpa using h1))
  rw [hg] at hy
  have hy' := RustM.ok_injective hy
  subst hy'
  simp only [List.getElem_map] at hy1 ⊢
  exact hy1.symm

end Plonky3Lean.Lib
