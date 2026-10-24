module

public import Plonky3Lean.Lib.Slice

@[expose] public section

/-!
# What an iterator yields

An iterator yields a list from a state when its `next` returns the list's items in turn, then nothing.

A slice iterator yields the slice.

A zip yields the zip of what its two halves yield.

A map whose closure keeps its state yields the image of what it maps.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc

namespace Plonky3Lean.Lib

/-- The items an iterator returns from a state, up to the first time it returns nothing. -/
inductive Yields {I A : Type} (it : core.iter.traits.iterator.Iterator I A) : I → List A → Prop
  | nil {s s' : I} : it.next s = .ok (.None, s') → Yields it s []
  | cons {s s' : I} {x : A} {l : List A} :
      it.next s = .ok (.Some x, s') → Yields it s' l → Yields it s (x :: l)

/-- A slice iterator yields the slice's entries. -/
theorem yields_slice {T : Type} :
    ∀ (l : List T) (s : core.slice.iter.Iter T), Slice.val s = l →
      Yields (core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT T) s l
  | [], s, hs => .nil (s' := s) <| by
    simp [core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.next,
      rust_primitives.sequence.seq_len,
      UScalar.eq_of_val_eq (by simp [hs] : (Slice.len s).val = (0#usize).val)]
  | a :: rest, s, hs => by
    obtain ⟨s', e, hs'⟩ := seq_remove_head s a rest hs
    refine .cons ?_ (yields_slice rest s' hs')
    have hne : Slice.len s ≠ 0#usize := fun h0 => by simpa [hs] using congrArg UScalar.val h0
    simp [core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.next,
      rust_primitives.sequence.seq_len, hne, e]
    rfl

/-- A zip yields the pairs of what its halves yield, up to the shorter. -/
theorem yields_zip {I₁ I₂ A B : Type} {it₁ : core.iter.traits.iterator.Iterator I₁ A}
    {it₂ : core.iter.traits.iterator.Iterator I₂ B} {a : I₁} {l₁ : List A}
    (h₁ : Yields it₁ a l₁) :
    ∀ {b : I₂} {l₂ : List B}, Yields it₂ b l₂ →
      Yields (core.iter.adapters.zip.Zip.Insts.CoreIterTraitsIteratorIteratorPair it₁ it₂)
        { it1 := a, it2 := b } (l₁.zip l₂) := by
  induction h₁ with
  | nil e =>
    intro b l₂ _
    exact .nil (by simp [core.iter.adapters.zip.Zip.Insts.CoreIterTraitsIteratorIteratorPair.next, e]; rfl)
  | cons e _ ih =>
    intro b l₂ h₂
    cases h₂ with
    | nil e₂ =>
      exact .nil (by
        simp [core.iter.adapters.zip.Zip.Insts.CoreIterTraitsIteratorIteratorPair.next, e, e₂]; rfl)
    | cons e₂ h₂ =>
      exact .cons (by
        simp [core.iter.adapters.zip.Zip.Insts.CoreIterTraitsIteratorIteratorPair.next, e, e₂])
        (ih h₂)

/-- A map whose closure returns g x and keeps its state yields the image under g. -/
theorem yields_map {I A O F : Type} {it : core.iter.traits.iterator.Iterator I A}
    (inst : core.ops.function.FnMut F A O) (c : F) (g : A → O)
    (hg : ∀ x, inst.call_mut c x = .ok (g x, c)) {s : I} {l : List A} (h : Yields it s l) :
    Yields (core.iter.adapters.map.Map.Insts.CoreIterTraitsIteratorIterator it inst)
      { iter := s, f := c } (l.map g) := by
  induction h with
  | nil e =>
    exact .nil (by simp [core.iter.adapters.map.Map.Insts.CoreIterTraitsIteratorIterator.next, e]; rfl)
  | cons e _ ih =>
    exact .cons (by simp [core.iter.adapters.map.Map.Insts.CoreIterTraitsIteratorIterator.next, e, hg]) ih

end Plonky3Lean.Lib
