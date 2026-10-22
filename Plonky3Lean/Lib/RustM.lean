import Aeneas

/-!
# `RustM`

Lemmas about Aeneas's `RustM` monad that are not specific to any crate.
-/

open Aeneas Aeneas.Std

namespace Plonky3Lean.Lib

/-- A `mapM` over a function that never fails never fails, and keeps the length. -/
theorem mapM_total {α β : Type} (f : α → RustM β) (hf : ∀ x, ∃ v, f x = .ok v)
    (l : List α) : ∃ l', l.mapM f = .ok l' ∧ l'.length = l.length := by
  induction l with
  | nil => exact ⟨[], rfl, rfl⟩
  | cons a l ih =>
    obtain ⟨v, hv⟩ := hf a
    obtain ⟨l', hl', hlen⟩ := ih
    refine ⟨v :: l', ?_, by simp [hlen]⟩
    simp [List.mapM_cons, hv, hl']
    rfl

/-- A `mapM` over a function with a pointwise spec never fails, and returns a
list related elementwise to its input by that spec. -/
theorem mapM_forall₂ {α β : Type} (f : α → RustM β) (P : α → β → Prop)
    (hf : ∀ x, f x ⦃ r => P x r ⦄) (l : List α) :
    ∃ l', l.mapM f = .ok l' ∧ List.Forall₂ P l l' := by
  induction l with
  | nil => exact ⟨[], rfl, .nil⟩
  | cons a l ih =>
    obtain ⟨v, hv, hp⟩ := Aeneas.Std.WP.spec_imp_exists (hf a)
    obtain ⟨l', hl', hall⟩ := ih
    refine ⟨v :: l', ?_, .cons hp hall⟩
    simp [List.mapM_cons, hv, hl']
    rfl

end Plonky3Lean.Lib
