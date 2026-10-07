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

end Plonky3Lean.Lib
