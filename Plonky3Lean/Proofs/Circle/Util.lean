module

public import Mathlib.Data.List.Basic

@[expose] public section

/-!
# p3-circle: list lemmas the proofs share
-/

namespace Plonky3Lean.Proofs.Circle

/-- A monadic map that succeeds on every entry is the plain map. -/
theorem mapM_eq_some_map {α β : Type _} (l : List α) (f : α → Option β) (g : α → β)
    (h : ∀ a ∈ l, f a = some (g a)) : l.mapM f = some (l.map g) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.mapM_cons, h a (by simp), ih (fun a ha => h a (by simp [ha]))]
    rfl

end Plonky3Lean.Proofs.Circle
