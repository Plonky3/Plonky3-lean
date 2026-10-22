module

public import Aeneas

@[expose] public section

/-!
# `RustM`

Lemmas about Aeneas's `RustM` monad that are not specific to any crate.

`RustM α` is an interaction tree: a computation either returns (`ok`), performs a
visible effect such as failing (`vis`), or diverges (`div`). A spec `m ⦃ r => P r ⦄`
holds of none but the first, so it says that `m` returns some `v` with `P v`.
-/

open Aeneas Aeneas.Std

namespace Plonky3Lean.Lib

/-- A computation that meets a spec returns a value that satisfies it. -/
theorem spec_imp_exists {α : Type _} {m : RustM α} {P : α → Prop} (h : m ⦃ r => P r ⦄) :
    ∃ v, m = .ok v ∧ P v := by
  cases m with
  | ret r => exact ⟨r, rfl, (WP.spec_ok r).mp h⟩
  | vis i k => exact ((WP.spec_vis i k).mp h).elim
  | div => exact (WP.spec_div.mp h).elim

/-- A computation whose spec pins its value returns that value. -/
theorem eq_ok_of_spec {α : Type _} {m : RustM α} {v : α} (h : m ⦃ r => r = v ⦄) : m = .ok v := by
  obtain ⟨w, hw, rfl⟩ := spec_imp_exists h
  exact hw

/-- A `mapM` over a function that never fails never fails, and keeps the length. -/
theorem mapM_total {α β : Type} (f : α → RustM β) (hf : ∀ x, ∃ v, f x = .ok v)
    (l : List α) : ∃ l', l.mapM f = .ok l' ∧ l'.length = l.length := by
  induction l with
  | nil => exact ⟨[], rfl, rfl⟩
  | cons a l ih =>
    obtain ⟨v, hv⟩ := hf a
    obtain ⟨l', hl', hlen⟩ := ih
    refine ⟨v :: l', ?_, by simp [hlen]⟩
    simp only [List.mapM_cons, hv, hl', bind_tc_ok]
    rfl

/-- A `mapM` over a function with a pointwise spec never fails, and returns a
list related elementwise to its input by that spec. -/
theorem mapM_forall₂ {α β : Type} (f : α → RustM β) (P : α → β → Prop)
    (hf : ∀ x, f x ⦃ r => P x r ⦄) (l : List α) :
    ∃ l', l.mapM f = .ok l' ∧ List.Forall₂ P l l' := by
  induction l with
  | nil => exact ⟨[], rfl, .nil⟩
  | cons a l ih =>
    obtain ⟨v, hv, hp⟩ := spec_imp_exists (hf a)
    obtain ⟨l', hl', hall⟩ := ih
    refine ⟨v :: l', ?_, .cons hp hall⟩
    simp only [List.mapM_cons, hv, hl', bind_tc_ok]
    rfl

end Plonky3Lean.Lib
