module

public import Mathlib.Data.List.Range
public import Mathlib.Algebra.Group.Defs

@[expose] public section

/-!
# In-place list updates

A descending loop that overwrites entry i from entries i - 1 and i reads only entries it has not yet written.
-/

namespace Plonky3Lean.Proofs.Stir

variable {α : Type _}

theorem getD_set_eq (l : List α) (i : ℕ) (a d : α) (j : ℕ) :
    (l.set i a).getD j d = if i = j ∧ i < l.length then a else l.getD j d := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_set]
  split_ifs <;> simp_all
  omega

@[simp] theorem length_foldl_set {β : Type _} (l : List α) (xs : List β) (idx : β → List α → ℕ)
    (val : β → List α → α) :
    (xs.foldl (fun cs b => cs.set (idx b cs) (val b cs)) l).length = l.length := by
  induction xs generalizing l with
  | nil => rfl
  | cons b xs ih => simp [List.foldl_cons, ih]

/-- Overwrite entries o, ..., o + m - 1 from the top down with g j (entry j - 1) (entry j).

This reads the original entries. -/
theorem foldl_desc_set (g : ℕ → α → α → α) (d : α) (o : ℕ) (ho : 0 < o) :
    ∀ (m : ℕ) (cs : List α), o + m ≤ cs.length → ∀ j,
      ((List.range m).reverse.foldl (fun cs i' =>
          cs.set (i' + o) (g (i' + o) (cs.getD (i' + o - 1) d) (cs.getD (i' + o) d))) cs).getD j d =
        if o ≤ j ∧ j < o + m then g j (cs.getD (j - 1) d) (cs.getD j d) else cs.getD j d := by
  intro m
  induction m with
  | zero => intro cs _ j; simp
  | succ m ih =>
    intro cs hcs j
    rw [List.range_succ, List.reverse_append, List.reverse_singleton, List.singleton_append,
      List.foldl_cons, ih _ (by simp; omega)]
    simp only [getD_set_eq]
    split_ifs <;> first | rfl | omega | (casesm* _ ∧ _; subst_vars; rfl)

/-- Updating every slot i < t once, ascending, from its own value. -/
theorem foldl_set_self {α : Type _} [Zero α] (f : ℕ → α → α) :
    ∀ (t : ℕ) (cs : List α), t ≤ cs.length → ∀ j,
      ((List.range t).foldl (fun cs i => cs.set i (f i (cs.getD i 0))) cs).getD j 0 =
        if j < t then f j (cs.getD j 0) else cs.getD j 0 := by
  intro t
  induction t with
  | zero => intro cs _ j; simp
  | succ t ih =>
    intro cs hcs j
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, getD_set_eq,
      length_foldl_set]
    simp only [ih cs (by omega)]
    split_ifs <;> first | omega | (casesm* _ ∧ _; subst_vars; rfl) | rfl

end Plonky3Lean.Proofs.Stir
