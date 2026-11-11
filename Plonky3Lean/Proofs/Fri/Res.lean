module

public import P3Fri.Verifier

@[expose] public section

/-!
# Reading the verifier's result monad

A verifier step returns a value, a rejection, or a panic.

An accepting run passed every step, so each step returned a value.
-/

namespace Plonky3Lean.Proofs.Fri

open p3_fri.verifier.mirror

variable {ME IE α β : Type}

@[simp] theorem lift_some_bind {ME IE α β : Type} (x : α) (f : α → Res ME IE β) :
    (ExceptT.lift (some x) >>= f : Res ME IE β) = f x := rfl

@[simp] theorem lift_none_bind {ME IE α β : Type} (f : α → Res ME IE β) :
    (ExceptT.lift none >>= f : Res ME IE β) = ExceptT.lift none := rfl

@[simp] theorem throw_bind' {ME IE α β : Type} (e : FriError ME IE) (f : α → Res ME IE β) :
    (throw e >>= f : Res ME IE β) = throw e := rfl

@[simp] theorem throw_ne_pure {ME IE α : Type} (e : FriError ME IE) (x : α) :
    (throw e : Res ME IE α) ≠ pure x := by
  change (some (Except.error e) : Option (Except _ α)) ≠ some (Except.ok x)
  simp

@[simp] theorem lift_none_ne_pure {ME IE α : Type} (x : α) :
    (ExceptT.lift none : Res ME IE α) ≠ pure x := by
  change (none : Option (Except (FriError ME IE) α)) ≠ some (Except.ok x)
  simp

theorem bind_eq_pure (m : Res ME IE α) (k : α → Res ME IE β) (b : β) :
    (m >>= k) = pure b ↔ ∃ a, m = pure a ∧ k a = pure b := by
  change Option (Except (FriError ME IE) α) at m
  rcases m with _ | (e | a)
  · simp only [bind, ExceptT.bind, ExceptT.mk, ExceptT.bindCont]
    constructor
    · intro h; cases h
    · rintro ⟨a, ha, -⟩; cases ha
  · simp only [bind, ExceptT.bind, ExceptT.mk, ExceptT.bindCont]
    constructor
    · intro h; cases h
    · rintro ⟨a, ha, -⟩; cases ha
  · constructor
    · intro h; exact ⟨a, rfl, h⟩
    · rintro ⟨a', ha, hk⟩
      have : a = a' := by
        have := congrArg (fun o : Option (Except (FriError ME IE) α) => o) ha
        exact Except.ok.inj (Option.some.inj this)
      subst this; exact hk

theorem foldlM_cons_eq_pure (f : β → α → Res ME IE β) (s : β) (x : α) (l : List α) (t : β) :
    (x :: l).foldlM f s = pure t ↔ ∃ s', f s x = pure s' ∧ l.foldlM f s' = pure t := by
  rw [List.foldlM_cons, bind_eq_pure]

theorem pure_inj {a b : α} (h : (pure a : Res ME IE α) = pure b) : a = b := by
  have := congrArg (fun o : Option (Except (FriError ME IE) α) => o) h
  exact Except.ok.inj (Option.some.inj this)

/-! ## Steps that never panic -/

/-- A step that returns a value or a rejection, never a panic. -/
def Total (m : Res ME IE α) : Prop := (show Option (Except (FriError ME IE) α) from m).isSome

theorem total_pure (a : α) : Total (pure a : Res ME IE α) := rfl

theorem total_throw (e : FriError ME IE) : Total (throw e : Res ME IE α) := rfl

theorem total_lift_some (a : α) : Total (ExceptT.lift (some a) : Res ME IE α) := rfl

theorem total_bind {m : Res ME IE α} {k : α → Res ME IE β} (hm : Total m)
    (hk : ∀ a, m = pure a → Total (k a)) : Total (m >>= k) := by
  change Option (Except (FriError ME IE) α) at m
  rcases m with _ | (e | a)
  · exact absurd hm (by simp [Total])
  · rfl
  · exact hk a rfl

theorem total_ite {c : Prop} [Decidable c] {a b : Res ME IE α} (ha : c → Total a) (hb : ¬ c → Total b) :
    Total (if c then a else b) := by
  split_ifs with h
  · exact ha h
  · exact hb h

theorem total_foldlM {f : β → α → Res ME IE β} (hf : ∀ s x, Total (f s x)) :
    ∀ (l : List α) (s : β), Total (l.foldlM f s)
  | [], s => total_pure s
  | x :: l, s => by
    rw [List.foldlM_cons]
    exact total_bind (hf s x) fun a _ => total_foldlM hf l a

theorem total_mapM {f : α → Res ME IE β} (hf : ∀ x, Total (f x)) : ∀ (l : List α), Total (l.mapM f)
  | [] => total_pure []
  | x :: l => by
    rw [List.mapM_cons]
    exact total_bind (hf x) fun a _ => total_bind (total_mapM hf l) fun b _ => total_pure _

theorem total_forM' {f : α → Res ME IE PUnit} : ∀ (l : List α), (∀ x ∈ l, Total (f x)) → Total (l.forM f)
  | [], _ => total_pure _
  | x :: l, hf => by
    show Total (f x >>= fun _ => l.forM f)
    exact total_bind (hf x List.mem_cons_self) fun _ _ =>
      total_forM' l fun y hy => hf y (List.mem_cons_of_mem _ hy)

theorem total_forM {f : α → Res ME IE PUnit} (hf : ∀ x, Total (f x)) : ∀ (l : List α), Total (l.forM f)
  | [] => total_pure _
  | x :: l => by
    show Total (f x >>= fun _ => l.forM f)
    exact total_bind (hf x) fun _ _ => total_forM hf l

end Plonky3Lean.Proofs.Fri
