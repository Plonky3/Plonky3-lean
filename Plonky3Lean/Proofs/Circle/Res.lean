module

public import Mathlib.Data.List.Basic
public import Mathlib.Order.Basic

@[expose] public section

/-!
# p3-circle: steps that never panic

A verifier step returns a value, a rejection, or a panic.

A step is total when it never panics.

These lemmas show totality one bind at a time.
-/

namespace Plonky3Lean.Proofs.Circle

variable {ε ε' α β : Type _}

/-- A step that returns a value or a rejection, never a panic. -/
def Total (m : ExceptT ε Option α) : Prop := (ExceptT.run m).isSome

theorem total_pure (a : α) : Total (pure a : ExceptT ε Option α) := rfl

theorem total_throw (e : ε) : Total (throw e : ExceptT ε Option α) := rfl

theorem total_lift_some (a : α) : Total (ExceptT.lift (some a) : ExceptT ε Option α) := rfl

theorem not_total_lift_none : ¬ Total (ExceptT.lift none : ExceptT ε Option α) := by
  simp [Total, ExceptT.run, ExceptT.lift, ExceptT.mk]

@[simp] theorem lift_some_bind' (x : α) (f : α → ExceptT ε Option β) :
    (ExceptT.lift (some x) >>= f : ExceptT ε Option β) = f x := rfl

@[simp] theorem lift_none_bind' (f : α → ExceptT ε Option β) :
    (ExceptT.lift none >>= f : ExceptT ε Option β) = ExceptT.lift none := rfl

@[simp] theorem throw_bind'' (e : ε) (f : α → ExceptT ε Option β) :
    (throw e >>= f : ExceptT ε Option β) = throw e := rfl

theorem pure_inj' {a b : α} (h : (pure a : ExceptT ε Option α) = pure b) : a = b := by
  have := congrArg ExceptT.run h
  exact Except.ok.inj (Option.some.inj this)

@[simp] theorem throw_ne_pure' (e : ε) (a : α) : (throw e : ExceptT ε Option α) ≠ pure a := by
  intro h; cases h

@[simp] theorem lift_none_ne_pure' (a : α) : (ExceptT.lift none : ExceptT ε Option α) ≠ pure a := by
  intro h; cases h

theorem bind_eq_pure' (m : ExceptT ε Option α) (k : α → ExceptT ε Option β) (b : β) :
    (m >>= k) = pure b ↔ ∃ a, m = pure a ∧ k a = pure b := by
  rcases m with _ | (e | a)
  · constructor
    · intro h; cases h
    · rintro ⟨a, ha, -⟩; cases ha
  · constructor
    · intro h; cases h
    · rintro ⟨a, ha, -⟩; cases ha
  · constructor
    · intro h; exact ⟨a, rfl, h⟩
    · rintro ⟨a', ha, hk⟩
      cases pure_inj' (ε := ε) ha; exact hk

theorem ite_throw_eq_pure {c : Prop} [Decidable c] {e : ε} {m : ExceptT ε Option α} {a : α} :
    (if c then throw e else m) = pure a ↔ ¬ c ∧ m = pure a := by
  split_ifs with h <;> simp [h]

theorem ite_lift_none_eq_pure {c : Prop} [Decidable c] {m : ExceptT ε Option α} {a : α} :
    (if c then ExceptT.lift none else m) = pure a ↔ ¬ c ∧ m = pure a := by
  split_ifs with h <;> simp [h]

theorem total_bind {m : ExceptT ε Option α} {k : α → ExceptT ε Option β} (hm : Total m)
    (hk : ∀ a, m = pure a → Total (k a)) : Total (m >>= k) := by
  rcases m with _ | (e | a)
  · exact absurd hm (by simp [Total, ExceptT.run])
  · rfl
  · exact hk a rfl

/-- A bind panics exactly when its first step panics, or its first step returns a value and the rest panics. -/
theorem total_bind_iff {m : ExceptT ε Option α} {k : α → ExceptT ε Option β} :
    Total (m >>= k) ↔ Total m ∧ ∀ a, m = pure a → Total (k a) := by
  refine ⟨fun h => ?_, fun h => total_bind h.1 h.2⟩
  rcases m with _ | (e | a)
  · exact absurd h (by simp [Total, ExceptT.run]; rfl)
  · exact ⟨rfl, fun a ha => by cases ha⟩
  · exact ⟨rfl, fun a' ha => by cases pure_inj' (ε := ε) ha; exact h⟩

theorem total_ite {c : Prop} [Decidable c] {a b : ExceptT ε Option α} (ha : c → Total a)
    (hb : ¬ c → Total b) : Total (if c then a else b) := by
  split_ifs with h
  · exact ha h
  · exact hb h

theorem total_foldlM {f : β → α → ExceptT ε Option β} :
    ∀ (l : List α) (s : β), (∀ s, ∀ x ∈ l, Total (f s x)) → Total (l.foldlM f s)
  | [], s, _ => total_pure s
  | x :: l, s, hf => by
    rw [List.foldlM_cons]
    exact total_bind (hf s x List.mem_cons_self) fun a _ =>
      total_foldlM l a fun s y hy => hf s y (List.mem_cons_of_mem _ hy)

theorem total_mapM {f : α → ExceptT ε Option β} : ∀ (l : List α), (∀ x ∈ l, Total (f x)) → Total (l.mapM f)
  | [], _ => total_pure []
  | x :: l, hf => by
    rw [List.mapM_cons]
    exact total_bind (hf x List.mem_cons_self) fun a _ =>
      total_bind (total_mapM l fun y hy => hf y (List.mem_cons_of_mem _ hy)) fun b _ => total_pure _

theorem total_forM {f : α → ExceptT ε Option PUnit} :
    ∀ (l : List α), (∀ x ∈ l, Total (f x)) → Total (l.forM f)
  | [], _ => total_pure _
  | x :: l, hf => by
    show Total (f x >>= fun _ => l.forM f)
    exact total_bind (hf x List.mem_cons_self) fun _ _ =>
      total_forM l fun y hy => hf y (List.mem_cons_of_mem _ hy)

theorem total_lift {o : Option α} (h : o.isSome) : Total (ExceptT.lift o : ExceptT ε Option α) := by
  obtain ⟨a, rfl⟩ := Option.isSome_iff_exists.mp h; rfl

/-- A monadic map that returns a value returns one entry per input entry. -/
theorem mapM_eq_pure_length {f : α → ExceptT ε Option β} :
    ∀ {l : List α} {r : List β}, l.mapM f = pure r → r.length = l.length
  | [], r, h => by
    rw [List.mapM_nil] at h; cases pure_inj' (ε := ε) h; rfl
  | x :: l, r, h => by
    rw [List.mapM_cons, bind_eq_pure'] at h
    obtain ⟨b, -, h⟩ := h
    rw [bind_eq_pure'] at h
    obtain ⟨bs, hbs, h⟩ := h
    cases pure_inj' (ε := ε) h
    simp [mapM_eq_pure_length hbs]

/-- Every entry of a returned monadic map is the value of some input entry. -/
theorem mapM_eq_pure_mem {f : α → ExceptT ε Option β} :
    ∀ {l : List α} {r : List β}, l.mapM f = pure r → ∀ b ∈ r, ∃ a ∈ l, f a = pure b
  | [], r, h, b, hb => by
    rw [List.mapM_nil] at h; cases pure_inj' (ε := ε) h; simp at hb
  | x :: l, r, h, b, hb => by
    rw [List.mapM_cons, bind_eq_pure'] at h
    obtain ⟨c, hc, h⟩ := h
    rw [bind_eq_pure'] at h
    obtain ⟨bs, hbs, h⟩ := h
    cases pure_inj' (ε := ε) h
    rcases List.mem_cons.mp hb with rfl | hb
    · exact ⟨x, List.mem_cons_self, hc⟩
    · obtain ⟨a, ha, hfa⟩ := mapM_eq_pure_mem hbs b hb
      exact ⟨a, List.mem_cons_of_mem _ ha, hfa⟩

/-- An invariant every returning step keeps holds at the end of a returning fold. -/
theorem foldlM_invariant {f : β → α → ExceptT ε Option β} {P : β → Prop} :
    ∀ {l : List α} {s t : β}, (∀ s x s', x ∈ l → f s x = pure s' → P s → P s') →
      l.foldlM f s = pure t → P s → P t
  | [], s, t, _, h, hs => by
    rw [List.foldlM_nil] at h; cases pure_inj' (ε := ε) h; exact hs
  | x :: l, s, t, hf, h, hs => by
    rw [List.foldlM_cons, bind_eq_pure'] at h
    obtain ⟨s', hs', h⟩ := h
    exact foldlM_invariant (fun s y s'' hy => hf s y s'' (List.mem_cons_of_mem _ hy)) h
      (hf s x s' List.mem_cons_self hs' hs)

/-- A monadic loop that returns has every step return. -/
theorem forM_eq_pure {f : α → ExceptT ε Option PUnit} :
    ∀ {l : List α} {u : PUnit}, l.forM f = pure u → ∀ x ∈ l, f x = pure PUnit.unit
  | [], _, _, x, hx => by simp at hx
  | y :: l, u, h, x, hx => by
    change (f y >>= fun _ => l.forM f) = pure u at h
    rw [bind_eq_pure'] at h
    obtain ⟨⟨⟩, hy, h⟩ := h
    rcases List.mem_cons.mp hx with rfl | hx
    · exact hy
    · exact forM_eq_pure h x hx

end Plonky3Lean.Proofs.Circle
