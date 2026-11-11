module

public import Plonky3Lean.Spec.Bus
public import Mathlib.Data.List.Chain

@[expose] public section

/-!
# Memory consistency from a sorted trace

A list of accesses sorted strictly by cell, then by time, is consistent when two local rules hold:

- the first access, if a read, returns the initial value of its cell
- every later read returns the value of the access before it, if that access is on the same cell
- otherwise a later read returns the initial value.

Consistency only speaks of membership, so it passes to every permutation of the list.
-/

namespace Plonky3Lean.Proofs.Bus

open Plonky3Lean.Spec.Bus

variable {V : Type _}

/-- Strictly earlier in the order by cell, then by time. -/
def Before (x y : Access V) : Prop := x.addr < y.addr ∨ (x.addr = y.addr ∧ x.time < y.time)

theorem Before.trans {x y z : Access V} (h₁ : Before x y) (h₂ : Before y z) : Before x z := by
  unfold Before at *; omega

instance : Trans (@Before V) Before Before := ⟨Before.trans⟩

/-- The read rule between an access and the one after it. -/
def ReadStep (init : ℕ → V) (x y : Access V) : Prop :=
  y.write = false → y.value = if y.addr = x.addr then x.value else init y.addr

theorem timesDistinct_of_chain {accs : List (Access V)} (h : accs.IsChain Before) :
    TimesDistinct accs :=
  (List.isChain_iff_pairwise.1 h).imp fun hxy => by unfold Before at hxy; omega

/-- **Consistency of a sorted trace.**

A trace sorted strictly by cell then time, whose reads follow the read rule, is consistent. -/
theorem reads_of_sorted (init : ℕ → V) :
    ∀ (accs : List (Access V)), accs.IsChain Before →
      (∀ y ∈ accs.head?, y.write = false → y.value = init y.addr) →
      accs.IsChain (ReadStep init) → ReadsLastWrite init accs := by
  intro accs
  induction accs using List.reverseRecOn with
  | nil => intro _ _ _ y hy; simp at hy
  | append_singleton l y ih =>
    intro hs h0 hc
    have hpw := List.isChain_iff_pairwise.1 hs
    have hlt : ∀ z ∈ l, Before z y := fun z hz =>
      (List.pairwise_append.1 hpw).2.2 z hz y (List.mem_singleton_self y)
    have hl := ih (List.isChain_iff_pairwise.2 (List.pairwise_append.1 hpw).1)
      (fun z hz => h0 z (by cases l <;> simp_all)) (hc.infix ⟨[], [y], by simp⟩)
    intro z hz hzr
    rcases List.mem_append.1 hz with hz | hz
    · -- An earlier read keeps its witness: the new access is later on its cell.
      have hzy := hlt z hz
      unfold Before at hzy
      rcases hl z hz hzr with ⟨w, hw, h1, h2, h3, h4, h5⟩ | ⟨h1, h2⟩
      · refine Or.inl ⟨w, List.mem_append_left _ hw, h1, h2, h3, h4, fun w' hw' h1' h2' h3' => ?_⟩
        rcases List.mem_append.1 hw' with hw' | hw'
        · exact h5 w' hw' h1' h2' h3'
        · rw [List.mem_singleton.1 hw'] at h2' h3'; omega
      · refine Or.inr ⟨fun w hw h1' h2' => ?_, h2⟩
        rcases List.mem_append.1 hw with hw | hw
        · exact h1 w hw h1' h2'
        · rw [List.mem_singleton.1 hw] at h2' ⊢; omega
    · have hzy : z = y := List.mem_singleton.1 hz
      subst z
      -- Every write before the new read is a member of the list.
      have hy : ∀ w ∈ l ++ [y], w.write = true → w ∈ l := fun w hw hw' => by
        rcases List.mem_append.1 hw with hw | hw
        · exact hw
        · rw [List.mem_singleton.1 hw, hzr] at hw'; cases hw'
      rcases List.eq_nil_or_concat l with rfl | ⟨l', x, rfl⟩
      · exact Or.inr ⟨fun w hw hw' => absurd (hy w hw hw') List.not_mem_nil, h0 y (by simp) hzr⟩
      simp only [List.concat_eq_append] at *
      have hstep : ReadStep init x y := (List.isChain_append.1 hc).2.2 x (by simp) y (by simp)
      have hxy := hlt x (by simp)
      have hwx : ∀ w ∈ l' ++ [x], w = x ∨ Before w x := fun w hw => by
        rcases List.mem_append.1 hw with hw | hw
        · exact Or.inr ((List.pairwise_append.1 (List.pairwise_append.1 hpw).1).2.2 w hw x
            (by simp))
        · exact Or.inl (List.mem_singleton.1 hw)
      unfold ReadStep at hstep
      unfold Before at hxy
      by_cases hax : y.addr = x.addr
      · simp only [hax, ite_true] at hstep
        cases hxw : x.write
        · rcases hl x (by simp) hxw with ⟨w, hw, h1, h2, h3, h4, h5⟩ | ⟨h1, h2⟩
          · refine Or.inl ⟨w, List.mem_append_left _ hw, h1, by omega, by omega,
              by rw [h4, hstep hzr], fun w' hw' h1' h2' h3' => ?_⟩
            have hw'l := hy w' hw' h1'
            rcases hwx w' hw'l with rfl | hb
            · rw [hxw] at h1'; cases h1'
            · unfold Before at hb; exact h5 w' hw'l h1' (by omega) (by omega)
          · refine Or.inr ⟨fun w hw hw' ha => ?_, by rw [hstep hzr, h2, hax]⟩
            have hwl := hy w hw hw'
            rcases hwx w hwl with rfl | hb
            · rw [hxw] at hw'; cases hw'
            · have := h1 w hwl hw' (by omega); unfold Before at hb; omega
        · refine Or.inl ⟨x, by simp, hxw, hax.symm, by omega, (hstep hzr).symm,
            fun w' hw' h1' h2' h3' => ?_⟩
          rcases hwx w' (hy w' hw' h1') with rfl | hb
          · exact le_rfl
          · unfold Before at hb; omega
      · simp only [hax, ite_false] at hstep
        refine Or.inr ⟨fun w hw hw' ha => ?_, hstep hzr⟩
        rcases hwx w (hy w hw hw') with rfl | hb
        · exact absurd ha.symm hax
        · unfold Before at hb; omega

/-- A sorted trace that follows the read rule is a consistent memory. -/
theorem consistent_of_sorted (init : ℕ → V) {accs : List (Access V)} (hs : accs.IsChain Before)
    (h0 : ∀ y ∈ accs.head?, y.write = false → y.value = init y.addr)
    (hc : accs.IsChain (ReadStep init)) : Consistent init accs :=
  ⟨timesDistinct_of_chain hs, reads_of_sorted init accs hs h0 hc⟩

/-- Consistency passes to every permutation. -/
theorem Consistent.perm {init : ℕ → V} {l l' : List (Access V)} (h : l.Perm l')
    (hl : Consistent init l) : Consistent init l' := by
  refine ⟨h.pairwise hl.1 fun hxy hyx => (hxy hyx.symm).symm, fun y hy hr => ?_⟩
  simp only [← h.mem_iff] at hy ⊢
  exact hl.2 y hy hr

end Plonky3Lean.Proofs.Bus
