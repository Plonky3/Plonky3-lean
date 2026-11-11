module

public import Plonky3Lean.Proofs.BatchStark.Layout

@[expose] public section

/-!
# One payload width per bus

p3-lookup's width check reads every tuple of every global lookup, grouped by bus name.

It rejects a batch exactly when two tuples on one bus differ in width.

The challenge layout asks more: every lookup has one width, and global lookups naming one bus share it.

A lookup with no tuple still takes width 0 in the layout.

So the two differ on a bus that carries a lookup without tuples beside a wider tuple:

```text
    instance 0   exclusive group with no branch    width check: nothing
    instance 1   one send of width 2               layout:      0 and 2 differ, panic
```
-/

set_option linter.unusedSectionVars false

namespace Plonky3Lean.Proofs.BatchStark

open p3_lookup.mirror p3_air.symbolic.mirror p3_batch_stark.transcript.mirror

variable {F : Type}

/-- Every tuple on one bus has one width: global lookups naming one bus, all their tuples. -/
def BusWidthsOk (Q : List (Lookup F)) : Prop :=
  ∀ c ∈ Q, ∀ d ∈ Q, ∀ n, c.kind = .Global n → d.kind = .Global n →
    ∀ e ∈ c.elements, ∀ e' ∈ d.elements, e.length = e'.length

/-! ## The widths a bus carries -/

theorem mem_widths_new (buses : List (String × List ℕ)) (bus n : String) (widths : List ℕ) (w : ℕ) :
    (∃ ws, (n, ws) ∈ buses ++ [(bus, widths)] ∧ w ∈ ws) ↔
      (∃ ws, (n, ws) ∈ buses ∧ w ∈ ws) ∨ (bus = n ∧ w ∈ widths) := by
  simp only [List.mem_append, List.mem_singleton, Prod.mk.injEq]
  constructor
  · rintro ⟨ws, hm | ⟨rfl, rfl⟩, hw⟩
    exacts [Or.inl ⟨ws, hm, hw⟩, Or.inr ⟨rfl, hw⟩]
  · rintro (⟨ws, hm, hw⟩ | ⟨rfl, hw⟩)
    exacts [⟨ws, Or.inl hm, hw⟩, ⟨widths, Or.inr ⟨rfl, rfl⟩, hw⟩]

theorem mem_widths_any (buses : List (String × List ℕ)) (bus n : String) (widths : List ℕ) (w : ℕ)
    (hany : (buses.any fun x => decide (x.1 = bus)) = true) :
    (∃ ws, (n, ws) ∈ buses.map (fun b => if b.1 = bus then (b.1, b.2 ++ widths) else b) ∧ w ∈ ws) ↔
      (∃ ws, (n, ws) ∈ buses ∧ w ∈ ws) ∨ (bus = n ∧ w ∈ widths) := by
  constructor
  · rintro ⟨ws, hm, hw⟩
    obtain ⟨⟨n', ws'⟩, hb, he⟩ := List.mem_map.1 hm
    by_cases h : n' = bus
    · simp only [h, ite_true, Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      rcases List.mem_append.1 hw with hw | hw
      exacts [Or.inl ⟨_, h ▸ hb, hw⟩, Or.inr ⟨h.symm ▸ rfl, hw⟩]
    · simp only [h, ite_false, Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      exact Or.inl ⟨_, hb, hw⟩
  · rintro (⟨ws, hm, hw⟩ | ⟨rfl, hw⟩)
    · refine ⟨if n = bus then ws ++ widths else ws, List.mem_map.2 ⟨(n, ws), hm, by split_ifs <;> rfl⟩, ?_⟩
      split_ifs <;> simp [hw]
    · obtain ⟨⟨b, ws⟩, hb, hbn⟩ := List.any_eq_true.1 hany
      simp only [decide_eq_true_eq] at hbn
      subst hbn
      exact ⟨ws ++ widths, List.mem_map.2 ⟨(b, ws), hb, by simp⟩, List.mem_append_right _ hw⟩

/-- A width lies under a bus name exactly when some global lookup of that name has a tuple of that width. -/
theorem mem_bus_widths (air : List (Lookup F)) (n : String) (w : ℕ) :
    (∃ ws, (n, ws) ∈ bus_widths air ∧ w ∈ ws) ↔
      ∃ c ∈ air, c.kind = .Global n ∧ ∃ e ∈ c.elements, e.length = w := by
  suffices h : ∀ buses : List (String × List ℕ),
      (∃ ws, (n, ws) ∈ air.foldl (fun buses l =>
        match l.kind with
        | .Local => buses
        | .Global bus =>
          let widths := l.elements.map List.length
          if buses.any (·.1 = bus) then
            buses.map fun b => if b.1 = bus then (b.1, b.2 ++ widths) else b
          else buses ++ [(bus, widths)]) buses ∧ w ∈ ws) ↔
        (∃ ws, (n, ws) ∈ buses ∧ w ∈ ws) ∨ ∃ c ∈ air, c.kind = .Global n ∧ ∃ e ∈ c.elements, e.length = w by
    have := h []
    simp only [List.not_mem_nil, false_and, exists_false, false_or] at this
    exact this
  induction air with
  | nil => simp
  | cons c air ih =>
    intro buses
    rw [List.foldl_cons, ih]
    rcases hk : c.kind with _ | bus
    · simp [hk]
    · dsimp only
      split_ifs with hany <;>
        (first | rw [mem_widths_any _ _ _ _ _ hany] | rw [mem_widths_new]) <;>
        simp only [List.mem_cons, exists_eq_or_imp, hk, Kind.Global.injEq, List.mem_map] <;>
        exact or_assoc

/-! ## The width check -/

/-- One step of the width check: record a bus's first width, and compare each later width with it. -/
def widthStep (st : List (String × ℕ) × ℕ) (p : String × ℕ) :
    Except (String × ℕ × ℕ) (List (String × ℕ) × ℕ) :=
  match st.1.find? (·.1 = p.1) with
  | some (_, expected) => if expected ≠ p.2 then throw (p.1, expected, p.2) else pure (st.1, max st.2 p.2)
  | none => pure (st.1 ++ [p], max st.2 p.2)

/-- Every (bus, width) pair the check visits, in order. -/
def busWidthPairs (all : List (List (Lookup F))) : List (String × ℕ) :=
  all.flatMap fun air => (bus_widths air).flatMap fun b => b.2.map (b.1, ·)

theorem foldlM_flatMap {α β γ ε : Type} (l : List α) (g : α → List β) (f : γ → β → Except ε γ)
    (b : γ) : (l.flatMap g).foldlM f b = l.foldlM (fun b x => (g x).foldlM f b) b := by
  induction l generalizing b with
  | nil => rfl
  | cons x l ih =>
    simp only [List.flatMap_cons, List.foldlM_append, List.foldlM_cons]
    cases (g x).foldlM f b <;> simp [ih, bind, Except.bind]

/-- The check is one pass of the step over the visited pairs. -/
theorem check_bus_widths_eq (all : List (List (Lookup F))) :
    check_bus_widths all = ((busWidthPairs all).foldlM widthStep ([], 0)).map (·.2) := by
  simp only [check_bus_widths, busWidthPairs, foldlM_flatMap, List.foldlM_map]
  have hmap : ∀ x : Except (String × ℕ × ℕ) (List (String × ℕ) × ℕ),
      (x >>= fun r => pure r.2) = x.map (·.2) := fun x => by cases x <;> rfl
  exact hmap _

/-- Keys pairwise distinct. -/
def KeysDistinct (m : List (String × ℕ)) : Prop := m.Pairwise fun a b => a.1 ≠ b.1

/-- Pairs agree when they share a key. -/
def Agree (S T : List (String × ℕ)) : Prop := ∀ p ∈ S, ∀ q ∈ T, p.1 = q.1 → p.2 = q.2

theorem find?_key {m : List (String × ℕ)} (hm : KeysDistinct m) {q : String × ℕ} (hq : q ∈ m) :
    m.find? (·.1 = q.1) = some q := by
  induction m with
  | nil => simp at hq
  | cons a m ih =>
    rw [KeysDistinct, List.pairwise_cons] at hm
    rcases List.mem_cons.1 hq with rfl | hq
    · simp
    · have ha : a.1 ≠ q.1 := hm.1 q hq
      simp [ha, ih hm.2 hq]

/-- **The pass succeeds** exactly when the pairs agree with the recorded widths and among themselves. -/
theorem foldlM_widthStep_ok (S : List (String × ℕ)) (m : List (String × ℕ)) (hm : KeysDistinct m)
    (x : ℕ) :
    (∃ r, S.foldlM widthStep (m, x) = .ok r) ↔ Agree S m ∧ Agree S S := by
  induction S generalizing m x with
  | nil => simp [Agree, pure, Except.pure]
  | cons p S ih =>
    rw [List.foldlM_cons]
    rcases hf : m.find? (·.1 = p.1) with _ | ⟨n, e⟩
    · -- A new bus: its width is recorded.
      have hnew : ∀ q ∈ m, q.1 ≠ p.1 := fun q hq h => by
        have := find?_key hm hq; rw [h, hf] at this; cases this
      have hm' : KeysDistinct (m ++ [p]) :=
        List.pairwise_append.2 ⟨hm, List.pairwise_singleton _ _, fun a ha b hb => by
          rw [List.mem_singleton] at hb; subst hb; exact hnew a ha⟩
      simp only [widthStep, hf, pure, Except.pure, bind, Except.bind]
      rw [ih _ hm']
      simp only [Agree, List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
      constructor
      · rintro ⟨h1, h2⟩
        refine ⟨fun a ha q hq hk => ?_, fun a ha b hb hk => ?_⟩
        · rcases ha with rfl | ha
          · exact absurd hk.symm (hnew q hq)
          · exact h1 a ha q (Or.inl hq) hk
        · rcases ha with rfl | ha <;> rcases hb with rfl | hb
          · rfl
          · exact (h1 b hb a (Or.inr rfl) hk.symm).symm
          · exact h1 a ha b (Or.inr rfl) hk
          · exact h2 a ha b hb hk
      · rintro ⟨h1, h2⟩
        refine ⟨fun a ha q hq hk => ?_, fun a ha b hb hk => h2 a (Or.inr ha) b (Or.inr hb) hk⟩
        rcases hq with hq | rfl
        · exact h1 a (Or.inr ha) q hq hk
        · exact h2 a (Or.inr ha) q (Or.inl rfl) hk
    · -- A known bus: its width must equal the recorded one.
      have hmem : (n, e) ∈ m := List.mem_of_find?_eq_some hf
      have hkey : n = p.1 := by simpa using List.find?_some hf
      by_cases he : e = p.2
      · simp only [widthStep, hf, he, ne_eq, not_true_eq_false, ite_false, pure, Except.pure, bind,
          Except.bind]
        rw [ih _ hm]
        simp only [Agree, List.mem_cons]
        constructor
        · rintro ⟨h1, h2⟩
          have hp : ∀ q ∈ m, p.1 = q.1 → p.2 = q.2 := fun q hq hk => by
            have h1' := find?_key hm hq
            rw [← hk, hf, Option.some.injEq] at h1'
            rw [← h1', ← he]
          refine ⟨fun a ha q hq hk => ?_, fun a ha b hb hk => ?_⟩
          · rcases ha with rfl | ha; exacts [hp q hq hk, h1 a ha q hq hk]
          · rcases ha with rfl | ha <;> rcases hb with rfl | hb
            · rfl
            · rw [he.symm.trans (h1 b hb _ hmem (hk.symm.trans hkey.symm)).symm]
            · rw [h1 a ha _ hmem (hk.trans hkey.symm), he]
            · exact h2 a ha b hb hk
        · rintro ⟨h1, h2⟩
          exact ⟨fun a ha q hq hk => h1 a (Or.inr ha) q hq hk,
            fun a ha b hb hk => h2 a (Or.inr ha) b (Or.inr hb) hk⟩
      · simp only [widthStep, hf, ne_eq, he, not_false_eq_true, ite_true, throw, throwThe,
          MonadExceptOf.throw, bind, Except.bind]
        simp only [reduceCtorEq, exists_false, false_iff, not_and]
        intro h1
        exact absurd (h1 p List.mem_cons_self _ hmem hkey.symm).symm he

theorem mem_busWidthPairs (all : List (List (Lookup F))) (p : String × ℕ) :
    p ∈ busWidthPairs all ↔
      ∃ c ∈ all.flatten, c.kind = .Global p.1 ∧ ∃ e ∈ c.elements, e.length = p.2 := by
  have h : p ∈ busWidthPairs all ↔ ∃ air ∈ all, ∃ ws, (p.1, ws) ∈ bus_widths air ∧ p.2 ∈ ws := by
    simp only [busWidthPairs, List.mem_flatMap, List.mem_map]
    constructor
    · rintro ⟨air, hair, ⟨n, ws⟩, hb, w, hw, rfl⟩
      exact ⟨air, hair, ws, hb, hw⟩
    · rintro ⟨air, hair, ws, hb, hw⟩
      exact ⟨air, hair, (p.1, ws), hb, p.2, hw, rfl⟩
  rw [h]
  simp only [mem_bus_widths, List.mem_flatten]
  constructor
  · rintro ⟨air, hair, c, hc, hk⟩; exact ⟨c, ⟨air, hair, hc⟩, hk⟩
  · rintro ⟨c, ⟨air, hair, hc⟩, hk⟩; exact ⟨air, hair, c, hc, hk⟩

/-- **The width check** passes exactly when every tuple on one bus has one width. -/
theorem check_bus_widths_ok_iff (all : List (List (Lookup F))) :
    (∃ w, check_bus_widths all = .ok w) ↔ BusWidthsOk all.flatten := by
  have hok : (∃ w, check_bus_widths all = .ok w) ↔
      ∃ r, (busWidthPairs all).foldlM widthStep ([], 0) = .ok r := by
    rw [check_bus_widths_eq]
    constructor
    · rintro ⟨w, hw⟩
      rcases h : (busWidthPairs all).foldlM widthStep ([], 0) with e | r
      · rw [h] at hw; cases hw
      · exact ⟨r, rfl⟩
    · rintro ⟨r, hr⟩; exact ⟨r.2, by rw [hr]; rfl⟩
  rw [hok, foldlM_widthStep_ok _ _ List.Pairwise.nil]
  simp only [Agree, List.not_mem_nil, false_imp_iff, imp_true_iff, true_and, mem_busWidthPairs]
  constructor
  · intro h c hc d hd n hcn hdn e he e' he'
    exact h (n, e.length) ⟨c, hc, hcn, e, he, rfl⟩ (n, e'.length) ⟨d, hd, hdn, e', he', rfl⟩ rfl
  · rintro h ⟨n, w⟩ ⟨c, hc, hcn, e, he, rfl⟩ ⟨n', w'⟩ ⟨d, hd, hdn, e', he', rfl⟩ (rfl : n = n')
    exact h c hc d hd n hcn hdn e he e' he'

/-! ## The width check against the layout -/

theorem width_eq {c : Lookup F} {w : ℕ} (h : width c = some w) : ∀ e ∈ c.elements, e.length = w := by
  intro e he
  unfold width assert_uniform_tuple_width assert_uniform_widths at h
  rcases hl : c.elements with _ | ⟨e₀, rest⟩
  · simp [hl] at he
  · simp only [hl, List.map_cons] at h
    split_ifs at h with hall
    · cases h
      rw [hl, List.mem_cons] at he
      rcases he with rfl | he
      · rfl
      · simpa using List.all_eq_true.1 hall _ (List.mem_map_of_mem he)

/-- **The width check rejects nothing the layout accepts.** -/
theorem busWidthsOk_of_widthsOk {Q : List (Lookup F)} (h : WidthsOk Q) : BusWidthsOk Q := by
  intro c hc d hd n hcn hdn e he e' he'
  obtain ⟨w, hw⟩ := Option.isSome_iff_exists.1 (h.1 c hc)
  have hd' := h.2 c hc d hd n hcn hdn
  rw [hw] at hd'
  rw [width_eq hw e he, width_eq hd'.symm e' he']

/-- **The layout accepts what the width check accepts**, with two more conditions:

- every lookup's own tuples have one width
- every global lookup has a tuple. -/
theorem widthsOk_of_busWidthsOk {Q : List (Lookup F)} (h : BusWidthsOk Q)
    (hu : ∀ c ∈ Q, (width c).isSome) (hne : ∀ c ∈ Q, ∀ n, c.kind = .Global n → c.elements ≠ []) :
    WidthsOk Q := by
  refine ⟨hu, fun c hc d hd n hcn hdn => ?_⟩
  obtain ⟨w, hw⟩ := Option.isSome_iff_exists.1 (hu c hc)
  obtain ⟨w', hw'⟩ := Option.isSome_iff_exists.1 (hu d hd)
  obtain ⟨e, he⟩ := List.exists_mem_of_ne_nil _ (hne c hc n hcn)
  obtain ⟨e', he'⟩ := List.exists_mem_of_ne_nil _ (hne d hd n hdn)
  rw [hw, hw', ← width_eq hw e he, ← width_eq hw' e' he', h c hc d hd n hcn hdn e he e' he']

/-- An exclusive group with no branch on the bus "bus". -/
def emptyGroup : Lookup F := ⟨.Global "bus", [], [], 0, 0, some []⟩

/-- One send of width 2 on the bus "bus". -/
def widthTwoSend (x : F) : Lookup F :=
  ⟨.Global "bus", [[.Leaf (.Constant x), .Leaf (.Constant x)]], [.Leaf (.Constant x)], 1, 0, none⟩

/-- **A bus the width check passes and the layout panics on.**

An exclusive group with no branch shares a bus with a send of width 2.

The width check sees only the tuple of width 2.

The layout gives the group width 0, which differs. -/
theorem empty_group_gap {K : Type} [Field K] (x : F) (α β : K) :
    check_bus_widths [[emptyGroup], [widthTwoSend x]] = .ok 2 ∧
      lay_out_lookup_challenges 2 [[(emptyGroup : Lookup F)], [widthTwoSend x]] α β = none := by
  refine ⟨rfl, (lay_out_none_iff _ α β).2 fun h => ?_⟩
  have := h.2 emptyGroup (by simp) (widthTwoSend x) (by simp) "bus" rfl rfl
  simp [width, emptyGroup, widthTwoSend, assert_uniform_tuple_width, assert_uniform_widths] at this

end Plonky3Lean.Proofs.BatchStark
