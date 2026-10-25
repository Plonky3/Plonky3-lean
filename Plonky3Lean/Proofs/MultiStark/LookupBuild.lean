module

public import Plonky3Lean.Proofs.MultiStark.LookupPlan

@[expose] public section

/-!
# What the lookup planner builds

The planner reads each AIR's declarations and its height, and returns one plan.

A declaration with tuples is active.

Its tuples each own one block of the fraction tables, as tall as the AIR's trace.

Its bus gets an identifier:

```text
    AIR 0:  local [a], [b]          ->  bus 0, private to (0, 0)
            global "range" [x, y]   ->  bus 1
    AIR 1:  global "range" [u, v]   ->  bus 1 again, same width 2
            local, no tuple         ->  dummy identifier 0, no bus
```

This file proves:

- the planner rejects or panics exactly in the cases the code checks, in its order
- a returned plan places every tuple in one aligned block, of its AIR's height
- two active declarations share an identifier exactly when they share a bus
- the declarations on one bus share a width, and the widest one is nonzero
-/

namespace Plonky3Lean.Proofs.MultiStark

open p3_multi_stark.lookup.mirror

set_option linter.unusedSectionVars false

/-! ## The bus table -/

/-- One step of the bus table on an active declaration, given as its bus and its width. -/
def busStep (acc : BusTable × ℕ) (x : LookupBus × ℕ) : Option (BusTable × ℕ) :=
  match acc.1.lookup x.1 with
  | none => some (acc.1 ++ [(x.1, acc.1.length, x.2)], max acc.2 x.2)
  | some (_, established) =>
    match x.1 with
    | .Global _ => if x.2 = established then some (acc.1, max acc.2 x.2) else none
    | .Local _ _ => none

/-- Whether a bus is shared by name. -/
def isGlobal : LookupBus → Prop
  | .Global _ => True
  | .Local _ _ => False

/-- Two active declarations agree when sharing a bus means a named bus of one width. -/
def Agree (x y : LookupBus × ℕ) : Prop := x.1 = y.1 → isGlobal x.1 ∧ x.2 = y.2

theorem agree_symm {x y : LookupBus × ℕ} (h : Agree x y) : Agree y x := fun he => by
  obtain ⟨hg, hw⟩ := h he.symm
  exact ⟨he ▸ hg, hw.symm⟩

/-- A well-formed table: no bus twice, and each entry's identifier is its position. -/
def TableWF (t : BusTable) : Prop :=
  (t.map Prod.fst).Nodup ∧ ∀ k (hk : k < t.length), t[k].2.1 = k

theorem lookup_mem {t : BusTable} {b : LookupBus} {v : ℕ × ℕ} (h : t.lookup b = some v) :
    (b, v) ∈ t := by
  obtain ⟨l₁, l₂, rfl, -⟩ := List.lookup_eq_some_iff.1 h
  simp

theorem lookup_none {t : BusTable} {b : LookupBus} (h : t.lookup b = none) : b ∉ t.map Prod.fst := by
  intro hb
  obtain ⟨⟨b', v⟩, hm, rfl⟩ := List.mem_map.1 hb
  simpa using List.lookup_eq_none_iff.1 h _ hm

/-- In a table without repeated buses, an entry is determined by its bus. -/
theorem entry_unique {t : BusTable} (hnd : (t.map Prod.fst).Nodup) {b : LookupBus} {v w : ℕ × ℕ}
    (hv : (b, v) ∈ t) (hw : (b, w) ∈ t) : v = w := by
  induction t with
  | nil => simp at hv
  | cons e t ih =>
    rw [List.map_cons, List.nodup_cons] at hnd
    rcases List.mem_cons.1 hv with hv | hv <;> rcases List.mem_cons.1 hw with hw | hw
    · exact (Prod.mk.inj (hv.trans hw.symm)).2
    · exact absurd (List.mem_map_of_mem (f := Prod.fst) hw) (by subst hv; exact hnd.1)
    · exact absurd (List.mem_map_of_mem (f := Prod.fst) hv) (by subst hw; exact hnd.1)
    · exact ih hnd.2 hv hw

/-- **The bus table succeeds exactly on agreeing declarations.**

Start from a well-formed table.

Each declaration must agree with every table entry and every later declaration on its bus.

The resulting table is well formed, and lists the starting buses and the new ones.

The widest payload is the running maximum. -/
theorem busFold_spec : ∀ (xs : List (LookupBus × ℕ)) (t : BusTable) (m : ℕ), TableWF t →
    ((xs.foldlM busStep (t, m)).isSome ↔
      (∀ x ∈ xs, ∀ e ∈ t, e.1 = x.1 → isGlobal e.1 ∧ e.2.2 = x.2) ∧ xs.Pairwise Agree) ∧
    ∀ r, xs.foldlM busStep (t, m) = some r → TableWF r.1 ∧ t <+: r.1 ∧
      (∀ b, b ∈ r.1.map Prod.fst ↔ b ∈ t.map Prod.fst ∨ b ∈ xs.map Prod.fst) ∧
      r.2 = xs.foldl (fun a x => max a x.2) m
  | [], t, m, hwf => by simp [hwf]
  | (xb, xw) :: xs, t, m, hwf => by
    rw [List.foldlM_cons]
    cases hlk : t.lookup xb with
    | none =>
      rw [show busStep (t, m) (xb, xw) = some (t ++ [(xb, t.length, xw)], max m xw) by
        simp [busStep, hlk]]
      have hni := lookup_none hlk
      have hwf' : TableWF (t ++ [(xb, t.length, xw)]) := by
        refine ⟨?_, fun k hk => ?_⟩
        · rw [List.map_append, List.nodup_append]
          refine ⟨hwf.1, by simp, fun a ha b hb hab => hni ?_⟩
          simp only [List.map_cons, List.map_nil, List.mem_singleton] at hb
          rw [← hb, ← hab]; exact ha
        · rw [List.getElem_append]
          split_ifs with hkt
          · exact hwf.2 k hkt
          · simp at hk ⊢; omega
      obtain ⟨ih1, ih2⟩ := busFold_spec xs _ (max m xw) hwf'
      simp only [Option.bind_eq_bind, Option.bind_some]
      refine ⟨?_, fun r hr => ?_⟩
      · rw [ih1, List.pairwise_cons]
        constructor
        · rintro ⟨h1, h2⟩
          refine ⟨fun y hy e he hey => ?_, fun y hy hxy => ?_, h2⟩
          · rcases List.mem_cons.1 hy with hy | hy
            · subst hy
              have : e.1 ∈ t.map Prod.fst := List.mem_map_of_mem he
              rw [hey] at this
              exact absurd this hni
            · exact h1 y hy e (List.mem_append_left _ he) hey
          · exact h1 y hy _ (List.mem_append_right _ (List.mem_singleton_self _)) hxy
        · rintro ⟨h1, h2, h3⟩
          refine ⟨fun y hy e he hey => ?_, h3⟩
          rcases List.mem_append.1 he with he | he
          · exact h1 y (List.mem_cons_of_mem _ hy) e he hey
          · rw [List.mem_singleton.1 he] at hey ⊢; exact h2 y hy hey
      · obtain ⟨hw, hp, hm, hmax⟩ := ih2 r hr
        refine ⟨hw, (List.prefix_append _ _).trans hp, fun b => ?_, by simpa using hmax⟩
        rw [hm]; simp [or_assoc]
    | some v =>
      obtain ⟨id, established⟩ := v
      have hmem := lookup_mem hlk
      cases xb with
      | Local i j =>
        rw [show busStep (t, m) (.Local i j, xw) = none by simp [busStep, hlk]]
        simp only [Option.bind_eq_bind, Option.bind_none, Option.isSome_none, Bool.false_eq_true,
          false_iff, not_and, reduceCtorEq, false_implies, implies_true, and_true]
        intro h
        exact absurd (h _ List.mem_cons_self _ hmem rfl).1 (by simp [isGlobal])
      | Global nm =>
        rw [show busStep (t, m) (.Global nm, xw) = if xw = established then some (t, max m xw)
          else none by simp [busStep, hlk]]
        split_ifs with hw
        · obtain ⟨ih1, ih2⟩ := busFold_spec xs t (max m xw) hwf
          simp only [Option.bind_eq_bind, Option.bind_some]
          refine ⟨?_, fun r hr => ?_⟩
          · rw [ih1, List.pairwise_cons]
            constructor
            · rintro ⟨h1, h2⟩
              refine ⟨fun y hy e he hey => ?_, fun y hy hxy => ?_, h2⟩
              · rcases List.mem_cons.1 hy with hy | hy
                · subst hy
                  have he' : (LookupBus.Global nm, e.2) ∈ t := by
                    obtain ⟨e1, e2⟩ := e; simp only at hey; rw [← hey]; exact he
                  rw [entry_unique hwf.1 he' hmem]
                  exact ⟨by rw [hey]; trivial, hw.symm⟩
                · exact h1 y hy e he hey
              · have := h1 y hy _ hmem hxy
                exact ⟨trivial, hw.trans this.2⟩
            · rintro ⟨h1, -, h3⟩
              exact ⟨fun y hy e he hey => h1 y (List.mem_cons_of_mem _ hy) e he hey, h3⟩
          · obtain ⟨hw', hp, hm, hmax⟩ := ih2 r hr
            refine ⟨hw', hp, fun b => ?_, by simpa using hmax⟩
            rw [hm]
            have : LookupBus.Global nm ∈ t.map Prod.fst := List.mem_map_of_mem (f := Prod.fst) hmem
            simp only [List.map_cons, List.mem_cons]
            constructor
            · rintro (h | h) <;> tauto
            · rintro (h | rfl | h) <;> tauto
        · simp only [Option.bind_eq_bind, Option.bind_none, Option.isSome_none, Bool.false_eq_true,
            false_iff, not_and, reduceCtorEq, false_implies, implies_true, and_true]
          intro h
          exact absurd (h _ List.mem_cons_self _ hmem rfl).2 (Ne.symm hw)

/-! ## Identifiers -/

/-- The active declarations of a list, each as its bus and its width. -/
def itemsOf (air : ℕ) (lj : List (Lookup × ℕ)) : List (LookupBus × ℕ) :=
  lj.filterMap fun (l, j) => if l.active then some (busOf air j l, l.widths.headD 0) else none

/-- In a well-formed table, the identifier of an entry is where its bus sits. -/
theorem index_of_mem {t : BusTable} (hwf : TableWF t) {b : LookupBus} {id e : ℕ}
    (h : (b, id, e) ∈ t) : (t.map Prod.fst)[id]? = some b := by
  obtain ⟨k, hk, hke⟩ := List.getElem_of_mem h
  have := hwf.2 k hk
  rw [hke] at this
  subst this
  simp [hk, hke]

theorem prefix_getElem? {α : Type _} {l₁ l₂ : List α} (h : l₁ <+: l₂) {n : ℕ} {x : α}
    (hx : l₁[n]? = some x) : l₂[n]? = some x := by
  obtain ⟨u, rfl⟩ := h
  rw [List.getElem?_append_left (List.getElem?_eq_some_iff.1 hx).1, hx]

/-- **Identifiers follow the bus table.**

The identifier loop of one AIR succeeds exactly when the bus table does on its active declarations.

It then gives each active declaration the position of its bus in the final table. -/
theorem assign_spec (air : ℕ) : ∀ (lj : List (Lookup × ℕ)) (t : BusTable) (m : ℕ) (ids : List ℕ),
    TableWF t →
    ((lj.foldlM (assignBus air) (t, m, ids)).isSome ↔ ((itemsOf air lj).foldlM busStep (t, m)).isSome) ∧
    ∀ r, lj.foldlM (assignBus air) (t, m, ids) = some r →
      (itemsOf air lj).foldlM busStep (t, m) = some (r.1, r.2.1) ∧
      r.2.2.length = ids.length + lj.length ∧ ids <+: r.2.2 ∧
      ∀ k (hk : k < lj.length), lj[k].1.active →
        ∃ hr : ids.length + k < r.2.2.length,
          (r.1.map Prod.fst)[r.2.2[ids.length + k]]? = some (busOf air lj[k].2 lj[k].1)
  | [], t, m, ids, _ => by simp [itemsOf]
  | (l, j) :: lj, t, m, ids, hwf => by
    rw [List.foldlM_cons]
    by_cases ha : l.active
    · have hne : l.widths.isEmpty = false := by simpa [Lookup.active] using ha
      have hitems : itemsOf air ((l, j) :: lj) = (busOf air j l, l.widths.headD 0) :: itemsOf air lj := by
        simp [itemsOf, ha]
      rw [hitems, List.foldlM_cons]
      -- The step on this declaration mirrors the bus table's step, recording an identifier.
      obtain ⟨idx, hidx, hstep⟩ : ∃ idx, (∀ t', busStep (t, m) (busOf air j l, l.widths.headD 0) =
            some t' → (t'.1.map Prod.fst)[idx]? = some (busOf air j l)) ∧
          assignBus air (t, m, ids) (l, j) =
            (busStep (t, m) (busOf air j l, l.widths.headD 0)).map fun t' => (t'.1, t'.2, ids ++ [idx]) := by
        cases hlk : t.lookup (busOf air j l) with
        | none =>
          refine ⟨t.length, fun t' ht' => ?_, ?_⟩
          · simp only [busStep, hlk, Option.some.injEq] at ht'
            subst ht'; simp
          · simp [assignBus, hne, busStep, hlk]
        | some v =>
          obtain ⟨id, e⟩ := v
          have hidx0 := index_of_mem hwf (lookup_mem hlk)
          refine ⟨id, fun t' ht' => ?_, ?_⟩
          · simp only [busStep, hlk] at ht'
            generalize busOf air j l = B at ht' hidx0
            cases B with
            | Local => simp at ht'
            | Global nm =>
              split_ifs at ht'
              · simp only [Option.some.injEq] at ht'; subst ht'; exact hidx0
          · simp only [assignBus, hne, busStep, hlk, Bool.false_eq_true, ↓reduceIte]
            generalize busOf air j l = B
            cases B with
            | Local => simp
            | Global nm => split_ifs <;> simp
      rw [hstep]
      cases hb : busStep (t, m) (busOf air j l, l.widths.headD 0) with
      | none => simp
      | some t' =>
        have hwf' := ((busFold_spec [_] t m hwf).2 t' (by simpa using hb)).1
        obtain ⟨ih1, ih2⟩ := assign_spec air lj t'.1 t'.2 (ids ++ [idx]) hwf'
        simp only [Option.map_some, Option.bind_eq_bind, Option.bind_some]
        refine ⟨ih1, fun r hr => ?_⟩
        obtain ⟨hr1, hr2, hr3, hr4⟩ := ih2 r hr
        refine ⟨hr1, by simp [hr2]; omega, (List.prefix_append _ _).trans hr3, fun k hk hka => ?_⟩
        have hpre' := ((busFold_spec _ t'.1 t'.2 hwf').2 _ hr1).2.1
        cases k with
        | zero =>
          have hlen : ids.length < r.2.2.length := by simp at hr2; omega
          refine ⟨hlen, ?_⟩
          have hget : r.2.2[ids.length] = idx := by
            have := hr3.getElem (i := ids.length) (by simp)
            simpa using this.symm
          simp only [Nat.add_zero, hget, List.getElem_cons_zero]
          have := hidx t' hb
          exact prefix_getElem? (hpre'.map Prod.fst) this
        | succ k =>
          obtain ⟨hr, hk'⟩ := hr4 k (by simpa using hk) (by simpa using hka)
          refine ⟨by simp at hr ⊢; omega, ?_⟩
          simpa [Nat.add_assoc, Nat.add_comm 1 k] using hk'
    · have hi : l.widths.isEmpty = true := by simpa [Lookup.active] using ha
      have hitems : itemsOf air ((l, j) :: lj) = itemsOf air lj := by simp [itemsOf, ha]
      rw [hitems, show assignBus air (t, m, ids) (l, j) = some (t, m, ids ++ [0]) by
        simp [assignBus, hi]]
      simp only [Option.bind_eq_bind, Option.bind_some]
      obtain ⟨ih1, ih2⟩ := assign_spec air lj t m (ids ++ [0]) hwf
      refine ⟨ih1, fun r hr => ?_⟩
      obtain ⟨hr1, hr2, hr3, hr4⟩ := ih2 r hr
      refine ⟨hr1, by simp [hr2]; omega, (List.prefix_append _ _).trans hr3, fun k hk hka => ?_⟩
      cases k with
      | zero => exact absurd hka ha
      | succ k =>
        obtain ⟨hr, hk'⟩ := hr4 k (by simpa using hk) (by simpa using hka)
        refine ⟨by simp at hr ⊢; omega, ?_⟩
        simpa [Nat.add_assoc, Nat.add_comm 1 k] using hk'

/-! ## The placement loop -/

/-- The leaves an active AIR's tuples take: one block of its height per tuple. -/
def leafCount (i : ActiveAir) : ℕ := (i.lookups.map (·.widths.length)).sum * 2 ^ i.num_variables

/-- The active declarations of a list of AIRs, each as its bus and its width. -/
def itemsAll (L : List ActiveAir) : List (LookupBus × ℕ) :=
  L.flatMap fun i => itemsOf i.air_index i.lookups.zipIdx

/-- How a planned AIR answers its active AIR, against the final bus table:

- same position, height and tuple counts
- one identifier per declaration
- each active declaration's identifier is where its bus sits. -/
def Answers (table : BusTable) (a : ActiveAir) (i : LookupInstancePlan) : Prop :=
  i.air_index = a.air_index ∧ i.num_variables = a.num_variables ∧
    i.tuple_counts = a.lookups.map (·.widths.length) ∧ i.bus_ids.length = a.lookups.length ∧
    ∀ j (hj : j < a.lookups.length), a.lookups[j].active →
      ∃ hb : j < i.bus_ids.length, (table.map Prod.fst)[i.bus_ids[j]]? = some (busOf a.air_index j a.lookups[j])

theorem foldlM_option_append {α β : Type _} (f : β → α → Option β) (l₁ l₂ : List α) (b : β) :
    (l₁ ++ l₂).foldlM f b = (l₁.foldlM f b).bind fun b' => l₂.foldlM f b' := by
  simp [List.foldlM_append]

/-- One placement step, with its three overflow checks gathered. -/
theorem planStep_eq (done : List LookupInstancePlan) (t : BusTable) (m h : ℕ) (x : ActiveAir) :
    planStep (done, t, m, h) x =
      if x.num_variables < 64 ∧ leafCount x < 2 ^ 64 ∧ h + leafCount x < 2 ^ 64 then
        (x.lookups.zipIdx.foldlM (assignBus x.air_index) (t, m, [])).map fun a =>
          (done ++ [⟨x.air_index, x.num_variables, h, x.lookups.map (·.widths.length), a.2.2⟩],
            a.1, a.2.1, h + leafCount x)
      else none := by
  unfold planStep
  simp only [shl_one, word, leafCount]
  by_cases h1 : x.num_variables < 64 <;> simp only [h1, ↓reduceIte, Option.bind_eq_bind,
    Option.bind_some, Option.bind_none, true_and, false_and]
  by_cases h2 : (x.lookups.map (·.widths.length)).sum * 2 ^ x.num_variables < 2 ^ 64 <;>
    simp only [h2, ↓reduceIte, Option.bind_some, Option.bind_none, true_and, false_and]
  by_cases h3 : h + (x.lookups.map (·.widths.length)).sum * 2 ^ x.num_variables < 2 ^ 64 <;>
    simp only [h3, ↓reduceIte, Option.bind_some, Option.bind_none]
  cases x.lookups.zipIdx.foldlM (assignBus x.air_index) (t, m, []) <;> rfl

/-- **The placement loop.**

It succeeds exactly when every height is below 64, the leaves fit a word, and the bus table succeeds.

It then places the AIRs from the running height, in order, against the final bus table. -/
theorem planFold_spec : ∀ (L : List ActiveAir) (done : List LookupInstancePlan) (t : BusTable)
    (m h : ℕ), TableWF t → h < 2 ^ 64 →
    ((L.foldlM planStep (done, t, m, h)).isSome ↔ (∀ i ∈ L, i.num_variables < 64) ∧
      h + (L.map leafCount).sum < 2 ^ 64 ∧ ((itemsAll L).foldlM busStep (t, m)).isSome) ∧
    ∀ r, L.foldlM planStep (done, t, m, h) = some r → ∃ new, r.1 = done ++ new ∧
      (itemsAll L).foldlM busStep (t, m) = some (r.2.1, r.2.2.1) ∧
      r.2.2.2 = h + (L.map leafCount).sum ∧ place h new = (new, r.2.2.2) ∧
      List.Forall₂ (fun a i => Answers r.2.1 a i) L new
  | [], done, t, m, h, _, hh => by simpa [itemsAll, place] using hh
  | x :: xs, done, t, m, h, hwf, hh => by
    rw [List.foldlM_cons, planStep_eq]
    simp only [itemsAll, List.flatMap_cons, foldlM_option_append, List.map_cons, List.sum_cons,
      List.forall_mem_cons]
    by_cases hc : x.num_variables < 64 ∧ leafCount x < 2 ^ 64 ∧ h + leafCount x < 2 ^ 64
    swap
    · simp only [hc, ↓reduceIte, Option.bind_eq_bind, Option.bind_none, Option.isSome_none,
        Bool.false_eq_true, false_iff, not_and, reduceCtorEq, false_implies, implies_true, and_true]
      intro h1 h2 _; exact hc ⟨h1.1, by omega, by omega⟩
    obtain ⟨h64, hl, hw⟩ := hc
    simp only [h64, true_and, hl, hw, and_self, ↓reduceIte, Option.bind_eq_bind]
    obtain ⟨ha1, ha2⟩ := assign_spec x.air_index x.lookups.zipIdx t m [] hwf
    cases hfa : x.lookups.zipIdx.foldlM (assignBus x.air_index) (t, m, []) with
    | none =>
      have : ((itemsOf x.air_index x.lookups.zipIdx).foldlM busStep (t, m)) = none := by
        simpa [hfa] using ha1
      simp [this]
    | some a =>
      obtain ⟨hb1, hb2, -, hb4⟩ := ha2 a hfa
      obtain ⟨hwfa, -, -⟩ := (busFold_spec _ t m hwf).2 _ hb1
      obtain ⟨ih1, ih2⟩ := planFold_spec xs (done ++ [⟨x.air_index, x.num_variables, h,
        x.lookups.map (·.widths.length), a.2.2⟩]) a.1 a.2.1 (h + leafCount x) hwfa hw
      simp only [Option.map_some, Option.bind_some, hb1]
      refine ⟨?_, fun r hr => ?_⟩
      · rw [ih1]; constructor <;> rintro ⟨h1, h2, h3⟩ <;> exact ⟨h1, by omega, h3⟩
      obtain ⟨new, hr1, hr2, hr3, hr4, hr5⟩ := ih2 r hr
      have hpre := ((busFold_spec _ a.1 a.2.1 hwfa).2 _ hr2).2.1
      refine ⟨⟨x.air_index, x.num_variables, h, x.lookups.map (·.widths.length), a.2.2⟩ :: new,
        by simp [hr1], hr2, by rw [hr3]; omega, ?_, ?_⟩
      · simp only [place, leafCount] at hr4 ⊢
        simp [hr4, hr3]
      · refine List.Forall₂.cons ⟨rfl, rfl, rfl, by simpa using hb2, fun j hj hja => ?_⟩ hr5
        obtain ⟨hlen, hk⟩ := hb4 j (by simpa using hj) (by simpa using hja)
        simp only [List.length_nil, Nat.zero_add] at hlen hk
        refine ⟨hlen, ?_⟩
        have := prefix_getElem? (hpre.map Prod.fst) hk
        simpa using this

/-! ## The planner's checks -/

/-- Whether some AIR emits a tuple. -/
def anyActive (airs : List (List Lookup)) : Bool := airs.any (·.any Lookup.active)

/-- Whether some declaration carries exclusive flags or reads a periodic column. -/
def unsupported (airs : List (List Lookup)) : Bool := airs.flatten.any fun l => l.exclusive || l.periodic

/-- The worst-case multiplicity sum: each AIR's count weights times its height. -/
def weightedSum (airs : List (List Lookup)) (nv : List ℕ) : ℕ :=
  (List.zipWith (fun ls n => (ls.map (·.count_weight)).sum * 2 ^ n) airs nv).sum

/-- The leaves every tuple takes: one block of its AIR's height per tuple. -/
def leaves (airs : List (List Lookup)) (nv : List ℕ) : ℕ :=
  (List.zipWith (fun ls n => (ls.map (·.widths.length)).sum * 2 ^ n) airs nv).sum

/-- Every active declaration of the batch, as its bus and its width. -/
def declItems (airs : List (List Lookup)) : List (LookupBus × ℕ) :=
  airs.zipIdx.flatMap fun (ls, a) => itemsOf a ls.zipIdx

/-- The active AIRs, in caller order, as the planner collects them. -/
def activeAirs (airs : List (List Lookup)) (nv : List ℕ) : List ActiveAir :=
  ((airs.zip nv).zipIdx).filterMap fun ((ls, n), air) =>
    if ls.any Lookup.active then some (⟨air, n, ls⟩ : ActiveAir) else none

/-- The active AIRs in placement order: by decreasing height, ties in caller order. -/
def sortedAirs (airs : List (List Lookup)) (nv : List ℕ) : List ActiveAir :=
  (activeAirs airs nv).mergeSort fun a b => decide (b.num_variables ≤ a.num_variables)

/-- What the planner does once the multiplicity bound holds. -/
def afterBound (p : ℕ) (airs : List (List Lookup)) (nv : List ℕ) :
    Option (Except LookupError (Option LookupPlan)) :=
  if (sortedAirs airs nv).isEmpty then some (.ok none)
  else ((sortedAirs airs nv).foldlM planStep ([], [], 0, 0)).bind
    fun (instances, table, max_width, active_height) =>
      if p < table.length then some (.error .BusIdentifierCapacityExceeded)
      else if max_width = 0 then none
      else some (.ok (some ⟨instances, max_width, table.length, log2_ceil_usize active_height⟩))

theorem mapM_shl_one (nv : List ℕ) :
    nv.mapM shl_one = if ∀ n ∈ nv, n < 64 then some (nv.map (2 ^ ·)) else none := by
  induction nv with
  | nil => simp
  | cons n nv ih =>
    rw [List.mapM_cons, ih]
    by_cases hn : n < 64 <;> simp [shl_one, hn]
    split_ifs <;> simp

/-- **The planner's early checks**, in the Rust order. -/
theorem build_eq (p : ℕ) (airs : List (List Lookup)) (nv : List ℕ) :
    LookupPlan.build p airs nv =
      if airs.length ≠ nv.length then none
      else if p = 2 ∧ anyActive airs then some (.error .UnsupportedCharacteristic)
      else if unsupported airs then none
      else if ∃ n ∈ nv, 64 ≤ n then none
      else if p ≤ weightedSum airs nv then
        some (.error (.MultiplicityHeightBoundExceeded (weightedSum airs nv)))
      else afterBound p airs nv := by
  unfold LookupPlan.build anyActive unsupported
  rw [mapM_shl_one]
  by_cases h4 : ∃ n ∈ nv, 64 ≤ n
  · have : ¬ ∀ n ∈ nv, n < 64 := fun h => by obtain ⟨n, hn, h6⟩ := h4; have := h n hn; omega
    simp [this, h4]
  have h4' : ∀ n ∈ nv, n < 64 := fun n hn => by by_contra h; exact h4 ⟨n, hn, by omega⟩
  simp only [show (∀ n ∈ nv, n < 64) = True from eq_true h4', Option.bind_some,
    List.zipWith_map_right, weightedSum, afterBound, sortedAirs, activeAirs, h4, ↓reduceIte]

/-! ## The active AIRs -/

/-- The active AIRs from a starting position. -/
def activeFrom (k : ℕ) (airs : List (List Lookup)) (nv : List ℕ) : List ActiveAir :=
  ((airs.zip nv).zipIdx k).filterMap fun ((ls, n), air) =>
    if ls.any Lookup.active then some (⟨air, n, ls⟩ : ActiveAir) else none

/-- Every active declaration from a starting position. -/
def itemsFrom (k : ℕ) (airs : List (List Lookup)) : List (LookupBus × ℕ) :=
  (airs.zipIdx k).flatMap fun (ls, a) => itemsOf a ls.zipIdx

theorem itemsOf_inactive {a : ℕ} {ls : List Lookup} (h : ls.any Lookup.active = false) :
    itemsOf a ls.zipIdx = [] := by
  simp only [itemsOf, List.filterMap_eq_nil_iff]
  rintro ⟨l, j⟩ hm
  have hl := List.fst_mem_of_mem_zipIdx hm
  simp only [List.any_eq_false] at h
  simp [h l hl]

/-- The facts the planner's active AIRs carry, from a starting position. -/
theorem activeFrom_spec : ∀ (k : ℕ) (airs : List (List Lookup)) (nv : List ℕ),
    airs.length = nv.length →
    itemsAll (activeFrom k airs nv) = itemsFrom k airs ∧
      ((activeFrom k airs nv).map leafCount).sum =
        (List.zipWith (fun ls n => (ls.map (·.widths.length)).sum * 2 ^ n) airs nv).sum ∧
      ((activeFrom k airs nv).map ActiveAir.air_index).Pairwise (· < ·) ∧
      ∀ i ∈ activeFrom k airs nv, k ≤ i.air_index ∧ airs[i.air_index - k]? = some i.lookups ∧
        nv[i.air_index - k]? = some i.num_variables ∧ i.lookups.any Lookup.active
  | k, [], nv, _ => by simp [activeFrom, itemsFrom, itemsAll]
  | k, _ :: _, [], h => by simp at h
  | k, ls :: airs, n :: nv, h => by
    obtain ⟨ih1, ih2, ih3, ih4⟩ := activeFrom_spec (k + 1) airs nv (by simpa using h)
    have hrest : activeFrom k (ls :: airs) (n :: nv) =
        (if ls.any Lookup.active then [(⟨k, n, ls⟩ : ActiveAir)] else []) ++ activeFrom (k + 1) airs nv := by
      simp only [activeFrom, List.zip_cons_cons, List.zipIdx_cons, List.filterMap_cons]
      split_ifs <;> rfl
    have hitems : itemsFrom k (ls :: airs) = itemsOf k ls.zipIdx ++ itemsFrom (k + 1) airs := by
      simp [itemsFrom, List.zipIdx_cons]
    rw [hrest, hitems]
    by_cases ha : ls.any Lookup.active = true
    · simp only [ha, ↓reduceIte, List.singleton_append]
      refine ⟨by simp [itemsAll, ← ih1], ?_, ?_, ?_⟩
      · simp only [List.map_cons, List.sum_cons, ih2, List.zipWith_cons_cons, leafCount]
      · refine List.pairwise_cons.2 ⟨fun a ha' => ?_, ih3⟩
        obtain ⟨i, hi, rfl⟩ := List.mem_map.1 ha'
        have := (ih4 i hi).1; simp only at this ⊢; omega
      · intro i hi
        rcases List.mem_cons.1 hi with rfl | hi
        · simp [ha]
        · obtain ⟨h1, h2, h3, h4⟩ := ih4 i hi
          refine ⟨by omega, ?_, ?_, h4⟩
          · rw [show i.air_index - k = (i.air_index - (k + 1)) + 1 by omega]; simpa using h2
          · rw [show i.air_index - k = (i.air_index - (k + 1)) + 1 by omega]; simpa using h3
    · have hf : ls.any Lookup.active = false := by simpa using ha
      simp only [ha, Bool.false_eq_true, ↓reduceIte, List.nil_append]
      refine ⟨by rw [ih1, itemsOf_inactive hf]; simp, ?_, ih3, ?_⟩
      · rw [ih2, List.zipWith_cons_cons, List.sum_cons]
        have : (ls.map (·.widths.length)).sum = 0 := by
          simp only [List.any_eq_false, Lookup.active, Bool.not_eq_true'] at hf
          simp only [List.sum_eq_zero_iff, List.mem_map]
          rintro _ ⟨l, hl, rfl⟩
          have := hf l hl; simpa using this
        simp [this]
      · intro i hi
        obtain ⟨h1, h2, h3, h4⟩ := ih4 i hi
        refine ⟨by omega, ?_, ?_, h4⟩
        · rw [show i.air_index - k = (i.air_index - (k + 1)) + 1 by omega]; simpa using h2
        · rw [show i.air_index - k = (i.air_index - (k + 1)) + 1 by omega]; simpa using h3

theorem activeFrom_nil_iff : ∀ (k : ℕ) (airs : List (List Lookup)) (nv : List ℕ),
    airs.length = nv.length → (activeFrom k airs nv = [] ↔ anyActive airs = false)
  | k, [], nv, _ => by simp [activeFrom, anyActive]
  | k, _ :: _, [], h => by simp at h
  | k, ls :: airs, n :: nv, h => by
    have ih := activeFrom_nil_iff (k + 1) airs nv (by simpa using h)
    have hrest : activeFrom k (ls :: airs) (n :: nv) =
        (if ls.any Lookup.active then [(⟨k, n, ls⟩ : ActiveAir)] else []) ++ activeFrom (k + 1) airs nv := by
      simp only [activeFrom, List.zip_cons_cons, List.zipIdx_cons, List.filterMap_cons]
      split_ifs <;> rfl
    rw [hrest]
    by_cases ha : ls.any Lookup.active = true
    · simp [ha, anyActive]
    · simp only [Bool.not_eq_true] at ha
      simp only [ha, Bool.false_eq_true, ↓reduceIte, List.nil_append, ih]
      simp [anyActive, ha]

/-! ## Private buses never repeat -/

/-- Sharing a bus means sharing a name. -/
def LocalUnique (x y : LookupBus × ℕ) : Prop := x.1 = y.1 → isGlobal x.1

theorem itemsOf_local {a : ℕ} {lj : List (Lookup × ℕ)} {x : LookupBus × ℕ} (hx : x ∈ itemsOf a lj)
    {i j : ℕ} (h : x.1 = .Local i j) : i = a ∧ ∃ l, (l, j) ∈ lj := by
  simp only [itemsOf, List.mem_filterMap] at hx
  obtain ⟨⟨l, j'⟩, hm, hx⟩ := hx
  split_ifs at hx
  simp only [Option.some.injEq] at hx
  subst hx
  simp only [busOf] at h
  split at h
  · simp only [LookupBus.Local.injEq] at h; obtain ⟨rfl, rfl⟩ := h; exact ⟨rfl, l, hm⟩
  · cases h

theorem zipIdx_pairwise_lt {α : Type _} (l : List α) (k : ℕ) : (l.zipIdx k).Pairwise (·.2 < ·.2) := by
  have := List.pairwise_lt_range' (s := k) (n := l.length) (step := 1)
  rw [← List.zipIdx_map_snd] at this
  exact List.pairwise_map.1 this

theorem itemsFrom_unique (k : ℕ) (airs : List (List Lookup)) :
    (itemsFrom k airs).Pairwise LocalUnique := by
  refine List.pairwise_flatMap.2 ⟨fun ⟨ls, a⟩ _ => ?_, (zipIdx_pairwise_lt airs k).imp_of_mem ?_⟩
  · refine (zipIdx_pairwise_lt ls 0).filterMap _ fun ⟨l, j⟩ ⟨l', j'⟩ hxy u hu v hv he => ?_
    dsimp only at hu hv hxy
    split_ifs at hu hv
    simp only [Option.some.injEq] at hu hv
    subst hu hv
    simp only [busOf] at he ⊢
    split at he <;> split at he <;> simp_all [isGlobal]
  · rintro ⟨ls, a⟩ ⟨ls', a'⟩ - - hlt u hu v hv he
    cases hb : u.1 with
    | Global => simp [isGlobal]
    | Local i j =>
      have h1 := (itemsOf_local hu hb).1
      have h2 := (itemsOf_local hv (he ▸ hb)).1
      simp only at hlt; omega

/-- On declarations whose private buses never repeat, agreeing means one width per bus. -/
theorem pairwise_agree_iff {L : List (LookupBus × ℕ)} (hu : L.Pairwise LocalUnique) :
    L.Pairwise Agree ↔ ∀ x ∈ L, ∀ y ∈ L, x.1 = y.1 → x.2 = y.2 := by
  constructor
  · intro h
    have hR : L.Pairwise fun x y => x.1 = y.1 → x.2 = y.2 := h.imp fun hxy he => (hxy he).2
    refine hR.forall_of_forall_of_flip (fun _ _ _ => rfl) (hR.imp fun hxy he => (hxy he.symm).symm)
  · intro h
    exact hu.imp_of_mem fun hx hy hxy he => ⟨hxy he, h _ hx _ hy he⟩

/-! ## The placement of the sorted AIRs -/

/-- Two active declarations on one bus have the same width. -/
def WidthsAgree (airs : List (List Lookup)) : Prop :=
  ∀ x ∈ declItems airs, ∀ y ∈ declItems airs, x.1 = y.1 → x.2 = y.2

/-- The number of distinct buses of the active declarations. -/
def numBuses (airs : List (List Lookup)) : ℕ := ((declItems airs).map Prod.fst).dedup.length

/-- The widest first tuple among the active declarations. -/
def maxWidth (airs : List (List Lookup)) : ℕ := (declItems airs).foldl (fun a x => max a x.2) 0

/-- What a returned plan guarantees. -/
structure PlanWF (airs : List (List Lookup)) (nv : List ℕ) (instances : List LookupInstancePlan)
    (num_buses : ℕ) : Prop where
  /-- The offsets are the running heights, from zero, and end at the leaf count. -/
  placed : place 0 instances = (instances, leaves airs nv)
  /-- The AIRs come by decreasing height. -/
  sorted : instances.Pairwise fun a b => b.num_variables ≤ a.num_variables
  /-- The planned AIRs are the active ones, each once. -/
  active : (instances.map LookupInstancePlan.air_index).Perm ((activeAirs airs nv).map ActiveAir.air_index)
  /-- A planned AIR keeps its height, its tuple counts and one identifier per declaration. -/
  shape : ∀ i ∈ instances, ∃ ls, airs[i.air_index]? = some ls ∧ ls.any Lookup.active ∧
    nv[i.air_index]? = some i.num_variables ∧ i.tuple_counts = ls.map (·.widths.length) ∧
    i.bus_ids.length = ls.length
  /-- The identifiers number the distinct buses, and name each active declaration's bus. -/
  buses : ∃ buses : List LookupBus, buses.Nodup ∧ buses.length = num_buses ∧
    (∀ b, b ∈ buses ↔ b ∈ (declItems airs).map Prod.fst) ∧
    ∀ i ∈ instances, ∀ ls, airs[i.air_index]? = some ls → ∀ j (hj : j < ls.length), ls[j].active →
      ∃ hb : j < i.bus_ids.length, buses[i.bus_ids[j]]? = some (busOf i.air_index j ls[j])

theorem forall₂_mem_left' {α β : Type _} {R : α → β → Prop} :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ R l₁ l₂ → ∀ b ∈ l₂, ∃ a ∈ l₁, R a b
  | _, _, .nil, b, hb => by simp at hb
  | _, _, .cons h hs, b, hb => by
    rcases List.mem_cons.1 hb with rfl | hb
    · exact ⟨_, List.mem_cons_self, h⟩
    · obtain ⟨a, ha, hab⟩ := forall₂_mem_left' hs b hb
      exact ⟨a, List.mem_cons_of_mem _ ha, hab⟩

theorem forall₂_air_index {t : BusTable} {S : List ActiveAir} {I : List LookupInstancePlan}
    (h : List.Forall₂ (fun a i => Answers t a i) S I) :
    I.map LookupInstancePlan.air_index = S.map ActiveAir.air_index := by
  induction h with
  | nil => rfl
  | cons h _ ih => simp [ih, h.1]

theorem forall₂_sorted {t : BusTable} {S : List ActiveAir} {I : List LookupInstancePlan}
    (h : List.Forall₂ (fun a i => Answers t a i) S I)
    (hs : S.Pairwise fun a b => b.num_variables ≤ a.num_variables) :
    I.Pairwise fun a b => b.num_variables ≤ a.num_variables := by
  induction h with
  | nil => exact List.Pairwise.nil
  | @cons a i xs ys h hrest ih =>
    rw [List.pairwise_cons] at hs ⊢
    refine ⟨fun j hj => ?_, ih hs.2⟩
    obtain ⟨b, hb, hbj⟩ := forall₂_mem_left' hrest j hj
    rw [h.2.1, hbj.2.1]; exact hs.1 b hb

/-- **The placement of the sorted AIRs.**

It succeeds exactly when the leaves fit a word and every bus has one width.

It then yields a well-formed plan, the leaf count, the widest payload and the bus count. -/
theorem sorted_fold {airs : List (List Lookup)} {nv : List ℕ} (hlen : airs.length = nv.length)
    (h64 : ∀ n ∈ nv, n < 64) :
    (((sortedAirs airs nv).foldlM planStep ([], [], 0, 0)).isSome ↔
      leaves airs nv < 2 ^ 64 ∧ WidthsAgree airs) ∧
    ∀ r, (sortedAirs airs nv).foldlM planStep ([], [], 0, 0) = some r →
      r.2.2.2 = leaves airs nv ∧ r.2.2.1 = maxWidth airs ∧ r.2.1.length = numBuses airs ∧
        PlanWF airs nv r.1 r.2.1.length := by
  have hperm : (sortedAirs airs nv).Perm (activeAirs airs nv) := List.mergeSort_perm _ _
  obtain ⟨hitems, hsum, -, hfacts⟩ := activeFrom_spec 0 airs nv hlen
  have hwf0 : TableWF [] := ⟨by simp, by simp⟩
  obtain ⟨hf1, hf2⟩ := planFold_spec (sortedAirs airs nv) [] [] 0 0 hwf0 (by norm_num)
  obtain ⟨hb1, hb2⟩ := busFold_spec (itemsAll (sortedAirs airs nv)) [] 0 hwf0
  have hiperm : (itemsAll (sortedAirs airs nv)).Perm (declItems airs) := by
    rw [show declItems airs = itemsAll (activeAirs airs nv) from hitems.symm]
    exact hperm.flatMap_right _
  have hsum' : ((sortedAirs airs nv).map leafCount).sum = leaves airs nv := by
    rw [(hperm.map _).sum_eq]; exact hsum
  have hfacts' : ∀ i ∈ sortedAirs airs nv, airs[i.air_index]? = some i.lookups ∧
      nv[i.air_index]? = some i.num_variables ∧ i.lookups.any Lookup.active := fun i hi => by
    obtain ⟨-, h2, h3, h4⟩ := hfacts i (hperm.subset hi)
    simpa using And.intro h2 (And.intro h3 h4)
  have hagree : (itemsAll (sortedAirs airs nv)).Pairwise Agree ↔ WidthsAgree airs := by
    rw [List.Perm.pairwise_iff (fun h => agree_symm h) hiperm]
    exact pairwise_agree_iff (itemsFrom_unique 0 airs)
  refine ⟨?_, fun r hr => ?_⟩
  · rw [hf1, hb1, hagree, hsum']
    simp only [List.not_mem_nil, false_implies, implies_true, true_and, Nat.zero_add]
    constructor
    · rintro ⟨-, h1, h2⟩; exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩
      refine ⟨fun i hi => h64 _ ?_, h1, h2⟩
      exact List.mem_of_getElem? (hfacts' i hi).2.1
  obtain ⟨new, hr1, hr2, hr3, hr4, hr5⟩ := hf2 r hr
  obtain ⟨hwf, -, hmem, hmax⟩ := hb2 _ hr2
  simp only at hwf hmem hmax
  simp only [List.nil_append] at hr1
  subst hr1
  have hmax' : r.2.2.1 = maxWidth airs := by
    rw [hmax]
    exact hiperm.foldl_eq' (fun x _ y _ z => by omega) 0
  have hbus : ∀ b, b ∈ r.2.1.map Prod.fst ↔ b ∈ (declItems airs).map Prod.fst := fun b => by
    rw [hmem]; simp only [List.map_nil, List.not_mem_nil, false_or]
    exact ⟨fun h => (hiperm.map _).subset h, fun h => (hiperm.map _).symm.subset h⟩
  have hlen' : r.2.1.length = numBuses airs := by
    have := (List.perm_ext_iff_of_nodup (l₂ := ((declItems airs).map Prod.fst).dedup) hwf.1
      (List.nodup_dedup _)).2 fun b => by rw [List.mem_dedup]; exact hbus b
    simpa [numBuses] using this.length_eq
  refine ⟨by rw [hr3, hsum', Nat.zero_add], hmax', hlen', ?_⟩
  -- The planned AIRs answer the sorted ones, which are the active ones.
  have hs : (sortedAirs airs nv).Pairwise fun a b => b.num_variables ≤ a.num_variables :=
    (List.pairwise_mergeSort (le := fun a b : ActiveAir => decide (b.num_variables ≤ a.num_variables))
      (fun a b c h1 h2 => by simp only [decide_eq_true_eq] at *; omega)
      (fun a b => by simp only [Bool.or_eq_true, decide_eq_true_eq]; omega) _).imp
      fun h => of_decide_eq_true h
  refine ⟨by rw [hr4, hr3, hsum', Nat.zero_add], forall₂_sorted hr5 hs,
    by rw [forall₂_air_index hr5]; exact hperm.map _, fun i hi => ?_, ?_⟩
  · obtain ⟨a, ha, h1, h2, h3, h4, -⟩ := forall₂_mem_left' hr5 i hi
    obtain ⟨g1, g2, g3⟩ := hfacts' a ha
    exact ⟨a.lookups, by rw [h1]; exact g1, g3, by rw [h1, h2]; exact g2, h3, h4⟩
  · refine ⟨r.2.1.map Prod.fst, hwf.1, by simp, hbus, fun i hi ls hls j hj hja => ?_⟩
    obtain ⟨a, ha, h1, -, -, -, h5⟩ := forall₂_mem_left' hr5 i hi
    have hla : a.lookups = ls := by
      have := (hfacts' a ha).1; rw [← h1, hls] at this; exact (Option.some.inj this).symm
    subst hla
    rw [h1]
    exact h5 j hj hja

instance (airs : List (List Lookup)) : Decidable (WidthsAgree airs) := by
  unfold WidthsAgree; infer_instance

/-- The planned AIRs, as the placement loop returns them. -/
def plannedInstances (airs : List (List Lookup)) (nv : List ℕ) : List LookupInstancePlan :=
  (((sortedAirs airs nv).foldlM planStep ([], [], 0, 0)).map (·.1)).getD []

/-- The plan the planner returns when it returns one. -/
def thePlan (airs : List (List Lookup)) (nv : List ℕ) : LookupPlan :=
  ⟨plannedInstances airs nv, maxWidth airs, numBuses airs, log2_ceil_usize (leaves airs nv)⟩

theorem afterBound_eq (p : ℕ) {airs : List (List Lookup)} {nv : List ℕ} (hlen : airs.length = nv.length)
    (h64 : ∀ n ∈ nv, n < 64) :
    afterBound p airs nv =
      if anyActive airs = false then some (.ok none)
      else if ¬ (leaves airs nv < 2 ^ 64 ∧ WidthsAgree airs) then none
      else if p < numBuses airs then some (.error .BusIdentifierCapacityExceeded)
      else if maxWidth airs = 0 then none
      else some (.ok (some (thePlan airs nv))) := by
  have hempty : (sortedAirs airs nv).isEmpty = true ↔ anyActive airs = false := by
    rw [← activeFrom_nil_iff 0 airs nv hlen, List.isEmpty_iff, ← List.length_eq_zero_iff,
      ← List.length_eq_zero_iff (l := activeFrom 0 airs nv)]
    exact iff_of_eq (congrArg (· = 0) (List.mergeSort_perm _ _).length_eq)
  obtain ⟨hs1, hs2⟩ := sorted_fold hlen h64
  unfold afterBound
  by_cases ha : anyActive airs = false
  · simp [hempty.2 ha, ha]
  have hne : ¬ (sortedAirs airs nv).isEmpty = true := fun h => ha (hempty.1 h)
  simp only [hne, ha, Bool.false_eq_true, ↓reduceIte]
  cases hr : (sortedAirs airs nv).foldlM planStep ([], [], 0, 0) with
  | none =>
    have : ¬ (leaves airs nv < 2 ^ 64 ∧ WidthsAgree airs) := by rw [← hs1, hr]; simp
    simp only [Option.bind_none, show (¬ (leaves airs nv < 2 ^ 64 ∧ WidthsAgree airs)) = True from
      eq_true this, ↓reduceIte, Bool.true_eq_false]
  | some r =>
    have hc : leaves airs nv < 2 ^ 64 ∧ WidthsAgree airs := by rw [← hs1, hr]; simp
    obtain ⟨h1, h2, h3, -⟩ := hs2 r hr
    have hpl : plannedInstances airs nv = r.1 := by simp [plannedInstances, hr]
    simp only [hc, not_true_eq_false, ↓reduceIte, Option.bind_some, h3, h2, thePlan, hpl, h1,
      and_self, Bool.true_eq_false]

/-- **The planner's outcome**, check by check in the Rust order. -/
theorem build_spec (p : ℕ) (airs : List (List Lookup)) (nv : List ℕ) :
    LookupPlan.build p airs nv =
      if airs.length ≠ nv.length then none
      else if p = 2 ∧ anyActive airs then some (.error .UnsupportedCharacteristic)
      else if unsupported airs then none
      else if ∃ n ∈ nv, 64 ≤ n then none
      else if p ≤ weightedSum airs nv then
        some (.error (.MultiplicityHeightBoundExceeded (weightedSum airs nv)))
      else if anyActive airs = false then some (.ok none)
      else if ¬ (leaves airs nv < 2 ^ 64 ∧ WidthsAgree airs) then none
      else if p < numBuses airs then some (.error .BusIdentifierCapacityExceeded)
      else if maxWidth airs = 0 then none
      else some (.ok (some (thePlan airs nv))) := by
  rw [build_eq]
  by_cases h1 : airs.length ≠ nv.length
  · simp [h1]
  by_cases h4 : ∃ n ∈ nv, 64 ≤ n
  · simp [h4]
  have h64 : ∀ n ∈ nv, n < 64 := fun n hn => by by_contra h; exact h4 ⟨n, hn, by omega⟩
  simp only [h1, h4, ↓reduceIte, afterBound_eq p (not_not.1 h1) h64]

/-- **A returned plan is well formed.** -/
theorem build_wf {p : ℕ} {airs : List (List Lookup)} {nv : List ℕ} {plan : LookupPlan}
    (h : LookupPlan.build p airs nv = some (.ok (some plan))) :
    plan = thePlan airs nv ∧ PlanWF airs nv plan.instances plan.num_buses ∧
      0 < plan.max_width ∧ plan.num_buses ≤ p ∧ WidthsAgree airs ∧ leaves airs nv < 2 ^ 64 ∧
      plan.num_variables = log2_ceil_usize (leaves airs nv) := by
  rw [build_spec] at h
  split_ifs at h with h1 h2 h3 h4 h5 h6 h7 h8 h9 <;> cases h
  have hlen : airs.length = nv.length := not_not.1 h1
  have h64 : ∀ n ∈ nv, n < 64 := fun n hn => by by_contra hn'; exact h4 ⟨n, hn, by omega⟩
  obtain ⟨hs1, hs2⟩ := sorted_fold hlen h64
  have hc : leaves airs nv < 2 ^ 64 ∧ WidthsAgree airs := h7
  obtain ⟨r, hr⟩ := Option.isSome_iff_exists.1 (hs1.2 hc)
  obtain ⟨-, -, h3, hwf⟩ := hs2 r hr
  have hpl : plannedInstances airs nv = r.1 := by simp [plannedInstances, hr]
  refine ⟨rfl, ?_, Nat.pos_of_ne_zero h9, by simp only [thePlan]; omega, hc.2, hc.1, rfl⟩
  simp only [thePlan, hpl, ← h3]
  exact hwf

/-! ## Consequences for a returned plan -/

theorem mem_declItems {airs : List (List Lookup)} {a j : ℕ} {ls : List Lookup} {l : Lookup}
    (ha : airs[a]? = some ls) (hj : ls[j]? = some l) (hl : l.active) :
    (busOf a j l, l.widths.headD 0) ∈ declItems airs := by
  simp only [declItems, List.mem_flatMap, itemsOf, List.mem_filterMap]
  exact ⟨(ls, a), List.mk_mem_zipIdx_iff_getElem?.2 ha, (l, j),
    List.mk_mem_zipIdx_iff_getElem?.2 hj, by simp [hl]⟩

theorem le_foldl_max : ∀ (l : List (LookupBus × ℕ)) (m : ℕ), m ≤ l.foldl (fun a x => max a x.2) m
  | [], _ => le_rfl
  | _ :: l, _ => le_trans (le_max_left _ _) (le_foldl_max l _)

theorem mem_le_foldl_max : ∀ (l : List (LookupBus × ℕ)) (m : ℕ), ∀ x ∈ l,
    x.2 ≤ l.foldl (fun a x => max a x.2) m
  | [], _, _, h => by simp at h
  | y :: l, m, x, h => by
    rcases List.mem_cons.1 h with rfl | h
    · exact le_trans (le_max_right _ _) (le_foldl_max l _)
    · exact mem_le_foldl_max l _ x h

/-- **Identifiers name buses.**

In a returned plan, take two active declarations of planned AIRs.

Their identifiers are equal exactly when their buses are, and both are below the bus count. -/
theorem build_ids {p : ℕ} {airs : List (List Lookup)} {nv : List ℕ} {plan : LookupPlan}
    (h : LookupPlan.build p airs nv = some (.ok (some plan))) {i i' : LookupInstancePlan}
    (hi : i ∈ plan.instances) (hi' : i' ∈ plan.instances) {ls ls' : List Lookup}
    (hls : airs[i.air_index]? = some ls) (hls' : airs[i'.air_index]? = some ls') {j j' : ℕ}
    (hj : j < ls.length) (hj' : j' < ls'.length) (ha : ls[j].active) (ha' : ls'[j'].active) :
    ∃ (hb : j < i.bus_ids.length) (hb' : j' < i'.bus_ids.length),
      (i.bus_ids[j] = i'.bus_ids[j'] ↔ busOf i.air_index j ls[j] = busOf i'.air_index j' ls'[j']) ∧
        i.bus_ids[j] < plan.num_buses := by
  obtain ⟨-, hwf, -⟩ := build_wf h
  obtain ⟨buses, hnd, hlen, -, hid⟩ := hwf.buses
  obtain ⟨hb, e⟩ := hid i hi ls hls j hj ha
  obtain ⟨hb', e'⟩ := hid i' hi' ls' hls' j' hj' ha'
  obtain ⟨hk, -⟩ := List.getElem?_eq_some_iff.1 e
  obtain ⟨hk', -⟩ := List.getElem?_eq_some_iff.1 e'
  refine ⟨hb, hb', ⟨fun he => ?_, fun he => ?_⟩, hlen ▸ hk⟩
  · rw [he, e'] at e; exact (Option.some.inj e).symm
  · rw [← he] at e'
    rw [List.getElem?_eq_getElem hk] at e
    rw [List.getElem?_eq_getElem hk'] at e'
    exact (hnd.getElem_inj_iff).1 ((Option.some.inj e).trans (Option.some.inj e').symm)

/-- **One width per bus.**

In a returned plan, two active declarations on one bus have first tuples of one width.

Every active declaration's width is at most the widest, which is nonzero. -/
theorem build_widths {p : ℕ} {airs : List (List Lookup)} {nv : List ℕ} {plan : LookupPlan}
    (h : LookupPlan.build p airs nv = some (.ok (some plan))) {a a' j j' : ℕ} {ls ls' : List Lookup}
    {l l' : Lookup} (ha : airs[a]? = some ls) (ha' : airs[a']? = some ls') (hj : ls[j]? = some l)
    (hj' : ls'[j']? = some l') (hl : l.active) (hl' : l'.active) :
    (busOf a j l = busOf a' j' l' → l.widths.headD 0 = l'.widths.headD 0) ∧
      l.widths.headD 0 ≤ plan.max_width ∧ 0 < plan.max_width := by
  obtain ⟨rfl, -, hpos, -, hagree, -⟩ := build_wf h
  refine ⟨fun he => hagree _ (mem_declItems ha hj hl) _ (mem_declItems ha' hj' hl') he, ?_, hpos⟩
  exact mem_le_foldl_max _ 0 _ (mem_declItems ha hj hl)

theorem log2_ceil_usize_eq_zero_iff (n : ℕ) : log2_ceil_usize n = 0 ↔ n ≤ 1 := by
  unfold log2_ceil_usize; split_ifs with h <;> simp [h]

/-- **The fraction tables have a variable unless one tuple sits on a one-row trace.**

A returned plan's table has no variable exactly when the batch has one leaf.

The fractional reduction then has nothing to fold, and rejects. -/
theorem build_num_variables_eq_zero {p : ℕ} {airs : List (List Lookup)} {nv : List ℕ}
    {plan : LookupPlan} (h : LookupPlan.build p airs nv = some (.ok (some plan))) :
    plan.num_variables = 0 ↔ leaves airs nv ≤ 1 := by
  obtain ⟨-, -, -, -, -, -, hnv⟩ := build_wf h
  rw [hnv, log2_ceil_usize_eq_zero_iff]

section Link

open p3_multilinear_util.point.mirror Plonky3Lean.Proofs.MultilinearUtil
  Plonky3Lean.Spec.MultilinearUtil Plonky3Lean.Spec.MultiStark

variable {K : Type _} [Field K]

/-- **A returned plan's blocks are placed.**

They have pairwise disjoint leaves inside the padded table of 2^M leaves, for the plan's M. -/
theorem build_placed {p : ℕ} {airs : List (List Lookup)} {nv : List ℕ} {plan : LookupPlan}
    (h : LookupPlan.build p airs nv = some (.ok (some plan))) (m d : ℕ → ℕ → ℕ → K) :
    Placed (planFracBlocks plan.instances m d) plan.num_variables := by
  obtain ⟨-, hwf, -, -, -, -, hnv⟩ := build_wf h
  have := plan_placed plan.instances hwf.sorted m d
  rwa [hwf.placed, ← hnv] at this

/-- **The lookup link of a returned plan.**

Take the padded tables the plan defines, and a point q with one coordinate per table variable.

The folded claim N(q) + theta (D(q) - 1) is the sum, over the plan's blocks, of each block's share. -/
theorem build_link {p : ℕ} {airs : List (List Lookup)} {nv : List ℕ} {plan : LookupPlan}
    (h : LookupPlan.build p airs nv = some (.ok (some plan))) (m d : ℕ → ℕ → ℕ → K)
    (q : List K) (hq : q.length = plan.num_variables) (θ : K) :
    claimed_sum (rowExt (numTable (planFracBlocks plan.instances m d)) q)
        (rowExt (denTable (planFracBlocks plan.instances m d)) q) θ =
      ((planBlocks plan.instances).map fun nc =>
        eq (vertex (q.length - nc.1) nc.2) (q.take (q.length - nc.1)) *
          (rowExt (m nc.1 nc.2) (q.drop (q.length - nc.1)) +
            θ * (rowExt (d nc.1 nc.2) (q.drop (q.length - nc.1)) - 1))).sum := by
  obtain ⟨-, hwf, -, -, -, -, hnv⟩ := build_wf h
  have := plan_link plan.instances hwf.sorted m d q (by rw [hwf.placed, ← hnv, hq]) θ
  rwa [hwf.placed] at this

end Link

end Plonky3Lean.Proofs.MultiStark
