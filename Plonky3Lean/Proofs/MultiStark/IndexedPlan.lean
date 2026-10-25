module

public import P3MultiStark.Mirror.Indexed

@[expose] public section

/-!
# What the indexed-lookup planner builds

An AIR provides a named table, or reads entries out of one:

```text
    AIR 0  reads "range8", pulling columns 4, 5
    AIR 2  provides "range8" from preprocessed columns 0, 1, on 2^8 rows

        ->  one table "range8" of 2^8 entries, two columns, one reader (AIR 0)
```

This file proves:

- the planner accepts exactly the batches that describe a reduction
- each error names a real offence of its kind
- an accepted plan lists every provided table once, in name order
- each table's readers are exactly the reads that name it, in caller then emission order
-/

namespace Plonky3Lean.Proofs.MultiStark.Indexed

open p3_multi_stark.indexed.mirror

set_option linter.unusedSectionVars false

/-- Every provided table, with its AIR, in caller then emission order. -/
def providers (declared : List IndexedLookups) : List (ℕ × IndexedTable) :=
  declared.zipIdx.flatMap fun (d, a) => d.tables.map (a, ·)

/-- Every read, with its AIR, in caller then emission order. -/
def readsOf (declared : List IndexedLookups) : List (ℕ × IndexedRead) :=
  declared.zipIdx.flatMap fun (d, a) => d.reads.map (a, ·)

/-- The placement of the reads that name a table, in order. -/
def readersOf (nv : List ℕ) (R : List (ℕ × IndexedRead)) (nm : String) : List ReaderPlacement :=
  (R.filter (·.2.table = nm)).map fun (a, r) => ⟨a, r.position, r.payload, nv.getD a 0⟩

/-- A provided table's plan, given its readers. -/
def tablePlan (nv : List ℕ) (x : ℕ × IndexedTable) (readers : List ReaderPlacement) : IndexedTablePlan :=
  ⟨x.2.name, ⟨x.1, x.2.window, x.2.columns, nv.getD x.1 0⟩, readers⟩

theorem foldlM_flatMap_except {α β γ ε : Type _} (f : α → List β) (g : γ → β → Except ε γ) :
    ∀ (l : List α) (b : γ),
      (l.flatMap f).foldlM g b = l.foldlM (fun b x => (f x).foldlM g b) b
  | [], b => rfl
  | x :: l, b => by
    rw [List.flatMap_cons, List.foldlM_append, List.foldlM_cons]
    cases (f x).foldlM g b with
    | error e => rfl
    | ok b' => exact foldlM_flatMap_except f g l b'

/-! ## The providers' loop -/

/-- The providers' loop over provided tables, each with its AIR. -/
def tableStep (bits : ℕ) (nv : List ℕ) (plans : List IndexedTablePlan) (x : ℕ × IndexedTable) :
    Except IndexedPlanError (List IndexedTablePlan) :=
  addTable bits x.1 (nv.getD x.1 0) plans x.2

/-- What an error of the providers' loop says about the provided tables. -/
def TableOffence (bits : ℕ) (nv : List ℕ) (P : List (ℕ × IndexedTable)) : IndexedPlanError → Prop
  | .TableWithoutEntries t => ∃ x ∈ P, x.2.name = t ∧ nv.getD x.1 0 = 0
  | .TableTooLarge t n b => b = bits ∧ ∃ x ∈ P, x.2.name = t ∧ nv.getD x.1 0 = n ∧ 0 < n ∧ bits ≤ n
  | .TableProvidedTwice t f s => ∃ x y, [x, y].Sublist P ∧ x.2.name = t ∧ y.2.name = t ∧ x.1 = f ∧ y.1 = s
  | _ => False

theorem tableOffence_mono {bits : ℕ} {nv : List ℕ} {P Q : List (ℕ × IndexedTable)} (h : P.Sublist Q) :
    ∀ e, TableOffence bits nv P e → TableOffence bits nv Q e
  | .TableWithoutEntries _, ⟨x, hx, h1⟩ => ⟨x, h.subset hx, h1⟩
  | .TableTooLarge _ _ _, ⟨hb, x, hx, h1⟩ => ⟨hb, x, h.subset hx, h1⟩
  | .TableProvidedTwice _ _ _, ⟨x, y, hs, h1⟩ => ⟨x, y, hs.trans h, h1⟩
  | .TableNotProvided _ _, h => h.elim
  | .WidthMismatch _ _ _ _, h => h.elim
  | .TableNotRead _ _, h => h.elim

theorem find?_tablePlan_none {nv : List ℕ} {P : List (ℕ × IndexedTable)} {nm : String} :
    ((P.map (tablePlan nv · [])).find? (·.name = nm)) = none ↔ nm ∉ P.map (·.2.name) := by
  simp [List.find?_eq_none, tablePlan]

/-- **The providers' loop.**

Start from the plans of earlier providers, whose names are distinct.

The loop succeeds exactly when each table has a variable, fits the field, and brings a new name.

It then appends one plan per table, without readers.

On failure, its error is a real offence among the providers. -/
theorem tables_spec (bits : ℕ) (nv : List ℕ) : ∀ (P P₀ : List (ℕ × IndexedTable)),
    (P₀.map (·.2.name)).Nodup →
    (∀ r, P.foldlM (tableStep bits nv) (P₀.map (tablePlan nv · [])) = .ok r ↔
      (∀ x ∈ P, 0 < nv.getD x.1 0 ∧ nv.getD x.1 0 < bits) ∧ ((P₀ ++ P).map (·.2.name)).Nodup ∧
        r = (P₀ ++ P).map (tablePlan nv · [])) ∧
    ∀ e, P.foldlM (tableStep bits nv) (P₀.map (tablePlan nv · [])) = .error e →
      TableOffence bits nv (P₀ ++ P) e
  | [], P₀, hnd => by
    refine ⟨fun r => ?_, fun e h => ?_⟩
    · simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq, List.append_nil]
      exact ⟨fun h => ⟨by simp, hnd, h.symm⟩, fun h => h.2.2.symm⟩
    · simp [pure, Except.pure] at h
  | x :: P, P₀, hnd => by
    rw [List.foldlM_cons]
    have hstep : tableStep bits nv (P₀.map (tablePlan nv · [])) x =
        if nv.getD x.1 0 = 0 then .error (.TableWithoutEntries x.2.name)
        else if ¬ nv.getD x.1 0 < bits then .error (.TableTooLarge x.2.name (nv.getD x.1 0) bits)
        else match (P₀.map (tablePlan nv · [])).find? (·.name = x.2.name) with
          | some existing => .error (.TableProvidedTwice x.2.name existing.table.air x.1)
          | none => .ok (P₀.map (tablePlan nv · []) ++ [tablePlan nv x []]) := rfl
    rw [hstep]
    by_cases h0 : nv.getD x.1 0 = 0
    · simp only [h0, ↓reduceIte]
      refine ⟨fun r => ?_, fun e he => ?_⟩
      · simp only [bind, Except.bind, reduceCtorEq, false_iff, not_and, List.forall_mem_cons]
        intro h; omega
      · simp only [bind, Except.bind, Except.error.injEq] at he
        subst he
        exact ⟨x, by simp, rfl, h0⟩
    by_cases h1 : ¬ nv.getD x.1 0 < bits
    · simp only [h0, h1, ↓reduceIte, not_false_eq_true]
      refine ⟨fun r => ?_, fun e he => ?_⟩
      · simp only [bind, Except.bind, reduceCtorEq, false_iff, not_and, List.forall_mem_cons]
        intro h; exact absurd h.1.2 h1
      · simp only [bind, Except.bind, Except.error.injEq] at he
        subst he
        exact ⟨rfl, x, by simp, rfl, rfl, by omega, by omega⟩
    simp only [h0, h1, ↓reduceIte]
    cases hf : (P₀.map (tablePlan nv · [])).find? (·.name = x.2.name) with
    | some existing =>
      obtain ⟨hmem, hname⟩ : existing ∈ P₀.map (tablePlan nv · []) ∧ existing.name = x.2.name := by
        have := List.find?_some hf
        exact ⟨List.mem_of_find?_eq_some hf, by simpa using this⟩
      obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hmem
      refine ⟨fun r => ?_, fun e he => ?_⟩
      · simp only [bind, Except.bind, reduceCtorEq, false_iff, not_and]
        intro _ hn
        rw [List.map_append, List.nodup_append] at hn
        exact absurd (hn.2.2 _ (List.mem_map_of_mem hy) _
          (List.mem_map_of_mem (f := fun z : ℕ × IndexedTable => z.2.name) List.mem_cons_self)
          (by simpa [tablePlan] using hname)) id
      · simp only [bind, Except.bind, Except.error.injEq] at he
        subst he
        refine ⟨y, x, ?_, by simpa [tablePlan] using hname, rfl, rfl, rfl⟩
        exact (List.singleton_sublist.2 hy).append (List.singleton_sublist.2 List.mem_cons_self)
    | none =>
      have hni := find?_tablePlan_none.1 hf
      have hnd' : ((P₀ ++ [x]).map (·.2.name)).Nodup := by
        rw [List.map_append, List.nodup_append]
        refine ⟨hnd, by simp, fun a ha b hb hab => hni ?_⟩
        simp only [List.map_cons, List.map_nil, List.mem_singleton] at hb
        rw [← hb, ← hab]; exact ha
      obtain ⟨ih1, ih2⟩ := tables_spec bits nv P (P₀ ++ [x]) hnd'
      rw [List.map_append] at ih1 ih2
      simp only [List.map_cons, List.map_nil] at ih1 ih2
      simp only [bind, Except.bind]
      refine ⟨fun r => ?_, fun e he => ?_⟩
      · rw [ih1 r]
        simp only [List.append_assoc, List.singleton_append, List.forall_mem_cons]
        constructor
        · rintro ⟨h2, h3, h4⟩; exact ⟨⟨⟨by omega, by omega⟩, h2⟩, h3, h4⟩
        · rintro ⟨⟨-, h2⟩, h3, h4⟩; exact ⟨h2, h3, h4⟩
      · have := ih2 e he
        simpa using this

/-! ## The readers' loop -/

/-- The readers' loop over reads, each with its AIR. -/
def readStep (nv : List ℕ) (plans : List IndexedTablePlan) (y : ℕ × IndexedRead) :
    Except IndexedPlanError (List IndexedTablePlan) :=
  addRead y.1 (nv.getD y.1 0) plans y.2

/-- The plans of the provided tables, each with the reads that name it so far. -/
def planOf (nv : List ℕ) (T : List (ℕ × IndexedTable)) (R : List (ℕ × IndexedRead)) :
    List IndexedTablePlan :=
  T.map fun x => tablePlan nv x (readersOf nv R x.2.name)

/-- What an error of the readers' loop says about the reads. -/
def ReadOffence (T : List (ℕ × IndexedTable)) (R : List (ℕ × IndexedRead)) : IndexedPlanError → Prop
  | .TableNotProvided t a => ∃ y ∈ R, y.1 = a ∧ y.2.table = t ∧ t ∉ T.map (·.2.name)
  | .WidthMismatch t a pulled carried => ∃ y ∈ R, y.1 = a ∧ y.2.table = t ∧ y.2.payload.length = pulled ∧
      ∃ x ∈ T, x.2.name = t ∧ x.2.columns.length = carried ∧ pulled ≠ carried
  | _ => False

theorem readersOf_snoc (nv : List ℕ) (R : List (ℕ × IndexedRead)) (y : ℕ × IndexedRead) (nm : String) :
    readersOf nv (R ++ [y]) nm = readersOf nv R nm ++
      if y.2.table = nm then [⟨y.1, y.2.position, y.2.payload, nv.getD y.1 0⟩] else [] := by
  simp only [readersOf, List.filter_append, List.map_append]
  split_ifs with h <;> simp [h]

/-- **The readers' loop.**

Start from the provided tables, whose names are distinct, with the readers seen so far.

The loop succeeds exactly when each read names a provided table carrying as many columns as it pulls.

Each table then gains the reads that name it, in order.

On failure, its error is a real offence among the reads. -/
theorem reads_spec (nv : List ℕ) (T : List (ℕ × IndexedTable)) (hnd : (T.map (·.2.name)).Nodup) :
    ∀ (R R₀ : List (ℕ × IndexedRead)),
    (∀ res, R.foldlM (readStep nv) (planOf nv T R₀) = .ok res ↔
      (∀ y ∈ R, ∃ x ∈ T, x.2.name = y.2.table ∧ y.2.payload.length = x.2.columns.length) ∧
        res = planOf nv T (R₀ ++ R)) ∧
    ∀ e, R.foldlM (readStep nv) (planOf nv T R₀) = .error e → ReadOffence T R e
  | [], R₀ => by
    refine ⟨fun res => ?_, fun e h => ?_⟩
    · simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq, List.append_nil]
      exact ⟨fun h => ⟨by simp, h.symm⟩, fun h => h.2.symm⟩
    · simp [pure, Except.pure] at h
  | y :: R, R₀ => by
    rw [List.foldlM_cons]
    have hfind : (planOf nv T R₀).find? (·.name = y.2.table) =
        (T.find? (·.2.name = y.2.table)).map fun x => tablePlan nv x (readersOf nv R₀ x.2.name) := by
      simp only [planOf, List.find?_map]; rfl
    cases hT : T.find? (·.2.name = y.2.table) with
    | none =>
      have hni : y.2.table ∉ T.map (·.2.name) := by
        intro hm
        obtain ⟨x, hx, hxn⟩ := List.mem_map.1 hm
        have := List.find?_eq_none.1 hT x hx
        simp [hxn] at this
      have hstep : readStep nv (planOf nv T R₀) y = .error (.TableNotProvided y.2.table y.1) := by
        simp only [readStep, addRead, hfind, hT, Option.map_none]
      rw [hstep]
      refine ⟨fun res => ?_, fun e he => ?_⟩
      · simp only [bind, Except.bind, reduceCtorEq, false_iff, not_and, List.forall_mem_cons]
        rintro ⟨⟨x, hx, hxn, -⟩, -⟩
        exact absurd (hxn ▸ List.mem_map_of_mem hx) hni
      · simp only [bind, Except.bind, Except.error.injEq] at he
        subst he
        exact ⟨y, List.mem_cons_self, rfl, rfl, hni⟩
    | some x =>
      have hx := List.mem_of_find?_eq_some hT
      have hxn : x.2.name = y.2.table := by simpa using List.find?_some hT
      -- A provided name belongs to one table only.
      have huniq : ∀ x' ∈ T, x'.2.name = y.2.table → x' = x := fun x' hx' hn => by
        obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx'
        obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hx
        have := hnd.getElem_inj_iff (i := i) (j := j) (hi := by simpa using hi) (hj := by simpa using hj)
        have hij : i = j := this.1 (by simp [hn, hxn])
        subst hij; rfl
      by_cases hw : y.2.payload.length ≠ x.2.columns.length
      · have hstep : readStep nv (planOf nv T R₀) y =
            .error (.WidthMismatch y.2.table y.1 y.2.payload.length x.2.columns.length) := by
          simp only [readStep, addRead, hfind, hT, Option.map_some, tablePlan]
          simp only [ne_eq, hw, not_false_eq_true, ↓reduceIte]
        rw [hstep]
        refine ⟨fun res => ?_, fun e he => ?_⟩
        · simp only [bind, Except.bind, reduceCtorEq, false_iff, not_and, List.forall_mem_cons]
          rintro ⟨⟨x', hx', hxn', hw'⟩, -⟩
          rw [huniq x' hx' hxn'] at hw'
          exact absurd hw' hw
        · simp only [bind, Except.bind, Except.error.injEq] at he
          subst he
          exact ⟨y, List.mem_cons_self, rfl, rfl, rfl, x, hx, hxn, rfl, hw⟩
      · have hstep : readStep nv (planOf nv T R₀) y = .ok (planOf nv T (R₀ ++ [y])) := by
          simp only [readStep, addRead, hfind, hT, Option.map_some, tablePlan, hw, ↓reduceIte,
            Except.ok.injEq]
          simp only [planOf, List.map_map, readersOf_snoc]
          refine List.map_congr_left fun z _ => ?_
          by_cases hz : z.2.name = y.2.table
          · simp [tablePlan, hz]
          · simp [tablePlan, hz, Ne.symm hz]
        rw [hstep]
        obtain ⟨ih1, ih2⟩ := reads_spec nv T hnd R (R₀ ++ [y])
        simp only [bind, Except.bind]
        refine ⟨fun res => ?_, fun e he => ?_⟩
        · rw [ih1 res, List.append_assoc, List.singleton_append, List.forall_mem_cons]
          constructor
          · rintro ⟨h1, h2⟩; exact ⟨⟨⟨x, hx, hxn, not_not.1 hw⟩, h1⟩, h2⟩
          · rintro ⟨⟨-, h1⟩, h2⟩; exact ⟨h1, h2⟩
        · have := ih2 e he
          revert this
          cases e <;> simp only [ReadOffence] <;> try exact False.elim
          · rintro ⟨y', hy', h⟩; exact ⟨y', List.mem_cons_of_mem _ hy', h⟩
          · rintro ⟨y', hy', h⟩; exact ⟨y', List.mem_cons_of_mem _ hy', h⟩

/-! ## The planner -/

/-- The batch describes a reduction:

- every providing AIR has at least one variable and fewer than the field's bits
- no table name is provided twice
- every read names a provided table that carries as many columns as it pulls
- every provided table is read. -/
structure Accepted (bits : ℕ) (declared : List IndexedLookups) (nv : List ℕ) : Prop where
  heights : ∀ x ∈ providers declared, 0 < nv.getD x.1 0 ∧ nv.getD x.1 0 < bits
  names : ((providers declared).map (·.2.name)).Nodup
  reads : ∀ y ∈ readsOf declared, ∃ x ∈ providers declared,
    x.2.name = y.2.table ∧ y.2.payload.length = x.2.columns.length
  read : ∀ x ∈ providers declared, ∃ y ∈ readsOf declared, y.2.table = x.2.name

/-- What a table-not-read error says: the AIR provides the table and no read names it. -/
def NotRead (declared : List IndexedLookups) : IndexedPlanError → Prop
  | .TableNotRead t a => ∃ x ∈ providers declared, x.1 = a ∧ x.2.name = t ∧
      ∀ y ∈ readsOf declared, y.2.table ≠ t
  | _ => False

/-- The plan an accepted batch gets: every provided table with the reads naming it, in name order. -/
def acceptedPlan (declared : List IndexedLookups) (nv : List ℕ) : List IndexedTablePlan :=
  (planOf nv (providers declared) (readsOf declared)).mergeSort fun a b => decide (a.name ≤ b.name)

theorem tables_loop (bits : ℕ) (declared : List IndexedLookups) (nv : List ℕ) :
    (declared.zipIdx).foldlM (fun plans (d, air) =>
      d.tables.foldlM (addTable bits air (nv.getD air 0)) plans) [] =
    (providers declared).foldlM (tableStep bits nv) [] := by
  rw [providers, foldlM_flatMap_except]
  congr 1
  funext plans x
  rw [List.foldlM_map]
  rfl

theorem reads_loop (declared : List IndexedLookups) (nv : List ℕ) (plans : List IndexedTablePlan) :
    (declared.zipIdx).foldlM (fun plans (d, air) =>
      d.reads.foldlM (addRead air (nv.getD air 0)) plans) plans =
    (readsOf declared).foldlM (readStep nv) plans := by
  rw [readsOf, foldlM_flatMap_except]
  congr 1
  funext plans x
  rw [List.foldlM_map]
  rfl

theorem planOf_nil (nv : List ℕ) (T : List (ℕ × IndexedTable)) :
    planOf nv T [] = T.map (tablePlan nv · []) := by
  simp [planOf, readersOf]

theorem find?_readers_empty {nv : List ℕ} {T : List (ℕ × IndexedTable)} {R : List (ℕ × IndexedRead)}
    {q : IndexedTablePlan} (h : (planOf nv T R).find? (·.readers.isEmpty) = some q) :
    ∃ x ∈ T, q = tablePlan nv x (readersOf nv R x.2.name) ∧ ∀ y ∈ R, y.2.table ≠ x.2.name := by
  have hq := List.find?_some h
  obtain ⟨x, hx, rfl⟩ := List.mem_map.1 (List.mem_of_find?_eq_some h)
  refine ⟨x, hx, rfl, fun y hy he => ?_⟩
  simp only [tablePlan, List.isEmpty_iff, readersOf, List.map_eq_nil_iff,
    List.filter_eq_nil_iff, decide_eq_true_eq] at hq
  exact hq y hy he

/-- **The indexed-lookup planner.**

Take a batch whose slices agree and which declares something.

The planner returns a plan exactly when the batch is accepted, and the plan is the accepted plan.

Any error it returns names a real offence:

- a table without a variable, too large for the field, or provided twice
- a read of a missing table, or of the wrong width
- a table nobody reads. -/
theorem from_declared_spec (bits : ℕ) (declared : List IndexedLookups) (nv : List ℕ)
    (hlen : declared.length = nv.length) (hne : declared.all IndexedLookups.isEmpty = false) :
    (∀ plans, IndexedPlan.from_declared bits declared nv = some (.ok (some plans)) ↔
      Accepted bits declared nv ∧ plans = acceptedPlan declared nv) ∧
    ∀ e, IndexedPlan.from_declared bits declared nv = some (.error e) →
      TableOffence bits nv (providers declared) e ∨ ReadOffence (providers declared) (readsOf declared) e ∨
        NotRead declared e := by
  unfold IndexedPlan.from_declared
  simp only [hlen, ne_eq, not_true_eq_false, ↓reduceIte, hne, Bool.false_eq_true, Option.some.injEq,
    tables_loop, reads_loop]
  obtain ⟨ht1, ht2⟩ := tables_spec bits nv (providers declared) [] (by simp)
  simp only [List.map_nil, List.nil_append] at ht1 ht2
  cases htab : (providers declared).foldlM (tableStep bits nv) [] with
  | error e =>
    refine ⟨fun plans => ?_, fun e' he => ?_⟩
    · simp only [bind, Except.bind, reduceCtorEq, false_iff, not_and]
      intro hacc
      have := (ht1 _).2 ⟨hacc.heights, hacc.names, rfl⟩
      rw [htab] at this; cases this
    · simp only [bind, Except.bind, Except.error.injEq] at he
      subst he
      exact Or.inl (ht2 _ htab)
  | ok plans₁ =>
    obtain ⟨hh, hn, rfl⟩ := (ht1 _).1 htab
    obtain ⟨hr1, hr2⟩ := reads_spec nv (providers declared) hn (readsOf declared) []
    rw [planOf_nil] at hr1 hr2
    simp only [List.nil_append] at hr1
    simp only [bind, Except.bind]
    cases hrd : (readsOf declared).foldlM (readStep nv) ((providers declared).map (tablePlan nv · []))
      with
    | error e =>
      refine ⟨fun plans => ?_, fun e' he => ?_⟩
      · simp only [reduceCtorEq, false_iff, not_and]
        intro hacc
        have := (hr1 _).2 ⟨hacc.reads, rfl⟩
        rw [hrd] at this; cases this
      · simp only [Except.error.injEq] at he
        subst he
        exact Or.inr (Or.inl (hr2 _ hrd))
    | ok plans₂ =>
      obtain ⟨hreads, rfl⟩ := (hr1 _).1 hrd
      -- Sorting does not change which tables lack a reader.
      have hperm := List.mergeSort_perm (planOf nv (providers declared) (readsOf declared))
        fun a b => decide (a.name ≤ b.name)
      cases hf : ((planOf nv (providers declared) (readsOf declared)).mergeSort
          fun a b => decide (a.name ≤ b.name)).find? (·.readers.isEmpty) with
      | some q =>
        simp only [hf]
        have hq := List.find?_some hf
        have hqm := hperm.subset (List.mem_of_find?_eq_some hf)
        obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hqm
        refine ⟨fun plans => ?_, fun e' he => ?_⟩
        · simp only [throw, throwThe, MonadExceptOf.throw, reduceCtorEq, false_iff, not_and]
          intro hacc
          obtain ⟨y, hy, hyt⟩ := hacc.read x hx
          simp only [tablePlan, List.isEmpty_iff, readersOf, List.map_eq_nil_iff,
            List.filter_eq_nil_iff, decide_eq_true_eq] at hq
          exact absurd hyt (hq y hy)
        · simp only [throw, throwThe, MonadExceptOf.throw, Except.error.injEq] at he
          subst he
          refine Or.inr (Or.inr ⟨x, hx, rfl, rfl, fun y hy hyt => ?_⟩)
          simp only [tablePlan, List.isEmpty_iff, readersOf, List.map_eq_nil_iff,
            List.filter_eq_nil_iff, decide_eq_true_eq] at hq
          exact hq y hy hyt
      | none =>
        simp only [hf]
        have hall := List.find?_eq_none.1 hf
        refine ⟨fun plans => ?_, fun e' he => by simp [pure, Except.pure] at he⟩
        simp only [pure, Except.pure, Except.ok.injEq, Option.some.injEq]
        constructor
        · rintro rfl
          refine ⟨⟨hh, hn, hreads, fun x hx => ?_⟩, rfl⟩
          have := hall _ (hperm.symm.subset (List.mem_map_of_mem hx))
          simp only [tablePlan, List.isEmpty_iff, readersOf, List.map_eq_nil_iff,
            List.filter_eq_nil_iff, decide_eq_true_eq, not_forall, not_not] at this
          obtain ⟨y, hy, hyt⟩ := this
          exact ⟨y, hy, hyt⟩
        · rintro ⟨-, rfl⟩; rfl

/-- **The trivial outcomes.**

The planner panics exactly when the slices disagree on length.

With agreeing slices, it has no plan exactly when nothing is declared. -/
theorem from_declared_trivial (bits : ℕ) (declared : List IndexedLookups) (nv : List ℕ) :
    (IndexedPlan.from_declared bits declared nv = none ↔ declared.length ≠ nv.length) ∧
      (declared.length = nv.length →
        (IndexedPlan.from_declared bits declared nv = some (.ok none) ↔
          declared.all IndexedLookups.isEmpty)) := by
  unfold IndexedPlan.from_declared
  refine ⟨?_, fun hlen => ?_⟩
  · split_ifs with h1 h2 <;> simp [h1]
  · simp only [hlen, ne_eq, not_true_eq_false, ↓reduceIte]
    split_ifs with h2
    · simp [h2]
    · simp only [Option.some.injEq, h2, Bool.false_eq_true, iff_false]
      intro h
      simp only [bind, Except.bind] at h
      split at h
      · cases h
      split at h
      · cases h
      split at h <;> simp [throw, throwThe, MonadExceptOf.throw, pure, Except.pure] at h

/-! ## An accepted plan -/

theorem planOf_names (nv : List ℕ) (T : List (ℕ × IndexedTable)) (R : List (ℕ × IndexedRead)) :
    (planOf nv T R).map (·.name) = T.map (·.2.name) := by
  simp [planOf, tablePlan]

/-- **The tables come once each, in strict name order.** -/
theorem acceptedPlan_sorted {bits : ℕ} {declared : List IndexedLookups} {nv : List ℕ}
    (h : Accepted bits declared nv) :
    (acceptedPlan declared nv).Pairwise fun a b => a.name < b.name := by
  have hperm := List.mergeSort_perm (planOf nv (providers declared) (readsOf declared))
    fun a b => decide (a.name ≤ b.name)
  have hnd : ((acceptedPlan declared nv).map (·.name)).Nodup := by
    rw [acceptedPlan, (hperm.map _).nodup_iff, planOf_names]; exact h.names
  have hs := List.pairwise_mergeSort (le := fun a b : IndexedTablePlan => decide (a.name ≤ b.name))
    (fun a b c h1 h2 => by simp only [decide_eq_true_eq] at *; exact String.le_trans h1 h2)
    (fun a b => by simp only [Bool.or_eq_true, decide_eq_true_eq]; exact String.le_total _ _)
    (planOf nv (providers declared) (readsOf declared))
  exact (hs.and (List.pairwise_map.1 hnd)).imp fun ⟨h1, h2⟩ =>
    Std.lt_of_le_of_ne (of_decide_eq_true h1) h2

theorem filter_name_length {L : List IndexedTablePlan} (hnd : (L.map (·.name)).Nodup) {n : String}
    (hex : ∃ q ∈ L, q.name = n) : (L.filter (·.name = n)).length = 1 := by
  induction L with
  | nil => simp at hex
  | cons q L ih =>
    rw [List.map_cons, List.nodup_cons] at hnd
    by_cases hq : q.name = n
    · have : L.filter (·.name = n) = [] := List.filter_eq_nil_iff.2 fun r hr he => by
        simp only [decide_eq_true_eq] at he
        exact hnd.1 (hq ▸ he ▸ List.mem_map_of_mem hr)
      simp [hq, this]
    · obtain ⟨r, hr, hrn⟩ := hex
      rcases List.mem_cons.1 hr with rfl | hr
      · exact absurd hrn hq
      · simp [hq, ih hnd.2 ⟨r, hr, hrn⟩]

/-- The provider of a name is unique. -/
theorem provider_unique {declared : List IndexedLookups}
    (hnd : ((providers declared).map (·.2.name)).Nodup) {x x' : ℕ × IndexedTable}
    (hx : x ∈ providers declared) (hx' : x' ∈ providers declared) (h : x.2.name = x'.2.name) : x = x' := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hx'
  have := hnd.getElem_inj_iff (i := i) (j := j) (hi := by simpa using hi) (hj := by simpa using hj)
  have hij : i = j := this.1 (by simp [h])
  subst hij; rfl

/-- **Every table of an accepted plan.**

Each comes from one provided table, with the reads that name it, in caller then emission order.

It has a reader, a variable and fewer variables than the field's bits.

Every reader pulls as many columns as it carries. -/
theorem acceptedPlan_tables {bits : ℕ} {declared : List IndexedLookups} {nv : List ℕ}
    (h : Accepted bits declared nv) : ∀ q ∈ acceptedPlan declared nv, ∃ x ∈ providers declared,
      q = tablePlan nv x (readersOf nv (readsOf declared) x.2.name) ∧ q.readers ≠ [] ∧
      0 < q.table.num_variables ∧ q.table.num_variables < bits ∧
      ∀ r ∈ q.readers, r.payload.length = q.table.columns.length := by
  intro q hq
  have hperm := List.mergeSort_perm (planOf nv (providers declared) (readsOf declared))
    fun a b => decide (a.name ≤ b.name)
  obtain ⟨x, hx, rfl⟩ := List.mem_map.1 (hperm.subset hq)
  obtain ⟨y, hy, hyt⟩ := h.read x hx
  refine ⟨x, hx, rfl, ?_, (h.heights x hx).1, (h.heights x hx).2, fun r hr => ?_⟩
  · simp only [tablePlan, readersOf, ne_eq, List.map_eq_nil_iff, List.filter_eq_nil_iff,
      decide_eq_true_eq, not_forall, not_not]
    exact ⟨y, hy, hyt⟩
  · simp only [tablePlan, readersOf, List.mem_map, List.mem_filter, decide_eq_true_eq] at hr
    obtain ⟨y', ⟨hy', hyt'⟩, rfl⟩ := hr
    obtain ⟨x', hx', hn', hw'⟩ := h.reads y' hy'
    rw [provider_unique h.names hx' hx (hn'.trans hyt')] at hw'
    exact hw'

/-- **Every provided table appears in an accepted plan.** -/
theorem acceptedPlan_complete {declared : List IndexedLookups} {nv : List ℕ}
    (x : ℕ × IndexedTable) (hx : x ∈ providers declared) :
    tablePlan nv x (readersOf nv (readsOf declared) x.2.name) ∈ acceptedPlan declared nv :=
  (List.mergeSort_perm _ _).symm.subset (List.mem_map_of_mem hx)

/-- **Every read lands in exactly one table.**

An accepted plan has exactly one table of the read's name.

The read's placement is among that table's readers. -/
theorem acceptedPlan_reads {bits : ℕ} {declared : List IndexedLookups} {nv : List ℕ}
    (h : Accepted bits declared nv) (y : ℕ × IndexedRead) (hy : y ∈ readsOf declared) :
    ((acceptedPlan declared nv).filter (·.name = y.2.table)).length = 1 ∧
      ∃ q ∈ acceptedPlan declared nv, q.name = y.2.table ∧
        (⟨y.1, y.2.position, y.2.payload, nv.getD y.1 0⟩ : ReaderPlacement) ∈ q.readers := by
  obtain ⟨x, hx, hxn, -⟩ := h.reads y hy
  have hq := acceptedPlan_complete (nv := nv) x hx
  have hnd : ((acceptedPlan declared nv).map (·.name)).Nodup := by
    rw [acceptedPlan, ((List.mergeSort_perm _ _).map _).nodup_iff, planOf_names]; exact h.names
  refine ⟨filter_name_length hnd ⟨_, hq, by simpa [tablePlan] using hxn⟩, _, hq,
    by simpa [tablePlan] using hxn, ?_⟩
  simp only [tablePlan, readersOf, List.mem_map, List.mem_filter, decide_eq_true_eq]
  exact ⟨y, ⟨hy, hxn.symm⟩, rfl⟩

end Plonky3Lean.Proofs.MultiStark.Indexed
