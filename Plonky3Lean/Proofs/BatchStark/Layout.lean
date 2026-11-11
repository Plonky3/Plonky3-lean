module

public import P3BatchStark.Assumptions.Mirror.Transcript
public import Plonky3Lean.Proofs.Lookup.Api

@[expose] public section

/-!
# The layout of the lookup challenges

One pair (alpha, beta) is drawn for the whole batch.

Every lookup gets a bus id:

- two global lookups share an id exactly when they name the same bus
- a local lookup gets an id no other lookup has
- every id is below the number of lookups.

Lookup j of instance i then reads the pair (alpha + (id + 1) beta^W, beta).

Here W is the widest payload, at least 1.

The layout panics exactly when widths disagree in one of two places:

- the tuples of one lookup
- two global lookups on one bus.
-/

set_option linter.unusedSectionVars false

namespace Plonky3Lean.Proofs.BatchStark

open p3_batch_stark.transcript.mirror p3_lookup.mirror

variable {F : Type}

/-- The payload width of a lookup, or none when its tuples differ in width. -/
def width (l : Lookup F) : Option ℕ := assert_uniform_tuple_width l.elements

/-- Two lookups share a bus: the same position, or global lookups naming the same bus. -/
def SameBus (P : List (Lookup F)) (a b : ℕ) : Prop :=
  a = b ∨ ∃ n, P[a]?.map (·.kind) = some (.Global n) ∧ P[b]?.map (·.kind) = some (.Global n)

/-- The layout's invariant over the lookups P processed so far, their ids, and the bookkeeping. -/
structure Inv (P : List (Lookup F)) (ids : List ℕ) (st : LayoutState) : Prop where
  len : ids.length = P.length
  bound : st.next_bus ≤ P.length
  lt : ∀ a < ids.length, ids.getD a 0 < st.next_bus
  eq_iff : ∀ a < ids.length, ∀ b < ids.length, ids.getD a 0 = ids.getD b 0 ↔ SameBus P a b
  gi_some : ∀ n, ∀ a < P.length, P[a]?.map (·.kind) = some (.Global n) →
    lookupKey st.global_index n = some (ids.getD a 0)
  gi_ex : ∀ n x, lookupKey st.global_index n = some x → ∃ a < P.length, P[a]?.map (·.kind) = some (.Global n)
  gi_none : ∀ n, lookupKey st.global_index n = none → ∀ a < P.length, P[a]?.map (·.kind) ≠ some (.Global n)
  keys : ∀ n, lookupKey st.global_index n = none ↔ lookupKey st.global_width n = none
  wd : ∀ a < P.length, ∃ w, (P[a]?.bind width) = some w ∧ w ≤ st.max_message_width
  gw_some : ∀ n, ∀ a < P.length, P[a]?.map (·.kind) = some (.Global n) →
    lookupKey st.global_width n = (P[a]?.bind width)
  max_pos : 1 ≤ st.max_message_width

theorem lookupKey_append {β : Type} (m : List (String × β)) (k k' : String) (v : β) :
    lookupKey (m ++ [(k, v)]) k' = (lookupKey m k').or (if k = k' then some v else none) := by
  unfold lookupKey
  rw [List.find?_append]
  cases m.find? (·.1 = k') <;> by_cases h : k = k' <;> simp [h]

theorem inv_nil : Inv ([] : List (Lookup F)) [] ⟨[], [], 0, 1⟩ where
  len := rfl
  bound := le_refl _
  lt := by simp
  eq_iff := by simp
  gi_some := by simp
  gi_ex := by simp [lookupKey]
  gi_none := by simp
  keys := by simp [lookupKey]
  wd := by simp
  gw_some := by simp
  max_pos := le_refl _

theorem getD_append_left {l : List ℕ} {a : ℕ} (x : ℕ) (h : a < l.length) :
    (l ++ [x]).getD a 0 = l.getD a 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_append_right {l : List ℕ} (x : ℕ) : (l ++ [x]).getD l.length 0 = x := by
  simp [List.getD_eq_getElem?_getD]

theorem get_append_left {P : List (Lookup F)} {a : ℕ} (c : Lookup F) (h : a < P.length) :
    (P ++ [c])[a]? = P[a]? := List.getElem?_append_left h

theorem split_lt {P : List (Lookup F)} {c : Lookup F} {a : ℕ} (ha : a < (P ++ [c]).length) :
    a < P.length ∨ a = P.length := by
  simp at ha; omega

/-- The id characterization extends to a new lookup.

Its id must equal exactly the ids of the lookups it shares a bus with. -/
theorem eq_iff_ext {P : List (Lookup F)} {ids : List ℕ} {c : Lookup F} {id : ℕ}
    (len : ids.length = P.length)
    (eq_iff : ∀ a < ids.length, ∀ b < ids.length, ids.getD a 0 = ids.getD b 0 ↔ SameBus P a b)
    (hnew : ∀ a < P.length, ids.getD a 0 = id ↔ SameBus (P ++ [c]) a P.length) :
    ∀ a < (ids ++ [id]).length, ∀ b < (ids ++ [id]).length,
      (ids ++ [id]).getD a 0 = (ids ++ [id]).getD b 0 ↔ SameBus (P ++ [c]) a b := by
  have hsym : ∀ x y, SameBus (P ++ [c]) x y ↔ SameBus (P ++ [c]) y x := by
    intro x y; unfold SameBus; constructor <;> rintro (h | ⟨n, h1, h2⟩) <;> first | exact .inl h.symm | exact .inr ⟨n, h2, h1⟩
  intro a ha b hb
  have ha' : a < P.length ∨ a = P.length := by simp at ha; omega
  have hb' : b < P.length ∨ b = P.length := by simp at hb; omega
  rcases ha' with ha' | rfl <;> rcases hb' with hb' | rfl
  · rw [getD_append_left _ (len ▸ ha'), getD_append_left _ (len ▸ hb'), eq_iff a (len ▸ ha') b (len ▸ hb')]
    simp only [SameBus, get_append_left c ha', get_append_left c hb']
  · rw [getD_append_left (a := a) _ (len ▸ ha'), ← len, getD_append_right, len]; exact hnew a ha'
  · rw [getD_append_left (a := b) _ (len ▸ hb'), ← len, getD_append_right, len, eq_comm, hsym]; exact hnew b hb'
  · simp [SameBus]

/-- One step of the layout keeps the invariant. -/
theorem inv_step {P : List (Lookup F)} {ids : List ℕ} {st st' : LayoutState} {c : Lookup F} {id : ℕ}
    (hI : Inv P ids st) (h : busId st c = some (id, st')) : Inv (P ++ [c]) (ids ++ [id]) st' := by
  obtain ⟨len, bound, lt, eq_iff, gi_some, gi_ex, gi_none, keys, wd, gw_some, max_pos⟩ := hI
  unfold busId at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨w, hw, h⟩ := h
  have hlen : (ids ++ [id]).length = (P ++ [c]).length := by simp [len]
  have hc : (P ++ [c])[P.length]? = some c := by simp
  -- The width facts are the same in every branch.
  have wd' : ∀ m, m = max st.max_message_width w →
      ∀ a < (P ++ [c]).length, ∃ v, ((P ++ [c])[a]?.bind width) = some v ∧ v ≤ m := by
    rintro m rfl a ha
    rcases split_lt ha with ha' | rfl
    · obtain ⟨v, h1, h2⟩ := wd a ha'
      exact ⟨v, by rw [get_append_left c ha']; exact h1, le_trans h2 (le_max_left _ _)⟩
    · exact ⟨w, by simp [width, hw], le_max_right _ _⟩
  cases hk : c.kind with
  | Local =>
    simp only [hk, Option.pure_def, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have hnot : ∀ n, (P ++ [c])[P.length]?.map (·.kind) ≠ some (.Global n) := by simp [hk]
    refine ⟨hlen, by simp; omega, ?_, eq_iff_ext len eq_iff ?_, ?_, ?_, ?_, keys, wd' _ rfl, ?_,
      le_trans max_pos (le_max_left _ _)⟩
    · intro a ha
      rcases split_lt (hlen ▸ ha) with ha' | rfl
      · rw [getD_append_left _ (len ▸ ha')]; exact Nat.lt_succ_of_lt (lt a (len ▸ ha'))
      · rw [← len, getD_append_right]; exact Nat.lt_succ_self _
    · intro a ha
      refine iff_of_false (Nat.ne_of_lt (lt a (len ▸ ha))) ?_
      rintro (h | ⟨n, -, h2⟩)
      · omega
      · exact hnot n h2
    · intro n a ha hka
      rcases split_lt ha with ha' | rfl
      · rw [get_append_left c ha'] at hka; rw [getD_append_left _ (len ▸ ha')]; exact gi_some n a ha' hka
      · exact absurd hka (hnot n)
    · intro n x hx
      obtain ⟨a, ha, hka⟩ := gi_ex n x hx
      exact ⟨a, by simp; omega, by rw [get_append_left c ha]; exact hka⟩
    · intro n hn a ha hka
      rcases split_lt ha with ha' | rfl
      · rw [get_append_left c ha'] at hka; exact gi_none n hn a ha' hka
      · exact hnot n hka
    · intro n a ha hka
      rcases split_lt ha with ha' | rfl
      · rw [get_append_left c ha'] at hka ⊢; exact gw_some n a ha' hka
      · exact absurd hka (hnot n)
  | Global bus =>
    simp only [hk] at h
    have hkc : (P ++ [c])[P.length]?.map (·.kind) = some (.Global bus) := by simp [hk]
    have hG : ∀ a < P.length, ∀ n, (P ++ [c])[a]?.map (·.kind) = some (.Global n) →
        P[a]?.map (·.kind) = some (.Global n) := fun a ha n h => by rwa [get_append_left c ha] at h
    rcases hgi : lookupKey st.global_index bus with _ | x
    · -- A new bus: a fresh id, and no earlier lookup names it.
      have hnone := gi_none bus hgi
      have hgw : lookupKey st.global_width bus = none := (keys bus).1 hgi
      simp only [orInsert, hgi, hgw, ↓reduceIte, ne_eq, not_true_eq_false, Option.pure_def,
        Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨hlen, by simp; omega, ?_, eq_iff_ext len eq_iff ?_, ?_, ?_, ?_, ?_, wd' _ rfl, ?_,
        le_trans max_pos (le_max_left _ _)⟩
      · intro a ha
        rcases split_lt (hlen ▸ ha) with ha' | rfl
        · rw [getD_append_left _ (len ▸ ha')]; exact Nat.lt_succ_of_lt (lt a (len ▸ ha'))
        · rw [← len, getD_append_right]; exact Nat.lt_succ_self _
      · intro a ha
        refine iff_of_false (Nat.ne_of_lt (lt a (len ▸ ha))) ?_
        rintro (h | ⟨n, h1, h2⟩)
        · omega
        · rw [hkc, Option.some.injEq, Kind.Global.injEq] at h2
          subst h2
          exact hnone a ha (hG a ha _ h1)
      · intro n a ha hka
        rw [lookupKey_append]
        rcases split_lt ha with ha' | rfl
        · rw [getD_append_left _ (len ▸ ha'), gi_some n a ha' (hG a ha' n hka)]; rfl
        · rw [hkc, Option.some.injEq, Kind.Global.injEq] at hka
          subst hka
          rw [hgi, ← len, getD_append_right]; simp
      · intro n x hx
        rw [lookupKey_append] at hx
        rcases h' : lookupKey st.global_index n with _ | y
        · rw [h'] at hx
          by_cases hb : bus = n
          · subst hb; exact ⟨P.length, by simp, hkc⟩
          · simp [hb] at hx
        · obtain ⟨a, ha, hka⟩ := gi_ex n y h'
          exact ⟨a, by simp; omega, by rw [get_append_left c ha]; exact hka⟩
      · intro n hn a ha hka
        rw [lookupKey_append] at hn
        rcases split_lt ha with ha' | rfl
        · exact gi_none n (by revert hn; cases lookupKey st.global_index n <;> simp) a ha' (hG a ha' n hka)
        · rw [hkc, Option.some.injEq, Kind.Global.injEq] at hka
          subst hka; simp [hgi] at hn
      · intro n
        rw [lookupKey_append, lookupKey_append]
        have := keys n
        rcases h1 : lookupKey st.global_index n <;> rcases h2 : lookupKey st.global_width n <;>
          simp_all
      · intro n a ha hka
        rw [lookupKey_append]
        rcases split_lt ha with ha' | rfl
        · obtain ⟨v, hv, -⟩ := wd a ha'
          rw [get_append_left c ha', gw_some n a ha' (hG a ha' n hka), hv]; rfl
        · rw [hkc, Option.some.injEq, Kind.Global.injEq] at hka
          subst hka; simp [hgw, width, hw]
    · -- A known bus: the id of its first lookup, and the width that lookup fixed.
      obtain ⟨a0, ha0, hka0⟩ := gi_ex bus x hgi
      have hx : x = ids.getD a0 0 := by
        have := gi_some bus a0 ha0 hka0; rw [hgi] at this; exact Option.some.inj this
      obtain ⟨w0, hw0, -⟩ := wd a0 ha0
      have hgw : lookupKey st.global_width bus = some w0 := (gw_some bus a0 ha0 hka0).trans hw0
      simp only [orInsert, hgi, hgw, reduceCtorEq, ↓reduceIte] at h
      by_cases hww : w0 = w
      · subst hww
        simp only [ne_eq, not_true_eq_false, ↓reduceIte, Option.pure_def, Option.some.injEq,
          Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        refine ⟨hlen, by simp; omega, ?_, eq_iff_ext len eq_iff ?_, ?_, ?_, ?_, keys, wd' _ rfl, ?_,
          le_trans max_pos (le_max_left _ _)⟩
        · intro a ha
          rcases split_lt (hlen ▸ ha) with ha' | rfl
          · rw [getD_append_left _ (len ▸ ha')]; exact lt a (len ▸ ha')
          · rw [← len, getD_append_right, hx]; exact lt a0 (len ▸ ha0)
        · intro a ha
          rw [hx, eq_iff a (len ▸ ha) a0 (len ▸ ha0)]
          simp only [SameBus, get_append_left c ha, hkc, hka0, Option.some.injEq, Kind.Global.injEq]
          constructor
          · rintro (rfl | ⟨n, h1, rfl⟩)
            · exact .inr ⟨bus, hka0, rfl⟩
            · exact .inr ⟨_, h1, rfl⟩
          · rintro (h | ⟨n, h1, rfl⟩)
            · omega
            · exact .inr ⟨_, h1, rfl⟩
        · intro n a ha hka
          rcases split_lt ha with ha' | rfl
          · rw [getD_append_left _ (len ▸ ha')]; exact gi_some n a ha' (hG a ha' n hka)
          · rw [hkc, Option.some.injEq, Kind.Global.injEq] at hka
            subst hka
            rw [hgi, ← len, getD_append_right]
        · intro n x hx
          obtain ⟨a, ha, hka⟩ := gi_ex n x hx
          exact ⟨a, by simp; omega, by rw [get_append_left c ha]; exact hka⟩
        · intro n hn a ha hka
          rcases split_lt ha with ha' | rfl
          · exact gi_none n hn a ha' (hG a ha' n hka)
          · rw [hkc, Option.some.injEq, Kind.Global.injEq] at hka
            subst hka; simp [hgi] at hn
        · intro n a ha hka
          rcases split_lt ha with ha' | rfl
          · rw [get_append_left c ha']; exact gw_some n a ha' (hG a ha' n hka)
          · rw [hkc, Option.some.injEq, Kind.Global.injEq] at hka
            subst hka; simp [hgw, width, hw]
      · simp [hww] at h

/-- One lookup's step of the inner fold. -/
def stepIds (acc : List ℕ × LayoutState) (ctx : Lookup F) : Option (List ℕ × LayoutState) := do
  let (id, st) ← busId acc.2 ctx
  pure (acc.1 ++ [id], st)

/-- One instance's step of the outer fold. -/
def stepAir (acc : List (List ℕ) × LayoutState) (contexts : List (Lookup F)) :
    Option (List (List ℕ) × LayoutState) := do
  let (ids, st) ← contexts.foldlM stepIds ([], acc.2)
  pure (acc.1 ++ [ids], st)

theorem busIds_eq (all : List (List (Lookup F))) : busIds all = all.foldlM stepAir ([], ⟨[], [], 0, 1⟩) := rfl

theorem inner_inv {L : List (Lookup F)} {pre : List ℕ} {st : LayoutState} {P : List (Lookup F)}
    {idsP : List ℕ} {out : List ℕ} {st' : LayoutState} (hI : Inv P idsP st)
    (h : L.foldlM stepIds (pre, st) = some (out, st')) :
    ∃ new, out = pre ++ new ∧ new.length = L.length ∧ Inv (P ++ L) (idsP ++ new) st' := by
  induction L generalizing pre st P idsP with
  | nil => simp only [List.foldlM_nil, Option.pure_def, Option.some.injEq, Prod.mk.injEq] at h
           obtain ⟨rfl, rfl⟩ := h; exact ⟨[], by simp, rfl, by simpa using hI⟩
  | cons c L ih =>
    simp only [List.foldlM_cons, stepIds, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨⟨pre', st1⟩, ⟨⟨id, st1'⟩, hb, he⟩, h⟩ := h
    simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    obtain ⟨new, rfl, hl, hI'⟩ := ih (inv_step hI hb) h
    exact ⟨id :: new, by simp, by simp [hl], by simpa using hI'⟩

theorem outer_inv {all : List (List (Lookup F))} {acc : List (List ℕ)} {st : LayoutState}
    {P : List (Lookup F)} {idsP : List ℕ} {out : List (List ℕ)} {st' : LayoutState} (hI : Inv P idsP st)
    (h : all.foldlM stepAir (acc, st) = some (out, st')) :
    ∃ new, out = acc ++ new ∧ new.map List.length = all.map List.length ∧
      Inv (P ++ all.flatten) (idsP ++ new.flatten) st' := by
  induction all generalizing acc st P idsP with
  | nil => simp only [List.foldlM_nil, Option.pure_def, Option.some.injEq, Prod.mk.injEq] at h
           obtain ⟨rfl, rfl⟩ := h; exact ⟨[], by simp, rfl, by simpa using hI⟩
  | cons L all ih =>
    simp only [List.foldlM_cons, stepAir, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨⟨acc', st1⟩, ⟨⟨ids, st1'⟩, hb, he⟩, h⟩ := h
    simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    obtain ⟨n1, rfl, hl1, hI1⟩ := inner_inv hI hb
    obtain ⟨new, rfl, hl, hI'⟩ := ih hI1 h
    exact ⟨ids :: new, by simp, by simp [hl, hl1], by simpa using hI'⟩

/-- **The bus ids.**

When the layout's bookkeeping succeeds, it gives each instance one id per lookup.

Over the flattened lookups:

- two ids agree exactly when the lookups are the same one, or global lookups on the same bus
- every id is below the next free id, which is at most the number of lookups
- every lookup has a payload width, at most the widest payload W, and 1 <= W
- global lookups on one bus have one width. -/
theorem busIds_spec {all : List (List (Lookup F))} {ids : List (List ℕ)} {st : LayoutState}
    (h : busIds all = some (ids, st)) :
    ids.map List.length = all.map List.length ∧ Inv all.flatten ids.flatten st := by
  obtain ⟨new, rfl, hl, hI⟩ := outer_inv inv_nil h
  exact ⟨by simpa using hl, by simpa using hI⟩

theorem lt_of_mem_flatten {P : List (Lookup F)} {ids : List ℕ} {st : LayoutState} (hI : Inv P ids st)
    {b : ℕ} (hb : b ∈ ids) : b < st.next_bus := by
  obtain ⟨a, ha, rfl⟩ := List.getElem_of_mem hb
  have := hI.lt a ha
  rwa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ha, Option.getD_some] at this

/-- **The layout.**

With two challenges per lookup, lookup j of instance i reads two values:

- its bus offset alpha + (id + 1) beta^W, with W the widest payload
- then beta. -/
theorem lay_out_eq {K : Type} [Field K] {all : List (List (Lookup F))} {ids : List (List ℕ)}
    {st : LayoutState} (h : busIds all = some (ids, st)) (α β : K) :
    lay_out_lookup_challenges 2 all α β =
      some (ids.map fun l : List ℕ => l.flatMap fun b : ℕ => [α + ((b : K) + 1) * β ^ st.max_message_width, β]) := by
  have hI := (busIds_spec h).2
  have hW : st.max_message_width ≠ 0 := by have := hI.max_pos; omega
  simp only [lay_out_lookup_challenges, ne_eq, not_true_eq_false, ↓reduceIte, h, Plonky3Lean.Proofs.Lookup.challenges_new, hW,
    Option.bind_eq_bind, Option.bind_some, Option.pure_def, Option.some.injEq]
  refine List.map_congr_left fun l hl => List.flatMap_congr fun b hb => ?_
  have hb' := lt_of_mem_flatten hI (List.mem_flatten.2 ⟨l, hl, hb⟩)
  simp [List.getD_eq_getElem?_getD, hb']

/-- A gadget that does not read two challenges per lookup panics the layout. -/
theorem lay_out_num_challenges {K : Type} [Field K] {nc : ℕ} (h : nc ≠ 2)
    (all : List (List (Lookup F))) (α β : K) : lay_out_lookup_challenges nc all α β = none := by
  simp [lay_out_lookup_challenges, h]

/-! ## When the layout panics -/

/-- Every lookup has one payload width, and global lookups on one bus share it. -/
def WidthsOk (Q : List (Lookup F)) : Prop :=
  (∀ c ∈ Q, (width c).isSome) ∧
    ∀ c ∈ Q, ∀ d ∈ Q, ∀ n, c.kind = .Global n → d.kind = .Global n → width c = width d

theorem WidthsOk.left {Q R : List (Lookup F)} (h : WidthsOk (Q ++ R)) : WidthsOk Q :=
  ⟨fun c hc => h.1 c (by simp [hc]), fun c hc d hd => h.2 c (by simp [hc]) d (by simp [hd])⟩

theorem mem_iff_get {P : List (Lookup F)} {c : Lookup F} : c ∈ P ↔ ∃ a < P.length, P[a]? = some c := by
  constructor
  · intro h; obtain ⟨a, ha, rfl⟩ := List.getElem_of_mem h; exact ⟨a, ha, by simp [ha]⟩
  · rintro ⟨a, ha, h⟩; rw [List.getElem?_eq_getElem ha, Option.some.injEq] at h; exact h ▸ List.getElem_mem ha

theorem Inv.widthsOk {P : List (Lookup F)} {ids : List ℕ} {st : LayoutState} (hI : Inv P ids st) :
    WidthsOk P := by
  refine ⟨fun c hc => ?_, fun c hc d hd n hcn hdn => ?_⟩
  · obtain ⟨a, ha, hca⟩ := mem_iff_get.1 hc
    obtain ⟨w, hw, -⟩ := hI.wd a ha
    simp [hca] at hw; simp [hw]
  · obtain ⟨a, ha, hca⟩ := mem_iff_get.1 hc
    obtain ⟨b, hb, hdb⟩ := mem_iff_get.1 hd
    have h1 := hI.gw_some n a ha (by simp [hca, hcn])
    have h2 := hI.gw_some n b hb (by simp [hdb, hdn])
    rw [hca] at h1; rw [hdb] at h2
    simpa using h1.symm.trans h2

/-- Under the invariant, one step panics exactly when the new lookup breaks the width conditions. -/
theorem busId_none_iff {P : List (Lookup F)} {ids : List ℕ} {st : LayoutState} (hI : Inv P ids st)
    (c : Lookup F) : busId st c = none ↔ ¬ WidthsOk (P ++ [c]) := by
  have hok := hI.widthsOk
  -- The width conditions on P ++ [c], given those on P.
  have hiff : WidthsOk (P ++ [c]) ↔ (width c).isSome ∧
      ∀ d ∈ P, ∀ n, c.kind = .Global n → d.kind = .Global n → width d = width c := by
    constructor
    · intro h; exact ⟨h.1 c (by simp), fun d hd n hc hdn => h.2 d (by simp [hd]) c (by simp) n hdn hc⟩
    · rintro ⟨hw, hd⟩
      refine ⟨fun x hx => ?_, fun x hx y hy n hxn hyn => ?_⟩
      · simp only [List.mem_append, List.mem_singleton] at hx
        rcases hx with hx | rfl; exacts [hok.1 x hx, hw]
      · simp only [List.mem_append, List.mem_singleton] at hx hy
        rcases hx with hx | rfl <;> rcases hy with hy | rfl
        · exact hok.2 x hx y hy n hxn hyn
        · exact hd x hx n hyn hxn
        · exact (hd y hy n hxn hyn).symm
        · rfl
  rw [hiff]
  unfold busId
  rcases hw : assert_uniform_tuple_width c.elements with _ | w
  · simp [width, hw]
  · have hw' : width c = some w := hw
    simp only [hw', Option.isSome_some, true_and, Option.bind_eq_bind, Option.bind_some]
    cases hk : c.kind with
    | Local => simp
    | Global bus =>
      simp only [Kind.Global.injEq, forall_eq']
      rcases hgw : lookupKey st.global_width bus with _ | w0
      · -- A new bus: no earlier lookup names it, so nothing can disagree.
        have hgi : lookupKey st.global_index bus = none := (hI.keys bus).2 hgw
        simp only [orInsert, hgw, ne_eq, not_true_eq_false, ↓reduceIte, reduceCtorEq, false_iff,
          not_forall]
        rintro ⟨d, hd, hdk, -⟩
        obtain ⟨a, ha, hda⟩ := mem_iff_get.1 hd
        exact absurd (by simp [hda, hdk]) (hI.gi_none bus hgi a ha)
      · -- A known bus: its stored width is that of an earlier lookup on it.
        have hgi : lookupKey st.global_index bus ≠ none := fun h => by
          rw [(hI.keys bus).1 h] at hgw; cases hgw
        obtain ⟨x, hx⟩ := Option.ne_none_iff_exists'.1 hgi
        obtain ⟨a, ha, hka⟩ := hI.gi_ex bus x hx
        obtain ⟨d, hd⟩ : ∃ d, P[a]? = some d := ⟨P[a], by simp [ha]⟩
        have hdk : d.kind = .Global bus := by simpa [hd] using hka
        have hwd : width d = some w0 := by
          have := hI.gw_some bus a ha hka; rw [hgw, hd] at this; simpa using this.symm
        have hdP : d ∈ P := mem_iff_get.2 ⟨a, ha, hd⟩
        simp only [orInsert, hgw]
        by_cases h0 : w0 = w
        · subst h0
          simp only [ne_eq, not_true_eq_false, ↓reduceIte, reduceCtorEq, false_iff, not_forall]
          rintro ⟨e, he, hek, hne⟩
          exact hne ((hok.2 e he d hdP bus hek hdk).trans hwd)
        · simp only [ne_eq, h0, not_false_eq_true, ↓reduceIte, Option.bind_none, true_iff]
          exact fun hall => h0 (by simpa [hwd] using hall d hdP hdk)

theorem inner_none_iff {L : List (Lookup F)} {pre : List ℕ} {st : LayoutState} {P : List (Lookup F)}
    {idsP : List ℕ} (hI : Inv P idsP st) :
    L.foldlM stepIds (pre, st) = none ↔ ¬ WidthsOk (P ++ L) := by
  induction L generalizing pre st P idsP with
  | nil => simpa using hI.widthsOk
  | cons c L ih =>
    simp only [List.foldlM_cons, stepIds, Option.bind_eq_bind]
    rcases hb : busId st c with _ | ⟨id, st1⟩
    · simp only [Option.bind_none, true_iff]
      intro h
      exact (busId_none_iff hI c).1 hb (by simpa using (show WidthsOk ((P ++ [c]) ++ L) by simpa using h).left)
    · simp only [Option.bind_some, Option.pure_def]
      rw [ih (inv_step hI hb)]; simp

theorem outer_none_iff {all : List (List (Lookup F))} {acc : List (List ℕ)} {st : LayoutState}
    {P : List (Lookup F)} {idsP : List ℕ} (hI : Inv P idsP st) :
    all.foldlM stepAir (acc, st) = none ↔ ¬ WidthsOk (P ++ all.flatten) := by
  induction all generalizing acc st P idsP with
  | nil => simpa using hI.widthsOk
  | cons L all ih =>
    simp only [List.foldlM_cons, stepAir, Option.bind_eq_bind]
    rcases hb : L.foldlM stepIds ([], st) with _ | ⟨ids, st1⟩
    · simp only [Option.bind_none, true_iff]
      intro h
      exact (inner_none_iff hI).1 hb (by simpa using (show WidthsOk ((P ++ L) ++ all.flatten) by simpa using h).left)
    · obtain ⟨new, rfl, -, hI1⟩ := inner_inv hI hb
      simp only [Option.bind_some, Option.pure_def]
      rw [ih hI1]; simp

/-- **When the layout panics.**

With two challenges per lookup, the layout panics exactly when widths disagree in one of two places:

- the tuples of one lookup
- two global lookups on one bus. -/
theorem lay_out_none_iff {K : Type} [Field K] (all : List (List (Lookup F))) (α β : K) :
    lay_out_lookup_challenges 2 all α β = none ↔ ¬ WidthsOk all.flatten := by
  rcases h : busIds all with _ | ⟨ids, st⟩
  · have := (outer_none_iff (all := all) (acc := []) inv_nil).1 h
    simp only [List.nil_append] at this
    simp [lay_out_lookup_challenges, h, this]
  · rw [lay_out_eq h]
    simpa using (busIds_spec h).2.widthsOk

end Plonky3Lean.Proofs.BatchStark
