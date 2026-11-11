module

public import Plonky3Lean.Proofs.Bus.Plan

@[expose] public section

/-!
# What the planner builds

The planner reads each AIR's declarations and returns one plan.

Every declaration names a bus, a direction and a payload:

```text
    AIR a, declaration j:   bus "mem", push, payload of width w
        ->  domain "mem" of width w
        ->  one block of 2^(log height of a) leaves on the push side
```

This file proves that a returned plan is tied to its declarations:

- every declaration's bus is a domain of the plan, of the declaration's width
- every declaration owns exactly one block, of its AIR's height, on its side
- the blocks of a side are aligned, disjoint, and fit the logical leaf count
-/

namespace Plonky3Lean.Proofs.Bus

open p3_bus.plan.mirror p3_bus.mirror p3_bus.product.mirror

set_option linter.unusedSectionVars false

/-- The position the plan gives a bus name among its domains. -/
def busIndex (p : BusPlan) (nm : String) : ℕ := (p.domains.findIdx? (·.«name» = nm)).getD 0

/-- The block each declaration asks for, in caller order, before sorting. -/
def pendingOf {F : Type _} (p : BusPlan) (inputs : List (BusPlanInput F)) : List PendingBlock :=
  (inputs.zipIdx).flatMap fun (input, air) =>
    (input.interactions.zipIdx).map fun (interaction, declaration) =>
      (⟨busIndex p interaction.bus_name, interaction.direction, ⟨air, declaration⟩, input.log_height⟩ :
        PendingBlock)

/-- The sorted name widths the domains come from. -/
def sortedWidths (widths : List (String × ℕ)) : List (String × ℕ) :=
  widths.mergeSort fun a b => decide (a.1 ≤ b.1)

/-- **The planner's steps.**

A returned plan comes from:

- the recorded widths, whose sorted entries are its domains
- the block layout of its sorted pending blocks
- a logical leaf count covering both sides -/
theorem build_ok {F : Type _} {inputs : List (BusPlanInput F)} {p : BusPlan}
    (h : BusPlan.build inputs = .ok (some p)) :
    ∃ widths, collectWidths inputs = .ok widths ∧
      p.domains = ((sortedWidths widths).zipIdx).map (fun ((nm, payload_width), bus) =>
        (⟨nm, payload_width, bus + 1⟩ : BusDomain)) ∧
      ∃ c₀ c₁, layoutBlocks ((pendingOf p inputs).mergeSort pendingLe) = .ok (p.pushes, p.pulls, c₀, c₁) ∧
        p.geometry.non_padding_leaf_counts = (c₀, c₁) ∧
        c₀ ≤ p.geometry.logical_leaf_count ∧ c₁ ≤ p.geometry.logical_leaf_count := by
  unfold BusPlan.build at h
  split at h
  case h_2 => cases h
  split_ifs at h with h0
  · cases h
  obtain ⟨widths, hw, h⟩ := except_bind_ok h
  dsimp only at h
  split at h
  case h_2 => cases h
  split at h
  case h_2 => cases h
  split at h
  case h_2 => cases h
  obtain ⟨⟨pushes, pulls, c₀, c₁⟩, hl, h⟩ := except_bind_ok h
  dsimp only at h
  split at h
  case h_2 => cases h
  rename_i leaves hleaves
  split at h
  case h_2 => cases h
  injection h with h
  injection h with h
  subst h
  have hcover := hleaves
  unfold checked_next_power_of_two at hcover
  split_ifs at hcover <;>
  · replace hcover := (Option.some.inj hcover) ▸ Nat.le_pow_clog one_lt_two _
    refine ⟨widths, hw, rfl, c₀, c₁, hl, rfl, ?_, ?_⟩ <;> dsimp only at hcover ⊢ <;> omega

/-! ## The recorded widths -/

/-- A fold that succeeds moves its state along a preorder, and records each element it visits.

What it records survives every later step. -/
theorem foldlM_ok_records {α β ε : Type _} {f : β → α → Except ε β} {R : β → β → Prop}
    (hR : ∀ b, R b b) (hRt : ∀ a b c, R a b → R b c → R a c) {Q : α → β → Prop}
    (hQ : ∀ a b c, Q a b → R b c → Q a c) :
    ∀ (l : List α) (b r : β), (∀ a ∈ l, ∀ b b', f b a = .ok b' → R b b' ∧ Q a b') →
      l.foldlM f b = .ok r → R b r ∧ ∀ a ∈ l, Q a r
  | [], b, r, _, h => by
    simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at h; subst h
    exact ⟨hR b, by simp⟩
  | a :: l, b, r, hf, h => by
    rw [List.foldlM_cons] at h
    obtain ⟨b', hb', h⟩ := except_bind_ok h
    obtain ⟨hR1, hQ1⟩ := hf a List.mem_cons_self b b' hb'
    obtain ⟨hR2, hQ2⟩ := foldlM_ok_records hR hRt hQ l b' r
      (fun a ha => hf a (List.mem_cons_of_mem _ ha)) h
    refine ⟨hRt _ _ _ hR1 hR2, fun x hx => ?_⟩
    rcases List.mem_cons.1 hx with rfl | hx
    · exact hQ _ _ _ hQ1 hR2
    · exact hQ2 x hx

/-- How the width table grows: by appending, and never repeating a name. -/
def WidthsGrow (w w' : List (String × ℕ)) : Prop :=
  w <+: w' ∧ ((w.map Prod.fst).Nodup → (w'.map Prod.fst).Nodup)

theorem widthsGrow_refl (w : List (String × ℕ)) : WidthsGrow w w := ⟨List.prefix_refl _, id⟩

theorem widthsGrow_trans (a b c : List (String × ℕ)) (h1 : WidthsGrow a b) (h2 : WidthsGrow b c) :
    WidthsGrow a c := ⟨h1.1.trans h2.1, h2.2 ∘ h1.2⟩

/-- What a declaration leaves in the width table: a nonempty payload, and its name at its width. -/
def Recorded {F : Type _} (i : SymbolicBusInteraction F) (w : List (String × ℕ)) : Prop :=
  i.fields ≠ [] ∧ (i.bus_name, i.fields.length) ∈ w

theorem recorded_grow {F : Type _} (i : SymbolicBusInteraction F) (w w' : List (String × ℕ))
    (h : Recorded i w) (hg : WidthsGrow w w') : Recorded i w' :=
  ⟨h.1, hg.1.subset h.2⟩

/-- **The recorded widths.**

The width table names each bus once.

Every declaration has a nonempty payload, and its bus is recorded at its payload's width. -/
theorem collectWidths_spec {F : Type _} {inputs : List (BusPlanInput F)} {widths : List (String × ℕ)}
    (h : collectWidths inputs = .ok widths) :
    (widths.map Prod.fst).Nodup ∧ ∀ input ∈ inputs, ∀ i ∈ input.interactions, Recorded i widths := by
  unfold collectWidths at h
  have := foldlM_ok_records widthsGrow_refl widthsGrow_trans
    (Q := fun (x : BusPlanInput F × ℕ) w => ∀ i ∈ x.1.interactions, Recorded i w)
    (fun x b c hb hg i hi => recorded_grow i b c (hb i hi) hg) _ [] widths ?_ h
  · refine ⟨this.1.2 List.nodup_nil, fun input hin i hi => ?_⟩
    obtain ⟨k, hk⟩ := List.mem_iff_getElem?.1 hin
    exact this.2 (input, k) (List.mem_zipIdx_iff_getElem?.2 hk) i hi
  · rintro ⟨input, air⟩ - b b' hstep
    dsimp only at hstep
    split_ifs at hstep
    · exact absurd hstep (by simp [throw, throwThe, MonadExceptOf.throw, bind, Except.bind])
    have := foldlM_ok_records widthsGrow_refl widthsGrow_trans
      (Q := fun (x : SymbolicBusInteraction F × ℕ) w => Recorded x.1 w)
      (fun x b c hb hg => recorded_grow x.1 b c hb hg) _ b b' ?_ hstep
    · refine ⟨this.1, fun i hi => ?_⟩
      obtain ⟨k, hk⟩ := List.mem_iff_getElem?.1 hi
      exact this.2 (i, k) (List.mem_zipIdx_iff_getElem?.2 hk)
    · rintro ⟨i, decl⟩ - w w' hstep
      dsimp only at hstep
      split_ifs at hstep with hempty
      · exact absurd hstep (by simp [throw, throwThe, MonadExceptOf.throw, bind, Except.bind])
      split at hstep
      · exact absurd hstep (by simp [throw, throwThe, MonadExceptOf.throw, bind, Except.bind])
      obtain ⟨u, -, hstep⟩ := except_bind_ok hstep
      have hne : i.fields ≠ [] := by simpa using hempty
      split at hstep
      · rename_i expected hlk
        split_ifs at hstep with hw
        · exact absurd hstep (by simp [throw, throwThe, MonadExceptOf.throw, bind, Except.bind])
        simp only [pure, Except.pure, Except.ok.injEq, not_not] at hstep hw
        subst hstep hw
        obtain ⟨l₁, l₂, rfl, -⟩ := List.lookup_eq_some_iff.1 hlk
        exact ⟨widthsGrow_refl _, hne, by simp⟩
      · rename_i hlk
        simp only [pure, Except.pure, Except.ok.injEq] at hstep
        subst hstep
        refine ⟨⟨List.prefix_append _ _, fun hn => ?_⟩, hne, by simp⟩
        rw [List.map_append, List.nodup_append]
        refine ⟨hn, by simp, ?_⟩
        intro a ha b hb
        simp only [List.map_cons, List.map_nil, List.mem_singleton] at hb
        subst hb
        obtain ⟨⟨nm, w⟩, hmem, rfl⟩ := List.mem_map.1 ha
        have := List.lookup_eq_none_iff.1 hlk _ hmem
        exact fun he => by simp at this; exact this he.symm

/-! ## Every declaration's domain -/

/-- The domains a width table gives, in name order. -/
def domainsOf (widths : List (String × ℕ)) : List BusDomain :=
  ((sortedWidths widths).zipIdx).map fun ((nm, payload_width), bus) =>
    (⟨nm, payload_width, bus + 1⟩ : BusDomain)

/-- A recorded name is found among the domains, at its recorded width. -/
theorem domainsOf_find {widths : List (String × ℕ)} (hnd : (widths.map Prod.fst).Nodup) {nm : String}
    {w : ℕ} (hm : (nm, w) ∈ widths) :
    ∃ k, ∃ hk : k < (domainsOf widths).length, (domainsOf widths).findIdx? (·.«name» = nm) = some k ∧
      (domainsOf widths)[k].«name» = nm ∧ (domainsOf widths)[k].payload_width = w := by
  have hperm : (sortedWidths widths).Perm widths := List.mergeSort_perm _ _
  have hnd' : ((sortedWidths widths).map Prod.fst).Nodup := (hperm.map _).nodup_iff.2 hnd
  obtain ⟨j, hj, hjw⟩ := List.getElem_of_mem (hperm.mem_iff.2 hm)
  have hlen : (domainsOf widths).length = (sortedWidths widths).length := by simp [domainsOf]
  have hget : ∀ k (hk : k < (domainsOf widths).length),
      (domainsOf widths)[k] = ⟨(sortedWidths widths)[k].1, (sortedWidths widths)[k].2, k + 1⟩ := by
    intro k hk; simp [domainsOf]
  cases hf : (domainsOf widths).findIdx? (·.«name» = nm) with
  | none =>
    have := List.findIdx?_eq_none_iff.1 hf ((domainsOf widths)[j]'(by omega)) (List.getElem_mem _)
    simp [hget, hjw] at this
  | some k =>
    obtain ⟨hk, hkn, -⟩ := List.findIdx?_eq_some_iff_getElem.1 hf
    simp only [hget, decide_eq_true_eq] at hkn
    have hkj : k = j := by
      have := hnd'.getElem_inj_iff (i := k) (j := j) (hi := by simp; omega) (hj := by simp; omega)
      exact this.1 (by simp [hkn, hjw])
    subst hkj
    exact ⟨k, hk, rfl, by simp [hget, hjw], by simp [hget, hjw]⟩

/-- **Every declaration's domain.**

In a returned plan, each declaration's bus name is a domain of the plan.

That domain carries the declaration's payload width, and the payload is nonempty. -/
theorem build_domain {F : Type _} {inputs : List (BusPlanInput F)} {p : BusPlan}
    (h : BusPlan.build inputs = .ok (some p)) {input : BusPlanInput F} (hin : input ∈ inputs)
    {i : SymbolicBusInteraction F} (hi : i ∈ input.interactions) :
    ∃ hb : busIndex p i.bus_name < p.domains.length,
      p.domains[busIndex p i.bus_name].«name» = i.bus_name ∧
      p.domains[busIndex p i.bus_name].payload_width = i.fields.length ∧ i.fields ≠ [] := by
  obtain ⟨widths, hw, hdom, -⟩ := build_ok h
  obtain ⟨hnd, hrec⟩ := collectWidths_spec hw
  obtain ⟨hne, hm⟩ := hrec input hin i hi
  obtain ⟨k, hk, hf, hn, hpw⟩ := domainsOf_find hnd hm
  have hdom' : p.domains = domainsOf widths := hdom
  have hidx : busIndex p i.bus_name = k := by simp [busIndex, hdom', hf]
  subst hidx
  refine ⟨by rw [hdom']; exact hk, ?_⟩
  simp only [hdom']
  exact ⟨hn, hpw, hne⟩

/-! ## The blocks of each side -/

/-- A block without its offset: the request it answers. -/
def BusBlock.request (b : BusBlock) : PendingBlock := ⟨b.bus, b.direction, b.owner, b.log_height⟩

/-- The blocks of a side are laid end to end, and all end by a leaf count. -/
def Separated (L : List BusBlock) (c : ℕ) : Prop :=
  L.Pairwise (fun a b => a.offset + 2 ^ a.log_height ≤ b.offset) ∧
    ∀ b ∈ L, b.offset + 2 ^ b.log_height ≤ c

theorem separated_snoc {L : List BusBlock} {c : ℕ} (hs : Separated L c) (b : BusBlock)
    (hb : b.offset = c) : Separated (L ++ [b]) (c + 2 ^ b.log_height) := by
  refine ⟨List.pairwise_append.2 ⟨hs.1, by simp, fun x hx y hy => ?_⟩, fun x hx => ?_⟩
  · rw [List.mem_singleton.1 hy, hb]; exact hs.2 x hx
  · rcases List.mem_append.1 hx with hx | hx
    · exact le_trans (hs.2 x hx) (Nat.le_add_right _ _)
    · rw [List.mem_singleton.1 hx, hb]

/-- The layout loop sends each request to its side, in order, laid end to end. -/
theorem layout_sides : ∀ (l : List PendingBlock) (acc out : List BusBlock × List BusBlock × ℕ × ℕ),
    l.foldlM layoutStep acc = .ok out →
    out.1.map BusBlock.request = acc.1.map BusBlock.request ++ l.filter (·.direction = .Push) ∧
      out.2.1.map BusBlock.request = acc.2.1.map BusBlock.request ++ l.filter (·.direction = .Pull) ∧
      (Separated acc.1 acc.2.2.1 → Separated out.1 out.2.2.1) ∧
      (Separated acc.2.1 acc.2.2.2 → Separated out.2.1 out.2.2.2)
  | [], acc, out, h => by
    simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at h; subst h; simp
  | x :: l, acc, out, h => by
    rw [List.foldlM_cons] at h
    obtain ⟨acc', hstep, h⟩ := except_bind_ok h
    obtain ⟨h1, h2, h3, h4⟩ := layout_sides l acc' out h
    unfold layoutStep at hstep
    cases hd : x.direction <;>
      simp only [hd, BusDirection.index, ↓reduceIte, Nat.one_ne_zero, checked_add] at hstep
    · split_ifs at hstep
      simp only [pure, Except.pure, Except.ok.injEq] at hstep
      subst hstep
      refine ⟨?_, ?_, fun hs => h3 (separated_snoc hs _ rfl), h4⟩
      · rw [h1]; cases x; simp_all [BusBlock.request]
      · rw [h2]; simp [hd]
    · split_ifs at hstep
      simp only [pure, Except.pure, Except.ok.injEq] at hstep
      subst hstep
      refine ⟨?_, ?_, h3, fun hs => h4 (separated_snoc hs _ rfl)⟩
      · rw [h1]; simp [hd]
      · rw [h2]; cases x; simp_all [BusBlock.request]

/-- Each declaration asks for one block, so no owner repeats. -/
theorem pendingOf_owners_nodup {F : Type _} (p : BusPlan) (inputs : List (BusPlanInput F)) :
    ((pendingOf p inputs).map (·.owner)).Nodup := by
  have hnd : ∀ {α : Type _} (l : List α), (l.zipIdx.map Prod.snd).Nodup := fun l => by
    rw [List.zipIdx_map_snd]; exact List.nodup_range'
  have hsnd : ∀ {α : Type _} (l : List α), l.zipIdx.Pairwise (fun x y => x.2 ≠ y.2) := fun l =>
    List.pairwise_map.1 (hnd l)
  simp only [pendingOf, List.map_flatMap, List.map_map]
  refine List.nodup_flatMap.2 ⟨fun ⟨input, air⟩ _ => ?_, (hsnd inputs).imp fun {x y} hxy => ?_⟩
  · apply List.Nodup.of_map BusBlockOwner.declaration
    simpa [List.map_map, Function.comp_def] using hnd input.interactions
  · simp only [Function.onFun, List.disjoint_left, List.mem_map, Function.comp_apply]
    rintro _ ⟨u, -, rfl⟩ ⟨v, -, h⟩
    exact hxy (congrArg BusBlockOwner.air h).symm

/-- The request of the declaration at a position is among the pending blocks. -/
theorem mem_pendingOf {F : Type _} (p : BusPlan) {inputs : List (BusPlanInput F)} {a j : ℕ}
    {input : BusPlanInput F} {i : SymbolicBusInteraction F} (ha : inputs[a]? = some input)
    (hj : input.interactions[j]? = some i) :
    (⟨busIndex p i.bus_name, i.direction, ⟨a, j⟩, input.log_height⟩ : PendingBlock) ∈
      pendingOf p inputs := by
  simp only [pendingOf, List.mem_flatMap, List.mem_map]
  exact ⟨(input, a), List.mk_mem_zipIdx_iff_getElem?.2 ha, (i, j),
    List.mk_mem_zipIdx_iff_getElem?.2 hj, rfl⟩

/-- In a list without repeated keys, the entries of one member's key are that member alone. -/
theorem filter_key_singleton {α κ : Type _} [DecidableEq κ] (key : α → κ) :
    ∀ {L : List α} {x : α}, (L.map key).Nodup → x ∈ L → L.filter (key · = key x) = [x]
  | [], _, _, hx => absurd hx (by simp)
  | y :: L, x, hnd, hx => by
    rw [List.map_cons, List.nodup_cons] at hnd
    have hnone : ∀ z ∈ L, key z ≠ key y := fun z hz he => hnd.1 (he ▸ List.mem_map_of_mem hz)
    rcases List.mem_cons.1 hx with rfl | hx
    · simp only [List.filter_cons, decide_true, ↓reduceIte, List.cons.injEq, true_and]
      exact List.filter_eq_nil_iff.2 fun z hz => by simpa using hnone z hz
    · have hne : key y ≠ key x := fun he => hnone x hx he.symm
      simp [hne, filter_key_singleton key hnd.2 hx]

/-- **The blocks of a plan.**

In a returned plan:

- the pushes lie on the push side and the pulls on the pull side
- forgetting offsets, the blocks are the declarations' requests, rearranged
- each side's blocks are laid end to end and fit the logical leaf count
- each block starts at a multiple of its own height -/
theorem build_blocks {F : Type _} {inputs : List (BusPlanInput F)} {p : BusPlan}
    (h : BusPlan.build inputs = .ok (some p)) :
    (∀ b ∈ p.pushes, b.direction = .Push) ∧ (∀ b ∈ p.pulls, b.direction = .Pull) ∧
      ((p.pushes ++ p.pulls).map BusBlock.request).Perm (pendingOf p inputs) ∧
      Separated p.pushes p.geometry.logical_leaf_count ∧
      Separated p.pulls p.geometry.logical_leaf_count ∧
      ∀ b ∈ p.pushes ++ p.pulls, 2 ^ b.log_height ∣ b.offset := by
  obtain ⟨-, -, -, c₀, c₁, hl, -, h₀, h₁⟩ := build_ok h
  obtain ⟨hpush, hpull, hs₀, hs₁⟩ := layout_sides _ _ _ hl
  simp only [List.map_nil, List.nil_append] at hpush hpull
  have hsep : ∀ {L : List BusBlock} {c c' : ℕ}, Separated L c → c ≤ c' → Separated L c' :=
    fun hs hc => ⟨hs.1, fun b hb => le_trans (hs.2 b hb) hc⟩
  have hdir : ∀ (L : List BusBlock) (d : BusDirection),
      L.map BusBlock.request = ((pendingOf p inputs).mergeSort pendingLe).filter (·.direction = d) →
      ∀ b ∈ L, b.direction = d := fun L d hL b hb => by
    have := hL ▸ List.mem_map_of_mem (f := BusBlock.request) hb
    have h2 := (List.mem_filter.1 this).2
    simp only [BusBlock.request] at h2
    exact of_decide_eq_true h2
  refine ⟨hdir _ _ hpush, hdir _ _ hpull, ?_, hsep (hs₀ ⟨by simp, by simp⟩) h₀,
    hsep (hs₁ ⟨by simp, by simp⟩) h₁, layoutBlocks_aligned _ hl⟩
  rw [List.map_append, hpush, hpull]
  refine List.Perm.trans ?_ (List.mergeSort_perm (pendingOf p inputs) pendingLe)
  convert List.filter_append_perm (fun x : PendingBlock => decide (x.direction = .Push)) _ using 2
  exact List.filter_congr fun x _ => by cases x.direction <;> simp

/-- **Every declaration owns exactly one block.**

In a returned plan, the blocks owned by the declaration at a position are a single block.

That block names the declaration's bus, its direction and its AIR's height. -/
theorem build_block_unique {F : Type _} {inputs : List (BusPlanInput F)} {p : BusPlan}
    (h : BusPlan.build inputs = .ok (some p)) {a j : ℕ} {input : BusPlanInput F}
    {i : SymbolicBusInteraction F} (ha : inputs[a]? = some input) (hj : input.interactions[j]? = some i) :
    ((p.pushes ++ p.pulls).filter (·.owner = ⟨a, j⟩)).map BusBlock.request =
      [⟨busIndex p i.bus_name, i.direction, ⟨a, j⟩, input.log_height⟩] := by
  obtain ⟨-, -, hperm, -⟩ := build_blocks h
  have hmem := mem_pendingOf p ha hj
  have hone := filter_key_singleton (·.owner) (pendingOf_owners_nodup p inputs) hmem
  rw [← List.perm_singleton, ← hone]
  have := hperm.filter (fun r : PendingBlock => decide (r.owner = ⟨a, j⟩))
  rw [List.filter_map] at this
  exact this

/-! ## Soundness from the declarations -/

/-- A named payload some declaration of the inputs could send: its bus is declared, at its width. -/
def Declared {F K : Type _} (inputs : List (BusPlanInput F)) (d : String × List K) : Prop :=
  ∃ input ∈ inputs, ∃ i ∈ input.interactions, i.bus_name = d.1 ∧ d.2.length = i.fields.length

/-- **Soundness of the bus, from the declarations.**

Take the plan the planner returns for some inputs.

Take pushed and pulled named payloads that the inputs declare, and that are not a permutation of each other.

Their padded tuples have equal grand products on at most max(1, m) N |K|^m of the |K|^(m + 1) challenges. -/
theorem bus_soundness_of_build {F K : Type _} [Field K] [Fintype K] [DecidableEq K]
    {inputs : List (BusPlanInput F)} {p : BusPlan} (h : BusPlan.build inputs = .ok (some p))
    {push pull : List (String × List K)} (hpush : ∀ d ∈ push, Declared inputs d)
    (hpull : ∀ d ∈ pull, Declared inputs d) (hperm : ¬ push.Perm pull) {N : ℕ}
    (hN : push.length ≤ N) (hN' : pull.length ≤ N) :
    Finset.card {x : K × (Fin p.geometry.tuple_variables → K) |
      Plonky3Lean.Spec.Bus.grandProduct x.1 (List.ofFn x.2)
          (push.map fun d => tupleOf p (busIndex p d.1) d.2) =
        Plonky3Lean.Spec.Bus.grandProduct x.1 (List.ofFn x.2)
          (pull.map fun d => tupleOf p (busIndex p d.1) d.2)}
      ≤ max 1 p.geometry.tuple_variables * N * Fintype.card K ^ p.geometry.tuple_variables := by
  let idx : String × List K → ℕ × List K := fun d => (busIndex p d.1, d.2)
  -- A declared name is the name of the domain it indexes.
  have hdecl : ∀ d : String × List K, Declared inputs d → ∃ hb : busIndex p d.1 < p.domains.length,
      p.domains[busIndex p d.1].«name» = d.1 ∧ d.2.length = p.domains[busIndex p d.1].payload_width := by
    rintro ⟨nm, pl⟩ ⟨input, hin, i, hi, hn, hl⟩
    obtain ⟨hb, hname, hw, -⟩ := build_domain h hin hi
    simp only at hn hl ⊢
    subst hn
    exact ⟨hb, hname, hl.trans hw.symm⟩
  have hfits : ∀ d, Declared inputs d → Fits p (idx d) := fun d hd => by
    obtain ⟨hb, -, hl⟩ := hdecl d hd
    exact ⟨hb, hl⟩
  have := Plonky3Lean.Proofs.Bus.bus_soundness (build_wf h) (push := push.map idx)
    (pull := pull.map idx)
    (fun _ hd => by obtain ⟨d, hd', rfl⟩ := List.mem_map.1 hd; exact hfits d (hpush d hd'))
    (fun _ hd => by obtain ⟨d, hd', rfl⟩ := List.mem_map.1 hd; exact hfits d (hpull d hd'))
    (fun hp => hperm (perm_of_map_perm (fun a ha b hb he => ?_) hp))
    (by simpa using hN) (by simpa using hN')
  · simpa [List.map_map, Function.comp_def, idx] using this
  -- Equal indices of declared names mean equal names.
  have hd : ∀ x ∈ push ++ pull, Declared inputs x := fun x hx => by
    rcases List.mem_append.1 hx with hx | hx; exacts [hpush x hx, hpull x hx]
  obtain ⟨_, ha', _⟩ := hdecl a (hd a ha)
  obtain ⟨_, hb', _⟩ := hdecl b (hd b hb)
  simp only [idx, Prod.mk.injEq] at he
  have : a.1 = b.1 := by rw [← ha', ← hb']; simp only [he.1]
  exact Prod.ext this he.2

end Plonky3Lean.Proofs.Bus
