module

public import Plonky3Lean.Proofs.Bus.RamEval
public import Plonky3Lean.Proofs.Bus.Memory

@[expose] public section

/-!
# Read-write memory consistency

A trace of a self-contained memory is accepted when every row's constraints vanish.

The selectors are p3-air's: the first row, the last row, and every transition.

Each row decodes to an access:

- the operation marker 1 is a write
- the cell and clock digits are read least significant first
- the value is its components.

An accepted trace is sorted strictly by cell, then by clock.

Every read returns the value of the access above it in its cell's run, or zero at the run's start.

So the decoded trace is a consistent memory starting from zero, and so is every permutation of it.

That is what balancing the access channel against the machine's chips provides.
-/

namespace Plonky3Lean.Proofs.Bus

open p3_bus.ram.mirror p3_bus.mirror p3_air.builder.mirror Plonky3Lean.Spec.Bus Finset

set_option linter.unusedSectionVars false

variable {F : Type _} [Field F] [DecidableEq F]

/-- The access a row of the sorted trace holds. -/
def decode (L : RamLayout) (row : List F) : Access (List F) where
  write := decide (row.getD L.operation 0 = 1)
  addr := pv (row.drop L.address) L.address_bits
  time := pv (row.drop L.timestamp) L.timestamp_bits
  value := (row.drop L.value).take L.value_width

/-- The selectors of row i of a trace of height n: the first row, the last row, and every row but the last. -/
def rowSelectors (n i : ℕ) : F × F × F :=
  (if i = 0 then 1 else 0, if i = n - 1 then 1 else 0, if i ≠ n - 1 then 1 else 0)

/-- **An accepted trace.**

Every row has the AIR's width.

On every row the evaluation succeeds with all asserted values zero. -/
def Accepted (air : RamAir) (rows : List (List F)) : Prop :=
  (∀ r ∈ rows, r.length = air.layout.width) ∧
  ∀ (i : ℕ) (hi : i < rows.length), ∃ s : Collect F,
    air.eval (rowBuilder ⟨rows[i], rows[(i + 1) % rows.length]'(Nat.mod_lt _ (by omega))⟩
      (rowSelectors rows.length i).1 (rowSelectors rows.length i).2.1
      (rowSelectors rows.length i).2.2) ⟨[], []⟩ = some s ∧ s.Holds

theorem pv_slice (l : List F) (a n : ℕ) : pv ((l.drop a).take n) n = pv (l.drop a) n :=
  sum_congr rfl fun i hi => by
    simp [List.getD_eq_getElem?_getD, mem_range.1 hi]

theorem pv_drop_congr {l l' : List F} {a n : ℕ}
    (h : ∀ i < n, l.getD (a + i) 0 = l'.getD (a + i) 0) : pv (l.drop a) n = pv (l'.drop a) n :=
  sum_congr rfl fun i hi => by
    simp only [List.getD_eq_getElem?_getD, List.getElem?_drop] at h ⊢
    rw [h i (mem_range.1 hi)]

theorem bits_of_bool {L : RamLayout} {row : List F} (h : ∀ x ∈ boolAsserts L row, x = 0) :
    (∀ i < L.address_bits, IsBit (row.getD (L.address + i) 0)) ∧
    (∀ i < L.timestamp_bits, IsBit (row.getD (L.timestamp + i) 0)) ∧
    (∀ i < L.compare_bits, IsBit (row.getD (L.compare_delta + i) 0)) :=
  ⟨fun i hi => bc_eq_zero.1 (h _ (by simp [boolAsserts]; exact Or.inl ⟨i, hi, rfl⟩)),
   fun i hi => bc_eq_zero.1 (h _ (by simp [boolAsserts]; exact Or.inr (Or.inl ⟨i, hi, rfl⟩))),
   fun i hi => bc_eq_zero.1 (h _ (by simp [boolAsserts]; exact Or.inr (Or.inr ⟨i, hi, rfl⟩)))⟩

theorem value_ext {L : RamLayout} {r r' : List F} (hr : L.value + L.value_width ≤ r.length)
    (hr' : L.value + L.value_width ≤ r'.length)
    (h : ∀ k < L.value_width, r'.getD (L.value + k) 0 = r.getD (L.value + k) 0) :
    (r'.drop L.value).take L.value_width = (r.drop L.value).take L.value_width :=
  List.ext_getElem (by simp; omega) fun k h1 h2 => by
    have hk : k < L.value_width := by simp at h1; omega
    have := h k hk
    simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega : L.value + k < r'.length),
      List.getElem?_eq_getElem (by omega : L.value + k < r.length), Option.getD_some] at this
    simpa using this

/-- **One transition of a self-contained proof.**

Take two rows whose booleanity groups vanish, with a vanishing order group on the transition.

Then:

- they are strictly ordered by cell then clock
- a read in the lower row returns the upper row's value on the same cell
- it returns zero on a new cell. -/
theorem transition_sound {st : RamStatement} (hv : st.validate = .ok ()) {cur nxt : List F}
    (hc : cur.length = (stdLayout st).width) (hn : nxt.length = (stdLayout st).width) (first : F)
    (hbc : ∀ x ∈ boolAsserts (stdLayout st) cur, x = 0)
    (hbn : ∀ x ∈ boolAsserts (stdLayout st) nxt, x = 0)
    (hord : ∀ x ∈ orderAsserts (stdLayout st) first 1 cur nxt, x = 0) :
    Before (decode (stdLayout st) cur) (decode (stdLayout st) nxt) ∧
      ReadStep (fun _ => List.replicate st.value_width 0) (decode (stdLayout st) cur)
        (decode (stdLayout st) nxt) := by
  obtain ⟨-, hab, -, htb, -, -⟩ := validate_dims hv
  have hlay : (stdLayout st).address_bits = st.address_bits ∧ (stdLayout st).timestamp_bits = st.timestamp_bits ∧
      (stdLayout st).compare_bits = max st.address_bits st.timestamp_bits ∧ (stdLayout st).value_width = st.value_width ∧
      (stdLayout st).address + (stdLayout st).address_bits ≤ cur.length ∧ (stdLayout st).address + (stdLayout st).address_bits ≤ nxt.length ∧
      (stdLayout st).timestamp + (stdLayout st).timestamp_bits ≤ cur.length ∧ (stdLayout st).timestamp + (stdLayout st).timestamp_bits ≤ nxt.length ∧
      (stdLayout st).value + (stdLayout st).value_width ≤ cur.length ∧ (stdLayout st).value + (stdLayout st).value_width ≤ nxt.length ∧
      (stdLayout st).compare_delta + (stdLayout st).compare_bits ≤ nxt.length := by
    simp [stdLayout] at hc hn ⊢; omega
  obtain ⟨hla, hlt, hlc, hlv, h1, h2, h3, h4, h5, h6, h7⟩ := hlay
  obtain ⟨bca, bct, -⟩ := bits_of_bool hbc
  obtain ⟨-, -, bnd⟩ := bits_of_bool hbn
  set same := nxt.getD (stdLayout st).same_address 0
  -- The cell-equality, continuity and comparison parts of the order group.
  have hA : ∀ b < (stdLayout st).address_bits, same * (nxt.getD ((stdLayout st).address + b) 0 -
      cur.getD ((stdLayout st).address + b) 0) = 0 := fun b hb => by
    have := hord _ (by
      simp only [orderAsserts]
      exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
        (List.mem_append_right _ (List.mem_map.2 ⟨b, List.mem_range.2 hb, rfl⟩)))))
    rwa [one_mul] at this
  have hV : ∀ k < (stdLayout st).value_width, (1 - nxt.getD (stdLayout st).operation 0) *
      (nxt.getD ((stdLayout st).value + k) 0 - same * cur.getD ((stdLayout st).value + k) 0) = 0 :=
    fun k hk => by
      have := hord _ (by
        simp only [orderAsserts]
        exact List.mem_append_right _ (List.mem_map.2 ⟨k, List.mem_range.2 hk, rfl⟩))
      rwa [one_mul] at this
  have hS : ∀ en : F, en ≠ 0 → ∀ (a n : ℕ), n ≤ (stdLayout st).compare_bits → 0 < n →
      a + n ≤ cur.length → a + n ≤ nxt.length → (∀ i < n, IsBit (cur.getD (a + i) 0)) →
      (∀ x ∈ strictAsserts 1 en ((cur.drop a).take n) ((nxt.drop a).take n)
        ((nxt.drop (stdLayout st).compare_delta).take (stdLayout st).compare_bits)
        ((nxt.drop (stdLayout st).compare_carry).take ((stdLayout st).compare_bits + 1))
        ((nxt.drop (stdLayout st).compare_nonzero).take (stdLayout st).compare_bits), x = 0) →
      pv (nxt.drop a) n = pv (cur.drop a) n + pv ((nxt.drop (stdLayout st).compare_delta).take
        (stdLayout st).compare_bits) n ∧
      0 < pv ((nxt.drop (stdLayout st).compare_delta).take (stdLayout st).compare_bits) n := by
    intro en hen a n hn hn0 ha ha' hbits hz
    have hlen := length_slice (l := cur) (a := a) ha
    have := strict_increase_sound one_ne_zero hen (by omega)
      (fun i hi => by rw [getD_slice (by omega)]; exact hbits i (by omega))
      (fun i hi => by rw [getD_slice (by omega)]; exact bnd i (by omega)) hz
    rwa [hlen, pv_slice, pv_slice] at this
  have hS1 : ∀ x ∈ strictAsserts 1 (1 - same) ((cur.drop (stdLayout st).address).take
      (stdLayout st).address_bits) ((nxt.drop (stdLayout st).address).take (stdLayout st).address_bits)
      ((nxt.drop (stdLayout st).compare_delta).take (stdLayout st).compare_bits)
      ((nxt.drop (stdLayout st).compare_carry).take ((stdLayout st).compare_bits + 1))
      ((nxt.drop (stdLayout st).compare_nonzero).take (stdLayout st).compare_bits), x = 0 :=
    fun x hx => hord x (by
      simp only [orderAsserts]
      exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ hx)))
  have hS2 : ∀ x ∈ strictAsserts 1 same ((cur.drop (stdLayout st).timestamp).take
      (stdLayout st).timestamp_bits) ((nxt.drop (stdLayout st).timestamp).take
        (stdLayout st).timestamp_bits)
      ((nxt.drop (stdLayout st).compare_delta).take (stdLayout st).compare_bits)
      ((nxt.drop (stdLayout st).compare_carry).take ((stdLayout st).compare_bits + 1))
      ((nxt.drop (stdLayout st).compare_nonzero).take (stdLayout st).compare_bits), x = 0 :=
    fun x hx => hord x (by
      simp only [orderAsserts]
      exact List.mem_append_left _ (List.mem_append_right _ hx))
  have hca : (stdLayout st).address_bits ≤ (stdLayout st).compare_bits := by simp [stdLayout]
  have hct : (stdLayout st).timestamp_bits ≤ (stdLayout st).compare_bits := by simp [stdLayout]
  have hab' : 0 < (stdLayout st).address_bits := by simp [stdLayout]; omega
  have htb' : 0 < (stdLayout st).timestamp_bits := by simp [stdLayout]; omega
  -- Equal digits give equal cells.
  have heq : same ≠ 0 → (decode (stdLayout st) nxt).addr = (decode (stdLayout st) cur).addr :=
    fun h => pv_drop_congr fun b hb => sub_eq_zero.1 ((mul_eq_zero.1 (hA b hb)).resolve_left h)
  -- A read of a new cell sees zero.
  -- A read of the same cell sees the row above.
  have hval : nxt.getD (stdLayout st).operation 0 ≠ 1 → ∀ k < (stdLayout st).value_width,
      nxt.getD ((stdLayout st).value + k) 0 = same * cur.getD ((stdLayout st).value + k) 0 :=
    fun hop k hk => sub_eq_zero.1 ((mul_eq_zero.1 (hV k hk)).resolve_left
      (sub_ne_zero.2 (Ne.symm hop)))
  have hread : (decode (stdLayout st) nxt).write = false →
      nxt.getD (stdLayout st).operation 0 ≠ 1 := by simp [decode]
  by_cases h0 : same = 0
  · -- A new cell: the cell strictly increases, and a read sees zero.
    obtain ⟨hpv, hpos⟩ := hS 1 one_ne_zero _ _ hca hab' h1 h2 bca (by simpa [h0] using hS1)
    have hlt : (decode (stdLayout st) cur).addr < (decode (stdLayout st) nxt).addr := by
      simp only [decode]; omega
    refine ⟨Or.inl hlt, fun hw => ?_⟩
    rw [ite_eq_right (Nat.ne_of_gt hlt)]
    refine List.ext_getElem (by
      simp only [decode, List.length_take, List.length_drop, List.length_replicate]; omega)
      fun k hk _ => ?_
    have hk' : k < (stdLayout st).value_width := by
      simp only [decode, List.length_take, List.length_drop] at hk; omega
    have := hval (hread hw) k hk'
    rw [h0, zero_mul] at this
    simp only [decode, List.getElem_take, List.getElem_drop, List.getElem_replicate]
    rw [← this, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some]
  by_cases h1' : same = 1
  · -- The same cell: the clock strictly increases, and a read sees the row above.
    obtain ⟨hpv, hpos⟩ := hS same h0 _ _ hct htb' h3 h4 bct hS2
    have he := heq h0
    refine ⟨Or.inr ⟨he.symm, by simp only [decode]; omega⟩, fun hw => ?_⟩
    rw [ite_eq_left he]
    exact value_ext h5 h6 fun k hk => by rw [hval (hread hw) k hk, h1', one_mul]
  · -- Any other flag would run both comparisons, which no pair of equal cells satisfies.
    obtain ⟨hpv, hpos⟩ := hS (1 - same) (sub_ne_zero.2 (Ne.symm h1')) _ _ hca hab' h1 h2 bca hS1
    have he := heq h0
    simp only [decode] at he
    omega

theorem air_of_new {st : RamStatement} {air : RamAir} (h : RamAir.new st = .ok air) :
    st.validate = .ok () ∧ air = RamAir.mk st (stdLayout st) := by
  unfold RamAir.new at h
  cases hl : RamLayout.new st with
  | error e => simp [hl] at h
  | ok L =>
    simp only [hl] at h
    cases h
    obtain ⟨hv, rfl⟩ := layout_of_new hl
    exact ⟨hv, rfl⟩

/-- **Memory consistency of a self-contained memory.**

Take an accepted trace of the AIR of a valid self-contained statement.

It decodes to a consistent memory starting from zero:

- on each cell, times are distinct
- every read returns the latest earlier write, or zero. -/
theorem accepted_consistent {st : RamStatement} (hsp : st.boundary = .SingleProof) {air : RamAir}
    (hair : RamAir.new st = .ok air) {rows : List (List F)} (hacc : Accepted air rows) :
    Consistent (fun _ => List.replicate st.value_width 0) (rows.map (decode air.layout)) := by
  obtain ⟨hv, rfl⟩ := air_of_new hair
  obtain ⟨hw, hrow⟩ := hacc
  -- Every row's groups vanish, with its own selectors.
  have hold : ∀ i (hi : i < rows.length),
      (∀ x ∈ boolAsserts (stdLayout st) rows[i], x = 0) ∧
      (∀ x ∈ orderAsserts (stdLayout st) (rowSelectors rows.length i).1
        (rowSelectors rows.length i).2.2 rows[i]
        (rows[(i + 1) % rows.length]'(Nat.mod_lt _ (by omega))), x = 0) := fun i hi => by
    obtain ⟨s, hs, hH⟩ := hrow i hi
    exact row_holds hsp hv (hw _ (List.getElem_mem _)) (hw _ (List.getElem_mem _)) hs hH
  have htr : ∀ i (hi : i + 1 < rows.length),
      Before (decode (stdLayout st) rows[i]) (decode (stdLayout st) rows[i + 1]) ∧
      ReadStep (fun _ => List.replicate st.value_width 0) (decode (stdLayout st) rows[i])
        (decode (stdLayout st) rows[i + 1]) := fun i hi => by
    obtain ⟨hb, ho⟩ := hold i (by omega)
    have hsel : (rowSelectors (F := F) rows.length i).2.2 = 1 := by
      simp [rowSelectors]; omega
    have hmod : (i + 1) % rows.length = i + 1 := Nat.mod_eq_of_lt hi
    simp only [hsel, hmod] at ho
    exact transition_sound hv (hw _ (List.getElem_mem _)) (hw _ (List.getElem_mem _)) _ hb
      (hold (i + 1) hi).1 ho
  refine consistent_of_sorted _ (List.isChain_iff_getElem.2 fun i hi => ?_) (fun y hy hr => ?_)
    (List.isChain_iff_getElem.2 fun i hi => ?_)
  · simp only [List.length_map] at hi
    simpa using (htr i hi).1
  · -- The first row opens a run, so a read there returns zero.
    cases hrows : rows with
    | nil => simp [hrows] at hy
    | cons r rs =>
      simp only [hrows, List.map_cons, List.head?_cons, Option.mem_def, Option.some.injEq] at hy
      subst hy
      have h0 := hold 0 (by simp [hrows])
      simp only [hrows, List.getElem_cons_zero] at h0
      have hsel : (rowSelectors (F := F) (rs.length + 1) 0).1 = 1 := by simp [rowSelectors]
      have hst : ∀ k < (stdLayout st).value_width,
          (1 - r.getD (stdLayout st).operation 0) * r.getD ((stdLayout st).value + k) 0 = 0 :=
        fun k hk => by
          have := h0.2 _ (by
            simp only [orderAsserts]
            exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
              (List.mem_append_left _ (List.mem_append_right _
                (List.mem_map.2 ⟨_, List.mem_map.2 ⟨k, List.mem_range.2 hk, rfl⟩, rfl⟩))))))
          simpa [List.length_cons, hsel] using this
      have hop : r.getD (stdLayout st).operation 0 ≠ 1 := by simpa [decode] using hr
      have hwr := hw r (by simp [hrows])
      have hlen : (stdLayout st).value + (stdLayout st).value_width ≤ r.length ∧
          (stdLayout st).value_width = st.value_width := by
        simp [stdLayout] at hwr ⊢; omega
      refine List.ext_getElem (by
        simp only [decode, List.length_take, List.length_drop, List.length_replicate]; omega)
        fun k hk _ => ?_
      have hk' : k < (stdLayout st).value_width := by
        simp only [decode, List.length_take, List.length_drop] at hk; omega
      have := (mul_eq_zero.1 (hst k hk')).resolve_left (sub_ne_zero.2 (Ne.symm hop))
      simp only [decode, List.getElem_take, List.getElem_drop, List.getElem_replicate]
      rw [← this, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some]
  · simp only [List.length_map] at hi
    simpa using (htr i hi).2

/-- The same consistency holds for every reordering of the accesses.

That is what balancing the access channel against the machine's chips provides. -/
theorem accepted_consistent_perm {st : RamStatement} (hsp : st.boundary = .SingleProof)
    {air : RamAir} (hair : RamAir.new st = .ok air) {rows : List (List F)} (hacc : Accepted air rows)
    {machine : List (Access (List F))} (hperm : (rows.map (decode air.layout)).Perm machine) :
    Consistent (fun _ => List.replicate st.value_width 0) machine :=
  Consistent.perm hperm (accepted_consistent hsp hair hacc)

end Plonky3Lean.Proofs.Bus
