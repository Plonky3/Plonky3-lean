module

public import Plonky3Lean.Proofs.BatchStark.Soundness

@[expose] public section

/-!
# The message count of a batch

The bus soundness bound counts N, the messages of every row of every instance.

With instance i of height h_i emitting at most n_i messages per row:

```text
    N <= sum_i n_i h_i <= (sum_i n_i) 2^L,     every h_i <= 2^L
```

p3-security charges N (W + 2) / |K| with the per-row count summed over the instances and the largest height.

So it never charges less than the exact count of a batch with several heights.
-/

set_option linter.unusedSectionVars false

namespace Plonky3Lean.Proofs.BatchStark

open p3_batch_stark.transcript.mirror p3_lookup.mirror Plonky3Lean.Spec.Lookup Plonky3Lean.Proofs.Lookup
  Finset

variable {K : Type} [Field K]

/-- The messages of row r of an instance, over its columns. -/
def rowMessages (a : AirMessages K) (r : ℕ) : List (Key K × K) :=
  (List.range a.width).flatMap (a.msgs r)

/-- An instance with at most n messages per row has at most n h messages. -/
theorem length_all_le (a : AirMessages K) (n : ℕ) (hrow : ∀ r < a.height, (rowMessages a r).length ≤ n) :
    a.all.length ≤ n * a.height := by
  rw [AirMessages.all, List.length_flatMap]
  refine (List.sum_le_length_nsmul _ n fun x hx => ?_).trans (by simp [mul_comm])
  obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hx
  exact hrow r (List.mem_range.1 hr)

/-- **The exact count** is at most sum_i n_i h_i. -/
theorem length_allMessages_le (airs : List (AirMessages K)) (n : ℕ → ℕ)
    (hrow : ∀ i (h : i < airs.length), ∀ r < airs[i].height, (rowMessages airs[i] r).length ≤ n i) :
    (allMessages airs).length ≤ ∑ i ∈ range airs.length, n i * (airs.getD i ⟨0, 0, fun _ _ => []⟩).height := by
  induction airs using List.reverseRecOn with
  | nil => simp [allMessages]
  | append_singleton airs a ih =>
    have hl : ∀ i (h : i < airs.length), ∀ r < airs[i].height, (rowMessages airs[i] r).length ≤ n i := by
      intro i h r hr
      have := hrow i (by simp; omega) r (by simpa [List.getElem_append_left h] using hr)
      simpa [List.getElem_append_left h] using this
    have ha := length_all_le a (n airs.length) fun r hr => by
      simpa using hrow airs.length (by simp) r (by simpa using hr)
    rw [allMessages, List.flatMap_append, List.length_append, List.length_append,
      List.length_singleton, sum_range_succ]
    refine Nat.add_le_add ((ih hl).trans (le_of_eq (sum_congr rfl fun i hi => ?_))) ?_
    · have hi := mem_range.1 hi
      simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
    · simpa [List.getD_eq_getElem?_getD] using ha

/-- **At the largest height** the count is at most (sum_i n_i) 2^L. -/
theorem length_allMessages_le_max (airs : List (AirMessages K)) (n : ℕ → ℕ) (L : ℕ)
    (hrow : ∀ i (h : i < airs.length), ∀ r < airs[i].height, (rowMessages airs[i] r).length ≤ n i)
    (hh : ∀ a ∈ airs, a.height ≤ 2 ^ L) :
    (allMessages airs).length ≤ (∑ i ∈ range airs.length, n i) * 2 ^ L := by
  refine (length_allMessages_le airs n hrow).trans ?_
  rw [sum_mul]
  refine sum_le_sum fun i hi => Nat.mul_le_mul_left _ ?_
  have hi := mem_range.1 hi
  simpa [List.getD_eq_getElem?_getD, hi] using hh _ (List.getElem_mem hi)

variable [DecidableEq K]

open Classical in
/-- **p3-security's LogUp charge bounds the batch.**

Instance i emits at most n_i messages per row, over at most 2^L rows.

An unbalanced bus then passes on at most (sum_i n_i) 2^L (W + 2) |K| of the |K|^2 pairs.

That is the rate p3-security charges with the summed count and the largest height. -/
theorem batch_soundness_max_height [Fintype K] {p : ℕ} [CharP K p] {all : List (List (Lookup F))}
    {ids : List (List ℕ)} {st : LayoutState} (h : busIds all = some (ids, st))
    (hp : all.flatten.length ≤ p) (airs : List (AirMessages K))
    (hkey : KeyedBy all.flatten ids.flatten (allMessages airs))
    (hunbal : ¬ Balanced (allMessages airs)) (n : ℕ → ℕ) (L : ℕ)
    (hrow : ∀ i (h : i < airs.length), ∀ r < airs[i].height, (rowMessages airs[i] r).length ≤ n i)
    (hh : ∀ a ∈ airs, a.height ≤ 2 ^ L) :
    #{x : K × K | ∃ cols, Accepts x.1 x.2 st.max_message_width airs cols}
      ≤ (∑ i ∈ range airs.length, n i) * 2 ^ L * (st.max_message_width + 2) * Fintype.card K := by
  refine (batch_soundness h hp airs hkey hunbal).trans ?_
  gcongr
  · exact length_allMessages_le_max airs n L hrow hh
  · omega

/-! ## One-sided buses -/

/-- **p sends with no receiver balance.**

The net multiplicity p is zero in characteristic p, which is why the height bound keeps every count below p. -/
theorem balanced_replicate_char {p : ℕ} [CharP K p] (k : Key K) : Balanced (List.replicate p (k, (1 : K))) := by
  intro k'
  by_cases h : k = k'
  · subst h; simp [netMult, CharP.cast_eq_zero]
  · simp [netMult, h]

/-- **A bus with one sender** is unbalanced once it sends anything, with fewer than p unit sends. -/
theorem one_sided_unbalanced {p : ℕ} [CharP K p] (msgs : List (Key K × K)) (hne : msgs ≠ [])
    (hone : ∀ q ∈ msgs, q.2 = 1) (hlen : msgs.length < p) : ¬ Balanced msgs := by
  intro hb
  obtain ⟨q, hq⟩ := List.exists_mem_of_ne_nil _ hne
  have h := hb q.1
  have hsum : netMult msgs q.1 = ((msgs.filter (·.1 = q.1)).length : K) := by
    rw [netMult, List.map_congr_left fun x hx => hone x (List.mem_of_mem_filter hx)]
    simp
  have hpos : 0 < (msgs.filter (·.1 = q.1)).length := List.length_pos_of_mem (a := q) (by simpa using hq)
  have hlt : (msgs.filter (·.1 = q.1)).length < p := (List.length_filter_le _ _).trans_lt hlen
  rw [hsum, CharP.cast_eq_zero_iff K p] at h
  exact absurd (Nat.le_of_dvd hpos h) (by omega)

end Plonky3Lean.Proofs.BatchStark
