module

public import Plonky3Lean.Proofs.BatchStark.Layout
public import Plonky3Lean.Proofs.Lookup.RunningSum

@[expose] public section

/-!
# The cross-table bus sum

* Lookup j of instance i reads the pair at positions 2j and 2j + 1, the bus offset and beta.
* Its combiner alpha' - fingerprint(e) is then the domain-separated denominator of its bus id.
* Messages keyed by the layout's bus ids meet the hypotheses of p3-lookup's soundness count, when there are fewer lookups than the characteristic.
-/

set_option linter.unusedSectionVars false

namespace Plonky3Lean.Proofs.BatchStark

open p3_batch_stark.transcript.mirror p3_lookup.mirror Plonky3Lean.Spec.Lookup Plonky3Lean.Proofs.Lookup
  Finset

variable {F K : Type} [Field K]

theorem flatMap_pair_get (f : ℕ → K) (β : K) (l : List ℕ) (j : ℕ) (hj : j < l.length) :
    (l.flatMap fun b => [f b, β])[2 * j]? = some (f l[j]) ∧
      (l.flatMap fun b => [f b, β])[2 * j + 1]? = some β := by
  induction l generalizing j with
  | nil => simp at hj
  | cons b l ih =>
    cases j with
    | zero => simp
    | succ j =>
      have := ih j (by simpa using hj)
      simpa [show 2 * (j + 1) = 2 * j + 2 by ring, show 2 * j + 2 + 1 = 2 * j + 1 + 2 by ring] using this

/-- **The pair a lookup reads.** Lookup j of instance i reads alpha + (id + 1) beta^W at position 2j and beta at position 2j + 1. -/
theorem lay_out_pair {all : List (List (Lookup F))} {ids : List (List ℕ)} {st : LayoutState}
    (h : busIds all = some (ids, st)) (α β : K) {i j : ℕ} (hi : i < ids.length) (hj : j < ids[i].length) :
    ∃ ch, lay_out_lookup_challenges 2 all α β = some ch ∧
      ch[i]?.bind (·[2 * j]?) = some (α + ((ids[i][j] : K) + 1) * β ^ st.max_message_width) ∧
      ch[i]?.bind (·[2 * j + 1]?) = some β := by
  refine ⟨_, lay_out_eq h α β, ?_⟩
  have := flatMap_pair_get (fun b : ℕ => α + ((b : K) + 1) * β ^ st.max_message_width) β ids[i] j hj
  simpa [hi] using this

/-- The combiner on the bus offset is the domain-separated denominator. -/
theorem combiner_eq_busDenom (α β : K) (W b : ℕ) (e : List K) :
    (α + ((b : K) + 1) * β ^ W) - fingerprint β e = busDenom α β W b e := rfl

/-- Messages keyed by the layout: each carries the bus id of some lookup, and a payload of that lookup's width. -/
def KeyedBy (P : List (Lookup F)) (ids : List ℕ) (msgs : List (Key K × K)) : Prop :=
  ∀ q ∈ msgs, ∃ a < P.length, q.1.1 = ids.getD a 0 ∧ (P[a]?.bind width) = some q.1.2.length

variable [DecidableEq K]

open Classical in
/-- **The batch's bus soundness.** For messages keyed by the layout's bus ids, with fewer lookups than the characteristic p of K, an unbalanced bus passes on at most N (W + 1) |K| of the |K|^2 challenge pairs, whatever permutation columns the prover picks after the challenges. -/
theorem batch_soundness [Fintype K] {p : ℕ} [CharP K p] {all : List (List (Lookup F))}
    {ids : List (List ℕ)} {st : LayoutState} (h : busIds all = some (ids, st))
    (hp : all.flatten.length ≤ p) (airs : List (AirMessages K))
    (hkey : KeyedBy all.flatten ids.flatten (allMessages airs))
    (hunbal : ¬ Balanced (allMessages airs)) :
    #{x : K × K | ∃ cols, Accepts x.1 x.2 st.max_message_width airs cols}
      ≤ (allMessages airs).length * (st.max_message_width + 1) * Fintype.card K := by
  have hI := (busIds_spec h).2
  have hok := hI.widthsOk
  -- Every bus id is a position's id, below the number of lookups.
  have hid : ∀ q ∈ allMessages airs, ∃ a < all.flatten.length, q.1.1 = ids.flatten.getD a 0 ∧
      q.1.1 < p ∧ (all.flatten[a]?.bind width) = some q.1.2.length := by
    intro q hq
    obtain ⟨a, ha, h1, h2⟩ := hkey q hq
    exact ⟨a, ha, h1, by rw [h1]; have := hI.lt a (hI.len ▸ ha); have := hI.bound; omega, h2⟩
  refine card_accepting_le airs hI.max_pos (fun q hq => ?_) (fun q hq q' hq' he => ?_)
    (fun q hq q' hq' he => ?_) hunbal
  · obtain ⟨a, ha, -, -, hw⟩ := hid q hq
    obtain ⟨w, hw', hle⟩ := hI.wd a ha
    rw [hw] at hw'; cases hw'; exact hle
  · obtain ⟨-, -, -, h1, -⟩ := hid q hq
    obtain ⟨-, -, -, h2, -⟩ := hid q' hq'
    rw [CharP.natCast_eq_natCast K p, Nat.ModEq, Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2] at he
    exact he
  · obtain ⟨a, ha, ea, -, wa⟩ := hid q hq
    obtain ⟨b, hb, eb, -, wb⟩ := hid q' hq'
    rw [ea, eb, hI.eq_iff a (hI.len ▸ ha) b (hI.len ▸ hb)] at he
    rcases he with rfl | ⟨n, hna, hnb⟩
    · rw [wa] at wb; simpa using wb
    · obtain ⟨c, hc⟩ : ∃ c, all.flatten[a]? = some c := ⟨_, List.getElem?_eq_getElem ha⟩
      obtain ⟨d, hd⟩ : ∃ d, all.flatten[b]? = some d := ⟨_, List.getElem?_eq_getElem hb⟩
      rw [hc] at hna wa; rw [hd] at hnb wb
      have := hok.2 c (mem_iff_get.2 ⟨a, ha, hc⟩) d (mem_iff_get.2 ⟨b, hb, hd⟩) n
        (by simpa using hna) (by simpa using hnb)
      simp only [Option.bind_some] at wa wb
      rw [this, wb] at wa; simpa using wa.symm

end Plonky3Lean.Proofs.BatchStark
