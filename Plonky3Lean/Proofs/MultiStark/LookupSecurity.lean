module

public import P3MultiStark.Security
public import Plonky3Lean.Proofs.Lookup.Soundness

@[expose] public section

/-!
# The lookup terms p3-security charges

The fractional reduction over L layers has three kinds of bad draws in layer i:

- lambda, at most one value
- the i round challenges, at most 3 i of every |K| draws
- the branch, at most one value.

Summed over the layers this is the charged count:

```text
    sum_(i < L) (3 i + 2)  =  2 L + 3 L (L - 1) / 2
```

The fingerprint of a tuple on bus b is alpha + (b + 1) beta^W - sum_k e_k beta^k.

That is the bus denominator of LogUp with the payload reversed.

So the two-variable LogUp bound applies, under the plan's two checks:

- at most p buses, so that b + 1 stays distinct
- one width per bus.

An unbalanced list of N messages then passes on at most N (W + 2) |K| of the |K|^2 pairs.

That is the charged rate N (W + 2) / |K|.
-/

namespace Plonky3Lean.Proofs.MultiStark

open p3_multi_stark.security.mirror Plonky3Lean.Spec.Lookup Plonky3Lean.Proofs.Lookup Finset

set_option linter.unusedSectionVars false

/-! ## The fractional reduction -/

/-- **The reduction's charge is its count of bad draws.**

Layer i has one bad lambda, 3 i bad round challenges per |K| draws, and one bad branch. -/
theorem gkr_charge_eq (L : ℕ) :
    2 * L + 3 * (L * (L - 1) / 2) = ∑ i ∈ range L, (3 * i + 2) := by
  rw [sum_add_distrib, ← mul_sum, sum_range_id, sum_const, card_range, smul_eq_mul]
  ring

theorem lookup_terms_gkr (p : LookupParams) (hL : 0 < p.num_variables) :
    ⟨"fractional-gkr", ∑ i ∈ range p.num_variables, (3 * i + 2), .NonZero⟩ ∈ lookup_terms p := by
  rw [← gkr_charge_eq]
  refine List.mem_filter.mpr ⟨by simp, by simp; omega⟩

/-! ## The fingerprint -/

variable {K : Type _} [Field K] [DecidableEq K]

/-- The fingerprint of multi-stark: the bus prefix minus sum_k e_k beta^k. -/
def msDenom (α β : K) (W bus : ℕ) (e : List K) : K :=
  α + ((bus : K) + 1) * β ^ W - ∑ k ∈ range e.length, e.getD k 0 * β ^ k

/-- It is the LogUp bus denominator of the reversed payload. -/
theorem msDenom_eq (α β : K) (W bus : ℕ) (e : List K) :
    msDenom α β W bus e = busDenom α β W bus e.reverse := by
  simp [msDenom, busDenom, fingerprint]

/-- Reverse every payload. -/
def revKeys (msgs : List (Key K × K)) : List (Key K × K) :=
  msgs.map fun p => ((p.1.1, p.1.2.reverse), p.2)

theorem netMult_revKeys (msgs : List (Key K × K)) (k : Key K) :
    netMult (revKeys msgs) k = netMult msgs (k.1, k.2.reverse) := by
  induction msgs with
  | nil => simp [revKeys]
  | cons p msgs ih =>
    simp only [revKeys, List.map_cons] at ih ⊢
    rw [netMult_cons, netMult_cons, ih]
    congr 1
    obtain ⟨⟨b, e⟩, m⟩ := p
    obtain ⟨b', e'⟩ := k
    by_cases h : b = b' ∧ e = e'.reverse
    · obtain ⟨rfl, rfl⟩ := h; simp
    · have h1 : ¬ ((b, e.reverse) = (b', e')) := by
        simp only [Prod.mk.injEq, not_and]
        intro hb he; exact h ⟨hb, by rw [← he, List.reverse_reverse]⟩
      have h2 : ¬ ((b, e) = (b', e'.reverse)) := by simpa using h
      simp only [h1, h2, ↓reduceIte]

/-- **The fingerprint's soundness.**

Take an unbalanced list of N messages, at most W wide, with at most p buses and one width per bus.

Count the pairs (alpha, beta) where a denominator vanishes or the fractions sum to zero.

There are at most N (W + 2) |K| of them, out of |K|^2. -/
theorem logup_bad_card [Fintype K] (msgs : List (Key K × K)) {W : ℕ} (hW : 1 ≤ W)
    (hlen : ∀ p ∈ msgs, p.1.2.length ≤ W)
    (hbus : ∀ p ∈ msgs, ∀ q ∈ msgs, (p.1.1 : K) = q.1.1 → p.1.1 = q.1.1)
    (hwidth : ∀ p ∈ msgs, ∀ q ∈ msgs, p.1.1 = q.1.1 → p.1.2.length = q.1.2.length)
    (hunbal : ¬ Balanced msgs) :
    #{x : K × K | (∃ p ∈ msgs, msDenom x.1 x.2 W p.1.1 p.1.2 = 0) ∨
        (msgs.map fun p => p.2 / msDenom x.1 x.2 W p.1.1 p.1.2).sum = 0} ≤
      msgs.length * (W + 2) * Fintype.card K := by
  have hunbal' : ¬ Balanced (revKeys msgs) := fun h => hunbal fun k => by
    have := h (k.1, k.2.reverse)
    rwa [netMult_revKeys, List.reverse_reverse] at this
  have h := card_bad_challenges_le_security (revKeys msgs) hW
    (fun p hp => by obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp; simpa using hlen q hq)
    (fun p hp q hq => by
      obtain ⟨p', hp', rfl⟩ := List.mem_map.mp hp; obtain ⟨q', hq', rfl⟩ := List.mem_map.mp hq
      exact hbus p' hp' q' hq')
    (fun p hp q hq => by
      obtain ⟨p', hp', rfl⟩ := List.mem_map.mp hp; obtain ⟨q', hq', rfl⟩ := List.mem_map.mp hq
      simpa using hwidth p' hp' q' hq')
    hunbal'
  rw [show (revKeys msgs).length = msgs.length by simp [revKeys]] at h
  refine (card_le_card fun x hx => ?_).trans h
  rw [Finset.mem_filter] at hx ⊢
  refine ⟨mem_univ _, ?_⟩
  replace hx := hx.2
  rcases hx with ⟨p, hp, h0⟩ | h0
  · exact Or.inl ⟨_, by simp only [revKeys]; exact List.mem_map_of_mem hp,
      by rw [← msDenom_eq]; exact h0⟩
  · refine Or.inr ?_
    simp only [busSum, revKeys, List.map_map]
    rw [← h0]
    congr 1
    exact List.map_congr_left fun p _ => by simp [Function.comp, msDenom_eq]

end Plonky3Lean.Proofs.MultiStark
