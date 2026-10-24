module

public import Plonky3Lean.Proofs.Lookup.Fingerprint

@[expose] public section

/-!
# The soundness error of the bus sum

The challenges (alpha, beta) are drawn uniformly from a finite field K after the trace is fixed.

An unbalanced list of N messages passes one of two ways:

- a denominator vanishes, which leaves a fraction column free
- the sum of m / d vanishes with every denominator nonzero, at a root of the cleared polynomial.

The first happens for at most N |K| pairs, the second for at most (N - 1) W |K|.

Together that is at most N (W + 1) |K| of the |K|^2 pairs.

This is below the rate N (W + 2) / |K| that p3-security charges.
-/

namespace Plonky3Lean.Proofs.Lookup

open Polynomial Plonky3Lean.Spec.Lookup Finset

set_option linter.unusedSectionVars false

variable {K : Type _} [Field K] [DecidableEq K]

theorem eval_clearedMv (α β : K) (W : ℕ) (G : Finset (Key K)) (M : Key K → K) :
    MvPolynomial.eval ![α, β] (clearedMv W G M) =
      ∑ c ∈ G, M c * ∏ c' ∈ G.erase c, busDenom α β W c'.1 c'.2 := by
  simp [clearedMv, eval_busDenomMv]

/-- Assume no denominator vanishes.

Then the sum of M_c / D_c is the cleared polynomial over the product of the denominators. -/
theorem sum_div_eq_cleared (α β : K) (W : ℕ) (G : Finset (Key K)) (M : Key K → K)
    (hD : ∀ c ∈ G, busDenom α β W c.1 c.2 ≠ 0) :
    ∑ c ∈ G, M c / busDenom α β W c.1 c.2 =
      MvPolynomial.eval ![α, β] (clearedMv W G M) / ∏ c ∈ G, busDenom α β W c.1 c.2 := by
  rw [eval_clearedMv, eq_div_iff (prod_ne_zero_iff.2 hD), sum_mul]
  refine sum_congr rfl fun c hc => ?_
  rw [← mul_prod_erase G _ hc]
  field_simp [hD c hc]

/-- The bus sum regrouped by key. -/
theorem busSum_eq_sum (α β : K) (W : ℕ) (msgs : List (Key K × K)) (G : Finset (Key K))
    (hG : ∀ p ∈ msgs, p.1 ∈ G) :
    busSum α β W msgs = ∑ c ∈ G, netMult msgs c / busDenom α β W c.1 c.2 := by
  let g : Key K → K →+ K := fun c =>
    { toFun := fun m => m / busDenom α β W c.1 c.2
      map_zero' := zero_div _
      map_add' := fun a b => add_div a b _ }
  exact sum_map_eq_sum_netMult g msgs G hG

variable [Fintype K]

/-- **Schwartz-Zippel** in two variables: a nonzero polynomial vanishes on at most deg |K| of the |K|^2 pairs. -/
theorem card_roots_le (P : MvPolynomial (Fin 2) K) (hP : P ≠ 0) :
    #{x : K × K | MvPolynomial.eval ![x.1, x.2] P = 0} ≤ P.totalDegree * Fintype.card K := by
  have hsz := MvPolynomial.schwartz_zippel_totalDegree hP (univ : Finset K)
  set R := #{f ∈ Fintype.piFinset fun _ : Fin 2 => (univ : Finset K) | MvPolynomial.eval f P = 0}
  have hq : (0 : ℚ≥0) < Fintype.card K := by exact_mod_cast Fintype.card_pos
  rw [card_univ, div_le_div_iff₀ (by positivity) hq] at hsz
  have hR : R ≤ P.totalDegree * Fintype.card K := by
    have : (R : ℚ≥0) * Fintype.card K ≤ (P.totalDegree * Fintype.card K) * Fintype.card K := by
      calc (R : ℚ≥0) * Fintype.card K ≤ P.totalDegree * (Fintype.card K : ℚ≥0) ^ 2 := hsz
        _ = _ := by ring
    exact_mod_cast le_of_mul_le_mul_right this hq
  refine le_trans (card_le_card_of_injOn (fun x => ![x.1, x.2]) ?_ ?_) hR
  · intro x hx; simp_all
  · intro x _ y _ h
    have h0 := congrFun h 0; have h1 := congrFun h 1
    exact Prod.ext (by simpa using h0) (by simpa using h1)

/-- For each beta exactly one alpha makes a denominator vanish, so it vanishes on at most |K| pairs. -/
theorem card_denom_zero_le (W bus : ℕ) (e : List K) :
    #{x : K × K | busDenom x.1 x.2 W bus e = 0} ≤ Fintype.card K := by
  refine (card_le_card_of_injOn Prod.snd (fun _ _ => mem_coe.2 (mem_univ _)) ?_).trans
    (by rw [card_univ])
  intro x hx y hy h
  have hx' : busDenom x.1 x.2 W bus e = 0 := by simpa using hx
  have hy' : busDenom y.1 y.2 W bus e = 0 := by simpa using hy
  unfold busDenom at hx' hy'
  refine Prod.ext ?_ h
  rw [h] at hx'; linear_combination hx' - hy'

/-- **Soundness of the bus sum.**

Take an unbalanced list of messages, with widths at most W and one width per bus.

It passes on at most N (W + 1) |K| of the |K|^2 challenge pairs.

Passing means that a denominator vanishes, or that the sum of m / d vanishes. -/
theorem card_bad_challenges_le (msgs : List (Key K × K)) {W : ℕ} (hW : 1 ≤ W)
    (hlen : ∀ p ∈ msgs, p.1.2.length ≤ W)
    (hbus : ∀ p ∈ msgs, ∀ q ∈ msgs, (p.1.1 : K) = q.1.1 → p.1.1 = q.1.1)
    (hwidth : ∀ p ∈ msgs, ∀ q ∈ msgs, p.1.1 = q.1.1 → p.1.2.length = q.1.2.length)
    (hunbal : ¬ Balanced msgs) :
    #{x : K × K | (∃ p ∈ msgs, busDenom x.1 x.2 W p.1.1 p.1.2 = 0) ∨ busSum x.1 x.2 W msgs = 0}
      ≤ msgs.length * (W + 1) * Fintype.card K := by
  set G := (msgs.map (·.1)).toFinset
  have hmemG : ∀ p ∈ msgs, p.1 ∈ G := fun p hp => List.mem_toFinset.2 (List.mem_map_of_mem hp)
  have hGmem : ∀ c ∈ G, ∃ p ∈ msgs, p.1 = c := fun c hc => by
    simpa using List.mem_toFinset.1 hc
  obtain ⟨c₀, hc₀⟩ := not_forall.1 hunbal
  have hc₀G : c₀ ∈ G := by
    by_contra h; exact hc₀ (netMult_of_not_mem (by simpa [G] using h))
  have hP := clearedMv_ne_zero (W := W) G (netMult msgs)
    (fun c hc => by obtain ⟨p, hp, rfl⟩ := hGmem c hc; exact hlen p hp)
    (fun c hc c' hc' => by
      obtain ⟨p, hp, rfl⟩ := hGmem c hc; obtain ⟨q, hq, rfl⟩ := hGmem c' hc'; exact hbus p hp q hq)
    (fun c hc c' hc' => by
      obtain ⟨p, hp, rfl⟩ := hGmem c hc; obtain ⟨q, hq, rfl⟩ := hGmem c' hc'; exact hwidth p hp q hq)
    hc₀G hc₀
  -- The bad set lies in the union of the vanishing sets and the roots of the cleared polynomial.
  have hsub : ({x : K × K | (∃ p ∈ msgs, busDenom x.1 x.2 W p.1.1 p.1.2 = 0) ∨
      busSum x.1 x.2 W msgs = 0} : Finset (K × K)) ⊆
      (G.biUnion fun c => univ.filter fun x : K × K => busDenom x.1 x.2 W c.1 c.2 = 0) ∪
        univ.filter fun x : K × K =>
          MvPolynomial.eval ![x.1, x.2] (clearedMv W G (netMult msgs)) = 0 := by
    intro x hx
    simp only [mem_filter, mem_univ, true_and] at hx
    simp only [mem_union, mem_biUnion, mem_filter, mem_univ, true_and]
    by_cases hD : ∃ c ∈ G, busDenom x.1 x.2 W c.1 c.2 = 0
    · exact Or.inl hD
    · simp only [not_exists, not_and] at hD
      refine Or.inr ?_
      rcases hx with ⟨p, hp, h⟩ | h
      · exact absurd h (hD p.1 (hmemG p hp))
      · rw [busSum_eq_sum _ _ _ _ G hmemG, sum_div_eq_cleared _ _ _ _ _ hD,
          div_eq_zero_iff] at h
        exact h.resolve_right (prod_ne_zero_iff.2 hD)
  have hG : G.card ≤ msgs.length := (List.toFinset_card_le _).trans (by simp)
  have hGpos : 1 ≤ G.card := card_pos.2 ⟨c₀, hc₀G⟩
  calc _ ≤ _ := card_le_card hsub
    _ ≤ G.card * Fintype.card K + (G.card - 1) * W * Fintype.card K := by
      refine (card_union_le _ _).trans (Nat.add_le_add ?_ ?_)
      · refine card_biUnion_le.trans ?_
        calc ∑ c ∈ G, _ ≤ ∑ _c ∈ G, Fintype.card K := sum_le_sum fun c _ => card_denom_zero_le W _ _
          _ = _ := by rw [sum_const, smul_eq_mul]
      · refine (card_roots_le _ hP).trans (Nat.mul_le_mul_right _ ?_)
        exact totalDegree_clearedMv hW G _ fun c hc => by
          obtain ⟨p, hp, rfl⟩ := hGmem c hc; exact hlen p hp
    _ ≤ msgs.length * (W + 1) * Fintype.card K := by
      have : G.card + (G.card - 1) * W ≤ msgs.length * (W + 1) := by
        have := Nat.mul_le_mul_right W (Nat.sub_le G.card 1)
        nlinarith
      nlinarith

/-- The same count at p3-security's rate N (W + 2) / |K|. -/
theorem card_bad_challenges_le_security (msgs : List (Key K × K)) {W : ℕ} (hW : 1 ≤ W)
    (hlen : ∀ p ∈ msgs, p.1.2.length ≤ W)
    (hbus : ∀ p ∈ msgs, ∀ q ∈ msgs, (p.1.1 : K) = q.1.1 → p.1.1 = q.1.1)
    (hwidth : ∀ p ∈ msgs, ∀ q ∈ msgs, p.1.1 = q.1.1 → p.1.2.length = q.1.2.length)
    (hunbal : ¬ Balanced msgs) :
    #{x : K × K | (∃ p ∈ msgs, busDenom x.1 x.2 W p.1.1 p.1.2 = 0) ∨ busSum x.1 x.2 W msgs = 0}
      ≤ msgs.length * (W + 2) * Fintype.card K :=
  (card_bad_challenges_le msgs hW hlen hbus hwidth hunbal).trans
    (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (by omega)))

end Plonky3Lean.Proofs.Lookup
