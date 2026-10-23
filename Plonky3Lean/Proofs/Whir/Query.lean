module

public import Plonky3Lean.Proofs.Whir.Complete

@[expose] public section

/-!
# The query schedule

A query phase draws exactly its query count, unless that count reaches the folded domain, and then it opens every position.

A stratified schedule splits the count into its binary digits 2^d and draws one index in each of the 2^d equal strata.
-/

namespace Plonky3Lean.Proofs.Whir

open p3_sumcheck.mirror p3_whir.mirror p3_whir.transcript.mirror

set_option linter.unusedSectionVars false

variable {F EF : Type _} [Field F] [Field EF] [Algebra F EF] [DecidableEq F] [DecidableEq EF]

/-- The summands of the stratified schedule add up to the count. -/
theorem sum_query_summand_depths : ∀ m, ((query_summand_depths m).map (2 ^ ·)).sum = m := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    unfold query_summand_depths
    split
    · next h => simp [h]
    · next h =>
      rw [List.map_cons, List.sum_cons, ih _ (Nat.sub_lt (by omega) (Nat.two_pow_pos _))]
      have := Nat.pow_log_le_self 2 (show m ≠ 0 from h)
      omega

/-- The number of indices a query phase plays: every position when nothing is drawn, else the draw count. -/
theorem length_play_query_indices (S : WSponge F EF) (hlen : ∀ h bits count, (S.indices h bits count).length = count)
    (h : List (Step F EF)) (width draws : ℕ) (stratified : Bool) :
    (play_query_indices S h width draws stratified (query_summand_depths draws)).1.length =
      if draws = 0 then 2 ^ width else draws := by
  unfold play_query_indices
  split_ifs with h0 h1
  · simp
  · simp [draw, hlen]
  · suffices ∀ (ds : List ℕ) (acc : List ℕ × List (Step F EF)),
        (ds.foldl (fun (acc : List ℕ × List (Step F EF)) depth =>
          ((acc.1 ++ (List.range (draw S acc.2 (width - depth) (2 ^ depth)).1.length).map fun s =>
            stratified_index width depth s ((draw S acc.2 (width - depth) (2 ^ depth)).1.getD s 0)),
            (draw S acc.2 (width - depth) (2 ^ depth)).2)) acc).1.length =
          acc.1.length + (ds.map (2 ^ ·)).sum by
      rw [this, sum_query_summand_depths]; simp
    intro ds
    induction ds with
    | nil => simp
    | cons d ds ih => intro acc; rw [List.foldl_cons, ih]; simp [draw, hlen]; omega

/-- A stratified draw lands in its stratum: index s of depth d has top d bits equal to s. -/
theorem stratified_index_stratum {width depth stratum low : ℕ}
    (hlow : low < 2 ^ (width - depth)) : stratified_index width depth stratum low >>> (width - depth) = stratum := by
  unfold stratified_index
  rw [Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow,
    show stratum * 2 ^ (width - depth) ||| low = stratum * 2 ^ (width - depth) + low from ?_]
  · rw [Nat.add_comm, Nat.add_mul_div_right _ _ (Nat.two_pow_pos _), Nat.div_eq_of_lt hlow, zero_add]
  · rw [← Nat.shiftLeft_eq]
    exact (Nat.shiftLeft_add_eq_or_of_lt hlow stratum).symm

/-- When the query count is positive and below the folded domain, the phase opens at most that many distinct positions, all inside the domain.

This is the count the zero-knowledge encoding needs: an oracle with t randomness coefficients hides any t positions. -/
theorem opened_le_queries (S : WSponge F EF) (hidx : ∀ h bits count, ∀ i ∈ S.indices h bits count, i < 2 ^ bits)
    (hlen : ∀ h bits count, (S.indices h bits count).length = count) (h : List (Step F EF)) {width q : ℕ}
    (hq0 : 0 < q) (hq : q < 2 ^ width) (stratified : Bool) :
    let idx := (play_query_indices S h width (query_draws (2 ^ width) q) stratified
      (query_summand_depths (query_draws (2 ^ width) q))).1
    idx.toFinset.card ≤ q ∧ ∀ i ∈ idx, i < 2 ^ width := by
  intro idx
  have hd : query_draws (2 ^ width) q = q := by unfold query_draws; split_ifs <;> omega
  refine ⟨?_, play_query_indices_lt S hidx hlen h (by rw [hd]; exact Or.inr hq) stratified⟩
  refine (List.toFinset_card_le idx).trans ?_
  rw [length_play_query_indices S hlen, hd]
  split_ifs <;> omega

end Plonky3Lean.Proofs.Whir
