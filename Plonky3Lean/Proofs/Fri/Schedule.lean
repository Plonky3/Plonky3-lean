module

public import P3Fri.Config
public import Mathlib.Algebra.Order.BigOperators.Group.List
public import Mathlib.Tactic.Linarith

@[expose] public section

/-!
# The folding schedule

From the tallest input height down to the final height, every round folds by at least 1 and at most the cap, the arities sum to the distance, and the descent stops at every input height on the way.
-/

namespace Plonky3Lean.Proofs.Fri

open p3_fri.config.mirror

/-- The inputs with index below ni are those at height lh or above. -/
def SchedInv (hs : List ℕ) (lh ni : ℕ) : Prop :=
  ni ≤ hs.length ∧ ∀ j (hj : j < hs.length), j < ni ↔ lh ≤ hs[j]

theorem compute_log_arity_some {lh F A : ℕ} {nx : Option ℕ} (hA : 0 < A) (hF : F < lh)
    (hnx : ∀ x, nx = some x → x < lh) :
    ∃ a, compute_log_arity_for_round lh nx F A = some a ∧ 1 ≤ a ∧ a ≤ A ∧ a ≤ lh - F ∧
      ∀ x, nx = some x → a ≤ lh - x := by
  unfold compute_log_arity_for_round
  rcases nx with _ | x
  · exact ⟨min (lh - F) A, by simp [hA.ne', show ¬ lh ≤ F by omega], by omega, by omega, by omega,
      by simp⟩
  · have hx := hnx x rfl
    refine ⟨min (min (lh - x) (lh - F)) A, by simp [hA.ne', show ¬ lh ≤ F by omega,
      show ¬ lh ≤ x by omega], by omega, by omega, by omega, ?_⟩
    simp only [Option.some.injEq]
    rintro _ rfl
    omega

/-- The schedule loop, from height lh with the inputs below index ni rolled in. -/
theorem fold_schedule_loop_spec {hs : List ℕ} (hdec : hs.IsChain (· > ·)) {F A : ℕ} (hA : 0 < A) :
    ∀ fuel lh ni acc, lh - F ≤ fuel → SchedInv hs lh ni →
      ∃ L, fold_schedule_loop hs F A fuel lh ni acc = some (acc ++ L) ∧
        (∀ a ∈ L, 1 ≤ a ∧ a ≤ A) ∧ L.sum = lh - F ∧
        ∀ j (hj : j < hs.length), F ≤ hs[j] → hs[j] < lh → ∃ r ≤ L.length, lh - (L.take r).sum = hs[j]
  | 0, lh, ni, acc, hfuel, _ => ⟨[], by simp [fold_schedule_loop], by simp, by simp; omega,
      fun j hj h1 h2 => absurd h2 (by omega)⟩
  | fuel + 1, lh, ni, acc, hfuel, hI => by
    by_cases hlh : lh ≤ F
    · exact ⟨[], by simp [fold_schedule_loop, hlh], by simp, by simp; omega,
        fun j hj h1 h2 => absurd h2 (by omega)⟩
    have hnx : ∀ x, hs[ni]? = some x → x < lh := by
      intro x hx
      obtain ⟨hj, rfl⟩ := List.getElem?_eq_some_iff.1 hx
      exact lt_of_not_ge fun h => absurd ((hI.2 ni hj).2 h) (lt_irrefl _)
    obtain ⟨a, ha, ha1, haA, haF, hax⟩ := compute_log_arity_some (F := F) hA (by omega) hnx
    set ni' := if hs[ni]? = some (lh - a) then ni + 1 else ni with hni'
    have hpw := List.pairwise_iff_getElem.1 hdec.pairwise
    have hI' : SchedInv hs (lh - a) ni' := by
      refine ⟨?_, fun j hj => ?_⟩
      · by_cases hc : hs[ni]? = some (lh - a)
        · simp only [hni', hc, ↓reduceIte]
          exact (List.getElem?_eq_some_iff.1 hc).1
        · simp only [hni', hc, ↓reduceIte]; exact hI.1
      rcases Nat.lt_trichotomy j ni with hjn | rfl | hjn
      · have := (hI.2 j hj).1 hjn
        constructor
        · intro _; omega
        · intro _; by_cases hc : hs[j]? = some (lh - a) <;> simp only [hni'] <;> split_ifs <;> omega
      · have hx := hax hs[j] (List.getElem?_eq_getElem hj)
        have hlt := hnx hs[j] (List.getElem?_eq_getElem hj)
        by_cases hc : hs[j] = lh - a
        · simp only [hni', List.getElem?_eq_getElem hj, hc, ↓reduceIte]; omega
        · simp only [hni', List.getElem?_eq_getElem hj, Option.some.injEq, hc, ↓reduceIte]; omega
      · have hni : ni < hs.length := by omega
        have hx := hax hs[ni] (List.getElem?_eq_getElem hni)
        have hlt := hnx hs[ni] (List.getElem?_eq_getElem hni)
        have hd := hpw ni j hni hj hjn
        simp only [hni', List.getElem?_eq_getElem hni, Option.some.injEq]
        split_ifs <;> omega
    obtain ⟨L, hL, hLa, hLs, hLc⟩ :=
      fold_schedule_loop_spec (F := F) hdec hA fuel (lh - a) ni' (acc ++ [a]) (by omega) hI'
    refine ⟨a :: L, ?_, ?_, ?_, ?_⟩
    · simp only [fold_schedule_loop, hlh, ↓reduceIte, Option.bind_eq_bind, ha, Option.bind_some]
      rw [← hni', hL]; simp
    · intro b hb
      rcases List.mem_cons.1 hb with rfl | hb
      · exact ⟨ha1, haA⟩
      · exact hLa b hb
    · simp [hLs]; omega
    · intro j hj h1 h2
      by_cases hja : lh - a ≤ hs[j]
      · refine ⟨1, by simp, ?_⟩
        have hjni : ¬ j < ni := fun h => absurd ((hI.2 j hj).1 h) (by omega)
        have hni : ni < hs.length := by omega
        have hx := hax hs[ni] (List.getElem?_eq_getElem hni)
        rcases Nat.lt_or_ge ni j with hlt | hge
        · have := hpw ni j hni hj hlt; omega
        · obtain rfl : j = ni := by omega
          simp; omega
      · obtain ⟨r, hr, hr'⟩ := hLc j hj h1 (by omega)
        exact ⟨r + 1, by simp; omega, by simp [List.take_succ_cons]; omega⟩

/-- The schedule of strictly decreasing heights above the final height: every arity lies in [1, cap], they sum to the distance from the tallest height to the final one, and the descent stops at every input height at or above the final one. -/
theorem fold_schedule_spec {h0 : ℕ} {rest : List ℕ} (hdec : (h0 :: rest).IsChain (· > ·)) {F A : ℕ}
    (hA : 0 < A) (hF : F < h0) :
    ∃ L, fold_schedule (h0 :: rest) F A = some L ∧ (∀ a ∈ L, 1 ≤ a ∧ a ≤ A) ∧ L.sum = h0 - F ∧
      ∀ h ∈ h0 :: rest, F ≤ h → ∃ r ≤ L.length, h0 - (L.take r).sum = h := by
  have hpw := List.pairwise_iff_getElem.1 hdec.pairwise
  have hI : SchedInv (h0 :: rest) h0 1 := by
    refine ⟨by simp, fun j hj => ?_⟩
    rcases j with _ | j
    · simp
    · have := hpw 0 (j + 1) (by simp) hj (by omega)
      simp only [List.getElem_cons_zero] at this
      constructor <;> intro h <;> omega
  obtain ⟨L, hL, hLa, hLs, hLc⟩ := fold_schedule_loop_spec (F := F) hdec hA h0 h0 1 [] (by omega) hI
  refine ⟨L, by simp [fold_schedule, hdec, show ¬ h0 ≤ F by omega, hL], hLa, hLs, ?_⟩
  intro h hh hFh
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hh
  rcases j with _ | j
  · exact ⟨0, by simp, by simp⟩
  · exact hLc (j + 1) hj hFh (by have := hpw 0 (j + 1) (by simp) hj (by omega); simpa using this)

/-- No round is scheduled when the tallest height is at or below the final height. -/
theorem fold_schedule_nil {hs : List ℕ} (hdec : hs.IsChain (· > ·)) {F A : ℕ}
    (h : ∀ h0 ∈ hs.head?, h0 ≤ F) : fold_schedule hs F A = some [] := by
  rcases hs with _ | ⟨h0, rest⟩
  · simp [fold_schedule]
  · simp_all [fold_schedule]

/-- The schedule panics exactly on heights that are not strictly decreasing, or on a zero cap with a round to schedule. -/
theorem fold_schedule_eq_none {hs : List ℕ} {F A : ℕ} :
    fold_schedule hs F A = none ↔
      ¬ hs.IsChain (· > ·) ∨ (A = 0 ∧ ∃ h0 ∈ hs.head?, F < h0) := by
  by_cases hdec : hs.IsChain (· > ·)
  · rcases hs with _ | ⟨h0, rest⟩
    · simp [fold_schedule, hdec]
    · by_cases hF : h0 ≤ F
      · simp [fold_schedule, hdec, hF]
      · rcases Nat.eq_zero_or_pos A with rfl | hA
        · obtain ⟨m, rfl⟩ : ∃ m, h0 = m + 1 := ⟨h0 - 1, by omega⟩
          simp [fold_schedule, hdec, hF, fold_schedule_loop, compute_log_arity_for_round]
          omega
        · obtain ⟨L, hL, -⟩ := fold_schedule_spec (F := F) hdec hA (by omega)
          simpa [hL, hA.ne'] using hdec
  · simp [fold_schedule, hdec]

end Plonky3Lean.Proofs.Fri
