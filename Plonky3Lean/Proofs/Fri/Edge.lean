module

public import Plonky3Lean.Proofs.Fri.Pcs
public import Plonky3Lean.Proofs.Fri.Reduce

@[expose] public section

/-!
# Edge cases of the opening argument

- No queries, or a blowup of 1, is rejected before any transcript work.
- A claimed height past the adicity is rejected before the schedule is built.
- An input below the final height is never rolled in, so its query is rejected.
- The prover panics on an opening point inside the domain it divides by.
- For BabyBear, a grinding difficulty is safe exactly up to 30 bits.
-/

namespace Plonky3Lean.Proofs.Fri

open Polynomial Finset Plonky3Lean.Spec.Fri p3_fri.two_adic_pcs.mirror p3_dft.mirror
open p3_fri.verifier.mirror p3_fri.mirror p3_fri.config.mirror p3_fri.transcript.mirror Plonky3Lean.Proofs.Dft
open p3_commit.pcs.univariate.mirror

set_option linter.unusedSectionVars false

variable {K : Type} [Field K] [DecidableEq K]

section reject

variable (G : Gen K) (g : K) {C S : Type} (fmmcs immcs : MmcsOps K)
  (mkTx : FriShape → VerifierTx K fmmcs.Commitment S) (params : FriParameters)
  (proof : FriProof K fmmcs.Commitment fmmcs.MultiProof immcs.MultiProof) (s : S)
  (claims : List (Claim G C)) (commit_of : C → immcs.Commitment) (alpha : K)

/-- Zero queries are rejected. -/
theorem verify_fri_zero_queries (h : params.num_queries = 0) :
    verify_fri G g fmmcs immcs mkTx params proof s claims commit_of alpha = throw .ZeroQueries := by
  unfold verify_fri; simp [h]

/-- A blowup of 1 is rejected. -/
theorem verify_fri_zero_blowup (hq : params.num_queries ≠ 0) (h : params.log_blowup = 0) :
    verify_fri G g fmmcs immcs mkTx params proof s claims commit_of alpha = throw .ZeroBlowup := by
  unfold verify_fri; simp [hq, h]

/-- A tallest claimed height past the adicity is rejected. -/
theorem verify_fri_too_tall (hq : params.num_queries ≠ 0) (hb : params.log_blowup ≠ 0)
    (ha : params.max_log_arity ≠ 0) (hm : claims.all (·.matrices = []) = false)
    (h : G.adicity < (inputLogHeights params.log_blowup claims).headD 0) :
    verify_fri G g fmmcs immcs mkTx params proof s claims commit_of alpha = throw .GlobalMaxHeightTooLarge := by
  unfold verify_fri
  simp only [hq, hb, ha, hm, h, ↓reduceIte, throw_bind', Bool.false_eq_true]

end reject

/-! ## Inputs below the final height -/

theorem mem_rollIn (lh' : ℕ) (β : K) (a : ℕ) (u : K) (ro : List (ℕ × K)) :
    ∀ e ∈ ro, e ∈ (rollIn lh' β a u ro).2 ∨ e.1 = lh' := by
  intro e he
  rcases ro with _ | ⟨⟨h, v⟩, ro⟩
  · simp at he
  · unfold rollIn
    by_cases hh : h = lh'
    · rcases List.mem_cons.1 he with rfl | he
      · exact Or.inr hh
      · simp [hh, he]
    · simp [hh, he]

/-- A consistent chain consumes an opening only at a height it folds to. -/
theorem Consistent.consumed (G : Gen K) : ∀ (lh idx : ℕ) (v : K) (ro : List (ℕ × K)) (rds : List (K × ℕ))
    (recs : List (ℕ × List K)) (fin : K) (roF : List (ℕ × K)),
    Consistent G lh idx v ro rds recs fin roF → ∀ e ∈ ro, e ∈ roF ∨ lh - (rds.map (·.2)).sum ≤ e.1
  | _, _, _, ro, [], [], _, roF, h => by
    obtain ⟨-, rfl⟩ := h; exact fun e he => Or.inl he
  | lh, idx, v, ro, (β, a) :: rds, (gi, row) :: recs, fin, roF, h => by
    obtain ⟨-, -, -, u, -, hrest⟩ := h
    intro e he
    rcases mem_rollIn (lh - a) β a u ro e he with he' | he'
    · rcases Consistent.consumed G _ _ _ _ rds recs fin roF hrest e he' with h1 | h1
      · exact Or.inl h1
      · right; simp only [List.map_cons, List.sum_cons]; omega
    · right; simp only [List.map_cons, List.sum_cons]; omega
  | _, _, _, _, [], _ :: _, _, _, h => absurd h (by simp [Consistent])
  | _, _, _, _, _ :: _, [], _, _, h => absurd h (by simp [Consistent])

/-- An accepted fold chain has every opening at or above the final height.

So an input below the final height is never rolled in, and its query is rejected. -/
theorem fold_query_final_le {ME IE : Type} (G : Gen K) (q idx : ℕ) (betas : List K) (las : List ℕ)
    (svs : List (List (List K))) (ro : List (ℕ × K)) (H Hf : ℕ) {f : K} {i' : ℕ}
    {recorded : List (ℕ × List K)}
    (h : fold_query (ME := ME) (IE := IE) G q idx betas las svs ro H Hf = pure (f, i', recorded)) :
    ∀ e ∈ ro, Hf ≤ e.1 := by
  obtain ⟨v0, ro', rfl, hc, hHf⟩ := fold_query_sound G q idx betas las svs ro H Hf h
  intro e he
  rcases List.mem_cons.1 he with rfl | he
  · simp only; omega
  · rcases Consistent.consumed G _ _ _ _ _ _ _ _ hc e he with h1 | h1
    · simp at h1
    · simp only [List.map_map, Function.comp_def] at h1
      omega

/-! ## An opening point inside the domain -/

/-- The prover's inverse denominators panic exactly when z is one of the domain points it divides by.

These are the first 2^h points of the bit-reversed coset, for the tallest log height h opened at z. -/
theorem compute_inverse_denominators_eq_none (mats : List (MatToOpen K)) (coset : List K) (z : K) :
    compute_inverse_denominators mats coset z = none ↔
      z ∈ coset.take (2 ^ (((mats.filter fun m => z ∈ m.points).map fun m => Nat.log 2 m.mat.height).foldl
        max 0)) := by
  unfold compute_inverse_denominators
  simp only [p3_commit.domain.mirror.batchInv, List.mem_map, ne_eq]
  split_ifs with h
  · simp only [false_iff]
    intro hz; exact h _ (List.mem_map_of_mem hz) (sub_self z)
  · simp only [not_forall, not_not, List.mem_map] at h
    obtain ⟨_, ⟨x, hx, rfl⟩, h0⟩ := h
    simp only [true_iff]
    convert hx using 1
    exact sub_eq_zero.1 h0

/-! ## Grinding difficulties for BabyBear -/

/-- For the BabyBear order p = 15 2^27 + 1, a difficulty is safe exactly when it is at most 30 bits. -/
theorem powSafe_babyBear (b : ℕ) : PowSafe 2013265921 b ↔ b ≤ 30 := by
  unfold PowSafe
  constructor
  · rintro (rfl | ⟨-, h⟩)
    · omega
    · by_contra hb
      have : 2 ^ 31 ≤ 2 ^ b := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
  · intro hb
    rcases Nat.eq_zero_or_pos b with rfl | _
    · exact Or.inl rfl
    · right
      have : 2 ^ b ≤ 2 ^ 30 := Nat.pow_le_pow_right (by norm_num) hb
      omega

end Plonky3Lean.Proofs.Fri
