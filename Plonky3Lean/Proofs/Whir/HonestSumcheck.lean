module

public import Plonky3Lean.Proofs.Whir.Sumcheck
public import Plonky3Lean.Proofs.Sumcheck.Verifier

@[expose] public section

/-!
# The honest sumcheck prover against the sponge

Round i sends the kernel's pair on the tables folded at the challenges drawn so far, grinds when asked, and draws its challenge from the history.

The quadratic verifier accepts these rounds, and replays the claim sum_b f[b] w[b] to the sum over the folded tables.
-/

namespace Plonky3Lean.Proofs.Whir

open Finset Plonky3Lean.Spec.MultilinearUtil Plonky3Lean.Spec.Whir Plonky3Lean.Proofs.MultilinearUtil
open p3_sumcheck.mirror Plonky3Lean.Proofs.Sumcheck

variable {F EF : Type _} [Field EF]

/-- The kernel's pair on two tables: the sum over the lower halves and the sum of the products of the differences. -/
def kernelPair (f w : List EF) : EF × EF :=
  (∑ i ∈ range (f.length / 2), w.getD i 0 * f.getD i 0,
    ∑ i ∈ range (f.length / 2), (w.getD (f.length / 2 + i) 0 - w.getD i 0) *
      (f.getD (f.length / 2 + i) 0 - f.getD i 0))

/-- The state of the honest prover: messages, witnesses, challenges, both tables, and the history. -/
structure ProverState (F EF : Type _) where
  ms : List (EF × EF)
  ws : List F
  rs : List EF
  f : List EF
  w : List EF
  h : List (Step F EF)

/-- One honest round: send the pair, grind with the solver when asked, draw the challenge, fold both tables. -/
def proverStep (S : Sponge F EF) (solve : List (Step F EF) → ℕ → F) (pow : ℕ) (st : ProverState F EF) :
    ProverState F EF :=
  let m := kernelPair st.f st.w
  let h := st.h ++ [.message [m.1, m.2]]
  let wit := if 0 < pow then [solve h pow] else []
  let h := h ++ wit.map (Step.pow pow)
  let r := S.sample h
  ⟨st.ms ++ [m], st.ws ++ wit, st.rs ++ [r], fixHalf st.f r (st.f.length / 2),
    fixHalf st.w r (st.w.length / 2), h ++ [.challenge]⟩

/-- The honest prover after k rounds. -/
def proverRun (S : Sponge F EF) (solve : List (Step F EF) → ℕ → F) (pow : ℕ) (st : ProverState F EF) (k : ℕ) :
    ProverState F EF :=
  (List.range k).foldl (fun st _ => proverStep S solve pow st) st

theorem proverRun_succ (S : Sponge F EF) (solve : List (Step F EF) → ℕ → F) (pow : ℕ) (st : ProverState F EF)
    (k : ℕ) : proverRun S solve pow st (k + 1) = proverStep S solve pow (proverRun S solve pow st k) := by
  simp [proverRun, List.range_succ]

theorem proverRun_ms (S : Sponge F EF) (solve : List (Step F EF) → ℕ → F) (pow : ℕ) (st : ProverState F EF) :
    ∀ k, (proverRun S solve pow st k).ms.length = st.ms.length + k ∧
      (proverRun S solve pow st k).ws.length = st.ws.length + (if 0 < pow then k else 0) ∧
      (proverRun S solve pow st k).rs.length = st.rs.length + k
  | 0 => by simp [proverRun]
  | k + 1 => by
    obtain ⟨h1, h2, h3⟩ := proverRun_ms S solve pow st k
    rw [proverRun_succ]
    refine ⟨by simp [proverStep, h1]; omega, ?_, by simp [proverStep, h3]; omega⟩
    split_ifs with hp
    · simp [proverStep, h2, hp]; omega
    · simp [proverStep, h2, hp]

/-- Later states extend earlier ones. -/
theorem proverRun_prefix (S : Sponge F EF) (solve : List (Step F EF) → ℕ → F) (pow : ℕ) (st : ProverState F EF)
    (k : ℕ) : ∀ j, ∃ ms ws, (proverRun S solve pow st (k + j)).ms = (proverRun S solve pow st k).ms ++ ms ∧
      (proverRun S solve pow st (k + j)).ws = (proverRun S solve pow st k).ws ++ ws
  | 0 => ⟨[], [], by simp, by simp⟩
  | j + 1 => by
    obtain ⟨ms, ws, h1, h2⟩ := proverRun_prefix S solve pow st k j
    rw [← add_assoc, proverRun_succ]
    exact ⟨_, _, by simp only [proverStep, h1, List.append_assoc]; rfl,
      by simp only [proverStep, h2, List.append_assoc]; rfl⟩

theorem foldPrefix_append (P : List EF) (r : EF) : ∀ rs : List EF,
    foldPrefix P (rs ++ [r]) = (foldPrefix P rs).bind fun Q => p3_multilinear_util.poly.mirror.Poly.fix_prefix_var_mut Q r
  | [] => by simp [foldPrefix]
  | q :: rs => by
    simp only [List.cons_append, foldPrefix, Option.bind_eq_bind]
    cases p3_multilinear_util.poly.mirror.Poly.fix_prefix_var_mut P q with
    | none => rfl
    | some Q => exact foldPrefix_append Q r rs

@[simp] theorem length_foldTable (P : List EF) (n : ℕ) (r : List EF) :
    (foldTable P n r).length = 2 ^ (n - r.length) := by simp [foldTable]

/-- Folding at rs ++ [r] is folding at rs, then at r. -/
theorem foldTable_snoc (P : List EF) {n : ℕ} (hP : P.length = 2 ^ n) (rs : List EF) (r : EF)
    (hk : rs.length < n) :
    foldTable P n (rs ++ [r]) = fixHalf (foldTable P n rs) r (2 ^ (n - rs.length - 1)) := by
  have h1 := foldPrefix_eq (rs ++ [r]) P hP (by simp; omega)
  rw [foldPrefix_append, foldPrefix_eq rs P hP hk.le, Option.bind_some,
    fix_prefix_var_mut_eq _ r (n := n - rs.length - 1) (by simp; omega)] at h1
  exact (Option.some.inj h1).symm

theorem replay_snoc' (basis : Basis) (c : EF) {ms : List (EF × EF)} {rs : List EF} (h : ms.length = rs.length)
    (m : EF × EF) (r : EF) :
    replay basis c (ms ++ [m]) (rs ++ [r]) = basis.reduce_claim m.1 m.2 r (replay basis c ms rs) := by
  simp [replay, List.zip_append h]

/-- The tables stay of size 2^(n - k), and the replayed claim is the sum over them. -/
theorem proverRun_tables (S : Sponge F EF) (solve : List (Step F EF) → ℕ → F) (pow : ℕ) (f w : List EF)
    (h : List (Step F EF)) {n : ℕ} (hf : f.length = 2 ^ n) (hw : w.length = 2 ^ n) :
    ∀ k ≤ n, let st := proverRun S solve pow ⟨[], [], [], f, w, h⟩ k
      st.f.length = 2 ^ (n - k) ∧ st.w.length = 2 ^ (n - k) ∧ st.f = foldTable f n st.rs ∧
        st.w = foldTable w n st.rs ∧
        replay .Evaluation (∑ b ∈ range (2 ^ n), f.getD b 0 * w.getD b 0) st.ms st.rs =
          ∑ i ∈ range (2 ^ (n - k)), st.f.getD i 0 * st.w.getD i 0
  | 0, _ => by
    have hf' := foldPrefix_eq [] f hf (Nat.zero_le _)
    have hw' := foldPrefix_eq [] w hw (Nat.zero_le _)
    simp only [foldPrefix, Option.some.injEq] at hf' hw'
    simp [proverRun, hf, hw, ← hf', ← hw', replay]
  | k + 1, hk => by
    obtain ⟨h1, h2, h3, h4, h5⟩ := proverRun_tables S solve pow f w h hf hw k (by omega)
    obtain ⟨hl1, -, hl3⟩ := proverRun_ms S solve pow ⟨[], [], [], f, w, h⟩ k
    simp only [List.length_nil, zero_add] at hl1 hl3
    rw [proverRun_succ]
    set st := proverRun S solve pow ⟨[], [], [], f, w, h⟩ k
    have hm : n - k = (n - (k + 1)) + 1 := by omega
    have hhalf : st.f.length / 2 = 2 ^ (n - (k + 1)) := by rw [h1, hm, pow_succ]; omega
    have hhalf' : st.w.length / 2 = 2 ^ (n - (k + 1)) := by rw [h2, hm, pow_succ]; omega
    simp only [proverStep]
    rw [hhalf, hhalf']
    have hf1 : st.f.length = 2 ^ (n - (k + 1) + 1) := by rw [h1, hm]
    have hw1 : st.w.length = 2 ^ (n - (k + 1) + 1) := by rw [h2, hm]
    refine ⟨length_fixHalf _ _ hf1, length_fixHalf _ _ hw1, ?_, ?_, ?_⟩
    · rw [h3, foldTable_snoc f hf _ _ (by omega), hl3, Nat.sub_sub]
    · rw [h4, foldTable_snoc w hw _ _ (by omega), hl3, Nat.sub_sub]
    · rw [replay_snoc' _ _ (by simp [hl1, hl3]), h5, kernelPair, hhalf]
      rw [hm] at h1 ⊢
      exact reduce_claim_fixHalf st.f st.w hf1 hw1 _

/-- The messages and witnesses of the full run, read at round k, are those round k sent. -/
theorem proverRun_getD (S : Sponge F EF) (solve : List (Step F EF) → ℕ → F) (pow : ℕ) (st0 : ProverState F EF)
    (h0 : st0.ms = [] ∧ st0.ws = []) {k N : ℕ} (hk : k < N) :
    let st := proverRun S solve pow st0 k
    let m := kernelPair st.f st.w
    (proverRun S solve pow st0 N).ms.getD k (0, 0) = m ∧
      (0 < pow → (proverRun S solve pow st0 N).ws[k]? = some (solve (st.h ++ [.message [m.1, m.2]]) pow)) := by
  intro st m
  obtain ⟨ms, ws, h1, h2⟩ := proverRun_prefix S solve pow st0 (k + 1) (N - (k + 1))
  rw [show k + 1 + (N - (k + 1)) = N by omega, proverRun_succ] at h1 h2
  obtain ⟨hl1, hl2, -⟩ := proverRun_ms S solve pow st0 k
  rw [h0.1] at hl1
  rw [h0.2] at hl2
  refine ⟨?_, fun hp => ?_⟩
  · rw [h1]
    simp [proverStep, List.getD_eq_getElem?_getD, hl1, m, st]
  · rw [h2]
    simp only [List.length_nil, zero_add, hp, ↓reduceIte] at hl2
    simp [proverStep, hp, hl2, m, st]

/-- The quadratic verifier accepts the honest rounds: its challenges, claim and history are the prover's. -/
theorem foldlM_verifyRound_honest (S : Sponge F EF) (solve : List (Step F EF) → ℕ → F)
    (hsolve : ∀ h b, 0 < b → S.grind h b (solve h b) = true) (pow : ℕ) (st0 : ProverState F EF)
    (h0 : st0.ms = [] ∧ st0.ws = [] ∧ st0.rs = []) (c : EF) {N : ℕ} :
    ∀ k ≤ N, (List.range k).foldlM (verifyRound S (proverRun S solve pow st0 N).ms
      (proverRun S solve pow st0 N).ws pow .Evaluation) ([], c, st0.h) =
      .ok ((proverRun S solve pow st0 k).rs,
        replay .Evaluation c (proverRun S solve pow st0 k).ms (proverRun S solve pow st0 k).rs,
        (proverRun S solve pow st0 k).h)
  | 0, _ => by simp [proverRun, h0.2.2, h0.1, replay]; rfl
  | k + 1, hk => by
    rw [List.range_succ, List.foldlM_append, foldlM_verifyRound_honest S solve hsolve pow st0 h0 c k (by omega)]
    obtain ⟨hm, hw⟩ := proverRun_getD S solve pow st0 ⟨h0.1, h0.2.1⟩ (show k < N by omega)
    obtain ⟨hl1, -, hl3⟩ := proverRun_ms S solve pow st0 k
    rw [proverRun_succ]
    simp only [List.foldlM_cons, List.foldlM_nil, bind, Except.bind, verifyRound, hm]
    by_cases hp : 0 < pow
    · simp only [hp, ↓reduceIte, hw hp, VerifierTranscript.round, hsolve _ _ hp, bind, Except.bind, pure,
        Except.pure, proverStep, List.map_cons, List.map_nil]
      rw [replay_snoc' _ _ (by rw [hl1, hl3, h0.1, h0.2.2]; rfl)]
    · simp only [hp, ↓reduceIte, VerifierTranscript.round, bind, Except.bind, pure, Except.pure, proverStep,
        List.map_nil, List.append_nil]
      rw [replay_snoc' _ _ (by rw [hl1, hl3, h0.1, h0.2.2]; rfl)]

/-- The honest prover of N rounds, seeded as the verifier seeds. -/
def honestSumcheck (S : Sponge F EF) (solve : List (Step F EF) → ℕ → F) (pow : ℕ) (f w : List EF)
    (h : List (Step F EF)) (N : ℕ) : ProverState F EF :=
  proverRun S solve pow ⟨[], [], [], f, w, if 0 < N then h ++ [SumcheckShape.seed N pow .Evaluation] else h⟩ N

/-- verify_rounds accepts the honest prover: it returns the prover's challenges, the replayed claim and the prover's history. -/
theorem verify_rounds_honest (S : Sponge F EF) (solve : List (Step F EF) → ℕ → F)
    (hsolve : ∀ h b, 0 < b → S.grind h b (solve h b) = true) (pow : ℕ) (f w : List EF) (h : List (Step F EF))
    (c : EF) (N : ℕ) :
    let P := honestSumcheck S solve pow f w h N
    verify_rounds S P.ms P.ws h c N pow .Evaluation = .ok (P.rs, replay .Evaluation c P.ms P.rs, P.h) := by
  intro P
  obtain ⟨hl1, hl2, -⟩ := proverRun_ms S solve pow
    ⟨[], [], [], f, w, if 0 < N then h ++ [SumcheckShape.seed N pow .Evaluation] else h⟩ N
  simp only [List.length_nil, zero_add] at hl1 hl2
  simp only [verify_rounds, P, honestSumcheck, hl1, hl2, ne_eq, not_true_eq_false, ↓reduceIte]
  exact foldlM_verifyRound_honest S solve hsolve pow _ ⟨rfl, rfl, rfl⟩ c N le_rfl

end Plonky3Lean.Proofs.Whir
