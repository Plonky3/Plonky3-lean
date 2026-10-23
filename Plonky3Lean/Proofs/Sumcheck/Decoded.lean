module

public import Plonky3Lean.Proofs.Sumcheck.Protocol

@[expose] public section

/-!
# Sumcheck with compressed round messages

A verifier that does not receive g_i itself, but a message m_i it decodes with the running claim c_i:

```text
    g_i = dec(c_i, m_i)
```

When every decoding has degree at most d and satisfies g_i(0) + g_i(1) = c_i, the sum check passes by construction, and the verifier only keeps the claim:

```text
    c_{i+1} = dec(c_i, m_i)(r_i),    accept iff g(r) = c_n
```

This verifier accepts exactly when the verifier of Section 4.1 accepts the decoded polynomials.

Its soundness is therefore n d / |F|, and it is complete when every admissible polynomial has a message.
-/

namespace Plonky3Lean.Proofs.Sumcheck

open MvPolynomial Finset Plonky3Lean.Spec.Sumcheck

variable {F : Type _} [CommRing F] [DecidableEq F] {Msg : Type _}

/-- The claim left after replaying the messages against the challenges. -/
def finalClaim (dec : F → Msg → Polynomial F) (c : F) : List Msg → List F → F
  | m :: ms, r :: rs => finalClaim dec ((dec c m).eval r) ms rs
  | _, _ => c

omit [DecidableEq F] in
theorem finalClaim_snoc (dec : F → Msg → Polynomial F) (c : F) :
    ∀ (ms : List Msg) (rs : List F), ms.length = rs.length → ∀ m r,
      finalClaim dec c (ms ++ [m]) (rs ++ [r]) = (dec (finalClaim dec c ms rs) m).eval r
  | [], [], _, _, _ => rfl
  | m' :: ms, r' :: rs, h, m, r => by
    simp only [List.cons_append, finalClaim]
    exact finalClaim_snoc dec _ ms rs (by simpa using h) m r

/-- The polynomials the verifier decodes, as a prover strategy of Section 4.1. -/
noncomputable def induced (dec : F → Msg → Polynomial F) :
    {n : ℕ} → F → (Fin n → (Fin n → F) → Msg) → Fin n → (Fin n → F) → Polynomial F
  | 0, _, _ => fun i => i.elim0
  | _ + 1, c, M => fun i r =>
    Fin.cases (dec c (M 0 r))
      (fun j => induced dec ((dec c (M 0 r)).eval (r 0)) (fun i r' => M i.succ (Fin.cons (r 0) r'))
        j (Fin.tail r)) i

omit [CommRing F] [DecidableEq F] in
theorem causal_zero {α : Type _} {n : ℕ} {M : Fin (n + 1) → (Fin (n + 1) → F) → α} (hM : Causal M)
    (r r' : Fin (n + 1) → F) : M 0 r = M 0 r' :=
  hM 0 r r' fun j hj => absurd hj (Fin.not_lt_zero j)

omit [CommRing F] [DecidableEq F] in
theorem causal_shift {α : Type _} {n : ℕ} {M : Fin (n + 1) → (Fin (n + 1) → F) → α} (hM : Causal M)
    (a : F) : Causal fun (i : Fin n) r' => M i.succ (Fin.cons a r') := fun i r r' h =>
  hM _ _ _ fun j hj =>
    Fin.cases (fun _ => rfl) (fun k hk => by simp [h k (Fin.succ_lt_succ_iff.mp hk)]) j hj

omit [DecidableEq F] in
theorem induced_zero (dec : F → Msg → Polynomial F) {n : ℕ} (c : F)
    (M : Fin (n + 1) → (Fin (n + 1) → F) → Msg) (r : Fin (n + 1) → F) :
    induced dec c M 0 r = dec c (M 0 r) := rfl

omit [DecidableEq F] in
theorem induced_succ (dec : F → Msg → Polynomial F) {n : ℕ} (c : F)
    {M : Fin (n + 1) → (Fin (n + 1) → F) → Msg} (hM : Causal M) (r : Fin (n + 1) → F) :
    (fun i r' => induced dec c M i.succ (Fin.cons (r 0) r')) =
      induced dec ((dec c (M 0 r)).eval (r 0)) (fun i r' => M i.succ (Fin.cons (r 0) r')) := by
  funext i r'
  simp only [induced, Fin.cases_succ, Fin.cons_zero, Fin.tail_cons, causal_zero hM (Fin.cons (r 0) r') r]

omit [DecidableEq F] in
/-- A causal message strategy decodes to a causal prover. -/
theorem induced_causal (dec : F → Msg → Polynomial F) :
    ∀ {n : ℕ} (c : F) (M : Fin n → (Fin n → F) → Msg), Causal M → Causal (induced dec c M)
  | 0, _, _, _ => fun i => i.elim0
  | n + 1, c, M, hM => fun i r r' h => by
    refine Fin.cases (by simp [induced, causal_zero hM r r']) (fun j h => ?_) i h
    have h0 : r 0 = r' 0 := h 0 (Fin.succ_pos j)
    simp only [induced, Fin.cases_succ, causal_zero hM r r', h0]
    refine induced_causal dec _ _ (causal_shift hM _) j _ _ fun k hk => ?_
    simpa [Fin.tail] using h k.succ (Fin.succ_lt_succ_iff.mpr hk)

omit [DecidableEq F] in
/-- The verifier of Section 4.1 accepts the decoded polynomials exactly when g(r) is the replayed claim. -/
theorem accepts_induced_iff (dec : F → Msg → Polynomial F) {d : ℕ}
    (hdeg : ∀ c m, (dec c m).natDegree ≤ d) (hsum : ∀ c m, (dec c m).eval 0 + (dec c m).eval 1 = c) :
    ∀ {n : ℕ} (g : MvPolynomial (Fin n) F) (c : F) (M : Fin n → (Fin n → F) → Msg), Causal M →
      ∀ r, Accepts d g c (induced dec c M) r ↔
        eval r g = finalClaim dec c (List.ofFn fun i => M i r) (List.ofFn r)
  | 0, g, c, M, _, r => by simp [Accepts, finalClaim]
  | n + 1, g, c, M, hM, r => by
    simp only [Accepts, induced_zero, hdeg, hsum, true_and, List.ofFn_succ, finalClaim]
    rw [induced_succ dec c hM r, accepts_induced_iff dec hdeg hsum _ _ _ (causal_shift hM _),
      eval_fixFirst, Fin.cons_self_tail]
    rfl

open scoped Classical in
/-- Against a false claim, at most n d |F|^(n-1) challenge vectors replay to g(r), for every causal message strategy. -/
theorem soundness_decoded [IsDomain F] [Fintype F] (dec : F → Msg → Polynomial F) {d : ℕ}
    (hdeg : ∀ c m, (dec c m).natDegree ≤ d) (hsum : ∀ c m, (dec c m).eval 0 + (dec c m).eval 1 = c)
    {n : ℕ} (g : MvPolynomial (Fin n) F) (hg : IndividualDegreeLE g d) (H : F) (hH : H ≠ cubeSum g)
    (M : Fin n → (Fin n → F) → Msg) (hM : Causal M) :
    #{r | eval r g = finalClaim dec H (List.ofFn fun i => M i r) (List.ofFn r)} * Fintype.card F ≤
      n * d * Fintype.card F ^ n := by
  have := soundness g hg H hH _ (induced_causal dec H M hM)
  simpa only [accepts_induced_iff dec hdeg hsum g H M hM] using this

/-- When every polynomial of degree at most d with g_i(0) + g_i(1) = c has a message, the honest messages replay to g(r). -/
theorem completeness_decoded (dec : F → Msg → Polynomial F) (enc : Polynomial F → Msg) {d : ℕ}
    (henc : ∀ c p, p.natDegree ≤ d → p.eval 0 + p.eval 1 = c → dec c (enc p) = p) :
    ∀ {n : ℕ} (g : MvPolynomial (Fin n) F), IndividualDegreeLE g d → ∀ r,
      eval r g = finalClaim dec (cubeSum g) (List.ofFn fun i => enc (honestProver g i r)) (List.ofFn r)
  | 0, g, _, r => by
    simp [finalClaim, cubeSum, cube, Subsingleton.elim r (fun i => i.elim0)]
    rfl
  | n + 1, g, hg, r => by
    simp only [List.ofFn_succ, finalClaim, honestProver, Fin.cases_zero, Fin.cases_succ]
    rw [henc _ _ (natDegree_honestMessage_le hg) (honestMessage_sum g), eval_honestMessage,
      ← Fin.cons_self_tail r, ← eval_fixFirst]
    simpa using completeness_decoded dec enc henc _ (individualDegreeLE_fixFirst hg (r 0)) (Fin.tail r)

end Plonky3Lean.Proofs.Sumcheck
