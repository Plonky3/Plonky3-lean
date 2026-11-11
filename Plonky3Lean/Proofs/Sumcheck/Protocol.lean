module

public import Plonky3Lean.Spec.Sumcheck
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Algebra.BigOperators.Fin

@[expose] public section

/-!
# Completeness and soundness of the sumcheck protocol

Completeness: the honest prover makes the verifier accept the true sum on every challenge vector.

Soundness: against a false claim, at most n d |F|^(n-1) of the |F|^n challenge vectors accept.

So the error is at most n d / |F|.

The proof is the induction of Thaler, Section 4.1.

Either the first message is the honest one, and then it fails the sum check.

Or it differs, and it agrees with the honest one at r_0 for at most d values of r_0.
-/

namespace Plonky3Lean.Proofs.Sumcheck

open MvPolynomial Finset Plonky3Lean.Spec.Sumcheck

variable {F : Type _} [CommRing F] [DecidableEq F]

/-! ## The cube and the first variable -/

theorem sum_cube_succ {M : Type _} [AddCommMonoid M] {n : ℕ} (f : (Fin (n + 1) → F) → M) :
    ∑ b ∈ cube (n + 1), f b = ∑ a ∈ ({0, 1} : Finset F), ∑ b ∈ cube n, f (Fin.cons a b) := by
  rw [← Finset.sum_product']
  refine Finset.sum_nbij' (fun b => (b 0, Fin.tail b)) (fun p => Fin.cons p.1 p.2) ?_ ?_ ?_ ?_ ?_
  · intro b hb
    simp only [cube, Fintype.mem_piFinset] at hb
    simp [cube, Fin.tail, hb]
  · rintro ⟨a, b⟩ h
    simp only [mem_product, cube, Fintype.mem_piFinset] at h ⊢
    intro i
    exact Fin.cases (by simpa using h.1) (fun j => by simpa using h.2 j) i
  · intro b _; simp
  · rintro ⟨a, b⟩ _; simp
  · intro b _; simp

omit [DecidableEq F] in
theorem eval_fixFirst {n : ℕ} (a : F) (g : MvPolynomial (Fin (n + 1)) F) (s : Fin n → F) :
    eval s (fixFirst a g) = eval (Fin.cons a s) g := by
  rw [eval_eq_eval_mv_eval', fixFirst, Polynomial.eval_map, Polynomial.eval, Polynomial.hom_eval₂]
  simp

theorem eval_honestMessage {n : ℕ} (g : MvPolynomial (Fin (n + 1)) F) (a : F) :
    (honestMessage g).eval a = cubeSum (fixFirst a g) := by
  simp [honestMessage, cubeSum, Polynomial.eval_finsetSum, eval_fixFirst, eval_eq_eval_mv_eval']

theorem cubeSum_succ {n : ℕ} (g : MvPolynomial (Fin (n + 1)) F) :
    cubeSum g = cubeSum (fixFirst 0 g) + cubeSum (fixFirst 1 g) := by
  by_cases h : (0 : F) = 1
  · have : Subsingleton F := subsingleton_of_zero_eq_one h
    simp [Subsingleton.elim (cubeSum g) 0, Subsingleton.elim (cubeSum (fixFirst 0 g)) 0,
      Subsingleton.elim (cubeSum (fixFirst 1 g)) 0]
  · simp [cubeSum, sum_cube_succ, Finset.sum_pair h, eval_fixFirst]

theorem honestMessage_sum {n : ℕ} (g : MvPolynomial (Fin (n + 1)) F) :
    (honestMessage g).eval 0 + (honestMessage g).eval 1 = cubeSum g := by
  rw [eval_honestMessage, eval_honestMessage, cubeSum_succ]

/-! ## Degrees -/

theorem natDegree_honestMessage_le {n d : ℕ} {g : MvPolynomial (Fin (n + 1)) F}
    (hg : IndividualDegreeLE g d) : (honestMessage g).natDegree ≤ d :=
  Polynomial.natDegree_sum_le_of_forall_le _ _ fun _ _ =>
    (Polynomial.natDegree_map_le).trans ((natDegree_finSuccEquiv g).le.trans (hg 0))

omit [DecidableEq F] in
theorem individualDegreeLE_fixFirst {n d : ℕ} {g : MvPolynomial (Fin (n + 1)) F}
    (hg : IndividualDegreeLE g d) (a : F) : IndividualDegreeLE (Spec.Sumcheck.fixFirst a g) d := by
  intro i
  rw [Spec.Sumcheck.fixFirst, Polynomial.eval_eq_sum, Polynomial.sum_def]
  refine (degreeOf_sum_le _ _ _).trans (Finset.sup_le fun k _ => ?_)
  rw [← map_pow]
  exact (degreeOf_mul_C_le _ _ _).trans ((degreeOf_coeff_finSuccEquiv g i k).trans (hg i.succ))

/-! ## Completeness -/

/-- The honest prover makes the verifier accept the true sum, on every challenge vector. -/
theorem completeness {d : ℕ} : ∀ {n : ℕ} (g : MvPolynomial (Fin n) F), IndividualDegreeLE g d →
    ∀ r, Accepts d g (cubeSum g) (honestProver g) r
  | 0, g, _, r => by
    simp [Accepts, cubeSum, cube, Subsingleton.elim r (fun i => i.elim0)]
    rfl
  | n + 1, g, hg, r => by
    refine ⟨natDegree_honestMessage_le hg, honestMessage_sum g, ?_⟩
    simp only [honestProver, Fin.cases_zero, Fin.cases_succ, Fin.tail_cons]
    rw [eval_honestMessage]
    exact completeness _ (individualDegreeLE_fixFirst hg _) _

/-! ## Soundness -/

omit [CommRing F] [DecidableEq F] in
theorem card_filter_succ {n : ℕ} [Fintype F] (p : (Fin (n + 1) → F) → Prop) [DecidablePred p] :
    #{r | p r} = ∑ a : F, #{t : Fin n → F | p (Fin.cons a t)} := by
  simp only [card_filter]
  rw [← Fintype.sum_equiv (Fin.consEquiv fun _ => F) (fun x => if p (Fin.cons x.1 x.2) then 1 else 0)
    _ (fun _ => rfl), Fintype.sum_prod_type]

/-- Two distinct polynomials of degree at most d agree at most at d points. -/
theorem card_eval_eq_le [IsDomain F] [Fintype F] {d : ℕ} {p q : Polynomial F} (hpq : p ≠ q)
    (hp : p.natDegree ≤ d) (hq : q.natDegree ≤ d) : #{a | p.eval a = q.eval a} ≤ d := by
  have h0 : p - q ≠ 0 := sub_ne_zero.mpr hpq
  calc #{a | p.eval a = q.eval a} ≤ (p - q).roots.toFinset.card :=
        card_le_card fun a ha => by simpa [h0, sub_eq_zero] using ha
    _ ≤ (p - q).roots.card := Multiset.toFinset_card_le _
    _ ≤ (p - q).natDegree := Polynomial.card_roots' _
    _ ≤ d := (Polynomial.natDegree_sub_le _ _).trans (max_le hp hq)

open scoped Classical in
/-- Against a false claim, at most n d |F|^(n-1) challenge vectors accept, for every causal prover. -/
theorem soundness [IsDomain F] [Fintype F] {d : ℕ} :
    ∀ {n : ℕ} (g : MvPolynomial (Fin n) F), IndividualDegreeLE g d → ∀ (H : F), H ≠ cubeSum g →
      ∀ P, Causal P → #{r | Accepts d g H P r} * Fintype.card F ≤ n * d * Fintype.card F ^ n
  | 0, g, _, H, hH, P, _ => by
    have : ∀ r : Fin 0 → F, ¬ Accepts d g H P r := fun r h => hH <| by
      simp only [Accepts] at h
      simp [← h, cubeSum, cube, Subsingleton.elim r (fun i => i.elim0)]
      rfl
    simp [Finset.filter_false_of_mem fun r _ => this r]
  | n + 1, g, hg, H, hH, P, hP => by
    -- The first message reads no challenge.
    set p := P 0 (fun _ => 0)
    have hp : ∀ r, P 0 r = p := fun r => hP 0 _ _ fun j hj => absurd hj (Fin.not_lt_zero j)
    set s := honestMessage g
    by_cases hacc : ∃ r, Accepts d g H P r
    swap
    · push Not at hacc
      simp [Finset.filter_false_of_mem fun r _ => hacc r]
    -- A first message that passes the sum check is not the honest one.
    obtain ⟨r₀, hr₀⟩ := hacc
    simp only [Accepts, hp] at hr₀
    have hps : p ≠ s := fun he => hH (hr₀.2.1 ▸ he ▸ honestMessage_sum g)
    -- On the first challenge a, the rest of the run is a sumcheck of g(a, .) against p(a).
    set Q : F → Fin n → (Fin n → F) → Polynomial F := fun a i r' => P i.succ (Fin.cons a r')
    have hQ : ∀ a, Causal (Q a) := fun a i r r' h => hP _ _ _ fun j hj => by
      exact Fin.cases (fun _ => rfl) (fun k hk => by simp [h k (Fin.succ_lt_succ_iff.mp hk)]) j hj
    have key : ∀ a, #{t | Accepts d g H P (Fin.cons a t)} * Fintype.card F ≤
        if p.eval a = s.eval a then Fintype.card F ^ n * Fintype.card F
        else n * d * Fintype.card F ^ n := by
      intro a
      split_ifs with ha
      · exact Nat.mul_le_mul_right _ ((card_le_univ _).trans (by simp))
      · refine le_trans (Nat.mul_le_mul_right _ (card_le_card fun t ht => ?_))
          (soundness _ (individualDegreeLE_fixFirst hg a) (p.eval a)
            (by rwa [← eval_honestMessage]) (Q a) (hQ a))
        simp only [mem_filter, mem_univ, true_and, Accepts, hp, Fin.cons_zero, Fin.tail_cons] at ht ⊢
        exact ht.2.2
    have hroots := card_eval_eq_le hps hr₀.1 (natDegree_honestMessage_le hg)
    rw [card_filter_succ, Finset.sum_mul]
    refine (Finset.sum_le_sum fun a _ => key a).trans ?_
    rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const, smul_eq_mul, smul_eq_mul]
    have := card_le_univ (univ.filter fun a => ¬ p.eval a = s.eval a)
    calc _ ≤ d * (Fintype.card F ^ n * Fintype.card F) +
          Fintype.card F * (n * d * Fintype.card F ^ n) :=
          add_le_add (Nat.mul_le_mul_right _ hroots) (Nat.mul_le_mul_right _ this)
      _ = _ := by ring

end Plonky3Lean.Proofs.Sumcheck
