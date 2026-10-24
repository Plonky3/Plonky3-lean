module

public import Plonky3Lean.Proofs.MultiStark.Ext
public import Mathlib.Algebra.MvPolynomial.SchwartzZippel
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Data.NNRat.BigOperators

@[expose] public section

/-!
# Completeness and soundness of the batched zerocheck

A satisfied batch makes the zerocheck sum vanish at every point, for every alpha and beta.

An unsatisfied batch has some constraint C_ij nonzero at some row b.

The verifier draws alpha, then beta, then the free coordinates of tau, each nonzero.

The sum vanishes only if one of three events happens:

```text
    alpha is a root of  sum_j C_ij(b) X^(k_i - 1 - j)        at most k - 1 roots
    beta  is a root of  sum_i' X^i' (row b batched by alpha)  at most A - 1 roots
    tau   is a zero of  the extension of the batched rows    at most m (q - 1)^(m - 1) of (q - 1)^m
```

Over the q^2 (q - 1)^m draws this is

```text
    (k - 1) / q  +  (A - 1) / q  +  m / (q - 1)
```

the constraint-batching, air-batching and zerocheck terms p3-security charges.
-/

namespace Plonky3Lean.Proofs.MultiStark

open Plonky3Lean.Spec.MultiStark Plonky3Lean.Spec.MultilinearUtil Plonky3Lean.Proofs.MultilinearUtil
  Finset

variable {K : Type _} [Field K]

/-! ## Completeness -/

theorem batched_of_satisfied {A : Instance K} (hA : A.Satisfied) (α : K) {b : ℕ}
    (hb : b < 2 ^ A.log_height) : A.batched α b = 0 := by
  unfold Instance.batched
  suffices ∀ (cs : List (ℕ → K)), (∀ C ∈ cs, C b = 0) → ∀ acc : K,
      cs.foldl (fun acc C => acc * α + C b) acc = acc * α ^ cs.length by
    simpa using this _ (fun C hC => hA C hC b hb) 0
  intro cs hcs
  induction cs with
  | nil => simp
  | cons C cs ih =>
    intro acc
    rw [List.foldl_cons, ih (fun C' h => hcs C' (List.mem_cons_of_mem _ h)),
      hcs C List.mem_cons_self]
    simp [pow_succ]; ring

/-- **Completeness.** A satisfied batch has a zero batched constraint on every row, so its zerocheck sum is zero at every point. -/
theorem zerocheckSum_of_satisfied {batch : List (Instance K)} (h : Satisfied batch) (α β : K)
    (τ : List K) : zerocheckSum batch α β τ = 0 := by
  unfold zerocheckSum rowExt
  refine sum_eq_zero fun b _ => ?_
  rw [batchedRow, sum_eq_zero fun i _ => ?_, mul_zero]
  rw [batched_of_satisfied (A := batch[i]) (h _ (List.getElem_mem i.isLt)) α
    (Nat.mod_lt _ (Nat.two_pow_pos _)), mul_zero]

/-! ## Instances of fewer rows -/

/-- **Per-instance suffixes.** The zerocheck sum is the sum over the instances of beta^i times the extension of instance i's batched constraint at the suffix of tau of its own arity. -/
theorem zerocheckSum_eq_suffix (batch : List (Instance K)) (α β : K) (τ : List K)
    (h : ∀ A ∈ batch, A.log_height ≤ τ.length) :
    zerocheckSum batch α β τ = ∑ i : Fin batch.length,
      β ^ (i : ℕ) * rowExt (batch[i].batched α) (τ.drop (τ.length - batch[i].log_height)) := by
  unfold zerocheckSum batchedRow
  have hlin : ∀ (i : Fin batch.length), rowExt (fun b => β ^ (i : ℕ) *
      batch[i].batched α (b % 2 ^ batch[i].log_height)) τ =
      β ^ (i : ℕ) * rowExt (batch[i].batched α) (τ.drop (τ.length - batch[i].log_height)) := by
    intro i
    have hlen : (τ.drop (τ.length - batch[i].log_height)).length = batch[i].log_height := by
      have := h _ (List.getElem_mem i.isLt); simp; omega
    conv_lhs => rw [← List.take_append_drop (τ.length - batch[i].log_height) τ]
    have := ext_mod_append (batch[i].batched α) (τ.take (τ.length - batch[i].log_height))
      (τ.drop (τ.length - batch[i].log_height))
    rw [hlen] at this
    rw [← this]
    unfold rowExt
    rw [mul_sum]
    exact sum_congr rfl fun b _ => by ring
  rw [← sum_congr rfl fun i _ => hlin i]
  unfold rowExt
  rw [sum_comm]
  exact sum_congr rfl fun b _ => by rw [mul_sum]

/-! ## Polynomials in alpha and beta -/

open Polynomial in
/-- The Horner polynomial of a list: c_0 X^(k-1) + ... + c_(k-1). -/
noncomputable def hornerPoly (cs : List K) : K[X] := cs.foldl (fun acc c => acc * X + C c) 0

open Polynomial in
theorem eval_foldl_horner (cs : List K) (p : K[X]) (α : K) :
    (cs.foldl (fun acc c => acc * X + C c) p).eval α = cs.foldl (fun acc c => acc * α + c) (p.eval α) := by
  induction cs generalizing p with
  | nil => simp
  | cons c cs ih => simp [ih]

open Polynomial in
theorem hornerPoly_append (cs : List K) (c : K) : hornerPoly (cs ++ [c]) = hornerPoly cs * X + C c := by
  simp [hornerPoly]

open Polynomial in
theorem hornerPoly_eq_zero {cs : List K} (h : hornerPoly cs = 0) : ∀ c ∈ cs, c = 0 := by
  induction cs using List.reverseRecOn with
  | nil => simp
  | append_singleton cs c ih =>
    rw [hornerPoly_append] at h
    have hc : c = 0 := by simpa using congrArg (coeff · 0) h
    rw [hc, C_0, add_zero, mul_eq_zero] at h
    have hp := h.resolve_right X_ne_zero
    intro c' hc'
    rcases List.mem_append.mp hc' with hc' | hc'
    · exact ih hp c' hc'
    · simp_all

open Polynomial in
theorem natDegree_hornerPoly_le (cs : List K) : (hornerPoly cs).natDegree ≤ cs.length - 1 := by
  induction cs using List.reverseRecOn with
  | nil => simp [hornerPoly]
  | append_singleton cs c ih =>
    rw [hornerPoly_append, List.length_append, List.length_singleton, Nat.add_sub_cancel]
    refine (natDegree_add_le _ _).trans (max_le ?_ (by simp))
    rcases cs.eq_nil_or_concat with rfl | ⟨cs', c', rfl⟩
    · simp [hornerPoly]
    · refine (natDegree_mul_le).trans ?_
      have := natDegree_X_le (R := K)
      simp only [List.concat_eq_append, List.length_append, List.length_singleton,
        Nat.add_sub_cancel] at ih ⊢
      omega

open Polynomial in
/-- A nonzero polynomial vanishes on at most its degree many points. -/
theorem card_eval_eq_zero_le [Fintype K] [DecidableEq K] {p : K[X]} (hp : p ≠ 0) :
    #{a : K | p.eval a = 0} ≤ p.natDegree := by
  refine le_trans (card_le_card fun a ha => ?_) ((Multiset.toFinset_card_le _).trans (card_roots' p))
  simp only [mem_filter, mem_univ, true_and] at ha
  simpa [mem_roots hp] using ha

open Polynomial in
/-- The polynomial sum_i v_i X^i. -/
noncomputable def powPoly {A : ℕ} (v : Fin A → K) : K[X] := ∑ i : Fin A, C (v i) * X ^ (i : ℕ)

open Polynomial in
theorem eval_powPoly {A : ℕ} (v : Fin A → K) (β : K) :
    (powPoly v).eval β = ∑ i : Fin A, β ^ (i : ℕ) * v i := by
  simp only [powPoly, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X]
  exact sum_congr rfl fun _ _ => mul_comm _ _

open Polynomial in
theorem powPoly_ne_zero {A : ℕ} {v : Fin A → K} {i : Fin A} (hi : v i ≠ 0) : powPoly v ≠ 0 := by
  intro h
  have := congrArg (coeff · (i : ℕ)) h
  simp only [powPoly, finsetSum_coeff, coeff_C_mul, coeff_X_pow, coeff_zero] at this
  rw [sum_eq_single i (fun j _ hj => by simp [show (i : ℕ) ≠ j from fun h => hj (Fin.ext h).symm]) (by simp)] at this
  simp_all

open Polynomial in
theorem natDegree_powPoly_le {A : ℕ} (v : Fin A → K) : (powPoly v).natDegree ≤ A - 1 :=
  natDegree_sum_le_of_forall_le _ _ fun i _ =>
    (natDegree_C_mul_le _ _).trans ((natDegree_X_pow_le _).trans (by omega))

/-! ## The point -/

/-- Fibres: a filter on a product is at most the left set times a bound on every fibre. -/
theorem card_filter_product_le {α β : Type _} (s : Finset α) (t : Finset β) (P : α → β → Prop)
    [∀ a b, Decidable (P a b)] (n : ℕ) (h : ∀ a ∈ s, #{b ∈ t | P a b} ≤ n) :
    #{x ∈ s ×ˢ t | P x.1 x.2} ≤ #s * n := by
  rw [card_filter, sum_product]
  simp only [← card_filter]
  simpa using sum_le_card_nsmul s _ n h

/-- **Schwartz-Zippel at the zerocheck point.** A table nonzero somewhere on the m-cube has a zero extension at at most m (q - 1)^(m - 1) of the (q - 1)^m points with nonzero coordinates. -/
theorem card_rowExt_eq_zero_le [Fintype K] [DecidableEq K] (g : ℕ → K) {m b : ℕ} (hb : b < 2 ^ m)
    (hg : g b ≠ 0) :
    #{τ ∈ Fintype.piFinset (fun _ : Fin m => univ.erase (0 : K)) | rowExt g (List.ofFn τ) = 0}
      ≤ m * (Fintype.card K - 1) ^ (m - 1) := by
  set P := mlePoly ((List.range (2 ^ m)).map g) m
  have hP : P ≠ 0 := fun h => hg (by
    have := eval_mlePoly_vertex ((List.range (2 ^ m)).map g) hb
    change MvPolynomial.eval _ P = _ at this
    rw [h, map_zero] at this
    simpa [List.getD_eq_getElem?_getD, hb] using this.symm)
  have hsz := MvPolynomial.schwartz_zippel_sum_degreeOf hP fun _ => univ.erase (0 : K)
  have hev : ∀ x, MvPolynomial.eval x P = rowExt g (List.ofFn x) := fun x =>
    (ext_eq_eval_mlePoly g x).symm
  simp_rw [hev] at hsz
  set R := #{τ ∈ Fintype.piFinset (fun _ : Fin m => univ.erase (0 : K)) | rowExt g (List.ofFn τ) = 0}
  have hS : #(univ.erase (0 : K)) = Fintype.card K - 1 := by
    rw [card_erase_of_mem (mem_univ _), card_univ]
  have hq : 1 < Fintype.card K := Fintype.one_lt_card
  have hNq : (0 : ℚ) < (Fintype.card K - 1 : ℕ) := by exact_mod_cast (by omega : 0 < Fintype.card K - 1)
  rw [hS, prod_const, card_univ, Fintype.card_fin] at hsz
  have key : (R : ℚ) / ((Fintype.card K - 1 : ℕ) : ℚ) ^ m ≤ m / ((Fintype.card K - 1 : ℕ) : ℚ) := by
    have h1 := NNRat.coe_le_coe.mpr hsz
    simp only [NNRat.cast_sum, NNRat.cast_div, NNRat.cast_natCast, NNRat.coe_pow] at h1
    refine h1.trans ?_
    calc _ ≤ ∑ _i : Fin m, (1 : ℚ) / ((Fintype.card K - 1 : ℕ) : ℚ) :=
          sum_le_sum fun i _ => div_le_div_of_nonneg_right
            (by exact_mod_cast mlePoly_isMultilinear ((List.range (2 ^ m)).map g) m i) hNq.le
      _ = _ := by simp [div_eq_mul_inv]
  rw [div_le_div_iff₀ (by positivity) hNq] at key
  rcases m with _ | m
  · have : (R : ℚ) ≤ 0 := by simp at key; nlinarith
    simp only [Nat.zero_sub, pow_zero, zero_mul, nonpos_iff_eq_zero]
    exact_mod_cast le_antisymm this (by positivity)
  · have : (R : ℚ) ≤ (m + 1 : ℕ) * ((Fintype.card K - 1 : ℕ) : ℚ) ^ m := by
      refine le_of_mul_le_mul_right ?_ hNq
      calc _ ≤ _ := key
        _ = _ := by push_cast; ring
    simpa using (show R ≤ (m + 1) * (Fintype.card K - 1) ^ m by exact_mod_cast this)

/-! ## The three events -/

theorem batched_eq_eval (A : Instance K) (α : K) (b : ℕ) :
    A.batched α b = (hornerPoly (A.constraints.map (· b))).eval α := by
  rw [hornerPoly, eval_foldl_horner, Instance.batched, List.foldl_map]; simp

theorem batchedRow_eq_eval (batch : List (Instance K)) (α β : K) (b : ℕ) :
    batchedRow batch α β b =
      (powPoly fun j : Fin batch.length => batch[j].batched α (b % 2 ^ batch[j].log_height)).eval β := by
  rw [eval_powPoly]; rfl

theorem card_cube [Fintype K] [DecidableEq K] (m : ℕ) :
    #(Fintype.piFinset fun _ : Fin m => univ.erase (0 : K)) = (Fintype.card K - 1) ^ m := by
  rw [Fintype.card_piFinset, prod_const, card_erase_of_mem (mem_univ _), card_univ, card_univ,
    Fintype.card_fin]

/-- **Soundness of the batched zerocheck.** An unsatisfied batch over cubes of at most m variables, with at most k constraints per instance, has a zero zerocheck sum on at most

(k - 1) q (q - 1)^m + q (A - 1) (q - 1)^m + q^2 m (q - 1)^(m - 1)

of the q^2 (q - 1)^m draws of alpha, beta and a point with nonzero coordinates. -/
theorem card_zerocheck_eq_zero_le [Fintype K] [DecidableEq K] {batch : List (Instance K)}
    (hsat : ¬ Satisfied batch) {m k : ℕ} (hm : ∀ A ∈ batch, A.log_height ≤ m)
    (hk : ∀ A ∈ batch, A.constraints.length ≤ k) :
    #{x ∈ (univ : Finset K) ×ˢ ((univ : Finset K) ×ˢ
        Fintype.piFinset (fun _ : Fin m => univ.erase (0 : K))) |
        zerocheckSum batch x.1 x.2.1 (List.ofFn x.2.2) = 0}
      ≤ (k - 1) * (Fintype.card K * (Fintype.card K - 1) ^ m) +
        Fintype.card K * ((batch.length - 1) * (Fintype.card K - 1) ^ m) +
        Fintype.card K * (Fintype.card K * (m * (Fintype.card K - 1) ^ (m - 1))) := by
  simp only [Satisfied, Instance.Satisfied, not_forall, exists_prop] at hsat
  obtain ⟨A, hA, C, hC, b, hb, hCb⟩ := hsat
  obtain ⟨n, hn, rfl⟩ := List.mem_iff_getElem.mp hA
  set i : Fin batch.length := ⟨n, hn⟩
  have hbm : b < 2 ^ m := lt_of_lt_of_le hb (Nat.pow_le_pow_right two_pos (hm _ hA))
  set T := Fintype.piFinset fun _ : Fin m => univ.erase (0 : K)
  have hT : #T = (Fintype.card K - 1) ^ m := card_cube m
  have hhorner : hornerPoly (batch[n].constraints.map (· b)) ≠ 0 := fun h =>
    hCb (hornerPoly_eq_zero h _ (List.mem_map.mpr ⟨C, hC, rfl⟩))
  have hdeg : (hornerPoly (batch[n].constraints.map (· b))).natDegree ≤ k - 1 :=
    (natDegree_hornerPoly_le _).trans (by simpa using Nat.sub_le_sub_right (hk _ hA) 1)
  -- Every bad draw lands in one of the three events.
  refine le_trans (card_le_card (t :=
      {x ∈ (univ : Finset K) ×ˢ ((univ : Finset K) ×ˢ T) | batch[n].batched x.1 b = 0} ∪
      {x ∈ (univ : Finset K) ×ˢ ((univ : Finset K) ×ˢ T) | batch[n].batched x.1 b ≠ 0 ∧ batchedRow batch x.1 x.2.1 b = 0} ∪
      {x ∈ (univ : Finset K) ×ˢ ((univ : Finset K) ×ˢ T) |
        batchedRow batch x.1 x.2.1 b ≠ 0 ∧ zerocheckSum batch x.1 x.2.1 (List.ofFn x.2.2) = 0})
      fun x hx => ?_) ((card_union_le _ _).trans (add_le_add (card_union_le _ _) le_rfl) |>.trans
      (add_le_add (add_le_add ?_ ?_) ?_))
  · simp only [mem_filter] at hx
    simp only [mem_union, mem_filter, hx.1, true_and]
    by_cases h1 : batch[n].batched x.1 b = 0
    · exact Or.inl (Or.inl h1)
    · by_cases h2 : batchedRow batch x.1 x.2.1 b = 0
      · exact Or.inl (Or.inr ⟨h1, h2⟩)
      · exact Or.inr ⟨h2, hx.2⟩
  -- alpha is a root of the Horner polynomial of row b.
  · rw [filter_product_left (fun α => batch[n].batched α b = 0), card_product, card_product,
      card_univ, hT]
    refine Nat.mul_le_mul_right _ ((le_of_eq ?_).trans ((card_eval_eq_zero_le hhorner).trans hdeg))
    simp only [batched_eq_eval]
  -- beta is a root of the polynomial of the instances' batched rows.
  · rw [← card_univ (α := K)]
    refine card_filter_product_le (univ : Finset K) ((univ : Finset K) ×ˢ T)
      (fun α y => batch[n].batched α b ≠ 0 ∧ batchedRow batch α y.1 b = 0) _ fun α _ => ?_
    by_cases hα : batch[n].batched α b = 0
    · simp [hα]
    · simp only [ne_eq, hα, not_false_eq_true, true_and]
      rw [filter_product_left (fun β => batchedRow batch α β b = 0), card_product, hT]
      refine Nat.mul_le_mul_right _ ((le_of_eq ?_).trans
        ((card_eval_eq_zero_le (powPoly_ne_zero (i := i)
          (v := fun j : Fin batch.length => batch[j].batched α (b % 2 ^ batch[j].log_height)) ?_)).trans (natDegree_powPoly_le _)))
      · simp only [batchedRow_eq_eval]
      · simpa [i, Nat.mod_eq_of_lt hb] using hα
  -- the free coordinates of tau are a zero of the extension.
  · rw [← card_univ (α := K)]
    refine card_filter_product_le (univ : Finset K) ((univ : Finset K) ×ˢ T)
      (fun α y => batchedRow batch α y.1 b ≠ 0 ∧ zerocheckSum batch α y.1 (List.ofFn y.2) = 0) _
      fun α _ => ?_
    refine card_filter_product_le (univ : Finset K) T
      (fun β τ => batchedRow batch α β b ≠ 0 ∧ zerocheckSum batch α β (List.ofFn τ) = 0) _
      fun β _ => ?_
    by_cases hβ : batchedRow batch α β b = 0
    · simp [hβ]
    · simp only [ne_eq, hβ, not_false_eq_true, true_and]
      exact card_rowExt_eq_zero_le _ hbm hβ

end Plonky3Lean.Proofs.MultiStark
