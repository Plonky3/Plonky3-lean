module

public import P3UniStark
public import Plonky3Lean.Proofs.UniStark.Poly
public import Plonky3Lean.Proofs.UniStark.Folder

@[expose] public section

/-!
# The verifier's chunk recombination inverts the prover's split

Split the quotient coset s H' of order N = c m into the c chunks D_i = s omega^i H'^c, each of order m.

Write Z_j for the vanishing polynomial of chunk j, normalized as (x / s_j)^m - 1, and s_i for the first point of chunk i.

```text
    L_i(X) = prod_(j != i) Z_j(X) / Z_j(s_i)        1 on D_i, 0 on every other chunk
```

Z_j is constant on each chunk, since x^m = s_i^m there.

So for q_i the interpolant of Q on D_i, the polynomial sum_i L_i q_i agrees with Q on all N points.

Its degree is below (c - 1) m + m = N, so it is Q whenever deg Q < N.
-/

set_option linter.unusedSectionVars false

namespace Plonky3Lean.Proofs.UniStark

open Polynomial Finset
open p3_commit.domain.mirror p3_field.coset.mirror p3_dft.mirror p3_uni_stark.verifier.mirror
open Plonky3Lean.Spec.Commit Plonky3Lean.Proofs.Commit Plonky3Lean.Proofs.Dft

variable {K : Type _} [Field K] [DecidableEq K] {G : Gen K} (hV : GenValid G) (qd : Coset G) (l : ℕ)

/-- The vanishing polynomial of chunk j, normalized as (x / s_j)^m - 1. -/
noncomputable def chunkZ (j : ℕ) : K[X] :=
  (C (chunk G hV qd l j).shift⁻¹ * X) ^ 2 ^ (qd.log_size - l) - 1

theorem eval_chunkZ (j : ℕ) (x : K) :
    (chunkZ hV qd l j).eval x = Coset.vanishing_poly_at_point G (chunk G hV qd l j) x := by
  simp [chunkZ, Coset.vanishing_poly_at_point, TwoAdicMultiplicativeCoset.shift_inverse, chunk,
    mul_comm]

theorem natDegree_chunkZ_le (j : ℕ) : (chunkZ hV qd l j).natDegree ≤ 2 ^ (qd.log_size - l) := by
  refine (natDegree_sub_le _ _).trans (max_le ?_ (by simp))
  refine natDegree_pow_le.trans ?_
  have : (C (chunk G hV qd l j).shift⁻¹ * X).natDegree ≤ 1 :=
    (natDegree_C_mul_le _ _).trans natDegree_X_le
  calc _ ≤ 2 ^ (qd.log_size - l) * 1 := Nat.mul_le_mul_left _ this
    _ = _ := mul_one _

/-- Z_j takes one value on each chunk: its value at the chunk's first point. -/
theorem vanishing_chunk_point (i j t : ℕ) :
    Coset.vanishing_poly_at_point G (chunk G hV qd l j)
        ((chunk G hV qd l i).shift * (chunk G hV qd l i).subgroup_generator ^ t) =
      Coset.vanishing_poly_at_point G (chunk G hV qd l j) (chunk G hV qd l i).shift := by
  have hg := (prim G hV (chunk G hV qd l i)).pow_eq_one
  simp only [Coset.vanishing_poly_at_point]
  rw [mul_right_comm, mul_pow, ← pow_mul, mul_comm t, pow_mul]
  simp [chunk] at hg ⊢
  rw [hg, one_pow, mul_one]

/-- Z_j vanishes at the first point of chunk j, and only there among the first points. -/
theorem vanishing_chunk_first {i j : ℕ} (hi : i < 2 ^ l) (hj : j < 2 ^ l) (hl : l ≤ qd.log_size) :
    Coset.vanishing_poly_at_point G (chunk G hV qd l j) (chunk G hV qd l i).shift = 0 ↔ i = j := by
  have hω := prim G hV qd
  have hs := qd.shift_ne_zero
  have hw := gen_ne_zero G hV qd
  have hk : 2 ^ qd.log_size = 2 ^ l * 2 ^ (qd.log_size - l) := by rw [← pow_add]; congr 1; omega
  have hlt : ∀ a < 2 ^ l, a * 2 ^ (qd.log_size - l) < 2 ^ qd.log_size := fun a ha => by
    rw [hk]; exact Nat.mul_lt_mul_of_pos_right ha (by positivity)
  have e : qd.shift * qd.subgroup_generator ^ i * (qd.shift * qd.subgroup_generator ^ j)⁻¹ =
      qd.subgroup_generator ^ i / qd.subgroup_generator ^ j := by
    field_simp
  simp only [Coset.vanishing_poly_at_point, TwoAdicMultiplicativeCoset.shift_inverse, chunk,
    sub_eq_zero]
  rw [e, div_pow, div_eq_one_iff_eq (pow_ne_zero _ (pow_ne_zero _ hw)), ← pow_mul, ← pow_mul]
  exact ⟨fun h => Nat.eq_of_mul_eq_mul_right (by positivity) (hω.pow_inj (hlt i hi) (hlt j hj) h),
    fun h => h ▸ rfl⟩

/-- The Lagrange factor of chunk i: the product over the other chunks j of Z_j / Z_j(s_i). -/
noncomputable def chunkL (i : ℕ) : K[X] :=
  ∏ j ∈ (range (2 ^ l)).erase i,
    C (Coset.vanishing_poly_at_point G (chunk G hV qd l j) (chunk G hV qd l i).shift)⁻¹ *
      chunkZ hV qd l j

/-- The interpolant of Q on chunk i. -/
noncomputable def chunkInterp (Q : K[X]) (i : ℕ) : K[X] :=
  interpolant (chunk G hV qd l i).shift (chunk G hV qd l i).subgroup_generator
    (chunk G hV qd l i).log_size fun t => Q.eval (cosetPoints (chunk G hV qd l i).shift
      (chunk G hV qd l i).subgroup_generator (chunk G hV qd l i).log_size t)

theorem natDegree_chunkL_le (i : ℕ) (hi : i < 2 ^ l) :
    (chunkL hV qd l i).natDegree ≤ (2 ^ l - 1) * 2 ^ (qd.log_size - l) := by
  refine (natDegree_prod_le _ _).trans ?_
  have hcard : ((range (2 ^ l)).erase i).card = 2 ^ l - 1 := by
    rw [card_erase_of_mem (mem_range.mpr hi), card_range]
  rw [← hcard, ← smul_eq_mul]
  exact sum_le_card_nsmul _ _ _ fun j _ =>
    (natDegree_C_mul_le _ _).trans (natDegree_chunkZ_le hV qd l j)

theorem eval_chunkL_point {i i' : ℕ} (hi : i < 2 ^ l) (hi' : i' < 2 ^ l) (hl : l ≤ qd.log_size)
    (t : ℕ) :
    (chunkL hV qd l i').eval
        ((chunk G hV qd l i).shift * (chunk G hV qd l i).subgroup_generator ^ t) =
      if i' = i then 1 else 0 := by
  simp only [chunkL, eval_prod, eval_mul, eval_C, eval_chunkZ, vanishing_chunk_point]
  split_ifs with h
  · subst h
    refine prod_eq_one fun j hj => inv_mul_cancel₀ ?_
    obtain ⟨hne, hj⟩ := mem_erase.mp hj
    exact fun h0 => hne ((vanishing_chunk_first hV qd l hi' (mem_range.mp hj) hl).mp h0).symm
  · exact prod_eq_zero (mem_erase.mpr ⟨fun e => h e.symm, mem_range.mpr hi⟩)
      (by rw [(vanishing_chunk_first hV qd l hi hi hl).mpr rfl, mul_zero])

theorem eval_chunkInterp_point (Q : K[X]) (i : ℕ) {t : ℕ} (ht : t < 2 ^ (qd.log_size - l)) :
    (chunkInterp hV qd l Q i).eval
        ((chunk G hV qd l i).shift * (chunk G hV qd l i).subgroup_generator ^ t) =
      Q.eval ((chunk G hV qd l i).shift * (chunk G hV qd l i).subgroup_generator ^ t) := by
  classical
  have hinj : Set.InjOn (cosetPoints (chunk G hV qd l i).shift
      (chunk G hV qd l i).subgroup_generator (chunk G hV qd l i).log_size)
      ↑(univ : Finset (Fin (2 ^ (chunk G hV qd l i).log_size))) :=
    (cosetPoints_injective (prim G hV (chunk G hV qd l i)) (chunk G hV qd l i).shift_ne_zero).injOn
  exact Lagrange.eval_interpolate_at_node (i := ⟨t, ht⟩) _ hinj (mem_univ _)

theorem natDegree_chunkInterp_le (Q : K[X]) (i : ℕ) :
    (chunkInterp hV qd l Q i).natDegree ≤ 2 ^ (qd.log_size - l) - 1 := by
  classical
  have hinj : Set.InjOn (cosetPoints (chunk G hV qd l i).shift
      (chunk G hV qd l i).subgroup_generator (chunk G hV qd l i).log_size)
      ↑(univ : Finset (Fin (2 ^ (chunk G hV qd l i).log_size))) :=
    (cosetPoints_injective (prim G hV (chunk G hV qd l i)) (chunk G hV qd l i).shift_ne_zero).injOn
  have hd := Lagrange.degree_interpolate_lt (r := fun t => Q.eval (cosetPoints
    (chunk G hV qd l i).shift (chunk G hV qd l i).subgroup_generator (chunk G hV qd l i).log_size t)) hinj
  rw [card_univ, Fintype.card_fin] at hd
  by_cases h0 : chunkInterp hV qd l Q i = 0
  · simp [h0]
  · have := (natDegree_lt_iff_degree_lt h0).mpr hd
    simp only [chunk] at this
    omega

/-- Recombining the chunk interpolants of Q with the Lagrange factors gives Q, when deg Q < N. -/
theorem recombine (hN : GenNested G) (hl : l ≤ qd.log_size) (Q : K[X])
    (hQ : Q.degree < (2 ^ qd.log_size : ℕ)) (ζ : K) :
    ∑ i ∈ range (2 ^ l), (chunkL hV qd l i).eval ζ * (chunkInterp hV qd l Q i).eval ζ = Q.eval ζ := by
  have hω := prim G hV qd
  have hs := qd.shift_ne_zero
  have hk : 2 ^ qd.log_size = 2 ^ l * 2 ^ (qd.log_size - l) := by rw [← pow_add]; congr 1; omega
  have hm : 0 < 2 ^ (qd.log_size - l) := by positivity
  have hN0 : 0 < 2 ^ qd.log_size := by positivity
  set P := ∑ i ∈ range (2 ^ l), chunkL hV qd l i * chunkInterp hV qd l Q i with hP
  suffices hPQ : P = Q by
    have := congrArg (eval ζ) hPQ
    rw [hP, eval_finsetSum] at this
    simpa using this
  have hinj : Set.InjOn (fun n => qd.shift * qd.subgroup_generator ^ n) (range (2 ^ qd.log_size)) :=
    fun a ha b hb h => hω.pow_inj (mem_range.mp ha) (mem_range.mp hb) (mul_left_cancel₀ hs h)
  refine eq_of_degree_sub_lt_of_eval_finset_eq ((range (2 ^ qd.log_size)).image
    fun n => qd.shift * qd.subgroup_generator ^ n) ?_ ?_
  · rw [card_image_of_injOn hinj, card_range]
    refine (degree_sub_le _ _).trans_lt (max_lt ?_ hQ)
    refine degree_le_natDegree.trans_lt (Nat.cast_lt.mpr ?_)
    refine lt_of_le_of_lt (natDegree_sum_le_of_forall_le _ _ (n := 2 ^ qd.log_size - 1)
      fun i hi => (natDegree_mul_le).trans ?_) (by omega)
    have h1 := natDegree_chunkL_le hV qd l i (mem_range.mp hi)
    have h2 := natDegree_chunkInterp_le hV qd l Q i
    have : (2 ^ l - 1) * 2 ^ (qd.log_size - l) + 2 ^ (qd.log_size - l) = 2 ^ qd.log_size := by
      rw [hk, ← Nat.succ_mul, Nat.succ_eq_add_one, Nat.sub_add_cancel Nat.one_le_two_pow]
    omega
  · intro x hx
    obtain ⟨n, hn, rfl⟩ := mem_image.mp hx
    have hn' := mem_range.mp hn
    have hi : n % 2 ^ l < 2 ^ l := Nat.mod_lt _ (by positivity)
    have ht : n / 2 ^ l < 2 ^ (qd.log_size - l) := by
      rw [Nat.div_lt_iff_lt_mul (by positivity), mul_comm, ← hk]; exact hn'
    have hpt := chunk_point G hV hN qd hl (n % 2 ^ l) (n / 2 ^ l)
    rw [Nat.mod_add_div] at hpt
    rw [← hpt, hP, eval_finsetSum, sum_eq_single (n % 2 ^ l)]
    · simp only [eval_mul, eval_chunkL_point hV qd l hi hi hl, ↓reduceIte, one_mul,
        eval_chunkInterp_point hV qd l Q _ ht]
    · intro i' hi' hne
      simp only [eval_mul, eval_chunkL_point hV qd l hi (mem_range.mp hi') hl, hne, ↓reduceIte,
        zero_mul]
    · exact fun h => absurd (mem_range.mpr hi) h

/-! ## The transcribed recombination -/

theorem foldlM_mul_some {α : Type _} (l : List α) (f : K → α → Option K) (g : α → K)
    (h : ∀ acc, ∀ j ∈ l, f acc j = some (acc * g j)) (a : K) :
    l.foldlM f a = some (a * (l.map g).prod) := by
  induction l generalizing a with
  | nil => simp
  | cons j l ih =>
    rw [List.foldlM_cons, h a j (by simp)]
    simp only [Option.bind_eq_bind, Option.bind_some]
    rw [ih (fun acc j hj => h acc j (by simp [hj]))]
    simp [mul_assoc]

theorem foldlM_add_some {α : Type _} (l : List α) (f : K → α → Option K) (g : α → K)
    (h : ∀ acc, ∀ j ∈ l, f acc j = some (acc + g j)) (a : K) :
    l.foldlM f a = some (a + (l.map g).sum) := by
  induction l generalizing a with
  | nil => simp
  | cons j l ih =>
    rw [List.foldlM_cons, h a j (by simp)]
    simp only [Option.bind_eq_bind, Option.bind_some]
    rw [ih (fun acc j hj => h acc j (by simp [hj]))]
    simp [add_assoc]

theorem prod_filter_range_ne (c i : ℕ) (g : ℕ → K) :
    (((List.range c).filter (· ≠ i)).map g).prod = ∏ j ∈ (range c).erase i, g j := by
  have : (List.range c).filter (fun x => decide (x ≠ i)) = (List.range c).filter (· != i) := by
    congr 1
  rw [this, ← (List.nodup_range).erase_eq_filter, Finset.prod_eq_multiset_prod]
  simp [Finset.erase_val, Finset.range_val, Multiset.range]

/-- The chunk factor the verifier computes is the Lagrange factor at zeta. -/
theorem chunkFactor_eq (hl : l ≤ qd.log_size) {i : ℕ} (hi : i < 2 ^ l) (ζ : K) :
    chunkFactor G ((List.range (2 ^ l)).map (chunk G hV qd l)) ζ i =
      some ((chunkL hV qd l i).eval ζ) := by
  simp only [chunkFactor, List.length_map, List.length_range, List.getElem?_map,
    List.getElem?_range hi, Option.map_some, Option.bind_eq_bind, Option.bind_some]
  refine (foldlM_mul_some _ _ (fun j => Coset.vanishing_poly_at_point G (chunk G hV qd l j) ζ *
    (Coset.vanishing_poly_at_point G (chunk G hV qd l j) (chunk G hV qd l i).shift)⁻¹)
    (fun acc j hj => ?_) 1).trans ?_
  · obtain ⟨hj, hne⟩ : j < 2 ^ l ∧ j ≠ i := by simpa using hj
    have h0 : Coset.vanishing_poly_at_point G (chunk G hV qd l j) (chunk G hV qd l i).shift ≠ 0 :=
      fun h => hne ((vanishing_chunk_first hV qd l hi hj hl).mp h).symm
    simp [List.getElem?_range hj, Coset.first_point, p3_commit.domain.mirror.inv, h0]
  · rw [one_mul, prod_filter_range_ne, chunkL, eval_prod]
    refine congrArg some (prod_congr rfl fun j _ => ?_)
    rw [eval_mul, eval_C, eval_chunkZ, mul_comm]

/-- The transcribed recombination returns sum_i L_i(zeta) v_i, when chunk i rebuilds to v_i. -/
theorem recompose_eq {D : ℕ} {F : Type} [Field F] [Algebra F K] (B : Module.Basis (Fin D) F K)
    (hl : l ≤ qd.log_size) (chunks : List (List K)) (hlen : chunks.length = 2 ^ l) (v : ℕ → K)
    (hv : ∀ i (hi : i < 2 ^ l), from_ext_basis_coefficients B (chunks[i]'(hlen ▸ hi)) = some (v i))
    (ζ : K) :
    recompose_quotient_from_chunks G B ((List.range (2 ^ l)).map (chunk G hV qd l)) chunks ζ =
      some (∑ i ∈ range (2 ^ l), (chunkL hV qd l i).eval ζ * v i) := by
  have hz : (List.range ((List.range (2 ^ l)).map (chunk G hV qd l)).length).mapM
      (chunkFactor G ((List.range (2 ^ l)).map (chunk G hV qd l)) ζ) =
      some ((List.range (2 ^ l)).map fun i => (chunkL hV qd l i).eval ζ) := by
    rw [List.length_map, List.length_range]
    exact Plonky3Lean.Proofs.UniStark.mapM_some_of _ _ _ fun i hi =>
      chunkFactor_eq hV qd l hl (List.mem_range.mp hi) ζ
  rw [recompose_quotient_from_chunks, hz]
  simp only [Option.bind_eq_bind, Option.bind_some]
  rw [hlen,
    foldlM_add_some _ _ (fun i => (chunkL hV qd l i).eval ζ * v i), zero_add, sum_map_range]
  intro acc i hi
  have hi := List.mem_range.mp hi
  simp [hlen, hi, hv i hi]

/-- With the chunk interpolants of a quotient below N, the verifier recovers the quotient at zeta. -/
theorem recompose_quotient {D : ℕ} {F : Type} [Field F] [Algebra F K] (B : Module.Basis (Fin D) F K)
    (hN : GenNested G) (hl : l ≤ qd.log_size) (Q : K[X]) (hQ : Q.degree < (2 ^ qd.log_size : ℕ))
    (chunks : List (List K)) (hlen : chunks.length = 2 ^ l)
    (hv : ∀ i (hi : i < 2 ^ l), from_ext_basis_coefficients B (chunks[i]'(hlen ▸ hi)) =
      some ((chunkInterp hV qd l Q i).eval ζ)) :
    recompose_quotient_from_chunks G B ((List.range (2 ^ l)).map (chunk G hV qd l)) chunks ζ =
      some (Q.eval ζ) := by
  rw [recompose_eq hV qd l B hl chunks hlen _ hv, recombine hV qd l hN hl Q hQ]

end Plonky3Lean.Proofs.UniStark
