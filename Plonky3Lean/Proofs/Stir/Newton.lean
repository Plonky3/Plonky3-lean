module

public import Plonky3Lean.Proofs.Stir.NewtonAlgebra
public import Plonky3Lean.Proofs.Stir.Interp
public import Plonky3Lean.Proofs.Stir.Lists

@[expose] public section

/-!
# interpolate_poly

The table of divided differences, then the Newton expansion into coefficients, then trailing zeros removed.
-/

namespace Plonky3Lean.Proofs.Stir

open Polynomial Finset p3_stir.mirror p3_stir.utils.mirror Plonky3Lean.Spec.Stir

set_option linter.unusedSectionVars false

variable {K : Type _} [Field K] [DecidableEq K]

/-- Updating every slot i < t once, ascending, from its own value. -/
theorem foldl_set_self (f : ℕ → K → K) :
    ∀ (t : ℕ) (cs : List K), t ≤ cs.length → ∀ j,
      ((List.range t).foldl (fun cs i => cs.set i (f i (cs.getD i 0))) cs).getD j 0 =
        if j < t then f j (cs.getD j 0) else cs.getD j 0 := by
  intro t
  induction t with
  | zero => intro cs _ j; simp
  | succ t ih =>
    intro cs hcs j
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, getD_set_eq,
      length_foldl_set]
    simp only [ih cs (by omega)]
    split_ifs <;> first | omega | (casesm* _ ∧ _; subst_vars; rfl) | rfl

/-- The basis update: new[i + 1] += b[i] and new[i] -= b[i] pk, ascending, from zeros. -/
theorem newBasis_getD (b : List K) (pk : K) (j : ℕ) :
    ((List.range b.length).foldl (fun nb i =>
        let nb := nb.set (i + 1) (nb.getD (i + 1) 0 + b.getD i 0)
        nb.set i (nb.getD i 0 - b.getD i 0 * pk)) (List.replicate (b.length + 1) 0)).getD j 0 =
      (if 1 ≤ j ∧ j ≤ b.length then b.getD (j - 1) 0 else 0) - b.getD j 0 * pk := by
  set step := fun (nb : List K) (i : ℕ) =>
    let nb := nb.set (i + 1) (nb.getD (i + 1) 0 + b.getD i 0)
    nb.set i (nb.getD i 0 - b.getD i 0 * pk)
  have hstep : ∀ nb i, (step nb i).length = nb.length := fun nb i => by simp [step]
  have hstepget : ∀ nb i j, i + 1 < nb.length → (step nb i).getD j 0 =
      if j = i then nb.getD i 0 - b.getD i 0 * pk
      else if j = i + 1 then nb.getD (i + 1) 0 + b.getD i 0 else nb.getD j 0 := by
    intro nb i j hi
    simp only [step, getD_set_eq, List.length_set]
    split_ifs <;> first | omega | (casesm* _ ∧ _; subst_vars; rfl) | rfl
  have hlen : ∀ t, ((List.range t).foldl step (List.replicate (b.length + 1) 0)).length = b.length + 1 := by
    intro t; induction t with
    | zero => simp
    | succ t ih => rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, hstep, ih]
  have h : ∀ t ≤ b.length, ∀ j, ((List.range t).foldl step (List.replicate (b.length + 1) 0)).getD j 0 =
      (if 1 ≤ j ∧ j ≤ t then b.getD (j - 1) 0 else 0) - (if j < t then b.getD j 0 * pk else 0) := by
    intro t
    induction t with
    | zero =>
      intro _ j
      simp only [List.range_zero, List.foldl_nil, Nat.not_lt_zero, ↓reduceIte, sub_zero]
      rw [show (List.replicate (b.length + 1) (0 : K)).getD j 0 = 0 by
        simp [List.getD_eq_getElem?_getD, List.getElem?_replicate]; split_ifs <;> rfl]
      split_ifs <;> first | omega | rfl
    | succ t ih =>
      intro ht j
      have ih' := ih (by omega)
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
        hstepget _ _ _ (by rw [hlen]; omega)]
      simp only [ih']
      split_ifs <;> first | omega | (subst_vars; ring1) | (subst_vars; simp)
  rw [h b.length le_rfl j]
  congr 1
  split_ifs with h2
  · rfl
  · rw [getD_of_le _ _ (by omega), zero_mul]

theorem length_flatMap_range {α : Type _} (g : ℕ → List α) (m : ℕ) :
    ((List.range m).flatMap g).length = ∑ j ∈ range m, (g j).length := by
  induction m with
  | zero => simp
  | succ m ih => rw [List.range_succ, List.flatMap_append, List.length_append, ih, sum_range_succ]; simp

/-- Block m of a concatenation of blocks, read back by dropping the earlier ones. -/
theorem flatMap_range_slice {α : Type _} (g : ℕ → List α) {m M : ℕ} (hm : m < M) :
    (((List.range M).flatMap g).drop (∑ j ∈ range m, (g j).length)).take (g m).length = g m := by
  obtain ⟨d, rfl⟩ : ∃ d, M = m + 1 + d := ⟨M - (m + 1), by omega⟩
  rw [List.range_add, List.range_succ, List.flatMap_append, List.flatMap_append,
    List.flatMap_singleton, List.append_assoc, List.drop_append_of_le_length (by
      rw [length_flatMap_range]), ← length_flatMap_range, List.drop_length, List.nil_append,
    List.take_append_of_le_length le_rfl, List.take_length]

/-- The basis step multiplies by X - pk. -/
theorem coeffPoly_newBasis (b : List K) (pk : K) :
    coeffPoly ((List.range b.length).foldl (fun nb i =>
        let nb := nb.set (i + 1) (nb.getD (i + 1) 0 + b.getD i 0)
        nb.set i (nb.getD i 0 - b.getD i 0 * pk)) (List.replicate (b.length + 1) 0)) =
      (X - C pk) * coeffPoly b := by
  refine Polynomial.ext fun j => ?_
  rw [coeff_coeffPoly, newBasis_getD, sub_mul, coeff_sub, coeff_C_mul, coeff_coeffPoly]
  rcases j with _ | j
  · simp [mul_comm]
  · rw [coeff_X_mul, coeff_coeffPoly]
    simp only [Nat.add_sub_cancel]
    split_ifs with h
    · ring
    · rw [getD_of_le b (i := j) 0 (by omega), getD_of_le b (i := j + 1) 0 (by omega)]; ring

theorem length_newBasis (b : List K) (pk : K) :
    ((List.range b.length).foldl (fun nb i =>
        let nb := nb.set (i + 1) (nb.getD (i + 1) 0 + b.getD i 0)
        nb.set i (nb.getD i 0 - b.getD i 0 * pk)) (List.replicate (b.length + 1) 0)).length =
      b.length + 1 := by
  suffices ∀ t, ((List.range t).foldl (fun nb i =>
        let nb := nb.set (i + 1) (nb.getD (i + 1) 0 + b.getD i 0)
        nb.set i (nb.getD i 0 - b.getD i 0 * pk)) (List.replicate (b.length + 1) 0)).length =
      b.length + 1 from this _
  intro t; induction t with
  | zero => simp
  | succ t ih => rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]; simpa using ih

/-- Removing trailing zeros keeps the polynomial. -/
theorem coeffPoly_stripZeros (l : List K) :
    coeffPoly (interpolate_poly.stripZeros l) = coeffPoly l := by
  unfold interpolate_poly.stripZeros
  suffices ∀ (t : ℕ) (cs : List K), coeffPoly ((List.range t).foldl (fun cs _ =>
      if cs.getLast? = some 0 ∧ cs.length > 1 then cs.dropLast else cs) cs) = coeffPoly cs from this _ _
  intro t
  induction t with
  | zero => intro cs; rfl
  | succ t ih =>
    intro cs
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    split_ifs with h
    · rw [← ih cs]
      obtain ⟨hl, -⟩ := h
      rw [List.getLast?_eq_some_iff] at hl
      obtain ⟨ys, hys⟩ := hl
      rw [hys, List.dropLast_concat, coeffPoly_append]
      simp [coeffPoly_cons]
    · exact ih cs

theorem divDiff_self (v r : ℕ → K) (i : ℕ) : divDiff v r i i = r i := by
  simp [divDiff, interpAB]

/-- One stage of the table: entries k, ..., n - 1 move from f[v_(i-k+1)..v_i] to f[v_(i-k)..v_i], k = m + 1. -/
theorem dd_stage {n : ℕ} (v r : ℕ → K) (hv : Set.InjOn v (range n : Set ℕ)) (dinv : List K)
    (hdinv : dinv = (List.range (n - 1)).flatMap fun k' =>
      (List.range (n - (k' + 1))).map fun i' => (v (i' + (k' + 1)) - v (i' + (k' + 1) - (k' + 1)))⁻¹)
    {m : ℕ} (hm : m + 1 ≤ n - 1) (dd : List K) (off : ℕ) (hlen : dd.length = n)
    (hoff : off = ∑ j ∈ range m, (n - (j + 1)))
    (hdd : ∀ i < n, dd.getD i 0 = divDiff v r (i - min i m) i) :
    let dd' := (List.range (n - (m + 1))).reverse.foldl (fun dd i' => let i := i' + (m + 1);
      dd.set i ((dd.getD i 0 - dd.getD (i - 1) 0) * ((dinv.drop off).take (n - (m + 1))).getD (i - (m + 1)) 0)) dd
    dd'.length = n ∧ ∀ i < n, dd'.getD i 0 = divDiff v r (i - min i (m + 1)) i := by
  set inverses := (dinv.drop off).take (n - (m + 1))
  have hinv : inverses = (List.range (n - (m + 1))).map fun i' =>
      (v (i' + (m + 1)) - v (i' + (m + 1) - (m + 1)))⁻¹ := by
    have := flatMap_range_slice (fun k' => (List.range (n - (k' + 1))).map fun i' =>
      (v (i' + (k' + 1)) - v (i' + (k' + 1) - (k' + 1)))⁻¹) (m := m) (M := n - 1) (by omega)
    simp only [List.length_map, List.length_range] at this
    simp only [inverses, hdinv, hoff]; exact this
  have key := foldl_desc_set (fun i a b => (b - a) * inverses.getD (i - (m + 1)) 0) (0 : K) (m + 1)
    (by omega) (n - (m + 1)) dd (by omega)
  refine ⟨by erw [length_foldl_set]; exact hlen, fun i hi => ?_⟩
  rw [key i]
  split_ifs with h
  · have hinvi : inverses.getD (i - (m + 1)) 0 = (v i - v (i - (m + 1)))⁻¹ := by
      rw [hinv, getD_map_range _ _ (by omega)]
      congr 2 <;> congr 1 <;> omega
    rw [hinvi, hdd i hi, hdd (i - 1) (by omega), min_eq_right (by omega), min_eq_right (by omega),
      min_eq_right (by omega)]
    have hab : i - (m + 1) < i := by omega
    rw [divDiff_succ r (hv.mono (by intro x hx; simp at hx ⊢; omega)) hab,
      show i - (m + 1) + 1 = i - m by omega, show i - 1 - m = i - (m + 1) by omega]
  · rw [hdd i hi]
    congr 2
    omega

/-- The table of divided differences: after m stages, entry i holds f[v_(i - min(i, m)), ..., v_i]. -/
theorem dd_table {n : ℕ} (v r : ℕ → K) (hv : Set.InjOn v (range n : Set ℕ)) (vals : List K)
    (hvals : vals.length = n) (hr : ∀ i < n, vals.getD i 0 = r i) (dinv : List K)
    (hdinv : dinv = (List.range (n - 1)).flatMap fun k' =>
      (List.range (n - (k' + 1))).map fun i' => (v (i' + (k' + 1)) - v (i' + (k' + 1) - (k' + 1)))⁻¹) :
    ∀ m ≤ n - 1,
      let st := (List.range m).foldl (fun (st : List K × ℕ) k' =>
        let k := k' + 1
        let width := n - k
        let inverses := (dinv.drop st.2).take width
        let dd := (List.range (n - k)).reverse.foldl (fun dd i' => let i := i' + k;
          dd.set i ((dd.getD i 0 - dd.getD (i - 1) 0) * inverses.getD (i - k) 0)) st.1
        (dd, st.2 + width)) (vals, 0)
      st.1.length = n ∧ st.2 = ∑ j ∈ range m, (n - (j + 1)) ∧
        ∀ i < n, st.1.getD i 0 = divDiff v r (i - min i m) i := by
  intro m
  induction m with
  | zero =>
    intro _
    simp only [List.range_zero, List.foldl_nil, hvals, sum_range_zero, true_and]
    intro i hi; rw [hr i hi, Nat.min_zero, Nat.sub_zero, divDiff_self]
  | succ m ih =>
    intro hm
    obtain ⟨h1, h2, h3⟩ := ih (by omega)
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    obtain ⟨h4, h5⟩ := dd_stage v r hv dinv hdinv hm _ _ h1 h2 h3
    exact ⟨h4, by rw [h2, sum_range_succ], h5⟩

theorem coeffPoly_add_scaled (cs nb : List K) (d : K) (h : nb.length ≤ cs.length) :
    coeffPoly ((List.range nb.length).foldl (fun cs i => cs.set i (cs.getD i 0 + d * nb.getD i 0)) cs) =
      coeffPoly cs + C d * coeffPoly nb ∧
    ((List.range nb.length).foldl (fun cs i => cs.set i (cs.getD i 0 + d * nb.getD i 0)) cs).length =
      cs.length := by
  refine ⟨Polynomial.ext fun j => ?_, by erw [length_foldl_set]⟩
  rw [coeff_coeffPoly, foldl_set_self (fun i c => c + d * nb.getD i 0) _ cs h, coeff_add, coeff_C_mul,
    coeff_coeffPoly, coeff_coeffPoly]
  split_ifs with hj
  · rfl
  · rw [getD_of_le nb (i := j) 0 (by omega), mul_zero, add_zero]

/-- One step of interpolate_poly's Newton expansion, as the transcription writes it. -/
def newtonStep (points dd : List K) : List K × List K → ℕ → List K × List K := fun st k' =>
  let k := k' + 1
  let pk := points.getD (k - 1) 0
  let basis := st.2
  let new_basis := (List.range basis.length).foldl (fun nb i =>
    let b := basis.getD i 0
    let nb := nb.set (i + 1) (nb.getD (i + 1) 0 + b)
    nb.set i (nb.getD i 0 - b * pk)) (List.replicate (basis.length + 1) 0)
  let coeffs := (List.range new_basis.length).foldl (fun cs i =>
    cs.set i (cs.getD i 0 + dd.getD k 0 * new_basis.getD i 0)) st.1
  (coeffs, new_basis)

/-- The Newton expansion: after m steps the basis is prod_{j < m} (X - v_j) and the coefficients sum the first m + 1 terms. -/
theorem newton_expansion (points dd : List K) {n : ℕ} (hn : 0 < n) :
    ∀ m ≤ n - 1,
      let st := (List.range m).foldl (newtonStep points dd)
        ((List.replicate n (0 : K)).set 0 (dd.getD 0 0), [1])
      st.2.length = m + 1 ∧ coeffPoly st.2 = newtonBasis (fun j => points.getD j 0) m ∧
        st.1.length = n ∧
        coeffPoly st.1 = ∑ j ∈ range (m + 1), C (dd.getD j 0) * newtonBasis (fun j => points.getD j 0) j := by
  intro m
  induction m with
  | zero =>
    intro _
    simp only [List.range_zero, List.foldl_nil, zero_add, sum_range_one]
    refine ⟨rfl, by simp [newtonBasis, coeffPoly], by simp, ?_⟩
    simp only [newtonBasis, range_zero, prod_empty, mul_one]
    refine Polynomial.ext fun j => ?_
    rw [coeff_coeffPoly, coeff_C, getD_set_eq]
    rcases j with _ | j
    · simp [hn]
    · simp [List.getD_eq_getElem?_getD, List.getElem?_replicate]
      split_ifs <;> rfl
  | succ m ih =>
    intro hm
    obtain ⟨h1, h2, h3, h4⟩ := ih (by omega)
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    generalize (List.range m).foldl (newtonStep points dd)
      ((List.replicate n (0 : K)).set 0 (dd.getD 0 0), [1]) = S at h1 h2 h3 h4 ⊢
    obtain ⟨cs, b⟩ := S
    simp only at h1 h2 h3 h4
    have hB : newtonBasis (fun j => points.getD j 0) (m + 1) =
        (X - C (points.getD m 0)) * newtonBasis (fun j => points.getD j 0) m := by
      rw [newtonBasis, newtonBasis, prod_range_succ, mul_comm]
    have hnb := coeffPoly_newBasis b (points.getD m 0)
    have hnl := length_newBasis b (points.getD m 0)
    have hadd := coeffPoly_add_scaled cs _ (dd.getD (m + 1) 0) (by rw [hnl, h1, h3]; omega)
    simp only [newtonStep, Nat.add_sub_cancel]
    refine ⟨by rw [hnl, h1], by rw [hnb, h2, hB], by rw [hadd.2, h3], ?_⟩
    rw [hadd.1, h4, hnb, h2, ← hB, sum_range_succ _ (m + 1)]

theorem allDistinct_iff (points : List K) : allDistinct points = true ↔ points.Nodup := by
  rw [List.nodup_iff_getElem?_ne_getElem?]
  simp only [allDistinct, List.all_eq_true, List.mem_range, bne_iff_ne, ne_eq]
  constructor
  · intro h i j hij hj
    have := h j hj i hij
    simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj,
      List.getElem?_eq_getElem (hij.trans hj), Option.getD_some] at this
    simp [List.getElem?_eq_getElem hj, List.getElem?_eq_getElem (hij.trans hj)]
    exact fun h' => this h'.symm
  · intro h i hi j hji
    have := h j i hji hi
    simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi,
      List.getElem?_eq_getElem (hji.trans hi), Option.getD_some]
    simp [List.getElem?_eq_getElem hi, List.getElem?_eq_getElem (hji.trans hi)] at this
    exact fun h' => this h'.symm

/-- One stage of interpolate_poly's table, as the transcription writes it. -/
def ddStep (n : ℕ) (dinv : List K) : List K × ℕ → ℕ → List K × ℕ := fun st k' =>
  let k := k' + 1
  let width := n - k
  let inverses := (dinv.drop st.2).take width
  let dd := (List.range (n - k)).reverse.foldl (fun dd i' => let i := i' + k;
    dd.set i ((dd.getD i 0 - dd.getD (i - 1) 0) * inverses.getD (i - k) 0)) st.1
  (dd, st.2 + width)

/-- interpolate_poly with its loops named. -/
theorem interpolate_poly_unfold (points values : List K) :
    interpolate_poly points values =
      if points.length ≠ values.length then none
      else if !allDistinct points then none
      else if points.length = 0 then some []
      else (batchInv ((List.range (points.length - 1)).flatMap fun k' => let k := k' + 1;
          (List.range (points.length - k)).map fun i' => let i := i' + k;
            points.getD i 0 - points.getD (i - k) 0)).bind fun dinv =>
        let dd := ((List.range (points.length - 1)).foldl (ddStep points.length dinv) (values, 0)).1
        some (interpolate_poly.stripZeros ((List.range (points.length - 1)).foldl (newtonStep points dd)
          ((List.replicate points.length (0 : K)).set 0 (dd.getD 0 0), [1])).1) := by
  rfl

/-- interpolate_poly on distinct points: coefficients of the interpolant of degree below n. -/
theorem interpolate_poly_eq (points values : List K) (hlen : points.length = values.length)
    (hnd : points.Nodup) (hne : points ≠ []) :
    ∃ cs, interpolate_poly points values = some cs ∧
      coeffPoly cs = Lagrange.interpolate (range points.length) (fun i => points.getD i 0)
        (fun i => values.getD i 0) := by
  have hn : 0 < points.length := List.length_pos_of_ne_nil hne
  have hv : Set.InjOn (fun i => points.getD i 0) (range points.length : Set ℕ) :=
    injOn_getD_of_nodup hnd
  rw [interpolate_poly_unfold]
  simp only [← hlen, ne_eq, not_true_eq_false, ↓reduceIte, (allDistinct_iff points).2 hnd,
    Bool.not_true, Bool.false_eq_true, hn.ne']
  set n := points.length with hn_def
  set v : ℕ → K := fun i => points.getD i 0
  set D := (List.range (n - 1)).flatMap fun k' =>
    (List.range (n - (k' + 1))).map fun i' => v (i' + (k' + 1)) - v (i' + (k' + 1) - (k' + 1))
  have hD : (0 : K) ∉ D := by
    simp only [D, List.mem_flatMap, List.mem_map, List.mem_range, not_exists, not_and]
    intro k' hk' i' hi' h
    have := hv (show i' + (k' + 1) ∈ (range n : Set ℕ) by simp; omega)
      (show i' + (k' + 1) - (k' + 1) ∈ (range n : Set ℕ) by simp; omega) (sub_eq_zero.1 h)
    omega
  set dinv := (List.range (n - 1)).flatMap fun k' =>
    (List.range (n - (k' + 1))).map fun i' => (v (i' + (k' + 1)) - v (i' + (k' + 1) - (k' + 1)))⁻¹
  have hdinv : D.map (·⁻¹) = dinv := by simp [D, dinv, List.map_flatMap, Function.comp_def]
  change ∃ cs, ((batchInv D).bind fun a => _) = some cs ∧ _
  rw [show batchInv D = some dinv by simp [batchInv, hD, hdinv], Option.bind_some]
  refine ⟨_, rfl, ?_⟩
  rw [coeffPoly_stripZeros]
  obtain ⟨-, -, hdd⟩ := dd_table v (fun i => values.getD i 0) hv values hlen.symm (fun _ _ => rfl)
    dinv rfl (n - 1) le_rfl
  obtain ⟨-, -, -, hexp⟩ := newton_expansion points
    (List.foldl (ddStep n dinv) (values, 0) (List.range (n - 1))).1 hn (n - 1) le_rfl
  change ∀ i < n, (List.foldl (ddStep n dinv) (values, 0) (List.range (n - 1))).1.getD i 0 = _ at hdd
  have hIcc : Icc 0 (n - 1) = range n := by ext i; simp; omega
  rw [hexp, Nat.sub_add_cancel hn]
  rw [sum_congr rfl fun j hj => by
    rw [hdd j (mem_range.1 hj), min_eq_left (by have := mem_range.1 hj; omega), Nat.sub_self]]
  have := interpAB_newton (fun i => values.getD i 0) (n - 1) (by rw [hIcc]; exact hv)
  rw [Nat.sub_add_cancel hn] at this
  rw [← this, interpAB, hIcc]

/-- interpolate_poly panics on lengths that differ and on repeated points. -/
theorem interpolate_poly_panics (points values : List K)
    (h : points.length ≠ values.length ∨ ¬ points.Nodup) : interpolate_poly points values = none := by
  rw [interpolate_poly_unfold]
  rcases h with h | h
  · simp [h]
  · have : allDistinct points = false := by
      rw [← Bool.not_eq_true, allDistinct_iff]; exact h
    simp [this]

end Plonky3Lean.Proofs.Stir
