module

public import Plonky3Lean.Proofs.Stir.Lagrange

@[expose] public section

/-!
# The answer polynomial check

The check compares ans(rho) with the interpolant I through the n pairs (y_i, v_i).

I has degree below n, and the check evaluates it in barycentric form:

```text
    I(rho) = (sum_i w_i v_i / (rho - y_i)) / (sum_i w_i / (rho - y_i))

    w_i = 1 / prod_{j != i} (y_i - y_j)
```

It accepts exactly when ans(rho) = I(rho), for distinct nodes and rho off them.
-/

namespace Plonky3Lean.Proofs.Stir

open Polynomial Finset p3_stir.mirror p3_stir.utils.mirror Plonky3Lean.Spec.Stir

set_option linter.unusedSectionVars false

variable {K : Type _} [Field K] [DecidableEq K]

theorem foldl_mul_eq (f : ℕ → K) : ∀ (l : List ℕ) (a : K),
    l.foldl (fun p j => p * f j) a = a * (l.map f).prod := by
  intro l; induction l with
  | nil => simp
  | cons x l ih => intro a; simp [ih, mul_assoc]

/-- The product over j != i that the code accumulates. -/
theorem foldl_filter_ne (f : ℕ → K) (n i : ℕ) :
    ((List.range n).filter (· ≠ i)).foldl (fun p j => p * f j) 1 = ∏ j ∈ (range n).erase i, f j := by
  rw [foldl_mul_eq, one_mul, ← List.prod_toFinset _ ((List.nodup_range).filter _)]
  congr 1; ext j; simp [and_comm]

theorem foldl_pair_add (f g : ℕ → K) (n : ℕ) :
    (List.range n).foldl (fun (st : K × K) i => (st.1 + f i, st.2 + g i)) (0, 0) =
      (∑ i ∈ range n, f i, ∑ i ∈ range n, g i) := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.range_succ, List.foldl_append, ih]; simp [sum_range_succ]

theorem injOn_getD_of_nodup {l : List K} (hl : l.Nodup) :
    Set.InjOn (fun i => l.getD i 0) (range l.length : Set ℕ) := by
  intro a ha b hb h
  simp only [coe_range, Set.mem_Iio] at ha hb
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ha, List.getElem?_eq_getElem hb,
    Option.getD_some] at h
  exact (hl.getElem_inj_iff).1 h

/-- The answer check on distinct nodes, with rho off them.

It accepts exactly when ans(rho) is the interpolant at rho. -/
theorem check_ans_interpolates_eq (ans pts vals : List K) (ρ : K) (hlen : pts.length = vals.length)
    (hne : pts ≠ []) (hnodup : pts.Nodup) (hρ : ρ ∉ pts) :
    check_ans_interpolates ans pts vals ρ = some (decide ((coeffPoly ans).eval ρ =
      (Lagrange.interpolate (range pts.length) (fun i => pts.getD i 0) (fun i => vals.getD i 0)).eval ρ)) := by
  set v : ℕ → K := fun i => pts.getD i 0
  have hinj := injOn_getD_of_nodup hnodup
  have hn : (range pts.length).Nonempty := nonempty_range_iff.2 (by simpa using hne)
  have hvρ : ∀ i ∈ range pts.length, ρ ≠ v i := fun i hi h => hρ (by
    rw [h]; simp only [v, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (mem_range.1 hi),
      Option.getD_some]; exact List.getElem_mem _)
  set W := (List.range pts.length).map fun i =>
    ((List.range pts.length).filter (· ≠ i)).foldl (fun p j => p * (pts.getD i 0 - pts.getD j 0)) 1
  have hWget : ∀ i < pts.length, W.getD i 0 = (Lagrange.nodalWeight (range pts.length) v i)⁻¹ :=
    fun i hi => by
      rw [getD_map_range _ _ hi, foldl_filter_ne, Lagrange.nodalWeight, prod_inv_distrib, inv_inv]
  have hWlen : W.length = pts.length := by simp [W]
  have hW0 : (0 : K) ∉ W := by
    intro h
    obtain ⟨i, hi, hie⟩ := List.getElem_of_mem h
    have := hWget i (hWlen ▸ hi)
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some, hie] at this
    exact inv_ne_zero (Lagrange.nodalWeight_ne_zero hinj (mem_range.2 (hWlen ▸ hi))) this.symm
  have hD0 : (0 : K) ∉ pts.map fun y => ρ - y := by
    simp only [List.mem_map, not_exists, not_and]
    intro y hy h; exact hρ ((sub_eq_zero.1 h) ▸ hy)
  have htake : (W ++ pts.map fun y => ρ - y).take pts.length = W := by
    rw [List.take_append_of_le_length (by omega), List.take_of_length_le (by omega)]
  unfold check_ans_interpolates
  simp only [← hlen, ne_eq, not_true_eq_false, ↓reduceIte, hne, hρ]
  change (if (0 : K) ∈ (W ++ pts.map fun y => ρ - y).take pts.length then some false else _) = _
  rw [htake]
  simp only [hW0, ↓reduceIte, batchInv, List.mem_append, hD0, Option.bind_eq_bind, List.map_append]
  have hWeq : (List.range pts.length).map (fun i => List.foldl (fun p j => p * (pts.getD i 0 - pts.getD j 0)) 1
      (List.filter (fun x => decide ¬x = i) (List.range pts.length))) = W := rfl
  rw [hWeq]
  simp only [hW0, or_false, ↓reduceIte, Option.bind_some]
  have hlenW : (W.map fun x => x⁻¹).length = pts.length := by simp [hWlen]
  rw [List.take_left' hlenW, List.drop_left' hlenW, foldl_pair_add]
  dsimp only
  have hterm : ∀ i ∈ range pts.length, (W.map fun x => x⁻¹).getD i 0 *
      ((pts.map fun y => ρ - y).map fun x => x⁻¹).getD i 0 =
        Lagrange.nodalWeight (range pts.length) v i * (ρ - v i)⁻¹ := fun i hi => by
    have hi' := mem_range.1 hi
    have h1 : (W.map fun x => x⁻¹).getD i 0 = (W.getD i 0)⁻¹ := by
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (hWlen ▸ hi')]
    have h2 : ((pts.map fun y => ρ - y).map fun x => x⁻¹).getD i 0 = (ρ - v i)⁻¹ := by
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi', v]
    rw [h1, h2, hWget i hi', inv_inv]
  have hnum : ∑ i ∈ range pts.length, (W.map fun x => x⁻¹).getD i 0 *
      ((pts.map fun y => ρ - y).map fun x => x⁻¹).getD i 0 * vals.getD i 0 =
      ∑ i ∈ range pts.length, Lagrange.nodalWeight (range pts.length) v i * (ρ - v i)⁻¹ *
        vals.getD i 0 := sum_congr rfl fun i hi => by rw [hterm i hi]
  rw [sum_congr rfl hterm, hnum, eval_poly_eq,
    Lagrange.eval_interpolate_not_at_node' (fun i => vals.getD i 0) hinj hn hvρ]
  simp only [eq_div_iff (Lagrange.sum_nodalWeight_mul_inv_sub_ne_zero hinj hvρ hn)]
  rfl

end Plonky3Lean.Proofs.Stir
