module

public import Plonky3Lean.Proofs.Stir.Horner
public import Plonky3Lean.Proofs.Dft.Glue
public import Mathlib.FieldTheory.KummerExtension

@[expose] public section

/-!
# Barycentric evaluation on a coset of roots of unity

On the nodes x_l = x_0 zeta^l, l < n, zeta a primitive n-th root, the nodal polynomial is X^n - x_0^n.

So the barycentric weight of x_i is 1 / (n x_i^(n-1)) = x_i / (n x_0^n), and the interpolant at a point p off the nodes is

```text
    prod_l (p - x_l)  *  sum_i y_i (x_i / (n x_0^n)) / (p - x_i)
```
-/

namespace Plonky3Lean.Proofs.Stir

open Polynomial Finset p3_stir.mirror p3_stir.utils.mirror p3_dft.mirror Plonky3Lean.Proofs.Dft

set_option linter.unusedSectionVars false

section OneField

variable {K : Type _} [Field K] [DecidableEq K]

theorem foldl_add_range (f : ℕ → K) (a : K) (n : ℕ) :
    (List.range n).foldl (fun acc i => acc + f i) a = a + ∑ i ∈ range n, f i := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.range_succ, List.foldl_append, ih, sum_range_succ]; simp [add_assoc]

theorem prod_map_range (f : ℕ → K) (n : ℕ) : ((List.range n).map f).prod = ∏ i ∈ range n, f i := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.range_succ, List.map_append, List.prod_append, ih, prod_range_succ]; simp

theorem cosetNodes_injOn {ζ x0 : K} {n : ℕ} (hζ : IsPrimitiveRoot ζ n) (hx0 : x0 ≠ 0) :
    Set.InjOn (fun l => x0 * ζ ^ l) (range n : Set ℕ) := fun _ ha _ hb h =>
  hζ.pow_inj (mem_range.1 ha) (mem_range.1 hb) (mul_left_cancel₀ hx0 h)

/-- The barycentric weight of a node of a coset of the n-th roots of unity. -/
theorem nodalWeight_coset {ζ x0 : K} {n : ℕ} (hζ : IsPrimitiveRoot ζ n) (hn : (n : K) ≠ 0)
    (hx0 : x0 ≠ 0) {i : ℕ} (hi : i < n) :
    Lagrange.nodalWeight (range n) (fun l => x0 * ζ ^ l) i = x0 * ζ ^ i / (n * x0 ^ n) := by
  have hn0 : 0 < n := Nat.pos_of_ne_zero fun h => hn (by simp [h])
  have hnodal : Lagrange.nodal (range n) (fun l => x0 * ζ ^ l) = X ^ n - C (x0 ^ n) := by
    rw [X_pow_sub_C_eq_prod hζ hn0 rfl, Lagrange.nodal]
    exact prod_congr rfl fun l _ => by rw [mul_comm]
  have hxi : (x0 * ζ ^ i) ^ n = x0 ^ n := by
    rw [mul_pow, ← pow_mul, mul_comm i, pow_mul, hζ.pow_eq_one, one_pow, mul_one]
  have hxi0 : x0 * ζ ^ i ≠ 0 := mul_ne_zero hx0 (pow_ne_zero _ (hζ.ne_zero hn0.ne'))
  rw [Lagrange.nodalWeight_eq_eval_derivative_nodal (mem_range.2 hi), hnodal]
  simp only [derivative_sub, derivative_X_pow, derivative_C, sub_zero, eval_mul, eval_C, eval_pow,
    eval_X]
  rw [← hxi]
  have : (x0 * ζ ^ i) ^ n = (x0 * ζ ^ i) ^ (n - 1) * (x0 * ζ ^ i) := by
    rw [← pow_succ]; congr 1; omega
  have hζ0 : ζ ≠ 0 := hζ.ne_zero hn0.ne'
  rw [this]
  field_simp

/-- The interpolant on a coset of the n-th roots of unity, at a point off the nodes, in barycentric form. -/
theorem eval_interpolate_coset {ζ x0 : K} {n : ℕ} (hζ : IsPrimitiveRoot ζ n) (hn : (n : K) ≠ 0)
    (hx0 : x0 ≠ 0) (r : ℕ → K) {p : K} (hp : ∀ i < n, p ≠ x0 * ζ ^ i) :
    (Lagrange.interpolate (range n) (fun l => x0 * ζ ^ l) r).eval p =
      (∏ l ∈ range n, (p - x0 * ζ ^ l)) *
        ∑ i ∈ range n, r i * (x0 * ζ ^ i / (n * x0 ^ n)) * (p - x0 * ζ ^ i)⁻¹ := by
  rw [Lagrange.eval_interpolate_not_at_node r fun i hi => hp i (mem_range.1 hi)]
  simp only [Lagrange.nodal, eval_prod, eval_sub, eval_X, eval_C]
  congr 1
  refine sum_congr rfl fun i hi => ?_
  rw [nodalWeight_coset hζ hn hx0 (mem_range.1 hi)]; ring

end OneField

section TwoFields

variable {F EF : Type _} [Field F] [Field EF] [Algebra F EF] [DecidableEq F] [DecidableEq EF]

/-- The barycentric formula on the coset x_0 <zeta> of the 2^k-th roots of unity: the interpolant at the point. -/
theorem lagrange_interpolate_at_eq {ζ x0 : F} {k : ℕ} (hζ : IsPrimitiveRoot ζ (2 ^ k))
    (hn : ((2 ^ k : ℕ) : F) ≠ 0) (hx0 : x0 ≠ 0) (ys : List EF) (hys : ys.length = 2 ^ k)
    (point : EF) :
    lagrange_interpolate_at (shiftedPowersList ζ x0 (2 ^ k)) ys point =
      some ((Lagrange.interpolate (range (2 ^ k)) (fun l => algebraMap F EF (x0 * ζ ^ l))
        (fun l => ys.getD l 0)).eval point) := by
  set n := 2 ^ k with hn_def
  have hn0 : 0 < n := by positivity
  have hζ' : IsPrimitiveRoot (algebraMap F EF ζ) n := hζ.map_of_injective (algebraMap F EF).injective
  have hx0' : algebraMap F EF x0 ≠ 0 := by simpa using hx0
  have hnE : (n : EF) ≠ 0 := by simpa using (map_ne_zero (algebraMap F EF)).2 hn
  have hinj : Set.InjOn (fun l => algebraMap F EF (x0 * ζ ^ l)) (range n : Set ℕ) := by
    simpa [map_mul, map_pow] using cosetNodes_injOn hζ' hx0'
  have hlen : (shiftedPowersList ζ x0 n).length = n := by simp [shiftedPowersList]
  have hget : ∀ i < n, (shiftedPowersList ζ x0 n).getD i 0 = x0 * ζ ^ i := fun i hi =>
    getD_shiftedPowersList _ _ hi
  unfold lagrange_interpolate_at
  simp only [hlen, hys, ne_eq, not_true_eq_false, ite_false, hn0.ne', ite_false]
  split
  · -- The point is a node.
    rename_i i hfind
    have hpt := List.find?_some hfind
    have hi : i < n := List.mem_range.1 (List.mem_of_find?_eq_some hfind)
    simp only [decide_eq_true_eq, hget i hi] at hpt
    rw [hpt, Option.some.injEq]
    exact (Lagrange.eval_interpolate_at_node (fun l => ys.getD l 0) hinj (mem_range.2 hi)).symm
  · -- The point is off the nodes.
    rename_i hfind
    have hp : ∀ i < n, point ≠ algebraMap F EF x0 * algebraMap F EF ζ ^ i := fun i hi h => by
      have := List.find?_eq_none.1 hfind i (List.mem_range.2 hi)
      simp only [decide_eq_true_eq, hget i hi, map_mul, map_pow] at this
      exact this h
    have hlog : log2Strict n = some k := by
      simp [log2Strict, hn_def, Nat.log_pow (by norm_num : 1 < 2)]
    have hcp : (shiftedPowersList ζ x0 n).getD 0 0 = x0 := by simpa using hget 0 hn0
    have hw : (n : F) * x0 ^ 2 ^ k ≠ 0 := mul_ne_zero hn (pow_ne_zero _ hx0)
    have hdiffs : (0 : EF) ∉ (shiftedPowersList ζ x0 n).map fun x => point - algebraMap F EF x := by
      simp only [List.mem_map, not_exists, not_and, shiftedPowersList, List.mem_range]
      rintro _ ⟨i, hi, rfl⟩ h
      exact hp i hi (by rw [← sub_eq_zero, ← h]; simp [map_mul, map_pow])
    simp only [hlog, hcp, p3_stir.mirror.inverse, hw, ite_false, batchInv, hdiffs,
      Option.bind_eq_bind, Option.bind_some, Option.some.injEq]
    rw [foldl_add_range, zero_add, mul_comm]
    simp only [map_mul, map_pow]
    rw [eval_interpolate_coset hζ' hnE hx0' (fun l => ys.getD l 0) hp]
    congr 1
    · simp only [shiftedPowersList, List.map_map, Function.comp_def, prod_map_range, map_mul,
        map_pow]
    · refine sum_congr rfl fun i hi => ?_
      have hi' := mem_range.1 hi
      have hd : (((shiftedPowersList ζ x0 n).map fun x => point - algebraMap F EF x).map
          fun x => x⁻¹).getD i 0 = (point - algebraMap F EF x0 * algebraMap F EF ζ ^ i)⁻¹ := by
        simp [List.getD_eq_getElem?_getD, shiftedPowersList, hi']
      rw [hd, hget i hi']
      simp only [map_mul, map_inv₀, map_pow, map_natCast, hn_def]
      field_simp

end TwoFields

end Plonky3Lean.Proofs.Stir
