module

public import Plonky3Lean.Proofs.Whir.Table
public import Plonky3Lean.Proofs.Sumcheck.Prover

@[expose] public section

/-!
# The k sumcheck rounds of one WHIR iteration

WHIR runs k rounds of the quadratic sumcheck on a product P~ w~ of 2^n entries, with k <= n.

The honest messages replay the claim sum_b P[b] w[b] to the same sum over the folded tables:

```text
    sum_{b < 2^n} P[b] w[b]  ->  sum_{c < 2^(n-k)} P'[c] w'[c],    P' = fold(P, r),  w' = fold(w, r)
```
-/

namespace Plonky3Lean.Proofs.Whir

open Finset Plonky3Lean.Spec.MultilinearUtil Plonky3Lean.Spec.Whir Plonky3Lean.Proofs.MultilinearUtil
open p3_sumcheck.mirror p3_multilinear_util.poly.mirror Plonky3Lean.Proofs.Sumcheck

variable {K : Type _} [Field K]

/-- The fold at one challenge: each entry of the lower half moves towards its partner in the upper half. -/
def fixHalf (P : List K) (r : K) (half : ℕ) : List K :=
  List.zipWith (fun a0 a1 => a0 + (a1 - a0) * r) (P.take half) (P.drop half)

theorem getD_fixHalf (P : List K) (r : K) {half i : ℕ} (hP : P.length = 2 * half) (hi : i < half) :
    (fixHalf P r half).getD i 0 = P.getD i 0 + (P.getD (half + i) 0 - P.getD i 0) * r := by
  simp [fixHalf, List.getD_eq_getElem?_getD, List.getElem?_zipWith, hi, show i < P.length by omega,
    show half + i < P.length by omega]

theorem fix_prefix_var_mut_eq (P : List K) (r : K) {n : ℕ} (hP : P.length = 2 ^ (n + 1)) :
    Poly.fix_prefix_var_mut P r = some (fixHalf P r (2 ^ n)) := by
  have h1 : P.length ≠ 1 := by rw [hP, pow_succ]; have := Nat.one_le_two_pow (n := n); omega
  have hh : P.length / 2 = 2 ^ n := by rw [hP, pow_succ]; omega
  simp [Poly.fix_prefix_var_mut, h1, hh, fixHalf]

theorem length_fixHalf (P : List K) (r : K) {n : ℕ} (hP : P.length = 2 ^ (n + 1)) :
    (fixHalf P r (2 ^ n)).length = 2 ^ n := by
  simp [fixHalf, hP, pow_succ]; omega

/-- Folding at r :: rs is folding at r, then at rs. -/
theorem foldTable_cons (P : List K) {n : ℕ} (hP : P.length = 2 ^ (n + 1)) (r : K) (rs : List K)
    (hk : rs.length ≤ n) : foldTable P (n + 1) (r :: rs) = foldTable (fixHalf P r (2 ^ n)) n rs := by
  have hm : n + 1 - (rs.length + 1) = n - rs.length := by omega
  simp only [foldTable, List.length_cons, hm]
  refine List.map_congr_left fun c hc => ?_
  have hc := List.mem_range.mp hc
  rw [pow_succ, mul_two, sum_range_add]
  have h2 : 2 ^ rs.length * 2 ^ (n - rs.length) = 2 ^ n := by rw [← pow_add]; congr 1; omega
  rw [← sum_add_distrib]
  refine sum_congr rfl fun j hj => ?_
  have hj := mem_range.mp hj
  have hi : j * 2 ^ (n - rs.length) + c < 2 ^ n := by
    rw [← h2]; nlinarith
  rw [vertex_low hj, vertex_high hj, eq_cons, eq_cons,
    getD_fixHalf P r (by rw [hP, pow_succ, mul_comm]) hi,
    show (2 ^ rs.length + j) * 2 ^ (n - rs.length) + c = 2 ^ n + (j * 2 ^ (n - rs.length) + c) by
      rw [add_mul, h2, add_assoc]]
  ring

/-- The tables folded one challenge at a time. -/
def foldPrefix (P : List K) : List K → Option (List K)
  | [] => some P
  | r :: rs => do foldPrefix (← Poly.fix_prefix_var_mut P r) rs

/-- Folding one challenge at a time is the fold. -/
theorem foldPrefix_eq : ∀ (rs : List K) {n : ℕ} (P : List K), P.length = 2 ^ n → rs.length ≤ n →
    foldPrefix P rs = some (foldTable P n rs)
  | [], n, P, hP, _ => by
    simp only [foldPrefix, foldTable, List.length_nil, pow_zero, Nat.sub_zero, Option.some.injEq]
    refine List.ext_getElem (by simp [hP]) fun c h1 h2 => ?_
    simp [eq, vertex, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1]
  | r :: rs, n + 1, P, hP, hk => by
    rw [foldPrefix, fix_prefix_var_mut_eq P r hP]
    show foldPrefix (fixHalf P r (2 ^ n)) rs = _
    rw [foldPrefix_eq rs (fixHalf P r (2 ^ n)) (length_fixHalf P r hP) (by simpa using hk),
      foldTable_cons P hP r rs (by simpa using hk)]
  | _ :: _, 0, _, _, hk => by simp at hk

/-- One quadratic round: the honest pair, replayed at r, gives the sum over the folded tables. -/
theorem reduce_claim_fixHalf (f w : List K) {n : ℕ} (hf : f.length = 2 ^ (n + 1))
    (hw : w.length = 2 ^ (n + 1)) (r : K) :
    Basis.Evaluation.reduce_claim (∑ i ∈ range (2 ^ n), w.getD i 0 * f.getD i 0)
        (∑ i ∈ range (2 ^ n), (w.getD (2 ^ n + i) 0 - w.getD i 0) * (f.getD (2 ^ n + i) 0 - f.getD i 0))
        r (∑ b ∈ range (2 ^ (n + 1)), f.getD b 0 * w.getD b 0) =
      ∑ i ∈ range (2 ^ n), (fixHalf f r (2 ^ n)).getD i 0 * (fixHalf w r (2 ^ n)).getD i 0 := by
  rw [Basis.reduce_claim, pow_succ, mul_two, sum_range_add]
  simp only [p3_sumcheck.lagrange.mirror.extrapolate_01inf, p3_sumcheck.lagrange.mirror.lagrange_weights_01inf,
    sum_mul, ← sum_add_distrib, sub_eq_add_neg, ← sum_neg_distrib]
  refine sum_congr rfl fun i hi => ?_
  have hi := mem_range.mp hi
  rw [getD_fixHalf f r (by rw [hf, pow_succ, mul_comm]) hi, getD_fixHalf w r (by rw [hw, pow_succ, mul_comm]) hi]
  ring

/-- k rounds of the honest prover of a product replay the sum over the cube to the sum over the folded cube. -/
theorem proveProduct_partial [DecidableEq K] : ∀ (rs : List K) {n : ℕ} (f w : List K), f.length = 2 ^ n →
    w.length = 2 ^ n → rs.length ≤ n →
    ∃ ms, proveProduct f w rs = some ms ∧ ms.length = rs.length ∧
      replay .Evaluation (∑ b ∈ range (2 ^ n), f.getD b 0 * w.getD b 0) ms rs =
        ∑ c ∈ range (2 ^ (n - rs.length)), (foldTable f n rs).getD c 0 * (foldTable w n rs).getD c 0
  | [], n, f, w, hf, hw, _ => ⟨[], rfl, rfl, by
      have hf' := foldPrefix_eq [] f hf (Nat.zero_le _)
      have hw' := foldPrefix_eq [] w hw (Nat.zero_le _)
      simp only [foldPrefix, Option.some.injEq] at hf' hw'
      simp [replay, ← hf', ← hw']⟩
  | r :: rs, n + 1, f, w, hf, hw, hk => by
    have hk' : rs.length ≤ n := by simpa using hk
    obtain ⟨ms, hms, hlen, hrep⟩ := proveProduct_partial rs (fixHalf f r (2 ^ n)) (fixHalf w r (2 ^ n))
      (length_fixHalf f r hf) (length_fixHalf w r hw) hk'
    have hh : f.length / 2 = 2 ^ n := by rw [hf, pow_succ]; omega
    refine ⟨(∑ i ∈ range (2 ^ n), w.getD i 0 * f.getD i 0,
      ∑ i ∈ range (2 ^ n), (w.getD (2 ^ n + i) 0 - w.getD i 0) * (f.getD (2 ^ n + i) 0 - f.getD i 0)) :: ms,
      ?_, by simp [hlen], ?_⟩
    · simp only [proveProduct, sumcheck_coefficients_prefix_eq f w (by rw [hf, hw])
        (by rw [hf, pow_succ]; omega), fix_prefix_var_mut_eq f r hf, fix_prefix_var_mut_eq w r hw, hms,
        Option.bind_eq_bind, Option.bind_some, Option.pure_def, hh]
    · rw [foldTable_cons f hf r rs hk', foldTable_cons w hw r rs hk', List.length_cons,
        show n + 1 - (rs.length + 1) = n - rs.length by omega, ← hrep]
      simp only [replay, List.zip_cons_cons, List.foldl_cons]
      rw [reduce_claim_fixHalf f w hf hw r]
  | _ :: _, 0, _, _, _, _, hk => by simp at hk

end Plonky3Lean.Proofs.Whir
