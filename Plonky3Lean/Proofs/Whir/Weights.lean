module

public import Plonky3Lean.Proofs.Whir.Sumcheck
public import Plonky3Lean.Proofs.MultilinearUtil.Unique

@[expose] public section

/-!
# The constraint weights of one WHIR iteration

An out-of-domain answer is P~ at pow(z), the sum of P against eq(pow(z), .).

A shift answer is P^ at q, the sum of P against the selector of the powers of q.

With honest answers, the claim after one iteration is the sum of the folded table against the new weight.
-/

namespace Plonky3Lean.Proofs.Whir

open Finset Plonky3Lean.Spec.MultilinearUtil Plonky3Lean.Spec.Whir Plonky3Lean.Proofs.MultilinearUtil

variable {K : Type _} [Field K]

omit [Field K] in
theorem eq_comm' [CommRing K] (x r : List K) : eq x r = eq r x := by
  induction x generalizing r with
  | nil => cases r <;> simp [eq]
  | cons a x ih => cases r with
    | nil => simp [eq]
    | cons c r => rw [eq_cons, eq_cons, ih]; ring

omit [Field K] in
/-- The selector of q is the extension of the powers of q. -/
theorem sel_eq_mle [CommRing K] (q : K) : ∀ x : List K, sel q x = mle (powTable q x.length) x
  | [] => by simp [sel, powTable]
  | c :: x => by
    rw [List.length_cons, mle_powTable_cons, ← sel_eq_mle q x]
    simp only [sel, List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_map,
      List.zipWith_cons_cons, List.prod_cons, Nat.add_sub_cancel, Nat.sub_zero]
    rw [show c * q ^ 2 ^ x.length + (1 - c) = 1 - c + c * q ^ 2 ^ x.length by ring]
    congr 3
    exact List.map_congr_left fun i _ => by simp only [Function.comp]; omega

/-- At the vertex b the selector of q is q^b. -/
theorem sel_vertex (q : K) {n b : ℕ} (hb : b < 2 ^ n) : sel q (vertex n b) = q ^ b := by
  rw [sel_eq_mle, length_vertex, mle_vertex _ hb]
  simp [powTable, List.getD_eq_getElem?_getD, hb]

/-- The sum of a table against eq(pow(z), .) is its extension at pow(z). -/
theorem cubeDot_eq (P : List K) (n : ℕ) (z : K) :
    ∑ b ∈ range (2 ^ n), P.getD b 0 * eq (pow z n) (vertex n b) = mle P (pow z n) := by
  rw [mle]
  simp only [pow, List.length_map, List.length_range]
  exact sum_congr rfl fun b _ => by rw [eq_comm', mul_comm]

/-- The sum of a table of 2^n entries against the selector of q is its polynomial at q. -/
theorem cubeDot_sel (P : List K) {n : ℕ} (hP : P.length = 2 ^ n) (q : K) :
    ∑ b ∈ range (2 ^ n), P.getD b 0 * sel q (vertex n b) = uni P q := by
  rw [uni, hP]
  exact sum_congr rfl fun b hb => by rw [sel_vertex q (mem_range.mp hb)]

/-- Take the claim update of Construction 5.1, check 2(c), with honest answers.

It is the sum of the folded table against the weight update of step 2(e). -/
theorem nextClaim_cubeDot (P : List K) {m : ℕ} (hP : P.length = 2 ^ m) (w : List K → K) (r : List K)
    (γ : K) (ood queries : List K) :
    nextClaim (cubeDot P m fun x => w (r ++ x)) γ (ood.map fun z => mle P (pow z m))
        (queries.map (uni P)) = cubeDot P m (nextWeight w r γ ood queries m) := by
  simp only [nextClaim, cubeDot, nextWeight, List.length_map, mul_add, sum_add_distrib, mul_sum]
  congr 1
  · congr 1
    rw [sum_comm]
    refine sum_congr rfl fun j hj => ?_
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem (mem_range.mp hj),
      Option.map_some, Option.getD_some, ← cubeDot_eq, mul_sum]
    exact sum_congr rfl fun b _ => by simp [List.getD_eq_getElem?_getD, mem_range.mp hj]; ring
  · rw [sum_comm]
    refine sum_congr rfl fun j hj => ?_
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem (mem_range.mp hj),
      Option.map_some, Option.getD_some, ← cubeDot_sel P hP, mul_sum]
    exact sum_congr rfl fun b _ => by simp [List.getD_eq_getElem?_getD, mem_range.mp hj]; ring

end Plonky3Lean.Proofs.Whir
