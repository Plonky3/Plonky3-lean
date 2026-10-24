module

public import Plonky3Lean.Proofs.Lookup.RunningSum
public import P3Lookup

@[expose] public section

/-!
# The LogUp gadget

The transcribed tuple combiners compute the fingerprint.

The rational folds compute the cleared fraction U f = V of the specification.
-/

namespace Plonky3Lean.Proofs.Lookup

open Plonky3Lean.Spec.Lookup Finset p3_lookup.mirror

set_option linter.unusedSectionVars false

variable {K : Type} [Field K]

/-- The field's own ring operations. -/
def fieldOps (K : Type) [Field K] : RingOps K := ⟨(· + ·), (· - ·), (· * ·), 0, 1⟩

/-- **The constraint-side combiner** is alpha minus the fingerprint. -/
theorem combine_elements_field (elements : List (List K)) (α β : K) :
    combine_elements (fieldOps K) elements α β = elements.map fun e => α - fingerprint β e := by
  refine List.map_congr_left fun e _ => ?_
  simp only [fieldOps]
  rw [← foldl_horner_zero]
  congr 1; congr 1; funext acc x; ring

/-! ## Products of a list -/

theorem scanl_mul (b : K) (l : List K) :
    l.scanl (· * ·) b = (List.range (l.length + 1)).map fun i => b * (l.take i).prod := by
  induction l generalizing b with
  | nil => simp
  | cons a l ih =>
    rw [List.scanl_cons, ih]
    simp only [List.length_cons, List.range_succ_eq_map (n := l.length + 1), List.map_cons,
      List.map_map]
    simp [Function.comp_def, mul_assoc]

theorem scanr_mul (l : List K) :
    l.scanr (fun t acc => acc * t) 1 = (List.range (l.length + 1)).map fun i => (l.drop i).prod := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.scanr_cons, ih]
    simp only [List.length_cons, List.range_succ_eq_map (n := l.length + 1), List.map_cons,
      List.map_map]
    simp [Function.comp_def, mul_comm, List.prod_eq_foldr]

theorem prod_eq_prod_range (l : List K) : l.prod = ∏ j ∈ range l.length, l.getD j 1 := by
  induction l with
  | nil => simp
  | cons a l ih => rw [List.prod_cons, ih, List.length_cons, prod_range_succ']; simp [mul_comm]

theorem prod_take_eq (l : List K) {i : ℕ} (hi : i ≤ l.length) :
    (l.take i).prod = ∏ j ∈ range i, l.getD j 1 := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [List.prod_take_succ l i (by omega), ih (by omega), prod_range_succ]
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show i < l.length by omega)]

theorem prod_drop_eq (l : List K) (i : ℕ) :
    (l.drop i).prod = ∏ j ∈ Ico i l.length, l.getD j 1 := by
  rw [prod_eq_prod_range, prod_Ico_eq_prod_range, List.length_drop]
  refine prod_congr rfl fun k _ => ?_
  simp [List.getD_eq_getElem?_getD]

theorem range_erase_eq {n i : ℕ} (hi : i < n) : (range n).erase i = range i ∪ Ico (i + 1) n := by
  ext j; simp only [mem_erase, mem_range, mem_union, mem_Ico]; omega

/-- The product of the others is the product before times the product after. -/
theorem prod_erase_eq (l : List K) {i : ℕ} (hi : i < l.length) :
    ∏ j ∈ (range l.length).erase i, l.getD j 1 = (l.take i).prod * (l.drop (i + 1)).prod := by
  rw [range_erase_eq hi, prod_union (disjoint_left.2 fun j h1 h2 => by
    simp only [mem_range, mem_Ico] at h1 h2; omega), prod_take_eq l hi.le, prod_drop_eq]

/-! ## The rational fold -/

/-- The (d, m) pairs of a row: d = alpha - fingerprint(tuple). -/
def rowTerms (elements : List (List K)) (mults : List K) (α β : K) : List (K × K) :=
  (elements.map fun e => α - fingerprint β e).zip mults

theorem den_rowTerms {elements : List (List K)} {mults : List K} {α β : K}
    (h : mults.length = elements.length) {j : ℕ} (hj : j < elements.length) :
    den (rowTerms elements mults α β) j = (elements.map fun e => α - fingerprint β e).getD j 1 := by
  simp [den, rowTerms, List.getD_eq_getElem?_getD, hj, h ▸ hj]

theorem mul_rowTerms {elements : List (List K)} {mults : List K} {α β : K}
    (h : mults.length = elements.length) {j : ℕ} (hj : j < elements.length) :
    mul (rowTerms elements mults α β) j = mults.getD j 0 := by
  simp [mul, rowTerms, List.getD_eq_getElem?_getD, hj, h ▸ hj]

theorem foldlM_range_some {M : Type} (n : ℕ) (f : M → ℕ → Option M) (g : ℕ → M → M) (a : M)
    (hf : ∀ i < n, ∀ acc, f acc i = some (g i acc)) :
    (List.range n).foldlM f a = some ((List.range n).foldl (fun acc i => g i acc) a) := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih =>
    rw [List.range_succ, List.foldlM_append, ih a fun i hi => hf i (by omega), List.foldl_append]
    simp [hf n (by omega)]

theorem foldl_range_add (n : ℕ) (g : ℕ → K) (a : K) :
    (List.range n).foldl (fun acc i => acc + g i) a = a + ∑ i ∈ range n, g i := by
  induction n generalizing a with
  | zero => simp
  | succ n ih => rw [List.range_succ, List.foldl_append, ih, sum_range_succ]; simp [add_assoc]

/-- **The additive fold** computes V and U:

- V is the sum of each multiplicity times the other denominators
- U is the product of all denominators. -/
theorem compute_combined_sum_terms_field (elements : List (List K)) (mults : List K) (α β : K)
    (h : mults.length = elements.length) :
    compute_combined_sum_terms (fieldOps K) elements mults α β =
      some (numerator (rowTerms elements mults α β), denominator (rowTerms elements mults α β)) := by
  have hlen : (rowTerms elements mults α β).length = elements.length := by
    simp [rowTerms, h]
  unfold compute_combined_sum_terms
  split_ifs with he
  · rw [List.isEmpty_iff] at he; subst he
    simp [numerator, denominator, rowTerms, fieldOps]
  · set dl := elements.map fun e => α - fingerprint β e with hdl
    have hdlen : dl.length = elements.length := by simp [hdl]
    rw [combine_elements_field, ← hdl]
    simp only [fieldOps, scanl_mul, scanr_mul, one_mul]
    rw [foldlM_range_some _ _ (fun i acc => acc + mults.getD i 0 * (dl.take i).prod *
      (dl.drop (i + 1)).prod) _ fun i hi acc => by
        rw [List.getElem?_map, List.getElem?_range (by omega), List.getElem?_map,
          List.getElem?_range (by omega)]
        simp [List.getElem?_eq_getElem (show i < mults.length by omega)]]
    simp only [Option.map_some, foldl_range_add, zero_add]
    congr 2
    · unfold numerator; rw [hlen]
      refine sum_congr rfl fun i hi => ?_
      have hi := mem_range.1 hi
      rw [mul_rowTerms h hi, mul_assoc]
      congr 1
      rw [← prod_erase_eq dl (by omega), hdlen]
      exact prod_congr rfl fun j hj => (den_rowTerms h (mem_range.1 (mem_of_mem_erase hj))).symm
    · unfold denominator
      rw [List.getElem?_map, List.getElem?_range (by omega), Option.map_some, Option.getD_some,
        ← hdlen, List.take_length, hlen,
        prod_eq_prod_range, hdlen]
      exact prod_congr rfl fun j hj => (den_rowTerms h (mem_range.1 hj)).symm

end Plonky3Lean.Proofs.Lookup
