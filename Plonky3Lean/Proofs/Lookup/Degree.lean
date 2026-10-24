module

public import Plonky3Lean.Proofs.Lookup.Api

@[expose] public section

/-!
# The degree of the fraction pin

Quotient sizing reads the degree of U f - V in multiples of the trace length n.

Substitute polynomials of degree at most:

- deg_e n for the tuple entries
- deg_m n for the counts
- n for the fraction column.

Then the pin has degree at most d n, for the degree d the gadget reports:

```text
    d = max(1 + sum_i D_i, max_i (deg m_i + sum_(j != i) D_j)),    D_i = max_k deg e_(i,k)
```

So the reported degree never underestimates.
-/

namespace Plonky3Lean.Proofs.Lookup

open Polynomial Plonky3Lean.Spec.Lookup Finset p3_lookup.mirror p3_air.symbolic.mirror

set_option linter.unusedSectionVars false

variable {K : Type} [Field K]

/-- A fingerprint with a constant challenge has at most the degree of its widest entry. -/
theorem natDegree_fingerprint_le (β : K) (e : List K[X]) (D N : ℕ)
    (he : ∀ x ∈ e, x.natDegree ≤ D * N) : (fingerprint (C β) e).natDegree ≤ D * N := by
  unfold fingerprint
  refine natDegree_sum_le_of_forall_le _ _ fun j hj => ?_
  refine (natDegree_mul_le).trans ?_
  rw [← C_pow, natDegree_C, add_zero]
  have hj := mem_range.1 hj
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simpa using hj), Option.getD_some]
  exact he _ (List.mem_reverse.1 (List.getElem_mem _))

/-- A denominator alpha - fingerprint(e) has at most the degree of its widest entry. -/
theorem natDegree_denom_le (α β : K) (e : List K[X]) (D N : ℕ)
    (he : ∀ x ∈ e, x.natDegree ≤ D * N) : (C α - fingerprint (C β) e).natDegree ≤ D * N :=
  (natDegree_sub_le _ _).trans (max_le (by simp) (natDegree_fingerprint_le β e D N he))

/-- **The pin's degree.**

Assume degrees at most:

- D_i n for the denominators
- M_i n for the counts
- n for the fraction.

Then U f - V has degree at most d n. -/
theorem natDegree_pin_le (terms : List (K[X] × K[X])) (f : K[X]) (N : ℕ) (D M : ℕ → ℕ)
    (hd : ∀ i < terms.length, (den terms i).natDegree ≤ D i * N)
    (hm : ∀ i < terms.length, (mul terms i).natDegree ≤ M i * N) (hf : f.natDegree ≤ N) :
    (denominator terms * f - numerator terms).natDegree ≤
      max (1 + ∑ i ∈ range terms.length, D i)
        ((range terms.length).sup fun i => M i + (∑ j ∈ range terms.length, D j) - D i) * N := by
  set n := terms.length
  set S := ∑ i ∈ range n, D i
  have hU : (denominator terms).natDegree ≤ S * N := by
    unfold denominator
    refine (natDegree_prod_le _ _).trans ?_
    rw [sum_mul]
    exact sum_le_sum fun i hi => hd i (mem_range.1 hi)
  refine (natDegree_sub_le _ _).trans (max_le ?_ ?_)
  · refine natDegree_mul_le.trans ?_
    calc _ ≤ S * N + N := Nat.add_le_add hU hf
      _ = (1 + S) * N := by ring
      _ ≤ _ := Nat.mul_le_mul_right _ (le_max_left _ _)
  · unfold numerator
    refine natDegree_sum_le_of_forall_le _ _ fun i hi => ?_
    have hi' := mem_range.1 hi
    refine natDegree_mul_le.trans ?_
    have hrest : (∏ j ∈ (range n).erase i, den terms j).natDegree ≤ (S - D i) * N := by
      refine (natDegree_prod_le _ _).trans ?_
      have hsplit : S = ∑ j ∈ (range n).erase i, D j + D i := (sum_erase_add _ _ hi).symm
      rw [hsplit, Nat.add_sub_cancel, sum_mul]
      exact sum_le_sum fun j hj => hd j (mem_range.1 (mem_of_mem_erase hj))
    have hDS : D i ≤ S := single_le_sum (fun _ _ => Nat.zero_le _) hi
    calc _ ≤ M i * N + (S - D i) * N := Nat.add_le_add (hm i hi') hrest
      _ = (M i + S - D i) * N := by rw [← add_mul, Nat.add_sub_assoc hDS]
      _ ≤ _ := Nat.mul_le_mul_right _
        ((le_sup (f := fun i => M i + S - D i) hi).trans (le_max_right _ _))

theorem foldr_max_eq_sup {α : Type _} (l : List α) (g : α → ℕ) (d : α) :
    (l.map g).foldr max 0 = (range l.length).sup fun i => g (l.getD i d) := by
  induction l with
  | nil => simp
  | cons x l ih =>
    rw [List.map_cons, List.foldr_cons, ih, List.length_cons, range_add_one', sup_insert, sup_map]
    simp only [Function.comp_def, List.getD_cons_zero]
    congr 1

variable {F : Type} [Field F] [DecidableEq F]

/-- The largest degree in tuple i. -/
def tupleDegree (lookup : Lookup F) (t i : ℕ) : ℕ :=
  ((lookup.elements.getD i []).map (·.degree_multiple_with_transition t)).foldr max 0

/-- The degree of count i. -/
def countDegree (lookup : Lookup F) (t i : ℕ) : ℕ :=
  ((lookup.multiplicities[i]?).map (·.degree_multiple_with_transition t)).getD 0

/-- **The reported degree, additive column.**

It is max(1 + sum_i D_i, max_i (deg m_i + sum_(j != i) D_j)). -/
theorem constraint_degree_additive (lookup : Lookup F) (hflags : lookup.flags = none)
    (hlen : lookup.multiplicities.length = lookup.elements.length) (t : ℕ) :
    constraint_degree_with_transition lookup t =
      some (max (1 + ∑ i ∈ range lookup.elements.length, tupleDegree lookup t i)
        ((range lookup.elements.length).sup fun i => countDegree lookup t i +
          (∑ j ∈ range lookup.elements.length, tupleDegree lookup t j) - tupleDegree lookup t i)) := by
  unfold constraint_degree_with_transition
  simp only [hlen, ne_eq, not_true_eq_false, ite_false, hflags, Option.bind_eq_bind,
    Option.pure_def]
  have hsum : (lookup.elements.map fun elems =>
      (elems.map (·.degree_multiple_with_transition t)).foldr max 0).sum =
      ∑ i ∈ range lookup.elements.length, tupleDegree lookup t i := by
    rw [list_sum_map_eq_sum_range _ _ []]; rfl
  rw [hsum]
  congr 2
  rw [foldr_max_eq_sup _ _ (.Leaf (.Constant 0), 0)]
  simp only [List.length_zip, List.length_map, hlen, min_self]
  refine sup_congr rfl fun i hi => ?_
  have hi := mem_range.1 hi
  simp [List.getD_eq_getElem?_getD, hi, hlen ▸ hi, countDegree, tupleDegree]

end Plonky3Lean.Proofs.Lookup
