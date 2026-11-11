module

public import P3WordBackend
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

@[expose] public section

/-!
# The exponent lift of a full-width product

The bits of an integer select powers of one generator:

```text
    prod_t (if bit t of x then g^(2^t) else 1)  =  g^x
```

The factor tree lifts the product of the factors, and the result tree lifts the two limbs.
-/

open Finset p3_word_backend.integer_mul.mirror

namespace Plonky3Lean.Proofs.WordBackend

theorem mod_two_pow_succ (b w : ℕ) :
    b % 2 ^ (w + 1) = b % 2 ^ w + (if b.testBit w then 2 ^ w else 0) := by
  rw [Nat.pow_succ, Nat.mod_mul, Nat.testBit_eq_decide_div_mod_eq]
  rcases Nat.mod_two_eq_zero_or_one (b / 2 ^ w) with h | h <;> simp [h]

/-- The bits of $b$ below $w$ select the squarings of $x$: their product is $x^{b \bmod 2^w}$. -/
theorem prod_bits {M : Type _} [CommMonoid M] (x : M) (b : ℕ) (w : ℕ) :
    ∏ j ∈ range w, (if b.testBit j then x ^ 2 ^ j else 1) = x ^ (b % 2 ^ w) := by
  induction w with
  | zero => simp [Nat.mod_one]
  | succ w ih =>
    rw [prod_range_succ, ih, mod_two_pow_succ]
    split <;> simp [pow_add]

theorem and_one_iff (z : ℕ) : z &&& 1 = 1 ↔ z.testBit 0 := by
  rw [Nat.and_one_is_mod, Nat.testBit_zero]; simp

theorem and_one_eq_one (a b i j : ℕ) :
    (a >>> i) &&& (b >>> j) &&& 1 = 1 ↔ a.testBit i ∧ b.testBit j := by
  rw [and_one_iff, Nat.testBit_and, Nat.testBit_shiftRight, Nat.testBit_shiftRight]; simp

theorem shiftRight_and_one (x t : ℕ) : (x >>> t) &&& 1 = 1 ↔ x.testBit t := by
  rw [and_one_iff, Nat.testBit_shiftRight]; simp

theorem list_prod_range {M : Type _} [CommMonoid M] (n : ℕ) (f : ℕ → M) :
    ((List.range n).map f).prod = ∏ i ∈ range n, f i := by
  simp [Finset.prod_eq_multiset_prod, Finset.range_val, Multiset.range]

theorem prod_flatMap' {M : Type _} [CommMonoid M] {α : Type _} (l : List α) (f : α → List M) :
    (l.flatMap f).prod = (l.map fun x => (f x).prod).prod := by
  simp [List.flatMap, List.prod_flatten]; rfl

open Aeneas Aeneas.Std in
theorem mapM_ok {α β : Type} (f : α → RustM β) (g : α → β) (l : List α)
    (h : ∀ x ∈ l, f x = RustM.ok (g x)) : l.mapM f = RustM.ok (l.map g) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.mapM_cons, h a (by simp), ih (fun x hx => h x (by simp [hx])), List.map_cons]
    simp [pure]

variable {F : Type _} [Field F]

theorem generator_squarings_eq (g : F) (n : ℕ) :
    generator_squarings g n = (List.range n).map fun t => g ^ 2 ^ t := by
  unfold generator_squarings
  induction n generalizing g with
  | zero => rfl
  | succ n ih =>
    rw [List.range_succ_eq_map, List.map_cons, List.map_map]
    show g :: List.iterate _ (g ^ 2) n = _
    rw [ih]
    congr 1
    · simp
    · refine List.map_congr_left fun t _ => ?_
      simp only [Function.comp_apply, Nat.succ_eq_add_one, pow_succ', pow_mul]

theorem getD_squarings (g : F) {n t : ℕ} (h : t < n) :
    (generator_squarings g n).getD t 1 = g ^ 2 ^ t := by
  rw [generator_squarings_eq, List.getD_eq_getElem _ _ (by simpa using h)]
  simp


/-- One row of factor leaves multiplies to the generator raised to the product of the factors. -/
theorem factor_row_prod (g : F) {w a b : ℕ} (hb : b < 2 ^ w) :
    (factor_leaves [a] [b] w (generator_squarings g (2 * w))).prod = g ^ (b * (a % 2 ^ w)) := by
  simp only [factor_leaves, List.zip_cons_cons, List.zip_nil_left, List.flatMap_cons,
    List.flatMap_nil, List.append_nil, prod_flatMap', list_prod_range, and_one_eq_one]
  have hrow : ∀ i ∈ range w, (∏ j ∈ range w,
      if a.testBit i ∧ b.testBit j then (generator_squarings g (2 * w)).getD (i + j) 1 else 1) =
      if a.testBit i then (g ^ b) ^ 2 ^ i else 1 := by
    intro i hi
    rw [mem_range] at hi
    by_cases ha : a.testBit i
    · simp only [ha, ↓reduceIte]
      rw [show (g ^ b) ^ 2 ^ i = (g ^ 2 ^ i) ^ (b % 2 ^ w) by
        rw [Nat.mod_eq_of_lt hb, ← pow_mul, ← pow_mul, mul_comm], ← prod_bits]
      refine prod_congr rfl fun j hj => ?_
      rw [mem_range] at hj
      simp only [true_and]
      split
      · rw [getD_squarings g (by omega), pow_add, pow_mul]
      · rfl
    · simp [ha]
  rw [prod_congr rfl hrow, prod_bits, ← pow_mul]

/-- One row of result leaves multiplies to the generator raised to the integer its limbs encode. -/
theorem result_row_prod (g : F) {w lo hi : ℕ} (hl : lo < 2 ^ w) (hh : hi < 2 ^ w) :
    (result_leaves [lo] [hi] w (generator_squarings g (2 * w))).prod = g ^ (lo + 2 ^ w * hi) := by
  have hlimbs : lo ||| (hi <<< w) = lo + 2 ^ w * hi := by
    rw [Nat.lor_comm, ← Nat.shiftLeft_add_eq_or_of_lt hl, Nat.shiftLeft_eq]; ring
  have hlt : lo + 2 ^ w * hi < 2 ^ (2 * w) := by
    rw [two_mul, pow_add]; nlinarith
  simp only [result_leaves, List.zip_cons_cons, List.zip_nil_left, List.flatMap_cons,
    List.flatMap_nil, List.append_nil, list_prod_range, shiftRight_and_one, hlimbs]
  rw [← Nat.mod_eq_of_lt hlt, ← prod_bits]
  refine prod_congr rfl fun t ht => ?_
  rw [mem_range] at ht
  rw [Nat.mod_eq_of_lt hlt]
  split
  · rw [getD_squarings g ht]
  · rfl

end Plonky3Lean.Proofs.WordBackend
