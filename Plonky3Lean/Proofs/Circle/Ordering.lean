module

public import P3Circle.Ordering
public import Plonky3Lean.Proofs.Dft.Glue
public import Plonky3Lean.Proofs.Matrix.BitRev
public import Plonky3Lean.Proofs.Circle.Util

@[expose] public section

/-!
# p3-circle: the circle FFT order

For n >= 1 and a < 2^(n - 1), with rev the (n - 1)-bit reversal:

```text
    sigma(2 a)      = 2 rev(a)
    sigma(2 a + 1)  = 2 rev(2^(n-1) - 1 - a) + 1
```

So sigma keeps the parity of the index, permutes [0, 2^n), and is its own inverse.
-/

namespace Plonky3Lean.Proofs.Circle

open p3_circle.ordering.mirror Plonky3Lean.Proofs.Dft Plonky3Lean.Proofs.Matrix

local notation "rev" => Plonky3Lean.Spec.Matrix.bitRev

/-- Reversing the bits of the complement 2^k - 1 - x complements the reversal. -/
theorem rev_complement (k : ℕ) {x : ℕ} (hx : x < 2 ^ k) : rev k (2 ^ k - 1 - x) = 2 ^ k - 1 - rev k x := by
  induction k generalizing x with
  | zero => simp [Plonky3Lean.Spec.Matrix.bitRev]
  | succ k ih =>
    simp only [Plonky3Lean.Spec.Matrix.bitRev]
    have hp : 2 ^ (k + 1) = 2 * 2 ^ k := by ring
    rw [show (2 ^ (k + 1) - 1 - x) / 2 = 2 ^ k - 1 - x / 2 by omega, ih (by omega)]
    have := Plonky3Lean.Proofs.Matrix.bitRev_lt k (x / 2)
    rcases Nat.mod_two_eq_zero_or_one x with h | h
    · rw [show (2 ^ (k + 1) - 1 - x) % 2 = 1 by omega, h]; omega
    · rw [show (2 ^ (k + 1) - 1 - x) % 2 = 0 by omega, h]; omega

theorem cfft_permute_index_even {n a : ℕ} (ha : a < 2 ^ n) :
    cfft_permute_index (2 * a) (n + 1) = 2 * rev n a := by
  simp only [cfft_permute_index, Nat.mul_mod_right, ↓reduceIte, bitRev_eq,
    show 2 * a / 2 = a by omega]
  exact rev_upper n ha

theorem cfft_permute_index_odd {n a : ℕ} (ha : a < 2 ^ n) :
    cfft_permute_index (2 * a + 1) (n + 1) = 2 * rev n (2 ^ n - 1 - a) + 1 := by
  simp only [cfft_permute_index, show (2 * a + 1) % 2 = 1 by omega, show (2 * a + 1) / 2 = a by omega,
    one_ne_zero, ↓reduceIte, bitRev_eq]
  rw [show 2 ^ (n + 1) - a - 1 = 2 ^ n + (2 ^ n - 1 - a) by rw [pow_succ]; omega]
  exact rev_lower n (by omega)

/-- The order keeps the parity of the index. -/
theorem cfft_permute_index_mod_two {n i : ℕ} (hi : i < 2 ^ (n + 1)) :
    cfft_permute_index i (n + 1) % 2 = i % 2 := by
  obtain ⟨a, rfl | rfl⟩ := Nat.even_or_odd' i
  · rw [cfft_permute_index_even (by rw [pow_succ] at hi; omega)]; omega
  · rw [cfft_permute_index_odd (by rw [pow_succ] at hi; omega)]; omega

theorem cfft_permute_index_lt (n i : ℕ) : cfft_permute_index i n < 2 ^ n := by
  unfold cfft_permute_index; rw [bitRev_eq]; exact bitRev_lt _ _

/-- The order is an involution of [0, 2^n). -/
theorem cfft_permute_index_involutive {n i : ℕ} (hi : i < 2 ^ n) :
    cfft_permute_index (cfft_permute_index i n) n = i := by
  rcases n with _ | n
  · simp at hi; subst hi; rfl
  obtain ⟨a, rfl | rfl⟩ := Nat.even_or_odd' i
  · have ha : a < 2 ^ n := by rw [pow_succ] at hi; omega
    rw [cfft_permute_index_even ha, cfft_permute_index_even (bitRev_lt _ _), bitRev_bitRev ha]
  · have ha : a < 2 ^ n := by rw [pow_succ] at hi; omega
    have hc := bitRev_lt n (2 ^ n - 1 - a)
    rw [cfft_permute_index_odd ha, cfft_permute_index_odd hc, rev_complement n (by omega),
      bitRev_bitRev (by omega)]
    omega

/-- The order is a bijection of [0, 2^n). -/
theorem cfft_permute_index_bijOn (n : ℕ) :
    Set.BijOn (cfft_permute_index · n) (Set.Iio (2 ^ n)) (Set.Iio (2 ^ n)) :=
  Set.InvOn.bijOn ⟨fun _ hi => cfft_permute_index_involutive hi,
    fun _ hi => cfft_permute_index_involutive hi⟩
    (fun i _ => cfft_permute_index_lt n i) (fun i _ => cfft_permute_index_lt n i)

/-- The permuted slice reads entry i at sigma(i).

It panics exactly when the length is not a power of two. -/
theorem cfft_permute_slice_eq {α : Type _} (xs : List α) {n : ℕ} (hn : xs.length = 2 ^ n) :
    cfft_permute_slice xs = some ((List.range xs.length).map fun i =>
      xs[cfft_permute_index i n]'(by rw [hn]; exact cfft_permute_index_lt n i)) := by
  rw [cfft_permute_slice, hn, log2Strict_pow, ← hn]
  simp only [Option.bind_eq_bind, Option.bind_some]
  exact mapM_eq_some_map _ _ _ fun i _ => List.getElem?_eq_getElem _


/-- One step of an in-place permutation by an involution f.

It swaps rows i and f(i) when i < f(i). -/
def invStep {V : Type _} (f : ℕ → ℕ) (acc : ℕ → V) (i : ℕ) : ℕ → V :=
  if i < f i then p3_dft.mirror.swapRows i (f i) acc else acc

/-- After the first k steps, the rows r and f(r) are exchanged exactly when one of them is below k. -/
theorem invStep_loop {V : Type _} {N : ℕ} (f : ℕ → ℕ) (hf : ∀ x < N, f (f x) = x)
    (hN : ∀ x, f x < N) (rows : ℕ → V) (k : ℕ) (hk : k ≤ N) (r : ℕ) :
    (List.range k).foldl (invStep f) rows r =
      rows (if r < N ∧ (r < k ∨ f r < k) then f r else r) := by
  induction k generalizing r with
  | zero => simp
  | succ k ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    have ihA := ih (by omega)
    generalize List.foldl (invStep f) rows (List.range k) = A at ihA ⊢
    have := hf k; have := hf r; have := hf (f k); have := hf (f r)
    have := hN k; have := hN r; have := hN (f k); have := hN (f r)
    have : r < N → f r = k → r = f k := fun h e => by rw [← e, hf r h]
    have : r = k → f r = f k := fun e => by rw [e]
    unfold invStep p3_dft.mirror.swapRows
    by_cases hj : k < f k
    · simp only [hj, ↓reduceIte]
      by_cases h1 : r = k
      · subst h1; simp only [↓reduceIte, ihA]; congr 1; split <;> split <;> omega
      by_cases h2 : r = f k
      · subst h2
        simp only [show f k ≠ k by omega, ↓reduceIte, ihA]; congr 1; split <;> split <;> omega
      simp only [h1, h2, ↓reduceIte, ihA]; congr 1; split <;> split <;> omega
    · simp only [hj, ↓reduceIte, ihA]; congr 1; split <;> split <;> omega

/-- The in-place chunk permutation puts row sigma(r) at every row r below 2^n.

It leaves the rows past the end alone. -/
theorem cfft_permute_slice_chunked_in_place_eq {V : Type _} (n : ℕ) (rows : ℕ → V) :
    cfft_permute_slice_chunked_in_place (2 ^ n) rows =
      some fun r => if r < 2 ^ n then rows (cfft_permute_index r n) else rows r := by
  rw [cfft_permute_slice_chunked_in_place, log2Strict_pow]
  simp only [Option.bind_eq_bind, Option.bind_some, Option.some.injEq]
  funext r
  have := invStep_loop (cfft_permute_index · n) (fun x hx => cfft_permute_index_involutive hx)
    (cfft_permute_index_lt n) rows (2 ^ n) le_rfl r
  unfold invStep at this
  rw [this]
  by_cases hr : r < 2 ^ n <;> simp [hr]

end Plonky3Lean.Proofs.Circle
