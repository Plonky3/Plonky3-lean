module

public import P3MultiStark.LogupStar
public import Plonky3Lean.Proofs.MultiStark.Blocks
public import Plonky3Lean.Proofs.Lookup.LogUp
public import Mathlib.Algebra.CharP.Basic

@[expose] public section

/-!
# The indexed lookup (logup*)

The reduction follows Soukhanov (eprint 2025/946).

A reader pulls row i of its values out of the table entry pos(i):

```text
    X(i) = T(pos(i))
```

Entries are embedded into the field bit by bit:

```text
    iota(v) = sum over the set bits k of v of node(2^k)
```

The verifier evaluates the extension of the embedding in closed form, for any number of variables:

```text
    J(y) = sum_s y_s iota(2^(m - 1 - s))
```

The pushforward of the weights w(i) = rho^j eq(r_j, i) puts on entry v the weight of the rows reading it:

```text
    Y(v) = sum over readers j, rows i with pos_j(i) = v, of w_j(i)
```

The fractions of the reduction balance exactly when two things hold:

- Y is the pushforward
- the rows whose position is no embedded entry carry total weight zero.

With Y the pushforward, the inner product of Y and T is the batched claim of the readers:

```text
    sum_v Y(v) T(v)  =  sum_j rho^j X_j~(r_j)
```
-/

namespace Plonky3Lean.Proofs.MultiStark

open p3_multi_stark.logup_star.mirror Plonky3Lean.Spec.MultiStark Plonky3Lean.Spec.MultilinearUtil
  Plonky3Lean.Spec.Lookup Plonky3Lean.Proofs.Lookup Plonky3Lean.Proofs.MultilinearUtil Finset

set_option linter.unusedSectionVars false

variable {F EF : Type _} [Field F] [Field EF] [Algebra F EF]

/-! ## The embedding and its extension -/

/-- The embedding of an entry below 2^m reads only its m low bits. -/
theorem embed_eq_sum (node : ℕ → F) {m v : ℕ} (hm : m ≤ 64) (hv : v < 2 ^ m) :
    embed node v = ∑ k ∈ range m, if v.testBit k then node (2 ^ k) else 0 := by
  rw [embed, ← List.sum_toFinset _ (List.nodup_range.filter _), List.toFinset_filter,
    List.toFinset_range, sum_filter]
  rw [show (64 : ℕ) = m + (64 - m) by omega, sum_range_add, add_eq_left]
  refine sum_eq_zero fun k _ => ?_
  rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le hv (Nat.pow_le_pow_right (by norm_num) (by omega)))]
  simp

/-- The extension of one bit of the row index is the coordinate carrying it. -/
theorem rowExt_testBit : ∀ (y : List EF) {k : ℕ}, k < y.length →
    rowExt (fun v => if v.testBit k then (1 : EF) else 0) y = y.getD (y.length - 1 - k) 0
  | [], k, hk => absurd hk (by simp)
  | c :: y, k, hk => by
    rw [ext_cons]
    simp only [List.length_cons] at hk ⊢
    by_cases hky : k < y.length
    · have hhigh : rowExt (fun b => if (2 ^ y.length + b).testBit k then (1 : EF) else 0) y =
          rowExt (fun v => if v.testBit k then (1 : EF) else 0) y :=
        rowExt_congr fun b _ => by rw [Nat.testBit_two_pow_add_gt hky]
      rw [hhigh, rowExt_testBit y hky, show y.length + 1 - 1 - k = (y.length - 1 - k) + 1 by omega]
      simp only [List.getD_cons_succ]; ring
    · obtain rfl : k = y.length := by omega
      have hlow : rowExt (fun v => if v.testBit y.length then (1 : EF) else 0) y = 0 :=
        (rowExt_congr fun b hb => by rw [Nat.testBit_lt_two_pow hb]; rfl).trans (rowExt_zero y)
      have hhigh : rowExt (fun b => if (2 ^ y.length + b).testBit y.length then (1 : EF) else 0) y =
          1 :=
        (rowExt_congr fun b hb => by
          rw [Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow hb]; rfl).trans (rowExt_const 1 y)
      rw [hlow, hhigh]
      simp

theorem sum_zipIdx_map (c : ℕ → EF) : ∀ (y : List EF) (n : ℕ),
    ((y.zipIdx n).map fun p => p.1 * c p.2).sum = ∑ s ∈ range y.length, y.getD s 0 * c (n + s)
  | [], _ => by simp
  | a :: y, n => by
    rw [List.zipIdx_cons, List.map_cons, List.sum_cons, sum_zipIdx_map c y (n + 1),
      List.length_cons, sum_range_succ']
    simp only [List.getD_cons_succ, List.getD_cons_zero, Nat.add_zero, add_comm (a * c n)]
    exact congrArg (· + a * c n) (sum_congr rfl fun x _ => by rw [show n + 1 + x = n + (x + 1) by omega])

/-- **The closed form is the extension.**

For any point of at most 64 coordinates, the verifier's closed form is the extension of the embedding. -/
theorem eval_eq_rowExt (node : ℕ → F) (y : List EF) (hy : y.length ≤ 64) :
    eval node y = rowExt (fun v => algebraMap F EF (embed node v)) y := by
  have hcongr : rowExt (fun v => algebraMap F EF (embed node v)) y =
      rowExt (fun v => ∑ k ∈ range y.length,
        algebraMap F EF (node (2 ^ k)) * (if v.testBit k then (1 : EF) else 0)) y :=
    rowExt_congr fun v hv => by
      rw [embed_eq_sum node hy hv, map_sum]
      exact sum_congr rfl fun k _ => by split_ifs <;> simp
  rw [hcongr, rowExt_sum]
  simp only [rowExt_smul]
  rw [eval]
  have hpow : ∀ j < 64, embed node (2 ^ j) = node (2 ^ j) := fun j hj => by
    rw [embed_eq_sum node (le_refl 64) (Nat.pow_lt_pow_right (by norm_num) hj),
      sum_eq_single_of_mem j (mem_range.mpr hj) fun k _ hk => by
        rw [Nat.testBit_two_pow_of_ne (Ne.symm hk)]; rfl]
    simp
  have h := sum_zipIdx_map (fun s => algebraMap F EF (embed node (2 ^ (y.length - 1 - s)))) y 0
  simp only [zero_add] at h
  rw [h, ← sum_range_reflect]
  refine sum_congr rfl fun j hj => ?_
  have hj := mem_range.mp hj
  rw [show y.length - 1 - (y.length - 1 - j) = j by omega, hpow _ (by omega), rowExt_testBit y hj]
  ring

/-! ## Injectivity over a prime field -/

/-- The binary expansion: an entry below 2^n is the sum of the powers of its set bits. -/
theorem sum_testBit_two_pow : ∀ (n v : ℕ), v < 2 ^ n →
    ∑ k ∈ range n, (if v.testBit k then 2 ^ k else 0) = v
  | 0, v, hv => by simp at hv; simp [hv]
  | n + 1, v, hv => by
    rw [sum_range_succ]
    by_cases hlow : v < 2 ^ n
    · rw [sum_testBit_two_pow n v hlow, Nat.testBit_lt_two_pow hlow]; simp
    · obtain ⟨w, rfl⟩ : ∃ w, v = 2 ^ n + w := ⟨v - 2 ^ n, by omega⟩
      have hw : w < 2 ^ n := by rw [pow_succ] at hv; omega
      rw [sum_congr rfl fun k hk => by rw [Nat.testBit_two_pow_add_gt (mem_range.mp hk)],
        sum_testBit_two_pow n w hw, Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow hw]
      simp [add_comm]

/-- Over a prime field the nodes are the integers, so an entry embeds to itself. -/
theorem embed_natCast {v : ℕ} (hv : v < 2 ^ 64) : embed (fun i => (i : F)) v = (v : F) := by
  rw [embed_eq_sum _ (le_refl 64) hv]
  conv_rhs => rw [← sum_testBit_two_pow 64 v hv, Nat.cast_sum]
  exact sum_congr rfl fun k _ => by split_ifs <;> simp

/-- **The size check.**

Take a prime field of p elements whose bit count b has 2^(b - 1) <= p.

A table that fits has distinct embeddings for its entries. -/
theorem fits_injective (p : ℕ) [CharP F p] {bits m : ℕ} (hp : 2 ^ (bits - 1) ≤ p) (hb : bits ≤ 65)
    (hfit : fits bits m = true) {v w : ℕ} (hv : v < 2 ^ m) (hw : w < 2 ^ m)
    (h : embed (fun i => (i : F)) v = embed (fun i => (i : F)) w) : v = w := by
  simp only [fits, decide_eq_true_eq] at hfit
  have hm : 2 ^ m ≤ p := (Nat.pow_le_pow_right (by norm_num) (by omega)).trans hp
  have h64 : 2 ^ m ≤ 2 ^ 64 := Nat.pow_le_pow_right (by norm_num) (by omega)
  rw [embed_natCast (by omega), embed_natCast (by omega)] at h
  exact Nat.ModEq.eq_of_lt_of_lt ((CharP.natCast_eq_natCast F p).mp h) (by omega) (by omega)

/-! ## The pushforward identity -/

section Identity

variable {K : Type _} [Field K] [DecidableEq K]

/-- The table's messages: the embedded entry v with weight -Y(v), for v < 2^m. -/
def tableMsgs (ι : ℕ → K) (Y : ℕ → K) (m : ℕ) : List (K × K) :=
  (List.range (2 ^ m)).map fun v => (ι v, -Y v)

theorem netMult_map_range (ι g : ℕ → K) (a : K) : ∀ N,
    netMult ((List.range N).map fun v => (ι v, g v)) a = ∑ v ∈ range N, if ι v = a then g v else 0
  | 0 => by simp
  | N + 1 => by
    rw [List.range_succ, List.map_append, netMult_append, netMult_map_range ι g a N, sum_range_succ]
    simp [netMult_cons]

/-- **The pushforward identity.**

Take reader messages (I(i), w(i)), and an embedding that is injective on the 2^m entries.

The readers and the table balance exactly when two things hold:

- the table's weight on each entry is the readers' net weight on its embedding
- every other key carries net weight zero. -/
theorem balanced_iff_pushforward (msgs : List (K × K)) (ι Y : ℕ → K) (m : ℕ)
    (hinj : ∀ v < 2 ^ m, ∀ w < 2 ^ m, ι v = ι w → v = w) :
    Balanced (msgs ++ tableMsgs ι Y m) ↔
      (∀ v < 2 ^ m, Y v = netMult msgs (ι v)) ∧
        ∀ a, (∀ v < 2 ^ m, ι v ≠ a) → netMult msgs a = 0 := by
  have ht : ∀ a, netMult (tableMsgs ι Y m) a = ∑ v ∈ range (2 ^ m), if ι v = a then -Y v else 0 :=
    fun a => netMult_map_range ι (fun v => -Y v) a _
  have hone : ∀ v0 < 2 ^ m, netMult (tableMsgs ι Y m) (ι v0) = -Y v0 := fun v0 hv0 => by
    rw [ht, sum_eq_single_of_mem v0 (mem_range.mpr hv0) fun v hv hne => by
      split_ifs with h
      · exact absurd (hinj v (mem_range.mp hv) v0 hv0 h) hne
      · rfl]
    simp
  have hnone : ∀ a, (∀ v < 2 ^ m, ι v ≠ a) → netMult (tableMsgs ι Y m) a = 0 := fun a ha => by
    rw [ht]; exact sum_eq_zero fun v hv => by simp [ha v (mem_range.mp hv)]
  simp only [Balanced, netMult_append]
  constructor
  · intro h
    refine ⟨fun v hv => ?_, fun a ha => ?_⟩
    · have := h (ι v); rw [hone v hv] at this; linear_combination -this
    · have := h a; rwa [hnone a ha, add_zero] at this
  · rintro ⟨h1, h2⟩ a
    by_cases ha : ∃ v < 2 ^ m, ι v = a
    · obtain ⟨v, hv, rfl⟩ := ha
      rw [hone v hv, h1 v hv]; ring
    · push Not at ha
      rw [hnone a ha, h2 a ha, add_zero]

/-- **The logarithmic-derivative form.**

The readers' sum of w / (X - I), minus the table's sum of Y / (X - iota), vanishes in K(X).

That holds exactly when Y is the pushforward and no other key carries weight. -/
theorem logDerivSum_eq_zero_iff_pushforward (msgs : List (K × K)) (ι Y : ℕ → K) (m : ℕ)
    (hinj : ∀ v < 2 ^ m, ∀ w < 2 ^ m, ι v = ι w → v = w) :
    logDerivSum (msgs ++ tableMsgs ι Y m) = 0 ↔
      (∀ v < 2 ^ m, Y v = netMult msgs (ι v)) ∧
        ∀ a, (∀ v < 2 ^ m, ι v ≠ a) → netMult msgs a = 0 := by
  rw [logDerivSum_eq_zero_iff, balanced_iff_pushforward msgs ι Y m hinj]

end Identity

/-! ## The product claim -/

section Product

variable {K : Type _} [Field K]

/-- The pushforward of the readers' weights, on entry v. -/
def pushforward {J : ℕ} (n : Fin J → ℕ) (pos : Fin J → ℕ → ℕ) (w : Fin J → ℕ → K) (v : ℕ) : K :=
  ∑ j, ∑ i ∈ range (2 ^ n j), if pos j i = v then w j i else 0

/-- **Pullback and pushforward are adjoint.**

Take reader positions inside the table.

The inner product of the pushforward with T is the readers' weighted sum of T at their positions. -/
theorem sum_pushforward_mul {J : ℕ} (n : Fin J → ℕ) (pos : Fin J → ℕ → ℕ) (w : Fin J → ℕ → K)
    (T : ℕ → K) {m : ℕ} (hpos : ∀ j, ∀ i < 2 ^ n j, pos j i < 2 ^ m) :
    ∑ v ∈ range (2 ^ m), pushforward n pos w v * T v =
      ∑ j, ∑ i ∈ range (2 ^ n j), w j i * T (pos j i) := by
  simp only [pushforward, sum_mul]
  rw [sum_comm]
  refine sum_congr rfl fun j _ => ?_
  rw [sum_comm]
  refine sum_congr rfl fun i hi => ?_
  simp only [ite_mul, zero_mul]
  simp only [sum_ite_eq, mem_range.mpr (hpos j i (mem_range.mp hi)), ↓reduceIte]

/-- **The claimed identity.**

Weigh reader j's rows by rho^j eq(r_j, i), with r_j of the reader's own arity.

With positions inside the table, the inner product of the pushforward with T is the readers' claim:

```text
    sum_v Y(v) T(v)  =  sum_j rho^j X_j~(r_j),     X_j(i) = T(pos_j(i))
``` -/
theorem pushforward_claim {J : ℕ} (r : Fin J → List K) (pos : Fin J → ℕ → ℕ) (ρ : K) (T : ℕ → K)
    {m : ℕ} (hpos : ∀ j, ∀ i < 2 ^ (r j).length, pos j i < 2 ^ m) :
    ∑ v ∈ range (2 ^ m),
        pushforward (fun j => (r j).length) pos
          (fun j i => ρ ^ (j : ℕ) * eq (vertex (r j).length i) (r j)) v * T v =
      ∑ j : Fin J, ρ ^ (j : ℕ) * rowExt (fun i => T (pos j i)) (r j) := by
  rw [sum_pushforward_mul _ _ _ T hpos]
  refine sum_congr rfl fun j _ => ?_
  simp only [rowExt, mul_sum]
  exact sum_congr rfl fun i _ => by ring

end Product

end Plonky3Lean.Proofs.MultiStark
