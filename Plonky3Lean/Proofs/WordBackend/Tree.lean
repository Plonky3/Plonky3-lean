module

public import Plonky3Lean.Proofs.WordBackend.Lift

@[expose] public section

/-!
# Product trees

A layer multiplies each pair of adjacent entries of the layer below it.

After $e$ layers, entry $r$ is the product of the $2^e$ leaves that start at $r 2^e$:

```text
    leaves      x_0  x_1  x_2  x_3  x_4
    layer 1     x_0 x_1    x_2 x_3            x_4 has no partner and is dropped
    layer 2     x_0 x_1 x_2 x_3
```

So a layer $e$ levels up has $\lfloor n / 2^e \rfloor$ entries, for $n$ leaves.
-/

open Finset p3_word_backend.integer_mul.mirror

namespace Plonky3Lean.Proofs.WordBackend

variable {F : Type _} [Field F]

theorem layer_above_length (l : List F) : (layer_above l).length = l.length / 2 := by
  simp [layer_above]

theorem layer_above_getD (l : List F) {r : ℕ} (h : r < l.length / 2) :
    (layer_above l).getD r 0 = l.getD (2 * r) 0 * l.getD (2 * r + 1) 0 := by
  simp [layer_above, h]

theorem up_length (l : List F) (e : ℕ) : (layer_above^[e] l).length = l.length / 2 ^ e := by
  induction e with
  | zero => simp
  | succ e ih =>
    rw [Function.iterate_succ_apply', layer_above_length, ih, Nat.div_div_eq_div_mul, pow_succ]

/-- Entry $r$ of the layer $e$ levels up is the product of leaves $r 2^e$ to $r 2^e + 2^e - 1$. -/
theorem up_getD (l : List F) (e : ℕ) {r : ℕ} (h : r < l.length / 2 ^ e) :
    (layer_above^[e] l).getD r 0 = ∏ s ∈ range (2 ^ e), l.getD (r * 2 ^ e + s) 0 := by
  induction e generalizing r with
  | zero => simp
  | succ e ih =>
    have hq : l.length / 2 ^ (e + 1) = l.length / 2 ^ e / 2 := by
      rw [pow_succ, Nat.div_div_eq_div_mul]
    rw [Function.iterate_succ_apply', layer_above_getD _ (by rw [up_length]; omega),
      ih (by omega), ih (by omega), pow_succ, mul_two, prod_range_add]
    congr 1 <;> refine prod_congr rfl fun s _ => ?_ <;> congr 1 <;> ring

/-- The layers, root first: the layer at position $t$ is $d - t$ levels above the leaves. -/
theorem product_layers_eq (leaves : List F) (d : ℕ) :
    product_layers leaves d = (List.range (d + 1)).reverse.map (layer_above^[·] leaves) := by
  induction d with
  | zero => rfl
  | succ d ih =>
    rw [product_layers, List.range_succ, List.foldl_append, ← product_layers, ih,
      List.range_succ (n := d + 1), List.reverse_append]
    simp [Function.iterate_succ_apply', List.getLast?_range]

theorem product_layers_length (leaves : List F) (d : ℕ) : (product_layers leaves d).length = d + 1 := by
  simp [product_layers_eq]

theorem product_layers_getElem (leaves : List F) (d : ℕ) {t : ℕ}
    (h : t < (product_layers leaves d).length) :
    (product_layers leaves d)[t] = layer_above^[d - t] leaves := by
  simp only [product_layers_eq, List.getElem_map, List.getElem_reverse, List.getElem_range]
  congr 1
  simp only [List.length_range]
  omega

/-- Each layer above the leaves multiplies the pairs of the layer below it. -/
theorem product_layers_children (leaves : List F) (d : ℕ) {t : ℕ} (h : t < d) :
    (product_layers leaves d)[t]'(by rw [product_layers_length]; omega) =
      layer_above ((product_layers leaves d)[t + 1]'(by rw [product_layers_length]; omega)) := by
  rw [product_layers_getElem, product_layers_getElem, show d - t = d - (t + 1) + 1 by omega,
    Function.iterate_succ_apply']

theorem product_layers_root (leaves : List F) (d : ℕ) :
    (product_layers leaves d)[0]'(by rw [product_layers_length]; omega) = layer_above^[d] leaves := by
  rw [product_layers_getElem, Nat.sub_zero]

/-- A block of equal chunks: the entry at $r c + s$ is entry $s$ of chunk $r$. -/
theorem flatMap_getD {α : Type _} (rows : List α) (f : α → List F) {c : ℕ}
    (hc : ∀ x ∈ rows, (f x).length = c) {r s : ℕ} (hr : r < rows.length) (hs : s < c) :
    (rows.flatMap f).getD (r * c + s) 0 = (f rows[r]).getD s 0 := by
  induction rows generalizing r with
  | nil => simp at hr
  | cons x xs ih =>
    rw [List.flatMap_cons]
    have hx := hc x (by simp)
    cases r with
    | zero => simp [List.getD_eq_getElem?_getD, List.getElem?_append_left (show s < (f x).length by omega)]
    | succ r =>
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by rw [hx]; nlinarith), hx,
        show (r + 1) * c + s - c = r * c + s by rw [Nat.succ_mul]; omega, ← List.getD_eq_getElem?_getD,
        ih (fun y hy => hc y (by simp [hy])) (by simp at hr; omega)]
      simp

theorem prod_getD (l : List F) : ∏ s ∈ range l.length, l.getD s 0 = l.prod := by
  rw [← list_prod_range]
  congr 1
  refine List.ext_getElem (by simp) fun i _ h => ?_
  simp [List.getElem?_eq_getElem h]

/-- Leaves in rows of $2^d$: the layer $d$ levels up has one entry per row, the product of its row. -/
theorem up_rows {α : Type _} (rows : List α) (f : α → List F) (d : ℕ)
    (hc : ∀ x ∈ rows, (f x).length = 2 ^ d) :
    (layer_above^[d] (rows.flatMap f)).length = rows.length ∧
      ∀ r (hr : r < rows.length), (layer_above^[d] (rows.flatMap f)).getD r 0 = (f rows[r]).prod := by
  have hlen : (rows.flatMap f).length = rows.length * 2 ^ d := by
    rw [List.length_flatMap, List.map_congr_left hc, List.map_const', List.sum_replicate, smul_eq_mul]
  refine ⟨by rw [up_length, hlen, Nat.mul_div_cancel _ (by positivity)], fun r hr => ?_⟩
  rw [up_getD _ _ (by rw [hlen, Nat.mul_div_cancel _ (by positivity)]; exact hr),
    ← prod_getD, hc _ (List.getElem_mem hr)]
  exact prod_congr rfl fun s hs => flatMap_getD rows f hc hr (by simpa using hs)

theorem factor_leaves_rows (left right : List ℕ) (w : ℕ) (p : List F) :
    factor_leaves left right w p =
      (left.zip right).flatMap fun ab => factor_leaves [ab.1] [ab.2] w p := by
  simp [factor_leaves]

theorem result_leaves_rows (low high : List ℕ) (w : ℕ) (p : List F) :
    result_leaves low high w p =
      (low.zip high).flatMap fun ab => result_leaves [ab.1] [ab.2] w p := by
  simp [result_leaves]

/-- The factor tree over words of $2^k$ bits.

Its root has one entry per row, and entry $r$ is $g^{a_r b_r}$. -/
theorem factor_root (g : F) (k : ℕ) {left right : List ℕ} (hlen : left.length = right.length)
    (hl : ∀ a ∈ left, a < 2 ^ 2 ^ k) (hr : ∀ b ∈ right, b < 2 ^ 2 ^ k) :
    let root := layer_above^[Tree.depth k .Factor]
      (factor_leaves left right (2 ^ k) (generator_squarings g (2 * 2 ^ k)))
    root.length = left.length ∧
      ∀ r (h : r < left.length), root.getD r 0 = g ^ (left[r] * right[r]'(hlen ▸ h)) := by
  have hc : ∀ ab ∈ left.zip right,
      (factor_leaves [ab.1] [ab.2] (2 ^ k) (generator_squarings g (2 * 2 ^ k))).length =
        2 ^ Tree.depth k .Factor := by
    intro ab _
    simp [factor_leaves, Tree.depth, pow_mul', sq]
  obtain ⟨h1, h2⟩ := up_rows _ _ _ hc
  rw [factor_leaves_rows]
  refine ⟨by simpa [hlen] using h1, fun r h => ?_⟩
  have hz : r < (left.zip right).length := by simp [← hlen, h]
  rw [h2 r hz, factor_row_prod g (by simpa using hr _ (List.getElem_mem (hlen ▸ h))),
    List.getElem_zip, Nat.mod_eq_of_lt (hl _ (List.getElem_mem h)), mul_comm]

/-- The result tree over words of $2^k$ bits.

Its root has one entry per row, and entry $r$ is $g^{lo_r + 2^w hi_r}$, with $w = 2^k$. -/
theorem result_root (g : F) (k : ℕ) {low high : List ℕ} (hlen : low.length = high.length)
    (hl : ∀ a ∈ low, a < 2 ^ 2 ^ k) (hh : ∀ b ∈ high, b < 2 ^ 2 ^ k) :
    let root := layer_above^[Tree.depth k .Result]
      (result_leaves low high (2 ^ k) (generator_squarings g (2 * 2 ^ k)))
    root.length = low.length ∧
      ∀ r (h : r < low.length), root.getD r 0 = g ^ (low[r] + 2 ^ 2 ^ k * high[r]'(hlen ▸ h)) := by
  have hc : ∀ ab ∈ low.zip high,
      (result_leaves [ab.1] [ab.2] (2 ^ k) (generator_squarings g (2 * 2 ^ k))).length =
        2 ^ Tree.depth k .Result := by
    intro ab _
    simp [result_leaves, Tree.depth, pow_succ, mul_comm]
  obtain ⟨h1, h2⟩ := up_rows _ _ _ hc
  rw [result_leaves_rows]
  refine ⟨by simpa [hlen] using h1, fun r h => ?_⟩
  have hz : r < (low.zip high).length := by simp [← hlen, h]
  rw [h2 r hz, List.getElem_zip,
    result_row_prod g (hl _ (List.getElem_mem h)) (hh _ (List.getElem_mem (hlen ▸ h)))]

end Plonky3Lean.Proofs.WordBackend
