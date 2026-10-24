module

public import Mathlib.Algebra.BigOperators.Group.List.Basic
public import Mathlib.Tactic.Linarith

@[expose] public section

/-!
# Instance-packed blocks never overlap

A composition lays its calls out one after the other.

Call `k` owns a block of `m_k * w_k` words: `m_k` instances of `w_k` slots each.

```text
    word = (blocks of calls 0 .. k-1) + instance * w_k + slot
```

Two distinct (call, instance, slot) triples, each in range, always name distinct words.

Every such word lies below the total length.
-/

namespace Plonky3Lean.Proofs.Word

/-- The words the first `k` blocks own. -/
def pref (sizes : List ℕ) (k : ℕ) : ℕ := (sizes.take k).sum

theorem pref_succ (sizes : List ℕ) (k : ℕ) (h : k < sizes.length) :
    pref sizes (k + 1) = pref sizes k + sizes[k] :=
  List.sum_take_succ sizes k h

theorem pref_mono (sizes : List ℕ) {a b : ℕ} (h : a ≤ b) : pref sizes a ≤ pref sizes b := by
  unfold pref
  rw [← List.take_append_drop a (sizes.take b), List.take_take, Nat.min_eq_left h, List.sum_append]
  omega

theorem pref_le_sum (sizes : List ℕ) (k : ℕ) : pref sizes k ≤ sizes.sum := by
  have := pref_mono sizes (Nat.le_max_left k sizes.length)
  simp only [pref, List.take_of_length_le (Nat.le_max_right k sizes.length)] at this ⊢
  exact this

/-- A slot of an instance lies inside the instances' block. -/
theorem slot_in_block {m w i s : ℕ} (hi : i < m) (hs : s < w) : i * w + s < m * w := by
  have : (i + 1) * w ≤ m * w := Nat.mul_le_mul_right _ hi
  rw [Nat.succ_mul] at this
  omega

/-- An instance and a slot are recovered from their packed offset. -/
theorem offset_injective {w i₁ i₂ s₁ s₂ : ℕ} (hs₁ : s₁ < w) (hs₂ : s₂ < w)
    (h : i₁ * w + s₁ = i₂ * w + s₂) : i₁ = i₂ ∧ s₁ = s₂ := by
  rcases lt_trichotomy i₁ i₂ with hlt | rfl | hlt
  · have := slot_in_block hlt hs₁; nlinarith
  · exact ⟨rfl, by omega⟩
  · have := slot_in_block hlt hs₂; nlinarith

/-- The word of an in-range triple: the earlier blocks, then the instance and the slot. -/
def packed (m w : List ℕ) (k i s : ℕ) : ℕ :=
  pref (List.zipWith (· * ·) m w) k + i * w.getD k 0 + s

/-- An in-range triple names a word inside its call's block. -/
theorem packed_bounds (m w : List ℕ) (hlen : m.length = w.length) {k i s : ℕ}
    (hk : k < m.length) (hi : i < m.getD k 0) (hs : s < w.getD k 0) :
    pref (List.zipWith (· * ·) m w) k ≤ packed m w k i s ∧
      packed m w k i s < pref (List.zipWith (· * ·) m w) (k + 1) := by
  have hz : k < (List.zipWith (· * ·) m w).length := by simp; omega
  rw [pref_succ _ _ hz]
  simp only [List.getElem_zipWith]
  have := slot_in_block hi hs
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk,
    List.getElem?_eq_getElem (hlen ▸ hk), Option.getD_some] at this
  simp only [packed, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (hlen ▸ hk),
    Option.getD_some]
  omega

/-- Distinct in-range triples name distinct words. -/
theorem packed_injective (m w : List ℕ) (hlen : m.length = w.length) {k₁ k₂ i₁ i₂ s₁ s₂ : ℕ}
    (hk₁ : k₁ < m.length) (hi₁ : i₁ < m.getD k₁ 0) (hs₁ : s₁ < w.getD k₁ 0)
    (hk₂ : k₂ < m.length) (hi₂ : i₂ < m.getD k₂ 0) (hs₂ : s₂ < w.getD k₂ 0)
    (h : packed m w k₁ i₁ s₁ = packed m w k₂ i₂ s₂) : k₁ = k₂ ∧ i₁ = i₂ ∧ s₁ = s₂ := by
  have b₁ := packed_bounds m w hlen hk₁ hi₁ hs₁
  have b₂ := packed_bounds m w hlen hk₂ hi₂ hs₂
  rcases lt_trichotomy k₁ k₂ with hlt | rfl | hlt
  · have := pref_mono (List.zipWith (· * ·) m w) (show _ + 1 ≤ _ from hlt); omega
  · unfold packed at h
    exact ⟨rfl, offset_injective hs₁ hs₂ (by omega)⟩
  · have := pref_mono (List.zipWith (· * ·) m w) (show _ + 1 ≤ _ from hlt); omega

/-- Every in-range word lies below the total length. -/
theorem packed_lt_total (m w : List ℕ) (hlen : m.length = w.length) {k i s : ℕ}
    (hk : k < m.length) (hi : i < m.getD k 0) (hs : s < w.getD k 0) :
    packed m w k i s < (List.zipWith (· * ·) m w).sum :=
  lt_of_lt_of_le (packed_bounds m w hlen hk hi hs).2 (pref_le_sum _ _)

end Plonky3Lean.Proofs.Word
