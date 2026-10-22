module

public import Plonky3Lean.Proofs.Hash.Blake3.Hash

@[expose] public section

/-!
# p3-blake3: the lane digest is the BLAKE3 digest

The model's chunk windows are the specification's chunks, its plain-block chaining value is the
specification's fold over a chunk's blocks, and its split of the tree is the specification's.
-/

open Aeneas Aeneas.Std CoreModels
open Plonky3Lean.Spec.Blake3 Plonky3Lean.Lib

namespace Plonky3Lean.Proofs.Blake3

theorem cvBytes_eq (cv : List Word) (h : cv.length = 8) :
    cvBytes cv = ((cv.take 8).map bytesOfWord).flatten := by
  match cv, h with
  | [a, b, c, d, e, f, g, k], _ => rfl

theorem pow2Below_eq (f n : ℕ) (hn : 2 ≤ n) : pow2Below f n = 2 ^ min f (Nat.log 2 (n - 1)) := by
  induction f with
  | zero => simp [pow2Below]
  | succ f ih =>
    rw [pow2Below, ih]
    by_cases hf : f < Nat.log 2 (n - 1)
    · have h1 : 2 * 2 ^ f < n := by
        have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) (show f + 1 ≤ Nat.log 2 (n - 1) by omega)
        have := Nat.pow_log_le_self 2 (show n - 1 ≠ 0 by omega)
        rw [pow_succ] at *; omega
      rw [Nat.min_eq_left hf.le, ite_eq_left_of_eq_true _ _ (eq_true h1), Nat.min_eq_left (by omega), pow_succ]
      ring
    · have hm : min f (Nat.log 2 (n - 1)) = Nat.log 2 (n - 1) := Nat.min_eq_right (by omega)
      have h1 : ¬ 2 * 2 ^ Nat.log 2 (n - 1) < n := by
        have := Nat.lt_pow_succ_log_self (show 1 < 2 by norm_num) (n - 1)
        rw [pow_succ] at this; omega
      rw [hm, ite_eq_right_of_eq_false _ _ (eq_false h1), Nat.min_eq_right (by omega)]

theorem leftChunks_eq (c : ℕ) (hc : 2 ≤ c) : leftChunks c = pow2Below c c := by
  rw [pow2Below_eq c c hc, Nat.min_eq_right]
  · rfl
  · have := Nat.log_le_self 2 (c - 1); omega

theorem ceil_step (m k : ℕ) (hk : 0 < k) (hm : 0 < m) :
    (m + k - 1) / k = (m - k + k - 1) / k + 1 := by
  by_cases h : k ≤ m
  · rw [show m + k - 1 = (m - k + k - 1) + k by omega, Nat.add_div_right _ hk]
  · rw [show m - k = 0 by omega, Nat.zero_add, Nat.div_eq_of_lt (show k - 1 < k by omega)]
    have h1 : (m + k - 1) / k < 2 := (Nat.div_lt_iff_lt_mul hk).2 (by omega)
    have h2 : 1 ≤ (m + k - 1) / k := (Nat.le_div_iff_mul_le hk).2 (by omega)
    omega

theorem piecesAux_spec (k : ℕ) (hk : 0 < k) (n : ℕ) (l : List (BitVec 8)) (hn : (l.length + k - 1) / k ≤ n) :
    (piecesAux k n l).length = (l.length + k - 1) / k ∧
      ∀ i < (l.length + k - 1) / k, (piecesAux k n l).getD i [] = (l.drop (k * i)).take k := by
  induction n generalizing l with
  | zero =>
    have h0 : (l.length + k - 1) / k = 0 := Nat.le_zero.mp hn
    have hl : l.length = 0 := by
      rcases Nat.div_eq_zero_iff.1 h0 with h | h <;> omega
    rw [h0]; simp [piecesAux]
  | succ n ih =>
    by_cases hl : l = []
    · subst hl
      simp [piecesAux, hk]
    · have hm : 0 < l.length := List.length_pos_iff.2 hl
      have hs := ceil_step l.length k hk hm
      have hd : (l.drop k).length = l.length - k := List.length_drop ..
      obtain ⟨ih1, ih2⟩ := ih (l.drop k) (by rw [hd]; omega)
      rw [hd] at ih1 ih2
      simp only [piecesAux, List.isEmpty_iff, hl, ite_false, List.length_cons, ih1, hs, true_and]
      intro i hi
      rcases i with _ | i
      · simp
      · simp only [List.getD_cons_succ, ih2 i (by omega), List.drop_drop]
        congr 2
        ring

theorem pieces_spec (k : ℕ) (hk : 0 < k) (l : List (BitVec 8)) :
    (pieces k l).length = (if l = [] then 1 else (l.length + k - 1) / k) ∧
      ∀ i < (pieces k l).length, (pieces k l).getD i [] = (l.drop (k * i)).take k := by
  unfold pieces
  by_cases hl : l = []
  · subst hl; simp
  · have hm : 0 < l.length := List.length_pos_iff.2 hl
    have hle : (l.length + k - 1) / k ≤ l.length := by
      have e1 : l.length - 1 ≤ (l.length - 1) * k := Nat.le_mul_of_pos_right _ hk
      have e2 : l.length * k = (l.length - 1) * k + k := by
        rw [Nat.sub_one_mul, Nat.sub_add_cancel (Nat.le_mul_of_pos_left _ hm)]
      apply Nat.div_le_of_le_mul
      rw [Nat.mul_comm]; omega
    obtain ⟨h1, h2⟩ := piecesAux_spec k hk l.length l hle
    simp only [List.isEmpty_iff, hl, ite_false, h1]
    exact ⟨trivial, h2⟩

theorem getD_drop' {α : Type} (l : List α) (a p : ℕ) (d : α) : (l.drop a).getD p d = l.getD (a + p) d := by
  simp [List.getD_eq_getElem?_getD]

theorem getD_take' {α : Type} (l : List α) (n p : ℕ) (d : α) :
    (l.take n).getD p d = if p < n then l.getD p d else d := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_take]
  split_ifs <;> rfl

theorem blockWords_congr (x y : List (BitVec 8)) (h : ∀ p < 64, x.getD p 0 = y.getD p 0) :
    blockWords x = blockWords y := by
  unfold blockWords
  apply List.map_congr_left
  intro i hi
  have hi' := List.mem_range.1 hi
  rw [h _ (by omega), h _ (by omega), h _ (by omega), h _ (by omega)]

/-- The bytes of chunk `idx` of the `len`-byte message at byte `s` of `B`. -/
def chunkAt (B : List (BitVec 8)) (s len idx : ℕ) : List (BitVec 8) :=
  ((((B.drop s).take len).drop (1024 * idx)).take 1024)

theorem length_chunkAt (B : List (BitVec 8)) (s len idx : ℕ) (hB : s + len ≤ B.length) :
    (chunkAt B s len idx).length = min len (idx * 1024 + 1024) - idx * 1024 := by
  simp [chunkAt]; omega

theorem block_getD (B : List (BitVec 8)) (s len idx i p : ℕ) :
    (((chunkAt B s len idx).drop (64 * i)).take 64).getD p 0 =
      if p < 64 ∧ 64 * i + p < 1024 ∧ 1024 * idx + (64 * i + p) < len then
        B.getD (s + (1024 * idx + (64 * i + p))) 0 else 0 := by
  simp only [chunkAt, getD_take', getD_drop']
  by_cases h1 : p < 64 <;> by_cases h2 : 64 * i + p < 1024 <;>
    by_cases h3 : 1024 * idx + (64 * i + p) < len <;> simp [h1, h2, h3]

theorem window_block (B : List (BitVec 8)) (s len idx i k : ℕ) (hk : k ≤ 64)
    (hlo : 64 * i + k ≤ 1024) (hhi : idx * 1024 + 64 * i + k ≤ len)
    (hfull : k < 64 → idx * 1024 + 64 * i + k = len ∨ 64 * i + k = 1024) :
    blockWords (window B (s + (idx * 1024 + 64 * i)) k) =
      blockWords (((chunkAt B s len idx).drop (64 * i)).take 64) := by
  apply blockWords_congr
  intro p hp
  rw [window_getD _ _ _ _ hp, block_getD]
  by_cases h : p < k
  · rw [ite_eq_left_of_eq_true _ _ (eq_true h), ite_eq_left_of_eq_true _ _ (eq_true ⟨hp, by omega, by omega⟩)]
    congr 1; ring
  · rw [ite_eq_right_of_eq_false _ _ (eq_false h), ite_eq_right_of_eq_false _ _ (eq_false (by
      rintro ⟨-, h2, h3⟩
      have := hfull (by omega)
      omega))]

end Plonky3Lean.Proofs.Blake3
