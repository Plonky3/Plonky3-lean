module

public import Plonky3Lean.Proofs.KeccakAir.Words

@[expose] public section

/-!
# A trace of bits packed 64 rows to a word

A packed trace keeps the width of the trace.

Each of its rows holds 64 consecutive rows of the trace, one per bit.

```text
    packed row w, column j:   bit k  =  [cell (64 w + k, j) = 1]
```

The bits past the height of the trace are zero.
-/

namespace Plonky3Lean.Proofs.Air

open p3_air.air.mirror
open Plonky3Lean.Proofs.KeccakAir (bitsum bitsum_lt bitsum_testBit)
open Plonky3Lean.Proofs.Keccak (getD_flatMap_uniform)

/-- The 64-bit word whose bit `k` is `p k`. -/
def wordOf (p : ℕ → Bool) : BitVec 64 := BitVec.ofNat 64 (bitsum p 64)

theorem wordOf_getLsbD (p : ℕ → Bool) (k : ℕ) : (wordOf p).getLsbD k = (decide (k < 64) && p k) := by
  rw [wordOf, BitVec.getLsbD, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (bitsum_lt _ _), bitsum_testBit]

/-- A word is the word of its bits. -/
theorem eq_wordOf {x : BitVec 64} {p : ℕ → Bool} (h : ∀ k < 64, x.getLsbD k = p k) : x = wordOf p :=
  BitVec.eq_of_getLsbD_eq fun k hk => by rw [wordOf_getLsbD, h k hk]; simp [hk]

theorem wordOf_congr {p q : ℕ → Bool} (h : ∀ k < 64, p k = q k) : wordOf p = wordOf q := by
  rw [wordOf, wordOf, Plonky3Lean.Proofs.KeccakAir.bitsum_congr h]

/-- The words of a packed trace of width `W` and height `n`, given the bit of each cell. -/
def packRows (W n : ℕ) (bit : ℕ → ℕ → Bool) : List (BitVec 64) :=
  (List.range ((n + 63) / 64)).flatMap fun w => (List.range W).map fun j =>
    wordOf fun k => decide (64 * w + k < n) && bit (64 * w + k) j

/-- The packing of a matrix: bit `k` of word `(w, j)` says whether cell `(64 w + k, j)` is 1. -/
def packMat {F : Type _} [One F] [DecidableEq F] (M : Mat F) : Mat (BitVec 64) :=
  ⟨M.width, packRows M.width M.height fun r c => decide (M.get r c = some 1)⟩

theorem length_packRows (W n : ℕ) (bit : ℕ → ℕ → Bool) :
    (packRows W n bit).length = W * ((n + 63) / 64) := by
  simp [packRows, List.length_flatMap, Nat.mul_comm]

/-- Word `(w, j)` of a packed trace holds column `j` of rows `64 w` to `64 w + 63`. -/
theorem packRows_getD (W n : ℕ) (bit : ℕ → ℕ → Bool) {w j : ℕ} (hw : w < (n + 63) / 64) (hj : j < W) :
    (packRows W n bit).getD (w * W + j) 0 =
      wordOf fun k => decide (64 * w + k < n) && bit (64 * w + k) j := by
  have hk : w * W + j < W * (List.range ((n + 63) / 64)).length := by
    rw [List.length_range]
    have := Nat.mul_le_mul_right W (Nat.succ_le_of_lt hw)
    rw [Nat.succ_mul] at this
    rw [Nat.mul_comm W]; omega
  have hW : 0 < W := by omega
  rw [packRows, getD_flatMap_uniform _ _ (fun _ => by simp) _ _ 0 hk,
    show (w * W + j) / W = w by rw [Nat.mul_comm, Nat.mul_add_div hW, Nat.div_eq_of_lt hj, add_zero],
    show (w * W + j) % W = j by rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hj]]
  simp [List.getD_eq_getElem?_getD, hw, hj]

/-- The words depend only on the bits of the cells inside the trace. -/
theorem packRows_congr {W n : ℕ} {bit bit' : ℕ → ℕ → Bool} (h : ∀ r < n, ∀ c < W, bit r c = bit' r c) :
    packRows W n bit = packRows W n bit' := by
  refine List.flatMap_congr fun w _ => List.map_congr_left fun j hj => ?_
  congr 1
  funext k
  by_cases hr : 64 * w + k < n
  · simp [hr, h _ hr j (by simpa using hj)]
  · simp [hr]

/-- The packing of the trace whose rows are the given rows' cells, each row `W > 0` cells long. -/
theorem packMat_flatMap {F R : Type} [Zero F] [One F] [DecidableEq F] {W : ℕ} (hW : 0 < W)
    (rows : List R) (cells : R → List F) (hc : ∀ r, (cells r).length = W) (d : R) :
    packMat (⟨W, rows.flatMap cells⟩ : Mat F) =
      ⟨W, packRows W rows.length fun r c => decide ((cells (rows.getD r d)).getD c 0 = 1)⟩ := by
  have hlen : (rows.flatMap cells).length = W * rows.length := by
    simp [List.length_flatMap, hc, Nat.mul_comm]
  have hh : (⟨W, rows.flatMap cells⟩ : Mat F).height = rows.length := by
    simp only [Mat.height, hW.ne', ↓reduceIte, hlen]
    exact Nat.mul_div_cancel_left _ hW
  rw [packMat, hh, Mat.mk.injEq]
  refine ⟨rfl, ?_⟩
  refine packRows_congr fun r hr c hc' => ?_
  change c < W at hc'
  have hk : r * W + c < W * rows.length := by
    have := Nat.mul_le_mul_right W (Nat.succ_le_of_lt hr)
    rw [Nat.succ_mul] at this
    rw [Nat.mul_comm W]; omega
  simp only [Mat.get, hh, hr, hc', and_self, ↓reduceIte]
  rw [List.getElem?_eq_getElem (by omega), ← List.getD_eq_getElem _ 0 (by omega),
    getD_flatMap_uniform _ _ hc _ _ d hk,
    show (r * W + c) / W = r by rw [Nat.mul_comm, Nat.mul_add_div hW, Nat.div_eq_of_lt hc', add_zero],
    show (r * W + c) % W = c by rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hc']]
  simp

end Plonky3Lean.Proofs.Air
