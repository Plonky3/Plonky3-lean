module

public import Plonky3Lean.Proofs.Field.Binary.BasisMap

@[expose] public section

/-!
# `GF(2)`-linear maps on bit patterns

`clmul::basis` stores a `GF(2)`-linear map on `n`-bit patterns as its `n` columns, and applies
it to `v` as the xor of the columns the set bits of `v` select (`lin`). `invert` inverts such a
map by Gauss-Jordan elimination; its pivots exist because the row operations keep the
determinant of the column matrix (`rowM`) nonzero.
-/

open Aeneas Aeneas.Std CoreModels Polynomial
open p3_binary_field BinaryField
open Plonky3Lean.Lib Plonky3Lean.Spec.BinaryField

namespace Plonky3Lean.Proofs.Binary

/-! ## The map -/

/-- The map with columns `c` applied to the low `k` bits of `v`. -/
def lin (c : ℕ → ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 0
  | k + 1, v => lin c k v ^^^ (if v.testBit k then c k else 0)

theorem lin_zero (c : ℕ → ℕ) : ∀ k, lin c k 0 = 0
  | 0 => rfl
  | k + 1 => by simp [lin, lin_zero c k]

theorem lin_xor (c : ℕ → ℕ) : ∀ k v w, lin c k (v ^^^ w) = lin c k v ^^^ lin c k w
  | 0, _, _ => by simp [lin]
  | k + 1, v, w => by
    simp only [lin, lin_xor c k, Nat.testBit_xor]
    apply Nat.eq_of_testBit_eq
    intro i
    cases v.testBit k <;> cases w.testBit k <;> simp only [Nat.testBit_xor, Bool.false_xor,
      Bool.xor_false, Bool.false_eq_true, ↓reduceIte, Nat.zero_testBit,
      Bool.xor_self] <;>
      cases (lin c k v).testBit i <;> cases (lin c k w).testBit i <;> cases (c k).testBit i <;> rfl

theorem lin_ite (c : ℕ → ℕ) (k : ℕ) (b : Bool) (x : ℕ) :
    lin c k (if b then x else 0) = if b then lin c k x else 0 := by
  cases b <;> simp [lin_zero]

theorem lin_congr (c : ℕ → ℕ) : ∀ k {v w : ℕ}, (∀ i < k, v.testBit i = w.testBit i) →
    lin c k v = lin c k w
  | 0, _, _, _ => rfl
  | k + 1, v, w, h => by
    simp only [lin, lin_congr c k (fun i hi => h i (by omega)), h k (by omega)]

theorem lin_lt (c : ℕ → ℕ) {b : ℕ} : ∀ k v, (∀ i < k, c i < 2 ^ b) → lin c k v < 2 ^ b
  | 0, _, _ => by simp [lin]
  | k + 1, v, h => by
    simp only [lin]
    refine Nat.xor_lt_two_pow (lin_lt c k v (fun i hi => h i (by omega))) ?_
    split
    · exact h k (by omega)
    · exact Nat.two_pow_pos b

theorem lin_two_pow (c : ℕ → ℕ) {k i : ℕ} (hi : i < k) : lin c k (2 ^ i) = c i := by
  induction k with
  | zero => omega
  | succ k ih =>
    simp only [lin, Nat.testBit_two_pow]
    by_cases hik : i = k
    · subst hik
      rw [lin_congr c i (w := 0) (fun j hj => by
        rw [Nat.testBit_two_pow, Nat.zero_testBit]; simp; omega), lin_zero]
      simp
    · rw [ih (by omega)]
      simp [hik]

/-- Applying one map after another applies the map whose columns are the images of the
columns. -/
theorem lin_lin (c d : ℕ → ℕ) (m : ℕ) : ∀ k v,
    lin c m (lin d k v) = lin (fun j => lin c m (d j)) k v
  | 0, _ => lin_zero c m
  | k + 1, v => by
    simp only [lin, lin_xor, lin_ite, lin_lin c d m k v]

/-! ## Bits -/

/-- Bit `i` of `x`, in `GF(2)`. -/
def bitZ (x i : ℕ) : ZMod 2 := if x.testBit i then 1 else 0

theorem bitZ_xor (x y i : ℕ) : bitZ (x ^^^ y) i = bitZ x i + bitZ y i := by
  unfold bitZ
  rw [Nat.testBit_xor]
  cases x.testBit i <;> cases y.testBit i <;> decide

theorem bitZ_lin (c : ℕ → ℕ) (i : ℕ) : ∀ k v,
    bitZ (lin c k v) i = ∑ j ∈ Finset.range k, bitZ v j * bitZ (c j) i
  | 0, _ => by simp [lin, bitZ]
  | k + 1, v => by
    rw [lin, bitZ_xor, bitZ_lin c i k v, Finset.sum_range_succ]
    congr 1
    unfold bitZ
    split <;> simp

/-! ## The column matrix -/

/-- The `n × n` matrix whose row `r` holds the bits of `f r`. -/
def rowM (n : ℕ) (f : ℕ → ℕ) : Matrix (Fin n) (Fin n) (ZMod 2) := fun r i => bitZ (f r) i

/-- Swapping two rows keeps the determinant nonzero. -/
theorem det_rowM_swap {n : ℕ} {f : ℕ → ℕ} {p c : ℕ} (hp : p < n) (hc : c < n)
    (hdet : (rowM n f).det ≠ 0) :
    (rowM n (fun r => if r = c then f p else if r = p then f c else f r)).det ≠ 0 := by
  have h : rowM n (fun r => if r = c then f p else if r = p then f c else f r) =
      (rowM n f).submatrix (Equiv.swap ⟨p, hp⟩ ⟨c, hc⟩) id := by
    ext r i
    simp only [rowM, Matrix.submatrix_apply, id]
    by_cases hrc : r.val = c
    · have : r = ⟨c, hc⟩ := Fin.ext hrc
      subst this
      simp
    · by_cases hrp : r.val = p
      · have : r = ⟨p, hp⟩ := Fin.ext hrp
        subst this
        simp [hrc]
      · rw [Equiv.swap_apply_of_ne_of_ne (fun e => hrp (by rw [e])) (fun e => hrc (by rw [e]))]
        simp [hrc, hrp]
  rw [h, Matrix.det_permute]
  rcases Int.units_eq_one_or (Equiv.Perm.sign (Equiv.swap (⟨p, hp⟩ : Fin n) ⟨c, hc⟩)) with
    e | e <;> rw [e] <;> simpa using hdet

/-- Adding row `p` to another row keeps the determinant. -/
theorem det_rowM_add {n : ℕ} (f : ℕ → ℕ) {p c : ℕ} (hp : p < n) (hc : c < n) (hpc : c ≠ p) :
    (rowM n (fun r => if r = c then f c ^^^ f p else f r)).det = (rowM n f).det := by
  have h : rowM n (fun r => if r = c then f c ^^^ f p else f r) =
      (rowM n f).updateRow ⟨c, hc⟩ (rowM n f ⟨c, hc⟩ + rowM n f ⟨p, hp⟩) := by
    ext r i
    by_cases hrc : r.val = c
    · have : r = ⟨c, hc⟩ := Fin.ext hrc
      subst this
      simp [rowM, bitZ_xor]
    · rw [Matrix.updateRow_ne (fun e => hrc (by rw [e]))]
      simp [rowM, hrc]
  rw [h, Matrix.det_updateRow_add_self _ (fun e => hpc (by simpa using e))]

theorem bitZ_ofBits {n : ℕ} (v : Fin n → ZMod 2) (j : Fin n) :
    bitZ (Nat.ofBits fun i => decide (v i = 1)) j = v j := by
  unfold bitZ
  rw [Nat.testBit_ofBits_lt _ _ j.isLt]
  generalize v j = x
  fin_cases x <;> rfl

/-- An injective map has a nonsingular column matrix. -/
theorem det_rowM_ne_zero {n : ℕ} {c : ℕ → ℕ} (hc : ∀ i < n, c i < 2 ^ n)
    (hinj : ∀ w < 2 ^ n, lin c n w = 0 → w = 0) : (rowM n c).det ≠ 0 := by
  intro hdet
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_vecMul_eq_zero_iff.mpr hdet
  set w := Nat.ofBits fun i => decide (v i = 1)
  have hw : lin c n w = 0 := by
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.zero_testBit]
    by_cases hi : i < n
    · have h := congrFun hv ⟨i, hi⟩
      simp only [Matrix.vecMul, dotProduct, rowM, Pi.zero_apply] at h
      have hb : bitZ (lin c n w) i = 0 := by
        rw [bitZ_lin, ← h, ← Fin.sum_univ_eq_sum_range]
        apply Finset.sum_congr rfl
        intro j _
        rw [bitZ_ofBits]
      unfold bitZ at hb
      split at hb
      · exact absurd hb (by decide)
      · simp_all
    · exact Nat.testBit_lt_two_pow (lt_of_lt_of_le (lin_lt c n w hc)
        (Nat.pow_le_pow_right (by norm_num) (by omega)))
  have h0 := hinj w (Nat.ofBits_lt_two_pow _) hw
  apply hv0
  funext j
  rw [Pi.zero_apply, ← bitZ_ofBits v j]
  show bitZ w j = 0
  rw [h0]
  simp [bitZ]

/-- A nonsingular matrix reduced on its first `p` columns has a pivot in column `p`. -/
theorem exists_pivot {n : ℕ} {f : ℕ → ℕ} (hdet : (rowM n f).det ≠ 0) {p : ℕ} (hp : p < n)
    (hred : ∀ r < n, ∀ i < p, (f r).testBit i = decide (r = i)) :
    ∃ r, p ≤ r ∧ r < n ∧ (f r).testBit p = true := by
  by_contra hno
  push Not at hno
  apply hdet
  apply Matrix.exists_mulVec_eq_zero_iff.mp
  refine ⟨fun i => if i.val < p then bitZ (f i) p else if i.val = p then 1 else 0, ?_, ?_⟩
  · intro h
    have := congrFun h ⟨p, hp⟩
    simp at this
  · funext r
    simp only [Matrix.mulVec, dotProduct, rowM, Pi.zero_apply]
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ (⟨p, hp⟩ : Fin n))]
    simp only [lt_self_iff_false, ↓reduceIte, mul_one]
    have hrest : ∀ i ∈ Finset.univ.erase (⟨p, hp⟩ : Fin n),
        bitZ (f r) i * (if i.val < p then bitZ (f i) p else if i.val = p then 1 else 0) =
          if i = r then (if r.val < p then bitZ (f r) p else 0) else 0 := by
      intro i hi
      have hip : i.val ≠ p := fun e => (Finset.mem_erase.mp hi).1 (Fin.ext e)
      by_cases hlt : i.val < p
      · simp only [hlt, ↓reduceIte]
        unfold bitZ
        rw [hred r r.isLt i hlt]
        by_cases hir : i = r
        · subst hir; simp [hlt]
        · have : (r.val = i.val) = False := propext ⟨fun e => hir (Fin.ext e.symm), False.elim⟩
          simp [this, hir]
      · simp [hlt, hip]
        intro e
        subst e
        intro h
        exact absurd h hlt
    rw [Finset.sum_congr rfl hrest]
    by_cases hrp : r.val < p
    · rw [Finset.sum_ite_eq' (Finset.univ.erase _) r]
      rw [ite_eq_left (Finset.mem_erase.mpr ⟨fun e => by rw [e] at hrp; simp at hrp,
        Finset.mem_univ _⟩)]
      simp only [hrp, ↓reduceIte]
      exact CharTwo.add_self_eq_zero _
    · simp only [hrp, ↓reduceIte, ite_self, Finset.sum_const_zero, zero_add]
      unfold bitZ
      have : (f r).testBit p = false := by simpa using hno r (by omega) r.isLt
      simp [this]

end Plonky3Lean.Proofs.Binary
