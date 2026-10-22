/-
Copyright (c) 2026 CompPoly. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Coratger
-/
import CompPoly.Fields.Binary.Tower.Impl

/-!
# The tower product on natural numbers

`concrete_mul` is defined by well-founded recursion, which the kernel does not unfold.

`towerMul` computes the same product by structural recursion on the level, with `Nat`
operations only, so the kernel evaluates it directly.

`toNat_concrete_mul` states that the two agree, for every level and every pair of elements.
-/

namespace ConcreteBinaryTower

/-- `Z k`, the generator of level `k`, as a natural number. -/
def zNat (k : ℕ) : ℕ := if k = 0 then 1 else 2 ^ (2 ^ (k - 1))

/-- The product of level `k` on natural numbers, in the steps `concrete_mul` takes. -/
def towerMul : ℕ → ℕ → ℕ → ℕ
  | 0, a, b => a &&& b
  | k + 1, a, b =>
    let m := 2 ^ (2 ^ k)
    let a₁ := (a >>> 2 ^ k) % m
    let a₀ := (a &&& (m - 1)) % m
    let b₁ := (b >>> 2 ^ k) % m
    let b₀ := (b &&& (m - 1)) % m
    let z₂ := towerMul k a₁ b₁
    let lo := towerMul k a₀ b₀ ^^^ z₂
    let hi := (towerMul k (a₁ ^^^ a₀) (b₁ ^^^ b₀) ^^^ lo) ^^^ towerMul k z₂ (zNat k)
    hi <<< 2 ^ k ||| lo

theorem toNat_fromNat {k : ℕ} (n : ℕ) : (fromNat (k := k) n).toNat = n % 2 ^ (2 ^ k) :=
  BitVec.toNat_ofNat _ _

theorem toNat_add {k : ℕ} (x y : ConcreteBTField k) : (x + y).toNat = x.toNat ^^^ y.toNat :=
  BitVec.toNat_xor x y

theorem toNat_join {k : ℕ} (h : k > 0) (hi lo : ConcreteBTField (k - 1)) :
    (join h hi lo).toNat = hi.toNat <<< 2 ^ (k - 1) ||| lo.toNat := by
  rw [join_eq_dcast_append, ← BitVec.dcast_bitvec_toNat_eq]
  exact BitVec.toNat_append hi lo

theorem toNat_Z (k : ℕ) : (Z k).toNat = zNat k := by
  unfold Z zNat
  split_ifs with h
  · exact one_bitvec_toNat (by positivity)
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    rw [toNat_join]
    show (1#(2 ^ (j + 1 - 1))).toNat <<< 2 ^ (j + 1 - 1) ||| (0#(2 ^ (j + 1 - 1))).toNat = _
    rw [one_bitvec_toNat (by positivity), BitVec.toNat_zero, Nat.or_zero, Nat.one_shiftLeft]

theorem split_eq {k : ℕ} (a : ConcreteBTField (k + 1)) :
    split (k := k + 1) (by omega) a =
      (fromNat (k := k + 1 - 1) (a.toNat >>> 2 ^ (k + 1 - 1)),
        fromNat (k := k + 1 - 1) (a.toNat &&& (2 ^ (2 ^ (k + 1 - 1)) - 1))) :=
  (split_bitvec_eq_iff_fromNat (k := k + 1) (by omega) a _ _).mpr ⟨rfl, rfl⟩

/-- The structural product agrees with `concrete_mul`. -/
theorem toNat_concrete_mul : ∀ (k : ℕ) (a b : ConcreteBTField k),
    (concrete_mul a b).toNat = towerMul k a.toNat b.toNat
  | 0, a, b => by
    have ha : a.toNat < 2 := a.isLt
    have hb : b.toNat < 2 := b.isLt
    have hz : (zero (k := 0)).toNat = 0 := rfl
    have ho : (one (k := 0)).toNat = 1 := rfl
    rw [concrete_mul.eq_def]
    simp only [dif_pos]
    rw [towerMul]
    rcases (by omega : a.toNat = 0 ∨ a.toNat = 1) with h1 | h1 <;>
    rcases (by omega : b.toNat = 0 ∨ b.toNat = 1) with h2 | h2 <;>
    · have ea : (a : BitVec (2 ^ 0)) = BitVec.ofNat (2 ^ 0) a.toNat := by
        rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
      have eb : (b : BitVec (2 ^ 0)) = BitVec.ofNat (2 ^ 0) b.toNat := by
        rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
      rw [h1] at ea; rw [h2] at eb
      subst ea eb
      decide
  | k + 1, a, b => by
    have ih : ∀ x y : ConcreteBTField (k + 1 - 1),
        (concrete_mul x y).toNat = towerMul k x.toNat y.toNat := toNat_concrete_mul k
    rw [concrete_mul.eq_def]
    simp only [dif_neg (Nat.succ_ne_zero k)]
    rw [split_eq a, split_eq b]
    simp only
    rw [toNat_join]
    generalize BitVec.toNat a = A
    generalize BitVec.toNat b = B
    simp only [toNat_add, ih, toNat_Z, toNat_fromNat]
    rw [towerMul]
    rfl

end ConcreteBinaryTower
