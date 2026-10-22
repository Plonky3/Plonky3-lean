/-
Copyright (c) 2026 CompPoly. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Coratger
-/
module

public import CompPoly.Fields.Binary.Tower.Impl

@[expose] public section

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

theorem toNat_add {k : ℕ} (x y : ConcreteBTField k) : (x + y).toNat = x.toNat ^^^ y.toNat :=
  BitVec.toNat_xor x.toBitVec y.toBitVec

theorem toNat_join {k : ℕ} (h : k > 0) (hi lo : ConcreteBTField (k - 1)) :
    (join h hi lo).toNat = hi.toNat <<< 2 ^ (k - 1) ||| lo.toNat := by
  show (join h hi lo).toBitVec.toNat = _
  rw [join_eq_dcast_append, ← BitVec.dcast_bitvec_toNat_eq]
  exact BitVec.toNat_append hi.toBitVec lo.toBitVec

theorem toNat_Z (k : ℕ) : (Z k).toNat = zNat k := by
  unfold Z zNat
  split_ifs with h
  · exact one_bitvec_toNat (by positivity)
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    rw [toNat_join]
    show (1#(2 ^ (j + 1 - 1))).toNat <<< 2 ^ (j + 1 - 1) ||| (BitVec.zero (2 ^ (j + 1 - 1))).toNat = _
    rw [one_bitvec_toNat (by positivity), BitVec.zero_eq, BitVec.toNat_zero, Nat.or_zero, Nat.one_shiftLeft]

theorem split_eq {k : ℕ} (a : ConcreteBTField (k + 1)) :
    split (k := k + 1) (by omega) a =
      (fromNat (k := k + 1 - 1) (a.toNat >>> 2 ^ (k + 1 - 1)),
        fromNat (k := k + 1 - 1) (a.toNat &&& (2 ^ (2 ^ (k + 1 - 1)) - 1))) :=
  (split_bitvec_eq_iff_fromNat (k := k + 1) (by omega) a _ _).mpr ⟨rfl, rfl⟩

/-- The structural product agrees with `concrete_mul`. -/
theorem toNat_concrete_mul : ∀ (k : ℕ) (a b : ConcreteBTField k),
    (concrete_mul a b).toNat = towerMul k a.toNat b.toNat
  | 0, a, b => by
    have ha := a.toNat_lt
    have hb := b.toNat_lt
    have ea : a = fromNat a.toNat := (ConcreteBTField.fromNat_toNat a).symm
    have eb : b = fromNat b.toNat := (ConcreteBTField.fromNat_toNat b).symm
    have h0 : (fromNat (k := 0) 0 : ConcreteBTField 0) = zero := rfl
    have h1 : (fromNat (k := 0) 1 : ConcreteBTField 0) = one := rfl
    rcases (by norm_num at ha; omega : a.toNat = 0 ∨ a.toNat = 1) with e1 | e1 <;>
    rcases (by norm_num at hb; omega : b.toNat = 0 ∨ b.toNat = 1) with e2 | e2 <;>
    · rw [e1] at ea; rw [e2] at eb
      rw [ea, eb]
      simp only [h0, h1, concrete_mul_zero0, concrete_mul_one0]
      rfl
  | k + 1, a, b => by
    have ih : ∀ x y : ConcreteBTField (k + 1 - 1),
        (concrete_mul x y).toNat = towerMul k x.toNat y.toNat := toNat_concrete_mul k
    rw [concrete_mul.eq_def]
    simp only [dite_eq_right (Nat.succ_ne_zero k)]
    rw [split_eq a, split_eq b]
    simp only
    rw [toNat_join]
    generalize a.toNat = A
    generalize b.toNat = B
    simp only [toNat_add, ih, toNat_Z, ConcreteBTField.toNat_fromNat]
    rw [towerMul]
    rfl

/-! ## Facts about `towerMul` -/

theorem zNat_lt (k : ℕ) : zNat k < 2 ^ (2 ^ k) := by
  unfold zNat
  split_ifs with h
  · subst h; norm_num
  · exact Nat.pow_lt_pow_right (by norm_num) (Nat.pow_lt_pow_right (by norm_num) (by omega))

/-- A product of level `k` fits in `2 ^ k` bits. -/
theorem towerMul_lt : ∀ (k : ℕ) {a b : ℕ}, a < 2 ^ (2 ^ k) → b < 2 ^ (2 ^ k) →
    towerMul k a b < 2 ^ (2 ^ k)
  | 0, a, b, ha, _ => by
    simp only [towerMul]
    exact lt_of_le_of_lt Nat.and_le_left ha
  | k + 1, a, b, _, _ => by
    have hm : ∀ x, x % 2 ^ (2 ^ k) < 2 ^ (2 ^ k) := fun x => Nat.mod_lt _ (by positivity)
    have hx : ∀ x y, x < 2 ^ (2 ^ k) → y < 2 ^ (2 ^ k) → x ^^^ y < 2 ^ (2 ^ k) :=
      fun x y hx hy => Nat.xor_lt_two_pow hx hy
    have ih : ∀ {x y : ℕ}, x < 2 ^ (2 ^ k) → y < 2 ^ (2 ^ k) → towerMul k x y < 2 ^ (2 ^ k) :=
      fun hx hy => towerMul_lt k hx hy
    have hz := zNat_lt k
    have hsq : 2 ^ 2 ^ (k + 1) = 2 ^ 2 ^ k * 2 ^ 2 ^ k := by rw [pow_succ, pow_mul, sq]
    have key : ∀ hi lo, hi < 2 ^ (2 ^ k) → lo < 2 ^ (2 ^ k) →
        hi <<< 2 ^ k ||| lo < 2 ^ (2 ^ (k + 1)) := by
      intro hi lo hhi hlo
      refine Nat.or_lt_two_pow ?_ (lt_of_lt_of_le hlo ?_)
      · rw [Nat.shiftLeft_eq, hsq]
        exact Nat.mul_lt_mul_of_pos_right hhi (by positivity)
      · rw [hsq]; exact Nat.le_mul_of_pos_left _ (by positivity)
    simp only [towerMul]
    apply key <;>
      repeat (first | exact hz | apply hx | apply ih | apply hm)

theorem towerMul_zero_left : ∀ (k b : ℕ), towerMul k 0 b = 0
  | 0, b => by simp [towerMul]
  | k + 1, b => by
    simp only [towerMul, Nat.zero_shiftRight, Nat.zero_mod, Nat.zero_and,
      towerMul_zero_left k, Nat.xor_zero, Nat.zero_shiftLeft, Nat.zero_or]

theorem towerMul_zero_right : ∀ (k a : ℕ), towerMul k a 0 = 0
  | 0, a => by simp [towerMul]
  | k + 1, a => by
    simp only [towerMul, Nat.zero_shiftRight, Nat.zero_mod, Nat.zero_and, Nat.xor_zero,
      towerMul_zero_right k, towerMul_zero_left k, Nat.zero_shiftLeft, Nat.zero_or]

/-- A number below `2 ^ (2 n)` is its high half shifted back over its low half. -/
theorem shiftRight_shiftLeft_or_mod {a n : ℕ} :
    (a >>> n) <<< n ||| a % 2 ^ n = a := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_or, Nat.testBit_shiftLeft, Nat.testBit_shiftRight, Nat.testBit_mod_two_pow]
  by_cases h : n ≤ i
  · simp [h, show ¬ i < n by omega, show n + (i - n) = i by omega]
  · simp [h, show i < n by omega]

theorem mod_two_pow_two_pow_of_lt {a k : ℕ} (ha : a < 2 ^ (2 ^ (k + 1))) :
    (a >>> 2 ^ k) % 2 ^ (2 ^ k) = a >>> 2 ^ k := by
  apply Nat.mod_eq_of_lt
  rw [Nat.shiftRight_eq_div_pow]
  apply Nat.div_lt_of_lt_mul
  rw [← pow_add, ← two_mul, ← pow_succ']
  exact ha

theorem and_sub_one_mod {a n : ℕ} : (a &&& (2 ^ n - 1)) % 2 ^ n = a % 2 ^ n := by
  rw [Nat.and_two_pow_sub_one_eq_mod, Nat.mod_mod]

/-- `1` is the identity of every level. -/
theorem towerMul_one : ∀ (k : ℕ) {a : ℕ}, a < 2 ^ (2 ^ k) → towerMul k a 1 = a
  | 0, a, ha => by
    simp only [towerMul]
    have : a = 0 ∨ a = 1 := by norm_num at ha; omega
    rcases this with rfl | rfl <;> rfl
  | k + 1, a, ha => by
    have h1 : (1 >>> 2 ^ k) % 2 ^ (2 ^ k) = 0 := by
      rw [Nat.shiftRight_eq_div_pow, Nat.div_eq_of_lt (Nat.one_lt_two_pow (by positivity))]; rfl
    have h0 : (1 &&& (2 ^ (2 ^ k) - 1)) % 2 ^ (2 ^ k) = 1 := by
      rw [and_sub_one_mod, Nat.mod_eq_of_lt (Nat.one_lt_two_pow (by positivity))]
    have hlo := towerMul_one k (a := (a &&& (2 ^ (2 ^ k) - 1)) % 2 ^ (2 ^ k)) (Nat.mod_lt _ (by positivity))
    have hx := towerMul_one k (a := (a >>> 2 ^ k) % 2 ^ (2 ^ k) ^^^ (a &&& (2 ^ (2 ^ k) - 1)) % 2 ^ (2 ^ k))
      (Nat.xor_lt_two_pow (Nat.mod_lt _ (by positivity)) (Nat.mod_lt _ (by positivity)))
    simp only [towerMul, h1, h0, towerMul_zero_right, Nat.xor_zero, Nat.zero_xor, towerMul_zero_left,
      hlo, hx]
    rw [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero, mod_two_pow_two_pow_of_lt ha, and_sub_one_mod,
      shiftRight_shiftLeft_or_mod]

/-- Multiplying by the generator `zNat (k + 1)`: `(a_0 + a_1 X) X = a_1 + (a_0 + a_1 α) X`. -/
theorem towerMul_zNat_succ (k : ℕ) {a : ℕ} :
    towerMul (k + 1) a (zNat (k + 1)) =
      ((a &&& (2 ^ (2 ^ k) - 1)) % 2 ^ (2 ^ k) ^^^
        towerMul k ((a >>> 2 ^ k) % 2 ^ (2 ^ k)) (zNat k)) <<< 2 ^ k |||
      (a >>> 2 ^ k) % 2 ^ (2 ^ k) := by
  have hz : zNat (k + 1) = 2 ^ (2 ^ k) := by simp [zNat]
  have h1 : (2 ^ (2 ^ k) >>> 2 ^ k) % 2 ^ (2 ^ k) = 1 := by
    rw [Nat.shiftRight_eq_div_pow, Nat.div_self (by positivity),
      Nat.mod_eq_of_lt (Nat.one_lt_two_pow (by positivity))]
  have h0 : (2 ^ (2 ^ k) &&& (2 ^ (2 ^ k) - 1)) % 2 ^ (2 ^ k) = 0 := by
    rw [and_sub_one_mod, Nat.mod_self]
  have hm : ∀ x, x % 2 ^ (2 ^ k) < 2 ^ (2 ^ k) := fun x => Nat.mod_lt _ (by positivity)
  simp only [towerMul, hz, h1, h0, towerMul_zero_right, Nat.xor_zero, Nat.zero_xor,
    towerMul_one k (hm _), towerMul_one k (Nat.xor_lt_two_pow (hm _) (hm _))]
  congr 2
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_xor]
  cases ((a >>> 2 ^ k) % 2 ^ 2 ^ k).testBit i <;> simp

end ConcreteBinaryTower
