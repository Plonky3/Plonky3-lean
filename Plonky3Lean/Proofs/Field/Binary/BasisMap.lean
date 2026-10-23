module

public import Plonky3Lean.Proofs.Field.Binary.Basis
public import Plonky3Lean.Proofs.Field.Binary.ExtensionMul

@[expose] public section

/-!
# Mapping the tower into another field

Given images `ξ_k` in a ring `F` of characteristic 2, `towerMap ξ k` sends level `k` of the tower
to `F` coordinate by coordinate: `lo + hi X ↦ N(lo) + N(hi) ξ_k`. When every `ξ_k` satisfies the
tower's relation `ξ_k^2 = ξ_(k-1) ξ_k + 1` (with `ξ_(-1) = 1`), it is a ring homomorphism
(`towerMap_mul`), as `clmul::basis` claims.
-/

open ConcreteBinaryTower ConcreteBinaryTower.Coordinates

namespace Plonky3Lean.Proofs.Binary

variable {F : Type} [CommRing F] [CharP F 2]

/-! ## Level `0` -/

theorem level0_cases (x : ConcreteBTField 0) : x = 0 ∨ x = 1 := by
  have h := x.toNat_lt
  have : x.toNat = 0 ∨ x.toNat = 1 := by simp at h; omega
  rcases this with h0 | h1
  · left; apply ConcreteBTField.toNat_injective; rw [h0]; rfl
  · right; apply ConcreteBTField.toNat_injective; rw [h1]; rfl

theorem level0_one_ne_zero : (1 : ConcreteBTField 0) ≠ 0 := one_ne_zero

theorem level0_one_add_one : (1 : ConcreteBTField 0) + 1 = 0 := CharTwo.add_self_eq_zero 1

theorem level0_Z : Z 0 = 1 := by
  apply ConcreteBTField.toNat_injective
  rfl

/-! ## The map -/

/-- The image of `Z k`, the generator of level `k`, under `towerMap`: `ξ_(k-1)`, and `1` at
level `0`. -/
def prevGen (ξ : ℕ → F) : ℕ → F
  | 0 => 1
  | k + 1 => ξ k

/-- Level `k` mapped into `F`, coordinate by coordinate. -/
noncomputable def towerMap (ξ : ℕ → F) : (k : ℕ) → ConcreteBTField k → F
  | 0, x => if x = 0 then 0 else 1
  | k + 1, x => towerMap ξ k (low k x) + towerMap ξ k (high k x) * ξ k

omit [CharP F 2] in
theorem towerMap_succ (ξ : ℕ → F) (k : ℕ) (lo hi : ConcreteBTField k) :
    towerMap ξ (k + 1) (joinSucc k lo hi) = towerMap ξ k lo + towerMap ξ k hi * ξ k := by
  rw [towerMap, low_joinSucc, high_joinSucc]

omit [CharP F 2] in
theorem towerMap_zero (ξ : ℕ → F) : ∀ k, towerMap ξ k 0 = 0
  | 0 => by simp [towerMap]
  | k + 1 => by
    rw [show (0 : ConcreteBTField (k + 1)) = joinSucc k 0 0 by
      rw [joinSucc_eq_map_mul_add, map_zero]; simp, towerMap_succ, towerMap_zero ξ k]
    simp

omit [CharP F 2] in
theorem towerMap_one (ξ : ℕ → F) : ∀ k, towerMap ξ k 1 = 1
  | 0 => by simp [towerMap]
  | k + 1 => by
    rw [show (1 : ConcreteBTField (k + 1)) = joinSucc k 1 0 by
      rw [joinSucc_eq_map_mul_add, map_zero, map_one]; simp, towerMap_succ,
      towerMap_one ξ k, towerMap_zero]
    simp

omit [CharP F 2] in
theorem towerMap_Z (ξ : ℕ → F) : ∀ k, towerMap ξ k (Z k) = prevGen ξ k
  | 0 => by rw [level0_Z, towerMap_one]; rfl
  | k + 1 => by
    rw [Z_succ_eq_joinSucc, towerMap_succ, towerMap_zero, towerMap_one]
    simp [prevGen]

theorem towerMap_add (ξ : ℕ → F) : ∀ k (x y : ConcreteBTField k),
    towerMap ξ k (x + y) = towerMap ξ k x + towerMap ξ k y
  | 0, x, y => by
    rcases level0_cases x with rfl | rfl <;> rcases level0_cases y with rfl | rfl <;>
      simp [towerMap, CharTwo.add_self_eq_zero]
  | k + 1, x, y => by
    rw [towerMap, towerMap, towerMap, low_add, high_add, towerMap_add ξ k, towerMap_add ξ k]
    ring

/-- `towerMap` is multiplicative when every image satisfies the tower's relation. -/
theorem towerMap_mul (ξ : ℕ → F) (hrel : ∀ k, ξ k * ξ k = prevGen ξ k * ξ k + 1) :
    ∀ k (x y : ConcreteBTField k), towerMap ξ k (x * y) = towerMap ξ k x * towerMap ξ k y
  | 0, x, y => by
    rcases level0_cases x with rfl | rfl <;> rcases level0_cases y with rfl | rfl <;>
      simp [towerMap]
  | k + 1, x, y => by
    conv_lhs => rw [← joinSucc_low_high k x, ← joinSucc_low_high k y, joinSucc_mul_joinSucc]
    rw [towerMap_succ, towerMap, towerMap]
    simp only [towerMap_add, towerMap_mul ξ hrel k, towerMap_Z]
    linear_combination (towerMap ξ k (high k x) * towerMap ξ k (high k y)) * hrel k +
      (towerMap ξ k (high k x) * towerMap ξ k (high k y) * (1 + prevGen ξ k * ξ k - ξ k ^ 2)) *
        (CharTwo.two_eq_zero : (2 : F) = 0)

/-- `towerMap`, as a ring homomorphism. -/
noncomputable def towerHom (ξ : ℕ → F) (hrel : ∀ k, ξ k * ξ k = prevGen ξ k * ξ k + 1) (k : ℕ) :
    ConcreteBTField k →+* F where
  toFun := towerMap ξ k
  map_one' := towerMap_one ξ k
  map_mul' := towerMap_mul ξ hrel k
  map_zero' := towerMap_zero ξ k
  map_add' := towerMap_add ξ k

/-! ## In coordinates -/

/-- The image of the tower basis element with bit pattern `j`: the product of the `ξ_i` over the
set bits `i < K` of `j`. -/
noncomputable def colV (ξ : ℕ → F) (K j : ℕ) : F :=
  ∏ i ∈ Finset.range K, if j.testBit i then ξ i else 1

omit [CharP F 2] in
theorem colV_high (ξ : ℕ → F) (k j : ℕ) :
    colV ξ k (2 ^ k + j) = colV ξ k j := by
  unfold colV
  apply Finset.prod_congr rfl
  intro i hi
  rw [Finset.mem_range] at hi
  rw [Nat.testBit_two_pow_add_gt hi]

omit [CharP F 2] in
theorem colV_succ (ξ : ℕ → F) (k j : ℕ) :
    colV ξ (k + 1) j = colV ξ k j * (if j.testBit k then ξ k else 1) := by
  unfold colV
  rw [Finset.prod_range_succ]

omit [CharP F 2] in
/-- `towerMap` in coordinates: the sum of the columns the set bits select. -/
theorem towerMap_fromNat (ξ : ℕ → F) : ∀ (k : ℕ) {n : ℕ}, n < 2 ^ 2 ^ k →
    towerMap ξ k (fromNat n) = ∑ j ∈ Finset.range (2 ^ k), if n.testBit j then colV ξ k j else 0
  | 0, n, hn => by
    have : n = 0 ∨ n = 1 := by simp at hn; omega
    rcases this with rfl | rfl
    · have h0 : (fromNat 0 : ConcreteBTField 0) = 0 := ConcreteBTField.toNat_injective (by rfl)
      simp [towerMap, h0]
    · have h1 : (fromNat 1 : ConcreteBTField 0) = 1 := ConcreteBTField.toNat_injective (by rfl)
      simp [towerMap, h1, colV, Finset.filter_singleton]
  | k + 1, n, hn => by
    rw [fromNat_eq_joinSucc hn, towerMap_succ, towerMap_fromNat ξ k (Nat.mod_lt _ (by positivity)),
      towerMap_fromNat ξ k (shiftRight_lt_of_lt hn), pow_succ, mul_two, Finset.sum_range_add,
      Finset.sum_mul]
    congr 1
    · apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.mem_range] at hj
      have hjk : j.testBit k = false := Nat.testBit_lt_two_pow hj
      rw [colV_succ, Nat.testBit_mod_two_pow, hjk]
      simp [hj]
    · apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.mem_range] at hj
      have hjk : j.testBit k = false := Nat.testBit_lt_two_pow hj
      rw [Nat.testBit_shiftRight, colV_succ, colV_high ξ k j, Nat.testBit_two_pow_add_eq, hjk]
      split_ifs <;> simp_all

end Plonky3Lean.Proofs.Binary
