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
open p3_binary_field BinaryField

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

/-- `towerMap` is multiplicative on level `k` when the images below `k` satisfy the tower's
relation. -/
theorem towerMap_mul (ξ : ℕ → F) : ∀ k, (∀ j < k, ξ j * ξ j = prevGen ξ j * ξ j + 1) →
    ∀ x y : ConcreteBTField k, towerMap ξ k (x * y) = towerMap ξ k x * towerMap ξ k y
  | 0, _, x, y => by
    rcases level0_cases x with rfl | rfl <;> rcases level0_cases y with rfl | rfl <;>
      simp [towerMap]
  | k + 1, hrel, x, y => by
    have ih := towerMap_mul ξ k (fun j hj => hrel j (by omega))
    have hk := hrel k (by omega)
    conv_lhs => rw [← joinSucc_low_high k x, ← joinSucc_low_high k y, joinSucc_mul_joinSucc]
    rw [towerMap_succ, towerMap, towerMap]
    simp only [towerMap_add, ih, towerMap_Z]
    linear_combination (towerMap ξ k (high k x) * towerMap ξ k (high k y)) * hk +
      (towerMap ξ k (high k x) * towerMap ξ k (high k y) * (1 + prevGen ξ k * ξ k - ξ k ^ 2)) *
        (CharTwo.two_eq_zero : (2 : F) = 0)

/-- `towerMap`, as a ring homomorphism. -/
noncomputable def towerHom (ξ : ℕ → F) (k : ℕ)
    (hrel : ∀ j < k, ξ j * ξ j = prevGen ξ j * ξ j + 1) : ConcreteBTField k →+* F where
  toFun := towerMap ξ k
  map_one' := towerMap_one ξ k
  map_mul' := towerMap_mul ξ k hrel
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

omit [CharP F 2] in
/-- Clearing a set bit `t` of `j` removes the factor `ξ_t`. -/
theorem colV_clear (ξ : ℕ → F) {K j t : ℕ} (ht : t < K) (hjt : j.testBit t = true) :
    colV ξ K j = colV ξ K (j ^^^ 2 ^ t) * ξ t := by
  unfold colV
  have hm : t ∈ Finset.range K := Finset.mem_range.mpr ht
  rw [← Finset.mul_prod_erase _ _ hm, ← Finset.mul_prod_erase _ (fun i =>
    if (j ^^^ 2 ^ t).testBit i then ξ i else 1) hm]
  have hx : (j ^^^ 2 ^ t).testBit t = false := by
    rw [Nat.testBit_xor, Nat.testBit_two_pow_self, hjt]; rfl
  simp only [hjt, ↓reduceIte, hx, Bool.false_eq_true, one_mul]
  rw [mul_comm]
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  have hit : i ≠ t := Finset.ne_of_mem_erase hi
  rw [Nat.testBit_xor, Nat.testBit_two_pow]
  simp [Ne.symm hit]

/-! ## `columns` -/

open Aeneas Aeneas.Std CoreModels Polynomial in
/-- Entry `j` of an array of 128-bit values, as a natural number. -/
def aval (a : Std.Array Std.U128 128#usize) (j : ℕ) : ℕ := (a.val.getD j 0#u128).val

open Aeneas Aeneas.Std CoreModels Polynomial in
/-- The images `ξ_i` a slice of generator images stands for, in `GF(2)[x] / (x^n + tail)`. -/
noncomputable def xiOf (n tail : ℕ) (xi : Slice Std.U128) (i : ℕ) : AdjoinRoot (modPoly n tail) :=
  AdjoinRoot.mk (modPoly n tail) (natPoly (xi.val.getD i 0#u128).val)

open Aeneas Aeneas.Std CoreModels Polynomial in
theorem aval_set (a : Std.Array Std.U128 128#usize) (u : Std.Usize) (x : Std.U128)
    (hu : u.val < 128) (j : ℕ) :
    aval (a.set u x) j = if j = u.val then x.val else aval a j := by
  unfold aval
  rw [Std.Array.set_val_eq]
  by_cases h : j = u.val
  · subst h
    rw [ite_eq_left rfl, List.getD_eq_getElem?_getD, List.getElem?_set_self (by simpa using hu)]
    rfl
  · rw [ite_eq_right h, List.getD_eq_getElem?_getD, List.getElem?_set_ne (Ne.symm h),
      ← List.getD_eq_getElem?_getD]

open Aeneas Aeneas.Std CoreModels Polynomial in
theorem columns_loop_spec (bits : Std.Usize) (K : ℕ) (hK : bits.val = 2 ^ K) (hK1 : 1 ≤ K)
    (hK7 : K ≤ 7) (tail : Std.U128) (ht : tail.val < 2 ^ bits.val) (xi : Slice Std.U128)
    (hxi : xi.length = K) (hxiv : ∀ i < K, (xi.val.getD i 0#u128).val < 2 ^ bits.val)
    (cols : Std.Array Std.U128 128#usize) (j : Std.Usize) (hj1 : 1 ≤ j.val) (hj : j.val ≤ bits.val)
    (hdone : ∀ j' < j.val, aval cols j' < 2 ^ bits.val ∧
      AdjoinRoot.mk (modPoly bits.val tail.val) (natPoly (aval cols j')) =
        colV (xiOf bits.val tail.val xi) K j') :
    clmul.basis.columns_loop bits tail xi cols j ⦃ c => ∀ j' < bits.val,
      aval c j' < 2 ^ bits.val ∧
      AdjoinRoot.mk (modPoly bits.val tail.val) (natPoly (aval c j')) =
        colV (xiOf bits.val tail.val xi) K j' ⦄ := by
  unfold clmul.basis.columns_loop
  refine loop.spec_decr_nat (fun p => bits.val - p.2.val)
    (fun p => 1 ≤ p.2.val ∧ p.2.val ≤ bits.val ∧ ∀ j' < p.2.val, aval p.1 j' < 2 ^ bits.val ∧
      AdjoinRoot.mk (modPoly bits.val tail.val) (natPoly (aval p.1 j')) =
        colV (xiOf bits.val tail.val xi) K j') _ _ _ ?_ ⟨hj1, hj, hdone⟩
  rintro ⟨cs, n⟩ ⟨hn1, hn, hd⟩
  dsimp only at hn1 hn hd ⊢
  unfold clmul.basis.columns_loop.body
  have h128 : bits.val ≤ 128 := by
    rw [hK]; exact le_trans (Nat.pow_le_pow_right (by norm_num) hK7) (by norm_num)
  step*
  case h2 =>
    have : ¬ n.val < bits.val := fun h => ‹¬n < bits› (by scalar_tac)
    exact fun j' hj' => hd j' (by omega)
  have hnb : n.val < bits.val := by scalar_tac
  have hn0 : n.val ≠ 0 := by omega
  have hnb2 : n.val < 2 ^ System.Platform.numBits := by
    have := n.hBounds; simpa [UScalarTy.numBits] using this
  obtain ⟨t, hfind, htn, htb, hlow⟩ := find_lowest_bit hn0 hnb2
  have htK : t < K := by
    by_contra h
    have hlt : n.val < 2 ^ t := by
      have : 2 ^ K ≤ 2 ^ t := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    rw [Nat.testBit_lt_two_pow hlt] at htb
    exact absurd htb (by simp)
  have hnum := System.Platform.numBits_eq
  have hts : 2 ^ t < Usize.size := by
    rw [Usize.size_def]
    exact Nat.pow_lt_pow_right (by norm_num) (by simpa [Usize.numBits] using htn)
  have hx : n.val ^^^ 2 ^ t < n.val := by
    rw [← and_sub_one_eq_xor htb hlow]
    exact lt_of_le_of_lt Nat.and_le_right (by omega)
  have hfind' : List.find? (fun i => (n.val).testBit i) (List.range UScalarTy.Usize.numBits) =
      some t := by simpa [UScalarTy.numBits] using hfind
  simp only [core.num.Usize.trailing_zeros, hfind', Option.getD_some]
  have hcast : (UScalar.cast UScalarTy.Usize (⟨BitVec.ofNat 32 t⟩ : Std.U32)).val = t := by
    rw [UScalar.cast_val_eq]
    show (BitVec.ofNat 32 t).toNat % _ = t
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show t < 2 ^ 32 by omega)]
    apply Nat.mod_eq_of_lt
    simp only [UScalarTy.numBits]
    rcases hnum with e | e <;> rw [e] <;> omega
  step*
  all_goals have hlowv : low.val = t := by rw [low_post, hcast]
  all_goals have hi1 : i1.val = 2 ^ t := by rw [i1_post, hlowv, Nat.one_shiftLeft, Nat.mod_eq_of_lt hts]
  all_goals have hi2 : i2.val = n.val ^^^ 2 ^ t := by rw [i2_post, UScalar.val_xor, hi1]
  case h_fail => rw [hi2]; scalar_tac
  have hi3 : i3.val = aval cs (n.val ^^^ 2 ^ t) := by
    rw [i3_post1, ← hi2, aval, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem]; rfl
  have hi4 : i4.val = (xi.val.getD t 0#u128).val := by
    rw [i4_post1, ← hlowv, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem]; rfl
  obtain ⟨hb3, he3⟩ := hd (n.val ^^^ 2 ^ t) hx
  rw [← hi3] at hb3 he3
  have hb4 := hxiv t htK
  rw [← hi4] at hb4
  apply WP.spec_bind (poly_mul_spec i3 i4 tail bits (by omega) h128 hb3 hb4 ht)
  rintro i5 ⟨hb5, he5⟩
  step*
  refine ⟨by scalar_tac, by scalar_tac, ?_, by scalar_tac⟩
  intro j' hj'
  have hn128 : n.val < 128 := by omega
  rw [a_post, aval_set _ _ _ hn128]
  by_cases hjn : j' = n.val
  · rw [ite_eq_left hjn]
    refine ⟨hb5, ?_⟩
    rw [he5, map_mul, he3, hjn, colV_clear _ htK htb]
    congr 1
    rw [xiOf, hi4]
  · rw [ite_eq_right hjn]
    exact hd j' (by scalar_tac)

open Aeneas Aeneas.Std CoreModels Polynomial in
/-- Column `j` of `columns` is the image `∏_{i ∈ bits(j)} ξ_i` of tower basis element `j`. -/
theorem columns_spec (bits : Std.Usize) (K : ℕ) (hK : bits.val = 2 ^ K) (hK1 : 1 ≤ K)
    (hK7 : K ≤ 7) (tail : Std.U128) (ht : tail.val < 2 ^ bits.val) (xi : Slice Std.U128)
    (hxi : xi.length = K) (hxiv : ∀ i < K, (xi.val.getD i 0#u128).val < 2 ^ bits.val) :
    clmul.basis.columns bits tail xi ⦃ c => ∀ j < bits.val,
      aval c j < 2 ^ bits.val ∧
      AdjoinRoot.mk (modPoly bits.val tail.val) (natPoly (aval c j)) =
        colV (xiOf bits.val tail.val xi) K j ⦄ := by
  unfold clmul.basis.columns
  obtain ⟨z, hz, -⟩ :=
    Lib.array_repeat_eq 128#usize core.U128.Insts.CoreCloneClone (fun _ => rfl) 0#u128
  rw [hz, Aeneas.Std.bind_ok]
  have h2 : 2 ≤ bits.val := by
    rw [hK]; exact le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) hK1)
  step*
  refine columns_loop_spec bits K hK hK1 hK7 tail ht xi hxi hxiv a 1#usize (by simp)
    (by simp; omega) (fun j hj => ?_)
  have hj0 : j = 0 := by simpa using hj
  subst hj0
  rw [a_post, aval_set _ _ _ (by simp), ite_eq_left (by rfl)]
  refine ⟨Nat.one_lt_two_pow (by omega), ?_⟩
  rw [show ((1#u128 : Std.U128).val) = 1 from rfl, natPoly_one, map_one]
  unfold colV
  simp

end Plonky3Lean.Proofs.Binary
