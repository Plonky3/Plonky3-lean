module

public import Plonky3Lean.Proofs.Field.Binary.BasisTables

@[expose] public section

/-!
# The change of basis is a field isomorphism

With the columns `columns` computes, `lin` is `towerMap` in coordinates (`lin_eq_towerMap`).
`towerMap` is a ring homomorphism out of a field once the images satisfy the tower's
relations, so it is injective, which is what `invert` needs (`lin_injective`).
-/

open Aeneas Aeneas.Std CoreModels Polynomial
open ConcreteBinaryTower ConcreteBinaryTower.Coordinates
open p3_binary_field BinaryField
open Plonky3Lean.Lib Plonky3Lean.Spec.BinaryField

namespace Plonky3Lean.Proofs.Binary

/-! ## The quotient ring -/

theorem degree_modPoly {n tail : ℕ} (ht : tail < 2 ^ n) : (modPoly n tail).degree = n := by
  unfold modPoly
  rw [degree_add_eq_left_of_degree_lt (by rw [degree_X_pow]; exact degree_natPoly_lt ht),
    degree_X_pow]

theorem nontrivial_modPoly {n tail : ℕ} (hn : 1 ≤ n) (ht : tail < 2 ^ n) :
    Nontrivial (AdjoinRoot (modPoly n tail)) :=
  AdjoinRoot.nontrivial _ (by rw [degree_modPoly ht]; exact_mod_cast (by omega : n ≠ 0))

theorem charP_modPoly {n tail : ℕ} (hn : 1 ≤ n) (ht : tail < 2 ^ n) :
    CharP (AdjoinRoot (modPoly n tail)) 2 := by
  have := nontrivial_modPoly hn ht
  exact charP_of_injective_algebraMap (algebraMap (ZMod 2) (AdjoinRoot (modPoly n tail))).injective 2

/-! ## `lin` in the quotient -/

theorem mk_lin {R : Type} [CommRing R] (φ : (ZMod 2)[X] →+* R) (c : ℕ → ℕ) : ∀ k v,
    φ (natPoly (lin c k v)) =
      ∑ j ∈ Finset.range k, if v.testBit j then φ (natPoly (c j)) else 0
  | 0, v => by simp [lin, natPoly_zero]
  | k + 1, v => by
    rw [lin, natPoly_xor, map_add, mk_lin φ c k v, Finset.sum_range_succ]
    congr 1
    split <;> simp [natPoly_zero]

/-- With columns the images of the tower basis, `lin` is `towerMap` in coordinates. -/
theorem lin_eq_towerMap {n tail : ℕ} (ξ : ℕ → AdjoinRoot (modPoly n tail)) (K : ℕ) (c : ℕ → ℕ)
    (hc : ∀ j < 2 ^ K, AdjoinRoot.mk (modPoly n tail) (natPoly (c j)) = colV ξ K j) {v : ℕ}
    (hv : v < 2 ^ 2 ^ K) :
    AdjoinRoot.mk (modPoly n tail) (natPoly (lin c (2 ^ K) v)) = towerMap ξ K (fromNat v) := by
  rw [mk_lin, towerMap_fromNat ξ K hv]
  apply Finset.sum_congr rfl
  intro j hj
  rw [hc j (Finset.mem_range.mp hj)]

/-- The map with those columns is injective. -/
theorem lin_injective {n tail : ℕ} (hn : 1 ≤ n) (ht : tail < 2 ^ n)
    (ξ : ℕ → AdjoinRoot (modPoly n tail)) (K : ℕ)
    (hrel : ∀ j < K, ξ j * ξ j = prevGen ξ j * ξ j + 1) (c : ℕ → ℕ)
    (hc : ∀ j < 2 ^ K, AdjoinRoot.mk (modPoly n tail) (natPoly (c j)) = colV ξ K j) {w : ℕ}
    (hw : w < 2 ^ 2 ^ K) (h0 : lin c (2 ^ K) w = 0) : w = 0 := by
  have := nontrivial_modPoly hn ht
  have := charP_modPoly hn ht
  have h := lin_eq_towerMap ξ K c hc hw
  rw [h0, natPoly_zero, map_zero] at h
  have hz : towerHom ξ K hrel (fromNat w) = towerHom ξ K hrel 0 := by
    rw [map_zero]; exact h.symm
  have := congrArg ConcreteBTField.toNat ((towerHom ξ K hrel).injective hz)
  rw [ConcreteBTField.toNat_fromNat, Nat.mod_eq_of_lt hw] at this
  rw [this]
  rfl

/-! ## A kernel-friendly product in the quotient -/

/-- The carry-less product of two 128-bit numbers, from four products of 64-bit halves. -/
def clmul128Nat (a b : ℕ) : ℕ :=
  let a0 := a % 2 ^ 64
  let a1 := a >>> 64
  let b0 := b % 2 ^ 64
  let b1 := b >>> 64
  clmulHalves a0 b0 ^^^ (clmulHalves a0 b1 ^^^ clmulHalves a1 b0) <<< 64 ^^^
    clmulHalves a1 b1 <<< 128

theorem shiftRight_64_lt_of_lt {a : ℕ} (ha : a < 2 ^ 128) : a >>> 64 < 2 ^ 64 := by
  rw [Nat.shiftRight_eq_div_pow]
  exact Nat.div_lt_of_lt_mul (by omega)

theorem natPoly_clmul128Nat {a b : ℕ} (ha : a < 2 ^ 128) (hb : b < 2 ^ 128) :
    natPoly (clmul128Nat a b) = natPoly a * natPoly b := by
  have ha0 : a % 2 ^ 64 < 2 ^ 64 := Nat.mod_lt _ (by norm_num)
  have hb0 : b % 2 ^ 64 < 2 ^ 64 := Nat.mod_lt _ (by norm_num)
  have ha1 := shiftRight_64_lt_of_lt ha
  have hb1 := shiftRight_64_lt_of_lt hb
  unfold clmul128Nat
  simp only [natPoly_xor, natPoly_shiftLeft, natPoly_clmulHalves ha0 hb0,
    natPoly_clmulHalves ha0 hb1, natPoly_clmulHalves ha1 hb0, natPoly_clmulHalves ha1 hb1]
  rw [natPoly_split a 64, natPoly_split b 64]
  ring

/-- One fold modulo `x^n + tail`: the part from degree `n` up comes back multiplied by `tail`. -/
def foldOnce (n tail p : ℕ) : ℕ := p % 2 ^ n ^^^ clmul128Nat (p >>> n) tail

theorem mk_foldOnce {n tail p : ℕ} (hh : p >>> n < 2 ^ 128) (ht : tail < 2 ^ 128) :
    AdjoinRoot.mk (modPoly n tail) (natPoly (foldOnce n tail p)) =
      AdjoinRoot.mk (modPoly n tail) (natPoly p) := by
  rw [AdjoinRoot.mk_eq_mk]
  refine ⟨-natPoly (p >>> n), ?_⟩
  rw [foldOnce, natPoly_xor, natPoly_clmul128Nat hh ht, natPoly_split p n, modPoly]
  linear_combination (natPoly (p >>> n) * natPoly tail) *
    (CharTwo.two_eq_zero : (2 : (ZMod 2)[X]) = 0)

/-- The product modulo `x^n + tail`, by two folds. -/
def mulGen (n tail a b : ℕ) : ℕ := foldOnce n tail (foldOnce n tail (clmul128Nat a b))

/-- The relation `x² = prev·x + 1`, checked on natural numbers. -/
def relOK (n tail prev x : ℕ) : Bool :=
  decide (x < 2 ^ 128) && decide (prev < 2 ^ 128) && decide (tail < 2 ^ 128) &&
    decide (clmul128Nat x x >>> n < 2 ^ 128) &&
    decide (foldOnce n tail (clmul128Nat x x) >>> n < 2 ^ 128) &&
    decide (clmul128Nat prev x >>> n < 2 ^ 128) &&
    decide (foldOnce n tail (clmul128Nat prev x) >>> n < 2 ^ 128) &&
    mulGen n tail x x == (mulGen n tail prev x ^^^ 1)

theorem rel_of_relOK {n tail prev x : ℕ} (h : relOK n tail prev x = true) :
    AdjoinRoot.mk (modPoly n tail) (natPoly x) * AdjoinRoot.mk (modPoly n tail) (natPoly x) =
      AdjoinRoot.mk (modPoly n tail) (natPoly prev) *
        AdjoinRoot.mk (modPoly n tail) (natPoly x) + 1 := by
  simp only [relOK, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨hx, hp⟩, ht⟩, h1⟩, h2⟩, h3⟩, h4⟩, he⟩ := h
  have e1 := congrArg (fun m => AdjoinRoot.mk (modPoly n tail) (natPoly m)) he
  simp only [mulGen, natPoly_xor, map_add, mk_foldOnce h2 ht, mk_foldOnce h1 ht, mk_foldOnce h4 ht,
    mk_foldOnce h3 ht, natPoly_clmul128Nat hx hx, natPoly_clmul128Nat hp hx, map_mul, natPoly_one,
    map_one] at e1
  exact e1

/-- Every image in `xs` satisfies the relation with the one before it (`1` before the first). -/
def relsOK (n tail : ℕ) (xs : List ℕ) : Bool :=
  (List.range xs.length).all fun k =>
    relOK n tail (if k = 0 then 1 else xs.getD (k - 1) 0) (xs.getD k 0)

theorem rels_of_relsOK {n tail : ℕ} {xs : List ℕ} (h : relsOK n tail xs = true)
    (ξ : ℕ → AdjoinRoot (modPoly n tail))
    (hξ : ∀ i, ξ i = AdjoinRoot.mk (modPoly n tail) (natPoly (xs.getD i 0))) :
    ∀ k < xs.length, ξ k * ξ k = prevGen ξ k * ξ k + 1 := by
  intro k hk
  have hr := List.all_eq_true.mp h k (List.mem_range.mpr hk)
  have e := rel_of_relOK hr
  rw [hξ k]
  cases k with
  | zero => simpa [prevGen, natPoly_one] using e
  | succ k => simpa [prevGen, hξ k] using e

/-! ## The generator images -/

theorem relsOK_128 : relsOK 128 135 (clmul.basis.XI_128.val.map (·.val)) = true := by
  decide +kernel

theorem relsOK_64 : relsOK 64 27 (clmul.basis.XI_64.val.map (·.val)) = true := by
  decide +kernel

theorem relsOK_32 : relsOK 32 141 (clmul.basis.XI_32.val.map (·.val)) = true := by
  decide +kernel

end Plonky3Lean.Proofs.Binary
