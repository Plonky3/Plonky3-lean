module

public import Plonky3Lean.Proofs.Field.Binary.BasisIso

@[expose] public section

/-!
# Converting between the tower and the polynomial bases

`tower_to_poly_128` is the field isomorphism `N = towerMap ξ` from the tower's `GF(2^128)` onto
`GF(2)[x] / (x^128 + x^7 + x^2 + x + 1)`, and `poly_to_tower_128` is its inverse; likewise at
64 and 32 bits. Each is a byte-table application (`apply_128_spec`) of the columns of `N`
(`columns_spec`) or of their Gauss-Jordan inverse (`invert_spec`).
-/

open Aeneas Aeneas.Std CoreModels Polynomial
open ConcreteBinaryTower ConcreteBinaryTower.Coordinates
open p3_binary_field BinaryField BF128Ghash
open Plonky3Lean.Lib Plonky3Lean.Spec.BinaryField

namespace Plonky3Lean.Proofs.Binary

/-- The images `ξ_i` a list of generator images stands for, in `GF(2)[x] / (x^n + tail)`. -/
noncomputable def xiArr (n tail : ℕ) (xs : List ℕ) (i : ℕ) : AdjoinRoot (modPoly n tail) :=
  AdjoinRoot.mk (modPoly n tail) (natPoly (xs.getD i 0))

theorem xiOf_to_slice {N : Std.Usize} (n tail : ℕ) (a : Std.Array Std.U128 N) :
    xiOf n tail (Std.Array.to_slice a) = xiArr n tail (a.val.map (·.val)) := by
  funext i
  rw [xiOf, xiArr]
  congr 2
  rw [Std.Array.val_to_slice, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases a.val[i]? <;> rfl

/-- The identity's columns. -/
theorem lin_two_pow_cols : ∀ k v, lin (fun c => 2 ^ c) k v = v % 2 ^ k
  | 0, v => by simp [lin, Nat.mod_one]
  | k + 1, v => by
    rw [lin, lin_two_pow_cols k v]
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_xor, Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow]
    split
    · rw [Nat.testBit_two_pow]
      by_cases hik : i = k
      · subst hik; simp [*]
      · by_cases hi : i < k
        · simp [hi, show i < k + 1 by omega, Ne.symm hik]
        · simp [hi, show ¬ i < k + 1 by omega, Ne.symm hik]
    · rename_i hb
      simp only [Nat.zero_testBit, Bool.xor_false]
      by_cases hik : i = k
      · subst hik; simp [hb]
      · by_cases hi : i < k
        · simp [hi, show i < k + 1 by omega]
        · simp [hi, show ¬ i < k + 1 by omega]

theorem lin_congr_cols {c d : ℕ → ℕ} : ∀ k v, (∀ i < k, c i = d i) → lin c k v = lin d k v
  | 0, _, _ => rfl
  | k + 1, v, h => by
    simp only [lin, lin_congr_cols k v (fun i hi => h i (by omega)), h k (by omega)]

/-! ## 128 bits -/

/-- The images of the generators of the tower's `GF(2^128)` in
`GF(2)[x] / (x^128 + x^7 + x^2 + x + 1)`. -/
noncomputable abbrev xi128 : ℕ → AdjoinRoot (modPoly 128 135) :=
  xiArr 128 135 (clmul.basis.XI_128.val.map (·.val))

theorem xi128_rel : ∀ k < 7, xi128 k * xi128 k = prevGen xi128 k * xi128 k + 1 :=
  fun k hk => rels_of_relsOK relsOK_128 xi128 (fun _ => rfl) k (by simpa using hk)

theorem TAIL_128_val : clmul.basis.TAIL_128.val = 135 := by
  unfold clmul.basis.TAIL_128; rfl

theorem COLUMNS_128_spec : clmul.basis.COLUMNS_128 ⦃ c => ∀ j < 128,
    aval c j < 2 ^ 128 ∧ AdjoinRoot.mk (modPoly 128 135) (natPoly (aval c j)) = colV xi128 7 j ⦄ := by
  unfold clmul.basis.COLUMNS_128
  rw [array_as_slice_eq, Aeneas.Std.bind_ok]
  have h := columns_spec 128#usize 7 (by simp) (by norm_num) le_rfl clmul.basis.TAIL_128
    (by rw [TAIL_128_val]; norm_num) (Std.Array.to_slice clmul.basis.XI_128)
    (by simp [Std.Slice.length, Std.Array.val_to_slice]) (fun i _ => u128_val_lt _)
  rw [TAIL_128_val, xiOf_to_slice] at h
  exact h

/-- The columns of `N` at 128 bits, applied to `v`, are `N(v)`. -/
theorem lin_columns_128 {c : ℕ → ℕ}
    (hc : ∀ j < 128, AdjoinRoot.mk (modPoly 128 135) (natPoly (c j)) = colV xi128 7 j) {v : ℕ}
    (hv : v < 2 ^ 128) :
    AdjoinRoot.mk (modPoly 128 135) (natPoly (lin c 128 v)) = towerMap xi128 7 (fromNat v) :=
  lin_eq_towerMap xi128 7 c hc hv

theorem TOWER_TO_POLY_128_spec : clmul.basis.TOWER_TO_POLY_128 ⦃ T =>
    ∃ c : ℕ → ℕ, (∀ j < 128, AdjoinRoot.mk (modPoly 128 135) (natPoly (c j)) = colV xi128 7 j) ∧
      ∀ k < 16, ∀ w < 256, cellOf T k w = linB c k w ⦄ := by
  unfold clmul.basis.TOWER_TO_POLY_128
  apply WP.spec_bind COLUMNS_128_spec
  intro cols hcols
  apply WP.spec_mono (byte_tables_spec cols 128#usize (by simp))
  intro T hT
  exact ⟨aval cols, fun j hj => (hcols j hj).2, fun k hk w hw => hT k (by simpa using hk) w hw⟩

theorem POLY_TO_TOWER_128_spec : clmul.basis.POLY_TO_TOWER_128 ⦃ T =>
    ∃ c d : ℕ → ℕ, (∀ j < 128, AdjoinRoot.mk (modPoly 128 135) (natPoly (c j)) = colV xi128 7 j) ∧
      (∀ j < 128, lin c 128 (d j) = 2 ^ j) ∧
      ∀ k < 16, ∀ w < 256, cellOf T k w = linB d k w ⦄ := by
  unfold clmul.basis.POLY_TO_TOWER_128
  apply WP.spec_bind COLUMNS_128_spec
  intro cols hcols
  apply WP.spec_bind (invert_spec cols 128#usize (by simp) (fun c hc => (hcols c hc).1)
    (fun w hw h0 => lin_injective (by norm_num) (by norm_num) xi128 7 xi128_rel (aval cols)
      (fun j hj => (hcols j hj).2) hw h0))
  intro inv hinv
  apply WP.spec_mono (byte_tables_spec inv 128#usize (by simp))
  intro T hT
  exact ⟨aval cols, aval inv, fun j hj => (hcols j hj).2, fun j hj => (hinv j hj).2,
    fun k hk w hw => hT k (by simpa using hk) w hw⟩

/-- `tower_to_poly_128` is the field isomorphism `N`. -/
theorem tower_to_poly_128_spec (v : Std.U128) :
    clmul.basis.tower_to_poly_128 v ⦃ r =>
      AdjoinRoot.mk (modPoly 128 135) (natPoly r.val) = towerMap xi128 7 (towerOf 7 v) ⦄ := by
  unfold clmul.basis.tower_to_poly_128
  apply WP.spec_bind TOWER_TO_POLY_128_spec
  rintro T ⟨c, hc, hT⟩
  apply WP.spec_mono (apply_128_spec T c hT v)
  intro r hr
  rw [hr, towerOf]
  exact lin_columns_128 hc (u128_val_lt v)

/-- `poly_to_tower_128` is the inverse of `N`. -/
theorem poly_to_tower_128_spec (v : Std.U128) :
    clmul.basis.poly_to_tower_128 v ⦃ r =>
      towerMap xi128 7 (towerOf 7 r) = AdjoinRoot.mk (modPoly 128 135) (natPoly v.val) ⦄ := by
  unfold clmul.basis.poly_to_tower_128
  apply WP.spec_bind POLY_TO_TOWER_128_spec
  rintro T ⟨c, d, hc, hd, hT⟩
  apply WP.spec_mono (apply_128_spec T d hT v)
  intro r hr
  rw [towerOf, ← lin_columns_128 hc (u128_val_lt r), hr, lin_lin,
    lin_congr_cols 128 v.val (fun j hj => hd j hj), lin_two_pow_cols,
    Nat.mod_eq_of_lt (u128_val_lt v)]

/-- `N` at 128 bits, as a ring homomorphism. -/
noncomputable abbrev N128 : ConcreteBTField 7 →+* AdjoinRoot (modPoly 128 135) :=
  @towerHom _ _ (charP_modPoly (by norm_num) (by norm_num)) xi128 7 xi128_rel

theorem N128_apply (x : ConcreteBTField 7) : N128 x = towerMap xi128 7 x := rfl

theorem N128_injective : Function.Injective N128 := by
  have := nontrivial_modPoly (n := 128) (tail := 135) (by norm_num) (by norm_num)
  exact N128.injective

/-- A polynomial of degree below `n` vanishes modulo `x^n + tail` only if it is zero. -/
theorem mk_natPoly_eq_zero {n tail x : ℕ} (ht : tail < 2 ^ n) (hx : x < 2 ^ n)
    (h : AdjoinRoot.mk (modPoly n tail) (natPoly x) = 0) : x = 0 := by
  rw [AdjoinRoot.mk_eq_zero] at h
  have hd : (natPoly x).degree < (modPoly n tail).degree := by
    rw [degree_modPoly ht]; exact degree_natPoly_lt hx
  have h0 := Polynomial.eq_zero_of_dvd_of_degree_lt h hd
  exact natPoly_injective (by rw [h0, natPoly_zero])

/-! ## GHASH -/

theorem natPoly_135 : natPoly 135 = X ^ 7 + X ^ 2 + X + 1 := by
  rw [show (135 : ℕ) = 2 ^ 7 ^^^ 2 ^ 2 ^^^ 2 ^ 1 ^^^ 2 ^ 0 by decide +kernel]
  simp only [natPoly_xor, natPoly_two_pow, natPoly_two, natPoly_one, pow_one, pow_zero]

theorem modPoly_128_ghash : modPoly 128 135 = ghashPoly := by
  rw [ghashPoly_eq_X_pow_add_tail, modPoly, natPoly_135, ghashTail]

theorem mk_ghash_eq {p q : (ZMod 2)[X]}
    (h : AdjoinRoot.mk (modPoly 128 135) p = AdjoinRoot.mk (modPoly 128 135) q) :
    AdjoinRoot.mk ghashPoly p = AdjoinRoot.mk ghashPoly q := by
  rw [AdjoinRoot.mk_eq_mk] at h ⊢
  rwa [modPoly_128_ghash] at h

/-- `From<Ghash128> for BinaryField128` is `N⁻¹`. -/
theorem bf128_from_ghash_spec (x : ghash.Ghash128) :
    tower.BinaryField128.Insts.CoreConvertFromGhash128.from x ⦃ t =>
      N128 (towerOf 7 t) = AdjoinRoot.mk (modPoly 128 135) (natPoly x.val) ⦄ := by
  unfold tower.BinaryField128.Insts.CoreConvertFromGhash128.from
  apply WP.spec_bind (poly_to_tower_128_spec x)
  intro i hi
  apply WP.spec_mono (bf128_from_repr_spec i)
  intro t ht
  rw [N128_apply, ← hi, towerOf, towerOf, ht,
    Nat.mod_eq_of_lt (show i.val < 2 ^ 2 ^ 7 from u128_val_lt i)]

/-- `From<BinaryField128> for Ghash128` is `N`. -/
theorem ghash_from_bf128_spec (t : tower.BinaryField128) :
    ghash.Ghash128.Insts.CoreConvertFromBinaryField128.from t ⦃ x =>
      AdjoinRoot.mk (modPoly 128 135) (natPoly x.val) = N128 (towerOf 7 t) ⦄ := by
  unfold ghash.Ghash128.Insts.CoreConvertFromBinaryField128.from
  apply WP.spec_bind (bf128_to_repr_spec t)
  intro i hi
  apply WP.spec_bind (tower_to_poly_128_spec i)
  intro r hr
  rw [WP.spec_ok, hr, N128_apply, towerOf, towerOf, hi]

/-- `invert_or_zero` inverts in CompPoly's GHASH field, sending `0` to `0`. -/
theorem ghash_invert_or_zero_spec (x : ghash.Ghash128) :
    ghash.invert_or_zero x ⦃ r => ghash r = (ghash x)⁻¹ ⦄ := by
  unfold ghash.invert_or_zero
  apply WP.spec_bind (bf128_from_ghash_spec x)
  intro t ht
  apply WP.spec_bind (bf128_try_inverse_spec t)
  intro o ho
  unfold core.option.Option.map_or
  by_cases ht0 : towerOf 7 t = 0
  · rw [ho.1 ht0]
    rw [WP.spec_ok]
    have hx0 : x.val = 0 := by
      apply mk_natPoly_eq_zero (n := 128) (tail := 135) (by norm_num) (u128_val_lt x)
      rw [← ht, ht0, map_zero]
    have : x = 0#u128 := UScalar.eq_of_val_eq hx0
    subst this
    unfold ghash.Ghash128.Insts.P3_fieldFieldPrimeCharacteristicRing.ZERO
    rw [show ghash 0#u128 = 0 from rfl, inv_zero]
  · obtain ⟨c, hc, -, hcinv⟩ := ho.2 ht0
    rw [hc]
    dsimp only
    unfold P.Insts.CoreOpsFunctionFnOnceTupleBinaryField128Ghash128.call_once
    apply WP.spec_mono (ghash_from_bf128_spec c)
    intro r hr
    have hprod : AdjoinRoot.mk (modPoly 128 135) (natPoly r.val * natPoly x.val) =
        AdjoinRoot.mk (modPoly 128 135) 1 := by
      rw [map_mul, hr, ← ht, ← map_mul, hcinv, inv_mul_cancel₀ ht0, map_one, map_one]
    have hq : toQuot (ghash r) * toQuot (ghash x) = 1 := by
      rw [toQuot_eq_mk, toQuot_eq_mk, ← map_mul, mk_ghash_eq hprod, map_one]
    have hm : ghash r * ghash x = 1 := by
      apply toQuot_injective
      rw [toQuot_mul, hq, toQuot_one]
    exact eq_inv_of_mul_eq_one_left hm

end Plonky3Lean.Proofs.Binary
