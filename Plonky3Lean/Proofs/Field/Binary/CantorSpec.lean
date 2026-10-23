module

public import Plonky3Lean.Proofs.Field.Binary.Cantor

@[expose] public section

/-!
# The Cantor basis in each field

`cantorTower k i` is vector `i` of the Cantor basis in level `k` of the tower: `1` for `i = 0`,
and a root of `x^2 + x = v_(i-1)` otherwise (`cantorTower_succ`). The first `2^k` vectors form
a basis of level `k` (`cantor_basis_span`, `cantor_basis_indep`). Every `cantor_basis` method
returns these vectors, through the basis change `N` for `Ghash128` and `Poly64`.
-/

open Aeneas Aeneas.Std CoreModels Polynomial
open ConcreteBinaryTower ConcreteBinaryTower.Coordinates
open p3_binary_field BinaryField BF128Ghash
open Plonky3Lean.Lib Plonky3Lean.Spec.BinaryField

namespace Plonky3Lean.Proofs.Binary

/-- Vector `i` of the Cantor basis, in level `k` of the tower. -/
def cantorTower (k i : ℕ) : ConcreteBTField k := fromNat (cantorV i)

theorem toNat_one_tower (k : ℕ) : (1 : ConcreteBTField k).toNat = 1 :=
  one_bitvec_toNat (Nat.two_pow_pos k)

theorem cantorTower_zero (k : ℕ) : cantorTower k 0 = 1 := by
  apply ConcreteBTField.toNat_injective
  rw [cantorTower, ConcreteBTField.toNat_fromNat, cantorV_zero,
    Nat.mod_eq_of_lt (Nat.one_lt_two_pow (Nat.two_pow_pos k).ne'), toNat_one_tower]

/-- `v_i^2 + v_i = v_(i-1)`, in every level that holds `v_i`. -/
theorem cantorTower_succ {k : ℕ} (hk : k ≤ 7) {i : ℕ} (hi : i + 1 < 2 ^ k) :
    cantorTower k (i + 1) ^ 2 + cantorTower k (i + 1) = cantorTower k i := by
  apply ConcreteBTField.toNat_injective
  rw [toNat_add, _root_.sq,
    show cantorTower k (i + 1) * cantorTower k (i + 1) =
      concrete_mul (cantorTower k (i + 1)) (cantorTower k (i + 1)) from rfl,
    toNat_concrete_mul]
  simp only [cantorTower, ConcreteBTField.toNat_fromNat, Nat.mod_eq_of_lt (cantorV_lt hk hi),
    Nat.mod_eq_of_lt (cantorV_lt hk (show i < 2 ^ k by omega))]
  exact cantor_rel hk hi

/-! ## A basis -/

theorem lin_cantor_lt {k : ℕ} (hk : k ≤ 7) (w : ℕ) : lin cantorV (2 ^ k) w < 2 ^ 2 ^ k :=
  lin_lt _ _ _ (fun _ hi => cantorV_lt hk hi)

theorem cantorInv_spec {k : ℕ} (hk : k ≤ 7) {j : ℕ} (hj : j < 2 ^ k) :
    lin cantorV (2 ^ k) ((cantorInv k).getD j 0) = 2 ^ j ∧
      (cantorInv k).getD j 0 < 2 ^ 2 ^ k := by
  have h1 := List.all_eq_true.mp spanOK_all k (List.mem_range.mpr (by omega))
  have h2 := List.all_eq_true.mp h1 j (List.mem_range.mpr hj)
  simpa using h2

/-- Every element of level `k` is a sum of some of the first `2^k` vectors. -/
theorem cantor_span {k : ℕ} (hk : k ≤ 7) {x : ℕ} (hx : x < 2 ^ 2 ^ k) :
    lin cantorV (2 ^ k) (lin (fun j => (cantorInv k).getD j 0) (2 ^ k) x) = x := by
  rw [lin_lin, lin_congr_cols _ _ (fun j hj => (cantorInv_spec hk hj).1), lin_two_pow_cols,
    Nat.mod_eq_of_lt hx]

/-- A map on `[0, N)` with a right inverse there is injective there. -/
theorem injOn_of_rightInv {N : ℕ} {f g : ℕ → ℕ} (hg : ∀ x < N, g x < N)
    (hfg : ∀ x < N, f (g x) = x) {x y : ℕ} (hx : x < N) (hy : y < N) (h : f x = f y) :
    x = y := by
  have hinj : Set.InjOn g (Finset.range N : Set ℕ) := by
    intro a ha b hb e
    have ha' := Finset.mem_range.mp ha
    have hb' := Finset.mem_range.mp hb
    rw [← hfg a ha', ← hfg b hb', e]
  have himg : (Finset.range N).image g = Finset.range N := by
    apply Finset.eq_of_subset_of_card_le
    · intro z hz
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hz
      exact Finset.mem_range.mpr (hg a (Finset.mem_range.mp ha))
    · rw [Finset.card_image_of_injOn hinj]
  have hxm : x ∈ (Finset.range N).image g := by rw [himg]; exact Finset.mem_range.mpr hx
  have hym : y ∈ (Finset.range N).image g := by rw [himg]; exact Finset.mem_range.mpr hy
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hxm
  obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hym
  rw [hfg a (Finset.mem_range.mp ha), hfg b (Finset.mem_range.mp hb)] at h
  rw [h]

/-- The first `2^k` vectors are independent: only the empty sum vanishes. -/
theorem cantor_injective {k : ℕ} (hk : k ≤ 7) {w : ℕ} (hw : w < 2 ^ 2 ^ k)
    (h0 : lin cantorV (2 ^ k) w = 0) : w = 0 := by
  refine injOn_of_rightInv (N := 2 ^ 2 ^ k) (f := lin cantorV (2 ^ k))
    (g := lin (fun j => (cantorInv k).getD j 0) (2 ^ k))
    (fun x _ => lin_lt _ _ _ (fun j hj => (cantorInv_spec hk hj).2)) (fun x hx => cantor_span hk hx)
    hw (Nat.two_pow_pos _) ?_
  rw [h0, lin_zero]

theorem fromNat_xor {k : ℕ} (a b : ℕ) :
    (fromNat (a ^^^ b) : ConcreteBTField k) = fromNat a + fromNat b := by
  apply ConcreteBTField.toNat_injective
  rw [toNat_add, ConcreteBTField.toNat_fromNat, ConcreteBTField.toNat_fromNat,
    ConcreteBTField.toNat_fromNat]
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_mod_two_pow, Nat.testBit_xor]
  by_cases h : i < 2 ^ k <;> simp [h]

theorem fromNat_lin {k : ℕ} (c : ℕ → ℕ) : ∀ n w,
    (fromNat (lin c n w) : ConcreteBTField k) =
      ∑ i ∈ Finset.range n, if w.testBit i then fromNat (c i) else 0
  | 0, w => by
    apply ConcreteBTField.toNat_injective
    simp [lin, ConcreteBTField.toNat_fromNat]
    rfl
  | n + 1, w => by
    rw [lin, fromNat_xor, fromNat_lin c n w, Finset.sum_range_succ]
    congr 1
    split
    · rfl
    · apply ConcreteBTField.toNat_injective
      simp [ConcreteBTField.toNat_fromNat]
      rfl

/-- Every element of level `k` is a sum of some of the first `2^k` vectors of the basis. -/
theorem cantor_basis_span {k : ℕ} (hk : k ≤ 7) (x : ConcreteBTField k) :
    ∃ w < 2 ^ 2 ^ k, x = ∑ i ∈ Finset.range (2 ^ k), if w.testBit i then cantorTower k i else 0 := by
  refine ⟨lin (fun j => (cantorInv k).getD j 0) (2 ^ k) x.toNat,
    lin_lt _ _ _ (fun j hj => (cantorInv_spec hk hj).2), ?_⟩
  simp only [cantorTower]
  rw [← fromNat_lin, cantor_span hk x.toNat_lt, ConcreteBTField.fromNat_toNat]

/-- Only the empty sum of the first `2^k` vectors vanishes. -/
theorem cantor_basis_indep {k : ℕ} (hk : k ≤ 7) {w : ℕ} (hw : w < 2 ^ 2 ^ k)
    (h : (∑ i ∈ Finset.range (2 ^ k), if w.testBit i then cantorTower k i else 0) = 0) :
    w = 0 := by
  simp only [cantorTower] at h
  rw [← fromNat_lin] at h
  have := congrArg ConcreteBTField.toNat h
  rw [ConcreteBTField.toNat_fromNat, Nat.mod_eq_of_lt (lin_cantor_lt hk w)] at this
  exact cantor_injective hk hw (by rw [this]; rfl)

/-! ## The `cantor_basis` methods -/

theorem cantor_getElem {i : ℕ} (h : i < cantor.CANTOR_BASIS_128.val.length) :
    (cantor.CANTOR_BASIS_128.val[i]).val = cantorV i := by
  rw [cantorV_eq, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h, Option.getD_some]

theorem bf32_cantor_basis_spec (i : Std.Usize) (hi : i.val < 32) :
    tower.BinaryField32.Insts.P3_binary_fieldTowerTowerLevelU32.cantor_basis i ⦃ r =>
      towerOf 5 r = cantorTower 5 i.val ⦄ := by
  unfold tower.BinaryField32.Insts.P3_binary_fieldTowerTowerLevelU32.cantor_basis
  step*
  have hlt := cantorV_lt (k := 5) (by norm_num) (show i.val < 2 ^ 5 by simpa using hi)
  rw [towerOf, cantorTower, r_post, i2_post, UScalar.cast_val_eq, UScalarTy.U32_numBits_eq,
    i1_post1, cantor_getElem, Nat.mod_eq_of_lt (show cantorV i.val < 2 ^ 32 from hlt),
    Nat.mod_eq_of_lt hlt]

theorem bf2_cantor_basis_spec (i : Std.Usize) (hi : i.val < 2) :
    tower.BinaryField2.Insts.P3_binary_fieldTowerTowerLevelU8.cantor_basis i ⦃ r =>
      towerOf 1 r = cantorTower 1 i.val ⦄ := by
  unfold tower.BinaryField2.Insts.P3_binary_fieldTowerTowerLevelU8.cantor_basis
  step*
  have hlt := cantorV_lt (k := 1) (by norm_num) (show i.val < 2 ^ 1 by simpa using hi)
  rw [towerOf, cantorTower, r_post, i2_post, UScalar.cast_val_eq, UScalarTy.U8_numBits_eq,
    i1_post1, cantor_getElem, Nat.mod_eq_of_lt (show cantorV i.val < 2 ^ 8 from
      lt_of_lt_of_le hlt (by norm_num)), Nat.mod_eq_of_lt hlt]

theorem bf4_cantor_basis_spec (i : Std.Usize) (hi : i.val < 4) :
    tower.BinaryField4.Insts.P3_binary_fieldTowerTowerLevelU8.cantor_basis i ⦃ r =>
      towerOf 2 r = cantorTower 2 i.val ⦄ := by
  unfold tower.BinaryField4.Insts.P3_binary_fieldTowerTowerLevelU8.cantor_basis
  step*
  have hlt := cantorV_lt (k := 2) (by norm_num) (show i.val < 2 ^ 2 by simpa using hi)
  rw [towerOf, cantorTower, r_post, i2_post, UScalar.cast_val_eq, UScalarTy.U8_numBits_eq,
    i1_post1, cantor_getElem, Nat.mod_eq_of_lt (show cantorV i.val < 2 ^ 8 from
      lt_of_lt_of_le hlt (by norm_num)), Nat.mod_eq_of_lt hlt]

theorem bf8_cantor_basis_spec (i : Std.Usize) (hi : i.val < 8) :
    tower.BinaryField8.Insts.P3_binary_fieldTowerTowerLevelU8.cantor_basis i ⦃ r =>
      towerOf 3 r = cantorTower 3 i.val ⦄ := by
  unfold tower.BinaryField8.Insts.P3_binary_fieldTowerTowerLevelU8.cantor_basis
  step*
  have hlt := cantorV_lt (k := 3) (by norm_num) (show i.val < 2 ^ 3 by simpa using hi)
  rw [towerOf, cantorTower, r_post, i2_post, UScalar.cast_val_eq, UScalarTy.U8_numBits_eq,
    i1_post1, cantor_getElem, Nat.mod_eq_of_lt (show cantorV i.val < 2 ^ 8 from
      lt_of_lt_of_le hlt (by norm_num)), Nat.mod_eq_of_lt hlt]

theorem bf16_cantor_basis_spec (i : Std.Usize) (hi : i.val < 16) :
    tower.BinaryField16.Insts.P3_binary_fieldTowerTowerLevelU16.cantor_basis i ⦃ r =>
      towerOf 4 r = cantorTower 4 i.val ⦄ := by
  unfold tower.BinaryField16.Insts.P3_binary_fieldTowerTowerLevelU16.cantor_basis
  step*
  have hlt := cantorV_lt (k := 4) (by norm_num) (show i.val < 2 ^ 4 by simpa using hi)
  rw [towerOf, cantorTower, r_post, i2_post, UScalar.cast_val_eq, UScalarTy.U16_numBits_eq,
    i1_post1, cantor_getElem, Nat.mod_eq_of_lt (show cantorV i.val < 2 ^ 16 from
      lt_of_lt_of_le hlt (by norm_num)), Nat.mod_eq_of_lt hlt]

theorem bf64_cantor_basis_spec (i : Std.Usize) (hi : i.val < 64) :
    tower.BinaryField64.Insts.P3_binary_fieldTowerTowerLevelU64.cantor_basis i ⦃ r =>
      towerOf 6 r = cantorTower 6 i.val ⦄ := by
  unfold tower.BinaryField64.Insts.P3_binary_fieldTowerTowerLevelU64.cantor_basis
  step*
  have hlt := cantorV_lt (k := 6) (by norm_num) (show i.val < 2 ^ 6 by simpa using hi)
  rw [towerOf, cantorTower, r_post, i2_post, UScalar.cast_val_eq, UScalarTy.U64_numBits_eq,
    i1_post1, cantor_getElem, Nat.mod_eq_of_lt (show cantorV i.val < 2 ^ 64 from
      lt_of_lt_of_le hlt (by norm_num)), Nat.mod_eq_of_lt hlt]

theorem bf128_cantor_basis_spec (i : Std.Usize) (hi : i.val < 128) :
    tower.BinaryField128.Insts.P3_binary_fieldTowerTowerLevelU128.cantor_basis i ⦃ r =>
      towerOf 7 r = cantorTower 7 i.val ⦄ := by
  unfold tower.BinaryField128.Insts.P3_binary_fieldTowerTowerLevelU128.cantor_basis
  step*
  have hlt := cantorV_lt (k := 7) (by norm_num) (show i.val < 2 ^ 7 by simpa using hi)
  rw [towerOf, cantorTower, r_post, i1_post1, cantor_getElem, Nat.mod_eq_of_lt hlt]

theorem gf2_cantor_basis_spec (i : Std.Usize) (hi : i.val < 1) :
    gf2.Gf2.Insts.P3_binary_fieldTowerTowerLevelU8.cantor_basis i ⦃ r =>
      towerOf 0 r = cantorTower 0 i.val ⦄ := by
  unfold gf2.Gf2.Insts.P3_binary_fieldTowerTowerLevelU8.cantor_basis
  have h0 : i.val = 0 := by omega
  have : i < 1#usize := by scalar_tac
  simp only [massert, this, ↓reduceIte, Aeneas.Std.bind_ok, WP.spec_ok, h0, cantorTower_zero]
  unfold gf2.Gf2.Insts.P3_fieldFieldPrimeCharacteristicRing.ONE
  apply ConcreteBTField.toNat_injective
  rw [towerOf, ConcreteBTField.toNat_fromNat, toNat_one_tower]
  rfl

theorem gf2_cantor_basis_panic (i : Std.Usize) (hi : 1 ≤ i.val) :
    gf2.Gf2.Insts.P3_binary_fieldTowerTowerLevelU8.cantor_basis i = .fail .panic := by
  unfold gf2.Gf2.Insts.P3_binary_fieldTowerTowerLevelU8.cantor_basis
  have : ¬ i < 1#usize := by scalar_tac
  simp [massert, this]

theorem bf2_cantor_basis_panic (i : Std.Usize) (hi : 2 ≤ i.val) :
    tower.BinaryField2.Insts.P3_binary_fieldTowerTowerLevelU8.cantor_basis i = .fail .panic := by
  unfold tower.BinaryField2.Insts.P3_binary_fieldTowerTowerLevelU8.cantor_basis
  have : ¬ i < 2#usize := by scalar_tac
  simp [massert, this]

theorem bf4_cantor_basis_panic (i : Std.Usize) (hi : 4 ≤ i.val) :
    tower.BinaryField4.Insts.P3_binary_fieldTowerTowerLevelU8.cantor_basis i = .fail .panic := by
  unfold tower.BinaryField4.Insts.P3_binary_fieldTowerTowerLevelU8.cantor_basis
  have : ¬ i < 4#usize := by scalar_tac
  simp [massert, this]

theorem bf8_cantor_basis_panic (i : Std.Usize) (hi : 8 ≤ i.val) :
    tower.BinaryField8.Insts.P3_binary_fieldTowerTowerLevelU8.cantor_basis i = .fail .panic := by
  unfold tower.BinaryField8.Insts.P3_binary_fieldTowerTowerLevelU8.cantor_basis
  have : ¬ i < 8#usize := by scalar_tac
  simp [massert, this]

theorem bf16_cantor_basis_panic (i : Std.Usize) (hi : 16 ≤ i.val) :
    tower.BinaryField16.Insts.P3_binary_fieldTowerTowerLevelU16.cantor_basis i = .fail .panic := by
  unfold tower.BinaryField16.Insts.P3_binary_fieldTowerTowerLevelU16.cantor_basis
  have : ¬ i < 16#usize := by scalar_tac
  simp [massert, this]

theorem bf32_cantor_basis_panic (i : Std.Usize) (hi : 32 ≤ i.val) :
    tower.BinaryField32.Insts.P3_binary_fieldTowerTowerLevelU32.cantor_basis i = .fail .panic := by
  unfold tower.BinaryField32.Insts.P3_binary_fieldTowerTowerLevelU32.cantor_basis
  have : ¬ i < 32#usize := by scalar_tac
  simp [massert, this]

theorem bf64_cantor_basis_panic (i : Std.Usize) (hi : 64 ≤ i.val) :
    tower.BinaryField64.Insts.P3_binary_fieldTowerTowerLevelU64.cantor_basis i = .fail .panic := by
  unfold tower.BinaryField64.Insts.P3_binary_fieldTowerTowerLevelU64.cantor_basis
  have : ¬ i < 64#usize := by scalar_tac
  simp [massert, this]

theorem bf128_cantor_basis_panic (i : Std.Usize) (hi : 128 ≤ i.val) :
    tower.BinaryField128.Insts.P3_binary_fieldTowerTowerLevelU128.cantor_basis i = .fail .panic := by
  unfold tower.BinaryField128.Insts.P3_binary_fieldTowerTowerLevelU128.cantor_basis
  have : ¬ i < 128#usize := by scalar_tac
  simp [massert, this]

/-! ## Images of the basis -/

theorem image_loop_spec (bits : Std.Usize) (h128 : bits.val ≤ 128)
    (columns : Std.Array Std.U128 128#usize) (image column : Std.U128) (i : Std.Usize)
    (hi : i.val ≤ bits.val) (hc : column.val = lin (aval columns) i.val image.val) :
    clmul.basis.image_loop image bits columns column i ⦃ r =>
      r.val = lin (aval columns) bits.val image.val ⦄ := by
  unfold clmul.basis.image_loop
  refine loop.spec_decr_nat (fun s => bits.val - s.2.val)
    (fun s => s.2.val ≤ bits.val ∧ s.1.val = lin (aval columns) s.2.val image.val) _ _ _ ?_
    ⟨hi, hc⟩
  rintro ⟨col, n⟩ ⟨hn, hcol⟩
  dsimp only at hn hcol ⊢
  unfold clmul.basis.image_loop.body
  step*
  have hb : i2.val = if image.val.testBit n.val then 1 else 0 := by
    rw [i2_post, UScalar.val_and, i1_post, ← shiftRight_and_one_eq]; rfl
  split
  · rename_i h1
    have hbit : image.val.testBit n.val = true := by
      have : i2.val = 1 := by rw [h1]; rfl
      rw [hb] at this
      by_contra h; simp [h] at this
    step*
    refine ⟨by scalar_tac, ?_, by scalar_tac⟩
    rw [UScalar.val_xor, hcol, x_post1, ← aval_eq_getElem, i3_post, lin, hbit]
    rfl
  · rename_i h1
    have hbit : image.val.testBit n.val = false := by
      by_contra h
      have : i2.val = 1 := by rw [hb]; simp [h]
      exact h1 (UScalar.eq_of_val_eq this)
    step*
    refine ⟨by scalar_tac, ?_, by scalar_tac⟩
    rw [hcol, i3_post, lin, hbit]
    simp


/-- `tower_image_128` is `N` at 128 bits. -/
theorem tower_image_128_spec (v : Std.U128) :
    clmul.basis.tower_image_128 v ⦃ r =>
      AdjoinRoot.mk (modPoly 128 135) (natPoly r.val) = N128 (towerOf 7 v) ⦄ := by
  unfold clmul.basis.tower_image_128 clmul.basis.image
  apply WP.spec_bind COLUMNS_128_spec
  intro cols hcols
  apply WP.spec_mono (image_loop_spec 128#usize (by simp) cols v 0#u128 0#usize (by simp) rfl)
  intro r hr
  rw [hr, N128_apply, towerOf]
  exact lin_columns_128 (fun j hj => (hcols j hj).2) (u128_val_lt v)

/-- `tower_image_64` is `N` at 64 bits. -/
theorem tower_image_64_spec (v : Std.U64) :
    clmul.basis.tower_image_64 v ⦃ r =>
      AdjoinRoot.mk (modPoly 64 27) (natPoly r.val) = N64 (towerOf 6 v) ⦄ := by
  unfold clmul.basis.tower_image_64 clmul.basis.image
  step*
  apply WP.spec_bind COLUMNS_64_spec
  intro cols hcols
  apply WP.spec_bind (image_loop_spec 64#usize (by simp) cols i 0#u128 0#usize (by simp) rfl)
  intro r hr
  have hiv : i.val = v.val := by
    rw [i_post, UScalar.cast_val_eq, UScalarTy.U128_numBits_eq,
      Nat.mod_eq_of_lt (lt_of_lt_of_le (u64_val_lt v) (by norm_num))]
  have hlin : lin (aval cols) 64 v.val < 2 ^ 64 := lin_lt _ _ _ (fun j hj => (hcols j hj).1)
  rw [WP.spec_ok, UScalar.cast_val_eq, UScalarTy.U64_numBits_eq, hr, hiv,
    show (64#usize : Std.Usize).val = 64 from rfl, Nat.mod_eq_of_lt hlin,
    N64_apply, towerOf]
  exact lin_eq_towerMap xi64 6 _ (fun j hj => (hcols j hj).2) (u64_val_lt v)

theorem cantorTower_eq (k i : ℕ) (h : i < cantor.CANTOR_BASIS_128.val.length) :
    cantorTower k i = towerOf k (cantor.CANTOR_BASIS_128.val[i]) := by
  rw [cantorTower, towerOf, cantor_getElem]

/-! ## `Ghash128` -/

theorem ghash_cantor_loop_spec (b : Std.Array Std.U128 128#usize) (n : Std.Usize)
    (hn : n.val ≤ 128)
    (hd : ∀ j < n.val, AdjoinRoot.mk (modPoly 128 135) (natPoly (aval b j)) =
      N128 (cantorTower 7 j)) :
    ghash.CANTOR_BASIS_loop b n ⦃ r => ∀ j < 128,
      AdjoinRoot.mk (modPoly 128 135) (natPoly (aval r j)) = N128 (cantorTower 7 j) ⦄ := by
  unfold ghash.CANTOR_BASIS_loop
  refine loop.spec_decr_nat (fun s => 128 - s.2.val)
    (fun s => s.2.val ≤ 128 ∧ ∀ j < s.2.val,
      AdjoinRoot.mk (modPoly 128 135) (natPoly (aval s.1 j)) = N128 (cantorTower 7 j)) _ _ _ ?_
    ⟨hn, hd⟩
  rintro ⟨bs, m⟩ ⟨hm, hdm⟩
  dsimp only at hm hdm ⊢
  unfold ghash.CANTOR_BASIS_loop.body
  step*
  apply WP.spec_bind (tower_image_128_spec i1)
  intro i2 hi2
  step*
  refine ⟨by scalar_tac, fun j hj => ?_, by scalar_tac⟩
  rw [a_post, aval_set _ _ _ (by scalar_tac)]
  by_cases hjm : j = m.val
  · rw [ite_eq_left hjm, hi2, i1_post1, hjm, cantorTower_eq]
  · rw [ite_eq_right hjm]
    exact hdm j (by scalar_tac)

theorem ghash_CANTOR_BASIS_spec : ghash.CANTOR_BASIS ⦃ r => ∀ j < 128,
    AdjoinRoot.mk (modPoly 128 135) (natPoly (aval r j)) = N128 (cantorTower 7 j) ⦄ := by
  unfold ghash.CANTOR_BASIS
  obtain ⟨z, hz, -⟩ :=
    Lib.array_repeat_eq 128#usize core.U128.Insts.CoreCloneClone (fun _ => rfl) 0#u128
  rw [hz, Aeneas.Std.bind_ok]
  exact ghash_cantor_loop_spec z 0#usize (by simp) (fun _ h => absurd h (by simp))

/-- `Ghash128::cantor_basis i` is vector `i` of the Cantor basis, carried by `N`. -/
theorem ghash128_cantor_basis_spec (i : Std.Usize) (hi : i.val < 128) :
    ghash.Ghash128.Insts.P3_binary_fieldTowerTowerLevelU128.cantor_basis i ⦃ r =>
      toQuot (ghash r) = towerToGhash (cantorTower 7 i.val) ⦄ := by
  unfold ghash.Ghash128.Insts.P3_binary_fieldTowerTowerLevelU128.cantor_basis
  have : i < ghash.Ghash128.BITS := by unfold ghash.Ghash128.BITS; scalar_tac
  simp only [massert, this, ↓reduceIte, Aeneas.Std.bind_ok]
  apply WP.spec_bind ghash_CANTOR_BASIS_spec
  intro b hb
  step*
  rw [toQuot_eq_mk, towerToGhash_apply, ← hb i.val hi, ghashIso_mk, i1_post1, aval_eq_getElem]

theorem ghash128_cantor_basis_panic (i : Std.Usize) (hi : 128 ≤ i.val) :
    ghash.Ghash128.Insts.P3_binary_fieldTowerTowerLevelU128.cantor_basis i = .fail .panic := by
  unfold ghash.Ghash128.Insts.P3_binary_fieldTowerTowerLevelU128.cantor_basis
  have : ¬ i < ghash.Ghash128.BITS := by unfold ghash.Ghash128.BITS; scalar_tac
  simp [massert, this]

/-! ## `Poly64` -/

/-- Entry `j` of an array of 64-bit values, as a natural number. -/
def aval64 (a : Std.Array Std.U64 64#usize) (j : ℕ) : ℕ := (a.val.getD j 0#u64).val

theorem aval64_set (a : Std.Array Std.U64 64#usize) (u : Std.Usize) (x : Std.U64)
    (hu : u.val < 64) (j : ℕ) :
    aval64 (a.set u x) j = if j = u.val then x.val else aval64 a j := by
  unfold aval64
  rw [Std.Array.set_val_eq]
  by_cases h : j = u.val
  · subst h
    rw [ite_eq_left rfl, List.getD_eq_getElem?_getD, List.getElem?_set_self (by simpa using hu)]
    rfl
  · rw [ite_eq_right h, List.getD_eq_getElem?_getD, List.getElem?_set_ne (Ne.symm h),
      ← List.getD_eq_getElem?_getD]

theorem poly64_cantor_loop_spec (b : Std.Array Std.U64 64#usize) (n : Std.Usize)
    (hn : n.val ≤ 64)
    (hd : ∀ j < n.val, AdjoinRoot.mk (modPoly 64 27) (natPoly (aval64 b j)) =
      N64 (cantorTower 6 j)) :
    poly64.CANTOR_BASIS_loop b n ⦃ r => ∀ j < 64,
      AdjoinRoot.mk (modPoly 64 27) (natPoly (aval64 r j)) = N64 (cantorTower 6 j) ⦄ := by
  unfold poly64.CANTOR_BASIS_loop
  refine loop.spec_decr_nat (fun s => 64 - s.2.val)
    (fun s => s.2.val ≤ 64 ∧ ∀ j < s.2.val,
      AdjoinRoot.mk (modPoly 64 27) (natPoly (aval64 s.1 j)) = N64 (cantorTower 6 j)) _ _ _ ?_
    ⟨hn, hd⟩
  rintro ⟨bs, m⟩ ⟨hm, hdm⟩
  dsimp only at hm hdm ⊢
  unfold poly64.CANTOR_BASIS_loop.body
  step*
  apply WP.spec_bind (tower_image_64_spec i2)
  intro i3 hi3
  step*
  refine ⟨by scalar_tac, fun j hj => ?_, by scalar_tac⟩
  rw [a_post, aval64_set _ _ _ (by scalar_tac)]
  by_cases hjm : j = m.val
  · have hm64 : m.val < 64 := by scalar_tac
    have hlt := cantorV_lt (k := 6) (by norm_num) (show m.val < 2 ^ 6 by simpa using hm64)
    rw [ite_eq_left hjm, hi3, hjm, cantorTower, towerOf, i2_post, UScalar.cast_val_eq,
      UScalarTy.U64_numBits_eq, i1_post1, cantor_getElem,
      Nat.mod_eq_of_lt (show cantorV m.val < 2 ^ 64 from hlt)]
  · rw [ite_eq_right hjm]
    exact hdm j (by scalar_tac)

theorem poly64_CANTOR_BASIS_spec : poly64.CANTOR_BASIS ⦃ r => ∀ j < 64,
    AdjoinRoot.mk (modPoly 64 27) (natPoly (aval64 r j)) = N64 (cantorTower 6 j) ⦄ := by
  unfold poly64.CANTOR_BASIS
  obtain ⟨z, hz, -⟩ :=
    Lib.array_repeat_eq 64#usize core.U64.Insts.CoreCloneClone (fun _ => rfl) 0#u64
  rw [hz, Aeneas.Std.bind_ok]
  exact poly64_cantor_loop_spec z 0#usize (by simp) (fun _ h => absurd h (by simp))

/-- `Poly64::cantor_basis i` is vector `i` of the Cantor basis, carried by `N`. -/
theorem poly64_cantor_basis_spec (i : Std.Usize) (hi : i.val < 64) :
    poly64.Poly64.Insts.P3_binary_fieldTowerTowerLevelU64.cantor_basis i ⦃ r =>
      toQuot64 r = towerToBF64 (cantorTower 6 i.val) ⦄ := by
  unfold poly64.Poly64.Insts.P3_binary_fieldTowerTowerLevelU64.cantor_basis
  have : i < poly64.Poly64.BITS := by unfold poly64.Poly64.BITS; scalar_tac
  simp only [massert, this, ↓reduceIte, Aeneas.Std.bind_ok]
  apply WP.spec_bind poly64_CANTOR_BASIS_spec
  intro b hb
  step*
  rw [toQuot64_eq, towerToBF64_apply, ← hb i.val hi, algEquivOfEq_mk, i1_post1, aval64,
    List.getD_eq_getElem?_getD, List.getElem?_eq_getElem i1_post, Option.getD_some]

theorem poly64_cantor_basis_panic (i : Std.Usize) (hi : 64 ≤ i.val) :
    poly64.Poly64.Insts.P3_binary_fieldTowerTowerLevelU64.cantor_basis i = .fail .panic := by
  unfold poly64.Poly64.Insts.P3_binary_fieldTowerTowerLevelU64.cantor_basis
  have : ¬ i < poly64.Poly64.BITS := by unfold poly64.Poly64.BITS; scalar_tac
  simp [massert, this]

end Plonky3Lean.Proofs.Binary
