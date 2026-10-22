module

public import Plonky3Lean.Proofs.Field.Binary.LinearTable

@[expose] public section

/-!
# Square roots in the tower, by halves

`linear::sqrt` inverts `linear::square` on a value `a0 + a1 X` of `2^k` bits. Since
`(s0 + s1 X)^2 = (s0^2 + s1^2) + Z (s1^2) X`, it takes `s1 = sqrt(a1 / Z)` and
`s0 = sqrt(a0) + s1`. `linear::div_alpha` divides by `Z`: `mulAlphaNat_divAlphaNat`.

`sqNat_sqrtNat` is the result: `sqrtNat k a` squares to `a`.
-/

open Aeneas Aeneas.Std CoreModels
open p3_binary_field ConcreteBinaryTower
open Plonky3Lean.Lib

namespace Plonky3Lean.Proofs.Binary

/-- `linear::div_alpha` at width `2^k`, on natural numbers. -/
def divAlphaNat : ℕ → ℕ → ℕ
  | 0, a => a
  | k + 1, a => (a >>> 2 ^ k ^^^ mulAlphaNat k (a % 2 ^ 2 ^ k)) ||| (a % 2 ^ 2 ^ k) <<< 2 ^ k

/-- `linear::sqrt` at width `2^k`, on natural numbers. -/
def sqrtNat : ℕ → ℕ → ℕ
  | 0, a => a
  | k + 1, a =>
    (sqrtNat k (a % 2 ^ 2 ^ k) ^^^ sqrtNat k (divAlphaNat k (a >>> 2 ^ k))) |||
      sqrtNat k (divAlphaNat k (a >>> 2 ^ k)) <<< 2 ^ k

/-! ## Halves -/

theorem or_shiftLeft_mod {u v n : ℕ} (hu : u < 2 ^ n) : (u ||| v <<< n) % 2 ^ n = u := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_mod_two_pow, Nat.testBit_or, Nat.testBit_shiftLeft]
  by_cases h : i < n
  · simp [h]
  · simp [h, Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hu (Nat.pow_le_pow_right (by norm_num)
      (not_lt.mp h)))]

theorem or_shiftLeft_shiftRight {u v n : ℕ} (hu : u < 2 ^ n) : (u ||| v <<< n) >>> n = v := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_shiftRight, Nat.testBit_or, Nat.testBit_shiftLeft]
  rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hu (Nat.pow_le_pow_right (by norm_num)
    (by omega)))]
  simp

theorem mod_or_shiftRight_shiftLeft (a n : ℕ) : a % 2 ^ n ||| (a >>> n) <<< n = a := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_mod_two_pow, Nat.testBit_or, Nat.testBit_shiftLeft,
    Nat.testBit_shiftRight]
  by_cases h : i < n
  · simp [h]
  · simp only [h, decide_false, Bool.false_and, Bool.false_or, ge_iff_le, not_lt.mp h,
      decide_true, Bool.true_and]
    congr 1
    omega

/-- Two halves that fit join into a value of the level above. -/
theorem or_shiftLeft_lt {k u v : ℕ} (hu : u < 2 ^ 2 ^ k) (hv : v < 2 ^ 2 ^ k) :
    u ||| v <<< 2 ^ k < 2 ^ 2 ^ (k + 1) :=
  Nat.or_lt_two_pow (lt_of_lt_of_le hu (Nat.pow_le_pow_right (by norm_num)
    (Nat.pow_le_pow_right (by norm_num) (by omega)))) (shiftLeft_lt_of_lt hv)

/-! ## Dividing by the generator -/

theorem divAlphaNat_lt : ∀ {k a : ℕ}, a < 2 ^ 2 ^ k → divAlphaNat k a < 2 ^ 2 ^ k
  | 0, _, ha => ha
  | _ + 1, _, ha =>
    or_shiftLeft_lt (Nat.xor_lt_two_pow (shiftRight_lt_of_lt ha)
      (mulAlphaNat_lt (Nat.mod_lt _ (by positivity)))) (Nat.mod_lt _ (by positivity))

/-- `div_alpha` undoes `mul_alpha`. -/
theorem mulAlphaNat_divAlphaNat : ∀ {k a : ℕ}, a < 2 ^ 2 ^ k →
    mulAlphaNat k (divAlphaNat k a) = a
  | 0, _, _ => rfl
  | k + 1, a, ha => by
    have hlo : a % 2 ^ 2 ^ k < 2 ^ 2 ^ k := Nat.mod_lt _ (by positivity)
    have hx : a >>> 2 ^ k ^^^ mulAlphaNat k (a % 2 ^ 2 ^ k) < 2 ^ 2 ^ k :=
      Nat.xor_lt_two_pow (shiftRight_lt_of_lt ha) (mulAlphaNat_lt hlo)
    rw [divAlphaNat, mulAlphaNat, or_shiftLeft_shiftRight hx, or_shiftLeft_mod hx,
      Nat.xor_assoc, Nat.xor_self, Nat.xor_zero, mod_or_shiftRight_shiftLeft]

/-! ## Square roots -/

theorem sqrtNat_lt : ∀ {k a : ℕ}, a < 2 ^ 2 ^ k → sqrtNat k a < 2 ^ 2 ^ k
  | 0, _, ha => ha
  | _ + 1, _, ha => by
    have hh := sqrtNat_lt (divAlphaNat_lt (shiftRight_lt_of_lt ha))
    exact or_shiftLeft_lt (Nat.xor_lt_two_pow (sqrtNat_lt (Nat.mod_lt _ (by positivity))) hh) hh

/-- `sqrtNat k a` squares to `a`. -/
theorem sqNat_sqrtNat : ∀ {k a : ℕ}, a < 2 ^ 2 ^ k → sqNat k (sqrtNat k a) = a
  | 0, _, _ => rfl
  | k + 1, a, ha => by
    have hlo : a % 2 ^ 2 ^ k < 2 ^ 2 ^ k := Nat.mod_lt _ (by positivity)
    have hd := divAlphaNat_lt (shiftRight_lt_of_lt ha)
    have hh := sqrtNat_lt hd
    have hs := sqrtNat_lt hlo
    have hx := Nat.xor_lt_two_pow hs hh
    rw [sqrtNat, sqNat, or_shiftLeft_mod hx, or_shiftLeft_shiftRight hx, sqNat_xor hs hh,
      sqNat_sqrtNat hlo, sqNat_sqrtNat hd, Nat.xor_assoc, Nat.xor_self, Nat.xor_zero,
      mulAlphaNat_divAlphaNat (shiftRight_lt_of_lt ha), mod_or_shiftRight_shiftLeft]

/-- Squaring is injective: in characteristic 2, `u^2 = v^2` gives `(u + v)^2 = 0`. -/
theorem eq_of_sqNat_eq {k u v : ℕ} (hu : u < 2 ^ 2 ^ k) (hv : v < 2 ^ 2 ^ k)
    (h : sqNat k u = sqNat k v) : u = v := by
  have h2 : towerMul k (u ^^^ v) (u ^^^ v) = 0 := by
    rw [towerMul_sq_xor k hu hv, ← sqNat_eq k hu, ← sqNat_eq k hv, h, Nat.xor_self]
  set x : ConcreteBTField k := fromNat (u ^^^ v)
  have hx : x.toNat = u ^^^ v := by
    rw [ConcreteBTField.toNat_fromNat, Nat.mod_eq_of_lt (Nat.xor_lt_two_pow hu hv)]
  have hxx : x * x = 0 := by
    apply ConcreteBTField.toNat_injective
    rw [show x * x = concrete_mul x x from rfl, toNat_concrete_mul, hx, h2]
    rfl
  have h0 : u ^^^ v = 0 := by rw [← hx, mul_self_eq_zero.mp hxx]; rfl
  have h3 := congrArg (· ^^^ v) h0
  simpa [Nat.xor_assoc] using h3

theorem sqrtNat_xor {K x y : ℕ} (hx : x < 2 ^ 2 ^ K) (hy : y < 2 ^ 2 ^ K) :
    sqrtNat K (x ^^^ y) = sqrtNat K x ^^^ sqrtNat K y := by
  have hxy := Nat.xor_lt_two_pow hx hy
  apply eq_of_sqNat_eq (sqrtNat_lt hxy) (Nat.xor_lt_two_pow (sqrtNat_lt hx) (sqrtNat_lt hy))
  rw [sqNat_xor (sqrtNat_lt hx) (sqrtNat_lt hy), sqNat_sqrtNat hxy, sqNat_sqrtNat hx,
    sqNat_sqrtNat hy]

theorem sqrtNat_zero (K : ℕ) : sqrtNat K 0 = 0 :=
  eq_of_sqNat_eq (sqrtNat_lt (by positivity)) (by positivity)
    (by rw [sqNat_sqrtNat (by positivity), sqNat_zero])

theorem additive_sqrtNat (K : ℕ) : Additive (sqrtNat K) (2 ^ K) where
  zero := sqrtNat_zero K
  add x y hx hy h := by rw [or_eq_xor_of_and_eq_zero h, sqrtNat_xor hx hy]

/-! ## The extracted recursions -/

/-- `a & (u128::MAX >> (128 - 2^k))` keeps the low `2^k` bits. -/
theorem low_mask_val {k : ℕ} (hk : 2 ^ k ≤ 64) {a i3 : Std.U128} {i2 : Std.Usize}
    (hi2 : i2.val = 128 - 2 ^ k) (hi3 : i3.val = U128.rMax >>> i2.val) :
    (a &&& i3).val = a.val % 2 ^ 2 ^ k := by
  rw [UScalar.val_and, hi3, hi2, show U128.rMax = 2 ^ 128 - 1 from rfl, two_pow_sub_one_shiftRight,
    Nat.sub_sub_self (by omega : 2 ^ k ≤ 128), Nat.and_two_pow_sub_one_eq_mod]

theorem div_alpha_spec : ∀ (k : ℕ), k ≤ 7 → ∀ (a : Std.U128), a.val < 2 ^ 2 ^ k →
    linear.div_alpha a (widthUsize k) ⦃ r => r.val = divAlphaNat k a.val ⦄
  | 0, _, a, _ => by
    unfold linear.div_alpha
    rw [ite_eq_left (UScalar.eq_of_val_eq (by rw [widthUsize_val (by omega)]; rfl)), WP.spec_ok]
    rfl
  | k + 1, hk, a, ha => by
    have hw := widthUsize_val hk
    have hw' := widthUsize_val (k := k) (by omega)
    have hk64 : 2 ^ k ≤ 64 := by
      calc 2 ^ k ≤ 2 ^ 6 := Nat.pow_le_pow_right (by norm_num) (by omega)
        _ = 64 := by norm_num
    have hpos : 0 < 2 ^ k := by positivity
    have hsucc : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [pow_succ]; ring
    unfold linear.div_alpha
    step*
    have hh : half = widthUsize k := widthUsize_half hk half_post
    subst hh
    have hmask : i1.val = 2 ^ 2 ^ k - 1 := by
      rw [i1_post, i_post, hw', show U128.rMax = 2 ^ 128 - 1 from rfl, two_pow_sub_one_shiftRight]
      congr 2
      omega
    have hlo : lo.val = a.val % 2 ^ 2 ^ k := by
      rw [lo_post, UScalar.val_and, hmask, Nat.and_two_pow_sub_one_eq_mod]
    have hlo' : lo.val < 2 ^ 2 ^ k := hlo ▸ Nat.mod_lt _ (by positivity)
    refine WP.spec_bind (mul_alpha_spec k (by omega) lo hlo') fun r hr => ?_
    step*
    have h128 : 2 ^ 2 ^ (k + 1) ≤ 2 ^ 128 := Nat.pow_le_pow_right (by norm_num) (by
      calc 2 ^ (k + 1) ≤ 2 ^ 7 := Nat.pow_le_pow_right (by norm_num) hk
        _ = 128 := by norm_num)
    rw [UScalar.val_or, i3_post, UScalar.val_xor, i4_post, hw',
      show U128.size = 2 ^ 128 by simp [U128.size_def, U128.numBits_def],
      Nat.mod_eq_of_lt (lt_of_lt_of_le (shiftLeft_lt_of_lt hlo') h128), hr, hlo, hi_post, hw',
      divAlphaNat]

theorem sqrt_spec : ∀ (k : ℕ), k ≤ 7 → ∀ (a : Std.U128), a.val < 2 ^ 2 ^ k →
    linear.sqrt a (widthUsize k) ⦃ r => r.val = sqrtNat k a.val ⦄
  | 0, _, a, _ => by
    unfold linear.sqrt
    rw [ite_eq_left (UScalar.eq_of_val_eq (by rw [widthUsize_val (by omega)]; rfl)), WP.spec_ok]
    rfl
  | k + 1, hk, a, ha => by
    have hw := widthUsize_val hk
    have hw' := widthUsize_val (k := k) (by omega)
    have hk64 : 2 ^ k ≤ 64 := by
      calc 2 ^ k ≤ 2 ^ 6 := Nat.pow_le_pow_right (by norm_num) (by omega)
        _ = 64 := by norm_num
    have hpos : 0 < 2 ^ k := by positivity
    have hsucc : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [pow_succ]; ring
    unfold linear.sqrt
    step*
    have hh : half = widthUsize k := widthUsize_half hk half_post
    subst hh
    have hi : i.val < 2 ^ 2 ^ k := by rw [i_post, hw']; exact shiftRight_lt_of_lt ha
    refine WP.spec_bind (div_alpha_spec k (by omega) i hi) fun i1 hi1 => ?_
    have hi1' : i1.val < 2 ^ 2 ^ k := hi1 ▸ divAlphaNat_lt hi
    refine WP.spec_bind (sqrt_spec k (by omega) i1 hi1') fun hi' hhi => ?_
    step*
    case a => rw [i4_post, low_mask_val hk64 (by rw [i2_post, hw']) i3_post]; exact Nat.mod_lt _ (by positivity)
    have hlo : i4.val = a.val % 2 ^ 2 ^ k := by
      rw [i4_post, low_mask_val hk64 (by rw [i2_post, hw']) i3_post]
    have h128 : 2 ^ 2 ^ (k + 1) ≤ 2 ^ 128 := Nat.pow_le_pow_right (by norm_num) (by
      calc 2 ^ (k + 1) ≤ 2 ^ 7 := Nat.pow_le_pow_right (by norm_num) hk
        _ = 128 := by norm_num)
    have hhi' : hi'.val < 2 ^ 2 ^ k := hhi ▸ sqrtNat_lt hi1'
    rw [UScalar.val_or, lo_post, UScalar.val_xor, i6_post, hw',
      show U128.size = 2 ^ 128 by simp [U128.size_def, U128.numBits_def],
      Nat.mod_eq_of_lt (lt_of_lt_of_le (shiftLeft_lt_of_lt hhi') h128), i5_post, hhi, hi1, hlo,
      i_post, hw', sqrtNat]

/-! ## `sqrt_16` -/

theorem sqrt_16_table_inner (wide : Std.Array (Std.Array Std.U128 256#usize) 2#usize)
    (i : Std.Usize) (hi : i.val < 2) (t : Std.Array (Std.Array Std.U16 256#usize) 2#usize)
    (j : Std.Usize) (hj : j.val ≤ 256) (hdone : ∀ w < j.val, cellOf t i.val w = cell wide i.val w % 2 ^ 16) :
    linear.sqrt_16.TABLE_loop0_loop0 wide t i j ⦃ t' =>
      (∀ w < 256, cellOf t' i.val w = cell wide i.val w % 2 ^ 16) ∧
      ∀ i', i' ≠ i.val → ∀ w, cellOf t' i' w = cellOf t i' w ⦄ := by
  unfold linear.sqrt_16.TABLE_loop0_loop0
  refine loop.spec_decr_nat (fun p => 256 - p.2.val)
    (fun p => p.2.val ≤ 256 ∧ (∀ w < p.2.val, cellOf p.1 i.val w = cell wide i.val w % 2 ^ 16) ∧
      ∀ i', i' ≠ i.val → ∀ w, cellOf p.1 i' w = cellOf t i' w) _ _ _ ?_
    ⟨hj, hdone, fun _ _ _ => rfl⟩
  rintro ⟨tb, k⟩ ⟨hk, hd, ho⟩
  unfold linear.sqrt_16.TABLE_loop0_loop0.body
  step*
  simp only at hk hd ho
  have hk' : k.val < 256 := by scalar_tac
  have hlen : i.val < tb.length := by simpa using hi
  have hi1 : i1.val = cell wide i.val k.val := by
    subst a_post1
    rw [i1_post1]
    simp only [cell, List.getElem?_eq_getElem a_post, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem i1_post, Option.getD_some]
  have hcell : ∀ i' w, cellOf (index_mut_back a2) i' w =
      if i' = i.val ∧ w = k.val then i2.val else cellOf tb i' w := by
    intro i' w
    rw [index_mut_back_post, a2_post, a1_post1, cellOf_set _ _ _ _ hlen hk']
  refine ⟨by omega, ?_, ?_, by omega⟩
  · intro w hw
    rw [hcell]
    by_cases hwk : w = k.val
    · subst hwk
      rw [ite_eq_left ⟨rfl, rfl⟩, i2_post, UScalar.cast_val_eq, UScalarTy.U16_numBits_eq, hi1]
    · rw [ite_eq_right (fun h => hwk h.2)]
      exact hd w (by omega)
  · intro i' hi' w
    rw [hcell, ite_eq_right (fun h => hi' h.1)]
    exact ho i' hi' w

theorem sqrt_16_table_outer (wide : Std.Array (Std.Array Std.U128 256#usize) 2#usize)
    (t : Std.Array (Std.Array Std.U16 256#usize) 2#usize) (i : Std.Usize) (hi : i.val ≤ 2)
    (hdone : ∀ i' < i.val, ∀ w < 256, cellOf t i' w = cell wide i' w % 2 ^ 16) :
    linear.sqrt_16.TABLE_loop0 wide t i ⦃ t' =>
      ∀ i' < 2, ∀ w < 256, cellOf t' i' w = cell wide i' w % 2 ^ 16 ⦄ := by
  unfold linear.sqrt_16.TABLE_loop0
  refine loop.spec_decr_nat (fun p => 2 - p.2.val)
    (fun p => p.2.val ≤ 2 ∧ ∀ i' < p.2.val, ∀ w < 256, cellOf p.1 i' w = cell wide i' w % 2 ^ 16)
    _ _ _ ?_ ⟨hi, hdone⟩
  rintro ⟨tb, k⟩ ⟨hk, hd⟩
  unfold linear.sqrt_16.TABLE_loop0.body
  step*
  simp only at hk hd
  have hk' : k.val < 2 := by scalar_tac
  refine WP.spec_bind (sqrt_16_table_inner wide k hk' tb 0#usize (by simp)
    (fun w hw => absurd hw (by simp))) fun t' ⟨hrow, ho⟩ => ?_
  step*
  refine ⟨by omega, ?_, by omega⟩
  intro i' hi' w hw
  by_cases h : i' = k.val
  · subst h; exact hrow w hw
  · rw [ho i' h w]; exact hd i' (by omega) w hw

/-- `sqrt_16`'s table: entry `w` of row `i` is the square root of `w` placed at byte `i`. -/
theorem sqrt_16_TABLE_spec :
    linear.sqrt_16.TABLE ⦃ T => ∀ i < 2, ∀ w < 256, cellOf T i w = sqrtNat 4 (w <<< (8 * i)) ⦄ := by
  unfold linear.sqrt_16.TABLE
  have hspec : ∀ bit : Std.U128, bit.val < 2 ^ (8 * (2#usize : Std.Usize).val) →
      (if true then do
          let i3 ← (2#usize : Std.Usize) * 8#usize
          linear.sqrt bit i3
        else do
          let i3 ← (2#usize : Std.Usize) * 8#usize
          linear.square bit i3) ⦃ r => r.val = sqrtNat 4 bit.val ⦄ := by
    intro bit hbit
    rw [ite_eq_left rfl]
    step*
    have h16 : i3 = widthUsize 4 :=
      UScalar.eq_of_val_eq (by rw [i3_post, widthUsize_val (by norm_num)]; rfl)
    subst h16
    exact sqrt_spec 4 (by norm_num) bit (by simpa using hbit)
  refine WP.spec_bind (unary_table_spec (B := 2#usize) (sqrtNat 4) (by simpa using additive_sqrtNat 4)
    (by simp) true hspec) fun wide hwide => ?_
  obtain ⟨a, ha, -⟩ :=
    Lib.array_repeat_eq 256#usize core.U16.Insts.CoreCloneClone (fun _ => rfl) 0#u16
  rw [ha, Aeneas.Std.bind_ok]
  obtain ⟨tb, htb, -⟩ := Lib.array_repeat_eq 2#usize
    (core.Array.Insts.CoreCloneClone 256#usize core.U16.Insts.CoreCloneClone)
    (array_clone_eq _ (fun _ => rfl)) a
  rw [htb, Aeneas.Std.bind_ok]
  refine WP.spec_mono (sqrt_16_table_outer wide tb 0#usize (by simp)
    (fun _ h => absurd h (by simp))) fun T hT => ?_
  intro i hi w hw
  have hi2 : i < (2#usize : Std.Usize).val := by simpa using hi
  rw [hT i hi w hw, hwide i hi2 w hw, Nat.mod_eq_of_lt]
  have hlt : w <<< (8 * i) < 2 ^ 2 ^ 4 := by
    calc w <<< (8 * i) < 2 ^ (8 * i + 8) := shiftLeft_lt_two_pow (by omega)
      _ ≤ 2 ^ 2 ^ 4 := Nat.pow_le_pow_right (by norm_num) (by omega)
  exact sqrtNat_lt hlt

theorem sqrt_16_loop_spec (T : Std.Array (Std.Array Std.U16 256#usize) 2#usize)
    (hT : ∀ i < 2, ∀ w < 256, cellOf T i w = sqrtNat 4 (w <<< (8 * i))) (value : Std.U16)
    (it : CoreModels.core.iter.adapters.enumerate.Enumerate (CoreModels.core.slice.iter.Iter
      (Std.Array Std.U16 256#usize)))
    (result : Std.U16) (hit : iterList it.iter = T.val.drop it.count.val) (hc : it.count.val ≤ 2)
    (hres : result.val = sqrtNat 4 (value.val % 2 ^ (8 * it.count.val))) :
    linear.sqrt_16_loop it value result ⦃ r => r.val = sqrtNat 4 value.val ⦄ := by
  unfold linear.sqrt_16_loop
  refine loop.spec_decr_nat (fun p => 2 - p.1.count.val)
    (fun p => iterList p.1.iter = T.val.drop p.1.count.val ∧ p.1.count.val ≤ 2 ∧
      p.2.val = sqrtNat 4 (value.val % 2 ^ (8 * p.1.count.val))) _ _ _ ?_ ⟨hit, hc, hres⟩
  rintro ⟨it, res⟩ ⟨hit, hc, hres⟩
  unfold linear.sqrt_16_loop.body
  simp only at hit hc hres
  have hlenT : T.val.length = 2 := by simp
  by_cases hc2 : it.count.val < 2
  · have hcons : iterList it.iter = T.val[it.count.val] :: T.val.drop (it.count.val + 1) := by
      rw [hit, List.drop_eq_getElem_cons (by omega)]
    obtain ⟨c', hc', hnext⟩ := enumerate_next_cons it hcons (by
      have : (2 : ℕ) ≤ Usize.max := by scalar_tac
      omega)
    dsimp only
    rw [hnext]
    simp only [Aeneas.Std.bind_ok]
    have hc8 : (8 * it.count.val) < 16 := by omega
    step*
    · have h3 : i3.val ≤ 255 := by
        rw [i3_post, UScalar.val_and]; exact Nat.and_le_right
      rw [i4_post, UScalar.cast_val_eq, Nat.mod_eq_of_lt (by
        rcases System.Platform.numBits_eq with e | e <;> simp only [UScalarTy.Usize_numBits_eq, e] <;> omega)]
      simp; omega
    · have hbyte : i3.val = (value.val >>> (8 * it.count.val)) % 2 ^ 8 := by
        rw [i3_post, UScalar.val_and, i2_post, i1_post, show (255#u16).val = 2 ^ 8 - 1 from rfl,
          Nat.and_two_pow_sub_one_eq_mod]
      have h3 : i3.val < 256 := hbyte ▸ Nat.mod_lt _ (by norm_num)
      have hi4 : i4.val = i3.val := by
        rw [i4_post, UScalar.cast_val_eq, Nat.mod_eq_of_lt (by
          rcases System.Platform.numBits_eq with e | e <;> simp only [UScalarTy.Usize_numBits_eq, e] <;> omega)]
      have hi5 : i5.val = sqrtNat 4 (i3.val <<< (8 * it.count.val)) := by
        rw [← hi4, ← hT it.count.val hc2 i4.val (by omega)]
        unfold cellOf
        rw [List.getElem?_eq_getElem (by omega)]
        dsimp only
        rw [List.getElem?_eq_getElem i5_post, i5_post1]
      have hv16 : value.val < 2 ^ 16 := by have := value.hBounds; simpa using this
      have hx : value.val % 2 ^ (8 * it.count.val) < 2 ^ 2 ^ 4 :=
        lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos _))
          (Nat.pow_le_pow_right (by norm_num) (by omega))
      have hy : i3.val <<< (8 * it.count.val) < 2 ^ 2 ^ 4 :=
        lt_of_lt_of_le (shiftLeft_lt_two_pow (b := 8) (by omega))
          (Nat.pow_le_pow_right (by norm_num) (by omega))
      refine ⟨by rw [iterList_iterOf, hc'], by omega, ?_, by omega⟩
      rw [result1_post, UScalar.val_xor, hres, hi5, hc', ← sqrtNat_xor hx hy, hbyte, mul_add, mul_one,
        mod_two_pow_add_byte value.val (8 * it.count.val)]
  · have hnil : iterList it.iter = [] := by rw [hit]; exact List.drop_of_length_le (by omega)
    dsimp only
    simp only [CoreModels.core.iter.adapters.enumerate.Enumerate.Insts.CoreIterTraitsIteratorIteratorPairUsizeClause0_Item.next]
    rw [slice_iter_next_nil it.iter hnil]
    simp only [Aeneas.Std.bind_ok]
    have hc2' : it.count.val = 2 := by omega
    have hv16 : value.val < 2 ^ 16 := by have := value.hBounds; simpa using this
    step*
    rw [hres, hc2', Nat.mod_eq_of_lt hv16]

/-- `sqrt_16` takes square roots in the tower's `GF(2^16)`: it is `sqrtNat 4`. -/
theorem sqrt_16_spec (value : Std.U16) :
    linear.sqrt_16 value ⦃ r => r.val = sqrtNat 4 value.val ⦄ := by
  have hv16 : value.val < 2 ^ 2 ^ 4 := by have := value.hBounds; simpa using this
  unfold linear.sqrt_16
  refine WP.spec_bind sqrt_16_TABLE_spec fun T hT => ?_
  rw [array_as_slice_eq, Aeneas.Std.bind_ok, slice_iter_eq, Aeneas.Std.bind_ok,
    enumerate_default_eq, Aeneas.Std.bind_ok]
  apply sqrt_16_loop_spec T hT value
  · rw [iterList_iterOfSlice]; simp [Std.Array.to_slice]
  · simp
  · rw [show (0#u16 : Std.U16).val = 0 from rfl, show (0#usize : Std.Usize).val = 0 from rfl,
      mul_zero, pow_zero, Nat.mod_one, sqrtNat_zero]

/-! ## `sqrt_32` -/

theorem sqrt_32_table_inner (wide : Std.Array (Std.Array Std.U128 256#usize) 4#usize)
    (i : Std.Usize) (hi : i.val < 4) (t : Std.Array (Std.Array Std.U32 256#usize) 4#usize)
    (j : Std.Usize) (hj : j.val ≤ 256) (hdone : ∀ w < j.val, cellOf t i.val w = cell wide i.val w % 2 ^ 32) :
    linear.sqrt_32.TABLE_loop0_loop0 wide t i j ⦃ t' =>
      (∀ w < 256, cellOf t' i.val w = cell wide i.val w % 2 ^ 32) ∧
      ∀ i', i' ≠ i.val → ∀ w, cellOf t' i' w = cellOf t i' w ⦄ := by
  unfold linear.sqrt_32.TABLE_loop0_loop0
  refine loop.spec_decr_nat (fun p => 256 - p.2.val)
    (fun p => p.2.val ≤ 256 ∧ (∀ w < p.2.val, cellOf p.1 i.val w = cell wide i.val w % 2 ^ 32) ∧
      ∀ i', i' ≠ i.val → ∀ w, cellOf p.1 i' w = cellOf t i' w) _ _ _ ?_
    ⟨hj, hdone, fun _ _ _ => rfl⟩
  rintro ⟨tb, k⟩ ⟨hk, hd, ho⟩
  unfold linear.sqrt_32.TABLE_loop0_loop0.body
  step*
  simp only at hk hd ho
  have hk' : k.val < 256 := by scalar_tac
  have hlen : i.val < tb.length := by simpa using hi
  have hi1 : i1.val = cell wide i.val k.val := by
    subst a_post1
    rw [i1_post1]
    simp only [cell, List.getElem?_eq_getElem a_post, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem i1_post, Option.getD_some]
  have hcell : ∀ i' w, cellOf (index_mut_back a2) i' w =
      if i' = i.val ∧ w = k.val then i2.val else cellOf tb i' w := by
    intro i' w
    rw [index_mut_back_post, a2_post, a1_post1, cellOf_set _ _ _ _ hlen hk']
  refine ⟨by omega, ?_, ?_, by omega⟩
  · intro w hw
    rw [hcell]
    by_cases hwk : w = k.val
    · subst hwk
      rw [ite_eq_left ⟨rfl, rfl⟩, i2_post, UScalar.cast_val_eq, UScalarTy.U32_numBits_eq, hi1]
    · rw [ite_eq_right (fun h => hwk h.2)]
      exact hd w (by omega)
  · intro i' hi' w
    rw [hcell, ite_eq_right (fun h => hi' h.1)]
    exact ho i' hi' w

theorem sqrt_32_table_outer (wide : Std.Array (Std.Array Std.U128 256#usize) 4#usize)
    (t : Std.Array (Std.Array Std.U32 256#usize) 4#usize) (i : Std.Usize) (hi : i.val ≤ 4)
    (hdone : ∀ i' < i.val, ∀ w < 256, cellOf t i' w = cell wide i' w % 2 ^ 32) :
    linear.sqrt_32.TABLE_loop0 wide t i ⦃ t' =>
      ∀ i' < 4, ∀ w < 256, cellOf t' i' w = cell wide i' w % 2 ^ 32 ⦄ := by
  unfold linear.sqrt_32.TABLE_loop0
  refine loop.spec_decr_nat (fun p => 4 - p.2.val)
    (fun p => p.2.val ≤ 4 ∧ ∀ i' < p.2.val, ∀ w < 256, cellOf p.1 i' w = cell wide i' w % 2 ^ 32)
    _ _ _ ?_ ⟨hi, hdone⟩
  rintro ⟨tb, k⟩ ⟨hk, hd⟩
  unfold linear.sqrt_32.TABLE_loop0.body
  step*
  simp only at hk hd
  have hk' : k.val < 4 := by scalar_tac
  refine WP.spec_bind (sqrt_32_table_inner wide k hk' tb 0#usize (by simp)
    (fun w hw => absurd hw (by simp))) fun t' ⟨hrow, ho⟩ => ?_
  step*
  refine ⟨by omega, ?_, by omega⟩
  intro i' hi' w hw
  by_cases h : i' = k.val
  · subst h; exact hrow w hw
  · rw [ho i' h w]; exact hd i' (by omega) w hw

/-- `sqrt_32`'s table: entry `w` of row `i` is the square root of `w` placed at byte `i`. -/
theorem sqrt_32_TABLE_spec :
    linear.sqrt_32.TABLE ⦃ T => ∀ i < 4, ∀ w < 256, cellOf T i w = sqrtNat 5 (w <<< (8 * i)) ⦄ := by
  unfold linear.sqrt_32.TABLE
  have hspec : ∀ bit : Std.U128, bit.val < 2 ^ (8 * (4#usize : Std.Usize).val) →
      (if true then do
          let i3 ← (4#usize : Std.Usize) * 8#usize
          linear.sqrt bit i3
        else do
          let i3 ← (4#usize : Std.Usize) * 8#usize
          linear.square bit i3) ⦃ r => r.val = sqrtNat 5 bit.val ⦄ := by
    intro bit hbit
    rw [ite_eq_left rfl]
    step*
    have h16 : i3 = widthUsize 5 :=
      UScalar.eq_of_val_eq (by rw [i3_post, widthUsize_val (by norm_num)]; rfl)
    subst h16
    exact sqrt_spec 5 (by norm_num) bit (by simpa using hbit)
  refine WP.spec_bind (unary_table_spec (B := 4#usize) (sqrtNat 5) (by simpa using additive_sqrtNat 5)
    (by simp) true hspec) fun wide hwide => ?_
  obtain ⟨a, ha, -⟩ :=
    Lib.array_repeat_eq 256#usize core.U32.Insts.CoreCloneClone (fun _ => rfl) 0#u32
  rw [ha, Aeneas.Std.bind_ok]
  obtain ⟨tb, htb, -⟩ := Lib.array_repeat_eq 4#usize
    (core.Array.Insts.CoreCloneClone 256#usize core.U32.Insts.CoreCloneClone)
    (array_clone_eq _ (fun _ => rfl)) a
  rw [htb, Aeneas.Std.bind_ok]
  refine WP.spec_mono (sqrt_32_table_outer wide tb 0#usize (by simp)
    (fun _ h => absurd h (by simp))) fun T hT => ?_
  intro i hi w hw
  have hi2 : i < (4#usize : Std.Usize).val := by simpa using hi
  rw [hT i hi w hw, hwide i hi2 w hw, Nat.mod_eq_of_lt]
  have hlt : w <<< (8 * i) < 2 ^ 2 ^ 5 := by
    calc w <<< (8 * i) < 2 ^ (8 * i + 8) := shiftLeft_lt_two_pow (by omega)
      _ ≤ 2 ^ 2 ^ 5 := Nat.pow_le_pow_right (by norm_num) (by omega)
  exact sqrtNat_lt hlt

theorem sqrt_32_loop_spec (T : Std.Array (Std.Array Std.U32 256#usize) 4#usize)
    (hT : ∀ i < 4, ∀ w < 256, cellOf T i w = sqrtNat 5 (w <<< (8 * i))) (value : Std.U32)
    (it : CoreModels.core.iter.adapters.enumerate.Enumerate (CoreModels.core.slice.iter.Iter
      (Std.Array Std.U32 256#usize)))
    (result : Std.U32) (hit : iterList it.iter = T.val.drop it.count.val) (hc : it.count.val ≤ 4)
    (hres : result.val = sqrtNat 5 (value.val % 2 ^ (8 * it.count.val))) :
    linear.sqrt_32_loop it value result ⦃ r => r.val = sqrtNat 5 value.val ⦄ := by
  unfold linear.sqrt_32_loop
  refine loop.spec_decr_nat (fun p => 4 - p.1.count.val)
    (fun p => iterList p.1.iter = T.val.drop p.1.count.val ∧ p.1.count.val ≤ 4 ∧
      p.2.val = sqrtNat 5 (value.val % 2 ^ (8 * p.1.count.val))) _ _ _ ?_ ⟨hit, hc, hres⟩
  rintro ⟨it, res⟩ ⟨hit, hc, hres⟩
  unfold linear.sqrt_32_loop.body
  simp only at hit hc hres
  have hlenT : T.val.length = 4 := by simp
  by_cases hc2 : it.count.val < 4
  · have hcons : iterList it.iter = T.val[it.count.val] :: T.val.drop (it.count.val + 1) := by
      rw [hit, List.drop_eq_getElem_cons (by omega)]
    obtain ⟨c', hc', hnext⟩ := enumerate_next_cons it hcons (by
      have : (4 : ℕ) ≤ Usize.max := by scalar_tac
      omega)
    dsimp only
    rw [hnext]
    simp only [Aeneas.Std.bind_ok]
    have hc8 : (8 * it.count.val) < 32 := by omega
    step*
    · have h3 : i3.val ≤ 255 := by
        rw [i3_post, UScalar.val_and]; exact Nat.and_le_right
      rw [i4_post, UScalar.cast_val_eq, Nat.mod_eq_of_lt (by
        rcases System.Platform.numBits_eq with e | e <;> simp only [UScalarTy.Usize_numBits_eq, e] <;> omega)]
      simp; omega
    · have hbyte : i3.val = (value.val >>> (8 * it.count.val)) % 2 ^ 8 := by
        rw [i3_post, UScalar.val_and, i2_post, i1_post, show (255#u32).val = 2 ^ 8 - 1 from rfl,
          Nat.and_two_pow_sub_one_eq_mod]
      have h3 : i3.val < 256 := hbyte ▸ Nat.mod_lt _ (by norm_num)
      have hi4 : i4.val = i3.val := by
        rw [i4_post, UScalar.cast_val_eq, Nat.mod_eq_of_lt (by
          rcases System.Platform.numBits_eq with e | e <;> simp only [UScalarTy.Usize_numBits_eq, e] <;> omega)]
      have hi5 : i5.val = sqrtNat 5 (i3.val <<< (8 * it.count.val)) := by
        rw [← hi4, ← hT it.count.val hc2 i4.val (by omega)]
        unfold cellOf
        rw [List.getElem?_eq_getElem (by omega)]
        dsimp only
        rw [List.getElem?_eq_getElem i5_post, i5_post1]
      have hv16 : value.val < 2 ^ 32 := by have := value.hBounds; simpa using this
      have hx : value.val % 2 ^ (8 * it.count.val) < 2 ^ 2 ^ 5 :=
        lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos _))
          (Nat.pow_le_pow_right (by norm_num) (by omega))
      have hy : i3.val <<< (8 * it.count.val) < 2 ^ 2 ^ 5 :=
        lt_of_lt_of_le (shiftLeft_lt_two_pow (b := 8) (by omega))
          (Nat.pow_le_pow_right (by norm_num) (by omega))
      refine ⟨by rw [iterList_iterOf, hc'], by omega, ?_, by omega⟩
      rw [result1_post, UScalar.val_xor, hres, hi5, hc', ← sqrtNat_xor hx hy, hbyte, mul_add, mul_one,
        mod_two_pow_add_byte value.val (8 * it.count.val)]
  · have hnil : iterList it.iter = [] := by rw [hit]; exact List.drop_of_length_le (by omega)
    dsimp only
    simp only [CoreModels.core.iter.adapters.enumerate.Enumerate.Insts.CoreIterTraitsIteratorIteratorPairUsizeClause0_Item.next]
    rw [slice_iter_next_nil it.iter hnil]
    simp only [Aeneas.Std.bind_ok]
    have hc2' : it.count.val = 4 := by omega
    have hv16 : value.val < 2 ^ 32 := by have := value.hBounds; simpa using this
    step*
    rw [hres, hc2', Nat.mod_eq_of_lt hv16]

/-- `sqrt_32` takes square roots in the tower's `GF(2^32)`: it is `sqrtNat 5`. -/
theorem sqrt_32_spec (value : Std.U32) :
    linear.sqrt_32 value ⦃ r => r.val = sqrtNat 5 value.val ⦄ := by
  have hv16 : value.val < 2 ^ 2 ^ 5 := by have := value.hBounds; simpa using this
  unfold linear.sqrt_32
  refine WP.spec_bind sqrt_32_TABLE_spec fun T hT => ?_
  rw [array_as_slice_eq, Aeneas.Std.bind_ok, slice_iter_eq, Aeneas.Std.bind_ok,
    enumerate_default_eq, Aeneas.Std.bind_ok]
  apply sqrt_32_loop_spec T hT value
  · rw [iterList_iterOfSlice]; simp [Std.Array.to_slice]
  · simp
  · rw [show (0#u32 : Std.U32).val = 0 from rfl, show (0#usize : Std.Usize).val = 0 from rfl,
      mul_zero, pow_zero, Nat.mod_one, sqrtNat_zero]

/-! ## `sqrt_64` -/

theorem sqrt_64_table_inner (wide : Std.Array (Std.Array Std.U128 256#usize) 8#usize)
    (i : Std.Usize) (hi : i.val < 8) (t : Std.Array (Std.Array Std.U64 256#usize) 8#usize)
    (j : Std.Usize) (hj : j.val ≤ 256) (hdone : ∀ w < j.val, cellOf t i.val w = cell wide i.val w % 2 ^ 64) :
    linear.sqrt_64.TABLE_loop0_loop0 wide t i j ⦃ t' =>
      (∀ w < 256, cellOf t' i.val w = cell wide i.val w % 2 ^ 64) ∧
      ∀ i', i' ≠ i.val → ∀ w, cellOf t' i' w = cellOf t i' w ⦄ := by
  unfold linear.sqrt_64.TABLE_loop0_loop0
  refine loop.spec_decr_nat (fun p => 256 - p.2.val)
    (fun p => p.2.val ≤ 256 ∧ (∀ w < p.2.val, cellOf p.1 i.val w = cell wide i.val w % 2 ^ 64) ∧
      ∀ i', i' ≠ i.val → ∀ w, cellOf p.1 i' w = cellOf t i' w) _ _ _ ?_
    ⟨hj, hdone, fun _ _ _ => rfl⟩
  rintro ⟨tb, k⟩ ⟨hk, hd, ho⟩
  unfold linear.sqrt_64.TABLE_loop0_loop0.body
  step*
  simp only at hk hd ho
  have hk' : k.val < 256 := by scalar_tac
  have hlen : i.val < tb.length := by simpa using hi
  have hi1 : i1.val = cell wide i.val k.val := by
    subst a_post1
    rw [i1_post1]
    simp only [cell, List.getElem?_eq_getElem a_post, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem i1_post, Option.getD_some]
  have hcell : ∀ i' w, cellOf (index_mut_back a2) i' w =
      if i' = i.val ∧ w = k.val then i2.val else cellOf tb i' w := by
    intro i' w
    rw [index_mut_back_post, a2_post, a1_post1, cellOf_set _ _ _ _ hlen hk']
  refine ⟨by omega, ?_, ?_, by omega⟩
  · intro w hw
    rw [hcell]
    by_cases hwk : w = k.val
    · subst hwk
      rw [ite_eq_left ⟨rfl, rfl⟩, i2_post, UScalar.cast_val_eq, UScalarTy.U64_numBits_eq, hi1]
    · rw [ite_eq_right (fun h => hwk h.2)]
      exact hd w (by omega)
  · intro i' hi' w
    rw [hcell, ite_eq_right (fun h => hi' h.1)]
    exact ho i' hi' w

theorem sqrt_64_table_outer (wide : Std.Array (Std.Array Std.U128 256#usize) 8#usize)
    (t : Std.Array (Std.Array Std.U64 256#usize) 8#usize) (i : Std.Usize) (hi : i.val ≤ 8)
    (hdone : ∀ i' < i.val, ∀ w < 256, cellOf t i' w = cell wide i' w % 2 ^ 64) :
    linear.sqrt_64.TABLE_loop0 wide t i ⦃ t' =>
      ∀ i' < 8, ∀ w < 256, cellOf t' i' w = cell wide i' w % 2 ^ 64 ⦄ := by
  unfold linear.sqrt_64.TABLE_loop0
  refine loop.spec_decr_nat (fun p => 8 - p.2.val)
    (fun p => p.2.val ≤ 8 ∧ ∀ i' < p.2.val, ∀ w < 256, cellOf p.1 i' w = cell wide i' w % 2 ^ 64)
    _ _ _ ?_ ⟨hi, hdone⟩
  rintro ⟨tb, k⟩ ⟨hk, hd⟩
  unfold linear.sqrt_64.TABLE_loop0.body
  step*
  simp only at hk hd
  have hk' : k.val < 8 := by scalar_tac
  refine WP.spec_bind (sqrt_64_table_inner wide k hk' tb 0#usize (by simp)
    (fun w hw => absurd hw (by simp))) fun t' ⟨hrow, ho⟩ => ?_
  step*
  refine ⟨by omega, ?_, by omega⟩
  intro i' hi' w hw
  by_cases h : i' = k.val
  · subst h; exact hrow w hw
  · rw [ho i' h w]; exact hd i' (by omega) w hw

/-- `sqrt_64`'s table: entry `w` of row `i` is the square root of `w` placed at byte `i`. -/
theorem sqrt_64_TABLE_spec :
    linear.sqrt_64.TABLE ⦃ T => ∀ i < 8, ∀ w < 256, cellOf T i w = sqrtNat 6 (w <<< (8 * i)) ⦄ := by
  unfold linear.sqrt_64.TABLE
  have hspec : ∀ bit : Std.U128, bit.val < 2 ^ (8 * (8#usize : Std.Usize).val) →
      (if true then do
          let i3 ← (8#usize : Std.Usize) * 8#usize
          linear.sqrt bit i3
        else do
          let i3 ← (8#usize : Std.Usize) * 8#usize
          linear.square bit i3) ⦃ r => r.val = sqrtNat 6 bit.val ⦄ := by
    intro bit hbit
    rw [ite_eq_left rfl]
    step*
    have h16 : i3 = widthUsize 6 :=
      UScalar.eq_of_val_eq (by rw [i3_post, widthUsize_val (by norm_num)]; rfl)
    subst h16
    exact sqrt_spec 6 (by norm_num) bit (by simpa using hbit)
  refine WP.spec_bind (unary_table_spec (B := 8#usize) (sqrtNat 6) (by simpa using additive_sqrtNat 6)
    (by simp) true hspec) fun wide hwide => ?_
  obtain ⟨a, ha, -⟩ :=
    Lib.array_repeat_eq 256#usize core.U64.Insts.CoreCloneClone (fun _ => rfl) 0#u64
  rw [ha, Aeneas.Std.bind_ok]
  obtain ⟨tb, htb, -⟩ := Lib.array_repeat_eq 8#usize
    (core.Array.Insts.CoreCloneClone 256#usize core.U64.Insts.CoreCloneClone)
    (array_clone_eq _ (fun _ => rfl)) a
  rw [htb, Aeneas.Std.bind_ok]
  refine WP.spec_mono (sqrt_64_table_outer wide tb 0#usize (by simp)
    (fun _ h => absurd h (by simp))) fun T hT => ?_
  intro i hi w hw
  have hi2 : i < (8#usize : Std.Usize).val := by simpa using hi
  rw [hT i hi w hw, hwide i hi2 w hw, Nat.mod_eq_of_lt]
  have hlt : w <<< (8 * i) < 2 ^ 2 ^ 6 := by
    calc w <<< (8 * i) < 2 ^ (8 * i + 8) := shiftLeft_lt_two_pow (by omega)
      _ ≤ 2 ^ 2 ^ 6 := Nat.pow_le_pow_right (by norm_num) (by omega)
  exact sqrtNat_lt hlt

theorem sqrt_64_loop_spec (T : Std.Array (Std.Array Std.U64 256#usize) 8#usize)
    (hT : ∀ i < 8, ∀ w < 256, cellOf T i w = sqrtNat 6 (w <<< (8 * i))) (value : Std.U64)
    (it : CoreModels.core.iter.adapters.enumerate.Enumerate (CoreModels.core.slice.iter.Iter
      (Std.Array Std.U64 256#usize)))
    (result : Std.U64) (hit : iterList it.iter = T.val.drop it.count.val) (hc : it.count.val ≤ 8)
    (hres : result.val = sqrtNat 6 (value.val % 2 ^ (8 * it.count.val))) :
    linear.sqrt_64_loop it value result ⦃ r => r.val = sqrtNat 6 value.val ⦄ := by
  unfold linear.sqrt_64_loop
  refine loop.spec_decr_nat (fun p => 8 - p.1.count.val)
    (fun p => iterList p.1.iter = T.val.drop p.1.count.val ∧ p.1.count.val ≤ 8 ∧
      p.2.val = sqrtNat 6 (value.val % 2 ^ (8 * p.1.count.val))) _ _ _ ?_ ⟨hit, hc, hres⟩
  rintro ⟨it, res⟩ ⟨hit, hc, hres⟩
  unfold linear.sqrt_64_loop.body
  simp only at hit hc hres
  have hlenT : T.val.length = 8 := by simp
  by_cases hc2 : it.count.val < 8
  · have hcons : iterList it.iter = T.val[it.count.val] :: T.val.drop (it.count.val + 1) := by
      rw [hit, List.drop_eq_getElem_cons (by omega)]
    obtain ⟨c', hc', hnext⟩ := enumerate_next_cons it hcons (by
      have : (8 : ℕ) ≤ Usize.max := by scalar_tac
      omega)
    dsimp only
    rw [hnext]
    simp only [Aeneas.Std.bind_ok]
    have hc8 : (8 * it.count.val) < 64 := by omega
    step*
    · have h3 : i3.val ≤ 255 := by
        rw [i3_post, UScalar.val_and]; exact Nat.and_le_right
      rw [i4_post, UScalar.cast_val_eq, Nat.mod_eq_of_lt (by
        rcases System.Platform.numBits_eq with e | e <;> simp only [UScalarTy.Usize_numBits_eq, e] <;> omega)]
      simp; omega
    · have hbyte : i3.val = (value.val >>> (8 * it.count.val)) % 2 ^ 8 := by
        rw [i3_post, UScalar.val_and, i2_post, i1_post, show (255#u64).val = 2 ^ 8 - 1 from rfl,
          Nat.and_two_pow_sub_one_eq_mod]
      have h3 : i3.val < 256 := hbyte ▸ Nat.mod_lt _ (by norm_num)
      have hi4 : i4.val = i3.val := by
        rw [i4_post, UScalar.cast_val_eq, Nat.mod_eq_of_lt (by
          rcases System.Platform.numBits_eq with e | e <;> simp only [UScalarTy.Usize_numBits_eq, e] <;> omega)]
      have hi5 : i5.val = sqrtNat 6 (i3.val <<< (8 * it.count.val)) := by
        rw [← hi4, ← hT it.count.val hc2 i4.val (by omega)]
        unfold cellOf
        rw [List.getElem?_eq_getElem (by omega)]
        dsimp only
        rw [List.getElem?_eq_getElem i5_post, i5_post1]
      have hv16 : value.val < 2 ^ 64 := by have := value.hBounds; simpa using this
      have hx : value.val % 2 ^ (8 * it.count.val) < 2 ^ 2 ^ 6 :=
        lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos _))
          (Nat.pow_le_pow_right (by norm_num) (by omega))
      have hy : i3.val <<< (8 * it.count.val) < 2 ^ 2 ^ 6 :=
        lt_of_lt_of_le (shiftLeft_lt_two_pow (b := 8) (by omega))
          (Nat.pow_le_pow_right (by norm_num) (by omega))
      refine ⟨by rw [iterList_iterOf, hc'], by omega, ?_, by omega⟩
      rw [result1_post, UScalar.val_xor, hres, hi5, hc', ← sqrtNat_xor hx hy, hbyte, mul_add, mul_one,
        mod_two_pow_add_byte value.val (8 * it.count.val)]
  · have hnil : iterList it.iter = [] := by rw [hit]; exact List.drop_of_length_le (by omega)
    dsimp only
    simp only [CoreModels.core.iter.adapters.enumerate.Enumerate.Insts.CoreIterTraitsIteratorIteratorPairUsizeClause0_Item.next]
    rw [slice_iter_next_nil it.iter hnil]
    simp only [Aeneas.Std.bind_ok]
    have hc2' : it.count.val = 8 := by omega
    have hv16 : value.val < 2 ^ 64 := by have := value.hBounds; simpa using this
    step*
    rw [hres, hc2', Nat.mod_eq_of_lt hv16]

/-- `sqrt_64` takes square roots in the tower's `GF(2^64)`: it is `sqrtNat 6`. -/
theorem sqrt_64_spec (value : Std.U64) :
    linear.sqrt_64 value ⦃ r => r.val = sqrtNat 6 value.val ⦄ := by
  have hv16 : value.val < 2 ^ 2 ^ 6 := by have := value.hBounds; simpa using this
  unfold linear.sqrt_64
  refine WP.spec_bind sqrt_64_TABLE_spec fun T hT => ?_
  rw [array_as_slice_eq, Aeneas.Std.bind_ok, slice_iter_eq, Aeneas.Std.bind_ok,
    enumerate_default_eq, Aeneas.Std.bind_ok]
  apply sqrt_64_loop_spec T hT value
  · rw [iterList_iterOfSlice]; simp [Std.Array.to_slice]
  · simp
  · rw [show (0#u64 : Std.U64).val = 0 from rfl, show (0#usize : Std.Usize).val = 0 from rfl,
      mul_zero, pow_zero, Nat.mod_one, sqrtNat_zero]

/-! ## `sqrt_128` -/

theorem sqrt_128_table_inner (wide : Std.Array (Std.Array Std.U128 256#usize) 16#usize)
    (i : Std.Usize) (hi : i.val < 16) (t : Std.Array (Std.Array Std.U128 256#usize) 16#usize)
    (j : Std.Usize) (hj : j.val ≤ 256) (hdone : ∀ w < j.val, cellOf t i.val w = cell wide i.val w % 2 ^ 128) :
    linear.sqrt_128.TABLE_loop0_loop0 wide t i j ⦃ t' =>
      (∀ w < 256, cellOf t' i.val w = cell wide i.val w % 2 ^ 128) ∧
      ∀ i', i' ≠ i.val → ∀ w, cellOf t' i' w = cellOf t i' w ⦄ := by
  unfold linear.sqrt_128.TABLE_loop0_loop0
  refine loop.spec_decr_nat (fun p => 256 - p.2.val)
    (fun p => p.2.val ≤ 256 ∧ (∀ w < p.2.val, cellOf p.1 i.val w = cell wide i.val w % 2 ^ 128) ∧
      ∀ i', i' ≠ i.val → ∀ w, cellOf p.1 i' w = cellOf t i' w) _ _ _ ?_
    ⟨hj, hdone, fun _ _ _ => rfl⟩
  rintro ⟨tb, k⟩ ⟨hk, hd, ho⟩
  unfold linear.sqrt_128.TABLE_loop0_loop0.body
  step*
  simp only at hk hd ho
  have hk' : k.val < 256 := by scalar_tac
  have hlen : i.val < tb.length := by simpa using hi
  have hi1 : i1.val = cell wide i.val k.val := by
    subst a_post1
    rw [i1_post1]
    simp only [cell, List.getElem?_eq_getElem a_post, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem i1_post, Option.getD_some]
  have hcell : ∀ i' w, cellOf (index_mut_back a2) i' w =
      if i' = i.val ∧ w = k.val then i1.val else cellOf tb i' w := by
    intro i' w
    rw [index_mut_back_post, a2_post, a1_post1, cellOf_set _ _ _ _ hlen hk']
  refine ⟨by omega, ?_, ?_, by omega⟩
  · intro w hw
    rw [hcell]
    by_cases hwk : w = k.val
    · subst hwk
      rw [ite_eq_left ⟨rfl, rfl⟩, ← hi1, Nat.mod_eq_of_lt (by have := i1.hBounds; simpa using this)]
    · rw [ite_eq_right (fun h => hwk h.2)]
      exact hd w (by omega)
  · intro i' hi' w
    rw [hcell, ite_eq_right (fun h => hi' h.1)]
    exact ho i' hi' w

theorem sqrt_128_table_outer (wide : Std.Array (Std.Array Std.U128 256#usize) 16#usize)
    (t : Std.Array (Std.Array Std.U128 256#usize) 16#usize) (i : Std.Usize) (hi : i.val ≤ 16)
    (hdone : ∀ i' < i.val, ∀ w < 256, cellOf t i' w = cell wide i' w % 2 ^ 128) :
    linear.sqrt_128.TABLE_loop0 wide t i ⦃ t' =>
      ∀ i' < 16, ∀ w < 256, cellOf t' i' w = cell wide i' w % 2 ^ 128 ⦄ := by
  unfold linear.sqrt_128.TABLE_loop0
  refine loop.spec_decr_nat (fun p => 16 - p.2.val)
    (fun p => p.2.val ≤ 16 ∧ ∀ i' < p.2.val, ∀ w < 256, cellOf p.1 i' w = cell wide i' w % 2 ^ 128)
    _ _ _ ?_ ⟨hi, hdone⟩
  rintro ⟨tb, k⟩ ⟨hk, hd⟩
  unfold linear.sqrt_128.TABLE_loop0.body
  step*
  simp only at hk hd
  have hk' : k.val < 16 := by scalar_tac
  refine WP.spec_bind (sqrt_128_table_inner wide k hk' tb 0#usize (by simp)
    (fun w hw => absurd hw (by simp))) fun t' ⟨hrow, ho⟩ => ?_
  step*
  refine ⟨by omega, ?_, by omega⟩
  intro i' hi' w hw
  by_cases h : i' = k.val
  · subst h; exact hrow w hw
  · rw [ho i' h w]; exact hd i' (by omega) w hw

/-- `sqrt_128`'s table: entry `w` of row `i` is the square root of `w` placed at byte `i`. -/
theorem sqrt_128_TABLE_spec :
    linear.sqrt_128.TABLE ⦃ T => ∀ i < 16, ∀ w < 256, cellOf T i w = sqrtNat 7 (w <<< (8 * i)) ⦄ := by
  unfold linear.sqrt_128.TABLE
  have hspec : ∀ bit : Std.U128, bit.val < 2 ^ (8 * (16#usize : Std.Usize).val) →
      (if true then do
          let i3 ← (16#usize : Std.Usize) * 8#usize
          linear.sqrt bit i3
        else do
          let i3 ← (16#usize : Std.Usize) * 8#usize
          linear.square bit i3) ⦃ r => r.val = sqrtNat 7 bit.val ⦄ := by
    intro bit hbit
    rw [ite_eq_left rfl]
    step*
    have h16 : i3 = widthUsize 7 :=
      UScalar.eq_of_val_eq (by rw [i3_post, widthUsize_val (by norm_num)]; rfl)
    subst h16
    exact sqrt_spec 7 (by norm_num) bit (by simpa using hbit)
  refine WP.spec_bind (unary_table_spec (B := 16#usize) (sqrtNat 7) (by simpa using additive_sqrtNat 7)
    (by simp) true hspec) fun wide hwide => ?_
  obtain ⟨a, ha, -⟩ :=
    Lib.array_repeat_eq 256#usize core.U128.Insts.CoreCloneClone (fun _ => rfl) 0#u128
  rw [ha, Aeneas.Std.bind_ok]
  obtain ⟨tb, htb, -⟩ := Lib.array_repeat_eq 16#usize
    (core.Array.Insts.CoreCloneClone 256#usize core.U128.Insts.CoreCloneClone)
    (array_clone_eq _ (fun _ => rfl)) a
  rw [htb, Aeneas.Std.bind_ok]
  refine WP.spec_mono (sqrt_128_table_outer wide tb 0#usize (by simp)
    (fun _ h => absurd h (by simp))) fun T hT => ?_
  intro i hi w hw
  have hi2 : i < (16#usize : Std.Usize).val := by simpa using hi
  rw [hT i hi w hw, hwide i hi2 w hw, Nat.mod_eq_of_lt]
  have hlt : w <<< (8 * i) < 2 ^ 2 ^ 7 := by
    calc w <<< (8 * i) < 2 ^ (8 * i + 8) := shiftLeft_lt_two_pow (by omega)
      _ ≤ 2 ^ 2 ^ 7 := Nat.pow_le_pow_right (by norm_num) (by omega)
  exact sqrtNat_lt hlt

theorem sqrt_128_loop_spec (T : Std.Array (Std.Array Std.U128 256#usize) 16#usize)
    (hT : ∀ i < 16, ∀ w < 256, cellOf T i w = sqrtNat 7 (w <<< (8 * i))) (value : Std.U128)
    (it : CoreModels.core.iter.adapters.enumerate.Enumerate (CoreModels.core.slice.iter.Iter
      (Std.Array Std.U128 256#usize)))
    (result : Std.U128) (hit : iterList it.iter = T.val.drop it.count.val) (hc : it.count.val ≤ 16)
    (hres : result.val = sqrtNat 7 (value.val % 2 ^ (8 * it.count.val))) :
    linear.sqrt_128_loop it value result ⦃ r => r.val = sqrtNat 7 value.val ⦄ := by
  unfold linear.sqrt_128_loop
  refine loop.spec_decr_nat (fun p => 16 - p.1.count.val)
    (fun p => iterList p.1.iter = T.val.drop p.1.count.val ∧ p.1.count.val ≤ 16 ∧
      p.2.val = sqrtNat 7 (value.val % 2 ^ (8 * p.1.count.val))) _ _ _ ?_ ⟨hit, hc, hres⟩
  rintro ⟨it, res⟩ ⟨hit, hc, hres⟩
  unfold linear.sqrt_128_loop.body
  simp only at hit hc hres
  have hlenT : T.val.length = 16 := by simp
  by_cases hc2 : it.count.val < 16
  · have hcons : iterList it.iter = T.val[it.count.val] :: T.val.drop (it.count.val + 1) := by
      rw [hit, List.drop_eq_getElem_cons (by omega)]
    obtain ⟨c', hc', hnext⟩ := enumerate_next_cons it hcons (by
      have : (16 : ℕ) ≤ Usize.max := by scalar_tac
      omega)
    dsimp only
    rw [hnext]
    simp only [Aeneas.Std.bind_ok]
    have hc8 : (8 * it.count.val) < 128 := by omega
    step*
    · have h3 : i3.val ≤ 255 := by
        rw [i3_post, UScalar.val_and]; exact Nat.and_le_right
      rw [i4_post, UScalar.cast_val_eq, Nat.mod_eq_of_lt (by
        rcases System.Platform.numBits_eq with e | e <;> simp only [UScalarTy.Usize_numBits_eq, e] <;> omega)]
      simp; omega
    · have hbyte : i3.val = (value.val >>> (8 * it.count.val)) % 2 ^ 8 := by
        rw [i3_post, UScalar.val_and, i2_post, i1_post, show (255#u128).val = 2 ^ 8 - 1 from rfl,
          Nat.and_two_pow_sub_one_eq_mod]
      have h3 : i3.val < 256 := hbyte ▸ Nat.mod_lt _ (by norm_num)
      have hi4 : i4.val = i3.val := by
        rw [i4_post, UScalar.cast_val_eq, Nat.mod_eq_of_lt (by
          rcases System.Platform.numBits_eq with e | e <;> simp only [UScalarTy.Usize_numBits_eq, e] <;> omega)]
      have hi5 : i5.val = sqrtNat 7 (i3.val <<< (8 * it.count.val)) := by
        rw [← hi4, ← hT it.count.val hc2 i4.val (by omega)]
        unfold cellOf
        rw [List.getElem?_eq_getElem (by omega)]
        dsimp only
        rw [List.getElem?_eq_getElem i5_post, i5_post1]
      have hv16 : value.val < 2 ^ 128 := by have := value.hBounds; simpa using this
      have hx : value.val % 2 ^ (8 * it.count.val) < 2 ^ 2 ^ 7 :=
        lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos _))
          (Nat.pow_le_pow_right (by norm_num) (by omega))
      have hy : i3.val <<< (8 * it.count.val) < 2 ^ 2 ^ 7 :=
        lt_of_lt_of_le (shiftLeft_lt_two_pow (b := 8) (by omega))
          (Nat.pow_le_pow_right (by norm_num) (by omega))
      refine ⟨by rw [iterList_iterOf, hc'], by omega, ?_, by omega⟩
      rw [result1_post, UScalar.val_xor, hres, hi5, hc', ← sqrtNat_xor hx hy, hbyte, mul_add, mul_one,
        mod_two_pow_add_byte value.val (8 * it.count.val)]
  · have hnil : iterList it.iter = [] := by rw [hit]; exact List.drop_of_length_le (by omega)
    dsimp only
    simp only [CoreModels.core.iter.adapters.enumerate.Enumerate.Insts.CoreIterTraitsIteratorIteratorPairUsizeClause0_Item.next]
    rw [slice_iter_next_nil it.iter hnil]
    simp only [Aeneas.Std.bind_ok]
    have hc2' : it.count.val = 16 := by omega
    have hv16 : value.val < 2 ^ 128 := by have := value.hBounds; simpa using this
    step*
    rw [hres, hc2', Nat.mod_eq_of_lt hv16]

/-- `sqrt_128` takes square roots in the tower's `GF(2^128)`: it is `sqrtNat 7`. -/
theorem sqrt_128_spec (value : Std.U128) :
    linear.sqrt_128 value ⦃ r => r.val = sqrtNat 7 value.val ⦄ := by
  have hv16 : value.val < 2 ^ 2 ^ 7 := by have := value.hBounds; simpa using this
  unfold linear.sqrt_128
  refine WP.spec_bind sqrt_128_TABLE_spec fun T hT => ?_
  rw [array_as_slice_eq, Aeneas.Std.bind_ok, slice_iter_eq, Aeneas.Std.bind_ok,
    enumerate_default_eq, Aeneas.Std.bind_ok]
  apply sqrt_128_loop_spec T hT value
  · rw [iterList_iterOfSlice]; simp [Std.Array.to_slice]
  · simp
  · rw [show (0#u128 : Std.U128).val = 0 from rfl, show (0#usize : Std.Usize).val = 0 from rfl,
      mul_zero, pow_zero, Nat.mod_one, sqrtNat_zero]

end Plonky3Lean.Proofs.Binary
