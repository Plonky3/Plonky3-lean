module

public import Plonky3Lean.Proofs.Field.Binary.TowerFrobenius
public import Plonky3Lean.Proofs.Field.Binary.LinearSqrt

@[expose] public section

/-!
# Powers `x^(2^n)` from `GF(2^16)` up

`exp_power_of_2` applies `linear.rs`'s Frobenius tables there. `frobenius_columns` tabulates
squaring raised to the power `2^k`, `x ↦ x^(2^(2^k))`, on every basis vector: row `0` squares,
and row `k` applies row `k - 1` twice, summing the columns a vector's set bits select. The
nibble tables of `frobenius_N` then apply row `k` for every set bit `k` of the power.

`frobNat K e` is squaring iterated `e` times on natural numbers: `x^(2^e)` at level `K`.
-/

open Aeneas Aeneas.Std CoreModels
open p3_binary_field ConcreteBinaryTower
open Plonky3Lean.Lib Plonky3Lean.Spec.BinaryField

namespace Plonky3Lean.Proofs.Binary

/-! ## The model -/

/-- Squaring iterated `e` times at level `K`. -/
def frobNat (K e : ℕ) : ℕ → ℕ := (sqNat K)^[e]

theorem frobNat_lt {K : ℕ} : ∀ (e : ℕ) {a : ℕ}, a < 2 ^ 2 ^ K → frobNat K e a < 2 ^ 2 ^ K
  | 0, _, ha => ha
  | e + 1, _, ha => by
    rw [frobNat, Function.iterate_succ_apply]
    exact frobNat_lt e (sqNat_lt ha)

theorem frobNat_xor {K : ℕ} : ∀ (e : ℕ) {x y : ℕ}, x < 2 ^ 2 ^ K → y < 2 ^ 2 ^ K →
    frobNat K e (x ^^^ y) = frobNat K e x ^^^ frobNat K e y
  | 0, _, _, _, _ => rfl
  | e + 1, x, y, hx, hy => by
    simp only [frobNat, Function.iterate_succ_apply]
    rw [sqNat_xor hx hy]
    exact frobNat_xor e (sqNat_lt hx) (sqNat_lt hy)

theorem frobNat_zero (K e : ℕ) : frobNat K e 0 = 0 := by
  induction e with
  | zero => rfl
  | succ e ih => rw [frobNat, Function.iterate_succ_apply, sqNat_zero]; exact ih

theorem frobNat_add (K a b : ℕ) (x : ℕ) : frobNat K (a + b) x = frobNat K b (frobNat K a x) := by
  simp only [frobNat]
  rw [Nat.add_comm a b, Function.iterate_add_apply]

/-! ## The lowest set bit -/

/-- Clearing the lowest set bit `t` of `x`. -/
theorem and_sub_one_eq_xor {x t : ℕ} (ht : x.testBit t = true)
    (hlow : ∀ j < t, x.testBit j = false) : x &&& (x - 1) = x ^^^ 2 ^ t := by
  have hmod : x % 2 ^ (t + 1) = 2 ^ t := by
    apply Nat.eq_of_testBit_eq
    intro j
    rw [Nat.testBit_mod_two_pow, Nat.testBit_two_pow]
    by_cases hj : j < t
    · simp [hlow j hj, show j < t + 1 by omega, show t ≠ j by omega]
    · by_cases hjt : j = t
      · subst hjt; simp [ht]
      · simp [show ¬ j < t + 1 by omega, Ne.symm hjt]
  set q := x / 2 ^ (t + 1)
  have hx : x = 2 ^ (t + 1) * q + 2 ^ t := by
    rw [← hmod]; exact (Nat.div_add_mod x _).symm
  have hx1 : x - 1 = 2 ^ (t + 1) * q + (2 ^ t - 1) := by
    have : 1 ≤ 2 ^ t := Nat.one_le_two_pow
    omega
  rw [hx1, hx]
  apply Nat.eq_of_testBit_eq
  intro j
  have h1 : 2 ^ t < 2 ^ (t + 1) := Nat.pow_lt_pow_right (by norm_num) (by omega)
  have h2 : 2 ^ t - 1 < 2 ^ (t + 1) := by omega
  rw [Nat.testBit_and, Nat.testBit_xor, Nat.testBit_two_pow_mul_add _ h1,
    Nat.testBit_two_pow_mul_add _ h2, Nat.testBit_two_pow, Nat.testBit_two_pow_sub_one]
  by_cases hj : j < t + 1
  · by_cases hjt : j = t
    · subst hjt; simp
    · simp [hj, Ne.symm hjt, show j < t by omega]
  · simp [hj, show t ≠ j by omega]

/-- The lowest set bit, as `trailing_zeros` finds it. -/
theorem find_lowest_bit {x n : ℕ} (hx : x ≠ 0) (hxn : x < 2 ^ n) :
    ∃ t, ((List.range n).find? fun i => x.testBit i) = some t ∧ t < n ∧ x.testBit t = true ∧
      ∀ j < t, x.testBit j = false := by
  cases h : (List.range n).find? (fun i => x.testBit i) with
  | none =>
    exfalso
    apply hx
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.zero_testBit]
    by_cases hi : i < n
    · simpa using List.find?_range_eq_none.mp h i hi
    · exact Nat.testBit_lt_two_pow (lt_of_lt_of_le hxn (Nat.pow_le_pow_right (by norm_num) (by omega)))
  | some t =>
    obtain ⟨hp, hmem, hlow⟩ := List.find?_range_eq_some.mp h
    exact ⟨t, rfl, List.mem_range.mp hmem, hp, fun j hj => by simpa using hlow j hj⟩

/-! ## `frobenius_columns` -/

/-- Entry `i` of row `k` of a table of 128-bit columns, as a natural number. -/
noncomputable def mcell {N M : Std.Usize} (t : Std.Array (Std.Array Std.U128 N) M) (k i : ℕ) : ℕ :=
  match t.val[k]? with
  | some r => (r.val.getD i 0#u128).val
  | none => 0

/-- A map additive below `2^(2^K)`. -/
structure XorMap (F : ℕ → ℕ) (K : ℕ) : Prop where
  zero : F 0 = 0
  xor : ∀ x y, x < 2 ^ 2 ^ K → y < 2 ^ 2 ^ K → F (x ^^^ y) = F x ^^^ F y

theorem xorMap_frobNat (K e : ℕ) : XorMap (frobNat K e) K :=
  ⟨frobNat_zero K e, fun _ _ hx hy => frobNat_xor e hx hy⟩

theorem mcell_set {N M : Std.Usize} (t : Std.Array (Std.Array Std.U128 N) M) (k i : Std.Usize)
    (x : Std.U128) (hk : k.val < t.length) (hi : i.val < N.val) (k' w : ℕ) :
    mcell (t.set k ((t.val[k.val]'(by simpa using hk)).set i x)) k' w =
      if k' = k.val ∧ w = i.val then x.val else mcell t k' w := by
  unfold mcell
  rw [Std.Array.set_val_eq]
  by_cases h : k' = k.val
  · subst h
    rw [List.getElem?_set_self (by simpa using hk), List.getElem?_eq_getElem (by simpa using hk)]
    dsimp only
    rw [Std.Array.set_val_eq]
    by_cases hw : w = i.val
    · subst hw
      rw [List.getD_eq_getElem?_getD, List.getElem?_set_self (by simpa using hi)]
      simp
    · rw [List.getD_eq_getElem?_getD, List.getElem?_set_ne (Ne.symm hw),
        ← List.getD_eq_getElem?_getD]
      simp [hw]
  · rw [List.getElem?_set_ne (Ne.symm h)]
    simp [h]

/-- The innermost loop sums row `k - 1` over the set bits of `bits`. -/
theorem frob_inner_spec {BITS LOG : Std.Usize} (K : ℕ) (hK : K ≤ 7) (hB : BITS.val = 2 ^ K)
    (F : ℕ → ℕ) (hF : XorMap F K) (maps : Std.Array (Std.Array Std.U128 BITS) LOG)
    (k : Std.Usize) (hk1 : 1 ≤ k.val) (hkL : k.val < LOG.val)
    (hrow : ∀ b < 2 ^ K, mcell maps (k.val - 1) b = F (2 ^ b)) (orig : ℕ)
    (bits result : Std.U128) (hbits : bits.val < 2 ^ 2 ^ K)
    (hinv : result.val ^^^ F bits.val = F orig) :
    linear.frobenius_columns_loop1_loop0_loop0 maps k bits result ⦃ r => r.val = F orig ⦄ := by
  unfold linear.frobenius_columns_loop1_loop0_loop0
  refine loop.spec_decr_nat (fun p => p.1.val)
    (fun p => p.1.val < 2 ^ 2 ^ K ∧ p.2.val ^^^ F p.1.val = F orig) _ _ _ ?_ ⟨hbits, hinv⟩
  rintro ⟨bs, res⟩ ⟨hbs, hres⟩
  dsimp only at hbs hres ⊢
  unfold linear.frobenius_columns_loop1_loop0_loop0.body
  step*
  case h2 =>
    have : bs = 0#u128 := UScalar.eq_of_val_eq (by simpa using ‹¬(bs != 0#u128) = true›)
    subst this
    rw [show (0#u128 : Std.U128).val = 0 from rfl, hF.zero, Nat.xor_zero] at hres
    exact hres
  have hbs0 : bs.val ≠ 0 := fun h => by
    have : bs = 0#u128 := UScalar.eq_of_val_eq (by rw [h]; rfl)
    have h0 := ‹(bs != 0#u128) = true›
    simp [this] at h0
  have h2K : 2 ^ 2 ^ K ≤ 2 ^ 128 := Nat.pow_le_pow_right (by norm_num)
    (le_trans (Nat.pow_le_pow_right (by norm_num) hK) (by norm_num))
  obtain ⟨t, hfind, ht128, htb, hlow⟩ := find_lowest_bit hbs0 (lt_of_lt_of_le hbs h2K)
  have htK : t < 2 ^ K := by
    by_contra h
    rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le hbs (Nat.pow_le_pow_right (by norm_num)
      (by omega)))] at htb
    exact absurd htb (by simp)
  simp only [core.num.U128.trailing_zeros, hfind, Option.getD_some, Aeneas.Std.bind_ok]
  have hnb := System.Platform.numBits_eq
  have hcast : (UScalar.cast UScalarTy.Usize (⟨BitVec.ofNat 32 t⟩ : Std.U32)).val = t := by
    rw [UScalar.cast_val_eq]
    show (BitVec.ofNat 32 t).toNat % _ = t
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show t < 2 ^ 32 by omega)]
    apply Nat.mod_eq_of_lt
    simp only [UScalarTy.numBits]
    rcases hnb with e | e <;> rw [e] <;> omega
  step*
  have hi2 : i2.val = t := by rw [i2_post, hcast]
  have hlen : i.val < maps.val.length := by simpa using a_post
  have hi3 : i3.val = F (2 ^ t) := by
    rw [← hrow t htK, ← i_post]
    simp only [mcell, List.getElem?_eq_getElem hlen, ← a_post1, i3_post1, hi2,
      List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show t < a.val.length by
        rw [← hi2]; simpa using i3_post), Option.getD_some]
  have hb1 : bits1.val = bs.val ^^^ 2 ^ t := by
    rw [bits1_post, UScalar.val_and, i4_post, and_sub_one_eq_xor htb hlow]
  have hle : bits1.val < bs.val := by
    rw [bits1_post, UScalar.val_and, i4_post]
    exact lt_of_le_of_lt Nat.and_le_right (by omega)
  have ht2 : 2 ^ t < 2 ^ 2 ^ K := Nat.pow_lt_pow_right (by norm_num) htK
  refine ⟨by omega, ?_, hle⟩
  have hx : bs.val ^^^ 2 ^ t < 2 ^ 2 ^ K := Nat.xor_lt_two_pow hbs ht2
  rw [result1_post, UScalar.val_xor, hi3, hb1, hF.xor _ _ hbs ht2, ← hres]
  rw [Nat.xor_assoc, ← Nat.xor_assoc (F (2 ^ t)), Nat.xor_comm (F (2 ^ t)) (F bs.val),
    Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]

/-- Row `k` is row `k - 1` applied to itself, entry by entry. -/
theorem frob_middle_spec {BITS LOG : Std.Usize} (K : ℕ) (hK : K ≤ 7) (hB : BITS.val = 2 ^ K)
    (maps : Std.Array (Std.Array Std.U128 BITS) LOG) (k : Std.Usize) (hk1 : 1 ≤ k.val)
    (hkL : k.val < LOG.val)
    (hrow : ∀ b < 2 ^ K, mcell maps (k.val - 1) b = frobNat K (2 ^ (k.val - 1)) (2 ^ b))
    (i : Std.Usize) (hi : i.val ≤ 2 ^ K)
    (hdone : ∀ w < i.val, mcell maps k.val w = frobNat K (2 ^ k.val) (2 ^ w)) :
    linear.frobenius_columns_loop1_loop0 maps i k ⦃ p =>
      (∀ w < 2 ^ K, mcell p.1 k.val w = frobNat K (2 ^ k.val) (2 ^ w)) ∧
        ∀ j, j ≠ k.val → ∀ w, mcell p.1 j w = mcell maps j w ⦄ := by
  unfold linear.frobenius_columns_loop1_loop0
  refine loop.spec_decr_nat (fun p => 2 ^ K - p.2.val)
    (fun p => p.2.val ≤ 2 ^ K ∧ (∀ w < p.2.val, mcell p.1 k.val w = frobNat K (2 ^ k.val) (2 ^ w)) ∧
      ∀ j, j ≠ k.val → ∀ w, mcell p.1 j w = mcell maps j w) _ _ _ ?_
    ⟨hi, hdone, fun _ _ _ => rfl⟩
  rintro ⟨mp, n⟩ ⟨hn, hd, ho⟩
  dsimp only at hn hd ho ⊢
  unfold linear.frobenius_columns_loop1_loop0.body
  step*
  have hnK : n.val < 2 ^ K := by rw [← hB]; scalar_tac
  have hlen : i1.val < mp.val.length := by simpa using a_post
  have hrow' : ∀ b < 2 ^ K, mcell mp (k.val - 1) b = frobNat K (2 ^ (k.val - 1)) (2 ^ b) :=
    fun b hb => by rw [ho _ (by omega)]; exact hrow b hb
  have hbits : bits.val = frobNat K (2 ^ (k.val - 1)) (2 ^ n.val) := by
    rw [← hrow' n.val hnK, ← i1_post]
    simp only [mcell, List.getElem?_eq_getElem hlen, ← a_post1, bits_post1,
      List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show n.val < a.val.length by
        simpa using bits_post), Option.getD_some]
  have h2n : 2 ^ n.val < 2 ^ 2 ^ K := Nat.pow_lt_pow_right (by norm_num) hnK
  have hblt : bits.val < 2 ^ 2 ^ K := hbits ▸ frobNat_lt _ h2n
  refine WP.spec_bind (frob_inner_spec K hK hB (frobNat K (2 ^ (k.val - 1)))
    (xorMap_frobNat K _) mp k hk1 hkL hrow' bits.val bits 0#u128
    hblt (by rw [show (0#u128 : Std.U128).val = 0 from rfl, Nat.zero_xor])) fun result hres => ?_
  have hresv : result.val = frobNat K (2 ^ k.val) (2 ^ n.val) := by
    rw [hres, hbits, ← frobNat_add, ← two_mul, ← pow_succ', Nat.sub_add_cancel hk1]
  step*
  have hk' : k.val < mp.length := by simpa using hkL
  have hset : ∀ j w, mcell (index_mut_back a2) j w =
      if j = k.val ∧ w = n.val then result.val else mcell mp j w := by
    intro j w
    rw [index_mut_back_post, a2_post, a1_post1]
    exact mcell_set mp k n result hk' (by omega) j w
  refine ⟨by scalar_tac, fun w hw => ?_, fun j hj w => ?_, by scalar_tac⟩
  · rw [hset]
    split_ifs with h
    · rw [hresv, h.2]
    · have hwn : w ≠ n.val := fun h' => h ⟨rfl, h'⟩
      exact hd w (by scalar_tac)
  · rw [hset]
    split_ifs with h
    · exact absurd h.1 hj
    · exact ho j hj w

/-- Every row `k ≥ 1` is row `k - 1` applied twice. -/
theorem frob_outer_spec {BITS LOG : Std.Usize} (K : ℕ) (hK : K ≤ 7) (hB : BITS.val = 2 ^ K)
    (maps : Std.Array (Std.Array Std.U128 BITS) LOG) (i k : Std.Usize) (hk1 : 1 ≤ k.val)
    (hkL : k.val ≤ LOG.val)
    (hrows : ∀ j < k.val, ∀ w < 2 ^ K, mcell maps j w = frobNat K (2 ^ j) (2 ^ w)) :
    linear.frobenius_columns_loop1 maps i k ⦃ m =>
      ∀ j < LOG.val, ∀ w < 2 ^ K, mcell m j w = frobNat K (2 ^ j) (2 ^ w) ⦄ := by
  unfold linear.frobenius_columns_loop1
  refine loop.spec_decr_nat (fun p => LOG.val - p.2.2.val)
    (fun p => 1 ≤ p.2.2.val ∧ p.2.2.val ≤ LOG.val ∧
      ∀ j < p.2.2.val, ∀ w < 2 ^ K, mcell p.1 j w = frobNat K (2 ^ j) (2 ^ w)) _ _ _ ?_
    ⟨hk1, hkL, hrows⟩
  rintro ⟨mp, n, kk⟩ ⟨h1, hL, hr⟩
  dsimp only at h1 hL hr ⊢
  unfold linear.frobenius_columns_loop1.body
  split
  · rename_i hlt
    have hlt' : kk.val < LOG.val := hlt
    refine WP.spec_bind (frob_middle_spec K hK hB mp kk h1 hlt'
      (fun b hb => hr _ (by omega) b hb) 0#usize (by simp) (fun w hw => absurd hw (by simp)))
      fun ⟨m1, i1⟩ ⟨hrow, ho⟩ => ?_
    show (do
      let k1 ← kk + 1#usize
      RustM.ok (ControlFlow.cont (m1, i1, k1))) ⦃ _ ⦄
    step*
    refine ⟨by omega, by omega, fun j hj w hw => ?_, by omega⟩
    by_cases hjk : j = kk.val
    · subst hjk; exact hrow w hw
    · rw [ho j hjk w]; exact hr j (by omega) w hw
  · rename_i hge
    have : LOG.val ≤ kk.val := by have := hge; scalar_tac
    rw [WP.spec_ok]
    exact fun j hj w hw => hr j (by omega) w hw

/-- The first loop fills row `0` with the squares of the basis vectors. -/
theorem frob_first_spec {LOG : Std.Usize} (K : ℕ) (hK : K ≤ 7) (hL : 1 ≤ LOG.val)
    (maps : Std.Array (Std.Array Std.U128 (widthUsize K)) LOG) (i : Std.Usize) (hi : i.val ≤ 2 ^ K)
    (hdone : ∀ w < i.val, mcell maps 0 w = frobNat K (2 ^ 0) (2 ^ w)) :
    linear.frobenius_columns_loop0 maps i ⦃ p =>
      ∀ w < 2 ^ K, mcell p.1 0 w = frobNat K (2 ^ 0) (2 ^ w) ⦄ := by
  have hB := widthUsize_val hK
  unfold linear.frobenius_columns_loop0
  refine loop.spec_decr_nat (fun p => 2 ^ K - p.2.val)
    (fun p => p.2.val ≤ 2 ^ K ∧ ∀ w < p.2.val, mcell p.1 0 w = frobNat K (2 ^ 0) (2 ^ w)) _ _ _ ?_
    ⟨hi, hdone⟩
  rintro ⟨mp, n⟩ ⟨hn, hd⟩
  dsimp only at hn hd ⊢
  unfold linear.frobenius_columns_loop0.body
  have h128 : 2 ^ K ≤ 128 := le_trans (Nat.pow_le_pow_right (by norm_num) hK) (by norm_num)
  step*
  have hnK : n.val < 2 ^ K := by have : n.val < (widthUsize K).val := by scalar_tac
                                 omega
  have hi1 : i1.val = 2 ^ n.val := by
    rw [i1_post, Nat.one_shiftLeft, show U128.size = 2 ^ 128 by simp [U128.size_def, U128.numBits_def],
      Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by norm_num) i1_post2)]
  have h2n : 2 ^ n.val < 2 ^ 2 ^ K := Nat.pow_lt_pow_right (by norm_num) hnK
  refine WP.spec_bind (square_spec K hK i1 (hi1 ▸ h2n)) fun i2 hi2 => ?_
  step*
  have hk' : (0#usize : Std.Usize).val < mp.length := by simp; omega
  have hset : ∀ j w, mcell (index_mut_back a1) j w =
      if j = 0 ∧ w = n.val then i2.val else mcell mp j w := by
    intro j w
    rw [index_mut_back_post, a1_post, a_post1]
    exact mcell_set mp 0#usize n i2 hk' (by omega) j w
  refine ⟨by scalar_tac, fun w hw => ?_, by scalar_tac⟩
  rw [hset]
  split_ifs with h
  · rw [hi2, hi1, h.2]; rfl
  · have hwn : w ≠ n.val := fun h' => h ⟨rfl, h'⟩
    exact hd w (by scalar_tac)

/-- Row `k` of `frobenius_columns` holds `x ↦ x^(2^(2^k))` on every basis vector. -/
theorem frobenius_columns_spec (K : ℕ) (hK : K ≤ 7) (LOG : Std.Usize) (hL : 1 ≤ LOG.val) :
    linear.frobenius_columns (widthUsize K) LOG ⦃ m =>
      ∀ j < LOG.val, ∀ w < 2 ^ K, mcell m j w = frobNat K (2 ^ j) (2 ^ w) ⦄ := by
  unfold linear.frobenius_columns
  obtain ⟨a, ha, -⟩ :=
    Lib.array_repeat_eq (widthUsize K) core.U128.Insts.CoreCloneClone (fun _ => rfl) 0#u128
  rw [ha, Aeneas.Std.bind_ok]
  obtain ⟨m, hm, -⟩ := Lib.array_repeat_eq LOG
    (core.Array.Insts.CoreCloneClone (widthUsize K) core.U128.Insts.CoreCloneClone)
    (array_clone_eq _ (fun _ => rfl)) a
  rw [hm, Aeneas.Std.bind_ok]
  refine WP.spec_bind (frob_first_spec K hK hL m 0#usize (by simp)
    (fun w hw => absurd hw (by simp))) fun ⟨m1, i1⟩ h => ?_
  show linear.frobenius_columns_loop1 m1 i1 1#usize ⦃ _ ⦄
  exact frob_outer_spec K hK (widthUsize_val hK) m1 i1 1#usize (by simp) (by simpa using hL)
    (fun j hj w hw => by
      have : j = 0 := by simpa using hj
      subst this; exact h w hw)

theorem frobenius_columns_spec' (K : ℕ) (hK : K ≤ 7) (BITS : Std.Usize) (hB : BITS.val = 2 ^ K)
    (LOG : Std.Usize) (hL : 1 ≤ LOG.val) :
    linear.frobenius_columns BITS LOG ⦃ m =>
      ∀ j < LOG.val, ∀ w < 2 ^ K, mcell m j w = frobNat K (2 ^ j) (2 ^ w) ⦄ := by
  have : BITS = widthUsize K := UScalar.eq_of_val_eq (by rw [hB, widthUsize_val hK])
  subst this
  exact frobenius_columns_spec K hK LOG hL

/-! ## The nibble tables -/

/-- Entry `w` of row `i` of table `k`, as a natural number (`0` past the end). -/
noncomputable def tcell {ty : UScalarTy} {E R L : Std.Usize}
    (t : Std.Array (Std.Array (Std.Array (UScalar ty) E) R) L) (k i w : ℕ) : ℕ :=
  match t.val[k]? with
  | some r =>
    match r.val[i]? with
    | some e =>
      match e.val[w]? with
      | some x => x.val
      | none => 0
    | none => 0
  | none => 0

theorem tcell_set {ty : UScalarTy} {E R L : Std.Usize}
    (t : Std.Array (Std.Array (Std.Array (UScalar ty) E) R) L) (k i u : Std.Usize) (x : UScalar ty)
    (hk : k.val < t.length) (hi : i.val < R.val) (hu : u.val < E.val) (k' i' w : ℕ) :
    tcell (t.set k ((t.val[k.val]'(by simpa using hk)).set i
      (((t.val[k.val]'(by simpa using hk)).val[i.val]'(by simpa using hi)).set u x))) k' i' w =
      if k' = k.val ∧ i' = i.val ∧ w = u.val then x.val else tcell t k' i' w := by
  unfold tcell
  rw [Std.Array.set_val_eq]
  by_cases h : k' = k.val
  · subst h
    rw [List.getElem?_set_self (by simpa using hk), List.getElem?_eq_getElem (by simpa using hk)]
    dsimp only
    rw [Std.Array.set_val_eq]
    by_cases hi' : i' = i.val
    · subst hi'
      rw [List.getElem?_set_self (by simpa using hi), List.getElem?_eq_getElem (by simpa using hi)]
      dsimp only
      rw [Std.Array.set_val_eq]
      by_cases hw : w = u.val
      · subst hw
        rw [List.getElem?_set_self (by simpa using hu)]
        simp
      · rw [List.getElem?_set_ne (Ne.symm hw)]
        simp [hw]
    · rw [List.getElem?_set_ne (Ne.symm hi')]
      simp [hi']
  · rw [List.getElem?_set_ne (Ne.symm h)]
    simp [h]

theorem one_shiftLeft_usize_val {b x : Std.Usize} (hb : b.val < 32)
    (hx : x.val = 1 <<< b.val % Usize.size) : x.val = 2 ^ b.val := by
  rw [hx, Nat.one_shiftLeft, Nat.mod_eq_of_lt]
  rw [show Usize.size = 2 ^ System.Platform.numBits by simp [Usize.size_def, Usize.numBits_def]]
  exact Nat.pow_lt_pow_right (by norm_num)
    (by rcases System.Platform.numBits_eq with e | e <;> rw [e] <;> omega)

/-- Setting entry `v | 2^b` to `entry v ^ column`, for an additive image. -/
theorem nibble_entry {F : ℕ → ℕ} {K : ℕ} (hF : XorMap F K) {v b s : ℕ} (hv : v < 2 ^ b)
    (hlt : s + b < 2 ^ K) :
    F (v <<< s) ^^^ F (2 ^ (s + b)) = F ((v ||| 2 ^ b) <<< s) := by
  rw [or_two_pow_shiftLeft, or_eq_xor_of_and_eq_zero (shiftLeft_and_two_pow hv)]
  refine (hF.xor _ _ ?_ ?_).symm
  · exact lt_of_lt_of_le (shiftLeft_lt_two_pow hv) (Nat.pow_le_pow_right (by norm_num) (by omega))
  · exact Nat.pow_lt_pow_right (by norm_num) hlt

/-- A table filled with copies of rows filled with zeros reads `0` everywhere. -/
theorem tcell_repeat_zero {ty : UScalarTy} {E R L : Std.Usize}
    (t : Std.Array (Std.Array (Std.Array (UScalar ty) E) R) L) (r : Std.Array (Std.Array (UScalar ty) E) R)
    (e : Std.Array (UScalar ty) E) (ht : ∀ y ∈ t.val, y = r) (hr : ∀ y ∈ r.val, y = e)
    (he : ∀ y ∈ e.val, y.val = 0) (k i w : ℕ) : tcell t k i w = 0 := by
  unfold tcell
  split
  · rename_i r' hr'
    have := ht r' (List.mem_of_getElem? hr')
    subst this
    split
    · rename_i e' he'
      have := hr e' (List.mem_of_getElem? he')
      subst this
      split
      · rename_i x hx
        exact he x (List.mem_of_getElem? hx)
      · rfl
    · rfl
  · rfl

/-! ## `frobenius_16` -/

theorem frob16_inner_spec (cols : Std.Array (Std.Array Std.U128 16#usize) 3#usize)
    (k i b : Std.Usize) (hk : k.val < 3) (hi : i.val < 4) (hb : b.val < 4)
    (hcol : mcell cols k.val (4 * i.val + b.val) = frobNat 4 (2 ^ k.val) (2 ^ (4 * i.val + b.val)))
    (t : Std.Array (Std.Array (Std.Array Std.U16 16#usize) 4#usize) 3#usize) (v : Std.Usize)
    (hv : v.val ≤ 2 ^ b.val)
    (hrow : ∀ w < 2 ^ b.val, tcell t k.val i.val w = frobNat 4 (2 ^ k.val) (w <<< (4 * i.val)))
    (hdone : ∀ w < v.val, tcell t k.val i.val (w ||| 2 ^ b.val) =
      frobNat 4 (2 ^ k.val) ((w ||| 2 ^ b.val) <<< (4 * i.val))) :
    linear.frobenius_16.TABLES_loop0_loop0_loop0_loop0 cols t k i b v ⦃ t' =>
      (∀ w < 2 ^ (b.val + 1), tcell t' k.val i.val w = frobNat 4 (2 ^ k.val) (w <<< (4 * i.val))) ∧
        ∀ k' i', ¬(k' = k.val ∧ i' = i.val) → ∀ w, tcell t' k' i' w = tcell t k' i' w ⦄ := by
  unfold linear.frobenius_16.TABLES_loop0_loop0_loop0_loop0
  refine loop.spec_decr_nat (fun p => 2 ^ b.val - p.2.val)
    (fun p => p.2.val ≤ 2 ^ b.val ∧
      (∀ w < 2 ^ b.val, tcell p.1 k.val i.val w = frobNat 4 (2 ^ k.val) (w <<< (4 * i.val))) ∧
      (∀ w < p.2.val, tcell p.1 k.val i.val (w ||| 2 ^ b.val) =
        frobNat 4 (2 ^ k.val) ((w ||| 2 ^ b.val) <<< (4 * i.val))) ∧
      ∀ k' i', ¬(k' = k.val ∧ i' = i.val) → ∀ w, tcell p.1 k' i' w = tcell t k' i' w) _ _ _ ?_
    ⟨hv, hrow, hdone, fun _ _ _ _ => rfl⟩
  rintro ⟨tb, n⟩ ⟨hn, hr, hd, ho⟩
  dsimp only at hn hr hd ho ⊢
  unfold linear.frobenius_16.TABLES_loop0_loop0_loop0_loop0.body
  have hbits : b.val < System.Platform.numBits := by
    rcases System.Platform.numBits_eq with e | e <;> rw [e] <;> omega
  have h2b : 2 ^ b.val ≤ 8 :=
    calc 2 ^ b.val ≤ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ = 8 := by norm_num
  step*
  case h2 =>
    have hi1 := one_shiftLeft_usize_val (by omega) i1_post
    have hnb : ¬ n.val < 2 ^ b.val := fun h => by
      have : n < i1 := by scalar_tac
      contradiction
    refine ⟨fun w hw => ?_, ho⟩
    by_cases hlo : w < 2 ^ b.val
    · exact hr w hlo
    · have hw' : w - 2 ^ b.val < 2 ^ b.val := by rw [pow_succ] at hw; omega
      have := hd (w - 2 ^ b.val) (by omega)
      rwa [Nat.or_two_pow_eq_add_of_lt hw', Nat.sub_add_cancel (by omega)] at this
  all_goals have hi1 := one_shiftLeft_usize_val (by omega) i1_post
  all_goals have hni : n.val < i1.val := by scalar_tac
  all_goals have hnb : n.val < 2 ^ b.val := by omega
  all_goals try first
    | (simp; omega)
    | (rw [i7_post, UScalar.val_or, hi1, Nat.or_two_pow_eq_add_of_lt hnb]; simp; omega)
  · have hi7 : i7.val = n.val + 2 ^ b.val := by
      rw [i7_post, UScalar.val_or, hi1, Nat.or_two_pow_eq_add_of_lt hnb]
    have hklen : k.val < tb.length := by simpa using a_post
    have hset : ∀ k' i' w, tcell (index_mut_back (index_mut_back1 a5)) k' i' w =
        if k' = k.val ∧ i' = i.val ∧ w = i7.val then i8.val else tcell tb k' i' w := by
      intro k' i' w
      subst index_mut_back_post index_mut_back1_post a5_post a4_post1 a3_post1
      exact tcell_set tb k i i7 i8 hklen (by simp; omega) (by simp; omega) k' i' w
    have hi2 : i2.val = frobNat 4 (2 ^ k.val) (n.val <<< (4 * i.val)) := by
      rw [← hr n.val hnb]
      simp only [tcell, List.getElem?_eq_getElem (show k.val < tb.val.length by simpa using a_post),
        ← a_post1, List.getElem?_eq_getElem (show i.val < a.val.length by simpa using a1_post),
        ← a1_post1, List.getElem?_eq_getElem (show n.val < a1.val.length by simpa using i2_post),
        ← i2_post1]
    have hi5 : i5.val = frobNat 4 (2 ^ k.val) (2 ^ (4 * i.val + b.val)) := by
      rw [← hcol, ← (show i4.val = 4 * i.val + b.val by rw [i4_post, i3_post])]
      simp only [mcell, List.getElem?_eq_getElem (show k.val < cols.val.length by simpa using a2_post),
        ← a2_post1, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show i4.val < a2.val.length by
          simpa using i5_post), ← i5_post1, Option.getD_some]
    have hi5lt : i5.val < 2 ^ 16 := by
      rw [hi5]; exact frobNat_lt (K := 4) _ (Nat.pow_lt_pow_right (by norm_num) (by omega))
    have hi6 : i6.val = i5.val := by
      rw [i6_post, UScalar.cast_val_eq, UScalarTy.U16_numBits_eq, Nat.mod_eq_of_lt hi5lt]
    have hi8 : i8.val = frobNat 4 (2 ^ k.val) ((n.val ||| 2 ^ b.val) <<< (4 * i.val)) := by
      rw [i8_post, UScalar.val_xor, hi2, hi6, hi5,
        nibble_entry (xorMap_frobNat 4 _) hnb (by omega)]
    refine ⟨by omega, fun w hw => ?_, fun w hw => ?_, fun k' i' h w => ?_, by omega⟩
    · rw [hset, ite_eq_right (by omega)]
      exact hr w hw
    · rw [hset]
      by_cases hwn : w = n.val
      · subst hwn
        rw [ite_eq_left ⟨rfl, rfl, by rw [hi7, Nat.or_two_pow_eq_add_of_lt hnb]⟩, hi8]
      · rw [ite_eq_right (by
          rw [hi7, Nat.or_two_pow_eq_add_of_lt (show w < 2 ^ b.val by omega)]; omega)]
        exact hd w (by omega)
    · rw [hset, ite_eq_right (fun h' => h ⟨h'.1, h'.2.1⟩)]
      exact ho k' i' h w

/-- The loop over bits fills row `i` of table `k`. -/
theorem frob16_bloop_spec (cols : Std.Array (Std.Array Std.U128 16#usize) 3#usize)
    (hcols : ∀ k < 3, ∀ j < 16, mcell cols k j = frobNat 4 (2 ^ k) (2 ^ j))
    (k i : Std.Usize) (hk : k.val < 3) (hi : i.val < 4)
    (t : Std.Array (Std.Array (Std.Array Std.U16 16#usize) 4#usize) 3#usize) (b : Std.Usize)
    (hb : b.val ≤ 4)
    (hrow : ∀ w < 2 ^ b.val, tcell t k.val i.val w = frobNat 4 (2 ^ k.val) (w <<< (4 * i.val))) :
    linear.frobenius_16.TABLES_loop0_loop0_loop0 cols t k i b ⦃ t' =>
      (∀ w < 16, tcell t' k.val i.val w = frobNat 4 (2 ^ k.val) (w <<< (4 * i.val))) ∧
        ∀ k' i', ¬(k' = k.val ∧ i' = i.val) → ∀ w, tcell t' k' i' w = tcell t k' i' w ⦄ := by
  unfold linear.frobenius_16.TABLES_loop0_loop0_loop0
  refine loop.spec_decr_nat (fun p => 4 - p.2.val)
    (fun p => p.2.val ≤ 4 ∧
      (∀ w < 2 ^ p.2.val, tcell p.1 k.val i.val w = frobNat 4 (2 ^ k.val) (w <<< (4 * i.val))) ∧
      ∀ k' i', ¬(k' = k.val ∧ i' = i.val) → ∀ w, tcell p.1 k' i' w = tcell t k' i' w) _ _ _ ?_
    ⟨hb, hrow, fun _ _ _ _ => rfl⟩
  rintro ⟨tb, n⟩ ⟨hn, hr, ho⟩
  dsimp only at hn hr ho ⊢
  unfold linear.frobenius_16.TABLES_loop0_loop0_loop0.body
  split
  · rename_i hlt
    have hn4 : n.val < 4 := hlt
    refine WP.spec_bind (frob16_inner_spec cols k i n hk hi hn4 (hcols _ hk _ (by omega)) tb
      0#usize (by simp) hr (fun w hw => absurd hw (by simp))) fun t' ⟨hrow', ho'⟩ => ?_
    step*
    refine ⟨by omega, by rw [b1_post]; exact hrow', fun k' i' h w => by rw [ho' k' i' h w, ho k' i' h w],
      by omega⟩
  · rename_i hge
    have hn4 : n.val = 4 := by have : ¬ n.val < 4 := hge; omega
    rw [WP.spec_ok]
    exact ⟨fun w hw => hr w (by rw [hn4]; omega), ho⟩

/-- The loop over rows fills table `k`; rows not yet reached are still zero. -/
theorem frob16_iloop_spec (cols : Std.Array (Std.Array Std.U128 16#usize) 3#usize)
    (hcols : ∀ k < 3, ∀ j < 16, mcell cols k j = frobNat 4 (2 ^ k) (2 ^ j)) (k : Std.Usize)
    (hk : k.val < 3) (t : Std.Array (Std.Array (Std.Array Std.U16 16#usize) 4#usize) 3#usize)
    (i : Std.Usize) (hi : i.val ≤ 4)
    (hdone : ∀ i' < i.val, ∀ w < 16, tcell t k.val i' w = frobNat 4 (2 ^ k.val) (w <<< (4 * i')))
    (hzero : ∀ i', i.val ≤ i' → tcell t k.val i' 0 = 0) :
    linear.frobenius_16.TABLES_loop0_loop0 cols t k i ⦃ t' =>
      (∀ i' < 4, ∀ w < 16, tcell t' k.val i' w = frobNat 4 (2 ^ k.val) (w <<< (4 * i'))) ∧
        ∀ k', k' ≠ k.val → ∀ i' w, tcell t' k' i' w = tcell t k' i' w ⦄ := by
  unfold linear.frobenius_16.TABLES_loop0_loop0
  refine loop.spec_decr_nat (fun p => 4 - p.2.val)
    (fun p => p.2.val ≤ 4 ∧
      (∀ i' < p.2.val, ∀ w < 16, tcell p.1 k.val i' w = frobNat 4 (2 ^ k.val) (w <<< (4 * i'))) ∧
      (∀ i', p.2.val ≤ i' → tcell p.1 k.val i' 0 = 0) ∧
      ∀ k', k' ≠ k.val → ∀ i' w, tcell p.1 k' i' w = tcell t k' i' w) _ _ _ ?_
    ⟨hi, hdone, hzero, fun _ _ _ _ => rfl⟩
  rintro ⟨tb, n⟩ ⟨hn, hd, hz, ho⟩
  dsimp only at hn hd hz ho ⊢
  unfold linear.frobenius_16.TABLES_loop0_loop0.body
  step*
  · have hn4 : n.val < 4 := by scalar_tac
    refine WP.spec_bind (frob16_bloop_spec cols hcols k n hk hn4 tb 0#usize (by simp)
      (fun w hw => by
        have : w = 0 := by simpa using hw
        subst this
        rw [hz n.val le_rfl, Nat.zero_shiftLeft, frobNat_zero])) fun t' ⟨hrow', ho'⟩ => ?_
    step*
    refine ⟨by omega, fun i' hi' w hw => ?_, fun i' hi' => ?_, fun k' hk' i' w => ?_, by omega⟩
    · by_cases hin : i' = n.val
      · subst hin; exact hrow' w hw
      · rw [ho' _ _ (fun h => hin h.2)]; exact hd i' (by omega) w hw
    · rw [ho' _ _ (fun h => by omega)]; exact hz i' (by omega)
    · rw [ho' _ _ (fun h => hk' h.1)]; exact ho k' hk' i' w

/-- The loop over tables fills every table; tables not yet reached are still zero. -/
theorem frob16_kloop_spec (cols : Std.Array (Std.Array Std.U128 16#usize) 3#usize)
    (hcols : ∀ k < 3, ∀ j < 16, mcell cols k j = frobNat 4 (2 ^ k) (2 ^ j))
    (t : Std.Array (Std.Array (Std.Array Std.U16 16#usize) 4#usize) 3#usize) (k : Std.Usize)
    (hk : k.val ≤ 3)
    (hdone : ∀ k' < k.val, ∀ i < 4, ∀ w < 16, tcell t k' i w = frobNat 4 (2 ^ k') (w <<< (4 * i)))
    (hzero : ∀ k' i, k.val ≤ k' → tcell t k' i 0 = 0) :
    linear.frobenius_16.TABLES_loop0 cols t k ⦃ t' =>
      ∀ k' < 3, ∀ i < 4, ∀ w < 16, tcell t' k' i w = frobNat 4 (2 ^ k') (w <<< (4 * i)) ⦄ := by
  unfold linear.frobenius_16.TABLES_loop0
  refine loop.spec_decr_nat (fun p => 3 - p.2.val)
    (fun p => p.2.val ≤ 3 ∧
      (∀ k' < p.2.val, ∀ i < 4, ∀ w < 16, tcell p.1 k' i w = frobNat 4 (2 ^ k') (w <<< (4 * i))) ∧
      ∀ k' i, p.2.val ≤ k' → tcell p.1 k' i 0 = 0) _ _ _ ?_ ⟨hk, hdone, hzero⟩
  rintro ⟨tb, n⟩ ⟨hn, hd, hz⟩
  dsimp only at hn hd hz ⊢
  unfold linear.frobenius_16.TABLES_loop0.body
  split
  · rename_i hlt
    have hn3 : n.val < 3 := hlt
    refine WP.spec_bind (frob16_iloop_spec cols hcols n hn3 tb 0#usize (by simp)
      (fun i' hi' => absurd hi' (by simp)) (fun i' _ => hz n.val i' le_rfl))
      fun t' ⟨hrow', ho'⟩ => ?_
    step*
    refine ⟨by omega, fun k' hk' i hi w hw => ?_, fun k' i hk' => ?_, by omega⟩
    · by_cases hkn : k' = n.val
      · subst hkn; exact hrow' i hi w hw
      · rw [ho' k' hkn]; exact hd k' (by omega) i hi w hw
    · rw [ho' k' (by omega)]; exact hz k' i (by omega)
  · rename_i hge
    have hn3 : n.val = 3 := by have : ¬ n.val < 3 := hge
                               omega
    rw [WP.spec_ok]
    exact fun k' hk' i hi w hw => hd k' (by omega) i hi w hw

/-- Entry `w` of row `i` of table `k` is `x ↦ x^(2^(2^k))` applied to `w` placed at nibble `i`. -/
theorem frobenius_16_TABLES_spec :
    linear.frobenius_16.TABLES ⦃ T =>
      ∀ k < 3, ∀ i < 4, ∀ w < 16, tcell T k i w = frobNat 4 (2 ^ k) (w <<< (4 * i)) ⦄ := by
  unfold linear.frobenius_16.TABLES
  refine WP.spec_bind (frobenius_columns_spec' 4 (by norm_num) 16#usize (by simp) 3#usize (by simp))
    fun cols hcols => ?_
  obtain ⟨a, ha, hav⟩ :=
    Lib.array_repeat_eq 16#usize core.U16.Insts.CoreCloneClone (fun _ => rfl) 0#u16
  rw [ha, Aeneas.Std.bind_ok]
  obtain ⟨a1, ha1, ha1v⟩ := Lib.array_repeat_eq 4#usize
    (core.Array.Insts.CoreCloneClone 16#usize core.U16.Insts.CoreCloneClone)
    (array_clone_eq _ (fun _ => rfl)) a
  rw [ha1, Aeneas.Std.bind_ok]
  obtain ⟨tb, htb, htbv⟩ := Lib.array_repeat_eq 3#usize
    (core.Array.Insts.CoreCloneClone 4#usize
      (core.Array.Insts.CoreCloneClone 16#usize core.U16.Insts.CoreCloneClone))
    (array_clone_eq _ (array_clone_eq _ (fun _ => rfl))) a1
  rw [htb, Aeneas.Std.bind_ok]
  exact frob16_kloop_spec cols (fun k hk j hj => hcols k (by simpa using hk) j (by simpa using hj))
    tb 0#usize (by simp) (fun k hk => absurd hk (by simp))
    (fun k i _ => tcell_repeat_zero tb a1 a htbv ha1v (fun y hy => by rw [hav y hy]; rfl) k i 0)

end Plonky3Lean.Proofs.Binary
