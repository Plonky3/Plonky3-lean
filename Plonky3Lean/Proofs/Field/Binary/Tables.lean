module

public import Plonky3Lean.Proofs.Field.Binary.Clmul
public import Plonky3Lean.Lib.Scalar
public import ToCompPoly.Fields.Binary.Tower.NatMul

@[expose] public section

/-!
# The `GF(2^8)` lookup tables

p3-binary-field multiplies in the tower's `GF(2^8)` through logarithm tables.

- `EXP[e]` is `g^e` for the generator `g = 19`, over two periods.
- `LOG[x]` is the exponent of `x`, for `x ≠ 0`.

The kernel checks both tables against `towerMul`, the tower product on natural numbers.

`towerMul` is CompPoly's `concrete_mul` (`toNat_concrete_mul`), so the tables are CompPoly's
field, and a product of powers of `g` is a sum of exponents.
-/

open Aeneas Aeneas.Std CoreModels
open p3_binary_field ConcreteBinaryTower
open Plonky3Lean.Spec.BinaryField

namespace Plonky3Lean.Proofs.Binary

/-- The tower's `GF(2^8)`, as CompPoly defines it. -/
abbrev F8 := ConcreteBTField 3

/-! ## The tables, checked by the kernel -/

/-- The entries of `EXP`, as numbers. -/
def expL : List ℕ := tables.EXP.val.map (·.val)

/-- The entries of `LOG`, as numbers. -/
def logL : List ℕ := tables.LOG.val.map (·.val)

/-- Each entry of `EXP` is the previous one times `19`. -/
theorem expL_succ : ∀ i < 510, expL.getD (i + 1) 0 = towerMul 3 (expL.getD i 0) 19 := by
  decide +kernel

theorem expL_zero : expL.getD 0 0 = 1 := by decide +kernel

theorem expL_255 : expL.getD 255 0 = 1 := by decide +kernel

theorem expL_lt : ∀ i < 511, expL.getD i 0 < 256 := by decide +kernel

/-- `LOG` inverts `EXP` on the nonzero elements. -/
theorem expL_logL : ∀ x < 256, 0 < x → expL.getD (logL.getD x 0) 0 = x := by
  decide +kernel

theorem logL_lt : ∀ x < 256, logL.getD x 0 < 255 := by decide +kernel

/-! ## Powers of the generator -/

/-- The generator `19`. -/
def gen8 : F8 := fromNat 19

theorem toNat_lt_256 (x : F8) : x.toNat < 256 := x.isLt

/-- One step of the chain: multiplying by `19` in the field. -/
theorem fromNat_towerMul {e : ℕ} (he : e < 256) :
    (fromNat (k := 3) (towerMul 3 e 19) : F8) = fromNat e * gen8 := by
  have h := toNat_concrete_mul 3 (fromNat (k := 3) e) gen8
  rw [toNat_fromNat, gen8, toNat_fromNat] at h
  norm_num [Nat.mod_eq_of_lt he] at h
  apply BitVec.eq_of_toNat_eq
  rw [toNat_fromNat, show fromNat e * gen8 = concrete_mul (fromNat e) (fromNat 19) from rfl, h,
    Nat.mod_eq_of_lt (h ▸ toNat_lt_256 _)]

/-- `EXP[i]` is `g^i`. -/
theorem fromNat_expL : ∀ i < 511, (fromNat (k := 3) (expL.getD i 0) : F8) = gen8 ^ i
  | 0, _ => by rw [expL_zero, pow_zero]; rfl
  | i + 1, hi => by
    rw [expL_succ i (by omega), fromNat_towerMul (expL_lt i (by omega)),
      fromNat_expL i (by omega), pow_succ]

/-- `g^LOG[x]` is `x`, for `x ≠ 0`. -/
theorem gen8_pow_logL {x : ℕ} (hx : 0 < x) (hx' : x < 256) :
    gen8 ^ logL.getD x 0 = fromNat x := by
  rw [← fromNat_expL _ (by have := logL_lt x hx'; omega), expL_logL x hx' hx]

theorem gen8_pow_255 : gen8 ^ 255 = 1 := by
  rw [← fromNat_expL 255 (by norm_num), expL_255]
  rfl

/-! ## The extracted functions -/

theorem tower8_eq (x : Std.U8) : tower8 x = fromNat x.val := by
  show x.bv = BitVec.ofNat 8 x.bv.toNat
  rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]

theorem tower8_eq_zero_iff (x : Std.U8) : tower8 x = 0 ↔ x = 0#u8 := by
  constructor
  · intro h
    apply UScalar.eq_of_val_eq
    have := congrArg BitVec.toNat h
    exact this
  · rintro rfl
    rfl

/-- An entry of a table of bytes, as a number. -/
theorem val_getElem {n : Std.Usize} (v : Std.Array Std.U8 n) (j : ℕ) (h : j < v.val.length) :
    (v.val[j]'h).val = (v.val.map (·.val)).getD j 0 := by
  rw [List.getD_eq_getElem _ _ (by simpa using h), List.getElem_map]

theorem cast_usize_val (x : Std.U8) : (UScalar.cast .Usize x).val = x.val := by
  rw [UScalar.cast_val_eq]
  have := x.hBounds
  rw [UScalarTy.U8_numBits_eq] at this
  apply Nat.mod_eq_of_lt
  rcases System.Platform.numBits_eq with h | h <;>
    simp only [UScalarTy.Usize_numBits_eq, h] <;> omega

theorem tables_mul_spec (a b : Std.U8) :
    tables.mul a b ⦃ r => tower8 r = tower8 a * tower8 b ⦄ := by
  unfold tables.mul
  step*
  subst_vars
  have ha := a.hBounds
  have hb := b.hBounds
  rw [UScalarTy.U8_numBits_eq] at ha hb
  have hexp : exponent.val = logL.getD a.val 0 + logL.getD b.val 0 := by
    simp only [exponent_post, cast_usize_val, val_getElem]
    rfl
  have hE : ((↑tables.EXP : List Std.U8)[exponent.val]'i9).val =
      expL.getD (logL.getD a.val 0 + logL.getD b.val 0) 0 := by
    simp only [val_getElem, hexp]
    rfl
  rw [tower8_eq, tower8_eq, tower8_eq, UScalar.val_and, hE]
  by_cases ha0 : a = 0#u8
  · have : i6.val = 0 := by rw [i6_post, ha0]; rfl
    have h8 : i8.val = 0 := by
      rw [i8_post1, UScalar.val_and, this, Nat.zero_and]
    rw [both_nonzero_post, h8, ha0]
    show fromNat _ = fromNat 0 * fromNat b.val
    rw [show (fromNat (k := 3) 0 : F8) = 0 from rfl, zero_mul,
      show (0 + 2 ^ 8 - 0) % 2 ^ 8 = 0 by norm_num, Nat.and_zero]
    rfl
  by_cases hb0 : b = 0#u8
  · have : i7.val = 0 := by rw [i7_post, hb0]; rfl
    have h8 : i8.val = 0 := by
      rw [i8_post1, UScalar.val_and, this, Nat.and_zero]
    rw [both_nonzero_post, h8, hb0]
    show fromNat _ = fromNat a.val * fromNat 0
    rw [show (fromNat (k := 3) 0 : F8) = 0 from rfl, mul_zero,
      show (0 + 2 ^ 8 - 0) % 2 ^ 8 = 0 by norm_num, Nat.and_zero]
    rfl
  have h6 : i6.val = 1 := by rw [i6_post]; simp [ha0]
  have h7 : i7.val = 1 := by rw [i7_post]; simp [hb0]
  have h8 : i8.val = 1 := by rw [i8_post1, UScalar.val_and, h6, h7]; rfl
  have ha' : 0 < a.val := by
    rcases Nat.eq_zero_or_pos a.val with h | h
    · exact absurd (UScalar.eq_of_val_eq (by rw [h]; rfl)) ha0
    · exact h
  have hb' : 0 < b.val := by
    rcases Nat.eq_zero_or_pos b.val with h | h
    · exact absurd (UScalar.eq_of_val_eq (by rw [h]; rfl)) hb0
    · exact h
  have hlt := expL_lt (logL.getD a.val 0 + logL.getD b.val 0)
    (by have := logL_lt a.val ha; have := logL_lt b.val hb; omega)
  rw [both_nonzero_post, h8, show (0 + 2 ^ 8 - 1) % 2 ^ 8 = 255 by norm_num,
    show expL.getD (logL.getD a.val 0 + logL.getD b.val 0) 0 &&& 255 =
      expL.getD (logL.getD a.val 0 + logL.getD b.val 0) 0 by
      rw [show (255 : ℕ) = 2 ^ 8 - 1 by norm_num, Nat.and_two_pow_sub_one_eq_mod,
        Nat.mod_eq_of_lt hlt],
    fromNat_expL _ (by have := logL_lt a.val ha; have := logL_lt b.val hb; omega), pow_add,
    gen8_pow_logL ha' ha, gen8_pow_logL hb' hb]


/-! ## The unary tables -/

/-- After the loop reaches `i`, entry `0` is still `0`, and entry `j` for `1 ≤ j < i` is
`EXP[f(LOG[j])]`. -/
def TableInv (f : ℕ → ℕ) (t : Std.Array Std.U8 256#usize) (i : ℕ) : Prop :=
  1 ≤ i ∧ i ≤ 256 ∧ (t.val.map (·.val)).getD 0 0 = 0 ∧
    ∀ j, 1 ≤ j → j < i → (t.val.map (·.val)).getD j 0 = expL.getD (f (logL.getD j 0)) 0

theorem getD_map_set {i j : ℕ} {l : List Std.U8} (x : Std.U8) (hi : i < l.length) :
    ((l.set i x).map (·.val)).getD j 0 = if i = j then x.val else (l.map (·.val)).getD j 0 := by
  rw [List.map_set]
  by_cases h : i = j
  · subst h
    rw [ite_eq_left rfl, List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_set_self]
  · rw [ite_eq_right h, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_set_ne h]

theorem SQUARE_loop_spec (t : Std.Array Std.U8 256#usize) (i : Std.Usize)
    (h : TableInv (fun e => 2 * e) t i.val) :
    tables.SQUARE_loop t i ⦃ r => TableInv (fun e => 2 * e) r 256 ⦄ := by
  unfold tables.SQUARE_loop
  refine loop.spec_decr_nat (fun p => 256 - p.2.val) (fun p => TableInv (fun e => 2 * e) p.1 p.2.val)
    _ _ _ ?_ h
  rintro ⟨tb, k⟩ ⟨h1, h2, h0, hinv⟩
  unfold tables.SQUARE_loop.body
  step*
  · subst_vars
    simp only at h1 h2 h0 hinv
    have hk : k.val < 256 := by scalar_tac
    have hlen : k.val < tb.val.length := by simp; omega
    refine ⟨⟨by omega, by omega, ?_, ?_⟩, by omega⟩
    · rw [Array.set_val_eq, getD_map_set _ hlen, ite_eq_right (by omega), h0]
    · intro j hj1 hj2
      rw [Array.set_val_eq, getD_map_set _ hlen]
      by_cases hjk : k.val = j
      · subst hjk
        rw [ite_eq_left rfl]
        simp only [val_getElem, i3_post, cast_usize_val]
        rfl
      · rw [ite_eq_right hjk]
        exact hinv j hj1 (by omega)
  · simp only at h1 h2 h0 hinv
    have hk : k.val = 256 := by scalar_tac
    rw [hk] at hinv
    exact ⟨by omega, le_rfl, h0, hinv⟩

theorem INVERSE_loop_spec (t : Std.Array Std.U8 256#usize) (i : Std.Usize)
    (h : TableInv (fun e => 255 - e) t i.val) :
    tables.INVERSE_loop t i ⦃ r => TableInv (fun e => 255 - e) r 256 ⦄ := by
  unfold tables.INVERSE_loop
  refine loop.spec_decr_nat (fun p => 256 - p.2.val) (fun p => TableInv (fun e => 255 - e) p.1 p.2.val)
    _ _ _ ?_ h
  rintro ⟨tb, k⟩ ⟨h1, h2, h0, hinv⟩
  unfold tables.INVERSE_loop.body
  step*
  · subst_vars
    simp only at h1 h2 h0 hinv
    have hk : k.val < 256 := by scalar_tac
    have hlen : k.val < tb.val.length := by simp; omega
    refine ⟨⟨by omega, by omega, ?_, ?_⟩, by omega⟩
    · rw [Array.set_val_eq, getD_map_set _ hlen, ite_eq_right (by omega), h0]
    · intro j hj1 hj2
      rw [Array.set_val_eq, getD_map_set _ hlen]
      by_cases hjk : k.val = j
      · subst hjk
        rw [ite_eq_left rfl]
        simp only [val_getElem, i3_post1, cast_usize_val]
        rfl
      · rw [ite_eq_right hjk]
        exact hinv j hj1 (by omega)
  · simp only at h1 h2 h0 hinv
    have hk : k.val = 256 := by scalar_tac
    rw [hk] at hinv
    exact ⟨by omega, le_rfl, h0, hinv⟩

theorem tableInv_init (f : ℕ → ℕ) : TableInv f (Std.Array.repeat 256#usize 0#u8) 1 :=
  ⟨le_rfl, by norm_num, by decide, fun j hj1 hj2 => absurd hj2 (by omega)⟩

theorem SQUARE_spec : tables.SQUARE ⦃ r => TableInv (fun e => 2 * e) r 256 ⦄ := by
  unfold tables.SQUARE
  exact SQUARE_loop_spec _ 1#usize (tableInv_init _)

theorem INVERSE_spec : tables.INVERSE ⦃ r => TableInv (fun e => 255 - e) r 256 ⦄ := by
  unfold tables.INVERSE
  exact INVERSE_loop_spec _ 1#usize (tableInv_init _)

/-- `square(a)` is `a · a` in the tower's `GF(2^8)`. -/
theorem tables_square_spec (a : Std.U8) :
    tables.square a ⦃ r => tower8 r = tower8 a * tower8 a ⦄ := by
  unfold tables.square
  refine WP.spec_bind SQUARE_spec fun t ⟨_, _, h0, hinv⟩ => ?_
  step*
  subst_vars
  have ha := a.hBounds
  rw [UScalarTy.U8_numBits_eq] at ha
  rw [tower8_eq, tower8_eq]
  have hv : ((↑t : List Std.U8)[(UScalar.cast .Usize a).val]'(by simp; omega)).val =
      (t.val.map (·.val)).getD a.val 0 := by
    simp only [val_getElem, cast_usize_val]
  rw [hv]
  rcases Nat.eq_zero_or_pos a.val with h | h
  · rw [h, h0]
    show (fromNat (k := 3) 0 : F8) = fromNat 0 * fromNat 0
    rw [show (fromNat (k := 3) 0 : F8) = 0 from rfl, zero_mul]
  · rw [hinv a.val h ha]
    beta_reduce
    rw [fromNat_expL _ (by have := logL_lt a.val ha; omega), pow_mul', sq, gen8_pow_logL h ha]

/-- `try_inverse(a)` is `None` for `0`, and otherwise the inverse in the tower's `GF(2^8)`. -/
theorem tables_try_inverse_spec (a : Std.U8) :
    tables.try_inverse a ⦃ r => (tower8 a = 0 → r = none) ∧
      (tower8 a ≠ 0 → ∃ c, r = some c ∧ tower8 c * tower8 a = 1) ⦄ := by
  unfold tables.try_inverse
  by_cases ha0 : a = 0#u8
  · rw [ite_eq_left ha0, WP.spec_ok]
    exact ⟨fun _ => rfl, fun h => absurd ((tower8_eq_zero_iff a).mpr ha0) h⟩
  rw [ite_eq_right ha0]
  refine WP.spec_bind INVERSE_spec fun t ⟨_, _, _, hinv⟩ => ?_
  step*
  subst_vars
  have ha := a.hBounds
  rw [UScalarTy.U8_numBits_eq] at ha
  have h : 0 < a.val := by
    rcases Nat.eq_zero_or_pos a.val with h | h
    · exact absurd (UScalar.eq_of_val_eq (by rw [h]; rfl)) ha0
    · exact h
  refine ⟨fun h' => absurd ((tower8_eq_zero_iff a).mp h') ha0, fun _ => ⟨_, rfl, ?_⟩⟩
  rw [tower8_eq, tower8_eq]
  have hv : ((↑t : List Std.U8)[(UScalar.cast .Usize a).val]'(by simp; omega)).val =
      (t.val.map (·.val)).getD a.val 0 := by
    simp only [val_getElem, cast_usize_val]
  have hL := logL_lt a.val ha
  rw [hv, hinv a.val h ha]
  beta_reduce
  rw [fromNat_expL _ (by omega), ← gen8_pow_logL h ha, ← pow_add,
    Nat.sub_add_cancel (by omega), gen8_pow_255]

end Plonky3Lean.Proofs.Binary
