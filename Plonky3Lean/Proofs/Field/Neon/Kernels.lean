module

public import P3FieldNeon
public import P3Monty31Neon
public import Plonky3Lean.Proofs.Field.Neon.Shims

@[expose] public section

/-!
# NEON: the vector kernels of `PackedMontyField31Neon`, lane by lane

The functions on `uint32x4_t` and `int32x4_t` that the packed operators call: p3-field's
`uint32x4_mod_add` and `uint32x4_mod_sub`, and p3-monty-31's `neg`, `mul` and `halve_neon`.
For inputs whose lanes are canonical (`< p`, for `0 < p < 2^31`), each never fails and each
lane of its result is canonical, and is the lane-wise sum, difference, negation or half mod `p`,
stated on natural numbers.

`mul` is NEON's signed Montgomery multiplication, built on `vqdmulhq_s32` (the high half of a
doubled product). `monty_signed` is its arithmetic, for any `p` and `mu` with `p · mu ≡ 1`
(mod `2^32`) and inputs in `[-p, p]`, the range the code documents. `mul` is the statement
about the code, for the same inputs.
-/

open Aeneas Aeneas.Std CoreModels
open Plonky3Lean.Lib

namespace Plonky3Lean.Proofs.Neon

open shims

/-! ## `uint32x4_mod_add` and `uint32x4_mod_sub` -/

/-- `uint32x4_mod_add(a, b, P)`, with `P` holding `p` in every lane and `a`, `b` canonical, is
`(a + b) mod p` in every lane. -/
theorem mod_add (a b P : U) (p : ℕ) (hp : p < 2 ^ 31) (ha : ∀ i < 4, ln a i < p)
    (hb : ∀ i < 4, ln b i < p) (hP : ∀ i < 4, ln P i = p) :
    ∃ r, p3_field.packed.aarch64_neon.uint32x4_mod_add a b P = .ok r ∧
      ∀ i < 4, ln r i = (ln a i + ln b i) % p := by
  obtain ⟨t, ht, htl⟩ := shims.vaddq_u32 a b
  obtain ⟨u, hu, hul⟩ := shims.vsubq_u32 t P
  obtain ⟨r, hr, hrl⟩ := shims.vminq_u32 t u
  refine ⟨r, ?_, fun i hi => ?_⟩
  · unfold p3_field.packed.aarch64_neon.uint32x4_mod_add
    rw [ht, bind_ok, hu, bind_ok, hr]
  · have hai := ha i hi; have hbi := hb i hi
    rw [hrl i hi, hul i hi, htl i hi, hP i hi]
    by_cases h : p ≤ ln a i + ln b i
    · rw [Nat.mod_eq_sub_mod h, Nat.mod_eq_of_lt (by omega : ln a i + ln b i - p < p)]
      omega
    · rw [Nat.mod_eq_of_lt (by omega : ln a i + ln b i < p)]
      omega

/-- `uint32x4_mod_sub(a, b, P)`, with `P` holding `p` in every lane and `a`, `b` canonical, is
`(a + p - b) mod p` in every lane. -/
theorem mod_sub (a b P : U) (p : ℕ) (hp : p < 2 ^ 31) (ha : ∀ i < 4, ln a i < p)
    (hb : ∀ i < 4, ln b i < p) (hP : ∀ i < 4, ln P i = p) :
    ∃ r, p3_field.packed.aarch64_neon.uint32x4_mod_sub a b P = .ok r ∧
      ∀ i < 4, ln r i = (ln a i + p - ln b i) % p := by
  obtain ⟨t, ht, htl⟩ := shims.vsubq_u32 a b
  obtain ⟨u, hu, hul⟩ := shims.vaddq_u32 t P
  obtain ⟨r, hr, hrl⟩ := shims.vminq_u32 t u
  refine ⟨r, ?_, fun i hi => ?_⟩
  · unfold p3_field.packed.aarch64_neon.uint32x4_mod_sub
    rw [ht, bind_ok, hu, bind_ok, hr]
  · have hai := ha i hi; have hbi := hb i hi
    rw [hrl i hi, hul i hi, htl i hi, hP i hi]
    by_cases h : ln b i ≤ ln a i
    · rw [Nat.mod_eq_sub_mod (by omega : p ≤ ln a i + p - ln b i),
        Nat.mod_eq_of_lt (by omega : ln a i + p - ln b i - p < p)]
      omega
    · rw [Nat.mod_eq_of_lt (by omega : ln a i + p - ln b i < p)]
      omega

/-! ## `neg` -/

open p3_monty_31_neon in
/-- `neg(val)`, with `PACKED_P` holding `p` in every lane and `val` canonical, is `(p - val) mod p`
in every lane: `p - val`, except `0` where `val` is `0`. -/
theorem neg {MPNeon : Type} (inst : aarch64_neon.packing.MontyParametersNeon MPNeon) (P a : U)
    (p : ℕ) (hp : p < 2 ^ 31) (hinst : inst.PACKED_P = .ok P) (hP : ∀ i < 4, ln P i = p)
    (ha : ∀ i < 4, ln a i < p) :
    ∃ r, aarch64_neon.packing.neg inst a = .ok r ∧ ∀ i < 4, ln r i = (p - ln a i) % p := by
  obtain ⟨t, ht, htl⟩ := shims.vsubq_u32 P a
  obtain ⟨z, hz, hzl⟩ := shims.vceqzq_u32 a
  obtain ⟨r, hr, hrl⟩ := shims.vbicq_u32 t z
  refine ⟨r, ?_, fun i hi => ?_⟩
  · unfold aarch64_neon.packing.neg
    rw [hinst, bind_ok, ht, bind_ok, hz, bind_ok, hr]
  · have hai := ha i hi
    have hr' : ln r i = ((t.val[i]!).bv &&& ~~~(z.val[i]!).bv).toNat := by
      show (r.val[i]!).bv.toNat = _
      rw [hrl i hi]
    have hz' := hzl i hi
    by_cases h0 : ln a i = 0
    · simp only [h0, ↓reduceIte] at hz'
      have hzb : (z.val[i]!).bv = BitVec.allOnes 32 :=
        BitVec.eq_of_toNat_eq (by rw [BitVec.toNat_allOnes]; exact hz')
      rw [hr', hzb, BitVec.not_allOnes, BitVec.and_zero, h0, Nat.sub_zero, Nat.mod_self]
      rfl
    · simp only [h0, ↓reduceIte] at hz'
      have hzb : (z.val[i]!).bv = 0#32 := BitVec.eq_of_toNat_eq (by rw [BitVec.toNat_ofNat]; exact hz')
      rw [hr', hzb, BitVec.not_zero, BitVec.and_allOnes]
      show ln t i = _
      rw [htl i hi, hP i hi, Nat.mod_eq_of_lt (by omega : p - ln a i < p)]
      omega

/-! ## `halve_neon` -/

open p3_monty_31_neon in
/-- `halve_neon(input)`, with `PACKED_P` holding an odd `p` in every lane and `input` canonical,
is in every lane the canonical `r` with `2r ≡ input (mod p)`: `input / 2`, or `(input + p) / 2`
when `input` is odd. The halving add has a 33-bit intermediate, so no bound on `p` beyond
`p < 2^31` is needed. -/
theorem halve_neon {PMP : Type} (inst : data_traits.PackedMontyParameters PMP) (P a : U) (p : ℕ)
    (hp : p < 2 ^ 31) (hodd : p % 2 = 1)
    (hinst : inst.aarch64_neonpackingMontyParametersNeonInst.PACKED_P = .ok P)
    (hP : ∀ i < 4, ln P i = p) (ha : ∀ i < 4, ln a i < p) :
    ∃ r, aarch64_neon.utils.halve_neon inst a = .ok r ∧
      ∀ i < 4, ln r i < p ∧ ln r i * 2 % p = ln a i := by
  obtain ⟨one, hone, honel⟩ := shims.vdupq_n_u32 1#u32
  obtain ⟨m, hm, hml⟩ := shims.vtstq_u32 a one
  obtain ⟨t, ht, htl⟩ := shims.vandq_u32 P m
  obtain ⟨r, hr, hrl⟩ := shims.vhaddq_u32 a t
  refine ⟨r, ?_, fun i hi => ?_⟩
  · unfold aarch64_neon.utils.halve_neon
    rw [hone, bind_ok, hm, bind_ok, hinst, bind_ok, ht, bind_ok, hr]
  · have hai := ha i hi
    have hmi : ln m i = if ln a i % 2 = 0 then 0 else 2 ^ 32 - 1 := by
      rw [hml i hi, honel i hi, show (1#u32 : Std.U32).val = 1 from rfl, Nat.and_one_is_mod]
    have hti : ln t i = if ln a i % 2 = 0 then 0 else p := by
      rw [htl i hi, hmi, hP i hi]
      split
      · exact Nat.and_zero p
      · exact Nat.and_two_pow_sub_one_of_lt_two_pow (by omega)
    rw [hrl i hi, hti]
    split
    · rename_i h2
      refine ⟨by omega, ?_⟩
      rw [Nat.add_zero, show ln a i / 2 * 2 = ln a i by omega, Nat.mod_eq_of_lt hai]
    · rename_i h2
      refine ⟨by omega, ?_⟩
      rw [show (ln a i + p) / 2 * 2 = ln a i + p by omega, Nat.add_mod_right,
        Nat.mod_eq_of_lt hai]

/-! ## `mul`: NEON's signed Montgomery multiplication -/

/-- The arithmetic of `mul_with_precomp::<_, true>`, for `p · mu ≡ 1 (mod 2^32)` and inputs in
`[-p, p]` (the code's documented range). With `B = 2^32` and `mu_s` any integer `≡ mu (mod B)`
(the `i32` lanes of `PACKED_MU`):

* `m = smod_B(b · mu_s)` and `q = smod_B(a · m)`, so `q ≡ mu · a · b (mod B)` (`vmulq_s32`);
* `c = ⌊2ab / B⌋` and `h = ⌊2qp / B⌋` (`vqdmulhq_s32`, which does not saturate here);
* `d = ⌊(c - h) / 2⌋` (`vhsubq_s32`).

Then `d` is the exact quotient `(ab - qp) / B`, so `d · B ≡ a · b (mod p)`; `d ∈ (-p, p)`; and
`d < 0` exactly when `c < h`, which is when the code adds `p`. -/
theorem monty_signed (p mu : ℕ) (hp : p < 2 ^ 31) (hp0 : 0 < p) (hinv : p * mu % 2 ^ 32 = 1)
    (a b mu_s m q c h d : ℤ) (hmu : mu_s % 2 ^ 32 = mu) (ha : |a| ≤ p) (hb : |b| ≤ p)
    (hm : m = Int.bmod (b * mu_s) (2 ^ 32)) (hq : q = Int.bmod (a * m) (2 ^ 32))
    (hc : c = a * b / 2 ^ 31) (hh : h = q * p / 2 ^ 31) (hd : d = (c - h) / 2) :
    (c < h ↔ d < 0) ∧ -(p : ℤ) < d ∧ d < p ∧ d * 2 ^ 32 % p = a * b % p := by
  -- `q` is a balanced residue.
  have hq1 : -2 ^ 31 ≤ q := by
    have := Int.le_bmod (x := a * m) (m := 2 ^ 32) (by norm_num)
    rw [hq]; simpa using this
  have hq2 : q < 2 ^ 31 := by
    have := Int.bmod_lt (x := a * m) (m := 2 ^ 32) (by norm_num)
    rw [hq]; simpa using this
  -- `q p ≡ a b (mod B)`.
  have h1 : q ≡ a * m [ZMOD 2 ^ 32] := by
    rw [hq]; show _ % _ = _ % _; exact_mod_cast Int.bmod_emod (x := a * m) (m := 2 ^ 32)
  have h2 : m ≡ b * mu_s [ZMOD 2 ^ 32] := by
    rw [hm]; show _ % _ = _ % _; exact_mod_cast Int.bmod_emod (x := b * mu_s) (m := 2 ^ 32)
  have h3 : mu_s ≡ mu [ZMOD 2 ^ 32] := by
    show _ % _ = _ % _
    rw [hmu, Int.emod_eq_of_lt (by positivity) (by
      have : mu_s % 2 ^ 32 < 2 ^ 32 := Int.emod_lt_of_pos _ (by norm_num)
      omega)]
  have h4 : (p : ℤ) * mu ≡ 1 [ZMOD 2 ^ 32] := by
    show _ % _ = _ % _
    exact_mod_cast hinv
  have hcong : q * p ≡ a * b [ZMOD 2 ^ 32] := by
    calc q * p ≡ a * m * p [ZMOD 2 ^ 32] := h1.mul_right _
      _ ≡ a * (b * mu_s) * p [ZMOD 2 ^ 32] := (h2.mul_left a).mul_right _
      _ = a * b * (p * mu_s) := by ring
      _ ≡ a * b * (p * mu) [ZMOD 2 ^ 32] := (h3.mul_left (p : ℤ)).mul_left (a * b)
      _ ≡ a * b * 1 [ZMOD 2 ^ 32] := h4.mul_left (a * b)
      _ = a * b := by ring
  obtain ⟨D, hD⟩ : (2 ^ 32 : ℤ) ∣ a * b - q * p := Int.ModEq.dvd hcong
  -- The floors.
  have hc0 := Int.mul_ediv_add_emod (a * b) (2 ^ 31)
  have hc1 := Int.emod_nonneg (a * b) (by norm_num : (2 ^ 31 : ℤ) ≠ 0)
  have hc2 := Int.emod_lt_of_pos (a * b) (by norm_num : (0 : ℤ) < 2 ^ 31)
  have hh0 := Int.mul_ediv_add_emod (q * p) (2 ^ 31)
  have hh1 := Int.emod_nonneg (q * p) (by norm_num : (2 ^ 31 : ℤ) ≠ 0)
  have hh2 := Int.emod_lt_of_pos (q * p) (by norm_num : (0 : ℤ) < 2 ^ 31)
  rw [← hc] at hc0
  rw [← hh] at hh0
  have hcd : c - h = 2 * D := by omega
  have hdD : d = D := by rw [hd]; omega
  -- The bounds.
  have hp0' : (0 : ℤ) ≤ p := by positivity
  have hpI : (p : ℤ) < 2 ^ 31 := by exact_mod_cast hp
  have hab1 : a * b ≤ p * p := by
    calc a * b ≤ |a * b| := le_abs_self _
      _ = |a| * |b| := abs_mul a b
      _ ≤ p * p := mul_le_mul ha hb (abs_nonneg _) hp0'
  have hab2 : -((p : ℤ) * p) ≤ a * b := by
    have h5 : -(a * b) ≤ |a * b| := neg_le_abs _
    have h6 : |a * b| ≤ p * p := by
      rw [abs_mul]; exact mul_le_mul ha hb (abs_nonneg _) hp0'
    linarith
  have hpp : (p : ℤ) * p < 2 ^ 31 * p := by
    have : (0 : ℤ) < p := by exact_mod_cast hp0
    nlinarith
  have hqp1 : q * p ≤ (2 ^ 31 - 1) * p := by nlinarith
  have hqp2 : -(2 ^ 31) * (p : ℤ) ≤ q * p := by nlinarith
  have hp1 : (0 : ℤ) < p := by exact_mod_cast hp0
  refine ⟨by rw [hdD]; omega, by rw [hdD]; omega, by rw [hdD]; omega, ?_⟩
  rw [hdD]
  have : D * 2 ^ 32 = a * b + p * (-q) := by linarith
  rw [this, Int.add_mul_emod_self_left]

open p3_monty_31_neon in
/-- `mul(lhs, rhs)`, with `PACKED_P` holding `p` and `PACKED_MU` holding `mu` (as `i32` lanes
`≡ mu mod 2^32`) in every lane, for `p · mu ≡ 1 (mod 2^32)` and `lhs`, `rhs` in `[-p, p]`, is in
every lane the canonical `r` with `r · 2^32 ≡ lhs · rhs (mod p)`: the Montgomery product. -/
theorem mul {MPNeon : Type} (inst : aarch64_neon.packing.MontyParametersNeon MPNeon)
    (P : U) (M a b : S) (p mu : ℕ) (hp : p < 2 ^ 31) (hp0 : 0 < p) (hinv : p * mu % 2 ^ 32 = 1)
    (hPP : inst.PACKED_P = .ok P) (hP : ∀ i < 4, ln P i = p)
    (hMM : inst.PACKED_MU = .ok M) (hM : ∀ i < 4, sn M i % 2 ^ 32 = mu)
    (ha : ∀ i < 4, |sn a i| ≤ p) (hb : ∀ i < 4, |sn b i| ≤ p) :
    ∃ r, aarch64_neon.packing.mul inst a b = .ok r ∧
      ∀ i < 4, ln r i < p ∧ (ln r i : ℤ) * 2 ^ 32 % p = sn a i * sn b i % p := by
  have hpI : (p : ℤ) < 2 ^ 31 := by exact_mod_cast hp
  have hp0' : (0 : ℤ) ≤ p := by positivity
  have hprod : ∀ x y : ℤ, |x| ≤ p → |y| ≤ p → x * y < 2 ^ 62 := by
    intro x y hx hy
    have hxy : |x| * |y| ≤ p * p := mul_le_mul hx hy (abs_nonneg _) hp0'
    have : (p : ℤ) * p < 2 ^ 62 := by nlinarith
    calc x * y ≤ |x * y| := le_abs_self _
      _ = |x| * |y| := abs_mul x y
      _ < 2 ^ 62 := by linarith
  -- `mulby_mu`
  obtain ⟨mr, hmr, hmrl⟩ := shims.vmulq_s32 b M
  -- `get_c_hi`
  obtain ⟨ch, hch, hchl⟩ := shims.vqdmulhq_s32 a b (fun i hi => hprod _ _ (ha i hi) (hb i hi))
  -- `get_qp_hi`
  obtain ⟨q, hq, hql⟩ := shims.vmulq_s32 a mr
  obtain ⟨ix, hix, hixl⟩ := shims.vreinterpretq_s32_u32 P
  have hixv : ∀ i < 4, sn ix i = p := by
    intro i hi; rw [hixl i hi, hP i hi]; exact bmod32_self (by omega) (by omega)
  have hqb : ∀ i < 4, -2 ^ 31 ≤ sn q i ∧ sn q i < 2 ^ 31 := by
    intro i hi
    rw [hql i hi]
    refine ⟨?_, ?_⟩
    · have := Int.le_bmod (x := sn a i * sn mr i) (m := 2 ^ 32) (by norm_num); simpa using this
    · have := Int.bmod_lt (x := sn a i * sn mr i) (m := 2 ^ 32) (by norm_num); simpa using this
  obtain ⟨qh, hqh, hqhl⟩ := shims.vqdmulhq_s32 q ix (fun i hi => by
    rw [hixv i hi]
    have := hqb i hi
    nlinarith)
  obtain ⟨d, hd, hdl⟩ := shims.vhsubq_s32 ch qh
  obtain ⟨uf, huf, hufl⟩ := shims.vcltq_s32 ch qh
  obtain ⟨du, hdu, hdul⟩ := shims.vreinterpretq_u32_s32 d
  obtain ⟨red, hred, hredl⟩ := shims.vmlsq_u32 du uf P
  obtain ⟨rs, hrs, hrsl⟩ := shims.vreinterpretq_s32_u32 red
  obtain ⟨r, hr, hrl⟩ := shims.vreinterpretq_u32_s32 rs
  refine ⟨r, ?_, fun i hi => ?_⟩
  · unfold aarch64_neon.packing.mul aarch64_neon.packing.mulby_mu
      aarch64_neon.packing.mul_with_precomp aarch64_neon.packing.get_c_hi
      aarch64_neon.packing.get_qp_hi aarch64_neon.packing.confuse_compiler
    simp only [hMM, hmr, hch, hq, hPP, hix, hqh, hd, huf, hdu, hred, hrs, hr, bind_ok, ite_true]
  · obtain ⟨hneg, hlo, hhi, hmod⟩ := monty_signed p mu hp hp0 hinv (sn a i) (sn b i) (sn M i)
      (sn mr i) (sn q i) (sn ch i) (sn qh i) (sn d i) (hM i hi) (ha i hi) (hb i hi) (hmrl i hi)
      (hql i hi) (hchl i hi) (by rw [hqhl i hi, hixv i hi]) (hdl i hi)
    -- Lane `i` of the result is `d`, plus `p` where `c < h`.
    have hbits : (ln r i : ℤ) = ln red i := by
      have hlt := u32_lt (red.val[i]!)
      rw [hrl i hi, hrsl i hi]
      have := Int.bmod_emod (x := (ln red i : ℤ)) (m := 2 ^ 32)
      simp only [Nat.cast_pow, Nat.cast_ofNat] at this
      rw [this]
      exact Int.emod_eq_of_lt (by positivity) (by simp only [ln]; omega)
    have hred' := hredl i hi
    have hduv := hdul i hi
    have hufv := hufl i hi
    have hPv := hP i hi
    have hrv : (ln r i : ℤ) = if sn ch i < sn qh i then sn d i + p else sn d i := by
      rw [hbits]
      by_cases hc : sn ch i < sn qh i
      · simp only [hc, ↓reduceIte] at hufv ⊢
        rw [hufv, hPv] at hred'
        have hd0 := hneg.mp hc
        omega
      · simp only [hc, ↓reduceIte] at hufv ⊢
        rw [hufv, hPv] at hred'
        have hd0 : 0 ≤ sn d i := by have := hneg.not.mp hc; omega
        omega
    have hr0 : 0 ≤ (ln r i : ℤ) ∧ (ln r i : ℤ) < p ∧ (ln r i : ℤ) * 2 ^ 32 % p =
        sn a i * sn b i % p := by
      rw [hrv]
      by_cases hc : sn ch i < sn qh i
      · simp only [hc, ↓reduceIte]
        have hd0 := hneg.mp hc
        refine ⟨by omega, by omega, ?_⟩
        rw [Int.add_mul, Int.add_mul_emod_self_left, hmod]
      · simp only [hc, ↓reduceIte]
        have hd0 : 0 ≤ sn d i := by have := hneg.not.mp hc; omega
        exact ⟨hd0, hhi, hmod⟩
    exact ⟨by exact_mod_cast hr0.2.1, hr0.2.2⟩

end Plonky3Lean.Proofs.Neon
