module

public import P3FieldAvx2
public import P3Monty31Avx2
public import Plonky3Lean.Proofs.Field.Avx2.Shims

@[expose] public section

/-!
# AVX2: the vector kernels of `PackedMontyField31AVX2`, lane by lane

The functions on `__m256i` that the packed operators call: p3-field's `mm256_mod_add` and
`mm256_mod_sub`, and p3-monty-31's `neg`, `mul` with `red_signed_to_canonical`, and
`halve_avx2`. For inputs whose lanes are canonical (`< p`, for an odd `p < 2^31`), each never
fails and each lane of its result is canonical, and is the lane-wise sum, difference, negation,
Montgomery product or half mod `p`, stated on natural numbers.
-/

open Aeneas Aeneas.Std CoreModels
open Plonky3Lean.Lib

namespace Plonky3Lean.Proofs.Avx2

open shims

/-! ## `mm256_mod_add` and `mm256_mod_sub` -/

/-- `mm256_mod_add(a, b, P)`, with `P` holding `p` in every lane and `a`, `b` canonical, is
`(a + b) mod p` in every lane. -/
theorem mod_add (a b P : V) (p : ℕ) (hp : p < 2 ^ 31) (ha : ∀ i < 8, ln a i < p)
    (hb : ∀ i < 8, ln b i < p) (hP : ∀ i < 8, ln P i = p) :
    ∃ r, p3_field.packed.x86_64_avx.mm256_mod_add a b P = .ok r ∧
      ∀ i < 8, ln r i = (ln a i + ln b i) % p := by
  obtain ⟨t, ht, htl⟩ := add_epi32 a b
  obtain ⟨u, hu, hul⟩ := sub_epi32 t P
  obtain ⟨r, hr, hrl⟩ := min_epu32 t u
  refine ⟨r, ?_, fun i hi => ?_⟩
  · unfold p3_field.packed.x86_64_avx.mm256_mod_add
    rw [ht, bind_ok, hu, bind_ok, hr]
  · have hai := ha i hi; have hbi := hb i hi
    rw [hrl i hi, hul i hi, htl i hi, hP i hi]
    by_cases h : p ≤ ln a i + ln b i
    · rw [Nat.mod_eq_sub_mod h, Nat.mod_eq_of_lt (by omega : ln a i + ln b i - p < p)]
      omega
    · rw [Nat.mod_eq_of_lt (by omega : ln a i + ln b i < p)]
      omega

/-- `mm256_mod_sub(a, b, P)`, with `P` holding `p` in every lane and `a`, `b` canonical, is
`(a + p - b) mod p` in every lane. -/
theorem mod_sub (a b P : V) (p : ℕ) (hp : p < 2 ^ 31) (ha : ∀ i < 8, ln a i < p)
    (hb : ∀ i < 8, ln b i < p) (hP : ∀ i < 8, ln P i = p) :
    ∃ r, p3_field.packed.x86_64_avx.mm256_mod_sub a b P = .ok r ∧
      ∀ i < 8, ln r i = (ln a i + p - ln b i) % p := by
  obtain ⟨t, ht, htl⟩ := sub_epi32 a b
  obtain ⟨u, hu, hul⟩ := add_epi32 t P
  obtain ⟨r, hr, hrl⟩ := min_epu32 t u
  refine ⟨r, ?_, fun i hi => ?_⟩
  · unfold p3_field.packed.x86_64_avx.mm256_mod_sub
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

open p3_monty_31_avx2 in
/-- `neg(val)`, with `PACKED_P` holding `p` in every lane and `val` canonical, is `(p - val) mod p`
in every lane: `p - val`, except `0` where `val` is `0`. -/
theorem neg {MPAVX2 : Type} (inst : x86_64_avx2.packing.MontyParametersAVX2 MPAVX2) (P a : V)
    (p : ℕ) (hp : p < 2 ^ 31) (hinst : inst.PACKED_P = .ok P) (hP : ∀ i < 8, ln P i = p)
    (ha : ∀ i < 8, ln a i < p) :
    ∃ r, x86_64_avx2.packing.neg inst a = .ok r ∧ ∀ i < 8, ln r i = (p - ln a i) % p := by
  obtain ⟨t, ht, htl⟩ := sub_epi32 P a
  obtain ⟨r, hr, hrl⟩ := sign_epi32 t a (fun i hi => by have := ha i hi; omega)
  refine ⟨r, ?_, fun i hi => ?_⟩
  · unfold x86_64_avx2.packing.neg
    rw [hinst, bind_ok, ht, bind_ok, hr]
  · have hai := ha i hi
    rw [hrl i hi, htl i hi, hP i hi]
    split
    · rename_i h; rw [h, Nat.sub_zero, Nat.mod_self]
    · rw [Nat.mod_eq_of_lt (by omega : p - ln a i < p)]
      omega

/-! ## `halve_avx2` -/

theorem halve_one : ∃ r, p3_monty_31_avx2.x86_64_avx2.utils.halve_avx2.ONE = .ok r ∧
    ∀ i < 8, ln r i = 1 := by
  obtain ⟨d, hd, hdx⟩ := array_repeat_eq 8#usize core.U32.Insts.CoreCloneClone (fun _ => rfl) 1#u32
  refine ⟨d, ?_, fun i hi => ?_⟩
  · unfold p3_monty_31_avx2.x86_64_avx2.utils.halve_avx2.ONE
    rw [hd, bind_ok]; rfl
  · have hi' : i < d.val.length := by rw [V.len]; exact hi
    simp only [ln, List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hi', Option.getD_some]
    rw [hdx _ (List.getElem_mem hi')]; rfl

open p3_monty_31_avx2 in
/-- `halve_avx2(input)`, for an odd `PRIME = p` with `p + 1 < 2^31` and `input` canonical, is in
every lane the canonical `r` with `2r ≡ input (mod p)`: `input / 2`, plus `(p + 1) / 2` when
`input` is odd.

`p + 1 < 2^31` is needed: the code computes `(PRIME as i32 + 1) / 2`, which overflows `i32`
at `p = 2^31 - 1`. -/
theorem halve_avx2 {MP : Type} (inst : data_traits.MontyParameters MP) (pp : Std.U32)
    (hprime : inst.PRIME = .ok pp) (hodd : pp.val % 2 = 1) (hp1 : pp.val + 1 < 2 ^ 31)
    (a : V) (ha : ∀ i < 8, ln a i < pp.val) :
    ∃ r, x86_64_avx2.utils.halve_avx2 inst a = .ok r ∧
      ∀ i < 8, ln r i < pp.val ∧ ln r i * 2 % pp.val = ln a i := by
  have hi1 := hcast_u32_i32_val pp (by omega)
  have hmin : IScalar.min .I32 = -2 ^ 31 := by
    simp only [IScalar.min, IScalarTy.I32_numBits_eq]
  have hmax : IScalar.max .I32 = 2 ^ 31 - 1 := by
    simp only [IScalar.max, IScalarTy.I32_numBits_eq]
  have hone : (1#i32 : Std.I32).val = 1 := by rfl
  obtain ⟨i2, hi2, hi2v⟩ := spec_imp_exists (IScalar.add_bv_spec (x := UScalar.hcast .I32 pp)
    (y := 1#i32) (by rw [hi1, hmin, hone]; omega)
    (by rw [hi1, hmax, hone]; omega))
  have hi2val : i2.val = (pp.val : Int) + 1 := by rw [hi2v.1, hi1]; rfl
  obtain ⟨i3, hi3, hi3v⟩ := IScalar.div_spec (x := i2) (y := 2#i32) (by decide)
    (by rw [hi2val, hmin]; omega)
  have hi3val : i3.val = (((pp.val + 1) / 2 : ℕ) : Int) := by
    rw [hi3v, hi2val, show ((2#i32 : Std.I32).val) = 2 from rfl,
      Int.tdiv_eq_ediv_of_nonneg (by omega)]
    omega
  obtain ⟨half, hh, hhl⟩ := set1_epi32 i3
  have hhalf : ∀ i < 8, ln half i = (pp.val + 1) / 2 := by
    intro i hi
    rw [hhl i hi]
    have := hcast_i32_u32_val i3 (by rw [hi3val]; omega)
    rw [hi3val] at this; exact_mod_cast this
  obtain ⟨one, hone, honel⟩ := halve_one
  obtain ⟨lb, hlb, hlbl⟩ := and_si256 a one
  have hlb2 : ∀ i < 8, ln lb i = ln a i % 2 := by
    intro i hi; rw [hlbl i hi, honel i hi, Nat.and_one_is_mod]
  obtain ⟨t, ht, htl⟩ := srli_epi32_one a
  obtain ⟨mh, hmh, hmhl⟩ := sign_epi32 half lb (fun i hi => by rw [hlb2 i hi]; omega)
  obtain ⟨r, hr, hrl⟩ := add_epi32 t mh
  refine ⟨r, ?_, fun i hi => ?_⟩
  · unfold x86_64_avx2.utils.halve_avx2
    rw [hprime, bind_ok, lift_eq, bind_ok, hi2, bind_ok, hi3, bind_ok, hh, bind_ok, hone, bind_ok,
      hlb, bind_ok, ht, bind_ok, hmh, bind_ok, hr]
  · have hai := ha i hi
    rw [hrl i hi, htl i hi, hmhl i hi, hlb2 i hi, hhalf i hi]
    by_cases h2 : ln a i % 2 = 0
    · simp only [h2, ↓reduceIte, Nat.add_zero]
      rw [Nat.mod_eq_of_lt (by omega : ln a i / 2 < 2 ^ 32)]
      refine ⟨by omega, ?_⟩
      rw [show ln a i / 2 * 2 = ln a i by omega, Nat.mod_eq_of_lt hai]
    · simp only [h2, ↓reduceIte]
      rw [Nat.mod_eq_of_lt (by omega : ln a i / 2 + (pp.val + 1) / 2 < 2 ^ 32)]
      refine ⟨by omega, ?_⟩
      rw [show (ln a i / 2 + (pp.val + 1) / 2) * 2 = ln a i + pp.val by omega, Nat.add_mod_right,
        Nat.mod_eq_of_lt hai]

/-! ## `mul` and `red_signed_to_canonical` -/

/-- The value `monty_mul` leaves in the high lane of a 64-bit pair whose low lanes multiply to
`X`: the high half of `X - t · p` (mod `2^32`), for Montgomery's quotient `t = X · mu mod 2^32`.
It is `X · 2^(-32) mod p` up to a multiple of `p`, read as a signed value in `(-p, p)`. -/
def montyHi (p mu X : ℕ) : ℕ :=
  (X / 2 ^ 32 + (2 ^ 32 - (X % 2 ^ 32 * mu % 2 ^ 32) * p / 2 ^ 32)) % 2 ^ 32

/-- `red_signed_to_canonical` of `montyHi`: `min(h, h + p mod 2^32)` is the canonical `r` with
`r · 2^32 ≡ X (mod p)`, for `X < p^2`. -/
theorem montyHi_red (p mu X : ℕ) (hp : p < 2 ^ 31) (hp0 : 0 < p) (hinv : p * mu % 2 ^ 32 = 1)
    (hX : X < p * p) :
    let h := montyHi p mu X
    min h ((h + p) % 2 ^ 32) < p ∧ min h ((h + p) % 2 ^ 32) * 2 ^ 32 % p = X % p := by
  intro h
  set T := X % 2 ^ 32 * mu % 2 ^ 32 with hT
  have hTlt : T < 2 ^ 32 := Nat.mod_lt _ (by norm_num)
  have hcong : T * p % 2 ^ 32 = X % 2 ^ 32 := by
    rw [hT, Nat.mod_mul_mod, Nat.mul_assoc, Nat.mul_mod, Nat.mul_comm mu, hinv, Nat.mul_one,
      Nat.mod_mod, Nat.mod_mod]
  have hXp : X < 2 ^ 32 * p :=
    lt_of_lt_of_le hX (Nat.mul_le_mul_right _ (by omega))
  have hTp : T * p < 2 ^ 32 * p := Nat.mul_lt_mul_of_pos_right hTlt hp0
  have hx := Nat.div_add_mod X (2 ^ 32)
  have ht := Nat.div_add_mod (T * p) (2 ^ 32)
  have hxh : X / 2 ^ 32 < p := by omega
  have hth : T * p / 2 ^ 32 < p := by omega
  have hh : h = (X / 2 ^ 32 + (2 ^ 32 - T * p / 2 ^ 32)) % 2 ^ 32 := rfl
  by_cases hc : T * p / 2 ^ 32 ≤ X / 2 ^ 32
  · have h1 : h = X / 2 ^ 32 - T * p / 2 ^ 32 := by rw [hh]; omega
    have h2 : (h + p) % 2 ^ 32 = h + p := Nat.mod_eq_of_lt (by omega)
    rw [h2, Nat.min_eq_left (by omega)]
    refine ⟨by omega, ?_⟩
    have : h * 2 ^ 32 + p * T = X := by rw [Nat.mul_comm p]; omega
    rw [← this, Nat.add_mul_mod_self_left]
  · have h1 : h = X / 2 ^ 32 + 2 ^ 32 - T * p / 2 ^ 32 := by rw [hh]; omega
    have h2 : (h + p) % 2 ^ 32 = X / 2 ^ 32 + p - T * p / 2 ^ 32 := by rw [h1]; omega
    rw [h2, Nat.min_eq_right (by omega)]
    refine ⟨by omega, ?_⟩
    have : (X / 2 ^ 32 + p - T * p / 2 ^ 32) * 2 ^ 32 + p * T = X + p * 2 ^ 32 := by
      rw [Nat.sub_mul, Nat.add_mul, Nat.mul_comm p T]; omega
    rw [← Nat.add_mul_mod_self_left ((X / 2 ^ 32 + p - T * p / 2 ^ 32) * 2 ^ 32) p T, this,
      Nat.add_mul_mod_self_left]

open p3_monty_31_avx2 in
theorem movehdup_epi32 (x : V) : ∃ r, x86_64_avx2.packing.movehdup_epi32 x = .ok r ∧
    ∀ i < 8, ln r i = ln x (2 * (i / 2) + 1) := by
  obtain ⟨r, hr, hrl⟩ := movehdup_ps x
  refine ⟨r, ?_, hrl⟩
  unfold x86_64_avx2.packing.movehdup_epi32
  rw [castsi256_ps, bind_ok, hr, bind_ok, castps_si256]

open p3_monty_31_avx2 in
/-- `monty_mul(x, y)`: for each 64-bit pair `j`, `montyHi` of the product of the low lanes in
the high lane `2j + 1`. -/
theorem monty_mul {MPAVX2 : Type} (inst : x86_64_avx2.packing.MontyParametersAVX2 MPAVX2)
    (P M x y : V) (p mu : ℕ) (hPP : inst.PACKED_P = .ok P) (hP : ∀ i < 8, ln P i = p)
    (hMM : inst.PACKED_MU = .ok M) (hM : ∀ i < 8, ln M i = mu) :
    ∃ d, x86_64_avx2.packing.monty_mul inst x y = .ok d ∧
      ∀ j < 4, ln d (2 * j + 1) = montyHi p mu (ln x (2 * j) * ln y (2 * j)) := by
  obtain ⟨prod, hprod, hprodl⟩ := mul_epu32 x y
  obtain ⟨q, hq, hql⟩ := mul_epu32 prod M
  obtain ⟨qp, hqp, hqpl⟩ := mul_epu32 q P
  obtain ⟨d, hd, hdl⟩ := sub_epi32 prod qp
  refine ⟨d, ?_, fun j hj => ?_⟩
  · unfold x86_64_avx2.packing.monty_mul x86_64_avx2.packing.partial_monty_red_unsigned_to_signed
    rw [hprod, bind_ok, hMM, bind_ok, hq, bind_ok, hPP, bind_ok, hqp, bind_ok, hd]
  · rw [hdl _ (by omega), (hprodl j hj).2, (hqpl j hj).2, (hql j hj).1, (hprodl j hj).1,
      hM _ (by omega), hP _ (by omega)]
    rfl

open p3_monty_31_avx2 in
/-- `red_signed_to_canonical(mul(a, b))`, with `PACKED_P` and `PACKED_MU` holding `p` and `mu`
in every lane and `a`, `b` canonical, is in every lane the canonical `r` with
`r · 2^32 ≡ a · b (mod p)`: the Montgomery product. -/
theorem mul_red {MPAVX2 : Type} (inst : x86_64_avx2.packing.MontyParametersAVX2 MPAVX2)
    (P M a b : V) (p mu : ℕ) (hp : p < 2 ^ 31) (hp0 : 0 < p) (hinv : p * mu % 2 ^ 32 = 1)
    (hPP : inst.PACKED_P = .ok P) (hP : ∀ i < 8, ln P i = p)
    (hMM : inst.PACKED_MU = .ok M) (hM : ∀ i < 8, ln M i = mu)
    (ha : ∀ i < 8, ln a i < p) (hb : ∀ i < 8, ln b i < p) :
    ∃ t, x86_64_avx2.packing.mul inst a b = .ok t ∧
      ∃ r, x86_64_avx2.packing.red_signed_to_canonical inst t = .ok r ∧
        ∀ i < 8, ln r i < p ∧ ln r i * 2 ^ 32 % p = ln a i * ln b i % p := by
  obtain ⟨ao, hao, haol⟩ := movehdup_epi32 a
  obtain ⟨bo, hbo, hbol⟩ := movehdup_epi32 b
  obtain ⟨de, hde, hdel⟩ := monty_mul inst P M a b p mu hPP hP hMM hM
  obtain ⟨dd, hdd, hddl⟩ := monty_mul inst P M ao bo p mu hPP hP hMM hM
  obtain ⟨eh, heh, hehl⟩ := movehdup_epi32 de
  obtain ⟨t, ht, htl⟩ := blend_epi32_170 eh dd
  have htv : ∀ i < 8, ln t i = montyHi p mu (ln a i * ln b i) := by
    intro i hi
    rw [htl i hi]
    split
    · rename_i hodd
      obtain ⟨j, rfl⟩ : ∃ j, i = 2 * j + 1 := ⟨i / 2, by omega⟩
      rw [hddl j (by omega), haol _ (by omega), hbol _ (by omega),
        show 2 * (2 * j / 2) + 1 = 2 * j + 1 by omega]
    · obtain ⟨j, rfl⟩ : ∃ j, i = 2 * j := ⟨i / 2, by omega⟩
      rw [hehl _ hi, show 2 * (2 * j / 2) + 1 = 2 * j + 1 by omega, hdel j (by omega)]
  obtain ⟨c, hc, hcl⟩ := add_epi32 t P
  obtain ⟨r, hr, hrl⟩ := min_epu32 t c
  refine ⟨t, ?_, r, ?_, fun i hi => ?_⟩
  · unfold x86_64_avx2.packing.mul x86_64_avx2.packing.blend_evn_odd
    rw [hao, bind_ok, hbo, bind_ok, hde, bind_ok, hdd, bind_ok, heh, bind_ok, ht]
  · unfold x86_64_avx2.packing.red_signed_to_canonical
    rw [hPP, bind_ok, hc, bind_ok, hr]
  · rw [hrl i hi, hcl i hi, hP i hi, htv i hi]
    exact montyHi_red p mu _ hp hp0 hinv (Nat.mul_lt_mul'' (ha i hi) (hb i hi))

end Plonky3Lean.Proofs.Avx2
