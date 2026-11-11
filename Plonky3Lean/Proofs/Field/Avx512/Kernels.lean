module

public import P3FieldAvx512
public import P3Monty31Avx512
public import Plonky3Lean.Proofs.Field.Avx2.Kernels
public import Plonky3Lean.Proofs.Field.Avx512.Shims

@[expose] public section

/-!
# AVX-512: the vector kernels of `PackedMontyField31AVX512`, lane by lane

The functions on `__m512i` that the packed operators call: p3-field's `mm512_mod_add` and
`mm512_mod_sub`, and p3-monty-31's `neg`, `mul` and `halve_avx512`. For inputs whose lanes are
canonical (`< p`, for an odd `p < 2^31`), each never fails and each lane of its result is
canonical, and is the lane-wise sum, difference, negation, Montgomery product or half mod `p`,
stated on natural numbers.

`mul` reduces with masks: it gathers the high halves of the sixteen 64-bit products and of the
sixteen `q · p` with a masked `vmovshdup` (`mask_movehdup_epi32`, whose `asm!` block pre-patch
`monty-31/040` replaces by its intrinsic), and adds `p` back in the lanes where the subtraction
of the two underflows (a `vpcmpltud` mask). Its arithmetic is AVX2's Montgomery reduction
(`Plonky3Lean.Proofs.Avx2.montyHi`), with that correction in place of AVX2's `min`.
-/

open Aeneas Aeneas.Std CoreModels
open Plonky3Lean.Lib

namespace Plonky3Lean.Proofs.Avx512

open shims

/-! ## `mm512_mod_add` and `mm512_mod_sub` -/

/-- `mm512_mod_add(a, b, P)`, with `P` holding `p` in every lane and `a`, `b` canonical, is
`(a + b) mod p` in every lane. -/
theorem mod_add (a b P : V) (p : ℕ) (hp : p < 2 ^ 31) (ha : ∀ i < 16, ln a i < p)
    (hb : ∀ i < 16, ln b i < p) (hP : ∀ i < 16, ln P i = p) :
    ∃ r, p3_field.packed.x86_64_avx.mm512_mod_add a b P = .ok r ∧
      ∀ i < 16, ln r i = (ln a i + ln b i) % p := by
  obtain ⟨t, ht, htl⟩ := add_epi32 a b
  obtain ⟨u, hu, hul⟩ := sub_epi32 t P
  obtain ⟨r, hr, hrl⟩ := min_epu32 t u
  refine ⟨r, ?_, fun i hi => ?_⟩
  · unfold p3_field.packed.x86_64_avx.mm512_mod_add
    rw [ht, bind_ok, hu, bind_ok, hr]
  · have hai := ha i hi; have hbi := hb i hi
    rw [hrl i hi, hul i hi, htl i hi, hP i hi]
    by_cases h : p ≤ ln a i + ln b i
    · rw [Nat.mod_eq_sub_mod h, Nat.mod_eq_of_lt (by omega : ln a i + ln b i - p < p)]
      omega
    · rw [Nat.mod_eq_of_lt (by omega : ln a i + ln b i < p)]
      omega

/-- `mm512_mod_sub(a, b, P)`, with `P` holding `p` in every lane and `a`, `b` canonical, is
`(a + p - b) mod p` in every lane. -/
theorem mod_sub (a b P : V) (p : ℕ) (hp : p < 2 ^ 31) (ha : ∀ i < 16, ln a i < p)
    (hb : ∀ i < 16, ln b i < p) (hP : ∀ i < 16, ln P i = p) :
    ∃ r, p3_field.packed.x86_64_avx.mm512_mod_sub a b P = .ok r ∧
      ∀ i < 16, ln r i = (ln a i + p - ln b i) % p := by
  obtain ⟨t, ht, htl⟩ := sub_epi32 a b
  obtain ⟨u, hu, hul⟩ := add_epi32 t P
  obtain ⟨r, hr, hrl⟩ := min_epu32 t u
  refine ⟨r, ?_, fun i hi => ?_⟩
  · unfold p3_field.packed.x86_64_avx.mm512_mod_sub
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

open p3_monty_31_avx512 in
/-- `neg(val)`, with `PACKED_P` holding `p` in every lane and `val` canonical, is `(p - val) mod p`
in every lane: `p - val` where `val` is nonzero (`vptestmd`), and `0` where it is `0` (the
zeroing mask of `vpsubd`). -/
theorem neg {MPAVX512 : Type} (inst : x86_64_avx512.packing.MontyParametersAVX512 MPAVX512)
    (P a : V) (p : ℕ) (hp : p < 2 ^ 31) (hinst : inst.PACKED_P = .ok P)
    (hP : ∀ i < 16, ln P i = p) (ha : ∀ i < 16, ln a i < p) :
    ∃ r, x86_64_avx512.packing.neg inst a = .ok r ∧ ∀ i < 16, ln r i = (p - ln a i) % p := by
  obtain ⟨nz, hnz, hnzl⟩ := test_epi32_mask a a
  obtain ⟨r, hr, hrl⟩ := maskz_sub_epi32 nz P a
  refine ⟨r, ?_, fun i hi => ?_⟩
  · unfold x86_64_avx512.packing.neg
    rw [hnz, bind_ok, hinst, bind_ok, hr]
  · have hai := ha i hi
    rw [hrl i hi, hP i hi]
    have hbit := hnzl i hi
    rw [Nat.and_self] at hbit
    split
    · rename_i h
      have h0 : ln a i ≠ 0 := hbit.mp h
      rw [Nat.mod_eq_of_lt (by omega : p - ln a i < p)]
      omega
    · rename_i h
      have h0 : ln a i = 0 := by by_contra h0; exact h (hbit.mpr h0)
      rw [h0, Nat.sub_zero, Nat.mod_self]

/-! ## `halve_avx512` -/

theorem halve_one : ∃ r, p3_monty_31_avx512.x86_64_avx512.utils.halve_avx512.ONE = .ok r ∧
    ∀ i < 16, ln r i = 1 := by
  obtain ⟨d, hd, hdx⟩ := array_repeat_eq 16#usize core.U32.Insts.CoreCloneClone (fun _ => rfl)
    1#u32
  refine ⟨d, ?_, fun i hi => ?_⟩
  · unfold p3_monty_31_avx512.x86_64_avx512.utils.halve_avx512.ONE
    rw [hd, bind_ok]; rfl
  · have hi' : i < d.val.length := by rw [V.len]; exact hi
    simp only [ln, List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hi', Option.getD_some]
    rw [hdx _ (List.getElem_mem hi')]; rfl

open p3_monty_31_avx512 in
/-- `halve_avx512(input)`, for an odd `PRIME = p` with `p + 1 < 2^31` and `input` canonical, is
in every lane the canonical `r` with `2r ≡ input (mod p)`: `input / 2`, plus `(p + 1) / 2` in the
lanes where `input` is odd (`vptestmd` against `1`, then a masked `vpaddd`).

`p + 1 < 2^31` is needed, as for AVX2: the code computes `(PRIME as i32 + 1) / 2`, which
overflows `i32` at `p = 2^31 - 1`. -/
theorem halve_avx512 {MP : Type} (inst : data_traits.MontyParameters MP) (pp : Std.U32)
    (hprime : inst.PRIME = .ok pp) (hodd : pp.val % 2 = 1) (hp1 : pp.val + 1 < 2 ^ 31)
    (a : V) (ha : ∀ i < 16, ln a i < pp.val) :
    ∃ r, x86_64_avx512.utils.halve_avx512 inst a = .ok r ∧
      ∀ i < 16, ln r i < pp.val ∧ ln r i * 2 % pp.val = ln a i := by
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
  have hhalf : ∀ i < 16, ln half i = (pp.val + 1) / 2 := by
    intro i hi
    rw [hhl i hi]
    have := hcast_i32_u32_val i3 (by rw [hi3val]; omega)
    rw [hi3val] at this; exact_mod_cast this
  obtain ⟨one, hone, honel⟩ := halve_one
  obtain ⟨lb, hlb, hlbl⟩ := test_epi32_mask a one
  have hlb2 : ∀ i < 16, (mbit lb.val i ↔ ln a i % 2 = 1) := by
    intro i hi; rw [hlbl i hi, honel i hi, Nat.and_one_is_mod]; omega
  obtain ⟨t, ht, htl⟩ := srli_epi32_one a
  obtain ⟨r, hr, hrl⟩ := mask_add_epi32 t lb t half
  refine ⟨r, ?_, fun i hi => ?_⟩
  · unfold x86_64_avx512.utils.halve_avx512
    rw [hprime, bind_ok, lift_eq, bind_ok, hi2, bind_ok, hi3, bind_ok, hh, bind_ok, hone, bind_ok,
      hlb, bind_ok, ht, bind_ok, hr]
  · have hai := ha i hi
    rw [hrl i hi, htl i hi, hhalf i hi]
    by_cases h2 : ln a i % 2 = 1
    · simp only [(hlb2 i hi).mpr h2, ↓reduceIte]
      rw [Nat.mod_eq_of_lt (by omega : ln a i / 2 + (pp.val + 1) / 2 < 2 ^ 32)]
      refine ⟨by omega, ?_⟩
      rw [show (ln a i / 2 + (pp.val + 1) / 2) * 2 = ln a i + pp.val by omega, Nat.add_mod_right,
        Nat.mod_eq_of_lt hai]
    · simp only [show ¬ mbit lb.val i from fun h => h2 ((hlb2 i hi).mp h), ↓reduceIte]
      refine ⟨by omega, ?_⟩
      rw [show ln a i / 2 * 2 = ln a i by omega, Nat.mod_eq_of_lt hai]

/-! ## `mul` -/

/-- The masked correction `mul` applies to `Avx2.montyHi`: add `p` (mod `2^32`) where the high
half of `X` is below that of `t · p`. It is the canonical `r` with `r · 2^32 ≡ X (mod p)`, for
`X < p^2`: the same value as AVX2's `min(h, h + p)`. -/
theorem montyHi_select (p mu X : ℕ) (hp : p < 2 ^ 31) (hp0 : 0 < p) (hinv : p * mu % 2 ^ 32 = 1)
    (hX : X < p * p) :
    let h := Avx2.montyHi p mu X
    let r := if X / 2 ^ 32 < (X % 2 ^ 32 * mu % 2 ^ 32) * p / 2 ^ 32 then (h + p) % 2 ^ 32 else h
    r < p ∧ r * 2 ^ 32 % p = X % p := by
  intro h r
  have key := Avx2.montyHi_red p mu X hp hp0 hinv hX
  set T := X % 2 ^ 32 * mu % 2 ^ 32 with hT
  have hTlt : T < 2 ^ 32 := Nat.mod_lt _ (by norm_num)
  have hXp : X < 2 ^ 32 * p :=
    lt_of_lt_of_le hX (Nat.mul_le_mul_right _ (by omega))
  have hTp : T * p < 2 ^ 32 * p := Nat.mul_lt_mul_of_pos_right hTlt hp0
  have hxh : X / 2 ^ 32 < p := by
    rw [Nat.div_lt_iff_lt_mul (by norm_num)]; exact lt_of_lt_of_eq hXp (Nat.mul_comm _ _)
  have hth : T * p / 2 ^ 32 < p := by
    rw [Nat.div_lt_iff_lt_mul (by norm_num)]; exact lt_of_lt_of_eq hTp (Nat.mul_comm _ _)
  have hh : h = (X / 2 ^ 32 + (2 ^ 32 - T * p / 2 ^ 32)) % 2 ^ 32 := rfl
  have hr : r = min h ((h + p) % 2 ^ 32) := by
    show (if X / 2 ^ 32 < T * p / 2 ^ 32 then (h + p) % 2 ^ 32 else h) = _
    split
    · rename_i hc
      rw [Nat.min_eq_right]
      rw [hh]; omega
    · rename_i hc
      rw [Nat.min_eq_left]
      rw [hh]; omega
  rw [hr]
  exact key

open p3_monty_31_avx512 in
theorem movehdup_epi32 (x : V) : ∃ r, x86_64_avx512.packing.movehdup_epi32 x = .ok r ∧
    ∀ i < 16, ln r i = ln x (2 * (i / 2) + 1) := by
  obtain ⟨r, hr, hrl⟩ := movehdup_ps x
  refine ⟨r, ?_, hrl⟩
  unfold x86_64_avx512.packing.movehdup_epi32
  rw [castsi512_ps, bind_ok, hr, bind_ok, castps_si512]

open p3_monty_31_avx512 in
/-- `mask_movehdup_epi32(src, k, a)`, the stand-in for the masked `vmovshdup` `asm!` block:
lane `i` is `a`'s odd lane `2 (i / 2) + 1` where bit `i` of `k` is set, and `src`'s lane `i`
elsewhere. -/
theorem mask_movehdup_epi32 (src : V) (k : Std.U16) (a : V) :
    ∃ r, x86_64_avx512.packing.mask_movehdup_epi32 src k a = .ok r ∧
      ∀ i < 16, ln r i = if mbit k.val i then ln a (2 * (i / 2) + 1) else ln src i := by
  obtain ⟨r, hr, hrl⟩ := mask_movehdup_ps src k a
  refine ⟨r, ?_, hrl⟩
  unfold x86_64_avx512.packing.mask_movehdup_epi32
  rw [castsi512_ps, bind_ok, castsi512_ps, bind_ok, hr, bind_ok, castps_si512]

open p3_monty_31_avx512 in
theorem confuse_compiler (x : V) : x86_64_avx512.packing.confuse_compiler x = .ok x := rfl

open p3_monty_31_avx512 in
/-- `EVENS = 0b0101010101010101`: bit `i` is set exactly for the even lanes. -/
theorem evens_bit {i : ℕ} (hi : i < 16) :
    mbit x86_64_avx512.packing.EVENS.val i ↔ i % 2 = 0 := by
  have hE : x86_64_avx512.packing.EVENS = 21845#u16 := by
    unfold x86_64_avx512.packing.EVENS; rfl
  rw [hE]
  unfold mbit
  interval_cases i <;> decide

/-- The high halves of the sixteen products, gathered by `mask_movehdup_epi32(odd, EVENS, evn)`
from the even products in `evn` and the odd ones in `odd`. -/
theorem gather_hi (evn odd : V) (f : ℕ → ℕ)
    (hevn : ∀ j < 8, ln evn (2 * j + 1) = f (2 * j))
    (hodd : ∀ j < 8, ln odd (2 * j + 1) = f (2 * j + 1)) (r : V)
    (hr : ∀ i < 16, ln r i = if mbit p3_monty_31_avx512.x86_64_avx512.packing.EVENS.val i then
      ln evn (2 * (i / 2) + 1) else ln odd i) :
    ∀ i < 16, ln r i = f i := by
  intro i hi
  rw [hr i hi]
  split
  · rename_i h
    have he := (evens_bit hi).mp h
    rw [hevn (i / 2) (by omega), show 2 * (i / 2) = i by omega]
  · rename_i h
    have ho : i % 2 = 1 := by
      by_contra h'; exact h ((evens_bit hi).mpr (by omega))
    rw [show i = 2 * (i / 2) + 1 by omega, hodd (i / 2) (by omega)]

open p3_monty_31_avx512 in
/-- `mul(a, b)`, with `PACKED_P` and `PACKED_MU` holding `p` and `mu` in every lane and `a`, `b`
canonical, is in every lane the canonical `r` with `r · 2^32 ≡ a · b (mod p)`: the Montgomery
product. -/
theorem mul {MPAVX512 : Type} (inst : x86_64_avx512.packing.MontyParametersAVX512 MPAVX512)
    (P M a b : V) (p mu : ℕ) (hp : p < 2 ^ 31) (hp0 : 0 < p) (hinv : p * mu % 2 ^ 32 = 1)
    (hPP : inst.PACKED_P = .ok P) (hP : ∀ i < 16, ln P i = p)
    (hMM : inst.PACKED_MU = .ok M) (hM : ∀ i < 16, ln M i = mu)
    (ha : ∀ i < 16, ln a i < p) (hb : ∀ i < 16, ln b i < p) :
    ∃ r, x86_64_avx512.packing.mul inst a b = .ok r ∧
      ∀ i < 16, ln r i < p ∧ ln r i * 2 ^ 32 % p = ln a i * ln b i % p := by
  -- The 64-bit products of lanes `i`, their Montgomery quotients, and their high halves.
  let X : ℕ → ℕ := fun i => ln a i * ln b i
  let T : ℕ → ℕ := fun i => X i % 2 ^ 32 * mu % 2 ^ 32
  have hXlt : ∀ i, X i < 2 ^ 64 := fun i => by
    calc X i < 2 ^ 32 * 2 ^ 32 := Nat.mul_lt_mul'' (u32_lt _) (u32_lt _)
      _ = 2 ^ 64 := by norm_num
  obtain ⟨ao, hao, haol⟩ := movehdup_epi32 a
  obtain ⟨bo, hbo, hbol⟩ := movehdup_epi32 b
  obtain ⟨pe, hpe, hpel⟩ := mul_epu32 a b
  obtain ⟨po, hpo, hpol⟩ := mul_epu32 ao bo
  obtain ⟨qe, hqe, hqel⟩ := mul_epu32 pe M
  obtain ⟨qo, hqo, hqol⟩ := mul_epu32 po M
  obtain ⟨ph, hph, hphl⟩ := mask_movehdup_epi32 po x86_64_avx512.packing.EVENS pe
  obtain ⟨qpe, hqpe, hqpel⟩ := mul_epu32 qe P
  obtain ⟨qpo, hqpo, hqpol⟩ := mul_epu32 qo P
  obtain ⟨qph, hqph, hqphl⟩ := mask_movehdup_epi32 qpo x86_64_avx512.packing.EVENS qpe
  obtain ⟨uf, huf, hufl⟩ := cmplt_epu32_mask ph qph
  obtain ⟨t, ht, htl⟩ := sub_epi32 ph qph
  obtain ⟨r, hr, hrl⟩ := mask_add_epi32 t uf t P
  -- Lane `i` of the products' high halves, and of `T i · p`'s.
  have hodd_a : ∀ j < 8, ln ao (2 * j) = ln a (2 * j + 1) := fun j hj => by
    rw [haol _ (by omega), show 2 * (2 * j / 2) + 1 = 2 * j + 1 by omega]
  have hodd_b : ∀ j < 8, ln bo (2 * j) = ln b (2 * j + 1) := fun j hj => by
    rw [hbol _ (by omega), show 2 * (2 * j / 2) + 1 = 2 * j + 1 by omega]
  have hphv : ∀ i < 16, ln ph i = X i / 2 ^ 32 :=
    gather_hi pe po (fun i => X i / 2 ^ 32) (fun j hj => (hpel j hj).2)
      (fun j hj => by rw [(hpol j hj).2, hodd_a j hj, hodd_b j hj]) ph hphl
  have hqe2 : ∀ j < 8, ln qe (2 * j) = T (2 * j) := fun j hj => by
    rw [(hqel j hj).1, (hpel j hj).1, hM _ (by omega)]
  have hqo2 : ∀ j < 8, ln qo (2 * j) = T (2 * j + 1) := fun j hj => by
    rw [(hqol j hj).1, (hpol j hj).1, hodd_a j hj, hodd_b j hj, hM _ (by omega)]
  have hqphv : ∀ i < 16, ln qph i = T i * p / 2 ^ 32 :=
    gather_hi qpe qpo (fun i => T i * p / 2 ^ 32)
      (fun j hj => by rw [(hqpel j hj).2, hqe2 j hj, hP _ (by omega)])
      (fun j hj => by rw [(hqpol j hj).2, hqo2 j hj, hP _ (by omega)]) qph hqphl
  refine ⟨r, ?_, fun i hi => ?_⟩
  · unfold x86_64_avx512.packing.mul
    rw [hao, bind_ok, hbo, bind_ok, hpe, bind_ok, hpo, bind_ok, hMM, bind_ok, hqe, bind_ok,
      confuse_compiler, bind_ok, hqo, bind_ok, confuse_compiler, bind_ok, hph, bind_ok, hPP,
      bind_ok, hqpe, bind_ok, hqpo, bind_ok, hqph, bind_ok, huf, bind_ok, ht, bind_ok, hr]
  · have hsel := montyHi_select p mu (X i) hp hp0 hinv (Nat.mul_lt_mul'' (ha i hi) (hb i hi))
    have hti : ln t i = Avx2.montyHi p mu (X i) := by
      rw [htl i hi, hphv i hi, hqphv i hi]; rfl
    rw [hrl i hi, hti, hP i hi]
    simp only [hufl i hi, hphv i hi, hqphv i hi]
    exact hsel

end Plonky3Lean.Proofs.Avx512
