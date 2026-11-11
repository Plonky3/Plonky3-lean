module

public import Plonky3Lean.Proofs.Field.Avx2.Packing
public import Plonky3Lean.Proofs.Field.Monty31.Arith
public import Plonky3Lean.Lib.Slice
public import Mathlib.Tactic.LinearCombination

@[expose] public section

/-!
# AVX2: the dot-product kernels of `PackedMontyField31AVX2`, lane by lane

p3-monty-31's AVX2 dot products `dot_product_2` and `dot_product_4` to `dot_product_8`
(`x86_64_avx2/packing.rs`), which `PackedField::dot_product` dispatches to. Each sums the
64-bit products of its inputs' lanes and does one Montgomery reduction, relying on the
sum's bound: `dot_product_2` reduces a sum below `2 p^2`, `dot_product_4` one below
`4 p^2 < 2 · 2^32 p` (`monty_red_wide_to_canonical`), and the longer ones split their terms
into a group of four and a group of one to four, fold a group below `2^32 p` when its sum
can exceed it (`fold_wide`), and add the groups before reducing.

For any `p < 2^31` with `mu = p^(-1) mod 2^32` (`Prm`), and inputs whose lanes are below
`p`, each never fails and lane `i` of its result is the canonical `r` with
`r · 2^32 ≡ Σ_k lhs[k]_i · rhs[k]_i (mod p)` (`dot2` to `dot8`). The inputs are any
`IntoM256` values whose `as_m256i` and `as_shifted_m256i` put their elements in the low
lane of each 64-bit pair (`IntoSpec`). Nothing here depends on the prime beyond `p < 2^31`.

`monty_dot` reads such an `r` in `ZMod p`: it stands for the sum of the products of what
the inputs stand for.

The 64-bit intrinsics' models are read as four 64-bit elements, `w v j`, lanes `2j` and
`2j + 1`.
-/

open Aeneas Aeneas.Std CoreModels
open Plonky3Lean.Lib Plonky3Lean.Spec.Packed

namespace Plonky3Lean.Proofs.Avx2
open shims

/-- 64-bit element `j` of a vector: lanes `2j` (low) and `2j + 1` (high). -/
def w (v : V) (j : ℕ) : ℕ := ln v (2 * j) + 2 ^ 32 * ln v (2 * j + 1)

theorem w_lt (v : V) (j : ℕ) : w v j < 2 ^ 64 := by
  have h1 : ln v (2 * j) < 2 ^ 32 := u32_lt _
  have h2 : ln v (2 * j + 1) < 2 ^ 32 := u32_lt _
  unfold w; omega

/-- Two 32-bit halves or-ed into a 64-bit value. -/
theorem or_shift (x y : BitVec 32) :
    (x.setWidth 64 ||| (y.setWidth 64 <<< 32)).toNat = y.toNat * 2 ^ 32 + x.toNat := by
  have hx := x.isLt
  have hy := y.isLt
  rw [BitVec.toNat_or, BitVec.toNat_shiftLeft, BitVec.toNat_setWidth, BitVec.toNat_setWidth,
    Nat.mod_eq_of_lt (show x.toNat < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show y.toNat < 2 ^ 64 by omega),
    Nat.shiftLeft_eq, Nat.mod_eq_of_lt (show y.toNat * 2 ^ 32 < 2 ^ 64 by omega), Nat.lor_comm,
    ← Nat.shiftLeft_eq, ← Nat.shiftLeft_add_eq_or_of_lt hx, Nat.shiftLeft_eq]

theorem lane64_eq (a : V) {k : ℕ} (hk : k < 4) :
    p3_arch_shims.x86_64.avx2.lane64 a (usz k) = .ok ⟨BitVec.ofNat 64 (w a k)⟩ := by
  unfold p3_arch_shims.x86_64.avx2.lane64
  rw [two_mul_usz hk, bind_ok, index_usz _ (show 2 * k < 8 by omega), bind_ok, lift_eq, bind_ok,
    usz_two_succ hk, bind_ok, index_usz _ (show 2 * k + 1 < 8 by omega), bind_ok, lift_eq,
    bind_ok, shiftLeft_i32_eq _ 32#i32 (by decide) (by decide), bind_ok]
  congr 1
  apply UScalar.eq_of_val_eq
  show (_ ||| _ : BitVec 64).toNat = (BitVec.ofNat 64 (w a k)).toNat
  have hc : ∀ x : Std.U32, (UScalar.cast .U64 x).bv = x.bv.setWidth 64 := fun x => rfl
  have hs : I32.toNat 32#i32 = 32 := by decide
  simp only [hc, hs]
  rw [or_shift, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (w_lt a k)]
  simp only [w, ln, UScalar.val]
  ring


theorem wrapping_add_u64_eq (x y : Std.U64) :
    CoreModels.core.num.U64.wrapping_add x y = .ok ⟨x.bv + y.bv⟩ := rfl

theorem wrapping_sub_u64_eq (x y : Std.U64) :
    CoreModels.core.num.U64.wrapping_sub x y = .ok ⟨x.bv - y.bv⟩ := rfl

/-- A left shift of a `u64` by a `u32` below the width. -/
theorem shl_u64_eq (x : Std.U64) (s : Std.U32) (h : s.val < 64) :
    (x <<< s : RustM Std.U64) = .ok ⟨x.bv <<< s.val⟩ := by
  show UScalar.shiftLeft_UScalar x s = _
  simp only [UScalar.shiftLeft_UScalar, UScalar.shiftLeft, UScalarTy.U64_numBits_eq, h, ite_true]
  rfl

theorem imm8_32 : p3_arch_shims.x86_64.avx2.imm8 32#i32 = .ok 32#u32 := by
  simp only [p3_arch_shims.x86_64.avx2.imm8, lift_eq, bind_ok]; congr 1

/-- The lanes a pair loop writes for a `u64` value `v`, read back as one 64-bit element. -/
theorem w_of_split (r : V) (j : ℕ) (v : Std.U64)
    (hlo : r.val[2 * j]! = UScalar.cast .U32 v)
    (hhi : r.val[2 * j + 1]! = UScalar.cast .U32 (⟨v.bv.ushiftRight 32⟩ : Std.U64)) :
    w r j = v.val := by
  have hPs : (⟨v.bv.ushiftRight 32⟩ : Std.U64).val = v.val / 2 ^ 32 := by
    show (v.bv.ushiftRight 32).toNat = v.bv.toNat / 2 ^ 32
    rw [BitVec.ushiftRight_eq, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  have hv := u64_lt v
  unfold w ln
  rw [hlo, hhi, cast_u64_u32_val, cast_u64_u32_val, hPs]
  rw [Nat.mod_eq_of_lt (show v.val / 2 ^ 32 < 2 ^ 32 by omega)]
  omega

theorem ofNat_val (n : ℕ) : (⟨BitVec.ofNat 64 n⟩ : Std.U64).val = n % 2 ^ 64 :=
  BitVec.toNat_ofNat _ _

/-- `_mm256_add_epi64`: 64-bit element `j` is the sum of those of `a` and `b`, mod `2^64`. -/
theorem add_epi64 (a b : V) : ∃ r, p3_arch_shims.x86_64.avx2._mm256_add_epi64 a b = .ok r ∧
    ∀ j < 4, w r j = (w a j + w b j) % 2 ^ 64 := by
  obtain ⟨d, hd⟩ := zeros
  let P : ℕ → Std.U64 := fun k => ⟨BitVec.ofNat 64 (w a k) + BitVec.ofNat 64 (w b k)⟩
  obtain ⟨r, hr, hl⟩ := pair_loop (fun (s : V × V × V × Std.Usize) =>
      p3_arch_shims.x86_64.avx2._mm256_add_epi64_loop.body s.1 s.2.1 s.2.2.1 s.2.2.2)
    (fun e j => (a, b, e, j)) (fun k => UScalar.cast .U32 (P k))
    (fun k => UScalar.cast .U32 (⟨(P k).bv.ushiftRight 32⟩ : Std.U64)) d
    (fun e k hk => by
      simp only [p3_arch_shims.x86_64.avx2._mm256_add_epi64_loop.body, usz_lt4 hk, ite_true,
        lane64_eq _ hk, bind_ok, wrapping_add_u64_eq, split64_eq, two_mul_usz hk,
        update_usz _ (show 2 * k < 8 by omega), usz_two_succ hk,
        update_usz _ (show 2 * k + 1 < 8 by omega), usz_succ4 hk]
      rfl)
    (fun e => by simp only [p3_arch_shims.x86_64.avx2._mm256_add_epi64_loop.body, usz_not_lt4,
      ite_false])
  refine ⟨r, ?_, fun j hj => ?_⟩
  · unfold p3_arch_shims.x86_64.avx2._mm256_add_epi64 p3_arch_shims.x86_64.avx2._mm256_add_epi64_loop
    rw [hd, bind_ok, hr, bind_ok]
  · obtain ⟨h1, h2⟩ := hl j hj
    rw [w_of_split r j (P j) h1 h2]
    show (BitVec.ofNat 64 (w a j) + BitVec.ofNat 64 (w b j)).toNat = _
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (w_lt a j),
      Nat.mod_eq_of_lt (w_lt b j)]

/-- `_mm256_sub_epi64`: 64-bit element `j` is the difference of those of `a` and `b`, mod
`2^64`. -/
theorem sub_epi64 (a b : V) : ∃ r, p3_arch_shims.x86_64.avx2._mm256_sub_epi64 a b = .ok r ∧
    ∀ j < 4, w r j = (w a j + (2 ^ 64 - w b j)) % 2 ^ 64 := by
  obtain ⟨d, hd⟩ := zeros
  let P : ℕ → Std.U64 := fun k => ⟨BitVec.ofNat 64 (w a k) - BitVec.ofNat 64 (w b k)⟩
  obtain ⟨r, hr, hl⟩ := pair_loop (fun (s : V × V × V × Std.Usize) =>
      p3_arch_shims.x86_64.avx2._mm256_sub_epi64_loop.body s.1 s.2.1 s.2.2.1 s.2.2.2)
    (fun e j => (a, b, e, j)) (fun k => UScalar.cast .U32 (P k))
    (fun k => UScalar.cast .U32 (⟨(P k).bv.ushiftRight 32⟩ : Std.U64)) d
    (fun e k hk => by
      simp only [p3_arch_shims.x86_64.avx2._mm256_sub_epi64_loop.body, usz_lt4 hk, ite_true,
        lane64_eq _ hk, bind_ok, wrapping_sub_u64_eq, split64_eq, two_mul_usz hk,
        update_usz _ (show 2 * k < 8 by omega), usz_two_succ hk,
        update_usz _ (show 2 * k + 1 < 8 by omega), usz_succ4 hk]
      rfl)
    (fun e => by simp only [p3_arch_shims.x86_64.avx2._mm256_sub_epi64_loop.body, usz_not_lt4,
      ite_false])
  refine ⟨r, ?_, fun j hj => ?_⟩
  · unfold p3_arch_shims.x86_64.avx2._mm256_sub_epi64 p3_arch_shims.x86_64.avx2._mm256_sub_epi64_loop
    rw [hd, bind_ok, hr, bind_ok]
  · obtain ⟨h1, h2⟩ := hl j hj
    rw [w_of_split r j (P j) h1 h2]
    show (BitVec.ofNat 64 (w a j) - BitVec.ofNat 64 (w b j)).toNat = _
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (w_lt a j),
      Nat.mod_eq_of_lt (w_lt b j)]
    omega

/-- `_mm256_slli_epi64::<32>`: 64-bit element `j` is the low lane of element `j` of `a`, moved
to the high half. -/
theorem slli_epi64_32 (a : V) : ∃ r, p3_arch_shims.x86_64.avx2._mm256_slli_epi64 32#i32 a = .ok r ∧
    ∀ j < 4, w r j = 2 ^ 32 * ln a (2 * j) := by
  obtain ⟨d, hd⟩ := zeros
  let P : ℕ → Std.U64 := fun k => ⟨BitVec.ofNat 64 (w a k) <<< (32#u32 : Std.U32).val⟩
  obtain ⟨r, hr, hl⟩ := pair_loop (fun (s : V × V × Std.Usize) =>
      p3_arch_shims.x86_64.avx2._mm256_slli_epi64_loop.body 32#u32 s.1 s.2.1 s.2.2)
    (fun e j => (a, e, j)) (fun k => UScalar.cast .U32 (P k))
    (fun k => UScalar.cast .U32 (⟨(P k).bv.ushiftRight 32⟩ : Std.U64)) d
    (fun e k hk => by
      have hgt : ¬ (32#u32 > 63#u32) := by decide
      simp only [p3_arch_shims.x86_64.avx2._mm256_slli_epi64_loop.body, usz_lt4 hk, ite_true,
        hgt, ite_false, lane64_eq _ hk, bind_ok, shl_u64_eq _ 32#u32 (by decide), split64_eq,
        two_mul_usz hk, update_usz _ (show 2 * k < 8 by omega), usz_two_succ hk,
        update_usz _ (show 2 * k + 1 < 8 by omega), usz_succ4 hk]
      rfl)
    (fun e => by simp only [p3_arch_shims.x86_64.avx2._mm256_slli_epi64_loop.body, usz_not_lt4,
      ite_false])
  refine ⟨r, ?_, fun j hj => ?_⟩
  · unfold p3_arch_shims.x86_64.avx2._mm256_slli_epi64
      p3_arch_shims.x86_64.avx2._mm256_slli_epi64_loop
    rw [imm8_32, bind_ok, hd, bind_ok, hr, bind_ok]
  · obtain ⟨h1, h2⟩ := hl j hj
    rw [w_of_split r j (P j) h1 h2]
    show (BitVec.ofNat 64 (w a j) <<< (32#u32 : Std.U32).val).toNat = _
    have h32 : (32#u32 : Std.U32).val = 32 := rfl
    have ha : ln a (2 * j) < 2 ^ 32 := u32_lt _
    rw [h32, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (w_lt a j),
      Nat.shiftLeft_eq]
    unfold w
    have : (ln a (2 * j) + 2 ^ 32 * ln a (2 * j + 1)) * 2 ^ 32 =
        2 ^ 32 * ln a (2 * j) + 2 ^ 64 * ln a (2 * j + 1) := by ring
    rw [this, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]


theorem ln_lo (v : V) (j : ℕ) : ln v (2 * j) = w v j % 2 ^ 32 := by
  have h1 : ln v (2 * j) < 2 ^ 32 := u32_lt _
  unfold w; omega

theorem ln_hi (v : V) (j : ℕ) : ln v (2 * j + 1) = w v j / 2 ^ 32 := by
  have h1 : ln v (2 * j) < 2 ^ 32 := u32_lt _
  unfold w; omega

open p3_monty_31_avx2 in
/-- `fold_wide(acc)`, for 64-bit elements below `2 · 2^32 p`: each is reduced below `2^32 p`
by subtracting `2^32 p` or nothing, so it keeps its low half and its residue mod `p`. -/
theorem fold_wide {MPAVX2 : Type} (inst : x86_64_avx2.packing.MontyParametersAVX2 MPAVX2)
    (P acc : V) (p : ℕ) (hp : p < 2 ^ 31) (hPP : inst.PACKED_P = .ok P) (hP : ∀ i < 8, ln P i = p)
    (hacc : ∀ j < 4, w acc j < 2 * 2 ^ 32 * p) :
    ∃ r, x86_64_avx2.packing.fold_wide inst acc = .ok r ∧ ∀ j < 4,
      w r j < 2 ^ 32 * p ∧ w r j % p = w acc j % p ∧ w r j % 2 ^ 32 = w acc j % 2 ^ 32 := by
  obtain ⟨sp, hsp, hspl⟩ := slli_epi64_32 P
  obtain ⟨sb, hsb, hsbl⟩ := sub_epi64 acc sp
  obtain ⟨r, hr, hrl⟩ := min_epu32 acc sb
  refine ⟨r, ?_, fun j hj => ?_⟩
  · unfold x86_64_avx2.packing.fold_wide
    rw [hPP, bind_ok, hsp, bind_ok, hsb, bind_ok, hr]
  · have hA := hacc j hj
    have hS := hsbl j hj
    rw [hspl j hj, hP _ (by omega)] at hS
    have hr0 : w r j = ln r (2 * j) + 2 ^ 32 * ln r (2 * j + 1) := rfl
    rw [hr0, hrl _ (by omega), hrl _ (by omega), ln_lo acc j, ln_hi acc j, ln_lo sb j,
      ln_hi sb j, hS]
    have hwl := w_lt acc j
    by_cases hc : 2 ^ 32 * p ≤ w acc j
    · have e : w acc j = (w acc j - 2 ^ 32 * p) + p * 2 ^ 32 := by omega
      refine ⟨by omega, ?_, by omega⟩
      have h1 : (w acc j + (2 ^ 64 - 2 ^ 32 * p)) % 2 ^ 64 = w acc j - 2 ^ 32 * p := by omega
      have h2 : min (w acc j % 2 ^ 32) ((w acc j - 2 ^ 32 * p) % 2 ^ 32) +
          2 ^ 32 * min (w acc j / 2 ^ 32) ((w acc j - 2 ^ 32 * p) / 2 ^ 32) =
          w acc j - 2 ^ 32 * p := by omega
      rw [h1, h2]
      conv_rhs => rw [e]
      rw [Nat.add_mul_mod_self_left]
    · refine ⟨by omega, ?_, by omega⟩
      have h2 : min (w acc j % 2 ^ 32) ((w acc j + (2 ^ 64 - 2 ^ 32 * p)) % 2 ^ 64 % 2 ^ 32) +
          2 ^ 32 * min (w acc j / 2 ^ 32) ((w acc j + (2 ^ 64 - 2 ^ 32 * p)) % 2 ^ 64 / 2 ^ 32) =
          w acc j := by omega
      rw [h2]

open p3_monty_31_avx2 in
/-- `blend_evn_odd(evn, odd)`: lane `i` is the high half of 64-bit element `i / 2` of `evn`
for even `i`, of `odd` for odd `i`. -/
theorem blend_evn_odd (evn odd : V) : ∃ r, x86_64_avx2.packing.blend_evn_odd evn odd = .ok r ∧
    ∀ i < 8, ln r i = (if i % 2 = 0 then w evn (i / 2) else w odd (i / 2)) / 2 ^ 32 := by
  obtain ⟨eh, heh, hehl⟩ := movehdup_epi32 evn
  obtain ⟨r, hr, hrl⟩ := blend_epi32_170 eh odd
  refine ⟨r, ?_, fun i hi => ?_⟩
  · unfold x86_64_avx2.packing.blend_evn_odd
    rw [heh, bind_ok, hr]
  · rw [hrl i hi]
    split
    · rename_i hodd
      have h0 : ¬ i % 2 = 0 := by omega
      simp only [h0, ite_false]
      rw [← ln_hi, show 2 * (i / 2) + 1 = i by omega]
    · have h0 : i % 2 = 0 := by omega
      simp only [h0, ite_true]
      rw [hehl i hi, ln_hi]

/-- `montyHi_red` for any `X < 2^32 p`, not only `X < p^2`: the Montgomery reduction of a
wide accumulator whose high half is already below `p`. -/
theorem montyHi_red_wide (p mu X : ℕ) (hp : p < 2 ^ 31) (hp0 : 0 < p)
    (hinv : p * mu % 2 ^ 32 = 1) (hXp : X < 2 ^ 32 * p) :
    let h := montyHi p mu X
    min h ((h + p) % 2 ^ 32) < p ∧ min h ((h + p) % 2 ^ 32) * 2 ^ 32 % p = X % p := by
  intro h
  set T := X % 2 ^ 32 * mu % 2 ^ 32 with hT
  have hTlt : T < 2 ^ 32 := Nat.mod_lt _ (by norm_num)
  have hcong : T * p % 2 ^ 32 = X % 2 ^ 32 := by
    rw [hT, Nat.mod_mul_mod, Nat.mul_assoc, Nat.mul_mod, Nat.mul_comm mu, hinv, Nat.mul_one,
      Nat.mod_mod, Nat.mod_mod]
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

/-- The accumulator of field element `i`: 64-bit element `i / 2` of `evn` for even `i`, of
`odd` for odd `i`. -/
def acc (evn odd : V) (i : ℕ) : ℕ := if i % 2 = 0 then w evn (i / 2) else w odd (i / 2)

open p3_monty_31_avx2 in
/-- `monty_red_wide_to_canonical(evn, odd)`, for accumulators below `2 · 2^32 p`: lane `i` is
the canonical `r` with `r · 2^32 ≡ acc i (mod p)`. -/
theorem monty_red_wide {PMP : Type} (inst : data_traits.PackedMontyParameters PMP)
    (P M evn odd : V) (p mu : ℕ) (hp : p < 2 ^ 31) (hp0 : 0 < p) (hinv : p * mu % 2 ^ 32 = 1)
    (hPP : inst.x86_64_avx2packingMontyParametersAVX2Inst.PACKED_P = .ok P)
    (hP : ∀ i < 8, ln P i = p)
    (hMM : inst.x86_64_avx2packingMontyParametersAVX2Inst.PACKED_MU = .ok M)
    (hM : ∀ i < 8, ln M i = mu)
    (he : ∀ j < 4, w evn j < 2 * 2 ^ 32 * p) (ho : ∀ j < 4, w odd j < 2 * 2 ^ 32 * p) :
    ∃ r, x86_64_avx2.packing.monty_red_wide_to_canonical inst evn odd = .ok r ∧
      ∀ i < 8, ln r i < p ∧ ln r i * 2 ^ 32 % p = acc evn odd i % p := by
  obtain ⟨dot, hdot, hdotl⟩ := blend_evn_odd evn odd
  obtain ⟨ds, hds, hdsl⟩ := sub_epi32 dot P
  obtain ⟨dp, hdp, hdpl⟩ := min_epu32 dot ds
  obtain ⟨qe, hqe, hqel⟩ := mul_epu32 evn M
  obtain ⟨qpe, hqpe, hqpel⟩ := mul_epu32 qe P
  obtain ⟨qo, hqo, hqol⟩ := mul_epu32 odd M
  obtain ⟨qpo, hqpo, hqpol⟩ := mul_epu32 qo P
  obtain ⟨qp, hqp, hqpl⟩ := blend_evn_odd qpe qpo
  obtain ⟨t, ht, htl⟩ := sub_epi32 dp qp
  obtain ⟨c, hc, hcl⟩ := add_epi32 t P
  obtain ⟨r, hr, hrl⟩ := min_epu32 t c
  refine ⟨r, ?_, fun i hi => ?_⟩
  · unfold x86_64_avx2.packing.monty_red_wide_to_canonical
      x86_64_avx2.packing.red_signed_to_canonical
    rw [hdot, bind_ok, hPP, bind_ok, hds, bind_ok, hdp, bind_ok, hMM, bind_ok, hqe, bind_ok,
      hqpe, bind_ok, hqo, bind_ok, hqpo, bind_ok, hqp, bind_ok, ht, bind_ok, bind_ok, hc,
      bind_ok, hr]
  · set C := acc evn odd i with hC
    have hCb : C < 2 * 2 ^ 32 * p := by
      rw [hC, acc]; split
      · exact he _ (by omega)
      · exact ho _ (by omega)
    -- the high half, reduced mod p
    have hdpv : ln dp i = C / 2 ^ 32 % p := by
      rw [hdpl i hi, hdsl i hi, hdotl i hi, hP i hi, ← acc, ← hC]
      have : C / 2 ^ 32 < 2 * p := by omega
      by_cases h : p ≤ C / 2 ^ 32
      · have e : C / 2 ^ 32 % p = C / 2 ^ 32 - p := by
          rw [Nat.mod_eq_sub_mod h, Nat.mod_eq_of_lt (by omega)]
        rw [e]; omega
      · have e : C / 2 ^ 32 % p = C / 2 ^ 32 := Nat.mod_eq_of_lt (by omega)
        rw [e]; omega
    -- the quotient's contribution
    have hqpv : ln qp i = (C % 2 ^ 32 * mu % 2 ^ 32) * p / 2 ^ 32 := by
      rw [hqpl i hi]
      split
      · rename_i hev
        rw [← ln_hi, (hqpel _ (by omega)).2, (hqel _ (by omega)).1, hP _ (by omega),
          hM _ (by omega), ln_lo, hC]
        simp only [acc, hev, ite_true]
      · rename_i hev
        rw [← ln_hi, (hqpol _ (by omega)).2, (hqol _ (by omega)).1, hP _ (by omega),
          hM _ (by omega), ln_lo, hC]
        simp only [acc, hev, ite_false]
    set X := C / 2 ^ 32 % p * 2 ^ 32 + C % 2 ^ 32 with hX
    have hXlo : X % 2 ^ 32 = C % 2 ^ 32 := by omega
    have hXhi : X / 2 ^ 32 = C / 2 ^ 32 % p := by omega
    have hXb : X < 2 ^ 32 * p := by
      have : C / 2 ^ 32 % p < p := Nat.mod_lt _ hp0
      have : C / 2 ^ 32 % p * 2 ^ 32 + 2 ^ 32 ≤ p * 2 ^ 32 := by nlinarith
      omega
    have htv : ln t i = montyHi p mu X := by
      rw [htl i hi, hdpv, hqpv, montyHi, hXlo, hXhi]
    have hred := montyHi_red_wide p mu X hp hp0 hinv hXb
    rw [hrl i hi, hcl i hi, hP i hi, htv]
    refine ⟨hred.1, ?_⟩
    rw [hred.2]
    have hd1 := Nat.div_add_mod C (2 ^ 32)
    have hd2 := Nat.div_add_mod (C / 2 ^ 32) p
    have : C = X + p * (C / 2 ^ 32 / p * 2 ^ 32) := by
      rw [hX]
      conv_lhs => rw [← hd1, ← hd2]
      ring
    rw [this, Nat.add_mul_mod_self_left]


/-! ## Products -/

/-- `_mm256_mul_epu32(a, b)` as 64-bit elements: element `j` is the product of lanes `2j`. -/
theorem mul_w (a b : V) : ∃ r, p3_arch_shims.x86_64.avx2._mm256_mul_epu32 a b = .ok r ∧
    ∀ j < 4, w r j = ln a (2 * j) * ln b (2 * j) := by
  obtain ⟨r, hr, hl⟩ := mul_epu32 a b
  refine ⟨r, hr, fun j hj => ?_⟩
  unfold w
  rw [(hl j hj).1, (hl j hj).2]
  omega

theorem index_some {α : Type} {n : Std.Usize} (a : Std.Array α n) (i : Std.Usize) (x : α)
    (h : a.val[i.val]? = some x) : Std.Array.index_usize a i = .ok x := by
  have hl : i.val < a.val.length := by
    by_contra hc; rw [List.getElem?_eq_none (by omega)] at h; cases h
  rw [index_usize_eq _ _ hl]
  rw [List.getElem?_eq_getElem hl] at h
  cases h; rfl

open p3_monty_31_avx2 in
/-- What a dot product needs of an `IntoM256` value `x`: `as_m256i` holds element `2j` of `e`
in lane `2j`, and `as_shifted_m256i` holds element `2j + 1` there. -/
structure IntoSpec {S PMP : Type} (inst : x86_64_avx2.packing.IntoM256 S PMP) (x : S)
    (e : ℕ → ℕ) : Prop where
  vec : ∃ v, inst.as_m256i x = .ok v ∧ ∀ j < 4, ln v (2 * j) = e (2 * j)
  shifted : ∃ v, inst.as_shifted_m256i x = .ok v ∧ ∀ j < 4, ln v (2 * j) = e (2 * j + 1)


/-- The sum of the first `K` products at element `i`. -/
def dsum (el er : ℕ → ℕ → ℕ) (K i : ℕ) : ℕ := ∑ k ∈ Finset.range K, el k i * er k i

theorem prod_lt (a b p : ℕ) (hp : p < 2 ^ 31) (ha : a < p) (hb : b < p) : a * b < 2 ^ 62 := by
  have : a * b < p * p := Nat.mul_lt_mul'' ha hb
  have : p * p ≤ 2 ^ 31 * 2 ^ 31 := Nat.mul_le_mul (by omega) (by omega)
  omega

open p3_monty_31_avx2 in
theorem wide_dot4 {PMP LHS RHS : Type} (inst : data_traits.PackedMontyParameters PMP)
    (iL : x86_64_avx2.packing.IntoM256 LHS PMP) (iR : x86_64_avx2.packing.IntoM256 RHS PMP)
    (lhs : Std.Array LHS 4#usize) (rhs : Std.Array RHS 4#usize) (el er : ℕ → ℕ → ℕ) (p : ℕ)
    (hp : p < 2 ^ 31)
    (hl : ∀ k < 4, ∃ x, lhs.val[k]? = some x ∧ IntoSpec iL x (el k))
    (hr : ∀ k < 4, ∃ y, rhs.val[k]? = some y ∧ IntoSpec iR y (er k))
    (hb : ∀ k < 4, ∀ i < 8, el k i < p ∧ er k i < p) :
    ∃ e o, x86_64_avx2.packing.wide_dot inst iL iR lhs rhs = .ok (e, o) ∧
      ∀ j < 4, w e j = dsum el er 4 (2 * j) ∧ w o j = dsum el er 4 (2 * j + 1) := by
  obtain ⟨x0, hx0, s0⟩ := hl 0 (by norm_num)
  obtain ⟨x1, hx1, s1⟩ := hl 1 (by norm_num)
  obtain ⟨x2, hx2, s2⟩ := hl 2 (by norm_num)
  obtain ⟨x3, hx3, s3⟩ := hl 3 (by norm_num)
  obtain ⟨y0, hy0, t0⟩ := hr 0 (by norm_num)
  obtain ⟨y1, hy1, t1⟩ := hr 1 (by norm_num)
  obtain ⟨y2, hy2, t2⟩ := hr 2 (by norm_num)
  obtain ⟨y3, hy3, t3⟩ := hr 3 (by norm_num)
  obtain ⟨a0, ha0, ha0l⟩ := s0.vec
  obtain ⟨a1, ha1, ha1l⟩ := s1.vec
  obtain ⟨a2, ha2, ha2l⟩ := s2.vec
  obtain ⟨a3, ha3, ha3l⟩ := s3.vec
  obtain ⟨c0, hc0, hc0l⟩ := s0.shifted
  obtain ⟨c1, hc1, hc1l⟩ := s1.shifted
  obtain ⟨c2, hc2, hc2l⟩ := s2.shifted
  obtain ⟨c3, hc3, hc3l⟩ := s3.shifted
  obtain ⟨b0, hb0, hb0l⟩ := t0.vec
  obtain ⟨b1, hb1, hb1l⟩ := t1.vec
  obtain ⟨b2, hb2, hb2l⟩ := t2.vec
  obtain ⟨b3, hb3, hb3l⟩ := t3.vec
  obtain ⟨d0, hd0, hd0l⟩ := t0.shifted
  obtain ⟨d1, hd1, hd1l⟩ := t1.shifted
  obtain ⟨d2, hd2, hd2l⟩ := t2.shifted
  obtain ⟨d3, hd3, hd3l⟩ := t3.shifted
  obtain ⟨e0, he0, he0l⟩ := mul_w a0 b0
  obtain ⟨e1, he1, he1l⟩ := mul_w a1 b1
  obtain ⟨e2, he2, he2l⟩ := mul_w a2 b2
  obtain ⟨e3, he3, he3l⟩ := mul_w a3 b3
  obtain ⟨o0, ho0, ho0l⟩ := mul_w c0 d0
  obtain ⟨o1, ho1, ho1l⟩ := mul_w c1 d1
  obtain ⟨o2, ho2, ho2l⟩ := mul_w c2 d2
  obtain ⟨o3, ho3, ho3l⟩ := mul_w c3 d3
  obtain ⟨e01, he01, he01l⟩ := add_epi64 e0 e1
  obtain ⟨o01, ho01, ho01l⟩ := add_epi64 o0 o1
  obtain ⟨e23, he23, he23l⟩ := add_epi64 e2 e3
  obtain ⟨o23, ho23, ho23l⟩ := add_epi64 o2 o3
  obtain ⟨e, he, hel⟩ := add_epi64 e01 e23
  obtain ⟨o, ho, hol⟩ := add_epi64 o01 o23
  refine ⟨e, o, ?_, fun j hj => ?_⟩
  · unfold x86_64_avx2.packing.wide_dot
    have hm1 : massert (4#usize >= 1#usize) = .ok () := by simp [massert]
    have hm2 : massert (4#usize <= 4#usize) = .ok () := by simp [massert]
    have n1 : ¬ (4#usize = 1#usize) := by decide
    have n2 : ¬ (4#usize = 2#usize) := by decide
    have n3 : ¬ (4#usize = 3#usize) := by decide
    simp only [hm1, hm2, bind_ok, n1, n2, n3, ite_false,
      index_some lhs 0#usize x0 hx0, index_some lhs 1#usize x1 hx1,
      index_some lhs 2#usize x2 hx2, index_some lhs 3#usize x3 hx3,
      index_some rhs 0#usize y0 hy0, index_some rhs 1#usize y1 hy1,
      index_some rhs 2#usize y2 hy2, index_some rhs 3#usize y3 hy3,
      ha0, ha1, ha2, ha3, hb0, hb1, hb2, hb3, hc0, hc1, hc2, hc3, hd0, hd1, hd2, hd3,
      he0, he1, he2, he3, ho0, ho1, ho2, ho3, he01, ho01, he23, ho23, he, ho]
  · have bnd : ∀ k < 4, ∀ i < 8, el k i * er k i < 2 ^ 62 := fun k hk i hi =>
      prod_lt _ _ p hp (hb k hk i hi).1 (hb k hk i hi).2
    have q := fun k hk => bnd k hk (2 * j) (by omega)
    have q' := fun k hk => bnd k hk (2 * j + 1) (by omega)
    have := q 0 (by norm_num); have := q 1 (by norm_num); have := q 2 (by norm_num)
    have := q 3 (by norm_num); have := q' 0 (by norm_num); have := q' 1 (by norm_num)
    have := q' 2 (by norm_num); have := q' 3 (by norm_num)
    simp only [dsum, Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    rw [hel j hj, he01l j hj, he23l j hj, he0l j hj, he1l j hj, he2l j hj, he3l j hj,
      hol j hj, ho01l j hj, ho23l j hj, ho0l j hj, ho1l j hj, ho2l j hj, ho3l j hj,
      ha0l j hj, ha1l j hj, ha2l j hj, ha3l j hj, hb0l j hj, hb1l j hj, hb2l j hj, hb3l j hj,
      hc0l j hj, hc1l j hj, hc2l j hj, hc3l j hj, hd0l j hj, hd1l j hj, hd2l j hj, hd3l j hj]
    omega

open p3_monty_31_avx2 in
theorem wide_dot1 {PMP LHS RHS : Type} (inst : data_traits.PackedMontyParameters PMP)
    (iL : x86_64_avx2.packing.IntoM256 LHS PMP) (iR : x86_64_avx2.packing.IntoM256 RHS PMP)
    (lhs : Std.Array LHS 1#usize) (rhs : Std.Array RHS 1#usize) (el er : ℕ → ℕ → ℕ) (p : ℕ)
    (hp : p < 2 ^ 31)
    (hl : ∀ k < 1, ∃ x, lhs.val[k]? = some x ∧ IntoSpec iL x (el k))
    (hr : ∀ k < 1, ∃ y, rhs.val[k]? = some y ∧ IntoSpec iR y (er k))
    (hb : ∀ k < 1, ∀ i < 8, el k i < p ∧ er k i < p) :
    ∃ e o, x86_64_avx2.packing.wide_dot inst iL iR lhs rhs = .ok (e, o) ∧
      ∀ j < 4, w e j = dsum el er 1 (2 * j) ∧ w o j = dsum el er 1 (2 * j + 1) := by
  obtain ⟨x0, hx0, s0⟩ := hl 0 (by norm_num)
  obtain ⟨y0, hy0, t0⟩ := hr 0 (by norm_num)
  obtain ⟨a0, ha0, ha0l⟩ := s0.vec
  obtain ⟨c0, hc0, hc0l⟩ := s0.shifted
  obtain ⟨b0, hb0, hb0l⟩ := t0.vec
  obtain ⟨d0, hd0, hd0l⟩ := t0.shifted
  obtain ⟨e0, he0, he0l⟩ := mul_w a0 b0
  obtain ⟨o0, ho0, ho0l⟩ := mul_w c0 d0
  refine ⟨e0, o0, ?_, fun j hj => ?_⟩
  · unfold x86_64_avx2.packing.wide_dot
    have hm1 : massert (1#usize >= 1#usize) = .ok () := by simp [massert]
    have hm2 : massert (1#usize <= 4#usize) = .ok () := by simp [massert]
    have n2 : ¬ (1#usize = 2#usize) := by decide
    have n3 : ¬ (1#usize = 3#usize) := by decide
    simp only [hm1, hm2, bind_ok, n2, n3, ite_true, ite_false,
      index_some lhs 0#usize x0 hx0,
      index_some rhs 0#usize y0 hy0,
      ha0, hb0, hc0, hd0, he0, ho0]
  · have bnd : ∀ k < 1, ∀ i < 8, el k i * er k i < 2 ^ 62 := fun k hk i hi =>
      prod_lt _ _ p hp (hb k hk i hi).1 (hb k hk i hi).2
    have := bnd 0 (by norm_num) (2 * j) (by omega)
    have := bnd 0 (by norm_num) (2 * j + 1) (by omega)
    simp only [dsum, Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    rw [he0l j hj, ho0l j hj, ha0l j hj, hb0l j hj, hc0l j hj, hd0l j hj]
    omega

open p3_monty_31_avx2 in
theorem wide_dot2 {PMP LHS RHS : Type} (inst : data_traits.PackedMontyParameters PMP)
    (iL : x86_64_avx2.packing.IntoM256 LHS PMP) (iR : x86_64_avx2.packing.IntoM256 RHS PMP)
    (lhs : Std.Array LHS 2#usize) (rhs : Std.Array RHS 2#usize) (el er : ℕ → ℕ → ℕ) (p : ℕ)
    (hp : p < 2 ^ 31)
    (hl : ∀ k < 2, ∃ x, lhs.val[k]? = some x ∧ IntoSpec iL x (el k))
    (hr : ∀ k < 2, ∃ y, rhs.val[k]? = some y ∧ IntoSpec iR y (er k))
    (hb : ∀ k < 2, ∀ i < 8, el k i < p ∧ er k i < p) :
    ∃ e o, x86_64_avx2.packing.wide_dot inst iL iR lhs rhs = .ok (e, o) ∧
      ∀ j < 4, w e j = dsum el er 2 (2 * j) ∧ w o j = dsum el er 2 (2 * j + 1) := by
  obtain ⟨x0, hx0, s0⟩ := hl 0 (by norm_num)
  obtain ⟨y0, hy0, t0⟩ := hr 0 (by norm_num)
  obtain ⟨a0, ha0, ha0l⟩ := s0.vec
  obtain ⟨c0, hc0, hc0l⟩ := s0.shifted
  obtain ⟨b0, hb0, hb0l⟩ := t0.vec
  obtain ⟨d0, hd0, hd0l⟩ := t0.shifted
  obtain ⟨e0, he0, he0l⟩ := mul_w a0 b0
  obtain ⟨o0, ho0, ho0l⟩ := mul_w c0 d0
  obtain ⟨x1, hx1, s1⟩ := hl 1 (by norm_num)
  obtain ⟨y1, hy1, t1⟩ := hr 1 (by norm_num)
  obtain ⟨a1, ha1, ha1l⟩ := s1.vec
  obtain ⟨c1, hc1, hc1l⟩ := s1.shifted
  obtain ⟨b1, hb1, hb1l⟩ := t1.vec
  obtain ⟨d1, hd1, hd1l⟩ := t1.shifted
  obtain ⟨e1, he1, he1l⟩ := mul_w a1 b1
  obtain ⟨o1, ho1, ho1l⟩ := mul_w c1 d1
  obtain ⟨e01, he01, he01l⟩ := add_epi64 e0 e1
  obtain ⟨o01, ho01, ho01l⟩ := add_epi64 o0 o1
  refine ⟨e01, o01, ?_, fun j hj => ?_⟩
  · unfold x86_64_avx2.packing.wide_dot
    have hm1 : massert (2#usize >= 1#usize) = .ok () := by simp [massert]
    have hm2 : massert (2#usize <= 4#usize) = .ok () := by simp [massert]
    have n1 : ¬ (2#usize = 1#usize) := by decide
    have n3 : ¬ (2#usize = 3#usize) := by decide
    simp only [hm1, hm2, bind_ok, n1, n3, ite_true, ite_false,
      index_some lhs 0#usize x0 hx0,
      index_some rhs 0#usize y0 hy0,
      index_some lhs 1#usize x1 hx1,
      index_some rhs 1#usize y1 hy1,
      ha0, hb0, hc0, hd0, he0, ho0, ha1, hb1, hc1, hd1, he1, ho1, he01, ho01]
  · have bnd : ∀ k < 2, ∀ i < 8, el k i * er k i < 2 ^ 62 := fun k hk i hi =>
      prod_lt _ _ p hp (hb k hk i hi).1 (hb k hk i hi).2
    have := bnd 0 (by norm_num) (2 * j) (by omega)
    have := bnd 0 (by norm_num) (2 * j + 1) (by omega)
    have := bnd 1 (by norm_num) (2 * j) (by omega)
    have := bnd 1 (by norm_num) (2 * j + 1) (by omega)
    simp only [dsum, Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    rw [he01l j hj, ho01l j hj, he0l j hj, ho0l j hj, he1l j hj, ho1l j hj, ha0l j hj, hb0l j hj,
      hc0l j hj, hd0l j hj, ha1l j hj, hb1l j hj, hc1l j hj, hd1l j hj]
    omega

open p3_monty_31_avx2 in
theorem wide_dot3 {PMP LHS RHS : Type} (inst : data_traits.PackedMontyParameters PMP)
    (iL : x86_64_avx2.packing.IntoM256 LHS PMP) (iR : x86_64_avx2.packing.IntoM256 RHS PMP)
    (lhs : Std.Array LHS 3#usize) (rhs : Std.Array RHS 3#usize) (el er : ℕ → ℕ → ℕ) (p : ℕ)
    (hp : p < 2 ^ 31)
    (hl : ∀ k < 3, ∃ x, lhs.val[k]? = some x ∧ IntoSpec iL x (el k))
    (hr : ∀ k < 3, ∃ y, rhs.val[k]? = some y ∧ IntoSpec iR y (er k))
    (hb : ∀ k < 3, ∀ i < 8, el k i < p ∧ er k i < p) :
    ∃ e o, x86_64_avx2.packing.wide_dot inst iL iR lhs rhs = .ok (e, o) ∧
      ∀ j < 4, w e j = dsum el er 3 (2 * j) ∧ w o j = dsum el er 3 (2 * j + 1) := by
  obtain ⟨x0, hx0, s0⟩ := hl 0 (by norm_num)
  obtain ⟨y0, hy0, t0⟩ := hr 0 (by norm_num)
  obtain ⟨a0, ha0, ha0l⟩ := s0.vec
  obtain ⟨c0, hc0, hc0l⟩ := s0.shifted
  obtain ⟨b0, hb0, hb0l⟩ := t0.vec
  obtain ⟨d0, hd0, hd0l⟩ := t0.shifted
  obtain ⟨e0, he0, he0l⟩ := mul_w a0 b0
  obtain ⟨o0, ho0, ho0l⟩ := mul_w c0 d0
  obtain ⟨x1, hx1, s1⟩ := hl 1 (by norm_num)
  obtain ⟨y1, hy1, t1⟩ := hr 1 (by norm_num)
  obtain ⟨a1, ha1, ha1l⟩ := s1.vec
  obtain ⟨c1, hc1, hc1l⟩ := s1.shifted
  obtain ⟨b1, hb1, hb1l⟩ := t1.vec
  obtain ⟨d1, hd1, hd1l⟩ := t1.shifted
  obtain ⟨e1, he1, he1l⟩ := mul_w a1 b1
  obtain ⟨o1, ho1, ho1l⟩ := mul_w c1 d1
  obtain ⟨x2, hx2, s2⟩ := hl 2 (by norm_num)
  obtain ⟨y2, hy2, t2⟩ := hr 2 (by norm_num)
  obtain ⟨a2, ha2, ha2l⟩ := s2.vec
  obtain ⟨c2, hc2, hc2l⟩ := s2.shifted
  obtain ⟨b2, hb2, hb2l⟩ := t2.vec
  obtain ⟨d2, hd2, hd2l⟩ := t2.shifted
  obtain ⟨e2, he2, he2l⟩ := mul_w a2 b2
  obtain ⟨o2, ho2, ho2l⟩ := mul_w c2 d2
  obtain ⟨e01, he01, he01l⟩ := add_epi64 e0 e1
  obtain ⟨o01, ho01, ho01l⟩ := add_epi64 o0 o1
  obtain ⟨e, he, hel⟩ := add_epi64 e01 e2
  obtain ⟨o, ho, hol⟩ := add_epi64 o01 o2
  refine ⟨e, o, ?_, fun j hj => ?_⟩
  · unfold x86_64_avx2.packing.wide_dot
    have hm1 : massert (3#usize >= 1#usize) = .ok () := by simp [massert]
    have hm2 : massert (3#usize <= 4#usize) = .ok () := by simp [massert]
    have n1 : ¬ (3#usize = 1#usize) := by decide
    have n2 : ¬ (3#usize = 2#usize) := by decide
    simp only [hm1, hm2, bind_ok, n1, n2, ite_true, ite_false,
      index_some lhs 0#usize x0 hx0,
      index_some rhs 0#usize y0 hy0,
      index_some lhs 1#usize x1 hx1,
      index_some rhs 1#usize y1 hy1,
      index_some lhs 2#usize x2 hx2,
      index_some rhs 2#usize y2 hy2,
      ha0, hb0, hc0, hd0, he0, ho0, ha1, hb1, hc1, hd1, he1, ho1, ha2, hb2, hc2, hd2, he2, ho2,
        he01, ho01, he, ho]
  · have bnd : ∀ k < 3, ∀ i < 8, el k i * er k i < 2 ^ 62 := fun k hk i hi =>
      prod_lt _ _ p hp (hb k hk i hi).1 (hb k hk i hi).2
    have := bnd 0 (by norm_num) (2 * j) (by omega)
    have := bnd 0 (by norm_num) (2 * j + 1) (by omega)
    have := bnd 1 (by norm_num) (2 * j) (by omega)
    have := bnd 1 (by norm_num) (2 * j + 1) (by omega)
    have := bnd 2 (by norm_num) (2 * j) (by omega)
    have := bnd 2 (by norm_num) (2 * j + 1) (by omega)
    simp only [dsum, Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    rw [hel j hj, hol j hj, he01l j hj, ho01l j hj, he0l j hj, ho0l j hj, he1l j hj, ho1l j hj,
      he2l j hj, ho2l j hj, ha0l j hj, hb0l j hj, hc0l j hj, hd0l j hj, ha1l j hj, hb1l j hj,
      hc1l j hj, hd1l j hj, ha2l j hj, hb2l j hj, hc2l j hj, hd2l j hj]
    omega


/-! ## The dot products -/

open p3_monty_31_avx2 in
/-- The packed parameters, read as numbers: an odd `p < 2^31` (here only `0 < p` is used), `mu`
its inverse mod `2^32`, and `PACKED_P`, `PACKED_MU` holding them in every lane. -/
structure Prm {PMP : Type} (inst : data_traits.PackedMontyParameters PMP) (p mu : ℕ) : Prop where
  lt : p < 2 ^ 31
  pos : 0 < p
  inv : p * mu % 2 ^ 32 = 1
  P : ∃ P, inst.x86_64_avx2packingMontyParametersAVX2Inst.PACKED_P = .ok P ∧ ∀ i < 8, ln P i = p
  M : ∃ M, inst.x86_64_avx2packingMontyParametersAVX2Inst.PACKED_MU = .ok M ∧
    ∀ i < 8, ln M i = mu

theorem dsum_le (el er : ℕ → ℕ → ℕ) (K i p : ℕ) (hb : ∀ k < K, el k i < p ∧ er k i < p) :
    dsum el er K i ≤ K * (p * p) := by
  unfold dsum
  calc ∑ k ∈ Finset.range K, el k i * er k i ≤ ∑ _k ∈ Finset.range K, p * p :=
        Finset.sum_le_sum fun k hk => by
          have := hb k (Finset.mem_range.mp hk)
          exact Nat.mul_le_mul (by omega) (by omega)
    _ = K * (p * p) := by simp

/-- A sum of at most `n` products of canonical values fits the wide reductions' bound
`n · 2^31 · p`: `n p^2 < n · 2^31 · p`. -/
theorem dsum_wide (el er : ℕ → ℕ → ℕ) (K i p n : ℕ) (hp : p < 2 ^ 31) (hp0 : 0 < p)
    (hK : K ≤ n) (hn : 0 < n) (hb : ∀ k < K, el k i < p ∧ er k i < p) :
    dsum el er K i < n * 2 ^ 31 * p := by
  have h1 := dsum_le el er K i p hb
  have h2 : K * (p * p) ≤ n * (p * p) := Nat.mul_le_mul_right _ hK
  have h3 : n * (p * p) < n * 2 ^ 31 * p := by
    rw [Nat.mul_assoc]; exact Nat.mul_lt_mul_of_pos_left (Nat.mul_lt_mul_of_pos_right hp hp0) hn
  omega

theorem dsum_add (el er : ℕ → ℕ → ℕ) (K L i : ℕ) :
    dsum el er (K + L) i = dsum el er K i + dsum (fun k => el (k + K)) (fun k => er (k + K)) L i := by
  unfold dsum
  rw [Finset.sum_range_add]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Nat.add_comm K k]

theorem make4_spec {S PMP : Type} (inst : p3_monty_31_avx2.x86_64_avx2.packing.IntoM256 S PMP)
    (e : ℕ → ℕ → ℕ) (x0 x1 x2 x3 : S) (s0 : IntoSpec inst x0 (e 0)) (s1 : IntoSpec inst x1 (e 1))
    (s2 : IntoSpec inst x2 (e 2)) (s3 : IntoSpec inst x3 (e 3)) (h) :
    ∀ k < 4, ∃ x, (Std.Array.make 4#usize [x0, x1, x2, x3] h).val[k]? = some x ∧
      IntoSpec inst x (e k) := by
  intro k hk
  interval_cases k
  · exact ⟨x0, rfl, s0⟩
  · exact ⟨x1, rfl, s1⟩
  · exact ⟨x2, rfl, s2⟩
  · exact ⟨x3, rfl, s3⟩

/-- Lane `i` of a vector reduced from accumulators: a field element index splits into its
64-bit element `j` and its parity. -/
theorem acc_split (evn odd : V) (i : ℕ) (hi : i < 8) :
    ∃ j < 4, (i = 2 * j ∧ acc evn odd i = w evn j) ∨ (i = 2 * j + 1 ∧ acc evn odd i = w odd j) := by
  refine ⟨i / 2, by omega, ?_⟩
  by_cases h : i % 2 = 0
  · left; exact ⟨by omega, by simp [acc, h]⟩
  · right; exact ⟨by omega, by simp [acc, h]⟩


open p3_monty_31_avx2 in
/-- `dot_product_8(lhs, rhs)`, on values whose lanes are canonical: lane `i` is the canonical
`r` with `r · 2^32 ≡ Σ_k lhs[k]_i · rhs[k]_i (mod p)`. -/
theorem dot8 {PMP LHS RHS : Type} (inst : data_traits.PackedMontyParameters PMP)
    (iL : x86_64_avx2.packing.IntoM256 LHS PMP) (iR : x86_64_avx2.packing.IntoM256 RHS PMP)
    (lhs : Std.Array LHS 8#usize) (rhs : Std.Array RHS 8#usize) (el er : ℕ → ℕ → ℕ) (p mu : ℕ)
    (hv : Prm inst p mu)
    (hl : ∀ k < 8, ∃ x, lhs.val[k]? = some x ∧ IntoSpec iL x (el k))
    (hr : ∀ k < 8, ∃ y, rhs.val[k]? = some y ∧ IntoSpec iR y (er k))
    (hb : ∀ k < 8, ∀ i < 8, el k i < p ∧ er k i < p) :
    ∃ r, x86_64_avx2.packing.dot_product_8 inst iL iR lhs rhs = .ok r ∧
      ∀ i < 8, ln r i < p ∧ ln r i * 2 ^ 32 % p = dsum el er 8 i % p := by
  obtain ⟨P, hPP, hP⟩ := hv.P
  obtain ⟨M, hMM, hM⟩ := hv.M
  have hp := hv.lt
  have hp0 := hv.pos
  obtain ⟨x0, hx0, s0⟩ := hl 0 (by norm_num)
  obtain ⟨x1, hx1, s1⟩ := hl 1 (by norm_num)
  obtain ⟨x2, hx2, s2⟩ := hl 2 (by norm_num)
  obtain ⟨x3, hx3, s3⟩ := hl 3 (by norm_num)
  obtain ⟨x4, hx4, s4⟩ := hl 4 (by norm_num)
  obtain ⟨x5, hx5, s5⟩ := hl 5 (by norm_num)
  obtain ⟨x6, hx6, s6⟩ := hl 6 (by norm_num)
  obtain ⟨x7, hx7, s7⟩ := hl 7 (by norm_num)
  obtain ⟨y0, hy0, t0⟩ := hr 0 (by norm_num)
  obtain ⟨y1, hy1, t1⟩ := hr 1 (by norm_num)
  obtain ⟨y2, hy2, t2⟩ := hr 2 (by norm_num)
  obtain ⟨y3, hy3, t3⟩ := hr 3 (by norm_num)
  obtain ⟨y4, hy4, t4⟩ := hr 4 (by norm_num)
  obtain ⟨y5, hy5, t5⟩ := hr 5 (by norm_num)
  obtain ⟨y6, hy6, t6⟩ := hr 6 (by norm_num)
  obtain ⟨y7, hy7, t7⟩ := hr 7 (by norm_num)
  let elB : ℕ → ℕ → ℕ := fun k => el (k + 4)
  let erB : ℕ → ℕ → ℕ := fun k => er (k + 4)
  obtain ⟨ae, ao, ha, hal⟩ := wide_dot4 inst iL iR
    (Std.Array.make 4#usize [x0, x1, x2, x3] (by simp)) (Std.Array.make 4#usize [y0, y1, y2,
      y3] (by simp))
    el er p hp (make4_spec iL el x0 x1 x2 x3 s0 s1 s2 s3 _)
    (make4_spec iR er y0 y1 y2 y3 t0 t1 t2 t3 _) (fun k hk => hb k (by omega))
  obtain ⟨be, bo, hbw, hbl⟩ := wide_dot4 inst iL iR
    (Std.Array.make 4#usize [x4, x5, x6, x7] (by simp)) (Std.Array.make 4#usize [y4, y5, y6,
      y7] (by simp))
    elB erB p hp (make4_spec iL elB x4 x5 x6 x7 s4 s5 s6 s7 _)
    (make4_spec iR erB y4 y5 y6 y7 t4 t5 t6 t7 _) (fun k hk => hb (k + 4) (by omega))
  have wA : ∀ i < 8, dsum el er 4 i < 2 * 2 ^ 32 * p := fun i hi => by
    have := dsum_wide el er 4 i p 4 hp hp0 le_rfl (by norm_num) (fun k hk => hb k (by omega) i hi)
    omega
  have wB : ∀ i < 8, dsum elB erB 4 i < 2 * 2 ^ 32 * p := fun i hi => by
    have := dsum_wide elB erB 4 i p 4 hp hp0 le_rfl (by norm_num)
      (fun k hk => hb (k + 4) (by omega) i hi)
    omega
  obtain ⟨fae, hfae, hfael⟩ := fold_wide _ P ae p hp hPP hP
    (fun j hj => by rw [(hal j hj).1]; exact wA _ (by omega))
  obtain ⟨fbe, hfbe, hfbel⟩ := fold_wide _ P be p hp hPP hP
    (fun j hj => by rw [(hbl j hj).1]; exact wB _ (by omega))
  obtain ⟨fao, hfao, hfaol⟩ := fold_wide _ P ao p hp hPP hP
    (fun j hj => by rw [(hal j hj).2]; exact wA _ (by omega))
  obtain ⟨fbo, hfbo, hfbol⟩ := fold_wide _ P bo p hp hPP hP
    (fun j hj => by rw [(hbl j hj).2]; exact wB _ (by omega))
  obtain ⟨de, hde, hdel⟩ := add_epi64 fae fbe
  obtain ⟨dd, hdd, hddl⟩ := add_epi64 fao fbo
  have hde' : ∀ j < 4, w de j = w fae j + w fbe j := fun j hj => by
    rw [hdel j hj]; have := (hfael j hj).1; have := (hfbel j hj).1
    exact Nat.mod_eq_of_lt (by omega)
  have hdd' : ∀ j < 4, w dd j = w fao j + w fbo j := fun j hj => by
    rw [hddl j hj]; have := (hfaol j hj).1; have := (hfbol j hj).1
    exact Nat.mod_eq_of_lt (by omega)
  obtain ⟨r, hr, hrl⟩ := monty_red_wide inst P M de dd p mu hp hp0 hv.inv hPP hP hMM hM
    (fun j hj => by rw [hde' j hj]; have := (hfael j hj).1; have := (hfbel j hj).1; omega)
    (fun j hj => by rw [hdd' j hj]; have := (hfaol j hj).1; have := (hfbol j hj).1; omega)
  refine ⟨r, ?_, fun i hi => ⟨(hrl i hi).1, ?_⟩⟩
  · unfold x86_64_avx2.packing.dot_product_8
    simp only [index_some lhs 0#usize x0 hx0, index_some lhs 1#usize x1 hx1,
      index_some lhs 2#usize x2 hx2, index_some lhs 3#usize x3 hx3,
      index_some lhs 4#usize x4 hx4, index_some lhs 5#usize x5 hx5,
      index_some lhs 6#usize x6 hx6, index_some lhs 7#usize x7 hx7,
      index_some rhs 0#usize y0 hy0, index_some rhs 1#usize y1 hy1,
      index_some rhs 2#usize y2 hy2, index_some rhs 3#usize y3 hy3,
      index_some rhs 4#usize y4 hy4, index_some rhs 5#usize y5 hy5,
      index_some rhs 6#usize y6 hy6, index_some rhs 7#usize y7 hy7, bind_ok, ha, hbw,
      Aeneas.Std.uncurry, hfae, hfbe, hfao, hfbo, hde, hdd, hr]
  · rw [(hrl i hi).2, show (8 : ℕ) = 4 + 4 from rfl, dsum_add]
    obtain ⟨j, hj, h | h⟩ := acc_split de dd i hi
    · obtain ⟨rfl, hac⟩ := h
      rw [hac, hde' j hj, Nat.add_mod, (hfael j hj).2.1, (hfbel j hj).2.1, (hal j hj).1,
        (hbl j hj).1, ← Nat.add_mod]
    · obtain ⟨rfl, hac⟩ := h
      rw [hac, hdd' j hj, Nat.add_mod, (hfaol j hj).2.1, (hfbol j hj).2.1, (hal j hj).2,
        (hbl j hj).2, ← Nat.add_mod]

theorem make1_spec {S PMP : Type} (inst : p3_monty_31_avx2.x86_64_avx2.packing.IntoM256 S PMP)
    (e : ℕ → ℕ → ℕ) (x0 : S) (s0 : IntoSpec inst x0 (e 0)) (h) :
    ∀ k < 1, ∃ x, (Std.Array.make 1#usize [x0] h).val[k]? = some x ∧ IntoSpec inst x (e k) := by
  intro k hk
  interval_cases k
  · exact ⟨x0, rfl, s0⟩

theorem make2_spec {S PMP : Type} (inst : p3_monty_31_avx2.x86_64_avx2.packing.IntoM256 S PMP)
    (e : ℕ → ℕ → ℕ) (x0 x1 : S) (s0 : IntoSpec inst x0 (e 0)) (s1 : IntoSpec inst x1 (e 1)) (h) :
    ∀ k < 2, ∃ x, (Std.Array.make 2#usize [x0, x1] h).val[k]? = some x ∧ IntoSpec inst x (e k) := by
  intro k hk
  interval_cases k
  · exact ⟨x0, rfl, s0⟩
  · exact ⟨x1, rfl, s1⟩

theorem make3_spec {S PMP : Type} (inst : p3_monty_31_avx2.x86_64_avx2.packing.IntoM256 S PMP)
    (e : ℕ → ℕ → ℕ) (x0 x1 x2 : S) (s0 : IntoSpec inst x0 (e 0)) (s1 : IntoSpec inst x1 (e 1)) (s2 : IntoSpec inst x2 (e 2)) (h) :
    ∀ k < 3, ∃ x, (Std.Array.make 3#usize [x0, x1,
      x2] h).val[k]? = some x ∧ IntoSpec inst x (e k) := by
  intro k hk
  interval_cases k
  · exact ⟨x0, rfl, s0⟩
  · exact ⟨x1, rfl, s1⟩
  · exact ⟨x2, rfl, s2⟩

open p3_monty_31_avx2 in
/-- `dot_product_5(lhs, rhs)`, on values whose lanes are canonical: lane `i` is the canonical
`r` with `r · 2^32 ≡ Σ_k lhs[k]_i · rhs[k]_i (mod p)`. -/
theorem dot5 {PMP LHS RHS : Type} (inst : data_traits.PackedMontyParameters PMP)
    (iL : x86_64_avx2.packing.IntoM256 LHS PMP) (iR : x86_64_avx2.packing.IntoM256 RHS PMP)
    (lhs : Std.Array LHS 5#usize) (rhs : Std.Array RHS 5#usize) (el er : ℕ → ℕ → ℕ) (p mu : ℕ)
    (hv : Prm inst p mu)
    (hl : ∀ k < 5, ∃ x, lhs.val[k]? = some x ∧ IntoSpec iL x (el k))
    (hr : ∀ k < 5, ∃ y, rhs.val[k]? = some y ∧ IntoSpec iR y (er k))
    (hb : ∀ k < 5, ∀ i < 8, el k i < p ∧ er k i < p) :
    ∃ r, x86_64_avx2.packing.dot_product_5 inst iL iR lhs rhs = .ok r ∧
      ∀ i < 8, ln r i < p ∧ ln r i * 2 ^ 32 % p = dsum el er 5 i % p := by
  obtain ⟨P, hPP, hP⟩ := hv.P
  obtain ⟨M, hMM, hM⟩ := hv.M
  have hp := hv.lt
  have hp0 := hv.pos
  obtain ⟨x0, hx0, s0⟩ := hl 0 (by norm_num)
  obtain ⟨y0, hy0, t0⟩ := hr 0 (by norm_num)
  obtain ⟨x1, hx1, s1⟩ := hl 1 (by norm_num)
  obtain ⟨y1, hy1, t1⟩ := hr 1 (by norm_num)
  obtain ⟨x2, hx2, s2⟩ := hl 2 (by norm_num)
  obtain ⟨y2, hy2, t2⟩ := hr 2 (by norm_num)
  obtain ⟨x3, hx3, s3⟩ := hl 3 (by norm_num)
  obtain ⟨y3, hy3, t3⟩ := hr 3 (by norm_num)
  obtain ⟨x4, hx4, s4⟩ := hl 4 (by norm_num)
  obtain ⟨y4, hy4, t4⟩ := hr 4 (by norm_num)
  let elB : ℕ → ℕ → ℕ := fun k => el (k + 4)
  let erB : ℕ → ℕ → ℕ := fun k => er (k + 4)
  obtain ⟨ae, ao, ha, hal⟩ := wide_dot4 inst iL iR
    (Std.Array.make 4#usize [x0, x1, x2, x3] (by simp)) (Std.Array.make 4#usize [y0, y1, y2,
      y3] (by simp))
    el er p hp (make4_spec iL el x0 x1 x2 x3 s0 s1 s2 s3 _)
    (make4_spec iR er y0 y1 y2 y3 t0 t1 t2 t3 _) (fun k hk => hb k (by omega))
  obtain ⟨be, bo, hbw, hbl⟩ := wide_dot1 inst iL iR
    (Std.Array.make 1#usize [x4] (by simp)) (Std.Array.make 1#usize [y4] (by simp))
    elB erB p hp (make1_spec iL elB x4 s4 _)
    (make1_spec iR erB y4 t4 _) (fun k hk => hb (k + 4) (by omega))
  have wA : ∀ i < 8, dsum el er 4 i < 2 * 2 ^ 32 * p := fun i hi => by
    have := dsum_wide el er 4 i p 4 hp hp0 le_rfl (by norm_num) (fun k hk => hb k (by omega) i hi)
    omega
  have wB : ∀ i < 8, dsum elB erB 1 i < 2 ^ 32 * p := fun i hi => by
    have := dsum_wide elB erB 1 i p 2 hp hp0 (by norm_num) (by norm_num)
      (fun k hk => hb (k + 4) (by omega) i hi)
    omega
  obtain ⟨fae, hfae, hfael⟩ := fold_wide _ P ae p hp hPP hP
    (fun j hj => by rw [(hal j hj).1]; exact wA _ (by omega))
  obtain ⟨fao, hfao, hfaol⟩ := fold_wide _ P ao p hp hPP hP
    (fun j hj => by rw [(hal j hj).2]; exact wA _ (by omega))
  obtain ⟨de, hde, hdel⟩ := add_epi64 fae be
  obtain ⟨dd, hdd, hddl⟩ := add_epi64 fao bo
  have hde' : ∀ j < 4, w de j = w fae j + w be j := fun j hj => by
    rw [hdel j hj]; have := (hfael j hj).1; have := (show w be j < 2 ^ 32 * p by rw [(hbl j hj).1]; exact wB _ (by omega))
    exact Nat.mod_eq_of_lt (by omega)
  have hdd' : ∀ j < 4, w dd j = w fao j + w bo j := fun j hj => by
    rw [hddl j hj]; have := (hfaol j hj).1; have := (show w bo j < 2 ^ 32 * p by rw [(hbl j hj).2]; exact wB _ (by omega))
    exact Nat.mod_eq_of_lt (by omega)
  obtain ⟨r, hr, hrl⟩ := monty_red_wide inst P M de dd p mu hp hp0 hv.inv hPP hP hMM hM
    (fun j hj => by rw [hde' j hj]; have := (hfael j hj).1; have := (show w be j < 2 ^ 32 * p by rw [(hbl j hj).1]; exact wB _ (by omega)); omega)
    (fun j hj => by rw [hdd' j hj]; have := (hfaol j hj).1; have := (show w bo j < 2 ^ 32 * p by rw [(hbl j hj).2]; exact wB _ (by omega)); omega)
  refine ⟨r, ?_, fun i hi => ⟨(hrl i hi).1, ?_⟩⟩
  · unfold x86_64_avx2.packing.dot_product_5
    simp only [index_some lhs 0#usize x0 hx0,
      index_some rhs 0#usize y0 hy0,
      index_some lhs 1#usize x1 hx1,
      index_some rhs 1#usize y1 hy1,
      index_some lhs 2#usize x2 hx2,
      index_some rhs 2#usize y2 hy2,
      index_some lhs 3#usize x3 hx3,
      index_some rhs 3#usize y3 hy3,
      index_some lhs 4#usize x4 hx4,
      index_some rhs 4#usize y4 hy4,
      bind_ok, ha, hbw, Aeneas.Std.uncurry, hfae, hfao, hde, hdd, hr]
  · rw [(hrl i hi).2, show (5 : ℕ) = 4 + 1 from rfl, dsum_add]
    obtain ⟨j, hj, h | h⟩ := acc_split de dd i hi
    · obtain ⟨rfl, hac⟩ := h
      rw [hac, hde' j hj, Nat.add_mod, (hfael j hj).2.1, (hbl j hj).1, (hal j hj).1, ← Nat.add_mod]
    · obtain ⟨rfl, hac⟩ := h
      rw [hac, hdd' j hj, Nat.add_mod, (hfaol j hj).2.1, (hbl j hj).2, (hal j hj).2, ← Nat.add_mod]

open p3_monty_31_avx2 in
/-- `dot_product_6(lhs, rhs)`, on values whose lanes are canonical: lane `i` is the canonical
`r` with `r · 2^32 ≡ Σ_k lhs[k]_i · rhs[k]_i (mod p)`. -/
theorem dot6 {PMP LHS RHS : Type} (inst : data_traits.PackedMontyParameters PMP)
    (iL : x86_64_avx2.packing.IntoM256 LHS PMP) (iR : x86_64_avx2.packing.IntoM256 RHS PMP)
    (lhs : Std.Array LHS 6#usize) (rhs : Std.Array RHS 6#usize) (el er : ℕ → ℕ → ℕ) (p mu : ℕ)
    (hv : Prm inst p mu)
    (hl : ∀ k < 6, ∃ x, lhs.val[k]? = some x ∧ IntoSpec iL x (el k))
    (hr : ∀ k < 6, ∃ y, rhs.val[k]? = some y ∧ IntoSpec iR y (er k))
    (hb : ∀ k < 6, ∀ i < 8, el k i < p ∧ er k i < p) :
    ∃ r, x86_64_avx2.packing.dot_product_6 inst iL iR lhs rhs = .ok r ∧
      ∀ i < 8, ln r i < p ∧ ln r i * 2 ^ 32 % p = dsum el er 6 i % p := by
  obtain ⟨P, hPP, hP⟩ := hv.P
  obtain ⟨M, hMM, hM⟩ := hv.M
  have hp := hv.lt
  have hp0 := hv.pos
  obtain ⟨x0, hx0, s0⟩ := hl 0 (by norm_num)
  obtain ⟨y0, hy0, t0⟩ := hr 0 (by norm_num)
  obtain ⟨x1, hx1, s1⟩ := hl 1 (by norm_num)
  obtain ⟨y1, hy1, t1⟩ := hr 1 (by norm_num)
  obtain ⟨x2, hx2, s2⟩ := hl 2 (by norm_num)
  obtain ⟨y2, hy2, t2⟩ := hr 2 (by norm_num)
  obtain ⟨x3, hx3, s3⟩ := hl 3 (by norm_num)
  obtain ⟨y3, hy3, t3⟩ := hr 3 (by norm_num)
  obtain ⟨x4, hx4, s4⟩ := hl 4 (by norm_num)
  obtain ⟨y4, hy4, t4⟩ := hr 4 (by norm_num)
  obtain ⟨x5, hx5, s5⟩ := hl 5 (by norm_num)
  obtain ⟨y5, hy5, t5⟩ := hr 5 (by norm_num)
  let elB : ℕ → ℕ → ℕ := fun k => el (k + 4)
  let erB : ℕ → ℕ → ℕ := fun k => er (k + 4)
  obtain ⟨ae, ao, ha, hal⟩ := wide_dot4 inst iL iR
    (Std.Array.make 4#usize [x0, x1, x2, x3] (by simp)) (Std.Array.make 4#usize [y0, y1, y2,
      y3] (by simp))
    el er p hp (make4_spec iL el x0 x1 x2 x3 s0 s1 s2 s3 _)
    (make4_spec iR er y0 y1 y2 y3 t0 t1 t2 t3 _) (fun k hk => hb k (by omega))
  obtain ⟨be, bo, hbw, hbl⟩ := wide_dot2 inst iL iR
    (Std.Array.make 2#usize [x4, x5] (by simp)) (Std.Array.make 2#usize [y4, y5] (by simp))
    elB erB p hp (make2_spec iL elB x4 x5 s4 s5 _)
    (make2_spec iR erB y4 y5 t4 t5 _) (fun k hk => hb (k + 4) (by omega))
  have wA : ∀ i < 8, dsum el er 4 i < 2 * 2 ^ 32 * p := fun i hi => by
    have := dsum_wide el er 4 i p 4 hp hp0 le_rfl (by norm_num) (fun k hk => hb k (by omega) i hi)
    omega
  have wB : ∀ i < 8, dsum elB erB 2 i < 2 ^ 32 * p := fun i hi => by
    have := dsum_wide elB erB 2 i p 2 hp hp0 (by norm_num) (by norm_num)
      (fun k hk => hb (k + 4) (by omega) i hi)
    omega
  obtain ⟨fae, hfae, hfael⟩ := fold_wide _ P ae p hp hPP hP
    (fun j hj => by rw [(hal j hj).1]; exact wA _ (by omega))
  obtain ⟨fao, hfao, hfaol⟩ := fold_wide _ P ao p hp hPP hP
    (fun j hj => by rw [(hal j hj).2]; exact wA _ (by omega))
  obtain ⟨de, hde, hdel⟩ := add_epi64 fae be
  obtain ⟨dd, hdd, hddl⟩ := add_epi64 fao bo
  have hde' : ∀ j < 4, w de j = w fae j + w be j := fun j hj => by
    rw [hdel j hj]; have := (hfael j hj).1; have := (show w be j < 2 ^ 32 * p by rw [(hbl j hj).1]; exact wB _ (by omega))
    exact Nat.mod_eq_of_lt (by omega)
  have hdd' : ∀ j < 4, w dd j = w fao j + w bo j := fun j hj => by
    rw [hddl j hj]; have := (hfaol j hj).1; have := (show w bo j < 2 ^ 32 * p by rw [(hbl j hj).2]; exact wB _ (by omega))
    exact Nat.mod_eq_of_lt (by omega)
  obtain ⟨r, hr, hrl⟩ := monty_red_wide inst P M de dd p mu hp hp0 hv.inv hPP hP hMM hM
    (fun j hj => by rw [hde' j hj]; have := (hfael j hj).1; have := (show w be j < 2 ^ 32 * p by rw [(hbl j hj).1]; exact wB _ (by omega)); omega)
    (fun j hj => by rw [hdd' j hj]; have := (hfaol j hj).1; have := (show w bo j < 2 ^ 32 * p by rw [(hbl j hj).2]; exact wB _ (by omega)); omega)
  refine ⟨r, ?_, fun i hi => ⟨(hrl i hi).1, ?_⟩⟩
  · unfold x86_64_avx2.packing.dot_product_6
    simp only [index_some lhs 0#usize x0 hx0,
      index_some rhs 0#usize y0 hy0,
      index_some lhs 1#usize x1 hx1,
      index_some rhs 1#usize y1 hy1,
      index_some lhs 2#usize x2 hx2,
      index_some rhs 2#usize y2 hy2,
      index_some lhs 3#usize x3 hx3,
      index_some rhs 3#usize y3 hy3,
      index_some lhs 4#usize x4 hx4,
      index_some rhs 4#usize y4 hy4,
      index_some lhs 5#usize x5 hx5,
      index_some rhs 5#usize y5 hy5,
      bind_ok, ha, hbw, Aeneas.Std.uncurry, hfae, hfao, hde, hdd, hr]
  · rw [(hrl i hi).2, show (6 : ℕ) = 4 + 2 from rfl, dsum_add]
    obtain ⟨j, hj, h | h⟩ := acc_split de dd i hi
    · obtain ⟨rfl, hac⟩ := h
      rw [hac, hde' j hj, Nat.add_mod, (hfael j hj).2.1, (hbl j hj).1, (hal j hj).1, ← Nat.add_mod]
    · obtain ⟨rfl, hac⟩ := h
      rw [hac, hdd' j hj, Nat.add_mod, (hfaol j hj).2.1, (hbl j hj).2, (hal j hj).2, ← Nat.add_mod]

open p3_monty_31_avx2 in
/-- `dot_product_7(lhs, rhs)`, on values whose lanes are canonical: lane `i` is the canonical
`r` with `r · 2^32 ≡ Σ_k lhs[k]_i · rhs[k]_i (mod p)`. -/
theorem dot7 {PMP LHS RHS : Type} (inst : data_traits.PackedMontyParameters PMP)
    (iL : x86_64_avx2.packing.IntoM256 LHS PMP) (iR : x86_64_avx2.packing.IntoM256 RHS PMP)
    (lhs : Std.Array LHS 7#usize) (rhs : Std.Array RHS 7#usize) (el er : ℕ → ℕ → ℕ) (p mu : ℕ)
    (hv : Prm inst p mu)
    (hl : ∀ k < 7, ∃ x, lhs.val[k]? = some x ∧ IntoSpec iL x (el k))
    (hr : ∀ k < 7, ∃ y, rhs.val[k]? = some y ∧ IntoSpec iR y (er k))
    (hb : ∀ k < 7, ∀ i < 8, el k i < p ∧ er k i < p) :
    ∃ r, x86_64_avx2.packing.dot_product_7 inst iL iR lhs rhs = .ok r ∧
      ∀ i < 8, ln r i < p ∧ ln r i * 2 ^ 32 % p = dsum el er 7 i % p := by
  obtain ⟨P, hPP, hP⟩ := hv.P
  obtain ⟨M, hMM, hM⟩ := hv.M
  have hp := hv.lt
  have hp0 := hv.pos
  obtain ⟨x0, hx0, s0⟩ := hl 0 (by norm_num)
  obtain ⟨y0, hy0, t0⟩ := hr 0 (by norm_num)
  obtain ⟨x1, hx1, s1⟩ := hl 1 (by norm_num)
  obtain ⟨y1, hy1, t1⟩ := hr 1 (by norm_num)
  obtain ⟨x2, hx2, s2⟩ := hl 2 (by norm_num)
  obtain ⟨y2, hy2, t2⟩ := hr 2 (by norm_num)
  obtain ⟨x3, hx3, s3⟩ := hl 3 (by norm_num)
  obtain ⟨y3, hy3, t3⟩ := hr 3 (by norm_num)
  obtain ⟨x4, hx4, s4⟩ := hl 4 (by norm_num)
  obtain ⟨y4, hy4, t4⟩ := hr 4 (by norm_num)
  obtain ⟨x5, hx5, s5⟩ := hl 5 (by norm_num)
  obtain ⟨y5, hy5, t5⟩ := hr 5 (by norm_num)
  obtain ⟨x6, hx6, s6⟩ := hl 6 (by norm_num)
  obtain ⟨y6, hy6, t6⟩ := hr 6 (by norm_num)
  let elB : ℕ → ℕ → ℕ := fun k => el (k + 4)
  let erB : ℕ → ℕ → ℕ := fun k => er (k + 4)
  obtain ⟨ae, ao, ha, hal⟩ := wide_dot4 inst iL iR
    (Std.Array.make 4#usize [x0, x1, x2, x3] (by simp)) (Std.Array.make 4#usize [y0, y1, y2,
      y3] (by simp))
    el er p hp (make4_spec iL el x0 x1 x2 x3 s0 s1 s2 s3 _)
    (make4_spec iR er y0 y1 y2 y3 t0 t1 t2 t3 _) (fun k hk => hb k (by omega))
  obtain ⟨be, bo, hbw, hbl⟩ := wide_dot3 inst iL iR
    (Std.Array.make 3#usize [x4, x5, x6] (by simp)) (Std.Array.make 3#usize [y4, y5, y6] (by simp))
    elB erB p hp (make3_spec iL elB x4 x5 x6 s4 s5 s6 _)
    (make3_spec iR erB y4 y5 y6 t4 t5 t6 _) (fun k hk => hb (k + 4) (by omega))
  have wA : ∀ i < 8, dsum el er 4 i < 2 * 2 ^ 32 * p := fun i hi => by
    have := dsum_wide el er 4 i p 4 hp hp0 le_rfl (by norm_num) (fun k hk => hb k (by omega) i hi)
    omega
  have wB : ∀ i < 8, dsum elB erB 3 i < 2 * 2 ^ 32 * p := fun i hi => by
    have := dsum_wide elB erB 3 i p 4 hp hp0 (by norm_num) (by norm_num)
      (fun k hk => hb (k + 4) (by omega) i hi)
    omega
  obtain ⟨fae, hfae, hfael⟩ := fold_wide _ P ae p hp hPP hP
    (fun j hj => by rw [(hal j hj).1]; exact wA _ (by omega))
  obtain ⟨fao, hfao, hfaol⟩ := fold_wide _ P ao p hp hPP hP
    (fun j hj => by rw [(hal j hj).2]; exact wA _ (by omega))
  obtain ⟨fbe, hfbe, hfbel⟩ := fold_wide _ P be p hp hPP hP
    (fun j hj => by rw [(hbl j hj).1]; exact wB _ (by omega))
  obtain ⟨fbo, hfbo, hfbol⟩ := fold_wide _ P bo p hp hPP hP
    (fun j hj => by rw [(hbl j hj).2]; exact wB _ (by omega))
  obtain ⟨de, hde, hdel⟩ := add_epi64 fae fbe
  obtain ⟨dd, hdd, hddl⟩ := add_epi64 fao fbo
  have hde' : ∀ j < 4, w de j = w fae j + w fbe j := fun j hj => by
    rw [hdel j hj]; have := (hfael j hj).1; have := (hfbel j hj).1
    exact Nat.mod_eq_of_lt (by omega)
  have hdd' : ∀ j < 4, w dd j = w fao j + w fbo j := fun j hj => by
    rw [hddl j hj]; have := (hfaol j hj).1; have := (hfbol j hj).1
    exact Nat.mod_eq_of_lt (by omega)
  obtain ⟨r, hr, hrl⟩ := monty_red_wide inst P M de dd p mu hp hp0 hv.inv hPP hP hMM hM
    (fun j hj => by rw [hde' j hj]; have := (hfael j hj).1; have := (hfbel j hj).1; omega)
    (fun j hj => by rw [hdd' j hj]; have := (hfaol j hj).1; have := (hfbol j hj).1; omega)
  refine ⟨r, ?_, fun i hi => ⟨(hrl i hi).1, ?_⟩⟩
  · unfold x86_64_avx2.packing.dot_product_7
    simp only [index_some lhs 0#usize x0 hx0,
      index_some rhs 0#usize y0 hy0,
      index_some lhs 1#usize x1 hx1,
      index_some rhs 1#usize y1 hy1,
      index_some lhs 2#usize x2 hx2,
      index_some rhs 2#usize y2 hy2,
      index_some lhs 3#usize x3 hx3,
      index_some rhs 3#usize y3 hy3,
      index_some lhs 4#usize x4 hx4,
      index_some rhs 4#usize y4 hy4,
      index_some lhs 5#usize x5 hx5,
      index_some rhs 5#usize y5 hy5,
      index_some lhs 6#usize x6 hx6,
      index_some rhs 6#usize y6 hy6,
      bind_ok, ha, hbw, Aeneas.Std.uncurry, hfae, hfao, hfbe, hfbo, hde, hdd, hr]
  · rw [(hrl i hi).2, show (7 : ℕ) = 4 + 3 from rfl, dsum_add]
    obtain ⟨j, hj, h | h⟩ := acc_split de dd i hi
    · obtain ⟨rfl, hac⟩ := h
      rw [hac, hde' j hj, Nat.add_mod, (hfael j hj).2.1, (hfbel j hj).2.1, (hbl j hj).1,
        (hal j hj).1, ← Nat.add_mod]
    · obtain ⟨rfl, hac⟩ := h
      rw [hac, hdd' j hj, Nat.add_mod, (hfaol j hj).2.1, (hfbol j hj).2.1, (hbl j hj).2,
        (hal j hj).2, ← Nat.add_mod]

open p3_monty_31_avx2 in
/-- `dot_product_4(lhs, rhs)`, on values whose lanes are canonical: lane `i` is the canonical
`r` with `r · 2^32 ≡ Σ_k lhs[k]_i · rhs[k]_i (mod p)`. -/
theorem dot4 {PMP LHS RHS : Type} (inst : data_traits.PackedMontyParameters PMP)
    (iL : x86_64_avx2.packing.IntoM256 LHS PMP) (iR : x86_64_avx2.packing.IntoM256 RHS PMP)
    (lhs : Std.Array LHS 4#usize) (rhs : Std.Array RHS 4#usize) (el er : ℕ → ℕ → ℕ) (p mu : ℕ)
    (hv : Prm inst p mu)
    (hl : ∀ k < 4, ∃ x, lhs.val[k]? = some x ∧ IntoSpec iL x (el k))
    (hr : ∀ k < 4, ∃ y, rhs.val[k]? = some y ∧ IntoSpec iR y (er k))
    (hb : ∀ k < 4, ∀ i < 8, el k i < p ∧ er k i < p) :
    ∃ r, x86_64_avx2.packing.dot_product_4 inst iL iR lhs rhs = .ok r ∧
      ∀ i < 8, ln r i < p ∧ ln r i * 2 ^ 32 % p = dsum el er 4 i % p := by
  obtain ⟨P, hPP, hP⟩ := hv.P
  obtain ⟨M, hMM, hM⟩ := hv.M
  have hp := hv.lt
  have hp0 := hv.pos
  obtain ⟨x0, hx0, s0⟩ := hl 0 (by norm_num)
  obtain ⟨y0, hy0, t0⟩ := hr 0 (by norm_num)
  obtain ⟨a0, ha0, ha0l⟩ := s0.vec
  obtain ⟨c0, hc0, hc0l⟩ := s0.shifted
  obtain ⟨b0, hb0, hb0l⟩ := t0.vec
  obtain ⟨d0, hd0, hd0l⟩ := t0.shifted
  obtain ⟨e0, he0, he0l⟩ := mul_w a0 b0
  obtain ⟨o0, ho0, ho0l⟩ := mul_w c0 d0
  obtain ⟨x1, hx1, s1⟩ := hl 1 (by norm_num)
  obtain ⟨y1, hy1, t1⟩ := hr 1 (by norm_num)
  obtain ⟨a1, ha1, ha1l⟩ := s1.vec
  obtain ⟨c1, hc1, hc1l⟩ := s1.shifted
  obtain ⟨b1, hb1, hb1l⟩ := t1.vec
  obtain ⟨d1, hd1, hd1l⟩ := t1.shifted
  obtain ⟨e1, he1, he1l⟩ := mul_w a1 b1
  obtain ⟨o1, ho1, ho1l⟩ := mul_w c1 d1
  obtain ⟨x2, hx2, s2⟩ := hl 2 (by norm_num)
  obtain ⟨y2, hy2, t2⟩ := hr 2 (by norm_num)
  obtain ⟨a2, ha2, ha2l⟩ := s2.vec
  obtain ⟨c2, hc2, hc2l⟩ := s2.shifted
  obtain ⟨b2, hb2, hb2l⟩ := t2.vec
  obtain ⟨d2, hd2, hd2l⟩ := t2.shifted
  obtain ⟨e2, he2, he2l⟩ := mul_w a2 b2
  obtain ⟨o2, ho2, ho2l⟩ := mul_w c2 d2
  obtain ⟨x3, hx3, s3⟩ := hl 3 (by norm_num)
  obtain ⟨y3, hy3, t3⟩ := hr 3 (by norm_num)
  obtain ⟨a3, ha3, ha3l⟩ := s3.vec
  obtain ⟨c3, hc3, hc3l⟩ := s3.shifted
  obtain ⟨b3, hb3, hb3l⟩ := t3.vec
  obtain ⟨d3, hd3, hd3l⟩ := t3.shifted
  obtain ⟨e3, he3, he3l⟩ := mul_w a3 b3
  obtain ⟨o3, ho3, ho3l⟩ := mul_w c3 d3
  obtain ⟨e01, he01, he01l⟩ := add_epi64 e0 e1
  obtain ⟨o01, ho01, ho01l⟩ := add_epi64 o0 o1
  obtain ⟨e23, he23, he23l⟩ := add_epi64 e2 e3
  obtain ⟨o23, ho23, ho23l⟩ := add_epi64 o2 o3
  obtain ⟨de, hde, hdel⟩ := add_epi64 e01 e23
  obtain ⟨dd, hdd, hddl⟩ := add_epi64 o01 o23
  have bnd : ∀ k < 4, ∀ i < 8, el k i * er k i < 2 ^ 62 := fun k hk i hi =>
    prod_lt _ _ p hp (hb k hk i hi).1 (hb k hk i hi).2
  have hsum : ∀ j < 4, w de j = dsum el er 4 (2 * j) ∧ w dd j = dsum el er 4 (2 * j + 1) := by
    intro j hj
    have := bnd 0 (by norm_num) (2 * j) (by omega); have := bnd 1 (by norm_num) (2 * j) (by omega)
    have := bnd 2 (by norm_num) (2 * j) (by omega); have := bnd 3 (by norm_num) (2 * j) (by omega)
    have := bnd 0 (by norm_num) (2 * j + 1) (by omega)
    have := bnd 1 (by norm_num) (2 * j + 1) (by omega)
    have := bnd 2 (by norm_num) (2 * j + 1) (by omega)
    have := bnd 3 (by norm_num) (2 * j + 1) (by omega)
    simp only [dsum, Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    rw [hdel j hj, he01l j hj, he23l j hj, he0l j hj, he1l j hj, he2l j hj, he3l j hj,
      hddl j hj, ho01l j hj, ho23l j hj, ho0l j hj, ho1l j hj, ho2l j hj, ho3l j hj,
      ha0l j hj, ha1l j hj, ha2l j hj, ha3l j hj, hb0l j hj, hb1l j hj, hb2l j hj, hb3l j hj,
      hc0l j hj, hc1l j hj, hc2l j hj, hc3l j hj, hd0l j hj, hd1l j hj, hd2l j hj, hd3l j hj]
    omega
  have wS : ∀ i < 8, dsum el er 4 i < 2 * 2 ^ 32 * p := fun i hi => by
    have := dsum_wide el er 4 i p 4 hp hp0 le_rfl (by norm_num) (fun k hk => hb k (by omega) i hi)
    omega
  obtain ⟨r, hr, hrl⟩ := monty_red_wide inst P M de dd p mu hp hp0 hv.inv hPP hP hMM hM
    (fun j hj => by rw [(hsum j hj).1]; exact wS _ (by omega))
    (fun j hj => by rw [(hsum j hj).2]; exact wS _ (by omega))
  refine ⟨r, ?_, fun i hi => ⟨(hrl i hi).1, ?_⟩⟩
  · unfold x86_64_avx2.packing.dot_product_4
    simp only [index_some lhs 0#usize x0 hx0,
      index_some rhs 0#usize y0 hy0,
      index_some lhs 1#usize x1 hx1,
      index_some rhs 1#usize y1 hy1,
      index_some lhs 2#usize x2 hx2,
      index_some rhs 2#usize y2 hy2,
      index_some lhs 3#usize x3 hx3,
      index_some rhs 3#usize y3 hy3,
      bind_ok, ha0, hb0, hc0, hd0, he0, ho0, ha1, hb1, hc1, hd1, he1, ho1, ha2, hb2, hc2, hd2, he2,
        ho2, ha3, hb3, hc3, hd3, he3, ho3,
      he01, ho01, he23, ho23, hde, hdd, hr]
  · rw [(hrl i hi).2]
    obtain ⟨j, hj, h | h⟩ := acc_split de dd i hi
    · obtain ⟨rfl, hac⟩ := h
      rw [hac, (hsum j hj).1]
    · obtain ⟨rfl, hac⟩ := h
      rw [hac, (hsum j hj).2]

open p3_monty_31_avx2 in
/-- `partial_monty_red_unsigned_to_signed(x)`: the high lane of 64-bit element `j` is
`montyHi` of that element. -/
theorem partial_red {MPAVX2 : Type} (inst : x86_64_avx2.packing.MontyParametersAVX2 MPAVX2)
    (P M x : V) (p mu : ℕ) (hPP : inst.PACKED_P = .ok P) (hP : ∀ i < 8, ln P i = p)
    (hMM : inst.PACKED_MU = .ok M) (hM : ∀ i < 8, ln M i = mu) :
    ∃ d, x86_64_avx2.packing.partial_monty_red_unsigned_to_signed inst x = .ok d ∧
      ∀ j < 4, ln d (2 * j + 1) = montyHi p mu (w x j) := by
  obtain ⟨q, hq, hql⟩ := mul_epu32 x M
  obtain ⟨qp, hqp, hqpl⟩ := mul_epu32 q P
  obtain ⟨d, hd, hdl⟩ := sub_epi32 x qp
  refine ⟨d, ?_, fun j hj => ?_⟩
  · unfold x86_64_avx2.packing.partial_monty_red_unsigned_to_signed
    rw [hMM, bind_ok, hq, bind_ok, hPP, bind_ok, hqp, bind_ok, hd]
  · rw [hdl _ (by omega), (hqpl j hj).2, (hql j hj).1, hM _ (by omega), hP _ (by omega),
      montyHi, ← ln_lo, ← ln_hi]

open p3_monty_31_avx2 in
/-- `dot_product_2(lhs, rhs)`, on values whose lanes are canonical: lane `i` is the canonical
`r` with `r · 2^32 ≡ Σ_k lhs[k]_i · rhs[k]_i (mod p)`. -/
theorem dot2 {PMP LHS RHS : Type} (inst : data_traits.PackedMontyParameters PMP)
    (iL : x86_64_avx2.packing.IntoM256 LHS PMP) (iR : x86_64_avx2.packing.IntoM256 RHS PMP)
    (lhs : Std.Array LHS 2#usize) (rhs : Std.Array RHS 2#usize) (el er : ℕ → ℕ → ℕ) (p mu : ℕ)
    (hv : Prm inst p mu)
    (hl : ∀ k < 2, ∃ x, lhs.val[k]? = some x ∧ IntoSpec iL x (el k))
    (hr : ∀ k < 2, ∃ y, rhs.val[k]? = some y ∧ IntoSpec iR y (er k))
    (hb : ∀ k < 2, ∀ i < 8, el k i < p ∧ er k i < p) :
    ∃ r, x86_64_avx2.packing.dot_product_2 inst iL iR lhs rhs = .ok r ∧
      ∀ i < 8, ln r i < p ∧ ln r i * 2 ^ 32 % p = dsum el er 2 i % p := by
  obtain ⟨P, hPP, hP⟩ := hv.P
  obtain ⟨M, hMM, hM⟩ := hv.M
  have hp := hv.lt
  have hp0 := hv.pos
  obtain ⟨x0, hx0, s0⟩ := hl 0 (by norm_num)
  obtain ⟨y0, hy0, t0⟩ := hr 0 (by norm_num)
  obtain ⟨a0, ha0, ha0l⟩ := s0.vec
  obtain ⟨c0, hc0, hc0l⟩ := s0.shifted
  obtain ⟨b0, hb0, hb0l⟩ := t0.vec
  obtain ⟨d0, hd0, hd0l⟩ := t0.shifted
  obtain ⟨e0, he0, he0l⟩ := mul_w a0 b0
  obtain ⟨o0, ho0, ho0l⟩ := mul_w c0 d0
  obtain ⟨x1, hx1, s1⟩ := hl 1 (by norm_num)
  obtain ⟨y1, hy1, t1⟩ := hr 1 (by norm_num)
  obtain ⟨a1, ha1, ha1l⟩ := s1.vec
  obtain ⟨c1, hc1, hc1l⟩ := s1.shifted
  obtain ⟨b1, hb1, hb1l⟩ := t1.vec
  obtain ⟨d1, hd1, hd1l⟩ := t1.shifted
  obtain ⟨e1, he1, he1l⟩ := mul_w a1 b1
  obtain ⟨o1, ho1, ho1l⟩ := mul_w c1 d1
  obtain ⟨de, hde, hdel⟩ := add_epi64 e0 e1
  obtain ⟨dd, hdd, hddl⟩ := add_epi64 o0 o1
  have hsum : ∀ j < 4, w de j = dsum el er 2 (2 * j) ∧ w dd j = dsum el er 2 (2 * j + 1) := by
    intro j hj
    have := prod_lt _ _ p hp (hb 0 (by norm_num) (2 * j) (by omega)).1 (hb 0 (by norm_num) (2 * j) (by omega)).2
    have := prod_lt _ _ p hp (hb 1 (by norm_num) (2 * j) (by omega)).1 (hb 1 (by norm_num) (2 * j) (by omega)).2
    have := prod_lt _ _ p hp (hb 0 (by norm_num) (2 * j + 1) (by omega)).1
      (hb 0 (by norm_num) (2 * j + 1) (by omega)).2
    have := prod_lt _ _ p hp (hb 1 (by norm_num) (2 * j + 1) (by omega)).1
      (hb 1 (by norm_num) (2 * j + 1) (by omega)).2
    simp only [dsum, Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    rw [hdel j hj, he0l j hj, he1l j hj, hddl j hj, ho0l j hj, ho1l j hj,
      ha0l j hj, ha1l j hj, hb0l j hj, hb1l j hj, hc0l j hj, hc1l j hj, hd0l j hj, hd1l j hj]
    omega
  have wS : ∀ i < 8, dsum el er 2 i < 2 ^ 32 * p := fun i hi => by
    have := dsum_wide el er 2 i p 2 hp hp0 le_rfl (by norm_num) (fun k hk => hb k (by omega) i hi)
    omega
  obtain ⟨re, hre, hrel⟩ := partial_red _ P M de p mu hPP hP hMM hM
  obtain ⟨ro, hro, hrol⟩ := partial_red _ P M dd p mu hPP hP hMM hM
  obtain ⟨t, ht, htl⟩ := blend_evn_odd re ro
  obtain ⟨c, hc, hcl⟩ := add_epi32 t P
  obtain ⟨r, hr, hrl⟩ := min_epu32 t c
  have htv : ∀ i < 8, ln t i = montyHi p mu (dsum el er 2 i) := by
    intro i hi
    rw [htl i hi]
    by_cases h : i % 2 = 0
    · simp only [h, ite_true]
      rw [← ln_hi, hrel _ (by omega), (hsum _ (by omega)).1, show 2 * (i / 2) = i by omega]
    · simp only [h, ite_false]
      rw [← ln_hi, hrol _ (by omega), (hsum _ (by omega)).2, show 2 * (i / 2) + 1 = i by omega]
  refine ⟨r, ?_, fun i hi => ?_⟩
  · unfold x86_64_avx2.packing.dot_product_2 x86_64_avx2.packing.red_signed_to_canonical
    simp only [index_some lhs 0#usize x0 hx0,
      index_some rhs 0#usize y0 hy0,
      index_some lhs 1#usize x1 hx1,
      index_some rhs 1#usize y1 hy1,
      bind_ok, ha0, hb0, hc0, hd0, he0, ho0, ha1, hb1, hc1, hd1, he1, ho1,
      hde, hdd, hre, hro, ht, hPP, hc, hr]
  · rw [hrl i hi, hcl i hi, hP i hi, htv i hi]
    exact montyHi_red_wide p mu _ hp hp0 hv.inv (wS i hi)


/-! ## As field elements -/

/-- A Montgomery dot product read in `ZMod P`: if `r · 2^32 ≡ Σ a_k b_k (mod P)`, then `r`
stands for the sum of the products of what the `a_k` and `b_k` stand for. -/
theorem monty_dot {ι : Type} (P r : ℕ) (hodd : P % 2 = 1) (a b : ι → ℕ) (S : Finset ι)
    (h : r * 2 ^ 32 % P = (∑ k ∈ S, a k * b k) % P) :
    (r : ZMod P) * (2 ^ 32 : ZMod P)⁻¹ =
      ∑ k ∈ S, ((a k : ZMod P) * (2 ^ 32 : ZMod P)⁻¹) * ((b k : ZMod P) * (2 ^ 32 : ZMod P)⁻¹) := by
  have hu : (2 ^ 32 : ZMod P) * (2 ^ 32 : ZMod P)⁻¹ = 1 :=
    ZMod.mul_inv_of_unit _ (Plonky3Lean.Proofs.Monty31.two_pow_32_isUnit hodd)
  have hc : ((r * 2 ^ 32 : ℕ) : ZMod P) = ((∑ k ∈ S, a k * b k : ℕ) : ZMod P) :=
    (ZMod.natCast_eq_natCast_iff' _ _ _).mpr h
  push_cast at hc
  have hs : ∑ k ∈ S, ((a k : ZMod P) * (2 ^ 32 : ZMod P)⁻¹) *
      ((b k : ZMod P) * (2 ^ 32 : ZMod P)⁻¹) =
      (∑ k ∈ S, (a k : ZMod P) * (b k : ZMod P)) *
        ((2 ^ 32 : ZMod P)⁻¹ * (2 ^ 32 : ZMod P)⁻¹) := by
    rw [Finset.sum_mul]; refine Finset.sum_congr rfl fun k _ => ?_; ring
  rw [hs, ← hc]
  linear_combination (-(r : ZMod P) * (2 ^ 32 : ZMod P)⁻¹) * hu

/-! ## Packed operands -/

section packed
open p3_monty_31_avx2
variable {PMP : Type} {inst : data_traits.PackedMontyParameters PMP} {p mu : Std.U32}

theorem prm_of_valid (hv : Valid inst p mu) : Prm inst p.val mu.val :=
  ⟨hv.monty.lt, valid_p_pos hv, hv.monty.inv, valid_lnP hv, valid_lnM hv⟩

theorem packed_spec {iI : x86_64_avx2.packing.IntoM256 (PackedAvx2 PMP) PMP}
    (hI : IsPackedInto iI inst) (x : PackedAvx2 PMP) : IntoSpec iI x (fun i => ln (vec x) i) := by
  have hv : iI.as_m256i x = .ok (vec x) := by
    rw [hI.as_m256i]
    unfold x86_64_avx2.packing.PackedMontyField31AVX2.Insts.P3_monty_31X86_64_avx2PackingIntoM256.as_m256i
    exact to_vector_eq inst x
  obtain ⟨s, hs, hsl⟩ := movehdup_epi32 (vec x)
  refine ⟨⟨vec x, hv, fun j _ => rfl⟩, ⟨s, ?_, fun j hj => ?_⟩⟩
  · rw [hI.as_shifted_m256i]
    unfold x86_64_avx2.packing.IntoM256.as_shifted_m256i.default
    rw [hv, bind_ok, hs]
  · rw [hsl _ (by omega), show 2 * (2 * j / 2) + 1 = 2 * j + 1 by omega]

/-- The lanes of an array's packed values, `0` past its end. -/
def lanesOf {N : Std.Usize} (a : Std.Array (PackedAvx2 PMP) N) (k i : ℕ) : ℕ :=
  match a.val[k]? with
  | some x => ln (vec x) i
  | none => 0

theorem lanesOf_spec {iI : x86_64_avx2.packing.IntoM256 (PackedAvx2 PMP) PMP}
    (hI : IsPackedInto iI inst) {N : Std.Usize} (a : Std.Array (PackedAvx2 PMP) N) :
    ∀ k < N.val, ∃ x, a.val[k]? = some x ∧ IntoSpec iI x (lanesOf a k) := by
  intro k hk
  have hk' : k < a.val.length := by simpa using hk
  refine ⟨a.val[k], List.getElem?_eq_getElem hk', ?_⟩
  have : lanesOf a k = fun i => ln (vec a.val[k]) i := by
    funext i; simp [lanesOf, List.getElem?_eq_getElem hk']
  rw [this]; exact packed_spec hI _

theorem lanesOf_lt {N : Std.Usize} (a : Std.Array (PackedAvx2 PMP) N)
    (ha : ∀ k : Fin N.val, Canonical p.val (a.val[k.val]'(by simp))) :
    ∀ k < N.val, ∀ i < 8, lanesOf a k i < p.val := by
  intro k hk i hi
  have hk' : k < a.val.length := by simpa using hk
  simp only [lanesOf, List.getElem?_eq_getElem hk']
  exact canonical_ln (ha ⟨k, hk⟩) i hi

theorem dsum_lanesOf {N : Std.Usize} (a b : Std.Array (PackedAvx2 PMP) N) (i : Fin 8) :
    dsum (lanesOf a) (lanesOf b) N.val i =
      ∑ k : Fin N.val, (toVector (a.val[k.val]'(by simp)))[i].value.val *
        (toVector (b.val[k.val]'(by simp)))[i].value.val := by
  unfold dsum
  rw [Finset.sum_range]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hka : k.val < a.val.length := by simp
  have hkb : k.val < b.val.length := by simp
  simp only [lanesOf, List.getElem?_eq_getElem hka, List.getElem?_eq_getElem hkb, ln_vec]

/-- What the packed dot products below share: from a kernel's lane-wise statement on
`lanesOf`, the statement on the packed values. -/
theorem packed_dot {N : Std.Usize} {m : RustM V}
    {iI : x86_64_avx2.packing.IntoM256 (PackedAvx2 PMP) PMP}
    (hI : IsPackedInto iI inst) (lhs rhs : Std.Array (PackedAvx2 PMP) N)
    (hl : ∀ k : Fin N.val, Canonical p.val (lhs.val[k.val]'(by simp)))
    (hr : ∀ k : Fin N.val, Canonical p.val (rhs.val[k.val]'(by simp)))
    (kern : ∀ el er : ℕ → ℕ → ℕ, (∀ k < N.val, ∃ x, lhs.val[k]? = some x ∧ IntoSpec iI x (el k)) →
      (∀ k < N.val, ∃ y, rhs.val[k]? = some y ∧ IntoSpec iI y (er k)) →
      (∀ k < N.val, ∀ i < 8, el k i < p.val ∧ er k i < p.val) →
      ∃ r, m = .ok r ∧ ∀ i < 8,
        ln r i < p.val ∧ ln r i * 2 ^ 32 % p.val = dsum el er N.val i % p.val) :
    ∃ v, m = .ok v ∧ FromVectorSafe p.val v ∧ ∀ i : Fin 8,
      (lane v i).val * 2 ^ 32 % p.val =
        (∑ k : Fin N.val, (toVector (lhs.val[k.val]'(by simp)))[i].value.val *
          (toVector (rhs.val[k.val]'(by simp)))[i].value.val) % p.val := by
  obtain ⟨r, hm,
    hrl⟩ := kern (lanesOf lhs) (lanesOf rhs) (lanesOf_spec hI lhs) (lanesOf_spec hI rhs)
    (fun k hk i hi => ⟨lanesOf_lt lhs hl k hk i hi, lanesOf_lt rhs hr k hk i hi⟩)
  refine ⟨r, hm, fun i => (hrl i i.isLt).1, fun i => ?_⟩
  rw [← dsum_lanesOf]
  exact (hrl i i.isLt).2

end packed

open p3_monty_31_avx2 in
/-- `dot_product_2` on packed values with canonical lanes: lane `i` of its result is the
canonical `r` with `r · 2^32 ≡ Σ_k lhs[k]_i · rhs[k]_i (mod p)`. -/
theorem dot2.packed {PMP : Type} {inst : data_traits.PackedMontyParameters PMP} {p mu : Std.U32}
    {iI : x86_64_avx2.packing.IntoM256 (PackedAvx2 PMP) PMP} (hv : Valid inst p mu)
    (hI : IsPackedInto iI inst) (lhs rhs : Std.Array (PackedAvx2 PMP) 2#usize)
    (hl : ∀ k : Fin 2, Canonical p.val (lhs.val[k.val]'(by simp; omega)))
    (hr : ∀ k : Fin 2, Canonical p.val (rhs.val[k.val]'(by simp; omega))) :
    ∃ v, x86_64_avx2.packing.dot_product_2 inst iI iI lhs rhs = .ok v ∧ FromVectorSafe p.val v ∧
      ∀ i : Fin 8, (lane v i).val * 2 ^ 32 % p.val =
        (∑ k : Fin 2, (toVector (lhs.val[k.val]'(by simp; omega)))[i].value.val *
          (toVector (rhs.val[k.val]'(by simp; omega)))[i].value.val) % p.val :=
  packed_dot hI lhs rhs hl hr fun el er hl' hr' hb =>
    dot2 inst iI iI lhs rhs el er p.val mu.val (prm_of_valid hv) hl' hr' hb

open p3_monty_31_avx2 in
/-- `dot_product_4` on packed values with canonical lanes: lane `i` of its result is the
canonical `r` with `r · 2^32 ≡ Σ_k lhs[k]_i · rhs[k]_i (mod p)`. -/
theorem dot4.packed {PMP : Type} {inst : data_traits.PackedMontyParameters PMP} {p mu : Std.U32}
    {iI : x86_64_avx2.packing.IntoM256 (PackedAvx2 PMP) PMP} (hv : Valid inst p mu)
    (hI : IsPackedInto iI inst) (lhs rhs : Std.Array (PackedAvx2 PMP) 4#usize)
    (hl : ∀ k : Fin 4, Canonical p.val (lhs.val[k.val]'(by simp)))
    (hr : ∀ k : Fin 4, Canonical p.val (rhs.val[k.val]'(by simp))) :
    ∃ v, x86_64_avx2.packing.dot_product_4 inst iI iI lhs rhs = .ok v ∧ FromVectorSafe p.val v ∧
      ∀ i : Fin 8, (lane v i).val * 2 ^ 32 % p.val =
        (∑ k : Fin 4, (toVector (lhs.val[k.val]'(by simp)))[i].value.val *
          (toVector (rhs.val[k.val]'(by simp)))[i].value.val) % p.val :=
  packed_dot hI lhs rhs hl hr fun el er hl' hr' hb =>
    dot4 inst iI iI lhs rhs el er p.val mu.val (prm_of_valid hv) hl' hr' hb

open p3_monty_31_avx2 in
/-- `dot_product_5` on packed values with canonical lanes: lane `i` of its result is the
canonical `r` with `r · 2^32 ≡ Σ_k lhs[k]_i · rhs[k]_i (mod p)`. -/
theorem dot5.packed {PMP : Type} {inst : data_traits.PackedMontyParameters PMP} {p mu : Std.U32}
    {iI : x86_64_avx2.packing.IntoM256 (PackedAvx2 PMP) PMP} (hv : Valid inst p mu)
    (hI : IsPackedInto iI inst) (lhs rhs : Std.Array (PackedAvx2 PMP) 5#usize)
    (hl : ∀ k : Fin 5, Canonical p.val (lhs.val[k.val]'(by simp)))
    (hr : ∀ k : Fin 5, Canonical p.val (rhs.val[k.val]'(by simp))) :
    ∃ v, x86_64_avx2.packing.dot_product_5 inst iI iI lhs rhs = .ok v ∧ FromVectorSafe p.val v ∧
      ∀ i : Fin 8, (lane v i).val * 2 ^ 32 % p.val =
        (∑ k : Fin 5, (toVector (lhs.val[k.val]'(by simp)))[i].value.val *
          (toVector (rhs.val[k.val]'(by simp)))[i].value.val) % p.val :=
  packed_dot hI lhs rhs hl hr fun el er hl' hr' hb =>
    dot5 inst iI iI lhs rhs el er p.val mu.val (prm_of_valid hv) hl' hr' hb

open p3_monty_31_avx2 in
/-- `dot_product_6` on packed values with canonical lanes: lane `i` of its result is the
canonical `r` with `r · 2^32 ≡ Σ_k lhs[k]_i · rhs[k]_i (mod p)`. -/
theorem dot6.packed {PMP : Type} {inst : data_traits.PackedMontyParameters PMP} {p mu : Std.U32}
    {iI : x86_64_avx2.packing.IntoM256 (PackedAvx2 PMP) PMP} (hv : Valid inst p mu)
    (hI : IsPackedInto iI inst) (lhs rhs : Std.Array (PackedAvx2 PMP) 6#usize)
    (hl : ∀ k : Fin 6, Canonical p.val (lhs.val[k.val]'(by simp)))
    (hr : ∀ k : Fin 6, Canonical p.val (rhs.val[k.val]'(by simp))) :
    ∃ v, x86_64_avx2.packing.dot_product_6 inst iI iI lhs rhs = .ok v ∧ FromVectorSafe p.val v ∧
      ∀ i : Fin 8, (lane v i).val * 2 ^ 32 % p.val =
        (∑ k : Fin 6, (toVector (lhs.val[k.val]'(by simp)))[i].value.val *
          (toVector (rhs.val[k.val]'(by simp)))[i].value.val) % p.val :=
  packed_dot hI lhs rhs hl hr fun el er hl' hr' hb =>
    dot6 inst iI iI lhs rhs el er p.val mu.val (prm_of_valid hv) hl' hr' hb

open p3_monty_31_avx2 in
/-- `dot_product_7` on packed values with canonical lanes: lane `i` of its result is the
canonical `r` with `r · 2^32 ≡ Σ_k lhs[k]_i · rhs[k]_i (mod p)`. -/
theorem dot7.packed {PMP : Type} {inst : data_traits.PackedMontyParameters PMP} {p mu : Std.U32}
    {iI : x86_64_avx2.packing.IntoM256 (PackedAvx2 PMP) PMP} (hv : Valid inst p mu)
    (hI : IsPackedInto iI inst) (lhs rhs : Std.Array (PackedAvx2 PMP) 7#usize)
    (hl : ∀ k : Fin 7, Canonical p.val (lhs.val[k.val]'(by simp)))
    (hr : ∀ k : Fin 7, Canonical p.val (rhs.val[k.val]'(by simp))) :
    ∃ v, x86_64_avx2.packing.dot_product_7 inst iI iI lhs rhs = .ok v ∧ FromVectorSafe p.val v ∧
      ∀ i : Fin 8, (lane v i).val * 2 ^ 32 % p.val =
        (∑ k : Fin 7, (toVector (lhs.val[k.val]'(by simp)))[i].value.val *
          (toVector (rhs.val[k.val]'(by simp)))[i].value.val) % p.val :=
  packed_dot hI lhs rhs hl hr fun el er hl' hr' hb =>
    dot7 inst iI iI lhs rhs el er p.val mu.val (prm_of_valid hv) hl' hr' hb

open p3_monty_31_avx2 in
/-- `dot_product_8` on packed values with canonical lanes: lane `i` of its result is the
canonical `r` with `r · 2^32 ≡ Σ_k lhs[k]_i · rhs[k]_i (mod p)`. -/
theorem dot8.packed {PMP : Type} {inst : data_traits.PackedMontyParameters PMP} {p mu : Std.U32}
    {iI : x86_64_avx2.packing.IntoM256 (PackedAvx2 PMP) PMP} (hv : Valid inst p mu)
    (hI : IsPackedInto iI inst) (lhs rhs : Std.Array (PackedAvx2 PMP) 8#usize)
    (hl : ∀ k : Fin 8, Canonical p.val (lhs.val[k.val]'(by simp)))
    (hr : ∀ k : Fin 8, Canonical p.val (rhs.val[k.val]'(by simp))) :
    ∃ v, x86_64_avx2.packing.dot_product_8 inst iI iI lhs rhs = .ok v ∧ FromVectorSafe p.val v ∧
      ∀ i : Fin 8, (lane v i).val * 2 ^ 32 % p.val =
        (∑ k : Fin 8, (toVector (lhs.val[k.val]'(by simp)))[i].value.val *
          (toVector (rhs.val[k.val]'(by simp)))[i].value.val) % p.val :=
  packed_dot hI lhs rhs hl hr fun el er hl' hr' hb =>
    dot8 inst iI iI lhs rhs el er p.val mu.val (prm_of_valid hv) hl' hr' hb

end Plonky3Lean.Proofs.Avx2
