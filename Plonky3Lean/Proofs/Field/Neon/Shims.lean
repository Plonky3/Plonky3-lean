module

public import P3ArchShims
public import Plonky3Lean.Proofs.Field.Avx2.Shims

@[expose] public section

/-!
# NEON: the intrinsic models, lane by lane

Each model in `P3ArchShims` (the extraction of `arch/`) that `PackedMontyField31Neon`'s
arithmetic reaches, as a function of its input lanes: it never fails, and lane `i` of its
result is a stated function of lane `i` of its inputs. Unsigned lanes are read as natural
numbers, `ln v i = v[i].val`, and signed lanes as integers, `sn v i = v[i].val`.

The models write their result one lane per loop iteration into an array of zeros; `lane_loop`
runs such a loop to the end. It is AVX2's (`Plonky3Lean.Proofs.Avx2.lane_loop`) at width 4,
for lanes of any type.
-/

open Aeneas Aeneas.Std CoreModels
open Plonky3Lean.Lib
open Plonky3Lean.Proofs.Avx2 (usz_lt4 usz_not_lt4)
open Plonky3Lean.Proofs.Avx2.shims (usz_succ4 ite_ok)

namespace Plonky3Lean.Proofs.Neon

/-- A 128-bit vector as the models have it: four lanes. -/
abbrev A (α : Type) := Std.Array α 4#usize

/-- `uint32x4_t`. -/
abbrev U := A Std.U32

/-- `int32x4_t`. -/
abbrev S := A Std.I32

/-- Lane `i` of an unsigned vector, as a natural number. -/
def ln (v : U) (i : ℕ) : ℕ := (v.val[i]!).val

/-- Lane `i` of a signed vector, as an integer. -/
def sn (v : S) (i : ℕ) : ℤ := (v.val[i]!).val

theorem A.len {α : Type} (v : A α) : v.val.length = 4 := by simp

/-! ## Small indices -/

theorem index_usz {α : Type} [Inhabited α] (a : A α) {k : ℕ} (hk : k < 4) :
    Aeneas.Std.Array.index_usize a (usz k) = .ok a.val[k]! := by
  have hk' : k < a.val.length := by rw [A.len]; exact hk
  simp [Aeneas.Std.Array.index_usize, Aeneas.Std.Array.getElem?_Usize_eq,
    usz_val (show k < 2 ^ 32 by omega), List.getElem?_eq_getElem hk',
    List.getElem!_eq_getElem?_getD]

theorem update_usz {α : Type} (a : A α) {k : ℕ} (hk : k < 4) (x : α) :
    Aeneas.Std.Array.update a (usz k) x = .ok (a.set (usz k) x) := by
  have hk' : k < a.val.length := by rw [A.len]; exact hk
  simp [Aeneas.Std.Array.update, Aeneas.Std.Array.set, Aeneas.Std.Array.getElem?_Usize_eq,
    usz_val (show k < 2 ^ 32 by omega), List.getElem?_eq_getElem hk']

/-! ## Lane loops -/

/-- The array after `k` iterations of a lane loop from `d`: lanes below `k` hold `f`. -/
def fill {α : Type} (f : ℕ → α) (d : A α) : ℕ → A α
  | 0 => d
  | k + 1 => (fill f d k).set (usz k) (f k)

theorem fill_lane {α : Type} [Inhabited α] (f : ℕ → α) (d : A α) :
    ∀ k ≤ 4, ∀ i < k, (fill f d k).val[i]! = f i := by
  intro k
  induction k with
  | zero => intro _ i hi; omega
  | succ k ih =>
    intro hk i hi
    simp only [fill, Aeneas.Std.Array.set_val_eq, usz_val (show k < 2 ^ 32 by omega)]
    have hlen : (fill f d k).val.length = 4 := A.len _
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h | h
    · rw [← ih (by omega) i h]
      simp only [List.getElem!_eq_getElem?_getD, List.getElem?_set_ne (show k ≠ i by omega)]
    · subst h
      rw [List.getElem!_eq_getElem?_getD, List.getElem?_set_self (by rw [hlen]; omega),
        Option.getD_some]

/-- A loop that, from `j = 0`, writes `f j` into lane `j` and stops at `j = 4`, returns the
array of the `f j`. -/
theorem lane_loop {α S : Type} [Inhabited α] (body : S → RustM (ControlFlow S (A α)))
    (mk : A α → Std.Usize → S) (f : ℕ → α) (d : A α)
    (hstep : ∀ (e : A α) (k : ℕ), k < 4 →
      body (mk e (usz k)) = .ok (.cont (mk (e.set (usz k) (f k)) (usz (k + 1)))))
    (hdone : ∀ e, body (mk e (usz 4)) = .ok (.done e)) :
    ∃ r, loop body (mk d 0#usize) = .ok r ∧ ∀ i < 4, r.val[i]! = f i :=
  ⟨fill f d 4,
    loop_of_steps body (fun k => mk (fill f d k) (usz k)) 4 (fill f d 4)
      (fun k hk => hstep _ k hk) (hdone _),
    fill_lane f d 4 le_rfl⟩

/-- The zero arrays the models start from. -/
theorem zeros : ∃ d : U, core.array.repeat 4#usize core.U32.Insts.CoreCloneClone 0#u32 = .ok d :=
  let ⟨d, hd, _⟩ := array_repeat_eq 4#usize core.U32.Insts.CoreCloneClone (fun _ => rfl) 0#u32
  ⟨d, hd⟩

theorem szeros : ∃ d : S, core.array.repeat 4#usize core.I32.Insts.CoreCloneClone 0#i32 = .ok d :=
  let ⟨d, hd, _⟩ := array_repeat_eq 4#usize core.I32.Insts.CoreCloneClone (fun _ => rfl) 0#i32
  ⟨d, hd⟩

/-! ## Scalar facts -/

theorem i32_bounds (x : Std.I32) : -2 ^ 31 ≤ x.val ∧ x.val < 2 ^ 31 := by
  have h1 := x.hmin; have h2 := x.hmax
  simp only [IScalarTy.I32_numBits_eq] at h1 h2
  omega

/-- A value in `[-2^31, 2^31)` is its own balanced residue mod `2^32`. -/
theorem bmod32_self {v : ℤ} (h1 : -2 ^ 31 ≤ v) (h2 : v < 2 ^ 31) : Int.bmod v (2 ^ 32) = v :=
  Int.bmod_eq_of_le (by norm_num; omega) (by norm_num; omega)

/-- An `i32` widened to `i64` keeps its value. -/
theorem cast_i32_i64_val (x : Std.I32) : (IScalar.cast .I64 x).val = x.val := by
  rw [IScalar.cast_val_eq]
  have := i32_bounds x
  simp only [IScalarTy.I64_numBits_eq, IScalarTy.I32_numBits_eq]
  rw [show Min.min 64 32 = 32 from rfl]
  exact bmod32_self (by omega) (by omega)

/-- `x >>> s` for an `i64` and a non-negative `i32` shift below 64: floor division. -/
theorem sshr_i64_eq (x : Std.I64) (s : Std.I32) (h0 : 0 ≤ s.val) (h : s.toNat < 64) :
    ∃ z : Std.I64, (x >>> s : RustM Std.I64) = .ok z ∧ z.val = x.val / 2 ^ s.toNat := by
  refine ⟨⟨x.bv.sshiftRight s.toNat⟩, ?_, ?_⟩
  · show IScalar.shiftRight_IScalar x s = _
    simp only [IScalar.shiftRight_IScalar, IScalar.shiftRight, IScalarTy.I64_numBits_eq,
      ge_iff_le, h0, ite_true, h]
  · show (x.bv.sshiftRight s.toNat).toInt = _
    rw [BitVec.toInt_sshiftRight, Int.shiftRight_eq_div_pow]
    rfl

/-- `u >>> s` for a `u64` and a non-negative `i32` shift below 64: floor division. -/
theorem ushr_u64_eq (x : Std.U64) (s : Std.I32) (h0 : 0 ≤ s.val) (h : s.toNat < 64) :
    ∃ z : Std.U64, (x >>> s : RustM Std.U64) = .ok z ∧ z.val = x.val / 2 ^ s.toNat := by
  refine ⟨⟨x.bv.ushiftRight s.toNat⟩, ?_, ?_⟩
  · show UScalar.shiftRight_IScalar x s = _
    simp only [UScalar.shiftRight_IScalar, UScalar.shiftRight, UScalarTy.U64_numBits_eq,
      ge_iff_le, h0, ite_true, h]
  · show (x.bv.ushiftRight s.toNat).toNat = x.bv.toNat / 2 ^ s.toNat
    rw [BitVec.ushiftRight_eq, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

/-- An `i64` value that fits an `i32`, narrowed, keeps its value. -/
theorem cast_i64_i32_val' (x : Std.I64) (h1 : -2 ^ 31 ≤ x.val) (h2 : x.val < 2 ^ 31) :
    (IScalar.cast .I32 x).val = x.val :=
  cast_i64_i32_val x (by omega) (by omega)

/-- `SignedSatQ(i, 32)` of a value in range is that value. -/
theorem signed_sat_q32_eq (x : Std.I64) (h1 : -2 ^ 31 ≤ x.val) (h2 : x.val < 2 ^ 31) :
    ∃ z : Std.I32, p3_arch_shims.aarch64.neon.signed_sat_q32 x = .ok z ∧ z.val = x.val := by
  have hmax : (IScalar.cast .I64 core.num.I32.MAX).val = 2 ^ 31 - 1 := by
    rw [cast_i32_i64_val]; rfl
  have hmin : (IScalar.cast .I64 core.num.I32.MIN).val = -2 ^ 31 := by
    rw [cast_i32_i64_val]; rfl
  refine ⟨IScalar.cast .I32 x, ?_, cast_i64_i32_val' x h1 h2⟩
  unfold p3_arch_shims.aarch64.neon.signed_sat_q32
  have hgt : ¬ (x > IScalar.cast .I64 core.num.I32.MAX) := by
    rw [gt_iff_lt, IScalar.lt_equiv, hmax]; omega
  have hlt : ¬ (x < IScalar.cast .I64 core.num.I32.MIN) := by
    rw [IScalar.lt_equiv, hmin]; omega
  simp only [lift_eq, bind_ok, hgt, hlt, ite_false]

/-- The `u32` with value `v`, for `v < 2^32`. -/
def u32of (v : ℕ) : Std.U32 := ⟨BitVec.ofNat 32 v⟩

theorem u32of_val {v : ℕ} (h : v < 2 ^ 32) : (u32of v).val = v := by
  show (BitVec.ofNat 32 v).toNat = v
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

/-- The `i32` with value `v`, for `-2^31 ≤ v < 2^31`. -/
def i32of (v : ℤ) : Std.I32 := ⟨BitVec.ofInt 32 v⟩

theorem i32of_val {v : ℤ} (h1 : -2 ^ 31 ≤ v) (h2 : v < 2 ^ 31) : (i32of v).val = v := by
  show (BitVec.ofInt 32 v).toInt = v
  rw [BitVec.toInt_ofInt]
  exact bmod32_self (by omega) (by omega)

/-! ## The models -/

namespace shims
open p3_arch_shims.aarch64.neon

/-- `vaddq_u32`: lane-wise `a + b mod 2^32`. -/
theorem vaddq_u32 (a b : U) : ∃ r, p3_arch_shims.aarch64.neon.vaddq_u32 a b = .ok r ∧
    ∀ i < 4, ln r i = (ln a i + ln b i) % 2 ^ 32 := by
  obtain ⟨d, hd⟩ := zeros
  obtain ⟨r, hr, hl⟩ := lane_loop (fun (s : U × U × U × Std.Usize) =>
      vaddq_u32_loop.body s.1 s.2.1 s.2.2.1 s.2.2.2)
    (fun e j => (a, b, e, j)) (fun i => a.val[i]!.wrapping_add b.val[i]!) d
    (fun e k hk => by
      simp only [vaddq_u32_loop.body, usz_lt4 hk, ite_true, index_usz _ hk, bind_ok,
        CoreModels.core.num.U32.wrapping_add, rust_primitives.arithmetic.wrapping_add_u32,
        update_usz _ hk, usz_succ4 hk])
    (fun e => by simp only [vaddq_u32_loop.body, usz_not_lt4, ite_false])
  refine ⟨r, ?_, fun i hi => ?_⟩
  · unfold p3_arch_shims.aarch64.neon.vaddq_u32 vaddq_u32_loop
    rw [hd, bind_ok, hr, bind_ok]
  · simp only [ln, hl i hi, U32.wrapping_add_val_eq, size_u32]

/-- `vsubq_u32`: lane-wise `a - b mod 2^32`. -/
theorem vsubq_u32 (a b : U) : ∃ r, p3_arch_shims.aarch64.neon.vsubq_u32 a b = .ok r ∧
    ∀ i < 4, ln r i = (ln a i + (2 ^ 32 - ln b i)) % 2 ^ 32 := by
  obtain ⟨d, hd⟩ := zeros
  obtain ⟨r, hr, hl⟩ := lane_loop (fun (s : U × U × U × Std.Usize) =>
      vsubq_u32_loop.body s.1 s.2.1 s.2.2.1 s.2.2.2)
    (fun e j => (a, b, e, j)) (fun i => a.val[i]!.wrapping_sub b.val[i]!) d
    (fun e k hk => by
      simp only [vsubq_u32_loop.body, usz_lt4 hk, ite_true, index_usz _ hk, bind_ok,
        CoreModels.core.num.U32.wrapping_sub, rust_primitives.arithmetic.wrapping_sub_u32,
        update_usz _ hk, usz_succ4 hk])
    (fun e => by simp only [vsubq_u32_loop.body, usz_not_lt4, ite_false])
  refine ⟨r, ?_, fun i hi => ?_⟩
  · unfold p3_arch_shims.aarch64.neon.vsubq_u32 vsubq_u32_loop
    rw [hd, bind_ok, hr, bind_ok]
  · rw [ln, hl i hi, U32.wrapping_sub_val_eq, size_u32]; rfl

/-- `vminq_u32`: lane-wise unsigned minimum. -/
theorem vminq_u32 (a b : U) : ∃ r, p3_arch_shims.aarch64.neon.vminq_u32 a b = .ok r ∧
    ∀ i < 4, ln r i = min (ln a i) (ln b i) := by
  obtain ⟨d, hd⟩ := zeros
  obtain ⟨r, hr, hl⟩ := lane_loop (fun (s : U × U × U × Std.Usize) =>
      vminq_u32_loop.body s.1 s.2.1 s.2.2.1 s.2.2.2)
    (fun e j => (a, b, e, j)) (fun i => if a.val[i]! ≤ b.val[i]! then a.val[i]! else b.val[i]!) d
    (fun e k hk => by
      simp only [vminq_u32_loop.body, usz_lt4 hk, ite_true, index_usz _ hk, bind_ok,
        ite_ok, update_usz _ hk, usz_succ4 hk])
    (fun e => by simp only [vminq_u32_loop.body, usz_not_lt4, ite_false])
  refine ⟨r, ?_, fun i hi => ?_⟩
  · unfold p3_arch_shims.aarch64.neon.vminq_u32 vminq_u32_loop
    rw [hd, bind_ok, hr, bind_ok]
  · simp only [ln, hl i hi]
    split
    · rename_i h; rw [Nat.min_eq_left (UScalar.le_equiv _ _ |>.mp h)]
    · rename_i h; rw [Nat.min_eq_right (by have := (UScalar.le_equiv _ _).not.mp h; omega)]

/-- `vandq_u32`: lane-wise bitwise and. -/
theorem vandq_u32 (a b : U) : ∃ r, p3_arch_shims.aarch64.neon.vandq_u32 a b = .ok r ∧
    ∀ i < 4, ln r i = ln a i &&& ln b i := by
  obtain ⟨d, hd⟩ := zeros
  obtain ⟨r, hr, hl⟩ := lane_loop (fun (s : U × U × U × Std.Usize) =>
      vandq_u32_loop.body s.1 s.2.1 s.2.2.1 s.2.2.2)
    (fun e j => (a, b, e, j)) (fun i => a.val[i]! &&& b.val[i]!) d
    (fun e k hk => by
      simp only [vandq_u32_loop.body, usz_lt4 hk, ite_true, index_usz _ hk, bind_ok,
        lift_eq, update_usz _ hk, usz_succ4 hk])
    (fun e => by simp only [vandq_u32_loop.body, usz_not_lt4, ite_false])
  refine ⟨r, ?_, fun i hi => ?_⟩
  · unfold p3_arch_shims.aarch64.neon.vandq_u32 vandq_u32_loop
    rw [hd, bind_ok, hr, bind_ok]
  · simp only [ln, hl i hi, UScalar.val_and]

/-- `vbicq_u32`: lane-wise `a AND NOT b`, on the bits. -/
theorem vbicq_u32 (a b : U) : ∃ r, p3_arch_shims.aarch64.neon.vbicq_u32 a b = .ok r ∧
    ∀ i < 4, (r.val[i]!).bv = (a.val[i]!).bv &&& ~~~(b.val[i]!).bv := by
  obtain ⟨d, hd⟩ := zeros
  obtain ⟨r, hr, hl⟩ := lane_loop (fun (s : U × U × U × Std.Usize) =>
      vbicq_u32_loop.body s.1 s.2.1 s.2.2.1 s.2.2.2)
    (fun e j => (a, b, e, j)) (fun i => a.val[i]! &&& ~~~ b.val[i]!) d
    (fun e k hk => by
      simp only [vbicq_u32_loop.body, usz_lt4 hk, ite_true, index_usz _ hk, bind_ok,
        lift_eq, update_usz _ hk, usz_succ4 hk])
    (fun e => by simp only [vbicq_u32_loop.body, usz_not_lt4, ite_false])
  refine ⟨r, ?_, fun i hi => ?_⟩
  · unfold p3_arch_shims.aarch64.neon.vbicq_u32 vbicq_u32_loop
    rw [hd, bind_ok, hr, bind_ok]
  · rw [hl i hi]; rfl

/-- `vtstq_u32`: all ones where `a` and `b` share a set bit, zero elsewhere. -/
theorem vtstq_u32 (a b : U) : ∃ r, p3_arch_shims.aarch64.neon.vtstq_u32 a b = .ok r ∧
    ∀ i < 4, ln r i = if ln a i &&& ln b i = 0 then 0 else 2 ^ 32 - 1 := by
  obtain ⟨d, hd⟩ := zeros
  obtain ⟨r, hr, hl⟩ := lane_loop (fun (s : U × U × U × Std.Usize) =>
      vtstq_u32_loop.body s.1 s.2.1 s.2.2.1 s.2.2.2)
    (fun e j => (a, b, e, j))
    (fun i => if a.val[i]! &&& b.val[i]! != 0#u32 then core.num.U32.MAX else 0#u32) d
    (fun e k hk => by
      simp only [vtstq_u32_loop.body, usz_lt4 hk, ite_true, index_usz _ hk, bind_ok,
        lift_eq, ite_ok, update_usz _ hk, usz_succ4 hk])
    (fun e => by simp only [vtstq_u32_loop.body, usz_not_lt4, ite_false])
  refine ⟨r, ?_, fun i hi => ?_⟩
  · unfold p3_arch_shims.aarch64.neon.vtstq_u32 vtstq_u32_loop
    rw [hd, bind_ok, hr, bind_ok]
  · simp only [ln, hl i hi]
    by_cases h : (a.val[i]!).val &&& (b.val[i]!).val = 0
    · have h0 : a.val[i]! &&& b.val[i]! = 0#u32 := by
        apply UScalar.eq_of_val_eq; rw [UScalar.val_and, h]; rfl
      simp only [h0, bne_self_eq_false, Bool.false_eq_true, ite_false, h, ite_true]; rfl
    · have h0 : (a.val[i]! &&& b.val[i]! != 0#u32) = true := by
        rw [bne_iff_ne]; intro he; apply h; rw [← UScalar.val_and, he]; rfl
      simp only [h0, ite_true, h, ite_false]; rfl

/-- `vceqzq_u32`: all ones where `a` is zero, zero elsewhere. -/
theorem vceqzq_u32 (a : U) : ∃ r, p3_arch_shims.aarch64.neon.vceqzq_u32 a = .ok r ∧
    ∀ i < 4, ln r i = if ln a i = 0 then 2 ^ 32 - 1 else 0 := by
  obtain ⟨d, hd⟩ := zeros
  obtain ⟨r, hr, hl⟩ := lane_loop (fun (s : U × U × Std.Usize) =>
      vceqzq_u32_loop.body s.1 s.2.1 s.2.2)
    (fun e j => (a, e, j)) (fun i => if a.val[i]! = 0#u32 then core.num.U32.MAX else 0#u32) d
    (fun e k hk => by
      simp only [vceqzq_u32_loop.body, usz_lt4 hk, ite_true, index_usz _ hk, bind_ok,
        ite_ok, update_usz _ hk, usz_succ4 hk])
    (fun e => by simp only [vceqzq_u32_loop.body, usz_not_lt4, ite_false])
  refine ⟨r, ?_, fun i hi => ?_⟩
  · unfold p3_arch_shims.aarch64.neon.vceqzq_u32 vceqzq_u32_loop
    rw [hd, bind_ok, hr, bind_ok]
  · simp only [ln, hl i hi]
    by_cases h : (a.val[i]!).val = 0
    · have h0 : a.val[i]! = 0#u32 := UScalar.eq_of_val_eq (by rw [h]; rfl)
      simp only [h0, ite_true]; rfl
    · have h0 : a.val[i]! ≠ 0#u32 := fun he => h (by rw [he]; rfl)
      simp only [h0, ite_false, h]; rfl

/-- `vdupq_n_u32`: every lane is `x`. -/
theorem vdupq_n_u32 (x : Std.U32) : ∃ r, p3_arch_shims.aarch64.neon.vdupq_n_u32 x = .ok r ∧
    ∀ i < 4, ln r i = x.val := by
  obtain ⟨d, hd⟩ := zeros
  obtain ⟨r, hr, hl⟩ := lane_loop (fun (s : U × Std.Usize) =>
      vdupq_n_u32_loop.body x s.1 s.2)
    (fun e j => (e, j)) (fun _ => x) d
    (fun e k hk => by
      simp only [vdupq_n_u32_loop.body, usz_lt4 hk, ite_true, bind_ok, update_usz _ hk,
        usz_succ4 hk])
    (fun e => by simp only [vdupq_n_u32_loop.body, usz_not_lt4, ite_false])
  refine ⟨r, ?_, fun i hi => ?_⟩
  · unfold p3_arch_shims.aarch64.neon.vdupq_n_u32 vdupq_n_u32_loop
    rw [hd, bind_ok, hr, bind_ok]
  · rw [ln, hl i hi]

/-- `vhaddq_u32`: lane-wise `(a + b) / 2`, without overflow. -/
theorem vhaddq_u32 (a b : U) : ∃ r, p3_arch_shims.aarch64.neon.vhaddq_u32 a b = .ok r ∧
    ∀ i < 4, ln r i = (ln a i + ln b i) / 2 := by
  obtain ⟨d, hd⟩ := zeros
  obtain ⟨r, hr, hl⟩ := lane_loop (fun (s : U × U × U × Std.Usize) =>
      vhaddq_u32_loop.body s.1 s.2.1 s.2.2.1 s.2.2.2)
    (fun e j => (a, b, e, j)) (fun i => u32of ((ln a i + ln b i) / 2)) d
    (fun e k hk => by
      have hx := u32_lt (a.val[k]!); have hy := u32_lt (b.val[k]!)
      obtain ⟨s, hs, hsv, -⟩ := spec_imp_exists (UScalar.add_bv_spec (x := UScalar.cast .U64 a.val[k]!)
        (y := UScalar.cast .U64 b.val[k]!)
        (by rw [cast_u32_u64_val, cast_u32_u64_val]; simp only [UScalar.max,
          UScalarTy.U64_numBits_eq]; omega))
      rw [cast_u32_u64_val, cast_u32_u64_val] at hsv
      obtain ⟨w, hw, hwv⟩ := ushr_u64_eq s 1#i32 (by decide) (by decide)
      have hcast : UScalar.cast .U32 w = u32of ((ln a k + ln b k) / 2) := by
        apply UScalar.eq_of_val_eq
        rw [cast_u64_u32_val, hwv, hsv, show (2 : ℕ) ^ (1#i32 : Std.I32).toNat = 2 from rfl,
          u32of_val (by simp only [ln]; omega), Nat.mod_eq_of_lt (by omega)]
        rfl
      simp only [vhaddq_u32_loop.body, usz_lt4 hk, ite_true, index_usz _ hk, bind_ok, lift_eq,
        hs, hw, hcast, update_usz _ hk, usz_succ4 hk])
    (fun e => by simp only [vhaddq_u32_loop.body, usz_not_lt4, ite_false])
  refine ⟨r, ?_, fun i hi => ?_⟩
  · unfold p3_arch_shims.aarch64.neon.vhaddq_u32 vhaddq_u32_loop
    rw [hd, bind_ok, hr, bind_ok]
  · have hx := u32_lt (a.val[i]!); have hy := u32_lt (b.val[i]!)
    rw [ln, hl i hi, u32of_val (by simp only [ln]; omega)]

/-- `vmlsq_u32`: lane-wise `a - b * c mod 2^32`. -/
theorem vmlsq_u32 (a b c : U) : ∃ r, p3_arch_shims.aarch64.neon.vmlsq_u32 a b c = .ok r ∧
    ∀ i < 4, ln r i = (ln a i + (2 ^ 32 - ln b i * ln c i % 2 ^ 32)) % 2 ^ 32 := by
  obtain ⟨d, hd⟩ := zeros
  obtain ⟨r, hr, hl⟩ := lane_loop (fun (s : U × U × U × U × Std.Usize) =>
      vmlsq_u32_loop.body s.1 s.2.1 s.2.2.1 s.2.2.2.1 s.2.2.2.2)
    (fun e j => (a, b, c, e, j))
    (fun i => a.val[i]!.wrapping_sub (b.val[i]!.wrapping_mul c.val[i]!)) d
    (fun e k hk => by
      simp only [vmlsq_u32_loop.body, usz_lt4 hk, ite_true, index_usz _ hk, bind_ok,
        CoreModels.core.num.U32.wrapping_mul, rust_primitives.arithmetic.wrapping_mul_u32,
        CoreModels.core.num.U32.wrapping_sub, rust_primitives.arithmetic.wrapping_sub_u32,
        update_usz _ hk, usz_succ4 hk])
    (fun e => by simp only [vmlsq_u32_loop.body, usz_not_lt4, ite_false])
  refine ⟨r, ?_, fun i hi => ?_⟩
  · unfold p3_arch_shims.aarch64.neon.vmlsq_u32 vmlsq_u32_loop
    rw [hd, bind_ok, hr, bind_ok]
  · rw [ln, hl i hi, U32.wrapping_sub_val_eq, U32.wrapping_mul_val_eq, size_u32]; rfl

/-- `vreinterpretq_s32_u32`: the same bits, read as `i32`s. -/
theorem vreinterpretq_s32_u32 (a : U) :
    ∃ r, p3_arch_shims.aarch64.neon.vreinterpretq_s32_u32 a = .ok r ∧
      ∀ i < 4, sn r i = Int.bmod (ln a i) (2 ^ 32) := by
  obtain ⟨d, hd⟩ := szeros
  obtain ⟨r, hr, hl⟩ := lane_loop (fun (s : U × S × Std.Usize) =>
      vreinterpretq_s32_u32_loop.body s.1 s.2.1 s.2.2)
    (fun e j => (a, e, j)) (fun i => UScalar.hcast .I32 a.val[i]!) d
    (fun e k hk => by
      simp only [vreinterpretq_s32_u32_loop.body, usz_lt4 hk, ite_true, index_usz _ hk, bind_ok,
        lift_eq, update_usz _ hk, usz_succ4 hk])
    (fun e => by simp only [vreinterpretq_s32_u32_loop.body, usz_not_lt4, ite_false])
  refine ⟨r, ?_, fun i hi => ?_⟩
  · unfold p3_arch_shims.aarch64.neon.vreinterpretq_s32_u32 vreinterpretq_s32_u32_loop
    rw [hd, bind_ok, hr, bind_ok]
  · rw [sn, hl i hi, UScalar.hcast_val_eq]; rfl

/-- `vreinterpretq_u32_s32`: the same bits, read as `u32`s. -/
theorem vreinterpretq_u32_s32 (a : S) :
    ∃ r, p3_arch_shims.aarch64.neon.vreinterpretq_u32_s32 a = .ok r ∧
      ∀ i < 4, (ln r i : ℤ) = sn a i % 2 ^ 32 := by
  obtain ⟨d, hd⟩ := zeros
  obtain ⟨r, hr, hl⟩ := lane_loop (fun (s : S × U × Std.Usize) =>
      vreinterpretq_u32_s32_loop.body s.1 s.2.1 s.2.2)
    (fun e j => (a, e, j)) (fun i => IScalar.hcast .U32 a.val[i]!) d
    (fun e k hk => by
      simp only [vreinterpretq_u32_s32_loop.body, usz_lt4 hk, ite_true, index_usz _ hk, bind_ok,
        lift_eq, update_usz _ hk, usz_succ4 hk])
    (fun e => by simp only [vreinterpretq_u32_s32_loop.body, usz_not_lt4, ite_false])
  refine ⟨r, ?_, fun i hi => ?_⟩
  · unfold p3_arch_shims.aarch64.neon.vreinterpretq_u32_s32 vreinterpretq_u32_s32_loop
    rw [hd, bind_ok, hr, bind_ok]
  · rw [ln, hl i hi, IScalar.hcast_val_eq, UScalarTy.U32_numBits_eq,
      Int.toNat_of_nonneg (Int.emod_nonneg _ (by norm_num))]
    rfl

/-- `vmulq_s32`: lane-wise product, wrapped to 32 bits. -/
theorem vmulq_s32 (a b : S) : ∃ r, p3_arch_shims.aarch64.neon.vmulq_s32 a b = .ok r ∧
    ∀ i < 4, sn r i = Int.bmod (sn a i * sn b i) (2 ^ 32) := by
  obtain ⟨d, hd⟩ := szeros
  obtain ⟨r, hr, hl⟩ := lane_loop (fun (s : S × S × S × Std.Usize) =>
      vmulq_s32_loop.body s.1 s.2.1 s.2.2.1 s.2.2.2)
    (fun e j => (a, b, e, j)) (fun i => I32.wrapping_mul a.val[i]! b.val[i]!) d
    (fun e k hk => by
      simp only [vmulq_s32_loop.body, usz_lt4 hk, ite_true, index_usz _ hk, bind_ok,
        CoreModels.core.num.I32.wrapping_mul, rust_primitives.arithmetic.wrapping_mul_i32,
        update_usz _ hk, usz_succ4 hk])
    (fun e => by simp only [vmulq_s32_loop.body, usz_not_lt4, ite_false])
  refine ⟨r, ?_, fun i hi => ?_⟩
  · unfold p3_arch_shims.aarch64.neon.vmulq_s32 vmulq_s32_loop
    rw [hd, bind_ok, hr, bind_ok]
  · rw [sn, hl i hi, sn, sn]
    show (a.val[i]!.bv * b.val[i]!.bv).toInt = _
    rw [BitVec.toInt_mul]
    rfl

/-- `vqdmulhq_s32`, where the product is below `2^62` (so that it does not saturate): lane-wise
`floor(2 a b / 2^32) = floor(a b / 2^31)`. -/
theorem vqdmulhq_s32 (a b : S) (h : ∀ i < 4, sn a i * sn b i < 2 ^ 62) :
    ∃ r, p3_arch_shims.aarch64.neon.vqdmulhq_s32 a b = .ok r ∧
      ∀ i < 4, sn r i = sn a i * sn b i / 2 ^ 31 := by
  obtain ⟨d, hd⟩ := szeros
  have hrange : ∀ k < 4, -2 ^ 31 ≤ sn a k * sn b k / 2 ^ 31 ∧
      sn a k * sn b k / 2 ^ 31 < 2 ^ 31 := by
    intro k hk
    have hx := i32_bounds (a.val[k]!); have hy := i32_bounds (b.val[k]!)
    have hlo : -(2 ^ 62) ≤ sn a k * sn b k := by simp only [sn]; nlinarith
    have := h k hk
    omega
  obtain ⟨r, hr, hl⟩ := lane_loop (fun (s : S × S × S × Std.Usize) =>
      vqdmulhq_s32_loop.body s.1 s.2.1 s.2.2.1 s.2.2.2)
    (fun e j => (a, b, e, j)) (fun i => i32of (sn a i * sn b i / 2 ^ 31)) d
    (fun e k hk => by
      have hx := i32_bounds (a.val[k]!); have hy := i32_bounds (b.val[k]!)
      have hlo : -(2 ^ 62) ≤ (a.val[k]!).val * (b.val[k]!).val := by nlinarith
      have hhi : (a.val[k]!).val * (b.val[k]!).val ≤ 2 ^ 62 := by nlinarith
      obtain ⟨z, hz, hzv⟩ := spec_imp_exists (IScalar.mul_spec
        (x := IScalar.cast .I64 a.val[k]!) (y := IScalar.cast .I64 b.val[k]!)
        (by rw [cast_i32_i64_val, cast_i32_i64_val]; simp only [IScalar.min,
          IScalarTy.I64_numBits_eq]; omega)
        (by rw [cast_i32_i64_val, cast_i32_i64_val]; simp only [IScalar.max,
          IScalarTy.I64_numBits_eq]; omega))
      rw [cast_i32_i64_val, cast_i32_i64_val] at hzv
      obtain ⟨w, hw, hwv⟩ := sshr_i64_eq z 31#i32 (by decide) (by decide)
      have hwv' : w.val = sn a k * sn b k / 2 ^ 31 := by rw [hwv, hzv]; rfl
      obtain ⟨s, hs, hsv⟩ := signed_sat_q32_eq w (by rw [hwv']; exact (hrange k hk).1)
        (by rw [hwv']; exact (hrange k hk).2)
      have hseq : s = i32of (sn a k * sn b k / 2 ^ 31) := by
        apply IScalar.eq_of_val_eq
        rw [hsv, hwv', i32of_val (hrange k hk).1 (hrange k hk).2]
      simp only [vqdmulhq_s32_loop.body, usz_lt4 hk, ite_true, index_usz _ hk, bind_ok, lift_eq,
        hz, hw, hs, hseq, update_usz _ hk, usz_succ4 hk])
    (fun e => by simp only [vqdmulhq_s32_loop.body, usz_not_lt4, ite_false])
  refine ⟨r, ?_, fun i hi => ?_⟩
  · unfold p3_arch_shims.aarch64.neon.vqdmulhq_s32 vqdmulhq_s32_loop
    rw [hd, bind_ok, hr, bind_ok]
  · rw [sn, hl i hi, i32of_val (hrange i hi).1 (hrange i hi).2]

/-- `vhsubq_s32`: lane-wise `floor((a - b) / 2)`, without overflow. -/
theorem vhsubq_s32 (a b : S) : ∃ r, p3_arch_shims.aarch64.neon.vhsubq_s32 a b = .ok r ∧
    ∀ i < 4, sn r i = (sn a i - sn b i) / 2 := by
  obtain ⟨d, hd⟩ := szeros
  have hrange : ∀ k, -2 ^ 31 ≤ (sn a k - sn b k) / 2 ∧ (sn a k - sn b k) / 2 < 2 ^ 31 := by
    intro k
    have hx := i32_bounds (a.val[k]!); have hy := i32_bounds (b.val[k]!)
    simp only [sn]; omega
  obtain ⟨r, hr, hl⟩ := lane_loop (fun (s : S × S × S × Std.Usize) =>
      vhsubq_s32_loop.body s.1 s.2.1 s.2.2.1 s.2.2.2)
    (fun e j => (a, b, e, j)) (fun i => i32of ((sn a i - sn b i) / 2)) d
    (fun e k hk => by
      have hx := i32_bounds (a.val[k]!); have hy := i32_bounds (b.val[k]!)
      obtain ⟨z, hz, hzv, -⟩ := spec_imp_exists (IScalar.sub_bv_spec
        (x := IScalar.cast .I64 a.val[k]!) (y := IScalar.cast .I64 b.val[k]!)
        (by rw [cast_i32_i64_val, cast_i32_i64_val]; simp only [IScalar.min,
          IScalarTy.I64_numBits_eq]; omega)
        (by rw [cast_i32_i64_val, cast_i32_i64_val]; simp only [IScalar.max,
          IScalarTy.I64_numBits_eq]; omega))
      rw [cast_i32_i64_val, cast_i32_i64_val] at hzv
      obtain ⟨w, hw, hwv⟩ := sshr_i64_eq z 1#i32 (by decide) (by decide)
      have hwv' : w.val = (sn a k - sn b k) / 2 := by rw [hwv, hzv]; rfl
      have hseq : IScalar.cast .I32 w = i32of ((sn a k - sn b k) / 2) := by
        apply IScalar.eq_of_val_eq
        rw [cast_i64_i32_val' w (by rw [hwv']; exact (hrange k).1)
          (by rw [hwv']; exact (hrange k).2), hwv', i32of_val (hrange k).1 (hrange k).2]
      simp only [vhsubq_s32_loop.body, usz_lt4 hk, ite_true, index_usz _ hk, bind_ok, lift_eq,
        hz, hw, hseq, update_usz _ hk, usz_succ4 hk])
    (fun e => by simp only [vhsubq_s32_loop.body, usz_not_lt4, ite_false])
  refine ⟨r, ?_, fun i hi => ?_⟩
  · unfold p3_arch_shims.aarch64.neon.vhsubq_s32 vhsubq_s32_loop
    rw [hd, bind_ok, hr, bind_ok]
  · rw [sn, hl i hi, i32of_val (hrange i).1 (hrange i).2]

/-- `vcltq_s32`: all ones where `a < b` as signed integers, zero elsewhere. -/
theorem vcltq_s32 (a b : S) : ∃ r, p3_arch_shims.aarch64.neon.vcltq_s32 a b = .ok r ∧
    ∀ i < 4, ln r i = if sn a i < sn b i then 2 ^ 32 - 1 else 0 := by
  obtain ⟨d, hd⟩ := zeros
  obtain ⟨r, hr, hl⟩ := lane_loop (fun (s : S × S × U × Std.Usize) =>
      vcltq_s32_loop.body s.1 s.2.1 s.2.2.1 s.2.2.2)
    (fun e j => (a, b, e, j)) (fun i => if b.val[i]! > a.val[i]! then core.num.U32.MAX else 0#u32) d
    (fun e k hk => by
      simp only [vcltq_s32_loop.body, usz_lt4 hk, ite_true, index_usz _ hk, bind_ok,
        ite_ok, update_usz _ hk, usz_succ4 hk])
    (fun e => by simp only [vcltq_s32_loop.body, usz_not_lt4, ite_false])
  refine ⟨r, ?_, fun i hi => ?_⟩
  · unfold p3_arch_shims.aarch64.neon.vcltq_s32 vcltq_s32_loop
    rw [hd, bind_ok, hr, bind_ok]
  · rw [ln, hl i hi]
    have hlt : (b.val[i]! > a.val[i]!) ↔ sn a i < sn b i := by
      rw [gt_iff_lt, IScalar.lt_equiv]; rfl
    by_cases h : sn a i < sn b i
    · simp only [hlt.mpr h, h, ite_true]; rfl
    · simp only [show ¬ (b.val[i]! > a.val[i]!) from fun h' => h (hlt.mp h'), h, ite_false]
      rfl

end shims

end Plonky3Lean.Proofs.Neon
