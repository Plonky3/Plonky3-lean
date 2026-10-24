module

public import P3ArchShims
public import Plonky3Lean.Lib.Array
public import Plonky3Lean.Lib.Range
public import Plonky3Lean.Lib.Scalar
public import Plonky3Lean.Lib.Scalar.Bits
public import Plonky3Lean.Lib.Scalar.Signed
public import Mathlib.Tactic.IntervalCases

@[expose] public section

/-!
# AVX2: the intrinsic models, lane by lane

Each model in `P3ArchShims` (the extraction of `arch/`) that `PackedMontyField31AVX2`'s
arithmetic reaches, as a function of its input lanes: it never fails, and lane `i` of its
result is a stated function of lane `i` (or, for the 64-bit and shuffling intrinsics, of
named lanes) of its inputs. Lanes are read as natural numbers, `ln v i = v[i].val`.

The models write their result one lane (or one 64-bit pair of lanes) per loop iteration
into an array of zeros; `lane_loop` and `pair_loop` run such a loop to the end.
-/

open Aeneas Aeneas.Std CoreModels
open Plonky3Lean.Lib

namespace Plonky3Lean.Proofs.Avx2

/-- An `__m256i` (or `__m256`) as the models have it: eight `u32` lanes. -/
abbrev V := Std.Array Std.U32 8#usize

/-- Lane `i` of `v`, as a natural number. -/
def ln (v : V) (i : ℕ) : ℕ := (v.val[i]!).val

theorem V.len (v : V) : v.val.length = 8 := by simp

/-! ## Small indices -/

theorem index_usz (a : V) {k : ℕ} (hk : k < 8) :
    Aeneas.Std.Array.index_usize a (usz k) = .ok a.val[k]! := by
  have hk' : k < a.val.length := by rw [V.len]; exact hk
  simp [Aeneas.Std.Array.index_usize, Aeneas.Std.Array.getElem?_Usize_eq,
    usz_val (show k < 2 ^ 32 by omega), List.getElem?_eq_getElem hk',
    List.getElem!_eq_getElem?_getD]

theorem update_usz (a : V) {k : ℕ} (hk : k < 8) (x : Std.U32) :
    Aeneas.Std.Array.update a (usz k) x = .ok (a.set (usz k) x) := by
  have hk' : k < a.val.length := by rw [V.len]; exact hk
  simp [Aeneas.Std.Array.update, Aeneas.Std.Array.set, Aeneas.Std.Array.getElem?_Usize_eq,
    usz_val (show k < 2 ^ 32 by omega), List.getElem?_eq_getElem hk']

theorem usz_succ {k : ℕ} (hk : k < 8) :
    (usz k + 1#usize : RustM Std.Usize) = .ok (usz (k + 1)) := by
  rw [show (1#usize) = usz 1 from eq_usz (by norm_num) (by simp)]
  exact usz_add (by omega)

theorem usz_lt8 {k : ℕ} (hk : k < 8) : (usz k < 8#usize) = True := by
  rw [show (8#usize) = usz 8 from eq_usz (by norm_num) (by simp), eq_iff_iff, iff_true]
  exact (usz_lt_iff (by omega) (by norm_num)).mpr hk

theorem usz_not_lt8 : (usz 8 < 8#usize) = False := by
  rw [show (8#usize) = usz 8 from eq_usz (by norm_num) (by simp), eq_iff_iff, iff_false]
  exact lt_irrefl (usz _)

theorem usz_lt4 {k : ℕ} (hk : k < 4) : (usz k < 4#usize) = True := by
  rw [show (4#usize) = usz 4 from eq_usz (by norm_num) (by simp), eq_iff_iff, iff_true]
  exact (usz_lt_iff (by omega) (by norm_num)).mpr hk

theorem usz_not_lt4 : (usz 4 < 4#usize) = False := by
  rw [show (4#usize) = usz 4 from eq_usz (by norm_num) (by simp), eq_iff_iff, iff_false]
  exact lt_irrefl (usz _)

/-! ## Lane loops -/

/-- The array after `k` iterations of a lane loop from `d`: lanes below `k` hold `f`. -/
def fill (f : ℕ → Std.U32) (d : V) : ℕ → V
  | 0 => d
  | k + 1 => (fill f d k).set (usz k) (f k)

theorem fill_lane (f : ℕ → Std.U32) (d : V) :
    ∀ k ≤ 8, ∀ i < k, (fill f d k).val[i]! = f i := by
  intro k
  induction k with
  | zero => intro _ i hi; omega
  | succ k ih =>
    intro hk i hi
    simp only [fill, Aeneas.Std.Array.set_val_eq, usz_val (show k < 2 ^ 32 by omega)]
    have hlen : (fill f d k).val.length = 8 := V.len _
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h | h
    · rw [← ih (by omega) i h]
      simp only [List.getElem!_eq_getElem?_getD, List.getElem?_set_ne (show k ≠ i by omega)]
    · subst h
      rw [List.getElem!_eq_getElem?_getD, List.getElem?_set_self (by rw [hlen]; omega),
        Option.getD_some]

/-- A loop that, from `j = 0`, writes `f j` into lane `j` and stops at `j = 8`, returns the
array of the `f j`. -/
theorem lane_loop {S : Type} (body : S → RustM (ControlFlow S V)) (mk : V → Std.Usize → S)
    (f : ℕ → Std.U32) (d : V)
    (hstep : ∀ (e : V) (k : ℕ), k < 8 →
      body (mk e (usz k)) = .ok (.cont (mk (e.set (usz k) (f k)) (usz (k + 1)))))
    (hdone : ∀ e, body (mk e (usz 8)) = .ok (.done e)) :
    ∃ r, loop body (mk d 0#usize) = .ok r ∧ ∀ i < 8, r.val[i]! = f i :=
  ⟨fill f d 8,
    loop_of_steps body (fun k => mk (fill f d k) (usz k)) 8 (fill f d 8)
      (fun k hk => hstep _ k hk) (hdone _),
    fill_lane f d 8 le_rfl⟩

/-- The array after `k` iterations of a pair loop from `d`: for `j < k`, lanes `2j` and
`2j + 1` hold `lo j` and `hi j`. -/
def fill2 (lo hi : ℕ → Std.U32) (d : V) : ℕ → V
  | 0 => d
  | k + 1 => ((fill2 lo hi d k).set (usz (2 * k)) (lo k)).set (usz (2 * k + 1)) (hi k)

theorem fill2_lane (lo hi : ℕ → Std.U32) (d : V) :
    ∀ k ≤ 4, ∀ j < k, (fill2 lo hi d k).val[2 * j]! = lo j ∧
      (fill2 lo hi d k).val[2 * j + 1]! = hi j := by
  intro k
  induction k with
  | zero => intro _ j hj; omega
  | succ k ih =>
    intro hk j hj
    simp only [fill2, Aeneas.Std.Array.set_val_eq, usz_val (show 2 * k < 2 ^ 32 by omega),
      usz_val (show 2 * k + 1 < 2 ^ 32 by omega)]
    have hlen : (fill2 lo hi d k).val.length = 8 := V.len _
    simp only [List.getElem!_eq_getElem?_getD]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with h | h
    · have := ih (by omega) j h
      simp only [List.getElem!_eq_getElem?_getD] at this
      rw [List.getElem?_set_ne (show 2 * k + 1 ≠ 2 * j by omega),
        List.getElem?_set_ne (show 2 * k ≠ 2 * j by omega),
        List.getElem?_set_ne (show 2 * k + 1 ≠ 2 * j + 1 by omega),
        List.getElem?_set_ne (show 2 * k ≠ 2 * j + 1 by omega)]
      exact this
    · subst h
      rw [List.getElem?_set_ne (show 2 * j + 1 ≠ 2 * j by omega),
        List.getElem?_set_self (by rw [hlen]; omega),
        List.getElem?_set_self (by rw [List.length_set, hlen]; omega)]
      exact ⟨rfl, rfl⟩

/-- A loop that, from `k = 0`, writes `lo k` and `hi k` into lanes `2k` and `2k + 1` and stops
at `k = 4`. -/
theorem pair_loop {S : Type} (body : S → RustM (ControlFlow S V)) (mk : V → Std.Usize → S)
    (lo hi : ℕ → Std.U32) (d : V)
    (hstep : ∀ (e : V) (k : ℕ), k < 4 →
      body (mk e (usz k)) = .ok (.cont (mk ((e.set (usz (2 * k)) (lo k)).set
        (usz (2 * k + 1)) (hi k)) (usz (k + 1)))))
    (hdone : ∀ e, body (mk e (usz 4)) = .ok (.done e)) :
    ∃ r, loop body (mk d 0#usize) = .ok r ∧
      ∀ j < 4, r.val[2 * j]! = lo j ∧ r.val[2 * j + 1]! = hi j :=
  ⟨fill2 lo hi d 4,
    loop_of_steps body (fun k => mk (fill2 lo hi d k) (usz k)) 4 (fill2 lo hi d 4)
      (fun k hk => hstep _ k hk) (hdone _),
    fill2_lane lo hi d 4 le_rfl⟩

/-- The zero array every model starts from. -/
theorem zeros : ∃ d : V, core.array.repeat 8#usize core.U32.Insts.CoreCloneClone 0#u32 = .ok d :=
  let ⟨d, hd, _⟩ := array_repeat_eq 8#usize core.U32.Insts.CoreCloneClone (fun _ => rfl) 0#u32
  ⟨d, hd⟩

/-! ## The models -/

namespace shims
open p3_arch_shims.x86_64.avx2

/-- `_mm256_add_epi32`: lane-wise `a + b mod 2^32`. -/
theorem add_epi32 (a b : V) : ∃ r, _mm256_add_epi32 a b = .ok r ∧
    ∀ i < 8, ln r i = (ln a i + ln b i) % 2 ^ 32 := by
  obtain ⟨d, hd⟩ := zeros
  obtain ⟨r, hr, hl⟩ := lane_loop (fun (s : V × V × V × Std.Usize) =>
      _mm256_add_epi32_loop.body s.1 s.2.1 s.2.2.1 s.2.2.2)
    (fun e j => (a, b, e, j)) (fun i => a.val[i]!.wrapping_add b.val[i]!) d
    (fun e k hk => by
      simp only [_mm256_add_epi32_loop.body, usz_lt8 hk, ite_true, index_usz _ hk, bind_ok,
        CoreModels.core.num.U32.wrapping_add, rust_primitives.arithmetic.wrapping_add_u32,
        update_usz _ hk, usz_succ hk])
    (fun e => by simp only [_mm256_add_epi32_loop.body, usz_not_lt8, ite_false])
  refine ⟨r, ?_, fun i hi => ?_⟩
  · unfold _mm256_add_epi32 _mm256_add_epi32_loop
    rw [hd, bind_ok]
    rw [hr, bind_ok]
  · simp only [ln, hl i hi, U32.wrapping_add_val_eq, size_u32]

/-- `_mm256_sub_epi32`: lane-wise `a - b mod 2^32`. -/
theorem sub_epi32 (a b : V) : ∃ r, _mm256_sub_epi32 a b = .ok r ∧
    ∀ i < 8, ln r i = (ln a i + (2 ^ 32 - ln b i)) % 2 ^ 32 := by
  obtain ⟨d, hd⟩ := zeros
  obtain ⟨r, hr, hl⟩ := lane_loop (fun (s : V × V × V × Std.Usize) =>
      _mm256_sub_epi32_loop.body s.1 s.2.1 s.2.2.1 s.2.2.2)
    (fun e j => (a, b, e, j)) (fun i => a.val[i]!.wrapping_sub b.val[i]!) d
    (fun e k hk => by
      simp only [_mm256_sub_epi32_loop.body, usz_lt8 hk, ite_true, index_usz _ hk, bind_ok,
        CoreModels.core.num.U32.wrapping_sub, rust_primitives.arithmetic.wrapping_sub_u32,
        update_usz _ hk, usz_succ hk])
    (fun e => by simp only [_mm256_sub_epi32_loop.body, usz_not_lt8, ite_false])
  refine ⟨r, ?_, fun i hi => ?_⟩
  · unfold _mm256_sub_epi32 _mm256_sub_epi32_loop
    rw [hd, bind_ok, hr, bind_ok]
  · rw [ln, hl i hi, U32.wrapping_sub_val_eq, size_u32]; rfl

theorem ite_ok {α : Type} (c : Prop) [Decidable c] (x y : α) :
    (if c then RustM.ok x else RustM.ok y) = RustM.ok (if c then x else y) := by
  split <;> rfl

/-- `_mm256_min_epu32`: lane-wise unsigned minimum. -/
theorem min_epu32 (a b : V) : ∃ r, _mm256_min_epu32 a b = .ok r ∧
    ∀ i < 8, ln r i = min (ln a i) (ln b i) := by
  obtain ⟨d, hd⟩ := zeros
  obtain ⟨r, hr, hl⟩ := lane_loop (fun (s : V × V × V × Std.Usize) =>
      _mm256_min_epu32_loop.body s.1 s.2.1 s.2.2.1 s.2.2.2)
    (fun e j => (a, b, e, j)) (fun i => if a.val[i]! ≤ b.val[i]! then a.val[i]! else b.val[i]!) d
    (fun e k hk => by
      simp only [_mm256_min_epu32_loop.body, usz_lt8 hk, ite_true, index_usz _ hk, bind_ok,
        ite_ok, update_usz _ hk, usz_succ hk])
    (fun e => by simp only [_mm256_min_epu32_loop.body, usz_not_lt8, ite_false])
  refine ⟨r, ?_, fun i hi => ?_⟩
  · unfold _mm256_min_epu32 _mm256_min_epu32_loop
    rw [hd, bind_ok, hr, bind_ok]
  · simp only [ln, hl i hi]
    split
    · rename_i h; rw [Nat.min_eq_left (UScalar.le_equiv _ _ |>.mp h)]
    · rename_i h; rw [Nat.min_eq_right (by have := (UScalar.le_equiv _ _).not.mp h; omega)]

/-- `_mm256_and_si256`: lane-wise bitwise and. -/
theorem and_si256 (a b : V) : ∃ r, _mm256_and_si256 a b = .ok r ∧
    ∀ i < 8, ln r i = ln a i &&& ln b i := by
  obtain ⟨d, hd⟩ := zeros
  obtain ⟨r, hr, hl⟩ := lane_loop (fun (s : V × V × V × Std.Usize) =>
      _mm256_and_si256_loop.body s.1 s.2.1 s.2.2.1 s.2.2.2)
    (fun e j => (a, b, e, j)) (fun i => a.val[i]! &&& b.val[i]!) d
    (fun e k hk => by
      simp only [_mm256_and_si256_loop.body, usz_lt8 hk, ite_true, index_usz _ hk, bind_ok,
        lift_eq, update_usz _ hk, usz_succ hk])
    (fun e => by simp only [_mm256_and_si256_loop.body, usz_not_lt8, ite_false])
  refine ⟨r, ?_, fun i hi => ?_⟩
  · unfold _mm256_and_si256 _mm256_and_si256_loop
    rw [hd, bind_ok, hr, bind_ok]
  · simp only [ln, hl i hi, UScalar.val_and]

/-- `_mm256_sign_epi32`, for `b` whose lanes are non-negative as `i32`s: lane `i` is `0` where
`b`'s lane is `0`, and `a`'s lane elsewhere. -/
theorem sign_epi32 (a b : V) (hb : ∀ i < 8, ln b i < 2 ^ 31) :
    ∃ r, _mm256_sign_epi32 a b = .ok r ∧
      ∀ i < 8, ln r i = if ln b i = 0 then 0 else ln a i := by
  obtain ⟨d, hd⟩ := zeros
  obtain ⟨r, hr, hl⟩ := lane_loop (fun (s : V × V × V × Std.Usize) =>
      _mm256_sign_epi32_loop.body s.1 s.2.1 s.2.2.1 s.2.2.2)
    (fun e j => (a, b, e, j)) (fun i => if (b.val[i]!).val = 0 then 0#u32 else a.val[i]!) d
    (fun e k hk => by
      have hbk := hcast_u32_i32_val (b.val[k]!) (hb k hk)
      have hneg : ¬ (UScalar.hcast .I32 (b.val[k]!) < 0#i32) := by
        rw [IScalar.lt_equiv, hbk]; simp
      have hz : (UScalar.hcast .I32 (b.val[k]!) = 0#i32) ↔ (b.val[k]!).val = 0 := by
        constructor
        · intro h; have := congrArg IScalar.val h; rw [hbk] at this; simpa using this
        · intro h; apply IScalar.eq_of_val_eq; rw [hbk, h]; simp
      simp only [_mm256_sign_epi32_loop.body, usz_lt8 hk, ite_true, index_usz _ hk, bind_ok,
        lift_eq, hneg, ite_false]
      by_cases h0 : (b.val[k]!).val = 0
      · simp only [hz.mpr h0, ite_true, bind_ok, update_usz _ hk, usz_succ hk, h0]
        rfl
      · simp only [show ¬ (UScalar.hcast .I32 (b.val[k]!) = 0#i32) from fun h => h0 (hz.mp h),
          ite_false, bind_ok, update_usz _ hk, usz_succ hk, h0]
        rfl)
    (fun e => by simp only [_mm256_sign_epi32_loop.body, usz_not_lt8, ite_false])
  refine ⟨r, ?_, fun i hi => ?_⟩
  · unfold _mm256_sign_epi32 _mm256_sign_epi32_loop
    rw [hd, bind_ok, hr, bind_ok]
  · simp only [ln, hl i hi]
    split <;> simp_all

/-- `imm8` of a literal is its low byte. -/
theorem imm8_one : imm8 1#i32 = .ok 1#u32 := by
  simp only [imm8, lift_eq, bind_ok]; congr 1

theorem imm8_170 : imm8 170#i32 = .ok 170#u32 := by
  simp only [imm8, lift_eq, bind_ok]; congr 1

/-- A logical right shift by a `u32` or `usize` below the width. -/
theorem shr_u32_eq {ty} (x : Std.U32) (s : UScalar ty) (h : s.val < 32) :
    (x >>> s : RustM Std.U32) = .ok ⟨x.bv.ushiftRight s.val⟩ := by
  show UScalar.shiftRight_UScalar x s = _
  simp only [UScalar.shiftRight_UScalar, UScalar.shiftRight, UScalarTy.U32_numBits_eq, h, ite_true]

theorem ushiftRight_val (x : Std.U32) (n : ℕ) :
    (⟨x.bv.ushiftRight n⟩ : Std.U32).val = x.val / 2 ^ n := by
  show (x.bv.ushiftRight n).toNat = x.bv.toNat / 2 ^ n
  rw [BitVec.ushiftRight_eq, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

/-- `_mm256_srli_epi32::<1>`: lane-wise logical shift right by one. -/
theorem srli_epi32_one (a : V) : ∃ r, _mm256_srli_epi32 1#i32 a = .ok r ∧
    ∀ i < 8, ln r i = ln a i / 2 := by
  obtain ⟨d, hd⟩ := zeros
  have hsh : ∀ x : Std.U32, (x >>> (1#u32) : RustM Std.U32) = .ok ⟨x.bv.ushiftRight 1⟩ :=
    fun x => shr_u32_eq x 1#u32 (by decide)
  obtain ⟨r, hr, hl⟩ := lane_loop (fun (s : V × V × Std.Usize) =>
      _mm256_srli_epi32_loop.body 1#u32 s.1 s.2.1 s.2.2)
    (fun e j => (a, e, j)) (fun i => ⟨(a.val[i]!).bv.ushiftRight 1⟩) d
    (fun e k hk => by
      simp only [_mm256_srli_epi32_loop.body, usz_lt8 hk, ite_true, index_usz _ hk, bind_ok,
        show ¬ ((1#u32) > 31#u32) by decide, ite_false, hsh, update_usz _ hk, usz_succ hk]
      rfl)
    (fun e => by simp only [_mm256_srli_epi32_loop.body, usz_not_lt8, ite_false])
  refine ⟨r, ?_, fun i hi => ?_⟩
  · unfold _mm256_srli_epi32 _mm256_srli_epi32_loop
    rw [imm8_one, bind_ok, hd, bind_ok, hr, bind_ok]
  · rw [ln, hl i hi, ushiftRight_val, pow_one]; rfl

/-- `_mm256_blend_epi32::<0b10101010>`: odd lanes from `b`, even lanes from `a`. -/
theorem blend_epi32_170 (a b : V) : ∃ r, _mm256_blend_epi32 170#i32 a b = .ok r ∧
    ∀ i < 8, ln r i = if i % 2 = 1 then ln b i else ln a i := by
  obtain ⟨d, hd⟩ := zeros
  have hsh : ∀ k < 8, ((170#u32) >>> usz k : RustM Std.U32) =
      .ok ⟨(170#u32).bv.ushiftRight k⟩ := by
    intro k hk
    rw [shr_u32_eq _ _ (by rw [usz_val (show k < 2 ^ 32 by omega)]; omega),
      usz_val (show k < 2 ^ 32 by omega)]
  have hbit : ∀ k < 8,
      ((⟨(170#u32).bv.ushiftRight k⟩ : Std.U32) &&& 1#u32 = 1#u32) ↔ k % 2 = 1 := by
    intro k hk; interval_cases k <;> decide
  obtain ⟨r, hr, hl⟩ := lane_loop (fun (s : V × V × V × Std.Usize) =>
      _mm256_blend_epi32_loop.body 170#i32 s.1 s.2.1 s.2.2.1 s.2.2.2)
    (fun e j => (a, b, e, j)) (fun i => if i % 2 = 1 then b.val[i]! else a.val[i]!) d
    (fun e k hk => by
      simp only [_mm256_blend_epi32_loop.body, usz_lt8 hk, ite_true, imm8_170, bind_ok,
        hsh k hk, lift_eq]
      by_cases h : k % 2 = 1
      · simp only [(hbit k hk).mpr h, ite_true, index_usz _ hk, bind_ok, update_usz _ hk,
          usz_succ hk, h]
        rfl
      · simp only [show ¬ ((⟨(170#u32).bv.ushiftRight k⟩ : Std.U32) &&& 1#u32 = 1#u32) from
          fun h' => h ((hbit k hk).mp h'), ite_false, index_usz _ hk, bind_ok, update_usz _ hk,
          usz_succ hk, h]
        rfl)
    (fun e => by simp only [_mm256_blend_epi32_loop.body, usz_not_lt8, ite_false])
  refine ⟨r, ?_, fun i hi => ?_⟩
  · unfold _mm256_blend_epi32 _mm256_blend_epi32_loop
    rw [hd, bind_ok, hr, bind_ok]
  · simp only [ln, hl i hi]
    split <;> rfl

theorem two_mul_usz {k : ℕ} (hk : k < 4) :
    (2#usize * usz k : RustM Std.Usize) = .ok (usz (2 * k)) := by
  rw [show (2#usize) = usz 2 from eq_usz (by norm_num) (by simp)]
  exact usz_mul (by omega) (by norm_num) (by omega)

theorem usz_two_succ {k : ℕ} (hk : k < 4) :
    (usz (2 * k) + 1#usize : RustM Std.Usize) = .ok (usz (2 * k + 1)) := by
  rw [show (1#usize) = usz 1 from eq_usz (by norm_num) (by simp)]
  exact usz_add (by omega)

theorem usz_succ4 {k : ℕ} (hk : k < 4) :
    (usz k + 1#usize : RustM Std.Usize) = .ok (usz (k + 1)) := usz_succ (by omega)

/-- The `u64` product of two `u32`s, which cannot overflow. -/
theorem mul_u64_eq (x y : Std.U32) :
    (UScalar.cast .U64 x * UScalar.cast .U64 y : RustM Std.U64) =
      .ok ⟨BitVec.ofNat 64 (x.val * y.val)⟩ := by
  have hx := u32_lt x; have hy := u32_lt y
  have hxy : x.val * y.val < 2 ^ 64 := by
    calc x.val * y.val < 2 ^ 32 * 2 ^ 32 := Nat.mul_lt_mul'' hx hy
      _ = 2 ^ 64 := by norm_num
  have hmax : UScalar.max .U64 = 2 ^ 64 - 1 := by
    simp only [UScalar.max, UScalarTy.U64_numBits_eq]
  obtain ⟨z, hz, hzv⟩ := spec_imp_exists (UScalar.mul_spec (x := UScalar.cast .U64 x)
    (y := UScalar.cast .U64 y)
    (by rw [cast_u32_u64_val, cast_u32_u64_val, hmax]; omega))
  rw [hz]; congr 1; apply UScalar.eq_of_val_eq
  rw [hzv, cast_u32_u64_val, cast_u32_u64_val]
  show _ = (BitVec.ofNat 64 (x.val * y.val)).toNat
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hxy]

theorem split64_eq (v : Std.U64) :
    split64 v = .ok (UScalar.cast .U32 v, UScalar.cast .U32 (⟨v.bv.ushiftRight 32⟩ : Std.U64)) := by
  unfold split64
  rw [lift_eq, bind_ok, shiftRight_i32_eq v 32#i32 (by decide) (by decide), bind_ok, lift_eq,
    bind_ok]
  rfl

/-- `_mm256_mul_epu32`: for each 64-bit pair `j`, the full product of the low lanes `2j` of `a`
and `b`, low half in lane `2j`, high half in lane `2j + 1`. -/
theorem mul_epu32 (a b : V) : ∃ r, _mm256_mul_epu32 a b = .ok r ∧
    ∀ j < 4, ln r (2 * j) = ln a (2 * j) * ln b (2 * j) % 2 ^ 32 ∧
      ln r (2 * j + 1) = ln a (2 * j) * ln b (2 * j) / 2 ^ 32 := by
  obtain ⟨d, hd⟩ := zeros
  let P : ℕ → Std.U64 := fun k => ⟨BitVec.ofNat 64 ((a.val[2 * k]!).val * (b.val[2 * k]!).val)⟩
  obtain ⟨r, hr, hl⟩ := pair_loop (fun (s : V × V × V × Std.Usize) =>
      _mm256_mul_epu32_loop.body s.1 s.2.1 s.2.2.1 s.2.2.2)
    (fun e j => (a, b, e, j)) (fun k => UScalar.cast .U32 (P k))
    (fun k => UScalar.cast .U32 (⟨(P k).bv.ushiftRight 32⟩ : Std.U64)) d
    (fun e k hk => by
      simp only [_mm256_mul_epu32_loop.body, usz_lt4 hk, ite_true, two_mul_usz hk, bind_ok,
        index_usz _ (show 2 * k < 8 by omega), lift_eq, mul_u64_eq, split64_eq,
        update_usz _ (show 2 * k < 8 by omega), usz_two_succ hk,
        update_usz _ (show 2 * k + 1 < 8 by omega), usz_succ4 hk]
      rfl)
    (fun e => by simp only [_mm256_mul_epu32_loop.body, usz_not_lt4, ite_false])
  refine ⟨r, ?_, fun j hj => ?_⟩
  · unfold _mm256_mul_epu32 _mm256_mul_epu32_loop
    rw [hd, bind_ok, hr, bind_ok]
  · have hxy : (a.val[2 * j]!).val * (b.val[2 * j]!).val < 2 ^ 64 := by
      calc _ < 2 ^ 32 * 2 ^ 32 := Nat.mul_lt_mul'' (u32_lt _) (u32_lt _)
        _ = 2 ^ 64 := by norm_num
    obtain ⟨h1, h2⟩ := hl j hj
    have hP : (P j).val = (a.val[2 * j]!).val * (b.val[2 * j]!).val := by
      show (BitVec.ofNat 64 _).toNat = _
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hxy]
    have hPs : (⟨(P j).bv.ushiftRight 32⟩ : Std.U64).val = (P j).val / 2 ^ 32 := by
      show ((P j).bv.ushiftRight 32).toNat = (P j).bv.toNat / 2 ^ 32
      rw [BitVec.ushiftRight_eq, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
    refine ⟨?_, ?_⟩
    · rw [ln, h1, cast_u64_u32_val, hP]; rfl
    · rw [ln, h2, cast_u64_u32_val, hPs, hP]
      refine Nat.mod_eq_of_lt ?_
      rw [Nat.div_lt_iff_lt_mul (by norm_num)]
      calc _ < 2 ^ 64 := hxy
        _ = 2 ^ 32 * 2 ^ 32 := by norm_num

/-- `_mm256_castsi256_ps` and `_mm256_castps_si256` reinterpret the lanes. -/
theorem castsi256_ps (a : V) : _mm256_castsi256_ps a = .ok a := rfl

theorem castps_si256 (a : V) : _mm256_castps_si256 a = .ok a := rfl

/-- `_mm256_movehdup_ps`: each odd lane copied into the even lane below it. -/
theorem movehdup_ps (a : V) : ∃ r, _mm256_movehdup_ps a = .ok r ∧
    ∀ i < 8, ln r i = ln a (2 * (i / 2) + 1) := by
  unfold _mm256_movehdup_ps
  rw [show (1#usize) = usz 1 from eq_usz (by norm_num) (by simp),
    show (3#usize) = usz 3 from eq_usz (by norm_num) (by simp),
    show (5#usize) = usz 5 from eq_usz (by norm_num) (by simp),
    show (7#usize) = usz 7 from eq_usz (by norm_num) (by simp),
    index_usz a (by norm_num : 1 < 8), index_usz a (by norm_num : 3 < 8),
    index_usz a (by norm_num : 5 < 8), index_usz a (by norm_num : 7 < 8)]
  simp only [bind_ok]
  refine ⟨_, rfl, fun i hi => ?_⟩
  interval_cases i <;> rfl

/-- `_mm256_set1_epi32`: every lane is the `i32` read as a `u32`. -/
theorem set1_epi32 (x : Std.I32) : ∃ r, _mm256_set1_epi32 x = .ok r ∧
    ∀ i < 8, ln r i = (IScalar.hcast .U32 x).val := by
  unfold _mm256_set1_epi32
  obtain ⟨d, hd, hdx⟩ := array_repeat_eq 8#usize core.U32.Insts.CoreCloneClone (fun _ => rfl)
    (IScalar.hcast .U32 x)
  rw [lift_eq, bind_ok, hd, bind_ok]
  refine ⟨d, rfl, fun i hi => ?_⟩
  have hi' : i < d.val.length := by rw [V.len]; exact hi
  simp only [ln, List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hi', Option.getD_some]
  rw [hdx _ (List.getElem_mem hi')]

end shims

end Plonky3Lean.Proofs.Avx2
