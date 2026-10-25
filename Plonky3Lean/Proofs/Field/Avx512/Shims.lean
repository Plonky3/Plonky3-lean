module

public import P3ArchShims
public import Plonky3Lean.Proofs.Field.Avx2.Shims

@[expose] public section

/-!
# AVX-512: the intrinsic models, lane by lane

Each model in `P3ArchShims` (the extraction of `arch/`) that `PackedMontyField31AVX512`'s
arithmetic reaches, as a function of its input lanes: it never fails, and lane `i` of its
result is a stated function of lane `i` (or, for the 64-bit and shuffling intrinsics, of named
lanes) of its inputs. Lanes are read as natural numbers, `ln v i = v[i].val`.

A mask (`__mmask16`, a `u16`) is read by its bits: `mbit k j` is bit `j` of `k`, `k[j]` in
Intel's pseudocode. The comparisons build a mask one bit per loop iteration (`mask_loop`), and
the masked operations read bit `j` to choose lane `j` (`bit16_eq`).

As for AVX2 (`Plonky3Lean.Proofs.Avx2`), the models write their result one lane (or one 64-bit
pair of lanes) per loop iteration into an array of zeros; `lane_loop` and `pair_loop` run such a
loop to the end, here at width 16.
-/

open Aeneas Aeneas.Std CoreModels
open Plonky3Lean.Lib
open Plonky3Lean.Proofs.Avx2 (usz_lt8 usz_not_lt8)
open Plonky3Lean.Proofs.Avx2.shims (ite_ok mul_u64_eq shr_u32_eq ushiftRight_val)

namespace Plonky3Lean.Proofs.Avx512

/-- An `__m512i` (or `__m512`) as the models have it: sixteen `u32` lanes. -/
abbrev V := Std.Array Std.U32 16#usize

/-- Lane `i` of `v`, as a natural number. -/
def ln (v : V) (i : ℕ) : ℕ := (v.val[i]!).val

theorem V.len (v : V) : v.val.length = 16 := by simp

/-! ## Small indices -/

theorem index_usz (a : V) {k : ℕ} (hk : k < 16) :
    Aeneas.Std.Array.index_usize a (usz k) = .ok a.val[k]! := by
  have hk' : k < a.val.length := by rw [V.len]; exact hk
  simp [Aeneas.Std.Array.index_usize, Aeneas.Std.Array.getElem?_Usize_eq,
    usz_val (show k < 2 ^ 32 by omega), List.getElem?_eq_getElem hk',
    List.getElem!_eq_getElem?_getD]

theorem update_usz (a : V) {k : ℕ} (hk : k < 16) (x : Std.U32) :
    Aeneas.Std.Array.update a (usz k) x = .ok (a.set (usz k) x) := by
  have hk' : k < a.val.length := by rw [V.len]; exact hk
  simp [Aeneas.Std.Array.update, Aeneas.Std.Array.set, Aeneas.Std.Array.getElem?_Usize_eq,
    usz_val (show k < 2 ^ 32 by omega), List.getElem?_eq_getElem hk']

theorem usz_succ {k : ℕ} (hk : k < 16) :
    (usz k + 1#usize : RustM Std.Usize) = .ok (usz (k + 1)) := by
  rw [show (1#usize) = usz 1 from eq_usz (by norm_num) (by simp)]
  exact usz_add (by omega)

theorem usz_lt16 {k : ℕ} (hk : k < 16) : (usz k < 16#usize) = True := by
  rw [show (16#usize) = usz 16 from eq_usz (by norm_num) (by simp), eq_iff_iff, iff_true]
  exact (usz_lt_iff (by omega) (by norm_num)).mpr hk

theorem usz_not_lt16 : (usz 16 < 16#usize) = False := by
  rw [show (16#usize) = usz 16 from eq_usz (by norm_num) (by simp), eq_iff_iff, iff_false]
  exact lt_irrefl (usz _)

theorem two_mul_usz {k : ℕ} (hk : k < 8) :
    (2#usize * usz k : RustM Std.Usize) = .ok (usz (2 * k)) := by
  rw [show (2#usize) = usz 2 from eq_usz (by norm_num) (by simp)]
  exact usz_mul (by omega) (by norm_num) (by omega)

theorem usz_two_succ {k : ℕ} (hk : k < 8) :
    (usz (2 * k) + 1#usize : RustM Std.Usize) = .ok (usz (2 * k + 1)) := by
  rw [show (1#usize) = usz 1 from eq_usz (by norm_num) (by simp)]
  exact usz_add (by omega)

/-! ## Lane loops -/

/-- The array after `k` iterations of a lane loop from `d`: lanes below `k` hold `f`. -/
def fill (f : ℕ → Std.U32) (d : V) : ℕ → V
  | 0 => d
  | k + 1 => (fill f d k).set (usz k) (f k)

theorem fill_lane (f : ℕ → Std.U32) (d : V) :
    ∀ k ≤ 16, ∀ i < k, (fill f d k).val[i]! = f i := by
  intro k
  induction k with
  | zero => intro _ i hi; omega
  | succ k ih =>
    intro hk i hi
    simp only [fill, Aeneas.Std.Array.set_val_eq, usz_val (show k < 2 ^ 32 by omega)]
    have hlen : (fill f d k).val.length = 16 := V.len _
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h | h
    · rw [← ih (by omega) i h]
      simp only [List.getElem!_eq_getElem?_getD, List.getElem?_set_ne (show k ≠ i by omega)]
    · subst h
      rw [List.getElem!_eq_getElem?_getD, List.getElem?_set_self (by rw [hlen]; omega),
        Option.getD_some]

/-- A loop that, from `j = 0`, writes `f j` into lane `j` and stops at `j = 16`, returns the
array of the `f j`. -/
theorem lane_loop {S : Type} (body : S → RustM (ControlFlow S V)) (mk : V → Std.Usize → S)
    (f : ℕ → Std.U32) (d : V)
    (hstep : ∀ (e : V) (k : ℕ), k < 16 →
      body (mk e (usz k)) = .ok (.cont (mk (e.set (usz k) (f k)) (usz (k + 1)))))
    (hdone : ∀ e, body (mk e (usz 16)) = .ok (.done e)) :
    ∃ r, loop body (mk d 0#usize) = .ok r ∧ ∀ i < 16, r.val[i]! = f i :=
  ⟨fill f d 16,
    loop_of_steps body (fun k => mk (fill f d k) (usz k)) 16 (fill f d 16)
      (fun k hk => hstep _ k hk) (hdone _),
    fill_lane f d 16 le_rfl⟩

/-- The array after `k` iterations of a pair loop from `d`: for `j < k`, lanes `2j` and
`2j + 1` hold `lo j` and `hi j`. -/
def fill2 (lo hi : ℕ → Std.U32) (d : V) : ℕ → V
  | 0 => d
  | k + 1 => ((fill2 lo hi d k).set (usz (2 * k)) (lo k)).set (usz (2 * k + 1)) (hi k)

theorem fill2_lane (lo hi : ℕ → Std.U32) (d : V) :
    ∀ k ≤ 8, ∀ j < k, (fill2 lo hi d k).val[2 * j]! = lo j ∧
      (fill2 lo hi d k).val[2 * j + 1]! = hi j := by
  intro k
  induction k with
  | zero => intro _ j hj; omega
  | succ k ih =>
    intro hk j hj
    simp only [fill2, Aeneas.Std.Array.set_val_eq, usz_val (show 2 * k < 2 ^ 32 by omega),
      usz_val (show 2 * k + 1 < 2 ^ 32 by omega)]
    have hlen : (fill2 lo hi d k).val.length = 16 := V.len _
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
at `k = 8`. -/
theorem pair_loop {S : Type} (body : S → RustM (ControlFlow S V)) (mk : V → Std.Usize → S)
    (lo hi : ℕ → Std.U32) (d : V)
    (hstep : ∀ (e : V) (k : ℕ), k < 8 →
      body (mk e (usz k)) = .ok (.cont (mk ((e.set (usz (2 * k)) (lo k)).set
        (usz (2 * k + 1)) (hi k)) (usz (k + 1)))))
    (hdone : ∀ e, body (mk e (usz 8)) = .ok (.done e)) :
    ∃ r, loop body (mk d 0#usize) = .ok r ∧
      ∀ j < 8, r.val[2 * j]! = lo j ∧ r.val[2 * j + 1]! = hi j :=
  ⟨fill2 lo hi d 8,
    loop_of_steps body (fun k => mk (fill2 lo hi d k) (usz k)) 8 (fill2 lo hi d 8)
      (fun k hk => hstep _ k hk) (hdone _),
    fill2_lane lo hi d 8 le_rfl⟩

/-- The zero array every model starts from. -/
theorem zeros : ∃ d : V, core.array.repeat 16#usize core.U32.Insts.CoreCloneClone 0#u32 = .ok d :=
  let ⟨d, hd, _⟩ := array_repeat_eq 16#usize core.U32.Insts.CoreCloneClone (fun _ => rfl) 0#u32
  ⟨d, hd⟩

/-! ## Masks -/

/-- Bit `j` of a mask, `k[j]`. -/
def mbit (k : ℕ) (j : ℕ) : Prop := k / 2 ^ j % 2 = 1

instance (k j : ℕ) : Decidable (mbit k j) := inferInstanceAs (Decidable (_ = _))

/-- The model's `bit16(k, j)`, for `j < 16`, is bit `j` of `k`. -/
theorem bit16_eq (k : Std.U16) {j : ℕ} (hj : j < 16) :
    p3_arch_shims.x86_64.avx512.bit16 k (usz j) = .ok (decide (mbit k.val j)) := by
  have hsh : (k >>> usz j : RustM Std.U16) = .ok ⟨k.bv.ushiftRight j⟩ := by
    show UScalar.shiftRight_UScalar k (usz j) = _
    simp only [UScalar.shiftRight_UScalar, UScalar.shiftRight, UScalarTy.U16_numBits_eq,
      usz_val (show j < 2 ^ 32 by omega), hj, ite_true]
  unfold p3_arch_shims.x86_64.avx512.bit16
  rw [hsh, bind_ok, lift_eq, bind_ok]
  congr 1
  apply decide_eq_decide.mpr
  have hv : ((⟨k.bv.ushiftRight j⟩ : Std.U16) &&& 1#u16).val = k.val / 2 ^ j % 2 := by
    rw [UScalar.val_and, show (1#u16 : Std.U16).val = 1 from rfl, Nat.and_one_is_mod]
    show (k.bv.ushiftRight j).toNat % 2 = _
    rw [BitVec.ushiftRight_eq, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
    rfl
  constructor
  · intro h
    have := congrArg UScalar.val h
    rw [hv] at this
    exact this
  · intro h
    apply UScalar.eq_of_val_eq
    rw [hv]
    exact h

/-- `1 << j` as a `u16`, for `j < 16`: the left shift the comparisons set bit `j` with. -/
def pow2u16 (j : ℕ) : Std.U16 := ⟨(1#u16).bv.shiftLeft j⟩

theorem pow2u16_val {j : ℕ} (hj : j < 16) : (pow2u16 j).val = 2 ^ j := by
  show ((1#u16).bv.shiftLeft j).toNat = 2 ^ j
  rw [BitVec.shiftLeft_eq, BitVec.toNat_shiftLeft]
  show (1 <<< j) % 2 ^ 16 = 2 ^ j
  rw [Nat.one_shiftLeft, Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by norm_num) hj)]

theorem shl_u16_eq {j : ℕ} (hj : j < 16) :
    (1#u16 <<< usz j : RustM Std.U16) = .ok (pow2u16 j) := by
  show UScalar.shiftLeft_UScalar (1#u16) (usz j) = _
  simp only [UScalar.shiftLeft_UScalar, UScalar.shiftLeft, UScalarTy.U16_numBits_eq,
    usz_val (show j < 2 ^ 32 by omega), hj, ite_true]
  rfl

/-- The mask after `k` iterations of a comparison loop: bit `j` set for each `j < k` where
`c j` holds. -/
def mfill (c : ℕ → Prop) [DecidablePred c] : ℕ → Std.U16
  | 0 => 0#u16
  | k + 1 => if c k then mfill c k ||| pow2u16 k else mfill c k

theorem mfill_bits (c : ℕ → Prop) [DecidablePred c] :
    ∀ k ≤ 16, (mfill c k).val < 2 ^ k ∧ ∀ j < k, (mbit (mfill c k).val j ↔ c j) := by
  intro k
  induction k with
  | zero => intro _; exact ⟨by simp [mfill], fun j hj => by omega⟩
  | succ k ih =>
    intro hk
    obtain ⟨hlt, hb⟩ := ih (by omega)
    set m := mfill c k with hm
    by_cases hck : c k
    · have hval : (mfill c (k + 1)).val = 2 ^ k + m.val := by
        simp only [mfill, hck, ite_true]
        rw [UScalar.val_or, pow2u16_val (by omega), ← hm]
        have := Nat.two_pow_add_eq_or_of_lt hlt 1
        rw [Nat.mul_one] at this
        rw [Nat.lor_comm]
        exact this.symm
      rw [hval]
      refine ⟨by rw [pow_succ]; omega, fun j hj => ?_⟩
      unfold mbit
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with h | h
      · have hdiv : (2 ^ k + m.val) / 2 ^ j = 2 ^ (k - j) + m.val / 2 ^ j := by
          rw [show 2 ^ k = 2 ^ (k - j) * 2 ^ j by rw [← pow_add]; congr 1; omega,
            Nat.add_comm, Nat.add_mul_div_right _ _ (by positivity), Nat.add_comm]
        rw [hdiv, show 2 ^ (k - j) = 2 * 2 ^ (k - j - 1) by
          rw [← pow_succ']; congr 1; omega, Nat.add_comm, Nat.add_mul_mod_self_left]
        exact hb j h
      · subst h
        have : (2 ^ j + m.val) / 2 ^ j = 1 := by
          rw [Nat.div_eq_of_lt_le] <;> [omega; omega]
        rw [this]
        simp [hck]
    · have hval : mfill c (k + 1) = m := by simp only [mfill, hck, ite_false, hm]
      rw [hval]
      refine ⟨lt_of_lt_of_le hlt (Nat.pow_le_pow_right (by norm_num) (by omega)), fun j hj => ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with h | h
      · exact hb j h
      · subst h
        unfold mbit
        rw [Nat.div_eq_of_lt hlt]
        simp [hck]

/-- A loop that, from `j = 0` and the mask `0`, sets bit `j` where `c j` holds and stops at
`j = 16`, returns the mask whose bit `j` is `c j`. -/
theorem mask_loop {S : Type} (body : S → RustM (ControlFlow S Std.U16))
    (mk : Std.U16 → Std.Usize → S) (c : ℕ → Prop) [DecidablePred c]
    (hstep : ∀ (m : Std.U16) (k : ℕ), k < 16 →
      body (mk m (usz k)) = .ok (.cont (mk (if c k then m ||| pow2u16 k else m) (usz (k + 1)))))
    (hdone : ∀ m, body (mk m (usz 16)) = .ok (.done m)) :
    ∃ r, loop body (mk 0#u16 0#usize) = .ok r ∧ ∀ j < 16, (mbit r.val j ↔ c j) :=
  ⟨mfill c 16,
    loop_of_steps body (fun k => mk (mfill c k) (usz k)) 16 (mfill c 16)
      (fun k hk => hstep _ k hk) (hdone _),
    (mfill_bits c 16 le_rfl).2⟩

/-! ## The models -/

namespace shims
open p3_arch_shims.x86_64.avx512

/-- `_mm512_add_epi32`: lane-wise `a + b mod 2^32`. -/
theorem add_epi32 (a b : V) : ∃ r, _mm512_add_epi32 a b = .ok r ∧
    ∀ i < 16, ln r i = (ln a i + ln b i) % 2 ^ 32 := by
  obtain ⟨d, hd⟩ := zeros
  obtain ⟨r, hr, hl⟩ := lane_loop (fun (s : V × V × V × Std.Usize) =>
      _mm512_add_epi32_loop.body s.1 s.2.1 s.2.2.1 s.2.2.2)
    (fun e j => (a, b, e, j)) (fun i => a.val[i]!.wrapping_add b.val[i]!) d
    (fun e k hk => by
      simp only [_mm512_add_epi32_loop.body, usz_lt16 hk, ite_true, index_usz _ hk, bind_ok,
        CoreModels.core.num.U32.wrapping_add, rust_primitives.arithmetic.wrapping_add_u32,
        update_usz _ hk, usz_succ hk])
    (fun e => by simp only [_mm512_add_epi32_loop.body, usz_not_lt16, ite_false])
  refine ⟨r, ?_, fun i hi => ?_⟩
  · unfold _mm512_add_epi32 _mm512_add_epi32_loop
    rw [hd, bind_ok, hr, bind_ok]
  · simp only [ln, hl i hi, U32.wrapping_add_val_eq, size_u32]

/-- `_mm512_sub_epi32`: lane-wise `a - b mod 2^32`. -/
theorem sub_epi32 (a b : V) : ∃ r, _mm512_sub_epi32 a b = .ok r ∧
    ∀ i < 16, ln r i = (ln a i + (2 ^ 32 - ln b i)) % 2 ^ 32 := by
  obtain ⟨d, hd⟩ := zeros
  obtain ⟨r, hr, hl⟩ := lane_loop (fun (s : V × V × V × Std.Usize) =>
      _mm512_sub_epi32_loop.body s.1 s.2.1 s.2.2.1 s.2.2.2)
    (fun e j => (a, b, e, j)) (fun i => a.val[i]!.wrapping_sub b.val[i]!) d
    (fun e k hk => by
      simp only [_mm512_sub_epi32_loop.body, usz_lt16 hk, ite_true, index_usz _ hk, bind_ok,
        CoreModels.core.num.U32.wrapping_sub, rust_primitives.arithmetic.wrapping_sub_u32,
        update_usz _ hk, usz_succ hk])
    (fun e => by simp only [_mm512_sub_epi32_loop.body, usz_not_lt16, ite_false])
  refine ⟨r, ?_, fun i hi => ?_⟩
  · unfold _mm512_sub_epi32 _mm512_sub_epi32_loop
    rw [hd, bind_ok, hr, bind_ok]
  · rw [ln, hl i hi, U32.wrapping_sub_val_eq, size_u32]; rfl

/-- `_mm512_min_epu32`: lane-wise unsigned minimum. -/
theorem min_epu32 (a b : V) : ∃ r, _mm512_min_epu32 a b = .ok r ∧
    ∀ i < 16, ln r i = min (ln a i) (ln b i) := by
  obtain ⟨d, hd⟩ := zeros
  obtain ⟨r, hr, hl⟩ := lane_loop (fun (s : V × V × V × Std.Usize) =>
      _mm512_min_epu32_loop.body s.1 s.2.1 s.2.2.1 s.2.2.2)
    (fun e j => (a, b, e, j)) (fun i => if a.val[i]! ≤ b.val[i]! then a.val[i]! else b.val[i]!) d
    (fun e k hk => by
      simp only [_mm512_min_epu32_loop.body, usz_lt16 hk, ite_true, index_usz _ hk, bind_ok,
        ite_ok, update_usz _ hk, usz_succ hk])
    (fun e => by simp only [_mm512_min_epu32_loop.body, usz_not_lt16, ite_false])
  refine ⟨r, ?_, fun i hi => ?_⟩
  · unfold _mm512_min_epu32 _mm512_min_epu32_loop
    rw [hd, bind_ok, hr, bind_ok]
  · simp only [ln, hl i hi]
    split
    · rename_i h; rw [Nat.min_eq_left (UScalar.le_equiv _ _ |>.mp h)]
    · rename_i h; rw [Nat.min_eq_right (by have := (UScalar.le_equiv _ _).not.mp h; omega)]

/-- `_mm512_test_epi32_mask`: bit `j` is set exactly where `a AND b` is nonzero in lane `j`. -/
theorem test_epi32_mask (a b : V) : ∃ m, _mm512_test_epi32_mask a b = .ok m ∧
    ∀ j < 16, (mbit m.val j ↔ ln a j &&& ln b j ≠ 0) := by
  obtain ⟨m, hm, hml⟩ := mask_loop (fun (s : V × V × Std.U16 × Std.Usize) =>
      _mm512_test_epi32_mask_loop.body s.1 s.2.1 s.2.2.1 s.2.2.2)
    (fun m j => (a, b, m, j)) (fun i => ¬ (a.val[i]! &&& b.val[i]! = 0#u32))
    (fun m k hk => by
      simp only [_mm512_test_epi32_mask_loop.body, usz_lt16 hk, ite_true, index_usz _ hk,
        bind_ok, lift_eq, bne_iff_ne, ne_eq, shl_u16_eq hk, ite_ok, usz_succ hk])
    (fun m => by simp only [_mm512_test_epi32_mask_loop.body, usz_not_lt16, ite_false])
  refine ⟨m, ?_, fun j hj => ?_⟩
  · unfold _mm512_test_epi32_mask _mm512_test_epi32_mask_loop
    exact hm
  · rw [hml j hj, ne_eq, not_iff_not, ln, ln, ← UScalar.val_and]
    constructor
    · intro h; rw [h]; rfl
    · intro h; exact UScalar.eq_of_val_eq h

/-- `_mm512_cmplt_epu32_mask`: bit `j` is set exactly where lane `j` of `a` is below `b`'s. -/
theorem cmplt_epu32_mask (a b : V) : ∃ m, _mm512_cmplt_epu32_mask a b = .ok m ∧
    ∀ j < 16, (mbit m.val j ↔ ln a j < ln b j) := by
  obtain ⟨m, hm, hml⟩ := mask_loop (fun (s : V × V × Std.U16 × Std.Usize) =>
      _mm512_cmplt_epu32_mask_loop.body s.1 s.2.1 s.2.2.1 s.2.2.2)
    (fun m j => (a, b, m, j)) (fun i => a.val[i]! < b.val[i]!)
    (fun m k hk => by
      simp only [_mm512_cmplt_epu32_mask_loop.body, usz_lt16 hk, ite_true, index_usz _ hk,
        bind_ok, shl_u16_eq hk, ite_ok, usz_succ hk])
    (fun m => by simp only [_mm512_cmplt_epu32_mask_loop.body, usz_not_lt16, ite_false])
  refine ⟨m, ?_, fun j hj => ?_⟩
  · unfold _mm512_cmplt_epu32_mask _mm512_cmplt_epu32_mask_loop
    exact hm
  · rw [hml j hj]; exact UScalar.lt_equiv _ _

/-- `_mm512_mask_add_epi32(src, k, a, b)`: lane `i` is `a + b mod 2^32` where bit `i` of `k` is
set, and `src`'s lane elsewhere. -/
theorem mask_add_epi32 (src : V) (k : Std.U16) (a b : V) :
    ∃ r, _mm512_mask_add_epi32 src k a b = .ok r ∧
      ∀ i < 16, ln r i = if mbit k.val i then (ln a i + ln b i) % 2 ^ 32 else ln src i := by
  obtain ⟨d, hd⟩ := zeros
  obtain ⟨r, hr, hl⟩ := lane_loop (fun (s : V × V × V × V × Std.Usize) =>
      _mm512_mask_add_epi32_loop.body k s.1 s.2.1 s.2.2.1 s.2.2.2.1 s.2.2.2.2)
    (fun e j => (src, a, b, e, j))
    (fun i => if mbit k.val i then a.val[i]!.wrapping_add b.val[i]! else src.val[i]!) d
    (fun e j hj => by
      simp only [_mm512_mask_add_epi32_loop.body, usz_lt16 hj, ite_true, bit16_eq k hj, bind_ok]
      by_cases hb : mbit k.val j
      · simp only [decide_true, ite_true, index_usz _ hj, bind_ok,
          CoreModels.core.num.U32.wrapping_add, rust_primitives.arithmetic.wrapping_add_u32,
          update_usz _ hj, usz_succ hj, hb]
        rfl
      · simp only [decide_false, Bool.false_eq_true, ite_false, index_usz _ hj, bind_ok,
          update_usz _ hj, usz_succ hj, hb]
        rfl)
    (fun e => by simp only [_mm512_mask_add_epi32_loop.body, usz_not_lt16, ite_false])
  refine ⟨r, ?_, fun i hi => ?_⟩
  · unfold _mm512_mask_add_epi32 _mm512_mask_add_epi32_loop
    rw [hd, bind_ok, hr, bind_ok]
  · rw [ln, hl i hi]
    split
    · rw [U32.wrapping_add_val_eq, size_u32]; rfl
    · rfl

/-- `_mm512_maskz_sub_epi32(k, a, b)`: lane `i` is `a - b mod 2^32` where bit `i` of `k` is
set, and `0` elsewhere. -/
theorem maskz_sub_epi32 (k : Std.U16) (a b : V) :
    ∃ r, _mm512_maskz_sub_epi32 k a b = .ok r ∧
      ∀ i < 16, ln r i = if mbit k.val i then (ln a i + (2 ^ 32 - ln b i)) % 2 ^ 32 else 0 := by
  obtain ⟨d, hd⟩ := zeros
  obtain ⟨r, hr, hl⟩ := lane_loop (fun (s : V × V × V × Std.Usize) =>
      _mm512_maskz_sub_epi32_loop.body k s.1 s.2.1 s.2.2.1 s.2.2.2)
    (fun e j => (a, b, e, j))
    (fun i => if mbit k.val i then a.val[i]!.wrapping_sub b.val[i]! else 0#u32) d
    (fun e j hj => by
      simp only [_mm512_maskz_sub_epi32_loop.body, usz_lt16 hj, ite_true, bit16_eq k hj, bind_ok]
      by_cases hb : mbit k.val j
      · simp only [decide_true, ite_true, index_usz _ hj, bind_ok,
          CoreModels.core.num.U32.wrapping_sub, rust_primitives.arithmetic.wrapping_sub_u32,
          update_usz _ hj, usz_succ hj, hb]
        rfl
      · simp only [decide_false, Bool.false_eq_true, ite_false, bind_ok,
          update_usz _ hj, usz_succ hj, hb]
        rfl)
    (fun e => by simp only [_mm512_maskz_sub_epi32_loop.body, usz_not_lt16, ite_false])
  refine ⟨r, ?_, fun i hi => ?_⟩
  · unfold _mm512_maskz_sub_epi32 _mm512_maskz_sub_epi32_loop
    rw [hd, bind_ok, hr, bind_ok]
  · rw [ln, hl i hi]
    split
    · rw [U32.wrapping_sub_val_eq, size_u32]; rfl
    · rfl

/-- `imm8u` of a literal below 256 is itself. -/
theorem imm8u_one : imm8u 1#u32 = .ok 1#u32 := by
  simp only [imm8u]; congr 1

/-- `_mm512_srli_epi32::<1>`: lane-wise logical shift right by one. -/
theorem srli_epi32_one (a : V) : ∃ r, _mm512_srli_epi32 1#u32 a = .ok r ∧
    ∀ i < 16, ln r i = ln a i / 2 := by
  obtain ⟨d, hd⟩ := zeros
  have hsh : ∀ x : Std.U32, (x >>> (1#u32) : RustM Std.U32) = .ok ⟨x.bv.ushiftRight 1⟩ :=
    fun x => shr_u32_eq x 1#u32 (by decide)
  obtain ⟨r, hr, hl⟩ := lane_loop (fun (s : V × V × Std.Usize) =>
      _mm512_srli_epi32_loop.body 1#u32 s.1 s.2.1 s.2.2)
    (fun e j => (a, e, j)) (fun i => ⟨(a.val[i]!).bv.ushiftRight 1⟩) d
    (fun e k hk => by
      simp only [_mm512_srli_epi32_loop.body, usz_lt16 hk, ite_true, index_usz _ hk, bind_ok,
        show ¬ ((1#u32) > 31#u32) by decide, ite_false, hsh, update_usz _ hk, usz_succ hk]
      rfl)
    (fun e => by simp only [_mm512_srli_epi32_loop.body, usz_not_lt16, ite_false])
  refine ⟨r, ?_, fun i hi => ?_⟩
  · unfold _mm512_srli_epi32 _mm512_srli_epi32_loop
    rw [imm8u_one, bind_ok, hd, bind_ok, hr, bind_ok]
  · rw [ln, hl i hi, ushiftRight_val, pow_one]; rfl

theorem split64_eq (v : Std.U64) :
    split64 v = .ok (UScalar.cast .U32 v, UScalar.cast .U32 (⟨v.bv.ushiftRight 32⟩ : Std.U64)) := by
  unfold split64
  rw [lift_eq, bind_ok, shiftRight_i32_eq v 32#i32 (by decide) (by decide), bind_ok, lift_eq,
    bind_ok]
  rfl

/-- `_mm512_mul_epu32`: for each 64-bit pair `j`, the full product of the low lanes `2j` of `a`
and `b`, low half in lane `2j`, high half in lane `2j + 1`. -/
theorem mul_epu32 (a b : V) : ∃ r, _mm512_mul_epu32 a b = .ok r ∧
    ∀ j < 8, ln r (2 * j) = ln a (2 * j) * ln b (2 * j) % 2 ^ 32 ∧
      ln r (2 * j + 1) = ln a (2 * j) * ln b (2 * j) / 2 ^ 32 := by
  obtain ⟨d, hd⟩ := zeros
  let P : ℕ → Std.U64 := fun k => ⟨BitVec.ofNat 64 ((a.val[2 * k]!).val * (b.val[2 * k]!).val)⟩
  obtain ⟨r, hr, hl⟩ := pair_loop (fun (s : V × V × V × Std.Usize) =>
      _mm512_mul_epu32_loop.body s.1 s.2.1 s.2.2.1 s.2.2.2)
    (fun e j => (a, b, e, j)) (fun k => UScalar.cast .U32 (P k))
    (fun k => UScalar.cast .U32 (⟨(P k).bv.ushiftRight 32⟩ : Std.U64)) d
    (fun e k hk => by
      simp only [_mm512_mul_epu32_loop.body, usz_lt8 hk, ite_true, two_mul_usz hk, bind_ok,
        index_usz _ (show 2 * k < 16 by omega), lift_eq, mul_u64_eq, split64_eq,
        update_usz _ (show 2 * k < 16 by omega), usz_two_succ hk,
        update_usz _ (show 2 * k + 1 < 16 by omega), usz_succ (show k < 16 by omega)]
      rfl)
    (fun e => by simp only [_mm512_mul_epu32_loop.body, usz_not_lt8, ite_false])
  refine ⟨r, ?_, fun j hj => ?_⟩
  · unfold _mm512_mul_epu32 _mm512_mul_epu32_loop
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

/-- `_mm512_castsi512_ps` and `_mm512_castps_si512` reinterpret the lanes. -/
theorem castsi512_ps (a : V) : _mm512_castsi512_ps a = .ok a := rfl

theorem castps_si512 (a : V) : _mm512_castps_si512 a = .ok a := rfl

/-- The constant indices the `vmovshdup` models read. -/
theorem index_odd (a : V) :
    Aeneas.Std.Array.index_usize a 1#usize = .ok a.val[1]! ∧
    Aeneas.Std.Array.index_usize a 3#usize = .ok a.val[3]! ∧
    Aeneas.Std.Array.index_usize a 5#usize = .ok a.val[5]! ∧
    Aeneas.Std.Array.index_usize a 7#usize = .ok a.val[7]! ∧
    Aeneas.Std.Array.index_usize a 9#usize = .ok a.val[9]! ∧
    Aeneas.Std.Array.index_usize a 11#usize = .ok a.val[11]! ∧
    Aeneas.Std.Array.index_usize a 13#usize = .ok a.val[13]! ∧
    Aeneas.Std.Array.index_usize a 15#usize = .ok a.val[15]! := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  · rw [← index_usz a (by norm_num)]; congr 1; exact eq_usz (by norm_num) (by simp)

/-- The array of odd lanes, each copied into the even lane below it: `vmovshdup`'s `tmp`. -/
def hdup (a : V) : V :=
  Aeneas.Std.Array.make 16#usize [a.val[1]!, a.val[1]!, a.val[3]!, a.val[3]!, a.val[5]!,
    a.val[5]!, a.val[7]!, a.val[7]!, a.val[9]!, a.val[9]!, a.val[11]!, a.val[11]!, a.val[13]!,
    a.val[13]!, a.val[15]!, a.val[15]!] (by simp)

theorem hdup_lane (a : V) : ∀ i < 16, ln (hdup a) i = ln a (2 * (i / 2) + 1) := by
  intro i hi
  interval_cases i <;> rfl

/-- `_mm512_movehdup_ps`: each odd lane copied into the even lane below it. -/
theorem movehdup_ps (a : V) : ∃ r, _mm512_movehdup_ps a = .ok r ∧
    ∀ i < 16, ln r i = ln a (2 * (i / 2) + 1) := by
  obtain ⟨h1, h3, h5, h7, h9, h11, h13, h15⟩ := index_odd a
  refine ⟨hdup a, ?_, hdup_lane a⟩
  unfold _mm512_movehdup_ps
  rw [h1, bind_ok, h3, bind_ok, h5, bind_ok, h7, bind_ok, h9, bind_ok, h11, bind_ok, h13, bind_ok,
    h15, bind_ok]
  rfl

/-- `_mm512_mask_movehdup_ps(src, k, a)`: lane `i` is `a`'s odd lane `2 (i / 2) + 1` where bit
`i` of `k` is set, and `src`'s lane `i` elsewhere. -/
theorem mask_movehdup_ps (src : V) (k : Std.U16) (a : V) :
    ∃ r, _mm512_mask_movehdup_ps src k a = .ok r ∧
      ∀ i < 16, ln r i = if mbit k.val i then ln a (2 * (i / 2) + 1) else ln src i := by
  obtain ⟨h1, h3, h5, h7, h9, h11, h13, h15⟩ := index_odd a
  obtain ⟨d, hd⟩ := zeros
  let t := hdup a
  obtain ⟨r, hr, hl⟩ := lane_loop (fun (s : V × V × Std.Usize) =>
      _mm512_mask_movehdup_ps_loop.body k t s.1 s.2.1 s.2.2)
    (fun e j => (src, e, j))
    (fun i => if mbit k.val i then t.val[i]! else src.val[i]!) d
    (fun e j hj => by
      simp only [_mm512_mask_movehdup_ps_loop.body, usz_lt16 hj, ite_true, bit16_eq k hj, bind_ok]
      by_cases hb : mbit k.val j
      · simp only [decide_true, ite_true, index_usz _ hj, bind_ok, update_usz _ hj,
          usz_succ hj, hb]
        rfl
      · simp only [decide_false, Bool.false_eq_true, ite_false, index_usz _ hj, bind_ok,
          update_usz _ hj, usz_succ hj, hb]
        rfl)
    (fun e => by simp only [_mm512_mask_movehdup_ps_loop.body, usz_not_lt16, ite_false])
  refine ⟨r, ?_, fun i hi => ?_⟩
  · have hr' : ∀ t', t' = hdup a → _mm512_mask_movehdup_ps_loop src k t' d 0#usize = .ok r := by
      rintro _ rfl; exact hr
    unfold _mm512_mask_movehdup_ps
    rw [h1, bind_ok, h3, bind_ok, h5, bind_ok, h7, bind_ok, h9, bind_ok, h11, bind_ok, h13,
      bind_ok, h15, bind_ok, hd, bind_ok, hr', bind_ok]
    rfl
  · rw [ln, hl i hi]
    split
    · exact hdup_lane a i hi
    · rfl

/-- `_mm512_set1_epi32`: every lane is the `i32` read as a `u32`. -/
theorem set1_epi32 (x : Std.I32) : ∃ r, _mm512_set1_epi32 x = .ok r ∧
    ∀ i < 16, ln r i = (IScalar.hcast .U32 x).val := by
  unfold _mm512_set1_epi32
  obtain ⟨d, hd, hdx⟩ := array_repeat_eq 16#usize core.U32.Insts.CoreCloneClone (fun _ => rfl)
    (IScalar.hcast .U32 x)
  rw [lift_eq, bind_ok, hd, bind_ok]
  refine ⟨d, rfl, fun i hi => ?_⟩
  have hi' : i < d.val.length := by rw [V.len]; exact hi
  simp only [ln, List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hi', Option.getD_some]
  rw [hdx _ (List.getElem_mem hi')]

end shims

end Plonky3Lean.Proofs.Avx512
