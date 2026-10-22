module

public import Mathlib.Tactic.LinearCombination
public import Plonky3Lean.Proofs.Field.Goldilocks.PowersOfTwo

@[expose] public section

/-!
# Goldilocks: inversion

`try_inverse` runs two rounds of 63 steps of `p3_util::gcd_inner` on `(x, p)`.

Each step lowers `bitlen(a) + bitlen(b)` by one, so 126 steps leave `b = 1`.

The update factors then give `2^126 = c * x mod p`, and the result is `c * 2^66`.

The input `x` may be any `u64` not divisible by `p`, including those above `p`.
-/

namespace Plonky3Lean.Proofs.P3Goldilocks

/-- The integer an `i64` update factor stands for: `i64::MIN` is read as `2^63`. -/
def unwrapFactor (v : ℤ) : ℤ := if v = -2 ^ 63 then 2 ^ 63 else v

/-- The state of `gcd_inner` after `k` rounds, from inputs `A0` and `B0`, with bit budget `S`. -/
structure GcdInv (A0 B0 S a b : ℕ) (f0 g0 f1 g1 : ℤ) (k : ℕ) : Prop where
  k_le : k ≤ 63
  odd : b % 2 = 1
  coprime : Nat.Coprime a b
  len : a = 0 ∨ ∃ i j, a < 2 ^ i ∧ b < 2 ^ j ∧ i + j + k ≤ S
  rel_a : (2 : ℤ) ^ k * a = f0 * A0 + g0 * B0
  rel_b : (2 : ℤ) ^ k * b = f1 * A0 + g1 * B0
  f0_lo : -(2 : ℤ) ^ k < f0
  f0_hi : f0 ≤ (2 : ℤ) ^ k
  g0_lo : -(2 : ℤ) ^ k < g0
  g0_hi : g0 ≤ (2 : ℤ) ^ k
  f1_lo : -(2 : ℤ) ^ k < f1
  f1_hi : f1 ≤ (2 : ℤ) ^ k
  g1_lo : -(2 : ℤ) ^ k < g1
  g1_hi : g1 ≤ (2 : ℤ) ^ k

/-- The swap of an odd `a` with `b` keeps the invariant. -/
theorem GcdInv.swap {A0 B0 S a b : ℕ} {f0 g0 f1 g1 : ℤ} {k : ℕ}
    (h : GcdInv A0 B0 S a b f0 g0 f1 g1 k) (ho : a % 2 = 1) :
    GcdInv A0 B0 S b a f1 g1 f0 g0 k where
  k_le := h.k_le
  odd := ho
  coprime := h.coprime.symm
  len := by
    rcases h.len with h0 | ⟨i, j, hi, hj, hij⟩
    · omega
    · exact .inr ⟨j, i, hj, hi, by omega⟩
  rel_a := h.rel_b
  rel_b := h.rel_a
  f0_lo := h.f1_lo
  f0_hi := h.f1_hi
  g0_lo := h.g1_lo
  g0_hi := h.g1_hi
  f1_lo := h.f0_lo
  f1_hi := h.f0_hi
  g1_lo := h.g0_lo
  g1_hi := h.g0_hi

/-- An even `a` is halved, and `f1`, `g1` are doubled. -/
theorem GcdInv.even {A0 B0 S a b : ℕ} {f0 g0 f1 g1 : ℤ} {k : ℕ}
    (h : GcdInv A0 B0 S a b f0 g0 f1 g1 k) (hk : k < 63) (he : a % 2 = 0) :
    GcdInv A0 B0 S (a / 2) b f0 g0 (2 * f1) (2 * g1) (k + 1) := by
  have t := h.f0_lo; have := h.f0_hi; have := h.g0_lo; have := h.g0_hi
  have := h.f1_lo; have := h.f1_hi; have := h.g1_lo; have := h.g1_hi
  have hpos : (0 : ℤ) < 2 ^ k := by positivity
  refine ⟨by omega, h.odd, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact h.coprime.coprime_dvd_left (Nat.div_dvd_of_dvd (Nat.dvd_of_mod_eq_zero he))
  · rcases h.len with h0 | ⟨i, j, hi, hj, hij⟩
    · exact .inl (by omega)
    · rcases Nat.eq_zero_or_pos (a / 2) with h0 | hpos
      · exact .inl h0
      · refine .inr ⟨i - 1, j, ?_, hj, ?_⟩
        · have : 1 ≤ i := by
            rcases Nat.eq_zero_or_pos i with rfl | h; · simp at hi; omega
            · exact h
          have : 2 ^ i = 2 * 2 ^ (i - 1) := by
            rw [← pow_succ']; congr 1; omega
          omega
        · have : 1 ≤ i := by
            rcases Nat.eq_zero_or_pos i with rfl | h; · simp at hi; omega
            · exact h
          omega
  · have hc : ((a / 2 : ℕ) : ℤ) * 2 = a := by omega
    rw [pow_succ]; linear_combination (2 : ℤ) ^ k * hc + h.rel_a
  · rw [pow_succ]; linear_combination 2 * h.rel_b
  all_goals rw [pow_succ]; omega

/-- An odd `a >= b` becomes `(a - b) / 2`. -/
theorem GcdInv.odd_ge {A0 B0 S a b : ℕ} {f0 g0 f1 g1 : ℤ} {k : ℕ}
    (h : GcdInv A0 B0 S a b f0 g0 f1 g1 k) (hk : k < 63) (ho : a % 2 = 1) (hba : b ≤ a) :
    GcdInv A0 B0 S ((a - b) / 2) b (f0 - f1) (g0 - g1) (2 * f1) (2 * g1) (k + 1) := by
  have := h.f0_lo; have := h.f0_hi; have := h.g0_lo; have := h.g0_hi
  have := h.f1_lo; have := h.f1_hi; have := h.g1_lo; have := h.g1_hi
  have hb := h.odd
  refine ⟨by omega, h.odd, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have h1 : Nat.Coprime (a - b) b := (Nat.coprime_sub_self_left hba).mpr h.coprime
    exact h1.coprime_dvd_left (Nat.div_dvd_of_dvd (by omega))
  · rcases h.len with h0 | ⟨i, j, hi, hj, hij⟩
    · omega
    · rcases Nat.eq_zero_or_pos ((a - b) / 2) with h0 | hpos
      · exact .inl h0
      · have : 1 ≤ i := by
          rcases Nat.eq_zero_or_pos i with rfl | h; · simp at hi; omega
          · exact h
        have : 2 ^ i = 2 * 2 ^ (i - 1) := by
          rw [← pow_succ']; congr 1; omega
        exact .inr ⟨i - 1, j, by omega, hj, by omega⟩
  · have hc : (((a - b) / 2 : ℕ) : ℤ) * 2 = a - b := by omega
    rw [pow_succ]; linear_combination (2 : ℤ) ^ k * hc + h.rel_a - h.rel_b
  · rw [pow_succ]; linear_combination 2 * h.rel_b
  all_goals rw [pow_succ]; omega


open Aeneas Aeneas.Std CoreModels Plonky3Lean.Lib

/-- `i64::MIN` read as `2^63` gives back any value in `(-2^63, 2^63]` after wrapping. -/
theorem unwrapFactor_bmod (x : ℤ) (h1 : -2 ^ 63 < x) (h2 : x ≤ 2 ^ 63) :
    unwrapFactor (Int.bmod x (2 ^ 64)) = x := by
  unfold unwrapFactor
  rw [Int.bmod_def]
  split_ifs <;> omega

/-- A factor at most `2^62` is not `i64::MIN`. -/
theorem unwrapFactor_of_le {v : ℤ} {k : ℕ} (hk : k ≤ 62) (h : unwrapFactor v ≤ 2 ^ k) :
    unwrapFactor v = v := by
  have : (2 : ℤ) ^ k ≤ 2 ^ 62 := pow_le_pow_right₀ (by norm_num) hk
  unfold unwrapFactor at *
  split_ifs at * <;> omega

/-- The loop state of `gcd_inner`: `(a, b, f0, g0, f1, g1, round)`. -/
abbrev GcdState := Std.U64 × Std.U64 × Std.I64 × Std.I64 × Std.I64 × Std.I64 × Std.Usize

/-- `GcdInv` read off a loop state. -/
def GcdSt (A0 B0 S : ℕ) : GcdState → Prop
  | (a, b, f0, g0, f1, g1, k) =>
    GcdInv A0 B0 S a.val b.val f0.val g0.val (unwrapFactor f1.val) (unwrapFactor g1.val) k.val

/-- `GcdInv` after the last round, read off the loop result. -/
def GcdPost (A0 B0 S : ℕ) : Std.U64 × Std.U64 × Std.I64 × Std.I64 × Std.I64 × Std.I64 → Prop
  | (a, b, f0, g0, f1, g1) =>
    GcdInv A0 B0 S a.val b.val f0.val g0.val (unwrapFactor f1.val) (unwrapFactor g1.val) 63

/-- The state after a round, from the invariant on the values before `f1` and `g1` are doubled. -/
theorem gcdSt_of_round (A0 B0 S : ℕ) (a1 b1 : Std.U64) (f01 g01 f11 g11 f12 g12 : Std.I64)
    (k round1 : Std.Usize) (hk : k.val < 63) (hf1 : -2 ^ 62 < f11.val ∧ f11.val ≤ 2 ^ 62)
    (hg1 : -2 ^ 62 < g11.val ∧ g11.val ≤ 2 ^ 62)
    (h : GcdInv A0 B0 S a1.val b1.val f01.val g01.val (2 * f11.val) (2 * g11.val) (k.val + 1))
    (hf : f12.val = Int.bmod (f11.val <<< 1) I64.size)
    (hg : g12.val = Int.bmod (g11.val <<< 1) I64.size) (hr : round1.val = k.val + 1) :
    GcdSt A0 B0 S (a1, b1, f01, g01, f12, g12, round1) ∧ 63 - round1.val < 63 - k.val := by
  simp only [GcdSt]
  refine ⟨?_, by omega⟩
  have hs : I64.size = 2 ^ 64 := by simp [I64.size, I64.numBits]
  have e1 : unwrapFactor f12.val = 2 * f11.val := by
    rw [hf, Int.shiftLeft_eq, hs, show f11.val * 2 ^ 1 = 2 * f11.val by ring]
    exact unwrapFactor_bmod _ (by omega) (by omega)
  have e2 : unwrapFactor g12.val = 2 * g11.val := by
    rw [hg, Int.shiftLeft_eq, hs, show g11.val * 2 ^ 1 = 2 * g11.val by ring]
    exact unwrapFactor_bmod _ (by omega) (by omega)
  rw [e1, e2, hr]
  exact h

/-- One round of `gcd_inner` keeps the invariant and advances the round. -/
theorem gcd_inner_loop.body.spec (A0 B0 S : ℕ) (x : GcdState) (hx : GcdSt A0 B0 S x) :
    p3_util.gcd_inner_loop.body 63#usize x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2.1 x.2.2.2.2.2.1
      x.2.2.2.2.2.2 ⦃ r => match r with
        | .done y => GcdPost A0 B0 S y
        | .cont x' => GcdSt A0 B0 S x' ∧ 63 - x'.2.2.2.2.2.2.val < 63 - x.2.2.2.2.2.2.val ⦄ := by
  obtain ⟨a, b, f0, g0, f1, g1, k⟩ := x
  simp only [GcdSt] at hx
  unfold p3_util.gcd_inner_loop.body
  split
  · rename_i hk
    have hk' : k.val < 63 := by simpa using hk
    have h62 : (2 : ℤ) ^ k.val ≤ 2 ^ 62 := pow_le_pow_right₀ (by norm_num) (by omega)
    rw [unwrapFactor_of_le (k := k.val) (by omega) hx.f1_hi,
      unwrapFactor_of_le (k := k.val) (by omega) hx.g1_hi] at hx
    have := hx.f0_lo; have := hx.f0_hi; have := hx.g0_lo; have := hx.g0_hi
    have := hx.f1_lo; have := hx.f1_hi; have := hx.g1_lo; have := hx.g1_hi
    have hb := hx.odd
    step
    have hi : i.val = a.val % 2 := by
      rw [i_post, UScalar.val_and, show (1#u64).val = 1 from rfl, Nat.and_one_is_mod]
    clear i_post i_post1
    by_cases hi0 : i = 0#u64
    · have he : a.val % 2 = 0 := by rw [← hi, hi0]; rfl
      simp only [hi0, ite_true]
      step as ⟨a2, a2_post, _, _⟩
      step*
      refine gcdSt_of_round A0 B0 S _ _ _ _ _ _ _ _ _ _ hk' (by omega) (by omega) ?_
        f12_post g12_post round1_post
      rw [a2_post, Nat.shiftRight_eq_div_pow, pow_one]
      exact hx.even hk' he
    · have ho : a.val % 2 = 1 := by
        have : i.val ≠ 0 := fun h => hi0 (UScalar.eq_of_val_eq h)
        omega
      simp only [hi0, ite_false]
      by_cases hab : a < b
      · have hab' : a.val < b.val := hab
        have hs := hx.swap ho
        have := hs.odd
        simp only [hab, ite_true, CoreModels.core.mem.swap, Aeneas.Std.core.mem.swap]
        step as ⟨a3, ha3, _⟩
        step as ⟨a4, ha4, _, _⟩
        step as ⟨f03, hf03⟩
        step as ⟨g03, hg03⟩
        step*
        refine gcdSt_of_round A0 B0 S _ _ _ _ _ _ _ _ _ _ hk' (by omega) (by omega) ?_
          f12_post g12_post round1_post
        rw [ha4, Nat.shiftRight_eq_div_pow, pow_one, ha3, hf03, hg03]
        exact hs.odd_ge hk' hb hab'.le
      · have hab' : b.val ≤ a.val := by
          have : ¬ a.val < b.val := hab
          omega
        simp only [hab, ite_false]
        step as ⟨a3, ha3, _⟩
        step as ⟨a4, ha4, _, _⟩
        step as ⟨f03, hf03⟩
        step as ⟨g03, hg03⟩
        step*
        refine gcdSt_of_round A0 B0 S _ _ _ _ _ _ _ _ _ _ hk' (by omega) (by omega) ?_
          f12_post g12_post round1_post
        rw [ha4, Nat.shiftRight_eq_div_pow, pow_one, ha3, hf03, hg03]
        exact hx.odd_ge hk' ho hab'
  · rename_i hk
    have hk' : k.val = 63 := by have := hx.k_le; simp at hk; omega
    simp only [WP.spec_ok, GcdPost]
    rw [← hk']; exact hx


/-- `gcd_inner::<63>(a, b)` never fails, and its outputs satisfy the invariant after 63 rounds.

The inputs must satisfy the invariant at round 0.

That is: `b` odd, `a` and `b` coprime, and both within the bit budget `S`. -/
theorem gcd_inner.spec (a b : Std.U64) (S : ℕ) (hodd : b.val % 2 = 1)
    (hcop : Nat.Coprime a.val b.val)
    (hlen : a.val = 0 ∨ ∃ i j, a.val < 2 ^ i ∧ b.val < 2 ^ j ∧ i + j ≤ S) :
    p3_util.gcd_inner 63#usize a b ⦃ r =>
      GcdInv a.val b.val S r.2.1.val r.2.2.val r.1.1.val r.1.2.1.val (unwrapFactor r.1.2.2.1.val)
        (unwrapFactor r.1.2.2.2.val) 63 ⦄ := by
  unfold p3_util.gcd_inner p3_util.gcd_inner_loop
  have hloop := loop.spec_decr_nat (fun x : GcdState => 63 - x.2.2.2.2.2.2.val)
    (GcdSt a.val b.val S) (GcdPost a.val b.val S)
    (fun x : GcdState => p3_util.gcd_inner_loop.body 63#usize x.1 x.2.1 x.2.2.1 x.2.2.2.1
      x.2.2.2.2.1 x.2.2.2.2.2.1 x.2.2.2.2.2.2)
    (a, b, 1#i64, 0#i64, 0#i64, 1#i64, 0#usize)
    (fun x hx => WP.spec_mono (gcd_inner_loop.body.spec a.val b.val S x hx)
      (fun r h => by cases r <;> exact h)) ?_
  · have heq : (fun x : GcdState => match x with
        | (a1, b1, f01, g01, f11, g11, round1) =>
          p3_util.gcd_inner_loop.body 63#usize a1 b1 f01 g01 f11 g11 round1) =
        (fun x : GcdState => p3_util.gcd_inner_loop.body 63#usize x.1 x.2.1 x.2.2.1 x.2.2.2.1
          x.2.2.2.2.1 x.2.2.2.2.2.1 x.2.2.2.2.2.2) := by
      funext x; obtain ⟨_, _, _, _, _, _, _⟩ := x; rfl
    rw [heq]
    refine WP.spec_bind hloop ?_
    rintro ⟨a1, b1, f0, g0, f1, g1⟩ hy
    simpa [GcdPost] using hy
  · simp only [GcdSt]
    refine ⟨by simp, hodd, hcop, by simpa using hlen, by simp, by simp [unwrapFactor], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp [unwrapFactor]

open Plonky3Lean.Spec.Goldilocks p3_goldilocks

/-- `from_unusual_int` stands for its input, with `i64::MIN` read as `2^63`. -/
theorem from_unusual_int.spec (int : Std.I64) :
    goldilocks.from_unusual_int int ⦃ r =>
      (r.value.val : Goldilocks.Field) = (unwrapFactor int.val : Goldilocks.Field) ⦄ := by
  unfold goldilocks.from_unusual_int
  rw [ORDER_U64.eq]
  have hb := int.hBounds
  simp only [IScalarTy.I64_numBits_eq] at hb
  have hmin : CoreModels.core.num.I64.MIN.val = -2 ^ 63 := rfl
  split
  · rename_i h
    simp only [ge_iff_le, IScalar.le_equiv, show (0#i64).val = 0 from rfl] at h
    simp only [lift]
    step*
    rw [r_post, IScalar.hcast_val_eq, UScalarTy.U64_numBits_eq, Int.emod_eq_of_lt h (by omega)]
    have : ((int.val.toNat : ℕ) : ℤ) = int.val := Int.toNat_of_nonneg h
    rw [unwrapFactor, ite_eq_right (by omega), ← this]; push_cast; rfl
  · rename_i h
    simp only [ge_iff_le, IScalar.le_equiv, not_le, show (0#i64).val = 0 from rfl] at h
    split
    · rename_i hm
      have hv : int.val = -2 ^ 63 := by rw [hm, hmin]
      simp only [lift]
      step*
      rw [r_post, IScalar.hcast_val_eq, UScalarTy.U64_numBits_eq, hv, unwrapFactor, ite_eq_left rfl]
      rfl
    · rename_i hm
      have hv : int.val ≠ -2 ^ 63 := fun h' => hm (IScalar.eq_of_val_eq (by rw [h', hmin]))
      step*
      rename r.value = _ => r_post
      have hv' : (i.val : ℤ) = 18446744069414584321 + int.val := by
        rw [i_post]; push_cast; rw [Int.emod_eq_of_lt (by omega) (by omega)]
      have : ((i.val : ℕ) : Goldilocks.Field) = (((i.val : ℕ) : ℤ) : Goldilocks.Field) :=
        (Int.cast_natCast _).symm
      rw [r_post, this, hv', unwrapFactor, ite_eq_right hv]; push_cast; rw [p_eq_zero, zero_add]

/-- After both rounds of 63 the remaining `b` is `1`. -/
theorem gcd_final_b {a b S : ℕ} {f0 g0 f1 g1 : ℤ} (A0 B0 : ℕ)
    (h : GcdInv A0 B0 S a b f0 g0 f1 g1 63) (hS : S ≤ 65) : b = 1 := by
  have hb := h.odd
  rcases Nat.eq_zero_or_pos a with ha | ha
  · have := h.coprime; rw [ha, Nat.coprime_zero_left] at this; exact this
  rcases h.len with h0 | ⟨i, j, hi, hj, hij⟩
  · omega
  · have hi1 : 1 ≤ i := by
      rcases Nat.eq_zero_or_pos i with rfl | hp
      · simp at hi; omega
      · exact hp
    have hj1 : j ≤ 1 := by omega
    have : b < 2 := lt_of_lt_of_le hj (by
      calc 2 ^ j ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) hj1
        _ = 2 := rfl)
    omega

/-- `p` is prime. -/
theorem p_prime : Nat.Prime 18446744069414584321 := Goldilocks.is_prime

/-- `gcd_inversion` inverts every nonzero input, canonical or not. -/
theorem gcd_inversion.spec (x : goldilocks.Goldilocks) (hx : x.value.val % 18446744069414584321 ≠ 0) :
    goldilocks.gcd_inversion x ⦃ r =>
      (r.value.val : Goldilocks.Field) * (x.value.val : Goldilocks.Field) = 1 ⦄ := by
  unfold goldilocks.gcd_inversion
  have hP : goldilocks.P = 18446744069414584321#u64 := by unfold goldilocks.P; rfl
  rw [hP]
  have hpv : (18446744069414584321#u64).val = 18446744069414584321 := rfl
  have hcop : Nat.Coprime x.value.val (18446744069414584321#u64).val := by
    rw [hpv, Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd p_prime]
    exact fun h => hx (Nat.mod_eq_zero_of_dvd h)
  have hlen : x.value.val = 0 ∨ ∃ i j, x.value.val < 2 ^ i ∧
      (18446744069414584321#u64).val < 2 ^ j ∧ i + j ≤ 128 :=
    .inr ⟨64, 64, u64_lt _, by rw [hpv]; norm_num, le_refl _⟩
  apply WP.spec_bind (gcd_inner.spec _ _ 128 (by rw [hpv]) hcop hlen)
  rintro ⟨⟨f00, g00, f10, g10⟩, a1, b1⟩ h1
  simp only at h1
  have hlen2 : a1.val = 0 ∨ ∃ i j, a1.val < 2 ^ i ∧ b1.val < 2 ^ j ∧ i + j ≤ 65 := by
    rcases h1.len with h0 | ⟨i, j, hi, hj, hij⟩
    · exact .inl h0
    · exact .inr ⟨i, j, hi, hj, by omega⟩
  apply WP.spec_bind (gcd_inner.spec _ _ 65 h1.odd h1.coprime hlen2)
  rintro ⟨⟨f01, g01, f11, g11⟩, a2, b2⟩ h2
  simp only at h2
  have hb2 := gcd_final_b _ _ h2 (le_refl _)
  have r1 := h1.rel_a
  have r2 := h1.rel_b
  have r3 := h2.rel_b
  rw [hb2] at r3
  have hf00 : unwrapFactor f00.val = f00.val := by
    unfold unwrapFactor; have := h1.f0_lo; split_ifs <;> omega
  apply WP.spec_bind (from_unusual_int.spec f00); intro u hu
  apply WP.spec_bind (from_unusual_int.spec f10); intro v hv
  apply WP.spec_bind (from_unusual_int.spec f11); intro uf huf
  apply WP.spec_bind (from_unusual_int.spec g11); intro vf hvf
  apply WP.spec_bind (mul.field u uf); intro g hg
  apply WP.spec_bind (mul.field v vf); intro g1 hg1
  apply WP.spec_bind (add.field g g1); intro g2 hg2
  apply WP.spec_mono (mul_2exp_u64.spec g2 66#u64)
  intro r hr
  rw [hpv] at r1 r2
  -- The Bezout relation, read in the field, where `p = 0`.
  have key : (2 : Goldilocks.Field) ^ 126 =
      ((f00.val : Goldilocks.Field) * (unwrapFactor f11.val : Goldilocks.Field) +
        (unwrapFactor f10.val : Goldilocks.Field) * (unwrapFactor g11.val : Goldilocks.Field)) *
        (x.value.val : Goldilocks.Field) := by
    have hZ : (2 : ℤ) ^ 63 * 2 ^ 63 = (f00.val * unwrapFactor f11.val + unwrapFactor f10.val *
        unwrapFactor g11.val) * x.value.val + 18446744069414584321 * (g00.val *
        unwrapFactor f11.val + unwrapFactor g10.val * unwrapFactor g11.val) := by
      linear_combination (2 : ℤ) ^ 63 * r3 + unwrapFactor f11.val * r1 + unwrapFactor g11.val * r2
    have := congrArg (Int.cast : ℤ → Goldilocks.Field) hZ
    simp only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_ofNat, Int.cast_natCast] at this
    rw [p_eq_zero, zero_mul, add_zero, ← pow_add] at this
    exact this
  rw [hr, hg2, hg, hg1, hu, hv, huf, hvf, hf00, show (66#u64).val = 66 from rfl]
  calc _ = (2 : Goldilocks.Field) ^ 66 * (((f00.val : Goldilocks.Field) * unwrapFactor f11.val +
        unwrapFactor f10.val * unwrapFactor g11.val) * x.value.val) := by ring
    _ = 1 := by rw [← key, ← pow_add]; exact two_pow_192

/-- `try_inverse` returns `None` on zero and the inverse otherwise, for every stored `u64`. -/
theorem try_inverse.spec (x : goldilocks.Goldilocks) :
    goldilocks.Goldilocks.Insts.P3_fieldFieldField.try_inverse x ⦃ r =>
      match r with
      | .None => toField x = 0
      | .Some y => toField y * toField x = 1 ⦄ := by
  unfold goldilocks.Goldilocks.Insts.P3_fieldFieldField.try_inverse
  apply WP.spec_bind (is_zero.spec x)
  intro b hb
  rw [hb]
  by_cases h : x.value.val % 18446744069414584321 = 0
  · simp only [h, decide_true, ite_true, WP.spec_ok]
    unfold toField
    have := natCast_eq_of_mod (x := x.value.val) (y := 0) (by rw [h])
    simpa using this
  · simp only [h, decide_false, Bool.false_eq_true, ite_false]
    apply WP.spec_bind (gcd_inversion.spec x h)
    intro y hy
    simp only [WP.spec_ok]
    exact hy

end Plonky3Lean.Proofs.P3Goldilocks
