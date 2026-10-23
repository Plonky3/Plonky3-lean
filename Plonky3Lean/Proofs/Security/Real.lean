module

public import Mathlib

@[expose] public section

/-!
# p3-security's floating-point bounds, over the reals, against their sources

# Overview

aeneas does not translate floating-point arithmetic (docs/extractor-issues.md, item 19).

So each definition ending in `R` below transcribes one Rust expression exactly as written.

The Rust's library calls are read as follows:

```text
    libm::log2(x)    ->  log_2 x
    libm::pow(2, x)  ->  2^x
    libm::sqrt(x)    ->  sqrt(x)
```

`crates/security/crate.toml` lists each transcription as a `[[mirror]]` entry.

Floating-point rounding is not modelled.

# The bounds from the papers

- The DEEP round costs `L * D / |F|`, for a decoding list of size `L`.
  This is Haböck's FRI summary (eprint 2022/1216), Theorem 8 and Remark 9.
  It decodes the trace and the quotient jointly, as one interleaved word.
- A looser analysis gives `L^2 * D / |F|`.
  This is ethSTARK (eprint 2021/582), Theorem 5, and eprint 2024/1553, Theorem 2.
  The square comes from a union bound over pairs of trace and quotient codewords.
- A folding round costs `(t - 1) * (zeta + (2m + 1)(n + 1) / (sqrt(rho) |F|))`, a sum.
  This is from the same two theorems.
- DKT26 (eprint 2026/2056), Theorem 5.12, bounds a folding round by its curve count alone.
  This uses full agreement sets.
- A WHIR folding round costs `d * L / |F| + err^*`, again a sum.
  This is WHIR (eprint 2024/1586), Theorem 5.2.
- The proximity parameter `m` needs `eta = sqrt(rho) (1 + 1/(2m)) - sqrt(rho^+) > 0`.
  This is the precondition of ethSTARK, Theorem 1.
-/

open Real

namespace Plonky3Lean.Proofs.Security.Real

/-! ## Bits -/

/-- `t < q - log_2 x` exactly when `x < 2^(q - t)`. -/
theorem lt_sub_logb_iff (q t x : ℝ) (hx : 0 < x) : t < q - logb 2 x ↔ x < (2 : ℝ) ^ (q - t) := by
  rw [← Real.logb_lt_iff_lt_rpow (by norm_num) hx]; constructor <;> intro h <;> linarith

/-- The bits of an error `e`: `-log_2 e`, the unit p3-security reports in. -/
noncomputable def bits (ε : ℝ) : ℝ := -logb 2 ε

theorem bits_mul (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : bits (a * b) = bits a + bits b := by
  simp only [bits, Real.logb_mul ha.ne' hb.ne']; ring

theorem logb_lt_of_lt (x : ℝ) (n : ℕ) (hx : 0 < x) (h : x < 2 ^ n) : logb 2 x < n := by
  rw [Real.logb_lt_iff_lt_rpow (by norm_num) hx, Real.rpow_natCast]; exact h

theorem logb_neg_of_lt_one (x : ℝ) (hx : 0 < x) (h : x < 1) : logb 2 x < 0 :=
  Real.logb_neg (by norm_num) hx h

/-! ## DEEP-ALI -/

/-- The DEEP round's bits, before the Rust clamps them at zero.

Here `q` is the field size in bits, `L` the list size and `D` the identity degree. -/
noncomputable def deepBitsR (q L D : ℝ) : ℝ := q - logb 2 L - logb 2 D

/-- The DEEP round's error in the looser analysis: `L^2 * D / |F|`.

This is ethSTARK, Theorem 5, item 2, and eprint 2024/1553, Theorem 2, item 2.

The papers divide by `|F|` minus the size of the union of the evaluation and trace domains.

Dividing by `|F|` only lowers the error, so every lower bound below holds for the papers too. -/
noncomputable def deepErrPaper (q L D : ℝ) : ℝ := L ^ 2 * D / 2 ^ q

/-- **The Rust charges `L`, as Haböck's Theorem 8 does, where the looser analysis charges `L^2`.**

For every list size `L > 0`, the Rust reports exactly `log_2 L` more bits than the `L^2` bound. -/
theorem deepBitsR_eq (q L D : ℝ) (hL : 0 < L) (hD : 0 < D) :
    deepBitsR q L D = bits (deepErrPaper q L D) + logb 2 L := by
  unfold deepBitsR bits deepErrPaper
  rw [Real.logb_div (by positivity) (by positivity), Real.logb_mul (by positivity) hD.ne',
    Real.logb_pow, Real.logb_rpow (by norm_num) (by norm_num)]
  push_cast; ring

/-- The list size in the list-decoding regime: `(m + 1/2) / sqrt(rho)`. -/
noncomputable def listSizeLdrR (logBlowup m : ℕ) : ℝ :=
  ((m : ℝ) + 0.5) / √((2 : ℝ) ^ (-(logBlowup : ℝ)))

/-- The identity degree of the DEEP round, for a trace of length `k`.

```text
    D = max(deg * (k + combo - 1) + (k - 1),  (chunks + 1) * k + combo - 1,  1)
```
-/
noncomputable def deepFactorR (k maxDeg combo chunks : ℝ) : ℝ :=
  max (max (maxDeg * (k + combo - 1) + (k - 1)) ((chunks + 1) * k + combo - 1)) 1

theorem listSizeLdrR_3_3 : listSizeLdrR 3 3 = 7 / 2 * √8 := by
  have h : (2 : ℝ) ^ (-((3 : ℕ) : ℝ)) = 1 / 8 := by
    rw [Real.rpow_neg (by norm_num)]; norm_num
  rw [listSizeLdrR, h, Real.sqrt_div' _ (by norm_num : (0 : ℝ) ≤ 8)]
  rw [Real.sqrt_one]; field_simp; norm_num

/-- A degree-3 AIR over a `2^24` trace, two opening points and two chunks has `D = 2^26 + 2`. -/
theorem deepFactorR_cex : deepFactorR (2 ^ 24) 3 2 2 = 2 ^ 26 + 2 := by
  unfold deepFactorR; norm_num

/-- **A DEEP term where the two analyses differ.**

The Rust reads more than 94 bits for the DEEP round.

The looser `L^2` error, at the Rust's own list size, exceeds `2^-92`.

```text
    degree-3 AIR, 2^24 trace, two opening points, two quotient chunks
    blowup 8, m = 3
    124-bit field (BabyBear's quartic extension)
```
-/
theorem deep_cex :
    94 < deepBitsR 124 (listSizeLdrR 3 3) (deepFactorR (2 ^ 24) 3 2 2) ∧
      (2 : ℝ) ^ (-92 : ℝ) < deepErrPaper 124 (listSizeLdrR 3 3) (deepFactorR (2 ^ 24) 3 2 2) := by
  rw [listSizeLdrR_3_3, deepFactorR_cex]
  have h8 : √8 ^ 2 = 8 := Real.sq_sqrt (by norm_num)
  have hs : 0 < √8 := by positivity
  constructor
  · rw [deepBitsR, sub_sub, ← Real.logb_mul (by positivity) (by positivity)]
    rw [show (94 : ℝ) < 124 - logb 2 (7 / 2 * √8 * (2 ^ 26 + 2)) ↔
        7 / 2 * √8 * (2 ^ 26 + 2) < (2 : ℝ) ^ ((124 : ℝ) - 94) from
      lt_sub_logb_iff _ _ _ (by positivity)]
    rw [show ((124 : ℝ) - 94) = ((30 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    have : √8 < 3 := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
    nlinarith
  · rw [deepErrPaper, mul_pow, h8]
    rw [show (-92 : ℝ) = 32 - 124 by norm_num, Real.rpow_sub (by norm_num),
      show ((32 : ℝ)) = ((32 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    apply div_lt_div_of_pos_right _ (by positivity)
    norm_num

/-! ## The rest of the list-decoding composite at the same parameters -/

/-- The constraint-composition round's bits, before the Rust clamps them at zero. -/
noncomputable def aliBitsR (q L C : ℝ) : ℝ := q - logb 2 L - logb 2 C

/-- The proximity parameter in the list-decoding regime: `(1 + 1/(2m)) sqrt(rho)`. -/
noncomputable def alphaLdrR (logBlowup m : ℕ) : ℝ :=
  (1 + 0.5 / (m : ℝ)) * √((2 : ℝ) ^ (-(logBlowup : ℝ)))

/-- The query phase's bits: `pow - log_2(alpha^s)`, for `s` queries. -/
noncomputable def queryBitsR (α : ℝ) (s pow : ℕ) : ℝ := pow - logb 2 (α ^ (s : ℝ))

/-- The `log_2` of the Johnson exceptional line count.

This is the branch for a positive log degree, a positive log inverse rate, and `m >= 3`. -/
noncomputable def johnsonLineLogR (ld lr m : ℕ) : ℝ :=
  3 + ((ld : ℝ) + lr) + 3 * logb 2 ((m : ℝ) + 0.5) - logb 2 3 -
    (logb 2 (1 - (2 : ℝ) ^ (-(ld : ℝ))) - lr)

/-- The commit phase's bits in the list-decoding regime.

It is the minimum of the line-MCA bound and the `n / |F|` bound.

This is the positive-gamma branch, before the Rust clamps it at zero. -/
noncomputable def commitLdrBitsR (q : ℝ) (ld lr m arity cpow : ℕ) : ℝ :=
  let f : ℝ := 2 ^ arity
  let L : ℝ := (ld : ℝ) + lr
  min (q - johnsonLineLogR ld lr m - logb 2 (f - 1) + cpow)
    (q - logb 2 f - (L + logb 2 (1 + (2 : ℝ) ^ (-L))) - logb 2 (2 * (m : ℝ) + 1) +
      0.5 * logb 2 ((2 : ℝ) ^ (-(lr : ℝ))) + cpow)

/-- The bits of a proven regime.

It is the minimum of the composition round, DEEP, the low-degree test and the collision cap. -/
noncomputable def regimeBitsR (ali deep ldt coll : ℝ) : ℝ := min (min ali deep) (min ldt coll)

theorem two_rpow_neg (x : ℕ) : (2 : ℝ) ^ (-(x : ℝ)) = 1 / 2 ^ x := by
  rw [Real.rpow_neg (by norm_num), Real.rpow_natCast]; ring

/-- The query phase reads more than 94 bits.

The parameters are blowup 8, `m = 3`, and 70 queries with 16 bits of grinding. -/
theorem query_cex : 94 < queryBitsR (alphaLdrR 3 3) 70 16 := by
  have h : (2 : ℝ) ^ (-((3 : ℕ) : ℝ)) = 1 / 8 := by rw [two_rpow_neg]; norm_num
  have hα : alphaLdrR 3 3 = 7 / 6 * √(1 / 8) := by rw [alphaLdrR, h]; norm_num
  have hpos : 0 < alphaLdrR 3 3 := by rw [hα]; positivity
  rw [queryBitsR, Real.rpow_natCast]
  have hsq : alphaLdrR 3 3 ^ 2 = 49 / 288 := by
    rw [hα, mul_pow, Real.sq_sqrt (by norm_num)]; norm_num
  have h70 : alphaLdrR 3 3 ^ 70 = (49 / 288) ^ 35 := by rw [← hsq, ← pow_mul]
  rw [h70]
  have : logb 2 ((49 / 288 : ℝ) ^ 35) < -78 := by
    rw [Real.logb_lt_iff_lt_rpow (by norm_num) (by positivity), Real.rpow_neg (by norm_num),
      show ((78 : ℝ)) = ((78 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    norm_num
  push_cast; linarith

/-- The commit phase reads more than 94 bits.

```text
    2^24 trace, blowup 8, binary folding, m = 3
    20 bits of commit grinding, 124-bit field
```
-/
theorem commit_cex : 94 < commitLdrBitsR 124 24 3 3 1 20 := by
  have h24 : (2 : ℝ) ^ (-((24 : ℕ) : ℝ)) = 1 / 2 ^ 24 := two_rpow_neg 24
  have h3 : logb 2 ((3 : ℕ) + 0.5 : ℝ) < 2 := by
    have := logb_lt_of_lt ((3 : ℕ) + 0.5 : ℝ) 2 (by norm_num) (by norm_num); exact_mod_cast this
  have hl3 : 0 < logb 2 (3 : ℝ) := Real.logb_pos (by norm_num) (by norm_num)
  have hlr : -1 < logb 2 (1 - (2 : ℝ) ^ (-((24 : ℕ) : ℝ))) := by
    rw [h24, Real.lt_logb_iff_rpow_lt (by norm_num) (by norm_num)]; norm_num
  unfold commitLdrBitsR johnsonLineLogR
  simp only [pow_one, show (2 : ℝ) - 1 = 1 by norm_num, Real.logb_one]
  have hL : logb 2 (1 + (2 : ℝ) ^ (-(((24 : ℕ) : ℝ) + ((3 : ℕ) : ℝ)))) < 1 := by
    have : (2 : ℝ) ^ (-(((24 : ℕ) : ℝ) + ((3 : ℕ) : ℝ))) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
    have h0 : 0 < (2 : ℝ) ^ (-(((24 : ℕ) : ℝ) + ((3 : ℕ) : ℝ))) := by positivity
    rw [Real.logb_lt_iff_lt_rpow (by norm_num) (by linarith), Real.rpow_one]
    linarith
  have h7 : logb 2 (2 * ((3 : ℕ) : ℝ) + 1) < 3 := by
    have := logb_lt_of_lt (2 * ((3 : ℕ) : ℝ) + 1) 3 (by norm_num) (by norm_num); exact_mod_cast this
  have hr : logb 2 ((2 : ℝ) ^ (-((3 : ℕ) : ℝ))) = -3 := by
    rw [Real.logb_rpow (by norm_num) (by norm_num)]; norm_num
  have h2 : logb 2 (2 : ℝ) = 1 := Real.logb_self_eq_one (by norm_num)
  rw [hr, h2]
  push_cast at *
  apply lt_min <;> norm_num at * <;> linarith

theorem ali_cex : 94 < aliBitsR 124 (listSizeLdrR 3 3) 10 := by
  rw [listSizeLdrR_3_3, aliBitsR, sub_sub, ← Real.logb_mul (by positivity) (by norm_num),
    lt_sub_logb_iff _ _ _ (by positivity),
    show ((124 : ℝ) - 94) = ((30 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have : √8 < 3 := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
  nlinarith

/-- **The list-decoding regime the Rust reports, against the looser `L^2` bound.**

Every term of the Rust's list-decoding regime at `m = 3` exceeds 94 bits.

So the regime reads more than 94 bits.

The DEEP round alone, under the `L^2` bound, has error above `2^-92`.

```text
    the DEEP parameters above, plus:
    10 constraints
    70 queries with 16 bits of query grinding
    binary folding with 20 bits of commit grinding
    128-bit hash

    Rust regime:            above 94 bits  (94.69 in p3-security's regression test)
    L^2 DEEP error:         above 2^-92
```
-/
theorem ldr_regime_cex :
    94 < regimeBitsR (aliBitsR 124 (listSizeLdrR 3 3) 10)
        (deepBitsR 124 (listSizeLdrR 3 3) (deepFactorR (2 ^ 24) 3 2 2))
        (min (commitLdrBitsR 124 24 3 3 1 20) (queryBitsR (alphaLdrR 3 3) 70 16)) 128 ∧
      (2 : ℝ) ^ (-92 : ℝ) < deepErrPaper 124 (listSizeLdrR 3 3) (deepFactorR (2 ^ 24) 3 2 2) := by
  refine ⟨?_, deep_cex.2⟩
  unfold regimeBitsR
  exact lt_min (lt_min ali_cex deep_cex.1) (lt_min (lt_min commit_cex query_cex) (by norm_num))

/-! ## Two errors of one round: a sum, not a maximum -/

/-- The larger of two positive errors reads more bits than their sum.

In bits, the larger error is the minimum of the two bit counts.

The excess is `log_2(1 + small/large)`, at most one bit. -/
theorem min_bits_gt_bits_add (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    bits (a + b) < min (bits a) (bits b) ∧ min (bits a) (bits b) ≤ bits (a + b) + 1 := by
  unfold bits
  have h2 : (1 : ℝ) = logb 2 2 := (Real.logb_self_eq_one (by norm_num)).symm
  constructor
  · apply lt_min
    · have := Real.logb_lt_logb (by norm_num : (1 : ℝ) < 2) ha (by linarith : a < a + b); linarith
    · have := Real.logb_lt_logb (by norm_num : (1 : ℝ) < 2) hb (by linarith : b < a + b); linarith
  · rcases le_total a b with h | h
    · have := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) (by positivity)
        (by linarith : a + b ≤ 2 * b)
      rw [Real.logb_mul (by norm_num) hb.ne', ← h2] at this
      exact le_trans (min_le_right _ _) (by linarith)
    · have := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) (by positivity)
        (by linarith : a + b ≤ 2 * a)
      rw [Real.logb_mul (by norm_num) ha.ne', ← h2] at this
      exact le_trans (min_le_left _ _) (by linarith)

/-- A list-decoding folding round has two terms in the Rust.

- The curve-MCA count, `(f - 1) * C / |F|`.
- The term `f (2m + 1)(n + 1) / (sqrt(rho) |F|)`.

The Rust takes the smaller of the two bit counts, so it reports only the larger error.

With the full agreement sets of DKT26, Theorem 5.12, the curve count alone bounds the round.

So the larger error is a valid, conservative bound. -/
theorem commit_ldr_is_max (q : ℝ) (ld lr m arity cpow : ℕ) :
    commitLdrBitsR q ld lr m arity cpow =
      min (q - johnsonLineLogR ld lr m - logb 2 ((2 : ℝ) ^ arity - 1) + cpow)
        (q - logb 2 ((2 : ℝ) ^ arity) - (((ld : ℝ) + lr) + logb 2 (1 + (2 : ℝ) ^ (-((ld : ℝ) + lr)))) -
          logb 2 (2 * (m : ℝ) + 1) + 0.5 * logb 2 ((2 : ℝ) ^ (-(lr : ℝ))) + cpow) := rfl

/-- The grinding bits a WHIR folding round adds to reach the target `lambda`.

The Rust measures the gap from the smaller of the proximity-gap and fold-sumcheck bits. -/
noncomputable def foldingPowBitsR (lam proxBits sumcheckBits : ℝ) : ℝ :=
  max 0 (lam - min proxBits sumcheckBits)

/-- WHIR, Theorem 5.2, bounds a folding round by the sum of its sumcheck and proximity-gap errors.

The Rust's grinding reaches `lambda` against the larger error only.

So the round lands below `lambda` when both errors are positive and grinding is needed.

The shortfall is less than one bit. -/
theorem foldingPowBitsR_short (lam a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hneed : min (bits a) (bits b) < lam) :
    bits (a + b) + foldingPowBitsR lam (bits a) (bits b) < lam := by
  have := (min_bits_gt_bits_add a b ha hb).1
  unfold foldingPowBitsR
  rw [max_eq_right (by linarith)]
  linarith

/-! ## Unique decoding and the commit phase -/

/-- The commit phase's bits in the unique-decoding regime, before the Rust clamps them at zero.

Here `n` is the size of the evaluation domain and `f` the folding factor. -/
noncomputable def commitUdrBitsR (q n f pow : ℝ) : ℝ := q - logb 2 ((f - 1) * (n + 1)) + pow

/-- A folding round of degree `t` costs `(t - 1)(n + 1) / |F|`.

This is eprint 2024/1553, Theorem 3, item 4.

Grinding then adds its bits.

The Rust charges the largest arity `f >= t` at the largest domain, so it never reports more. -/
theorem commitUdr_le_paper (q n f t pow : ℝ) (hn : 0 < n) (ht : 1 < t) (htf : t ≤ f) :
    commitUdrBitsR q n f pow ≤ bits ((t - 1) * (n + 1) / 2 ^ q) + pow := by
  unfold commitUdrBitsR bits
  rw [Real.logb_div (by nlinarith) (by positivity), Real.logb_rpow (by norm_num) (by norm_num)]
  have := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) (by nlinarith)
    (by nlinarith : (t - 1) * (n + 1) ≤ (f - 1) * (n + 1))
  linarith

/-! ## Union bounds -/

/-- The union bound of terms of `b_i` bits each: `-log_2 (sum_i 2^(-b_i))`. -/
noncomputable def sumBitsR (l : List ℝ) : ℝ := bits (l.map (fun b => (2 : ℝ) ^ (-b))).sum

/-- The union bound is at most every term.

So composing rounds by it never reports more than the weakest one. -/
theorem sumBitsR_le (l : List ℝ) (b : ℝ) (hb : b ∈ l) : sumBitsR l ≤ b := by
  unfold sumBitsR bits
  have hpos : ∀ x ∈ l.map (fun b => (2 : ℝ) ^ (-b)), 0 ≤ x := by
    intro x hx; simp only [List.mem_map] at hx; obtain ⟨c, -, rfl⟩ := hx; positivity
  have hmem : (2 : ℝ) ^ (-b) ∈ l.map (fun b => (2 : ℝ) ^ (-b)) := List.mem_map_of_mem hb
  have hle := List.single_le_sum hpos _ hmem
  have := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) (by positivity) hle
  rw [Real.logb_rpow (by norm_num) (by norm_num)] at this
  linarith

/-! ## LogUp -/

/-- The LogUp round charges `N (W + 2) / |EF|`.

That is the numerator root, `N (W + 1)`, plus the vanishing denominator, `N`. -/
theorem logup_numerator (N W : ℕ) : N * (W + 1) + N = N * (W + 2) := by ring

/-! ## The Johnson line count -/

/-- The Johnson exceptional line count is the `log_2` of DKT26, Theorem 5.12.

```text
    count = 8 n (m + 1/2)^3 / (3 rho^-),   n = 2^(ld + lr),   rho^- = (2^ld - 1) / n
```
-/
theorem johnsonLineLogR_eq (ld lr m : ℕ) (hld : 0 < ld) :
    johnsonLineLogR ld lr m =
      logb 2 (8 * 2 ^ (ld + lr) * ((m : ℝ) + 0.5) ^ 3 / (3 * ((2 ^ ld - 1) / 2 ^ (ld + lr)))) := by
  have hk : (1 : ℝ) < 2 ^ ld := one_lt_pow₀ (by norm_num) hld.ne'
  have hk' : (0 : ℝ) < 2 ^ ld - 1 := by linarith
  have hr : (2 : ℝ) ^ (-(ld : ℝ)) = 1 / 2 ^ ld := two_rpow_neg ld
  unfold johnsonLineLogR
  rw [hr, show (1 : ℝ) - 1 / 2 ^ ld = (2 ^ ld - 1) / 2 ^ ld by field_simp,
    Real.logb_div hk'.ne' (by positivity)]
  conv_rhs => rw [Real.logb_div (by positivity) (by positivity),
    Real.logb_mul (by positivity) (by positivity), Real.logb_mul (by norm_num) (by positivity),
    Real.logb_mul (by norm_num) (by positivity), Real.logb_div hk'.ne' (by positivity)]
  simp only [Real.logb_pow, show (8 : ℝ) = 2 ^ 3 by norm_num, Real.logb_self_eq_one
    (by norm_num : (1 : ℝ) < 2)]
  push_cast; ring

/-! ## The largest admissible `m` -/

/-- The real number whose floor is the largest admissible `m`.

```text
    X = 1 / (2 (sqrt((h + c) / h) - 1))
```
-/
noncomputable def upperX (h c : ℝ) : ℝ := 1 / (2 * (√((h + c) / h) - 1))

/-- The precondition of ethSTARK, Theorem 1, at proximity parameter `m`.

```text
    eta = sqrt(rho) (1 + 1/(2m)) - sqrt(rho^+) > 0,   rho = h / n,   rho^+ = (h + c) / n
```
-/
def EtaPos (h c n m : ℝ) : Prop := √(h + c) / √n < √h / √n * (1 + 1 / (2 * m))

/-- **`m < X` is exactly the precondition `eta > 0`**, for every `m > 0`. -/
theorem lt_upperX_iff (h c n m : ℝ) (hh : 0 < h) (hc : 0 < c) (hn : 0 < n) (hm : 0 < m) :
    m < upperX h c ↔ EtaPos h c n m := by
  have hs : √((h + c) / h) = √(h + c) / √h := Real.sqrt_div' _ hh.le
  have h1 : 1 < √((h + c) / h) := by
    rw [Real.lt_sqrt (by norm_num), one_pow, one_lt_div hh]; linarith
  have hsh : 0 < √h := Real.sqrt_pos.mpr hh
  have hsn : 0 < √n := Real.sqrt_pos.mpr hn
  have hs' : √(h + c) = √(h + c) / √h * √h := by field_simp
  unfold upperX EtaPos
  rw [hs, hs']
  rw [hs] at h1
  set t := √(h + c) / √h
  have hk : 0 < √h / √n := div_pos hsh hsn
  have e : t * √h / √h = t := by field_simp
  rw [e, show t * √h / √n = √h / √n * t by ring, mul_lt_mul_iff_of_pos_left hk,
    lt_div_iff₀ (by linarith)]
  have key : t < 1 + 1 / (2 * m) ↔ (t - 1) * (2 * m) < 1 := by
    rw [← sub_lt_iff_lt_add', lt_div_iff₀ (by positivity)]
  rw [key]; constructor <;> intro H <;> linarith

/-- At `h = 144` and `c = 25`, the real number `X` is exactly 6.

So `m = 6` sits on the boundary, where `eta = 0` and the Johnson bound gives no list. -/
theorem upperX_144_25 : upperX 144 25 = 6 := by
  unfold upperX
  rw [show ((144 : ℝ) + 25) / 144 = (13 / 12) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  norm_num

theorem not_etaPos_144_25 (n : ℝ) (hn : 0 < n) : ¬ EtaPos 144 25 n 6 := by
  rw [← lt_upperX_iff 144 25 n 6 (by norm_num) (by norm_num) hn (by norm_num), upperX_144_25]
  exact lt_irrefl _

end Plonky3Lean.Proofs.Security.Real
