module

public import Mathlib

@[expose] public section

/-!
# p3-security's `f64` bounds, read over ℝ, against their sources

aeneas does not translate `f64` arithmetic (docs/extractor-issues.md 19). Each `*R` definition
below transcribes one Rust expression exactly as written, with `libm::log2` read as `logb 2`,
`libm::pow(2, x)` as `2 ^ x` and `libm::sqrt` as `√`; `crates/security/crate.toml` lists them
as `[[mirror]]` entries. The rounding of `f64` itself is not modelled.

The bounds the Rust is compared with are stated from the papers:

* ethSTARK, eprint 2021/582, Theorem 5, and its STARK-with-quotient-chunks form in
  eprint 2024/1553, Theorem 2: the DEEP round costs `ε₂ = ℓ² · D / |F|` for a decoding list of
  size `ℓ`, union-bounded over pairs of candidate trace and quotient codewords.
* The same theorems' folding rounds, `εᵢ = (t - 1) · (ζ + (2m + 1)(n + 1)/(√ρ |F|))`: a sum.
* WHIR, eprint 2024/1586, Theorem 5.2: `ε_fold = d · ℓ / |F| + err*`: a sum.
* ethSTARK Theorem 1's precondition `η = √ρ (1 + 1/(2m)) - √ρ⁺ > 0`.
-/

open Real

namespace Plonky3Lean.Proofs.Security.Real

/-! ## Bits -/

/-- `t < q - log2 x` exactly when `x < 2^(q - t)`. -/
theorem lt_sub_logb_iff (q t x : ℝ) (hx : 0 < x) : t < q - logb 2 x ↔ x < (2 : ℝ) ^ (q - t) := by
  rw [← Real.logb_lt_iff_lt_rpow (by norm_num) hx]; constructor <;> intro h <;> linarith

/-- `-log2 ε`, the currency of p3-security's `ErrorBits`. -/
noncomputable def bits (ε : ℝ) : ℝ := -logb 2 ε

theorem bits_mul (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : bits (a * b) = bits a + bits b := by
  simp only [bits, Real.logb_mul ha.ne' hb.ne']; ring

theorem logb_lt_of_lt (x : ℝ) (n : ℕ) (hx : 0 < x) (h : x < 2 ^ n) : logb 2 x < n := by
  rw [Real.logb_lt_iff_lt_rpow (by norm_num) hx, Real.rpow_natCast]; exact h

theorem logb_neg_of_lt_one (x : ℝ) (hx : 0 < x) (h : x < 1) : logb 2 x < 0 :=
  Real.logb_neg (by norm_num) hx h

/-! ## DEEP-ALI -/

/-- Transcription of `p3_security::deep::deep_ali_error` before its `max(0)`, with `q` the
field size in bits, `L` the list size and `D` the identity degree (`factor`). -/
noncomputable def deepBitsR (q L D : ℝ) : ℝ := q - logb 2 L - logb 2 D

/-- ethSTARK Theorem 5, item 2, and eprint 2024/1553 Theorem 2, item 2: the DEEP round's error
`ℓ² · D / |F|`. The papers divide by `|F| - |D ∪ H|`; dividing by `|F|` only lowers this error,
so every lower bound on it below holds for the papers' value too. -/
noncomputable def deepErrPaper (q L D : ℝ) : ℝ := L ^ 2 * D / 2 ^ q

/-- **The Rust DEEP term charges `L`, the theorems `L²`.** For any list size `L > 0`, the Rust
reports exactly `log2 L` more bits than the theorem's error supports. -/
theorem deepBitsR_eq (q L D : ℝ) (hL : 0 < L) (hD : 0 < D) :
    deepBitsR q L D = bits (deepErrPaper q L D) + logb 2 L := by
  unfold deepBitsR bits deepErrPaper
  rw [Real.logb_div (by positivity) (by positivity), Real.logb_mul (by positivity) hD.ne',
    Real.logb_pow, Real.logb_rpow (by norm_num) (by norm_num)]
  push_cast; ring

/-- Transcription of `p3_security::proximity::list_size_ldr_m`: `(m + 1/2) / √ρ`. -/
noncomputable def listSizeLdrR (logBlowup m : ℕ) : ℝ :=
  ((m : ℝ) + 0.5) / √((2 : ℝ) ^ (-(logBlowup : ℝ)))

/-- Transcription of the identity degree in `p3_security::deep::deep_ali_error`, with `k` the
trace length: `max(max_deg (k + combo - 1) + (k - 1), (chunks + 1) k + combo - 1, 1)`. -/
noncomputable def deepFactorR (k maxDeg combo chunks : ℝ) : ℝ :=
  max (max (maxDeg * (k + combo - 1) + (k - 1)) ((chunks + 1) * k + combo - 1)) 1

theorem listSizeLdrR_3_3 : listSizeLdrR 3 3 = 7 / 2 * √8 := by
  have h : (2 : ℝ) ^ (-((3 : ℕ) : ℝ)) = 1 / 8 := by
    rw [Real.rpow_neg (by norm_num)]; norm_num
  rw [listSizeLdrR, h, Real.sqrt_div' _ (by norm_num : (0 : ℝ) ≤ 8)]
  rw [Real.sqrt_one]; field_simp; norm_num

/-- The identity degree of a degree-3 AIR over a `2^24` trace, two opening points, two chunks. -/
theorem deepFactorR_cex : deepFactorR (2 ^ 24) 3 2 2 = 2 ^ 26 + 2 := by
  unfold deepFactorR; norm_num

/-- **A DEEP term that overstates.** A degree-3 AIR over a `2^24` trace, opened at two points with
two quotient chunks, with blowup 8 and `m = 3`, over a 124-bit field (BabyBear's quartic
extension): the Rust reads more than 94 bits for the DEEP round, while the theorem's own error at
the Rust's own list size exceeds `2^-92`. -/
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

/-- Transcription of `p3_security::air::composition_error` before its `max(0)`. -/
noncomputable def aliBitsR (q L C : ℝ) : ℝ := q - logb 2 L - logb 2 C

/-- Transcription of `p3_security::proximity::alpha_ldr_m`: `(1 + 1/(2m)) √ρ`. -/
noncomputable def alphaLdrR (logBlowup m : ℕ) : ℝ :=
  (1 + 0.5 / (m : ℝ)) * √((2 : ℝ) ^ (-(logBlowup : ℝ)))

/-- Transcription of `p3_security::fri::query_phase_error`: `pow - log2(α^s)`. -/
noncomputable def queryBitsR (α : ℝ) (s pow : ℕ) : ℝ := pow - logb 2 (α ^ (s : ℝ))

/-- Transcription of `p3_security::proximity::johnson_exceptional_line_count_log2` for
`log_degree > 0`, `log_inv_rate > 0` and `m ≥ 3`. -/
noncomputable def johnsonLineLogR (ld lr m : ℕ) : ℝ :=
  3 + ((ld : ℝ) + lr) + 3 * logb 2 ((m : ℝ) + 0.5) - logb 2 3 -
    (logb 2 (1 - (2 : ℝ) ^ (-(ld : ℝ))) - lr)

/-- Transcription of `p3_security::fri::commit_phase_error_ldr_m` (positive-gamma branch, before
its `max(0)`): the minimum of the line-MCA bound and the `n / |F|` bound. -/
noncomputable def commitLdrBitsR (q : ℝ) (ld lr m arity cpow : ℕ) : ℝ :=
  let f : ℝ := 2 ^ arity
  let L : ℝ := (ld : ℝ) + lr
  min (q - johnsonLineLogR ld lr m - logb 2 (f - 1) + cpow)
    (q - logb 2 f - (L + logb 2 (1 + (2 : ℝ) ^ (-L))) - logb 2 (2 * (m : ℝ) + 1) +
      0.5 * logb 2 ((2 : ℝ) ^ (-(lr : ℝ))) + cpow)

/-- Transcription of `p3_security::stark::proven_security_regime`: the minimum of ALI, DEEP, the
low-degree test and the collision cap. -/
noncomputable def regimeBitsR (ali deep ldt coll : ℝ) : ℝ := min (min ali deep) (min ldt coll)

theorem two_rpow_neg (x : ℕ) : (2 : ℝ) ^ (-(x : ℝ)) = 1 / 2 ^ x := by
  rw [Real.rpow_neg (by norm_num), Real.rpow_natCast]; ring

/-- At blowup 8, `m = 3`, 70 queries and 16 bits of query grinding, the query phase reads more
than 94 bits. -/
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

/-- At a `2^24` trace, blowup 8, binary folding, `m = 3`, 20 bits of commit grinding and a 124-bit
field, the commit phase reads more than 94 bits. -/
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

/-- **The list-decoding regime the Rust reports, against the theorem.** At the parameters of
`deep_cex` (10 constraints, 70 queries with 16 bits of query grinding, binary folding with 20 bits
of commit grinding, a 128-bit hash), every term of the Rust's list-decoding regime at `m = 3`
exceeds 94 bits, so the regime reads more than 94 bits; the DEEP round alone, as the theorems
bound it, has error above `2^-92`. `p3-security`'s regression test reproduces this as
94.69 bits at the selected `m = 3`. -/
theorem ldr_regime_cex :
    94 < regimeBitsR (aliBitsR 124 (listSizeLdrR 3 3) 10)
        (deepBitsR 124 (listSizeLdrR 3 3) (deepFactorR (2 ^ 24) 3 2 2))
        (min (commitLdrBitsR 124 24 3 3 1 20) (queryBitsR (alphaLdrR 3 3) 70 16)) 128 ∧
      (2 : ℝ) ^ (-92 : ℝ) < deepErrPaper 124 (listSizeLdrR 3 3) (deepFactorR (2 ^ 24) 3 2 2) := by
  refine ⟨?_, deep_cex.2⟩
  unfold regimeBitsR
  exact lt_min (lt_min ali_cex deep_cex.1) (lt_min (lt_min commit_cex query_cex) (by norm_num))

/-! ## Two errors of one round: a sum, not a maximum -/

/-- Reporting the weaker of two error terms of one round (`min` of their bits, as
`commit_phase_error_ldr_m` and `SecurityAssumption::folding_pow_bits` do) overstates the round
whenever both terms are positive, by `log2(1 + small/large)`, at most one bit. -/
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

/-- The two terms of a list-decoding folding round, in the Rust: the curve-MCA count
`(f - 1) · C / |F|` and `f (2m + 1)(n + 1) / (√ρ |F|)`. The theorems add their own two terms;
`commitLdrBitsR` takes the smaller of the two bit counts, so it reports `bits` of the larger term
where the sum is due. -/
theorem commit_ldr_is_max (q : ℝ) (ld lr m arity cpow : ℕ) :
    commitLdrBitsR q ld lr m arity cpow =
      min (q - johnsonLineLogR ld lr m - logb 2 ((2 : ℝ) ^ arity - 1) + cpow)
        (q - logb 2 ((2 : ℝ) ^ arity) - (((ld : ℝ) + lr) + logb 2 (1 + (2 : ℝ) ^ (-((ld : ℝ) + lr)))) -
          logb 2 (2 * (m : ℝ) + 1) + 0.5 * logb 2 ((2 : ℝ) ^ (-(lr : ℝ))) + cpow) := rfl

/-- Transcription of the folding step of `SecurityAssumption::folding_pow_bits`: the PoW bits
the Rust charges to reach `λ`, from the weaker of the proximity-gap and fold-sumcheck bits. -/
noncomputable def foldingPowBitsR (lam proxBits sumcheckBits : ℝ) : ℝ :=
  max 0 (lam - min proxBits sumcheckBits)

/-- WHIR Theorem 5.2 bounds a folding round by the *sum* of the sumcheck and proximity-gap errors;
the Rust's PoW reaches `λ` against the larger term only, so the round lands below `λ`, by less
than one bit, whenever both terms are positive and the PoW is the binding lever. -/
theorem foldingPowBitsR_short (lam a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hneed : min (bits a) (bits b) < lam) :
    bits (a + b) + foldingPowBitsR lam (bits a) (bits b) < lam := by
  have := (min_bits_gt_bits_add a b ha hb).1
  unfold foldingPowBitsR
  rw [max_eq_right (by linarith)]
  linarith

/-! ## Unique decoding and the commit phase -/

/-- Transcription of `p3_security::fri::commit_phase_error_udr` before its `max(0)`, `n` the LDE
size, `f` the folding factor. -/
noncomputable def commitUdrBitsR (q n f pow : ℝ) : ℝ := q - logb 2 ((f - 1) * (n + 1)) + pow

/-- eprint 2024/1553, Theorem 3, item 4: a folding round of degree `t` costs
`(t - 1)(|D| + 1)/|F|`, boosted by grinding. The Rust charges the maximal arity `f ≥ t` at the
largest domain, so it never reports more. -/
theorem commitUdr_le_paper (q n f t pow : ℝ) (hn : 0 < n) (ht : 1 < t) (htf : t ≤ f) :
    commitUdrBitsR q n f pow ≤ bits ((t - 1) * (n + 1) / 2 ^ q) + pow := by
  unfold commitUdrBitsR bits
  rw [Real.logb_div (by nlinarith) (by positivity), Real.logb_rpow (by norm_num) (by norm_num)]
  have := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) (by nlinarith)
    (by nlinarith : (t - 1) * (n + 1) ≤ (f - 1) * (n + 1))
  linarith

/-! ## Union bounds -/

/-- Transcription of `ErrorBits::sum`: `-log2 Σ 2^-bᵢ`. -/
noncomputable def sumBitsR (l : List ℝ) : ℝ := bits (l.map (fun b => (2 : ℝ) ^ (-b))).sum

/-- `ErrorBits::sum` is at most every term, so composing by it never reports more than the
weakest term. -/
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

/-- `p3_security::logup` charges `N (W + 2) / |EF|`: the numerator root, `N (W + 1)`, plus the
vanishing denominator, `N`. -/
theorem logup_numerator (N W : ℕ) : N * (W + 1) + N = N * (W + 2) := by ring

/-! ## The Johnson line count -/

/-- `johnson_exceptional_line_count_log2` is `log2` of DKT26 Theorem 5.12's
`8 n (m + 1/2)^3 / (3 ρ⁻)`, with `n = 2^(ld + lr)` and `ρ⁻ = (2^ld - 1)/n`. -/
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

/-- The real number `compute_upper_m` floors: `X = 1 / (2 (√((h + c)/h) - 1))`. -/
noncomputable def upperX (h c : ℝ) : ℝ := 1 / (2 * (√((h + c) / h) - 1))

/-- ethSTARK Theorem 1's precondition at proximity parameter `m`, rate `ρ = h/n` and
`ρ⁺ = (h + c)/n`: `η = √ρ (1 + 1/(2m)) - √ρ⁺ > 0`. -/
def EtaPos (h c n m : ℝ) : Prop := √(h + c) / √n < √h / √n * (1 + 1 / (2 * m))

/-- **`m < X` is exactly the precondition** `η > 0`, for every `m > 0`. -/
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

/-- `X(144, 25) = 6`: at a trace of 144 rows opened at 25 points, `m = 6` sits exactly on the
boundary, where `η = 0` and the Johnson bound gives no list. -/
theorem upperX_144_25 : upperX 144 25 = 6 := by
  unfold upperX
  rw [show ((144 : ℝ) + 25) / 144 = (13 / 12) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  norm_num

theorem not_etaPos_144_25 (n : ℝ) (hn : 0 < n) : ¬ EtaPos 144 25 n 6 := by
  rw [← lt_upperX_iff 144 25 n 6 (by norm_num) (by norm_num) hn (by norm_num), upperX_144_25]
  exact lt_irrefl _

end Plonky3Lean.Proofs.Security.Real
