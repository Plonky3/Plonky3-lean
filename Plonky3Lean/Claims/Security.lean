module

public import Plonky3Lean.Proofs.Security.Fixed
public import Plonky3Lean.Proofs.Security.Budget
public import Plonky3Lean.Proofs.Security.Binary
public import Plonky3Lean.Proofs.Security.Real

@[expose] public section

/-!
# p3-security: claims

# Overview

These claims hold at the Plonky3 commit pinned in `plonky3/`.

The integer arithmetic is extracted from the Rust.

It covers the fixed-point logarithms, the round budget and the binary PCS schedule.

The notation `m ⦃ v => P v ⦄` says that `m` returns a value `v`, so it does not panic.

It also says that `P v` holds.

The floating-point bounds do not extract.

Their claims are about the same formulas read over the reals.

Each formula is compared with the paper it comes from:

- ethSTARK, eprint 2021/582;
- Haböck's FRI summary, eprint 2022/1216;
- eprint 2024/1553;
- WHIR, eprint 2024/1586;
- DKT26, eprint 2026/2056.

Floating-point rounding is not modelled.

# What the claims find

- The fixed-point ceiling logarithm does not round up at the pinned commit.
  At `x = 14917` it falls below `2^16 * log_2 x`.
  Plonky3 main has since fixed it.
- The round budget built on that logarithm overstates.
  It reports 100 bits for a round whose error exceeds `2^-100`.
- The WHIR folding grinding covers only the larger of a round's two errors.
  WHIR, Theorem 5.2, adds the two, so the round can land below its target.
- The largest admissible `m` is the floor of a real number `X`.
  When `X` is an integer, `m = X` violates the precondition `eta > 0`.
  The floating-point code returns that `m`.
- The DEEP round's doc says the choice of list-size bound never binds.
  At BabyBear-quartic parameters it does, as shown below.

# What the claims confirm

- The DEEP round charges the list size `L` once, and that is correct.
  Haböck's FRI summary (eprint 2022/1216), Theorem 8 and Remark 9, proves it.
  It decodes the trace and the quotient jointly, as one interleaved word.
  ethSTARK and eprint 2024/1553 charge `L^2`, a looser analysis.
- The FRI list-decoding commit round takes the larger of its two terms.
  With the full agreement sets of DKT26, Theorem 5.12, the curve count alone bounds the round.
  So the larger term is a valid, conservative bound.

```text
    degree-3 AIR, 2^24 trace, blowup 8, 70 queries, 124-bit field, m = 3

    list size charged once (Haböck):     94.7 bits
    list size charged squared (looser):  91.4 bits
```
-/

open Aeneas Aeneas.Std CoreModels p3_security
open Plonky3Lean.Proofs.Security
open Plonky3Lean.Proofs.Security.FixedLog Plonky3Lean.Proofs.Security.Budget
open Plonky3Lean.Proofs.Security.Real

namespace Plonky3Lean.Claims.P3Security

/-! ## Fixed-point logarithms -/

/-- The floor logarithm `y` of a nonzero `x` never exceeds `2^16 * log_2 x`.

Over the naturals this reads `2^y <= x^(2^16)`. -/
theorem fixed.floor_log2.le_log2 (x : Std.U64) (hx : x.val ≠ 0) :
    fixed.floor_log2 x ⦃ y => 2 ^ y.val ≤ x.val ^ 2 ^ 16 ⦄ :=
  WP.spec_mono (Fixed.floor_log2_spec x hx) fun y hy => hy ▸ flog_le x.val (by omega)

/-- The floor logarithm of zero panics. -/
theorem fixed.floor_log2.panics : fixed.floor_log2 0#u64 = .fail .panic :=
  Fixed.floor_log2_zero

/-- The ceiling logarithm of a nonzero `x` is exact on a power of two.

Elsewhere it is the floor logarithm plus one unit. -/
theorem fixed.ceil_log2.spec (x : Std.U64) (hx : x.val ≠ 0) :
    fixed.ceil_log2 x ⦃ y => y.val = clog x.val ⦄ :=
  Fixed.ceil_log2_spec x hx

/-- The ceiling logarithm of zero panics. -/
theorem fixed.ceil_log2.panics : fixed.ceil_log2 0#u64 = .fail .panic :=
  Fixed.ceil_log2_zero

/-- **The ceiling logarithm does not round up.**

At `x = 14917` it returns `908635`, which is below `2^16 * log_2 14917`.

Plonky3 main has since fixed it. -/
theorem fixed.ceil_log2.not_rounded_up :
    fixed.ceil_log2 14917#u64 ⦃ y => y.val = 908635 ∧ 2 ^ y.val < 14917 ^ 2 ^ 16 ⦄ :=
  Fixed.ceil_log2_14917

/-- Round every square and every halving up instead of down.

The resulting ceiling logarithm never falls below `2^16 * log_2 x`. -/
theorem fixed.ceil_log2.fix_rounds_up (x : ℕ) (hx : 0 < x) : x ^ 2 ^ 16 ≤ 2 ^ cflog x :=
  le_cflog x hx

/-- The bits of security per query never panic, for every input. -/
theorem fixed.bits_per_query.never_panics (b : Std.U32) (f : Std.U64) :
    fixed.bits_per_query b f ⦃ y => y.val = bpq b.val f.val ⦄ :=
  Fixed.bits_per_query_spec b f

/-! ## The round budget -/

/-- The security report never panics.

Its seven rounds equal the model on the naturals, for every input. -/
theorem budget.security_report.never_panics (pr : budget.shape.ProtocolParams)
    (i : budget.shape.InstanceShape) (a : budget.shape.AirShape) :
    budget.security_report pr i a ⦃ r => r.terms.val.map (fun t => t.bits.val) = reportM pr i a ⦄ :=
  security_report_spec pr i a

/-- The security level is the smallest round, in whole bits rounded down. -/
theorem budget.report.SecurityReport.security_level.spec (r : budget.report.SecurityReport)
    (hb : ∀ j < 7, (r.terms.val.map (fun t => t.bits.val))[j]! ≤ maxField) :
    budget.report.SecurityReport.security_level r ⦃ l => ∃ k < 7,
      l.val = (r.terms.val.map (fun t => t.bits.val))[k]! / 2 ^ 16 ∧
      ∀ j < 7, (r.terms.val.map (fun t => t.bits.val))[k]! ≤
        (r.terms.val.map (fun t => t.bits.val))[j]! ⦄ :=
  security_level_spec r hb

/-- **The budget overstates.**

The report says 100 bits, while the composition round's error exceeds `2^-100`:

```text
    14917 constraints, log_2 |E| = 7462235 / 2^16 (about 113.86)

    reported level:                 100 bits
    composition error 14917 / |E|:  above 2^-100
```
-/
theorem budget.security_report.overstates_composition :
    (∃ r, budget.security_report cexParams cexInstance cexAir = .ok r ∧
      budget.report.SecurityReport.security_level r ⦃ l => l.val = 100 ⦄) ∧
    2 ^ 7462235 < 2 ^ (100 * 2 ^ 16) * 14917 ^ 2 ^ 16 :=
  ⟨cex_level, cex_true_bound⟩

/-! ## The binary PCS schedule -/

/-- The field-error numerator never panics when `n + r < 64`.

It sums two errors over the `n` folds: the proximity error `N + 1` and the sumcheck error `2`. -/
theorem binary.field_error_numerator.spec (reg : binary.BinaryPcsRegime)
    (h : reg.num_variables.val + reg.log_inv_rate.val < 64) :
    binary.BinaryPcsRegime.field_error_numerator reg ⦃ y =>
      y.val = Binary.numeratorSpec reg.num_variables.val reg.log_inv_rate.val ⦄ :=
  Binary.field_error_numerator_spec reg h

/-- The field security bits never panic on an accepted schedule.

The field error is then at most `2^-bits`, unless `bits = 0`. -/
theorem binary.field_security_bits.spec (reg : binary.BinaryPcsRegime)
    (h : reg.num_variables.val + reg.log_inv_rate.val < 64) (hr : reg.log_inv_rate.val ≠ 0)
    (hn : reg.num_variables.val ≠ 0) :
    binary.BinaryPcsRegime.field_security_bits reg ⦃ y =>
      y.val = reg.challenge_field_bits.val - (Nat.log2 (Binary.numeratorSpec reg.num_variables.val
        reg.log_inv_rate.val - 1) + 1) ∧
      (y.val = 0 ∨ Binary.numeratorSpec reg.num_variables.val reg.log_inv_rate.val * 2 ^ y.val ≤
        2 ^ reg.challenge_field_bits.val) ⦄ :=
  Binary.field_security_bits_spec reg h hr hn

/-! ## The floating-point bounds, over the reals -/

/-- **The DEEP round charges the list size once.**

This is the bound of Haböck's FRI summary (eprint 2022/1216), Theorem 8, and of soundcalc.

ethSTARK, Theorem 5, and eprint 2024/1553, Theorem 2, give the looser bound `L^2`.

Against that looser bound, the Rust reports exactly `log_2 L` more bits. -/
theorem deep.deep_ali_error.charges_list_once (q L D : ℝ) (hL : 0 < L) (hD : 0 < D) :
    deepBitsR q L D = bits (deepErrPaper q L D) + Real.logb 2 L :=
  deepBitsR_eq q L D hL hD

/-- **The looser `L^2` bound would set a lower level.**

The Rust's list-decoding regime reads more than 94 bits, about 94.7.

The looser `L^2` DEEP error of ethSTARK and eprint 2024/1553 exceeds `2^-92`, about 91.4 bits.

So the choice of bound can set the reported level, at these parameters:

```text
    degree-3 AIR, 2^24 trace, blowup 8, 124-bit field, m = 3
    70 queries with 16 bits of query grinding
    binary folding with 20 bits of commit grinding
```
-/
theorem deep.deep_ali_error.l_squared_would_bind :
    94 < regimeBitsR (aliBitsR 124 (listSizeLdrR 3 3) 10)
        (deepBitsR 124 (listSizeLdrR 3 3) (deepFactorR (2 ^ 24) 3 2 2))
        (min (commitLdrBitsR 124 24 3 3 1 20) (queryBitsR (alphaLdrR 3 3) 70 16)) 128 ∧
      (2 : ℝ) ^ (-92 : ℝ) < deepErrPaper 124 (listSizeLdrR 3 3) (deepFactorR (2 ^ 24) 3 2 2) :=
  ldr_regime_cex

/-- The larger of two positive errors is below their sum, and at least half of it.

In bits, the larger error reads above the sum, by at most one bit.

The FRI list-decoding commit round reports the larger of its two terms.

With the full agreement sets of DKT26, Theorem 5.12, the curve count alone bounds the round.

So the larger term is a valid bound there, and this fact measures its gap to the sum. -/
theorem fri.commit_phase_error_ldr_m.max_le_sum (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    bits (a + b) < min (bits a) (bits b) ∧ min (bits a) (bits b) ≤ bits (a + b) + 1 :=
  min_bits_gt_bits_add a b ha hb

/-- The unique-decoding commit round never reports more than eprint 2024/1553, Theorem 3, item 4.

This holds for every round of degree `t` up to the folding factor. -/
theorem fri.commit_phase_error_udr.le_paper (q n f t pow : ℝ) (hn : 0 < n) (ht : 1 < t)
    (htf : t ≤ f) :
    commitUdrBitsR q n f pow ≤ bits ((t - 1) * (n + 1) / 2 ^ q) + pow :=
  commitUdr_le_paper q n f t pow hn ht htf

/-- The WHIR folding grinding can leave a folding round below the target.

This happens when grinding is what has to close the gap.

WHIR, Theorem 5.2, adds the round's two errors, while the grinding covers only the larger one.

The shortfall is less than one bit. -/
theorem whir.folding_pow_bits.short_of_target (lam a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hneed : min (bits a) (bits b) < lam) :
    bits (a + b) + foldingPowBitsR lam (bits a) (bits b) < lam :=
  foldingPowBitsR_short lam a b ha hb hneed

/-- The largest admissible `m` is the floor of a real number `X`.

The bound `m < X` is exactly the precondition `eta > 0` of ethSTARK, Theorem 1. -/
theorem proximity.compute_upper_m.iff_eta_pos (h c n m : ℝ) (hh : 0 < h) (hc : 0 < c)
    (hn : 0 < n) (hm : 0 < m) :
    m < upperX h c ↔ EtaPos h c n m :=
  lt_upperX_iff h c n m hh hc hn hm

/-- At `h = 144` and `combo = 25`, the real number `X` is exactly 6.

Then `m = 6` violates `eta > 0`, and the Rust returns 6. -/
theorem proximity.compute_upper_m.boundary (n : ℝ) (hn : 0 < n) :
    upperX 144 25 = 6 ∧ ¬ EtaPos 144 25 n 6 :=
  ⟨upperX_144_25, not_etaPos_144_25 n hn⟩

/-- The Johnson exceptional line count is the `log_2` of DKT26, Theorem 5.12.

That count is `8 n (m + 1/2)^3 / (3 rho^-)`. -/
theorem proximity.johnson_exceptional_line_count_log2.eq_dkt26 (ld lr m : ℕ) (hld : 0 < ld) :
    johnsonLineLogR ld lr m =
      Real.logb 2 (8 * 2 ^ (ld + lr) * ((m : ℝ) + 0.5) ^ 3 / (3 * ((2 ^ ld - 1) / 2 ^ (ld + lr)))) :=
  johnsonLineLogR_eq ld lr m hld

/-- A union bound of error terms never reports more than its weakest term. -/
theorem error.ErrorBits.sum.le_term (l : List ℝ) (b : ℝ) (hb : b ∈ l) : sumBitsR l ≤ b :=
  sumBitsR_le l b hb

end Plonky3Lean.Claims.P3Security
