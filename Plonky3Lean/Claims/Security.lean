module

public import Plonky3Lean.Proofs.Security.Fixed
public import Plonky3Lean.Proofs.Security.Budget
public import Plonky3Lean.Proofs.Security.Binary
public import Plonky3Lean.Proofs.Security.Real

@[expose] public section

/-!
# p3-security: claims

What this repository asserts about p3-security, at the Plonky3 commit pinned in `plonky3/`.

- The integer arithmetic (`fixed`, `budget`, the binary PCS schedule) is the scoped extraction in
  `crates/security`. `m ⦃ v => P v ⦄` states that `m` returns a value `v`, so it does not panic,
  and that `P v` holds.
- The `f64` bounds do not extract. Their claims are about the real-number reading of the Rust
  (`Proofs.Security.Real`, transcriptions listed as `[[mirror]]` entries), compared with the
  bounds of ethSTARK (eprint 2021/582), eprint 2024/1553, WHIR (eprint 2024/1586) and DKT26
  (eprint 2026/2056). `f64` rounding is not modelled.

Bugs these claims establish:
- `ceil_log2` is not an upper bound (`fixed.ceil_log2.not_rounded_up`), and the budget built on it
  reports 100 bits for a round whose error exceeds `2^-100`
  (`budget.security_report.overstates_composition`).
- `deep_ali_error` charges the list size `L` where the theorems charge `L²`
  (`deep.deep_ali_error.charges_list_once`); at BabyBear-quartic parameters the proven
  list-decoding regime reads above 94 bits while the theorem's DEEP error exceeds `2^-92`
  (`deep.deep_ali_error.overstates`).
- `commit_phase_error_ldr_m` and `folding_pow_bits` take the larger of two errors of one round,
  where the theorems add them (`fri.commit_phase_error_ldr_m.max_not_sum`,
  `whir.folding_pow_bits.short_of_target`).
- `compute_upper_m`'s real `X` can be an integer, where `m = X` violates `η > 0`
  (`proximity.compute_upper_m.boundary`); in `f64` the Rust returns that `m`.
-/

open Aeneas Aeneas.Std CoreModels p3_security
open Plonky3Lean.Proofs.Security
open Plonky3Lean.Proofs.Security.FixedLog Plonky3Lean.Proofs.Security.Budget
open Plonky3Lean.Proofs.Security.Real

namespace Plonky3Lean.Claims.P3Security

/-! ## Fixed-point logarithms -/

/-- `floor_log2 x` never exceeds `2^16 · log2 x` (`2 ^ y ≤ x ^ 2^16`), for every nonzero `x`. -/
theorem fixed.floor_log2.le_log2 (x : Std.U64) (hx : x.val ≠ 0) :
    fixed.floor_log2 x ⦃ y => 2 ^ y.val ≤ x.val ^ 2 ^ 16 ⦄ :=
  WP.spec_mono (Fixed.floor_log2_spec x hx) fun y hy => hy ▸ flog_le x.val (by omega)

/-- `floor_log2 0` panics. -/
theorem fixed.floor_log2.panics : fixed.floor_log2 0#u64 = .fail .panic :=
  Fixed.floor_log2_zero

/-- `ceil_log2 x` is exact on powers of two and `floor_log2 x + 1` elsewhere, for every nonzero
`x`. -/
theorem fixed.ceil_log2.spec (x : Std.U64) (hx : x.val ≠ 0) :
    fixed.ceil_log2 x ⦃ y => y.val = clog x.val ⦄ :=
  Fixed.ceil_log2_spec x hx

/-- `ceil_log2 0` panics. -/
theorem fixed.ceil_log2.panics : fixed.ceil_log2 0#u64 = .fail .panic :=
  Fixed.ceil_log2_zero

/-- **`ceil_log2` does not round up**: `ceil_log2 14917 = 908635`, below `2^16 · log2 14917`. -/
theorem fixed.ceil_log2.not_rounded_up :
    fixed.ceil_log2 14917#u64 ⦃ y => y.val = 908635 ∧ 2 ^ y.val < 14917 ^ 2 ^ 16 ⦄ :=
  Fixed.ceil_log2_14917

/-- The proposed fix (squares and halvings rounded up, `cflog`) never falls below the logarithm. -/
theorem fixed.ceil_log2.fix_rounds_up (x : ℕ) (hx : 0 < x) : x ^ 2 ^ 16 ≤ 2 ^ cflog x :=
  le_cflog x hx

/-- `bits_per_query` never panics. -/
theorem fixed.bits_per_query.never_panics (b : Std.U32) (f : Std.U64) :
    fixed.bits_per_query b f ⦃ y => y.val = bpq b.val f.val ⦄ :=
  Fixed.bits_per_query_spec b f

/-! ## The round budget -/

/-- `security_report` never panics, for every input, and its seven rounds are `reportM`. -/
theorem budget.security_report.never_panics (pr : budget.shape.ProtocolParams)
    (i : budget.shape.InstanceShape) (a : budget.shape.AirShape) :
    budget.security_report pr i a ⦃ r => r.terms.val.map (fun t => t.bits.val) = reportM pr i a ⦄ :=
  security_report_spec pr i a

/-- `security_level` is the smallest round, in whole bits rounded down. -/
theorem budget.report.SecurityReport.security_level.spec (r : budget.report.SecurityReport)
    (hb : ∀ j < 7, (r.terms.val.map (fun t => t.bits.val))[j]! ≤ maxField) :
    budget.report.SecurityReport.security_level r ⦃ l => ∃ k < 7,
      l.val = (r.terms.val.map (fun t => t.bits.val))[k]! / 2 ^ 16 ∧
      ∀ j < 7, (r.terms.val.map (fun t => t.bits.val))[k]! ≤
        (r.terms.val.map (fun t => t.bits.val))[j]! ⦄ :=
  security_level_spec r hb

/-- **The budget overstates.** At `cexParams`, `cexInstance` and `cexAir` (14917 constraints,
`log2|E| = 7462235/2^16`) the report says 100 bits, while the composition round's error
`14917/|E|` exceeds `2^-100`. -/
theorem budget.security_report.overstates_composition :
    (∃ r, budget.security_report cexParams cexInstance cexAir = .ok r ∧
      budget.report.SecurityReport.security_level r ⦃ l => l.val = 100 ⦄) ∧
    2 ^ 7462235 < 2 ^ (100 * 2 ^ 16) * 14917 ^ 2 ^ 16 :=
  ⟨cex_level, cex_true_bound⟩

/-! ## The binary PCS schedule -/

/-- `field_error_numerator` never panics when `n + r < 64`, and is the sum over the `n` folds of
the fold's proximity error `N + 1` and its sumcheck error `2`. -/
theorem binary.field_error_numerator.spec (reg : binary.BinaryPcsRegime)
    (h : reg.num_variables.val + reg.log_inv_rate.val < 64) :
    binary.BinaryPcsRegime.field_error_numerator reg ⦃ y =>
      y.val = Binary.numeratorSpec reg.num_variables.val reg.log_inv_rate.val ⦄ :=
  Binary.field_error_numerator_spec reg h

/-- `field_security_bits` never panics on an accepted schedule, and the field error is at most
`2^-bits` unless `bits = 0`. -/
theorem binary.field_security_bits.spec (reg : binary.BinaryPcsRegime)
    (h : reg.num_variables.val + reg.log_inv_rate.val < 64) (hr : reg.log_inv_rate.val ≠ 0)
    (hn : reg.num_variables.val ≠ 0) :
    binary.BinaryPcsRegime.field_security_bits reg ⦃ y =>
      y.val = reg.challenge_field_bits.val - (Nat.log2 (Binary.numeratorSpec reg.num_variables.val
        reg.log_inv_rate.val - 1) + 1) ∧
      (y.val = 0 ∨ Binary.numeratorSpec reg.num_variables.val reg.log_inv_rate.val * 2 ^ y.val ≤
        2 ^ reg.challenge_field_bits.val) ⦄ :=
  Binary.field_security_bits_spec reg h hr hn

/-! ## The `f64` bounds over ℝ -/

/-- **`deep_ali_error` charges the list size once**; ethSTARK Theorem 5 and eprint 2024/1553
Theorem 2 charge it squared, so the Rust reads `log2 L` bits too many. -/
theorem deep.deep_ali_error.charges_list_once (q L D : ℝ) (hL : 0 < L) (hD : 0 < D) :
    deepBitsR q L D = bits (deepErrPaper q L D) + Real.logb 2 L :=
  deepBitsR_eq q L D hL hD

/-- **A proven level above its source.** Degree-3 AIR, `2^24` trace, blowup 8, 70 queries with 16
bits of query grinding, binary folding with 20 bits of commit grinding, a 124-bit field: the
Rust's list-decoding regime at `m = 3` reads more than 94 bits, while the DEEP error of the
theorems exceeds `2^-92`. -/
theorem deep.deep_ali_error.overstates :
    94 < regimeBitsR (aliBitsR 124 (listSizeLdrR 3 3) 10)
        (deepBitsR 124 (listSizeLdrR 3 3) (deepFactorR (2 ^ 24) 3 2 2))
        (min (commitLdrBitsR 124 24 3 3 1 20) (queryBitsR (alphaLdrR 3 3) 70 16)) 128 ∧
      (2 : ℝ) ^ (-92 : ℝ) < deepErrPaper 124 (listSizeLdrR 3 3) (deepFactorR (2 ^ 24) 3 2 2) :=
  ldr_regime_cex

/-- Taking the larger of two errors of one round, as `commit_phase_error_ldr_m` does with its
line-MCA and `n/|F|` terms, reports more bits than their sum supports, by at most one bit. -/
theorem fri.commit_phase_error_ldr_m.max_not_sum (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    bits (a + b) < min (bits a) (bits b) ∧ min (bits a) (bits b) ≤ bits (a + b) + 1 :=
  min_bits_gt_bits_add a b ha hb

/-- `commit_phase_error_udr` never reports more than eprint 2024/1553 Theorem 3, item 4, for any
round of degree `t` at most the folding factor. -/
theorem fri.commit_phase_error_udr.le_paper (q n f t pow : ℝ) (hn : 0 < n) (ht : 1 < t)
    (htf : t ≤ f) :
    commitUdrBitsR q n f pow ≤ bits ((t - 1) * (n + 1) / 2 ^ q) + pow :=
  commitUdr_le_paper q n f t pow hn ht htf

/-- The PoW `folding_pow_bits` selects leaves a WHIR folding round below the target when it is the
binding lever: WHIR Theorem 5.2 adds the round's two errors. -/
theorem whir.folding_pow_bits.short_of_target (lam a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hneed : min (bits a) (bits b) < lam) :
    bits (a + b) + foldingPowBitsR lam (bits a) (bits b) < lam :=
  foldingPowBitsR_short lam a b ha hb hneed

/-- `m < X` (the real number `compute_upper_m` floors) is exactly ethSTARK Theorem 1's
precondition `η > 0`. -/
theorem proximity.compute_upper_m.iff_eta_pos (h c n m : ℝ) (hh : 0 < h) (hc : 0 < c)
    (hn : 0 < n) (hm : 0 < m) :
    m < upperX h c ↔ EtaPos h c n m :=
  lt_upperX_iff h c n m hh hc hn hm

/-- At `h = 144`, `combo = 25`, `X = 6` exactly and `m = 6` violates `η > 0`; the Rust returns 6. -/
theorem proximity.compute_upper_m.boundary (n : ℝ) (hn : 0 < n) :
    upperX 144 25 = 6 ∧ ¬ EtaPos 144 25 n 6 :=
  ⟨upperX_144_25, not_etaPos_144_25 n hn⟩

/-- `johnson_exceptional_line_count_log2` is `log2` of DKT26 Theorem 5.12's
`8 n (m + 1/2)^3 / (3 ρ⁻)`. -/
theorem proximity.johnson_exceptional_line_count_log2.eq_dkt26 (ld lr m : ℕ) (hld : 0 < ld) :
    johnsonLineLogR ld lr m =
      Real.logb 2 (8 * 2 ^ (ld + lr) * ((m : ℝ) + 0.5) ^ 3 / (3 * ((2 ^ ld - 1) / 2 ^ (ld + lr)))) :=
  johnsonLineLogR_eq ld lr m hld

/-- `ErrorBits::sum` never reports more than its weakest term. -/
theorem error.ErrorBits.sum.le_term (l : List ℝ) (b : ℝ) (hb : b ∈ l) : sumBitsR l ≤ b :=
  sumBitsR_le l b hb

end Plonky3Lean.Claims.P3Security
