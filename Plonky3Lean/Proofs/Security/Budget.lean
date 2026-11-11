module

public import Plonky3Lean.Proofs.Security.Fixed

@[expose] public section

/-!
# p3-security's conjectured round budget

# Overview

Each of the seven rounds of the security report is modelled on the naturals.

For every input, the report returns those seven values and does not panic.

All bit counts are in fixed point, with 16 fractional bits.
-/

open Aeneas Aeneas.Std CoreModels p3_security
open Plonky3Lean.Lib Plonky3Lean.Proofs.Security.FixedLog

namespace Plonky3Lean.Proofs.Security.Budget

open Plonky3Lean.Proofs.Security.Fixed

/-- The largest supported field size: `2^32 - 1` whole bits, in fixed point. -/
def maxField : ℕ := (2 ^ 32 - 1) * 2 ^ 16

/-- The cap on every round: the collision resistance, at most the field size.

It is zero when the field size is zero or unsupported. -/
def capM (fb cr : ℕ) : ℕ := if fb = 0 ∨ maxField < fb then 0 else min (cr * 2 ^ 16) fb

/-- A generic round: error `c * 2^ls / |E|`, plus `pow` bits of grinding, then capped. -/
def roundM (fb cap : ℕ) (c : Option ℕ) (ls pow : ℕ) : ℕ :=
  match c with
  | none => cap
  | some 0 => 0
  | some c =>
    let e := clog c + ls * 2 ^ 16
    min (if fb ≤ e then pow * 2 ^ 16 else fb - e + pow * 2 ^ 16) cap

/-- The out-of-domain round.

Its error is the identity degree over `|E|`, plus grinding, then capped.

It is zero in three cases:

- the log of the trace height is 64 or more;
- the chunk count is not a power of two;
- the identity degree overflows 64 bits. -/
def oodM (fb lmh d chunks combo pow cap : ℕ) : ℕ :=
  if 64 ≤ lmh ∨ ¬ (chunks ≠ 0 ∧ chunks &&& (chunks - 1) = 0) then 0 else
  let d' := if d = 0 then 1 else d
  let combo' := if combo = 0 then 1 else combo
  let h := 2 ^ lmh
  let size := max (d' * (h + combo' - 1) + (h - 1)) ((chunks + 1) * h + combo' - 1)
  if 2 ^ 64 - 1 < size then 0 else min (fb - clog size + pow * 2 ^ 16) cap

/-- The folding coefficient `2 * (2^a - 1)`, or nothing when it would overflow. -/
def foldCoefM (a : ℕ) : Option ℕ := if 63 ≤ a then none else some (2 * (2 ^ a - 1))

/-- Saturating addition on 32 bits. -/
def satAdd32 (a b : ℕ) : ℕ := min (a + b) (2 ^ 32 - 1)

/-- Saturating addition and multiplication on 64 bits. -/
def satAdd64 (a b : ℕ) : ℕ := min (a + b) (2 ^ 64 - 1)
def satMul64 (a b : ℕ) : ℕ := min (a * b) (2 ^ 64 - 1)

/-- The query round: queries times bits per query, plus grinding, then capped. -/
def queryM (fb lb q pow cap : ℕ) : ℕ := min (satAdd64 (satMul64 q (bpq lb fb)) (pow * 2 ^ 16)) cap

/-! ## Component specs -/

@[step]
theorem sat_add32_spec (x y : Std.U32) :
    core.num.U32.saturating_add_exposed x y ⦃ z => z.val = satAdd32 x.val y.val ⦄ := by
  simp only [core.num.U32.saturating_add_exposed, WP.spec_ok]
  show (BitVec.ofNat 32 (min (x.val + y.val) (2 ^ 32 - 1))).toNat = _
  rw [BitVec.toNat_ofNat, satAdd32, Nat.mod_eq_of_lt (by omega)]

@[step]
theorem sat_add64_spec (x y : Std.U64) :
    core.num.U64.saturating_add_exposed x y ⦃ z => z.val = satAdd64 x.val y.val ⦄ := by
  simp only [core.num.U64.saturating_add_exposed, WP.spec_ok]
  show (BitVec.ofNat 64 (min (x.val + y.val) (2 ^ 64 - 1))).toNat = _
  rw [BitVec.toNat_ofNat, satAdd64, Nat.mod_eq_of_lt (by omega)]

@[step]
theorem sat_mul64_spec (x y : Std.U64) :
    core.num.U64.saturating_mul_exposed x y ⦃ z => z.val = satMul64 x.val y.val ⦄ := by
  simp only [core.num.U64.saturating_mul_exposed, WP.spec_ok]
  show (BitVec.ofNat 64 (min (x.val * y.val) (2 ^ 64 - 1))).toNat = _
  rw [BitVec.toNat_ofNat, satMul64, Nat.mod_eq_of_lt (by omega)]

@[step]
theorem min_spec (a b : Std.U64) : budget.min a b ⦃ y => y.val = min a.val b.val ⦄ := by
  unfold budget.min
  split_ifs with h
  · simp only [WP.spec_ok]; scalar_tac
  · simp only [WP.spec_ok]; scalar_tac

@[step]
theorem cap_spec (i : budget.shape.InstanceShape) :
    budget.shape.InstanceShape.cap i ⦃ y => y.val = capM i.field_bits.val i.collision_resistance.val ⦄ := by
  unfold budget.shape.InstanceShape.cap
  by_cases h0 : i.field_bits = 0#u64
  · simp [h0, capM]
  · have h0' : i.field_bits.val ≠ 0 := fun h => h0 (by scalar_tac)
    simp only [h0, ↓reduceIte]
    step as ⟨m, hm⟩
    have hmv : m.val = maxField := by rw [hm]; simp [U32.rMax, maxField]
    by_cases hg : i.field_bits > m
    · have : maxField < i.field_bits.val := by rw [← hmv]; scalar_tac
      simp only [hg, ↓reduceIte, WP.spec_ok]
      simp [capM, this]
    · have : ¬ maxField < i.field_bits.val := by rw [← hmv]; scalar_tac
      simp only [hg, ↓reduceIte]
      step as ⟨c, hc⟩
      by_cases hlt : c < i.field_bits
      · simp only [hlt, ↓reduceIte, WP.spec_ok]
        have : c.val < i.field_bits.val := by scalar_tac
        simp only [capM, h0', false_or]
        rw [ite_eq_right_of_eq_false _ _ (eq_false ‹_›)]; omega
      · simp only [hlt, ↓reduceIte, WP.spec_ok]
        have : ¬ c.val < i.field_bits.val := by scalar_tac
        simp only [capM, h0', false_or]
        rw [ite_eq_right_of_eq_false _ _ (eq_false ‹¬ maxField < _›)]; omega

@[step]
theorem term_new_spec (l : Str) (b : Std.U64) :
    budget.report.SecurityTerm.new l b ⦃ t => t.label = l ∧ t.bits = b ⦄ := by
  simp [budget.report.SecurityTerm.new]

/-- A generic round never panics on a supported field size, and equals its model. -/
@[step]
theorem round_spec (l : Str) (i : budget.shape.InstanceShape) (c : core.option.Option Std.U64)
    (ls pow : Std.U32) (cap : Std.U64) (hf : i.field_bits.val ≤ maxField) :
    budget.round l i c ls pow cap ⦃ t => t.label = l ∧
      t.bits.val = roundM i.field_bits.val cap.val
        (match c with | .None => none | .Some c => some c.val) ls.val pow.val ⦄ := by
  unfold budget.round
  have hls := ls.hBounds
  have hpow := pow.hBounds
  rcases c with _ | c
  · step*; simp [roundM, *]
  · by_cases hc : c.val = 0
    · have : (core.num.nonzero.NonZero.new
          core.U64.Insts.CoreNumNonzeroZeroablePrimitiveNonZeroU64Inner c) =
          .ok core.option.Option.None := by
        simp [core.num.nonzero.NonZero.new,
          core.U64.Insts.CoreNumNonzeroZeroablePrimitiveNonZeroU64Inner, hc]
      simp only [this]
      step*; simp [roundM, *]
    · have : (core.num.nonzero.NonZero.new
          core.U64.Insts.CoreNumNonzeroZeroablePrimitiveNonZeroU64Inner c) =
          .ok (core.option.Option.Some c) := by
        simp [core.num.nonzero.NonZero.new,
          core.U64.Insts.CoreNumNonzeroZeroablePrimitiveNonZeroU64Inner, hc]
      simp only [this]
      have hcl := flog_lt c hc
      have : clog c.val ≤ 64 * 2 ^ 16 := by
        unfold clog; split_ifs
        · have := log2_lt_64 c; nlinarith
        · omega
      simp only [core.num.nonzero.NonZero.get]
      step*
      have hmf : maxField = (2 ^ 32 - 1) * 2 ^ 16 := rfl
      simp only [UScalarTy.U32_numBits_eq] at hls hpow
      have hr : roundM i.field_bits.val cap.val (some c.val) ls.val pow.val =
          min (if i.field_bits.val ≤ error.val then pow.val * 2 ^ 16
            else i.field_bits.val - error.val + pow.val * 2 ^ 16) cap.val := by
        simp only [roundM, error_post, i1_post, i2_post]
      rw [hr]
      by_cases he : error ≥ i.field_bits
      · have he' : i.field_bits.val ≤ error.val := by scalar_tac
        simp only [he, ↓reduceIte, he']
        step*
      · have he' : ¬ i.field_bits.val ≤ error.val := by scalar_tac
        simp only [he, ↓reduceIte, he']
        step*

/-- The power-of-two test on 32 bits is `x != 0` and `x &&& (x - 1) = 0`. -/
@[step]
theorem is_power_of_two32_spec (x : Std.U32) :
    CoreModels.core.num.U32.is_power_of_two x ⦃ b =>
      b = true ↔ x.val ≠ 0 ∧ x.val &&& (x.val - 1) = 0 ⦄ := by
  unfold CoreModels.core.num.U32.is_power_of_two
  by_cases h0 : x.val = 0
  · have : (x != 0#u32) = false := by simp; scalar_tac
    simp only [this, Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
    simp [h0]
  · have : (x != 0#u32) = true := by simp; scalar_tac
    simp only [this, ↓reduceIte]
    step*

/-- The out-of-domain round never panics on a supported field size, and equals its model. -/
@[step]
theorem ood_spec (i : budget.shape.InstanceShape) (d c k pow : Std.U32) (cap : Std.U64)
    (hf : i.field_bits.val ≤ maxField) :
    budget.out_of_domain_round i d c k pow cap ⦃ t =>
      t.bits.val = oodM i.field_bits.val i.log_max_height.val d.val c.val k.val pow.val cap.val ⦄ := by
  unfold budget.out_of_domain_round
  have hd := d.hBounds
  have hc := c.hBounds
  have hk := k.hBounds
  have hp := pow.hBounds
  simp only [UScalarTy.U32_numBits_eq] at hd hc hk hp
  have hmf : maxField = (2 ^ 32 - 1) * 2 ^ 16 := rfl
  by_cases hl : i.log_max_height ≥ core.num.U64.BITS
  · have hl' : 64 ≤ i.log_max_height.val := by
      have : (core.num.U64.BITS : Std.U32).val = 64 := by simp [core.num.U64.BITS]
      scalar_tac
    simp only [hl, ↓reduceIte]
    step*
    simp [oodM, *]
  · have hl' : i.log_max_height.val < 64 := by
      have : (core.num.U64.BITS : Std.U32).val = 64 := by simp [core.num.U64.BITS]
      scalar_tac
    simp only [hl, ↓reduceIte]
    step as ⟨b, hb⟩
    by_cases hb' : b = true
    · simp only [hb', ↓reduceIte]
      have hpw : c.val ≠ 0 ∧ c.val &&& (c.val - 1) = 0 := hb.mp hb'
      obtain ⟨dv, hdv, hdvv⟩ : ∃ dv : Std.U128,
          (if d = 0#u32 then RustM.ok 1#u128 else RustM.ok (UScalar.cast .U128 d)) = .ok dv ∧
          dv.val = (if d.val = 0 then 1 else d.val) := by
        by_cases h : d = 0#u32
        · exact ⟨1#u128, by simp [h], by simp [h]⟩
        · have h' : d.val ≠ 0 := fun e => h (by scalar_tac)
          exact ⟨UScalar.cast .U128 d, by simp [h], by simp [h']⟩
      obtain ⟨kv, hkv, hkvv⟩ : ∃ kv : Std.U128,
          (if k = 0#u32 then RustM.ok 1#u128 else RustM.ok (UScalar.cast .U128 k)) = .ok kv ∧
          kv.val = (if k.val = 0 then 1 else k.val) := by
        by_cases h : k = 0#u32
        · exact ⟨1#u128, by simp [h], by simp [h]⟩
        · have h' : k.val ≠ 0 := fun e => h (by scalar_tac)
          exact ⟨UScalar.cast .U128 k, by simp [h], by simp [h']⟩
      simp only [hdv, hkv]
      have hdb : 1 ≤ dv.val ∧ dv.val < 2 ^ 32 := by rw [hdvv]; split_ifs <;> omega
      have hkb : 1 ≤ kv.val ∧ kv.val < 2 ^ 32 := by rw [hkvv]; split_ifs <;> omega
      have hH : (2 : ℕ) ^ i.log_max_height.val < 2 ^ 64 := Nat.pow_lt_pow_right (by norm_num) hl'
      have hH1 : 1 ≤ (2 : ℕ) ^ i.log_max_height.val := Nat.one_le_two_pow
      step as ⟨h, hh⟩
      have hhv : h.val = 2 ^ i.log_max_height.val := by
        rw [hh, Nat.shiftLeft_eq, one_mul, U128.size, U128.numBits]
        exact Nat.mod_eq_of_lt (lt_trans hH (Nat.pow_lt_pow_right (by norm_num) (by simp)))
      set H := 2 ^ i.log_max_height.val with hHdef
      step as ⟨a1, ha1⟩
      step as ⟨a2, ha2⟩
      have hA2 : a2.val < 2 ^ 65 := by omega
      have hM : dv.val * a2.val < 2 ^ 97 := by
        calc dv.val * a2.val < 2 ^ 32 * 2 ^ 65 := Nat.mul_lt_mul'' hdb.2 hA2
          _ = 2 ^ 97 := by norm_num
      step as ⟨a3, ha3⟩
      step as ⟨a4, ha4⟩
      step as ⟨a5, ha5⟩
      step as ⟨ch, hch⟩
      step as ⟨a6, ha6⟩
      have hchv : ch.val = c.val := by rw [hch]; simp
      have hA6 : a6.val ≤ 2 ^ 32 := by omega
      have hM2 : a6.val * h.val < 2 ^ 97 := by
        calc a6.val * h.val < (2 ^ 32 + 1) * 2 ^ 64 := Nat.mul_lt_mul_of_le_of_lt (by omega) (by omega) (by omega)
          _ < 2 ^ 97 := by norm_num
      step as ⟨a7, ha7⟩
      step as ⟨a8, ha8⟩
      step as ⟨chunked, hchunked⟩
      obtain ⟨sz, hsz, hszv⟩ : ∃ sz : Std.U128,
          (if a5 > chunked then RustM.ok a5 else RustM.ok chunked) = .ok sz ∧
          sz.val = max a5.val chunked.val := by
        by_cases hg : a5 > chunked
        · exact ⟨a5, by simp [hg], by have : chunked.val < a5.val := hg; omega⟩
        · exact ⟨chunked, by simp [hg], by have : ¬ chunked.val < a5.val := hg; omega⟩
      simp only [hsz]
      have hmax64 : (UScalar.cast .U128 core.num.U64.MAX : Std.U128).val = 2 ^ 64 - 1 := by
        simp [core.num.U64.MAX, U64.rMax]
      step as ⟨m7, hm7⟩
      -- The size, as the model computes it.
      have hszM : sz.val = max ((if d.val = 0 then 1 else d.val) *
            (H + (if k.val = 0 then 1 else k.val) - 1) + (H - 1))
          ((c.val + 1) * H + (if k.val = 0 then 1 else k.val) - 1) := by
        rw [hszv, hchunked, ha8, ha7, ha6, hchv, ha5, ha3, ha4, ha2, ha1, hhv, ← hdvv, ← hkvv]
      have hcond : ¬ (64 ≤ i.log_max_height.val ∨ ¬ (c.val ≠ 0 ∧ c.val &&& (c.val - 1) = 0)) := by
        omega
      have hO : oodM i.field_bits.val i.log_max_height.val d.val c.val k.val pow.val cap.val =
          if 2 ^ 64 - 1 < sz.val then 0
          else min (i.field_bits.val - clog sz.val + pow.val * 2 ^ 16) cap.val := by
        unfold oodM
        rw [ite_eq_right_of_eq_false _ _ (eq_false hcond), hszM]
      rw [hO]
      by_cases hbig : sz > m7
      · have : 2 ^ 64 - 1 < sz.val := by rw [← hmax64, ← hm7]; scalar_tac
        simp only [hbig, ↓reduceIte, this]
        step*
      · have hsmall : ¬ 2 ^ 64 - 1 < sz.val := by rw [← hmax64, ← hm7]; scalar_tac
        simp only [hbig, ↓reduceIte, hsmall]
        have h7 : 1 ≤ a7.val := by rw [ha7]; exact Nat.mul_pos (by omega) (by omega)
        have hsz0 : sz.val ≠ 0 := by omega
        step as ⟨s8, hs8⟩
        have hs8v : s8.val = sz.val := by
          rw [hs8, UScalar.cast_val_mod_pow_of_inBounds_eq]
          rw [UScalarTy.U64_numBits_eq]; omega
        step as ⟨e8, he8⟩
        step as ⟨s9, hs9⟩
        step as ⟨p10, hp10⟩
        have hsum : s9.val + p10.val < 2 ^ 64 := by rw [hs9, hp10]; omega
        step as ⟨bits, hbits⟩
        step as ⟨m11, hm11⟩
        step as ⟨t, ht1, ht2⟩
        rw [ht2, hm11, hbits, hs9, hp10, he8, hs8v]
    · have hbf : b = false := by simpa using hb'
      simp only [hbf, Bool.false_eq_true, ↓reduceIte]
      step*
      have : ¬ (c.val ≠ 0 ∧ c.val &&& (c.val - 1) = 0) := fun h => hb' (hb.mpr h)
      simp [oodM, *]

/-- The folding round: a generic round with the folding coefficient. -/
def foldM (fb cap a lmh lb pow : ℕ) : ℕ :=
  match foldCoefM a with
  | none => 0
  | some c => roundM fb cap (some c) (satAdd32 lmh lb) pow

@[step]
theorem folding_coefficient_spec (a : Std.U32) :
    budget.folding_coefficient a ⦃ o =>
      (match o with | .None => none | .Some c => some c.val) = foldCoefM a.val ⦄ := by
  unfold budget.folding_coefficient
  have hbits : (core.num.U64.BITS : Std.U32).val = 64 := by simp [core.num.U64.BITS]
  step as ⟨i, hi⟩
  by_cases h : a ≥ i
  · have : 63 ≤ a.val := by scalar_tac
    simp only [h, ↓reduceIte, WP.spec_ok]
    simp [foldCoefM, this]
  · have ha : a.val < 63 := by scalar_tac
    simp only [h, ↓reduceIte]
    have h2 : (2 : ℕ) ^ a.val < 2 ^ 63 := Nat.pow_lt_pow_right (by norm_num) ha
    step as ⟨p, hp⟩
    have hpv : p.val = 2 ^ a.val := by
      rw [hp, Nat.shiftLeft_eq, one_mul, U64.size, U64.numBits]
      exact Nat.mod_eq_of_lt (lt_trans h2 (by simp))
    have h1 : 1 ≤ (2 : ℕ) ^ a.val := Nat.one_le_two_pow
    step*
    have hn : ¬ 63 ≤ a.val := by omega
    simp only [foldCoefM, hn, ↓reduceIte, Option.some.injEq]
    rw [i3_post, i2_post, hpv]

@[step]
theorem folding_round_spec (pr : budget.shape.ProtocolParams) (ins : budget.shape.InstanceShape)
    (cap : Std.U64) (hf : ins.field_bits.val ≤ maxField) :
    budget.folding_round pr ins cap ⦃ t => t.bits.val = foldM ins.field_bits.val cap.val
      pr.log_folding_arity.val ins.log_max_height.val pr.log_blowup.val pr.folding_pow_bits.val ⦄ := by
  unfold budget.folding_round
  step as ⟨o, ho⟩
  rcases o with _ | c
  · simp only at ho
    step*
    rw [t_post, foldM, ← ho]; rfl
  · simp only at ho
    step*
    rw [t_post, foldM, ← ho, i_post]

/-- The seven rounds of the security report, on the naturals, in the report's order.

```text
    lookup, composition, out-of-domain, DEEP, folding, query, collision cap
```
-/
def reportM (pr : budget.shape.ProtocolParams) (i : budget.shape.InstanceShape)
    (a : budget.shape.AirShape) : List ℕ :=
  let fb := i.field_bits.val
  let cap := capM fb i.collision_resistance.val
  if cap = 0 then [0, 0, 0, 0, 0, 0, 0] else
  [ roundM fb cap (match a.lookup with
      | .None => none
      | .Some l => some ((l.max_message_width.val + 2) * l.fractions_per_row.val))
      i.log_max_height.val pr.lookup_pow_bits.val,
    roundM fb cap (some a.num_composed_constraints.val) 0 0,
    oodM fb i.log_max_height.val a.max_constraint_degree.val a.num_quotient_chunks.val
      a.max_combo.val pr.ood_pow_bits.val cap,
    roundM fb cap (match a.num_deep_terms with | .None => none | .Some n => some n.val)
      (satAdd32 i.log_max_height.val pr.log_blowup.val) pr.deep_pow_bits.val,
    foldM fb cap pr.log_folding_arity.val i.log_max_height.val pr.log_blowup.val
      pr.folding_pow_bits.val,
    queryM fb pr.log_blowup.val pr.num_queries.val pr.query_pow_bits.val cap,
    cap ]

/-- **The security report never panics.**

For every input, its seven rounds equal the model. -/
theorem security_report_spec (pr : budget.shape.ProtocolParams) (ins : budget.shape.InstanceShape)
    (a : budget.shape.AirShape) :
    budget.security_report pr ins a ⦃ r => r.terms.val.map (fun t => t.bits.val) = reportM pr ins a ⦄ := by
  unfold budget.security_report
  step as ⟨cap, hcap⟩
  by_cases h0 : cap = 0#u64
  · have : capM ins.field_bits.val ins.collision_resistance.val = 0 := by rw [← hcap, h0]; rfl
    simp only [h0, ↓reduceIte]
    step*
    simp [reportM, budget.report.SecurityReport.new, *]
  · have hc0 : capM ins.field_bits.val ins.collision_resistance.val ≠ 0 := by
      rw [← hcap]; intro h; exact h0 (by scalar_tac)
    have hf : ins.field_bits.val ≤ maxField := by
      by_contra h; apply hc0; simp [capM]; omega
    simp only [h0, ↓reduceIte]
    rcases hl : a.lookup with _ | l
    · simp only
      step*
      all_goals
        simp only [budget.report.SecurityReport.new, WP.spec_ok, Array.make_val]
        simp only [reportM, ← hcap]
        rw [ite_eq_right_of_eq_false _ _ (eq_false (by rw [hcap]; exact hc0))]
        simp_all [queryM]
    · simp only
      have hw := l.max_message_width.hBounds
      have hfr := l.fractions_per_row.hBounds
      simp only [UScalarTy.U32_numBits_eq] at hw hfr
      have hmul : (l.max_message_width.val + 2) * l.fractions_per_row.val < 2 ^ 64 := by
        calc (l.max_message_width.val + 2) * l.fractions_per_row.val
            ≤ (2 ^ 32 + 1) * (2 ^ 32 - 1) := Nat.mul_le_mul (by omega) (by omega)
          _ < 2 ^ 64 := by norm_num
      step*
      all_goals
        simp only [budget.report.SecurityReport.new, WP.spec_ok, Array.make_val]
        simp only [reportM, ← hcap]
        rw [ite_eq_right_of_eq_false _ _ (eq_false (by rw [hcap]; exact hc0))]
        simp_all [queryM]

/-! ## The attained level -/

/-- The first-minimum loop returns a position whose value is a minimum. -/
theorem first_minimum_loop_spec (bits : Std.Array Std.U64 7#usize) (b i : Std.Usize)
    (hb : b.val < i.val) (hi : i.val ≤ 7)
    (hmin : ∀ j < i.val, bits.val[b.val]!.val ≤ bits.val[j]!.val) :
    budget.report.first_minimum_loop bits b i ⦃ r =>
      r.val < 7 ∧ ∀ j < 7, bits.val[r.val]!.val ≤ bits.val[j]!.val ⦄ := by
  unfold budget.report.first_minimum_loop
  apply loop.spec_decr_nat (fun s => 7 - s.2.val)
    (fun s => s.1.val < s.2.val ∧ s.2.val ≤ 7 ∧
      ∀ j < s.2.val, bits.val[s.1.val]!.val ≤ bits.val[j]!.val)
  · rintro ⟨b', i'⟩ ⟨hb', hi', hm'⟩
    simp only at hb' hi' hm'
    unfold budget.report.first_minimum_loop.body
    simp only [budget.report.NUM_TERMS]
    by_cases hlt : i' < 7#usize
    · have hlt' : i'.val < 7 := by scalar_tac
      simp only [hlt, ↓reduceIte]
      step*
      have hx : bits.val[i'.val]! = i := by rw [i_post1]; exact getElem!_pos _ _ _
      have hy : bits.val[b'.val]! = i1 := by rw [i1_post1]; exact getElem!_pos _ _ _
      by_cases hc : i < i1
      · have hc' : i.val < i1.val := hc
        simp only [hc, ↓reduceIte]
        step*
        refine ⟨by omega, by omega, fun j hj => ?_, by omega⟩
        rcases Nat.lt_or_ge j i'.val with hj' | hj'
        · have := hm' j hj'; rw [hx]; rw [hy] at this; omega
        · have : j = i'.val := by omega
          subst this; rw [hx]
      · have hc' : ¬ i.val < i1.val := hc
        simp only [hc, ↓reduceIte]
        step*
        refine ⟨by omega, by omega, fun j hj => ?_, by omega⟩
        rcases Nat.lt_or_ge j i'.val with hj' | hj'
        · exact hm' j hj'
        · have : j = i'.val := by omega
          subst this; rw [hx, hy]; omega
    · have h7 : i'.val = 7 := by scalar_tac
      simp only [hlt, ↓reduceIte, WP.spec_ok]
      exact ⟨by omega, fun j hj => hm' j (by omega)⟩
  · exact ⟨hb, hi, hmin⟩

@[step]
theorem first_minimum_spec (bits : Std.Array Std.U64 7#usize) :
    budget.report.first_minimum bits ⦃ r =>
      r.val < 7 ∧ ∀ j < 7, bits.val[r.val]!.val ≤ bits.val[j]!.val ⦄ := by
  unfold budget.report.first_minimum
  apply first_minimum_loop_spec <;> simp

/-- Converting fixed point to whole bits divides by `2^16`, rounding down. -/
@[step]
theorem to_bits_spec (v : Std.U64) (hv : v.val < 2 ^ 48) :
    fixed.to_bits v ⦃ l => l.val = v.val / 2 ^ 16 ⦄ := by
  unfold fixed.to_bits
  simp only [fixed.FRACTIONAL_BITS]
  step as ⟨w, hw⟩
  have hw' : w.val = v.val / 2 ^ 16 := by rw [hw, Nat.shiftRight_eq_div_pow]
  rw [UScalar.cast_val_mod_pow_of_inBounds_eq, hw']
  rw [hw', UScalarTy.U32_numBits_eq]
  exact Nat.div_lt_of_lt_mul (by omega)

/-- The security level is the minimum round, in whole bits rounded down.

This needs every round to be at most the largest supported field size. -/
theorem security_level_spec (r : budget.report.SecurityReport)
    (hb : ∀ j < 7, (r.terms.val.map (fun t => t.bits.val))[j]! ≤ maxField) :
    budget.report.SecurityReport.security_level r ⦃ l => ∃ k < 7,
      l.val = (r.terms.val.map (fun t => t.bits.val))[k]! / 2 ^ 16 ∧
      ∀ j < 7, (r.terms.val.map (fun t => t.bits.val))[k]! ≤
        (r.terms.val.map (fun t => t.bits.val))[j]! ⦄ := by
  unfold budget.report.SecurityReport.security_level budget.report.SecurityReport.attained
    budget.report.SecurityReport.binding_term budget.report.SecurityReport.binding_index
  simp only [Std.bind_assoc]
  have hlen : r.terms.val.length = 7 := by simp
  have hmap : ∀ l : List budget.report.SecurityTerm, (h : l.length = 7) →
      [(l[0]'(by omega)).bits, (l[1]'(by omega)).bits, (l[2]'(by omega)).bits,
        (l[3]'(by omega)).bits, (l[4]'(by omega)).bits, (l[5]'(by omega)).bits,
        (l[6]'(by omega)).bits] = l.map (fun t => t.bits) := by
    intro l h
    match l, h with
    | [_, _, _, _, _, _, _], _ => rfl
  step as ⟨s0, h0a, h0b⟩
  step as ⟨s1, h1a, h1b⟩
  step as ⟨s2, h2a, h2b⟩
  step as ⟨s3, h3a, h3b⟩
  step as ⟨s4, h4a, h4b⟩
  step as ⟨s5, h5a, h5b⟩
  step as ⟨s6, h6a, h6b⟩
  step as ⟨k, hk, hkmin⟩
  step as ⟨x, hxa, hxb⟩
  have hA : (Array.make 7#usize [s0.bits, s1.bits, s2.bits, s3.bits, s4.bits, s5.bits, s6.bits]
      (by simp)).val = r.terms.val.map (fun t => t.bits) := by
    rw [Array.make_val, h0b, h1b, h2b, h3b, h4b, h5b, h6b]; exact hmap _ hlen
  rw [hA] at hkmin
  have hL : ∀ j < 7, (r.terms.val.map (fun t => t.bits.val))[j]! =
      ((r.terms.val.map (fun t : budget.report.SecurityTerm => t.bits))[j]!).val := by
    intro j hj
    rw [getElem!_pos _ _ (by simp only [List.length_map]; omega),
      getElem!_pos _ _ (by simp only [List.length_map]; omega)]
    simp
  have hxv : x.bits.val = (r.terms.val.map (fun t => t.bits.val))[k.val]! := by
    rw [getElem!_pos _ _ (by simp only [List.length_map]; omega), hxb]; simp
  have hx48 : x.bits.val < 2 ^ 48 := by
    have := hb k.val hk; rw [← hxv] at this; unfold maxField at this; omega
  refine WP.spec_mono (to_bits_spec x.bits hx48) ?_
  intro l hl
  exact ⟨k.val, hk, by rw [hl, hxv], fun j hj => by rw [hL k.val hk, hL j hj]; exact hkmin j hj⟩

/-! ## Parameters where the reported level exceeds the bound -/

/-- Blowup 8, binary folding, 200 queries with 30 bits of query grinding. -/
def cexParams : budget.shape.ProtocolParams :=
  { log_blowup := 3#u32, log_folding_arity := 1#u32, num_queries := 200#u32,
    query_pow_bits := 30#u32, ood_pow_bits := 0#u32, deep_pow_bits := 0#u32,
    folding_pow_bits := 0#u32, lookup_pow_bits := 0#u32 }

/-- Trace height 4, `log_2 |E| = 7462235 / 2^16` (about 113.86), and a 128-bit hash. -/
def cexInstance : budget.shape.InstanceShape :=
  { log_max_height := 2#u32, field_bits := 7462235#u64, collision_resistance := 128#u32 }

/-- 14917 constraints of degree 2, two quotient chunks, and two opening points. -/
def cexAir : budget.shape.AirShape :=
  { num_composed_constraints := 14917#u32, max_constraint_degree := 2#u32,
    num_quotient_chunks := 2#u32, max_combo := 2#u32,
    num_deep_terms := .None, lookup := .None }

theorem cex_report : reportM cexParams cexInstance cexAir =
    [7462235, 6553600, 7219722, 7462235, 7069019, 7462235, 7462235] := by
  decide +kernel

/-- **The budget reports 100 bits** at these parameters.

The binding round is the constraint composition, at exactly `100 * 2^16` in fixed point. -/
theorem cex_level :
    ∃ r, budget.security_report cexParams cexInstance cexAir = .ok r ∧
      budget.report.SecurityReport.security_level r ⦃ l => l.val = 100 ⦄ := by
  obtain ⟨r, hr, hmap⟩ := spec_imp_exists (security_report_spec cexParams cexInstance cexAir)
  rw [cex_report] at hmap
  refine ⟨r, hr, ?_⟩
  refine WP.spec_mono (security_level_spec r (fun j hj => ?_)) ?_
  · rw [hmap]; interval_cases j <;> simp [maxField]
  · rintro l ⟨k, hk, hl, hmin⟩
    rw [hmap] at hl hmin
    have h1 := hmin 1 (by omega)
    interval_cases k <;> simp_all

/-- The composition round's true error at these parameters exceeds `2^-100`.

Take `|E| = 2^(7462235 / 2^16)`, the largest field the fixed-point size admits.

Then `14917 / |E| > 2^-100`, that is `2^7462235 < 2^(100 * 2^16) * 14917^(2^16)`. -/
theorem cex_true_bound : 2 ^ 7462235 < 2 ^ (100 * 2 ^ 16) * 14917 ^ 2 ^ 16 := by
  decide +kernel

end Plonky3Lean.Proofs.Security.Budget
