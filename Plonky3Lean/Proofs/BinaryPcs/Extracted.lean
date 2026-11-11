module

public import P3BinaryPcs
public import Plonky3Lean.Proofs.BinaryDft.Extracted
public import Plonky3Lean.Proofs.BinaryPcs.Params
public import Plonky3Lean.Proofs.Matrix.Views
public import Plonky3Lean.Lib.Scalar.Signed
public import Plonky3Lean.Proofs.Matrix.Log2

@[expose] public section

/-!
# The extracted fold and schedule

hax extracts the fold of a pair, generic over the tower-level and extension-field traits.

It also extracts the schedule's change of folding factor, which reads p3-security's ceiling.

The theorems assume a 64-bit word, as the transcriptions do.

The fold's theorem also assumes that the instances' members compute the operations they name.

Under these assumptions each item returns what its transcription computes, and panics exactly when it does.

So the theorems about the transcriptions hold for the shipped code.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open Plonky3Lean.Lib p3_binary_dft.mirror Plonky3Lean.Proofs.BinaryDft

namespace Plonky3Lean.Proofs.BinaryPcs

/-! ## The fold of a pair -/

section Fold

variable {F EF R : Type} [Field F] [Field EF] [Algebra F EF]

/-- The members the fold of a pair calls compute, beyond those of the domain:

- the product in the alphabet
- the product and the sum of a challenge and an alphabet element, through the algebra map -/
structure FoldComputes (inst : p3_binary_field.tower.TowerLevel F R)
    (einst : p3_field.field.ExtensionField EF F) (L : Level F) : Prop
    extends TowerComputes inst L where
  mul : ∀ a b : F, inst.p3_fieldfieldFieldInst.AlgebraInst.coreopsarithMulInst.mul a b = .ok (a * b)
  emul : ∀ (a : EF) (b : F), einst.AlgebraInst.coreopsarithMulInst.mul a b = .ok (a * algebraMap F EF b)
  eadd : ∀ (a : EF) (b : F), einst.AlgebraInst.coreopsarithAddInst.add a b = .ok (a + algebraMap F EF b)

variable {inst : p3_binary_field.tower.TowerLevel F R} {einst : p3_field.field.ExtensionField EF F}
  {L : Level F}

/-- The doubled index wraps at the word. -/
theorem shl_one_eq (h64 : System.Platform.numBits = 64) (index : Std.Usize) :
    ∃ i : Std.Usize, (index <<< 1#i32 : RustM Std.Usize) = .ok i ∧ i.val = 2 * index.val % 2 ^ 64 := by
  refine ⟨_, shiftLeft_i32_eq index 1#i32 (by decide) (by simp [UScalarTy.Usize_numBits_eq, h64]), ?_⟩
  simp only [UScalar.val, BitVec.toNat_shiftLeft, UScalarTy.Usize_numBits_eq, h64]
  rw [show I32.toNat 1#i32 = 1 from rfl, Nat.shiftLeft_eq, pow_one, mul_comm]

/-- The extracted fold of a pair returns what its transcription computes. -/
theorem fold_pair_eq_mirror (h64 : System.Platform.numBits = 64) (h : FoldComputes inst einst L)
    (index : Std.Usize) (beta : EF) (lo hi : F) :
    p3_binary_pcs.fold.fold_pair inst einst index beta lo hi =
      ofOption (p3_binary_pcs.fold.mirror.fold_pair L index.val beta lo hi) := by
  obtain ⟨i, hi, hiv⟩ := shl_one_eq h64 index
  rw [p3_binary_pcs.fold.fold_pair, hi, bind_ok, domain_point_eq_mirror h.toTowerComputes,
    p3_binary_pcs.fold.mirror.fold_pair, hiv]
  cases p3_binary_dft.domain.mirror.domain_point L (2 * index.val % 2 ^ 64) <;>
    simp [ofOption, h.add, h.mul, h.emul, h.eadd]

end Fold

/-! ## Word arithmetic -/

/-- A usize sum that fits is some sum, and one past the word is none. -/
theorem checked_add_eq (x y : Std.Usize) :
    ∃ o, core.num.Usize.checked_add x y = .ok o ∧
      (x.val + y.val < 2 ^ UScalarTy.Usize.numBits → ∃ z : Std.Usize, o = .Some z ∧ z.val = x.val + y.val) ∧
      (2 ^ UScalarTy.Usize.numBits ≤ x.val + y.val → o = .None) := by
  have h := UScalar.overflowing_add_eq x y
  simp only [core.num.Usize.checked_add, core.num.Usize.overflowing_add,
    rust_primitives.arithmetic.overflowing_add_usize, bind_ok]
  generalize UScalar.overflowing_add x y = r at h ⊢
  obtain ⟨z, b⟩ := r
  simp only [UScalar.max] at h
  have hp : 0 < 2 ^ UScalarTy.Usize.numBits := by positivity
  split_ifs at h with hc
  · obtain ⟨-, rfl⟩ := h
    exact ⟨_, rfl, fun hl => by omega, fun _ => rfl⟩
  · obtain ⟨hz, rfl⟩ := h
    exact ⟨_, rfl, fun _ => ⟨z, rfl, hz⟩, fun hl => by omega⟩

/-- The word's power-of-two test, as CoreModels runs it, decides whether the value is a power of two. -/
theorem is_power_of_two_eq (x : Std.Usize) :
    core.num.Usize.is_power_of_two x = .ok (decide x.val.isPowerOfTwo) := by
  unfold core.num.Usize.is_power_of_two
  by_cases h0 : x = 0#usize
  · subst h0
    simp [Nat.not_isPowerOfTwo_zero]
  · have hx : x.val ≠ 0 := fun h => h0 (UScalar.eq_of_val_eq (by simpa using h))
    obtain ⟨y, ey, hy⟩ : ∃ y, x - 1#usize = RustM.ok y ∧ y.val = x.val - 1 := by
      have : x - 1#usize ⦃ z => z.val = x.val - (1#usize : Std.Usize).val ⦄ := by step*
      obtain ⟨y, e1, h1⟩ := spec_imp_exists this
      exact ⟨y, e1, by simpa using h1⟩
    have hne : (x != 0#usize) = true := by simpa using h0
    simp only [hne, ite_true, ey, bind_ok, lift]
    congr 1
    apply decide_eq_decide.mpr
    rw [← Nat.and_sub_one_eq_zero_iff_isPowerOfTwo hx, ← hy, ← UScalar.val_and]
    constructor
    · intro h; rw [h]; rfl
    · intro h; exact UScalar.eq_of_val_eq (by rw [h]; rfl)

/-! ## The security model -/

/-- The model of p3-security's schedule, read as naturals. -/
def regM (s : p3_security.binary.BinaryPcsRegime) : p3_binary_pcs.params.mirror.BinaryPcsRegime :=
  ⟨s.challenge_field_bits.val, s.num_variables.val, s.log_inv_rate.val, s.log_folding_factor.val,
    s.num_queries.val, s.query_pow_bits.val⟩

/-- The extracted model constructor accepts exactly the schedules its transcription accepts. -/
theorem regime_new_eq (h64 : System.Platform.numBits = 64) (K n r f q p : Std.Usize) :
    p3_security.binary.BinaryPcsRegime.new K n r f q p =
      .ok (if (p3_binary_pcs.params.mirror.BinaryPcsRegime.new K.val n.val r.val f.val q.val
          p.val).isSome then .Some ⟨K, n, r, f, q, p⟩ else .None) := by
  obtain ⟨o, ho, hs, hn⟩ := checked_add_eq n r
  rw [p3_security.binary.BinaryPcsRegime.new, ho, bind_ok]
  simp only [UScalarTy.Usize_numBits_eq, h64] at hs hn
  by_cases hw : n.val + r.val < 2 ^ 64
  · obtain ⟨z, rfl, hz⟩ := hs hw
    have hb : (UScalar.cast .Usize core.num.Usize.BITS).val = 64 := by
      simp [UScalar.cast_val_eq, Std.core.num.Usize.BITS, h64]
    simp only [p3_binary_pcs.params.mirror.BinaryPcsRegime.new, is_power_of_two_eq, bind_ok,
      lift, hb, hz, p3_security.binary.BINARY_PCS_FIELD_BITS, p3_binary_pcs.params.mirror.USIZE_BITS,
      p3_binary_pcs.params.mirror.BINARY_PCS_FIELD_BITS, UScalar.lt_equiv, UScalar.le_equiv,
      UScalar.eq_equiv, gt_iff_lt, ge_iff_le, decide_eq_true_eq]
    split_ifs
    all_goals simp_all
    omega
  · rw [hn (by omega)]
    simp [p3_binary_pcs.params.mirror.BinaryPcsRegime.new, p3_binary_pcs.params.mirror.USIZE_BITS]
    intros; omega

/-- The security ceiling of a schedule the model accepts is the transcription's. -/
theorem max_security_bits_eq (h64 : System.Platform.numBits = 64) (s : p3_security.binary.BinaryPcsRegime)
    (hs : (p3_binary_pcs.params.mirror.BinaryPcsRegime.new s.challenge_field_bits.val s.num_variables.val
      s.log_inv_rate.val s.log_folding_factor.val s.num_queries.val s.query_pow_bits.val).isSome) :
    p3_security.binary.BinaryPcsRegime.max_security_bits s ⦃ y =>
      y.val = (regM s).max_security_bits ⦄ := by
  obtain ⟨t, ht⟩ := Option.isSome_iff_exists.1 hs
  obtain ⟨-, -, -, -, hn, hr, hw, -, hf, -⟩ := new_eq_some.1 ht
  have := Security.Binary.max_security_bits_accepted s hw hr hn (by omega)
    (by simp [UScalarTy.Usize_numBits_eq, h64]; omega)
  refine WP.spec_mono this fun y hy => ?_
  have hc := Security.Binary.numeratorSpec_closed s.num_variables.val s.log_inv_rate.val
  rw [hy]
  simp only [regM, p3_binary_pcs.params.mirror.BinaryPcsRegime.max_security_bits,
    p3_binary_pcs.params.mirror.BinaryPcsRegime.field_security_bits,
    p3_binary_pcs.params.mirror.BinaryPcsRegime.field_error_numerator,
    p3_binary_pcs.params.mirror.BinaryPcsRegime.queries_are_exhaustive]
  have hle : 2 ^ s.log_inv_rate.val ≤ 2 ^ (s.num_variables.val + s.log_inv_rate.val) :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  rw [show Security.Binary.numeratorSpec s.num_variables.val s.log_inv_rate.val =
    2 * 2 ^ (s.num_variables.val + s.log_inv_rate.val) - 2 * 2 ^ s.log_inv_rate.val +
      3 * s.num_variables.val by omega]
  by_cases hq : 2 ^ (s.num_variables.val + s.log_inv_rate.val - s.log_folding_factor.val) ≤
    s.num_queries.val <;> simp [hq]

/-! ## The schedule -/

/-- The caller's parameters, read as naturals. -/
def paramsM (p : p3_binary_pcs.params.BinaryPcsParams) : p3_binary_pcs.params.mirror.BinaryPcsParams :=
  ⟨p.log_inv_rate.val, p.pow_bits.val, p.security_level.val⟩

/-- A schedule, read as naturals. -/
def configM (c : p3_binary_pcs.params.BinaryPcsConfig) : p3_binary_pcs.params.mirror.BinaryPcsConfig :=
  ⟨paramsM c.params, c.committed_field_bits.val, c.challenge_field_bits.val, c.num_variables.val,
    c.num_queries.val, c.log_folding_factor.val⟩

/-- A rejection, read as naturals. -/
def errM : p3_binary_pcs.params.BinaryPcsConfigError → p3_binary_pcs.params.mirror.BinaryPcsConfigError
  | .InvalidFoldingFactor a b => .InvalidFoldingFactor a.val b.val
  | .UnpricedChallengeField a => .UnpricedChallengeField a.val
  | .CodewordExceedsAlphabetDomain a b => .CodewordExceedsAlphabetDomain a.val b.val
  | .CodewordLengthExceedsUsize a b => .CodewordLengthExceedsUsize a.val b.val
  | .NoVariablesToFold => .NoVariablesToFold
  | .PowBitsExceedWitnessCapacity a b => .PowBitsExceedWitnessCapacity a.val b.val
  | .SecurityLevelBelowPowBits a b => .SecurityLevelBelowPowBits a.val b.val
  | .SecurityLevelExceedsFieldCapacity a b => .SecurityLevelExceedsFieldCapacity a.val b.val
  | .ZeroQueries => .ZeroQueries
  | .CommittedFieldMismatch a b => .CommittedFieldMismatch a.val b.val
  | .ChallengeFieldMismatch a b => .ChallengeFieldMismatch a.val b.val

/-- A result, read through a map of its value and the reading of its rejection. -/
def resM {α β : Type} (f : α → β) :
    core.result.Result α p3_binary_pcs.params.BinaryPcsConfigError →
      Except p3_binary_pcs.params.mirror.BinaryPcsConfigError β
  | .Ok a => .ok (f a)
  | .Err e => .error (errM e)

/-- A computation's value, read through a map. -/
def liftR {α β : Type} (f : α → β) (m : RustM α) : RustM β := do
  let x ← m
  .ok (f x)

/-- A computation whose reading returns a value returns a preimage of it. -/
theorem liftR_ok {α β : Type} {f : α → β} {m : RustM α} {b : β} (h : liftR f m = .ok b) :
    ∃ a, m = .ok a ∧ f a = b := by
  cases m with
  | ret a => exact ⟨a, rfl, by simpa [liftR] using h⟩
  | vis i k => cases i with | fail e => simp [liftR] at h
  | div => simp [liftR] at h

/-- The extracted target check returns what its transcription computes. -/
theorem validate_security_eq (h64 : System.Platform.numBits = 64)
    (c : p3_binary_pcs.params.BinaryPcsConfig) :
    match (configM c).validate_security with
    | none => p3_binary_pcs.params.BinaryPcsConfig.validate_security c = .fail .panic
    | some r => ∃ x, p3_binary_pcs.params.BinaryPcsConfig.validate_security c = .ok x ∧
        resM id x = r := by
  unfold p3_binary_pcs.params.BinaryPcsConfig.validate_security
    p3_binary_pcs.params.BinaryPcsConfig.security_regime
    p3_binary_pcs.params.BinaryPcsConfig.try_security_regime
    p3_binary_pcs.params.mirror.BinaryPcsConfig.validate_security
    p3_binary_pcs.params.mirror.BinaryPcsConfig.security_regime
    p3_binary_pcs.params.mirror.BinaryPcsConfig.try_security_regime
  rw [regime_new_eq h64]
  simp only [configM, paramsM]
  cases hn : p3_binary_pcs.params.mirror.BinaryPcsRegime.new c.challenge_field_bits.val
      c.num_variables.val c.params.log_inv_rate.val c.log_folding_factor.val c.num_queries.val
      c.params.pow_bits.val with
  | none => simp
  | some t =>
    obtain ⟨rfl, -⟩ := new_eq_some.1 hn
    obtain ⟨m, hm, hmv⟩ := spec_imp_exists (max_security_bits_eq h64
      ⟨c.challenge_field_bits, c.num_variables, c.params.log_inv_rate, c.log_folding_factor,
        c.num_queries, c.params.pow_bits⟩ (by simp [hn]))
    simp only [Option.isSome_some, ↓reduceIte, bind_ok, hm]
    simp only [regM] at hmv
    by_cases h1 : c.params.security_level.val > m.val
    · have h1' : c.params.security_level > m := by simpa [UScalar.lt_equiv] using h1
      simp only [h1', ↓reduceIte]
      rw [hmv] at h1
      simp [resM, errM, h1, hmv]
    · have h1' : ¬ c.params.security_level > m := by simpa [UScalar.lt_equiv] using h1
      simp only [h1', ↓reduceIte]
      rw [hmv] at h1
      simp [resM, h1]

/-- The extracted change of folding factor returns what its transcription computes. -/
theorem try_with_folding_eq (h64 : System.Platform.numBits = 64)
    (c : p3_binary_pcs.params.BinaryPcsConfig) (lff : Std.Usize) :
    liftR (resM configM) (p3_binary_pcs.params.BinaryPcsConfig.try_with_folding c lff) =
      ofOption ((configM c).try_with_folding lff.val) := by
  unfold p3_binary_pcs.params.BinaryPcsConfig.try_with_folding
    p3_binary_pcs.params.mirror.BinaryPcsConfig.try_with_folding
  by_cases h0 : lff.val = 0
  · have : lff = 0#usize := UScalar.eq_of_val_eq (by simp [h0])
    subst this
    simp [liftR, ofOption, resM, errM, configM]
  by_cases h1 : c.num_variables.val < lff.val
  · have h0' : lff ≠ 0#usize := fun e => h0 (by simp [e])
    simp [h0', h0, h1, UScalar.lt_equiv, liftR, ofOption, resM, errM, configM]
  · have h0' : lff ≠ 0#usize := fun e => h0 (by simp [e])
    have hv := validate_security_eq h64 { c with log_folding_factor := lff }
    simp only [h0', ↓reduceIte, gt_iff_lt, UScalar.lt_equiv, h1, h0, false_or]
    have e : configM { c with log_folding_factor := lff } = { configM c with log_folding_factor := lff.val } := rfl
    rw [e] at hv
    simp only [configM, paramsM] at hv ⊢
    simp only [h1, ↓reduceIte]
    split at hv
    · rename_i hvo
      simp [hvo, hv, liftR, ofOption]
    · rename_i r hvo
      obtain ⟨x, hx, hr⟩ := hv
      simp only [hvo, hx, bind_ok, liftR]
      cases x <;> cases r <;> simp_all [resM, ofOption,
        core.result.Result.Insts.CoreOpsTry_traitTryTResultInfallibleE.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResultInfallibleE.from_residual,
        core.convert.From.Blanket.from, configM, paramsM]

/-- The extracted batch count returns what its transcription computes, and panics at a zero factor. -/
theorem num_fold_batches_eq (c : p3_binary_pcs.params.BinaryPcsConfig) :
    liftR UScalar.val (p3_binary_pcs.params.BinaryPcsConfig.num_fold_batches c) =
      ofOption (configM c).num_fold_batches := by
  unfold p3_binary_pcs.params.BinaryPcsConfig.num_fold_batches
    p3_binary_pcs.params.mirror.BinaryPcsConfig.num_fold_batches
  by_cases h0 : c.log_folding_factor.val = 0
  · have : c.log_folding_factor = 0#usize := UScalar.eq_of_val_eq (by simp [h0])
    simp [configM, this, liftR, ofOption, core.num.Usize.div_ceil, HDiv.hDiv, UScalar.div]
  · obtain ⟨d, hd, hdv⟩ := spec_imp_exists (Matrix.div_ceil_eq c.num_variables c.log_folding_factor
      (by omega))
    simp [hd, liftR, ofOption, configM, h0, hdv]

/-- The extracted model lookup of a schedule. -/
theorem try_security_regime_eq (h64 : System.Platform.numBits = 64)
    (c : p3_binary_pcs.params.BinaryPcsConfig) :
    p3_binary_pcs.params.BinaryPcsConfig.try_security_regime c =
      .ok (if (p3_binary_pcs.params.mirror.BinaryPcsRegime.new c.challenge_field_bits.val
          c.num_variables.val c.params.log_inv_rate.val c.log_folding_factor.val c.num_queries.val
          c.params.pow_bits.val).isSome then
        .Ok ⟨c.challenge_field_bits, c.num_variables, c.params.log_inv_rate, c.log_folding_factor,
          c.num_queries, c.params.pow_bits⟩
      else .Err (.UnpricedChallengeField c.challenge_field_bits)) := by
  unfold p3_binary_pcs.params.BinaryPcsConfig.try_security_regime
  rw [regime_new_eq h64]
  split <;> simp

/-- The word of a natural number. -/
def usizeOf (a : ℕ) : Std.Usize := ⟨BitVec.ofNat _ a⟩

/-- p3-security's query count, read as naturals. -/
def queriesNat (a b c : ℕ) : ℕ :=
  (p3_security.binary.BinaryPcsRegime.queriesForTargetCount (usizeOf a) (usizeOf b) (usizeOf c)).val

theorem usizeOf_val (x : Std.Usize) : usizeOf x.val = x := by
  apply UScalar.eq_of_val_eq
  simp only [usizeOf, UScalar.val, BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt x.bv.isLt

/-- The extracted constructor returns what its transcription computes, with p3-security's query count. -/
theorem try_new_with_folding_eq (h64 : System.Platform.numBits = 64) {F EF Enc R0 R1 : Type}
    (encInst : p3_binary_dft.encoder.EncodableLevel F Enc R0)
    (tInst : p3_binary_field.tower.TowerLevel EF R1) (fb eb : Std.Usize)
    (hfb : encInst.p3_binary_fieldtowerTowerLevelInst.p3_fieldfieldFieldInst.bits = .ok fb)
    (heb : tInst.p3_fieldfieldFieldInst.bits = .ok eb)
    (n : Std.Usize) (params : p3_binary_pcs.params.BinaryPcsParams) (lff : Std.Usize) :
    liftR (resM configM)
        (p3_binary_pcs.params.BinaryPcsConfig.try_new_with_folding encInst tInst n params lff) =
      ofOption (p3_binary_pcs.params.mirror.try_new_with_folding queriesNat fb.val eb.val n.val
        (paramsM params) lff.val) := by
  unfold p3_binary_pcs.params.BinaryPcsConfig.try_new_with_folding
    p3_binary_pcs.params.mirror.try_new_with_folding
  have hbits : (UScalar.cast .Usize core.num.Usize.BITS).val = 64 := by
    simp [UScalar.cast_val_eq, Std.core.num.Usize.BITS, h64]
  obtain ⟨o, ho, hs, hn⟩ := checked_add_eq n params.log_inv_rate
  simp only [UScalarTy.Usize_numBits_eq, h64] at hs hn
  simp only [lift, bind_ok, ho, core.num.Usize.saturating_add_exposed, paramsM,
    p3_binary_pcs.params.mirror.USIZE_BITS, p3_binary_pcs.params.mirror.POW_COUNTER_BITS,
    p3_binary_pcs.params.mirror.POW_HEADER_BITS]
  have hLv : ∀ a : ℕ, a < 2 ^ 64 →
      (⟨BitVec.ofNat UScalarTy.Usize.numBits (min a (2 ^ System.Platform.numBits - 1))⟩ : Std.Usize).val
        = a := by
    intro a ha
    simp only [UScalar.val, BitVec.toNat_ofNat, UScalarTy.Usize_numBits_eq, h64]
    rw [min_eq_left (by omega), Nat.mod_eq_of_lt ha]
  by_cases hw : n.val + params.log_inv_rate.val < 64
  · obtain ⟨z, rfl, hz⟩ := hs (by omega)
    have hzlt : z < UScalar.cast .Usize core.num.Usize.BITS := by
      rw [UScalar.lt_equiv, hbits, hz]; exact hw
    have hmin : min (n.val + params.log_inv_rate.val) (2 ^ 64 - 1) = n.val + params.log_inv_rate.val :=
      min_eq_left (by omega)
    have hL := hLv _ (by omega : n.val + params.log_inv_rate.val < 2 ^ 64)
    generalize (⟨BitVec.ofNat UScalarTy.Usize.numBits (min (n.val + params.log_inv_rate.val)
      (2 ^ System.Platform.numBits - 1))⟩ : Std.Usize) = L at hL ⊢
    simp only [hzlt, ↓reduceIte, bind_ok, hw, not_true_eq_false, UScalar.eq_equiv,
      show (0#usize : Std.Usize).val = 0 from rfl, hmin]
    by_cases hn0 : n.val = 0
    · simp [hn0, liftR, ofOption, resM, errM]
    by_cases hl0 : lff.val = 0
    · simp [hn0, hl0, liftR, ofOption, resM, errM]
    by_cases hln : n.val < lff.val
    · simp [hn0, hl0, hln, UScalar.lt_equiv, liftR, ofOption, resM, errM]
    simp only [hn0, hl0, hln, UScalar.lt_equiv, gt_iff_lt, false_or, ↓reduceIte, hfb, bind_ok, hL]
    by_cases hfl : fb.val < n.val + params.log_inv_rate.val
    · simp [hfl, liftR, ofOption, resM, errM, hL]
    obtain ⟨m1, hm1, hm1v⟩ := spec_imp_exists
      (Lib.core.Usize.Insts.CoreCmpOrd.min.spec fb p3_binary_pcs.params.POW_COUNTER_BITS)
    have hpc : (p3_binary_pcs.params.POW_COUNTER_BITS).val = 64 := by
      unfold p3_binary_pcs.params.POW_COUNTER_BITS; rfl
    have hph : (p3_binary_pcs.params.POW_HEADER_BITS).val = 8 := by
      unfold p3_binary_pcs.params.POW_HEADER_BITS; rfl
    rw [hpc] at hm1v
    simp only [hfl, ↓reduceIte, hm1, bind_ok]
    by_cases h8 : min fb.val 64 < 8
    · rw [usize_sub_fail _ _ (by rw [hm1v, hph]; exact h8)]
      simp [h8, liftR, ofOption]
    obtain ⟨mp, hmp, hmpv⟩ := usize_sub_ok m1 p3_binary_pcs.params.POW_HEADER_BITS (by omega)
    rw [hm1v, hph] at hmpv
    simp only [hmp, bind_ok, h8, ↓reduceIte, hmpv]
    by_cases hp : min fb.val 64 - 8 < params.pow_bits.val
    · simp [hp, liftR, ofOption, resM, errM, hmpv]
    by_cases hsl : params.security_level.val ≤ params.pow_bits.val
    · simp [hp, hsl, UScalar.le_equiv, liftR, ofOption, resM, errM]
    simp only [hp, hsl, UScalar.le_equiv, ↓reduceIte, p3_security.binary.BinaryPcsRegime.queries_for_target,
      bind_ok, queriesNat, usizeOf_val]
    by_cases hq0 : (p3_security.binary.BinaryPcsRegime.queriesForTargetCount params.security_level
      params.log_inv_rate params.pow_bits).val = 0
    · simp [hq0, liftR, ofOption, resM, errM]
    simp only [hq0, ↓reduceIte, heb, bind_ok, try_security_regime_eq h64]
    generalize p3_security.binary.BinaryPcsRegime.queriesForTargetCount params.security_level
      params.log_inv_rate params.pow_bits = q at hq0 ⊢
    have hv := validate_security_eq h64 ⟨params, fb, eb, n, q, lff⟩
    simp only [configM, paramsM] at hv
    unfold p3_binary_pcs.params.mirror.BinaryPcsConfig.try_security_regime
    dsimp only
    by_cases hnew : (p3_binary_pcs.params.mirror.BinaryPcsRegime.new eb.val n.val
      params.log_inv_rate.val lff.val q.val params.pow_bits.val).isSome
    · obtain ⟨t, ht⟩ := Option.isSome_iff_exists.1 hnew
      split at hv
      · rename_i hvo
        simp [hvo, hv, ht, liftR, ofOption,
          core.result.Result.Insts.CoreOpsTry_traitTryTResultInfallibleE.branch]
      · rename_i r hvo
        obtain ⟨x, hx, hr⟩ := hv
        cases x <;> cases r <;> simp_all [resM, ofOption, liftR,
          core.result.Result.Insts.CoreOpsTry_traitTryTResultInfallibleE.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResultInfallibleE.from_residual,
          core.convert.From.Blanket.from, configM, paramsM]
    · rw [Option.not_isSome_iff_eq_none] at hnew
      simp [hnew, core.result.Result.Insts.CoreOpsTry_traitTryTResultInfallibleE.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResultInfallibleE.from_residual,
        core.convert.From.Blanket.from, liftR, ofOption, resM, errM]
  · have hval : (⟨BitVec.ofNat UScalarTy.Usize.numBits (min (n.val + params.log_inv_rate.val)
        (2 ^ System.Platform.numBits - 1))⟩ : Std.Usize).val =
        min (n.val + params.log_inv_rate.val) 18446744073709551615 := by
      simp only [UScalar.val, BitVec.toNat_ofNat, UScalarTy.Usize_numBits_eq, h64]
      exact Nat.mod_eq_of_lt (by omega)
    generalize (⟨BitVec.ofNat UScalarTy.Usize.numBits (min (n.val + params.log_inv_rate.val)
      (2 ^ System.Platform.numBits - 1))⟩ : Std.Usize) = L at hval ⊢
    by_cases h2 : n.val + params.log_inv_rate.val < 2 ^ 64
    · obtain ⟨z, rfl, hz⟩ := hs h2
      have : ¬ z < UScalar.cast .Usize core.num.Usize.BITS := by
        rw [UScalar.lt_equiv, hbits, hz]; exact hw
      simp [this, hw, liftR, ofOption, resM, errM, hval, hbits]
    · rw [hn (by omega)]
      simp [hw, liftR, ofOption, resM, errM, hval, hbits]

/-! ## The transcript shape -/

/-- A transcript shape, read as naturals. -/
def shapeM (s : p3_binary_pcs.transcript.BinaryPcsShape) : p3_binary_pcs.transcript.mirror.BinaryPcsShape :=
  ⟨s.num_variables.val, s.log_folding_factor.val, s.num_oracles.val, s.final_codeword_len.val,
    s.pow_bits.val, s.pair_bits.val, s.num_pairs.val⟩

/-- On an accepted schedule, the extracted transcript shape never panics and is the transcription's. -/
theorem shape_new_spec (h64 : System.Platform.numBits = 64) (c : p3_binary_pcs.params.BinaryPcsConfig)
    (h : Inv (configM c)) :
    p3_binary_pcs.transcript.BinaryPcsShape.new c ⦃ s =>
      some (shapeM s) = p3_binary_pcs.transcript.mirror.BinaryPcsShape.new (configM c) ⦄ := by
  have hb := h.batches_pos
  have hl := h.lff_pos
  have hle := h.lff_le
  have hr := h.r_pos
  have hw := h.word
  rw [h.shape]
  simp only [configM, paramsM] at hb hl hle hr hw ⊢
  unfold p3_binary_pcs.transcript.BinaryPcsShape.new p3_binary_pcs.params.BinaryPcsConfig.domain_size
    p3_binary_pcs.params.BinaryPcsConfig.log_domain_size
    p3_binary_pcs.params.BinaryPcsConfig.num_fold_batches
    p3_binary_pcs.params.BinaryPcsConfig.impl.log_folding_factor
    p3_binary_pcs.params.BinaryPcsConfig.impl.num_variables
    p3_binary_pcs.params.BinaryPcsConfig.impl.num_queries
    p3_binary_pcs.params.BinaryPcsConfig.log_final_len
    p3_binary_pcs.params.BinaryPcsConfig.pow_bits
    p3_binary_pcs.verifier.num_distinct_queries
  have hnb : UScalarTy.Usize.numBits = 64 := by simp [h64]
  step*
  have hi1 : i1.val = 2 ^ (c.num_variables.val + c.params.log_inv_rate.val) := by
    rw [i1_post, Nat.one_shiftLeft, x_post, Usize.size, Usize.numBits_def, hnb]
    exact Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by norm_num) hw)
  have hpd : pair_domain.val / 2 =
      2 ^ (c.num_variables.val + c.params.log_inv_rate.val - c.log_folding_factor.val) := by
    rw [pair_domain_post, hi1, shift_post, ← shift_post]
    rw [shift_post]
    exact pow_shiftRight_div hl (by omega)
  obtain ⟨d, hd, hdv⟩ := spec_imp_exists (Matrix.div_ceil_eq c.num_variables c.log_folding_factor hl)
  simp only [hd, bind_ok]
  step*
  obtain ⟨lg, hlg, hlgv⟩ := spec_imp_exists (Matrix.log2_strict_usize_two_pow
    (k := c.num_variables.val + c.params.log_inv_rate.val - c.log_folding_factor.val)
    (by rw [hnb]; omega) i8 (by rw [i8_post, hpd]))
  simp only [hlg, bind_ok]
  step*
  have hi6 : i6.val = 2 ^ c.params.log_inv_rate.val := by
    rw [i6_post, Nat.one_shiftLeft, Usize.size, Usize.numBits_def, hnb]
    exact Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by norm_num) (by omega))
  split_ifs with hq <;> simp only [bind_ok, WP.spec_ok, shapeM, Option.some.injEq,
    p3_binary_pcs.transcript.mirror.BinaryPcsShape.mk.injEq] <;> simp only [UScalar.lt_equiv] at hq <;>
    refine ⟨trivial, trivial, by omega, hi6, trivial, hlgv, by omega⟩

end Plonky3Lean.Proofs.BinaryPcs
