module

public import P3UniStark
public import Plonky3Lean.Lib

@[expose] public section

/-!
# The extracted integer helpers

- The power of two is defined exactly below the word size.
- The degree-bits validation rejects with the right error.
- It panics only when the minimum overflows the word.
-/

namespace Plonky3Lean.Proofs.UniStark.Extracted

open Aeneas Aeneas.Std CoreModels

/-- The word size of the platform. -/
abbrev W : ℕ := UScalarTy.Usize.numBits

theorem W_cases : W = 32 ∨ W = 64 := by
  unfold W; rw [UScalarTy.Usize_numBits_eq]; exact System.Platform.numBits_eq

/-- The power of two is 2^n below the word size, and absent from it on. -/
@[step]
theorem checked_pow2_spec (n : Std.Usize) :
    p3_util.checked_pow2 n ⦃ o => match o with
      | .Some v => n.val < W ∧ v.val = 2 ^ n.val
      | .None => W ≤ n.val ⦄ := by
  unfold p3_util.checked_pow2
  step*
  refine ⟨«System.Platform.numBits_post», ?_⟩
  rw [i1_post, Nat.shiftLeft_eq, one_mul, Nat.mod_eq_of_lt (by
    rw [Usize.size_scalarTac_eq.2]; exact Nat.pow_lt_pow_right (by norm_num) «System.Platform.numBits_post»)]

/-- The degree-bits validation, when the minimum fits the word.

Write b for the degree bits and z for the zero-knowledge bit.

- Below z + min, it reports the bits too small, with that minimum.
- Above max, it reports them too large, with that maximum.
- At the word size or above, it reports them too large, with the word size minus one.
- Otherwise it returns the base domain's bits b - z and the extended domain's size 2^b. -/
theorem validate_degree_bits_spec (air : core.option.Option Std.Usize) (db zk lo hi : Std.Usize)
    (h : zk.val + lo.val ≤ Usize.max) :
    p3_uni_stark.verifier.validate_degree_bits air db zk lo hi ⦃ r =>
      if db.val < zk.val + lo.val then
        ∃ m : Std.Usize, m.val = zk.val + lo.val ∧
          r = .Err (.DegreeBitsTooSmall air m db)
      else if hi.val < db.val then r = .Err (.DegreeBitsTooLarge air hi db)
      else if W ≤ db.val then
        ∃ m : Std.Usize, m.val = W - 1 ∧ r = .Err (.DegreeBitsTooLarge air m db)
      else ∃ a b : Std.Usize, a.val = db.val - zk.val ∧ b.val = 2 ^ db.val ∧ r = .Ok (a, b) ⦄ := by
  unfold p3_uni_stark.verifier.validate_degree_bits
  step*
  have hdb1 : ¬ db.val < zk.val + lo.val := by scalar_tac
  have hdb2 : ¬ hi.val < db.val := by scalar_tac
  have hi : i.val = W := by
    rw [i_post]; simp [UScalar.cast_val_eq, Std.core.num.Usize.BITS]
  simp only [hdb1, hdb2, ↓reduceIte]
  rcases o with _ | v
  · simp only at o_post
    simp [CoreModels.core.option.Option.ok_or,
      CoreModels.core.result.Result.Insts.CoreOpsTry_traitTryTResultInfallibleE.branch,
      CoreModels.core.result.Result.Insts.CoreOpsTry_traitFromResidualResultInfallibleE.from_residual,
      CoreModels.core.convert.From.Blanket, CoreModels.core.convert.From.Blanket.from]
    exact ⟨o_post, by rw [i1_post, hi]; rfl⟩
  · obtain ⟨hlt, hv⟩ := o_post
    simp [CoreModels.core.option.Option.ok_or,
      CoreModels.core.result.Result.Insts.CoreOpsTry_traitTryTResultInfallibleE.branch]
    step*

/-- The opening rounds, in order:

- the randomization round, when hiding
- the trace
- the quotient
- the preprocessed trace. -/
theorem StarkOpeningLayout_new_spec (zk : Bool) :
    p3_uni_stark.config.StarkOpeningLayout.new zk ⦃ l =>
      l.trace.val = zk.toNat ∧ l.quotient.val = zk.toNat + 1 ∧ l.preprocessed.val = zk.toNat + 2 ⦄ := by
  unfold p3_uni_stark.config.StarkOpeningLayout.new
  have : zk.toNat ≤ 1 := Bool.toNat_le zk
  step*

end Plonky3Lean.Proofs.UniStark.Extracted
