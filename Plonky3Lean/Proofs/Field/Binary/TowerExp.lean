module

public import Plonky3Lean.Proofs.Field.Binary.Frobenius

@[expose] public section

/-!
# `exp_power_of_2` from `GF(2^16)` up

As below `GF(2^16)`, it reduces the power modulo `BITS` and conjugates for a power of at least
`BITS/2`. It then applies `frobenius_N` instead of squaring: `frobNat` is a power of the field
element (`fromNat_frobNat`).
-/

open Aeneas Aeneas.Std CoreModels
open p3_binary_field ConcreteBinaryTower ConcreteBinaryTower.Coordinates
open Plonky3Lean.Lib Plonky3Lean.Spec.BinaryField

namespace Plonky3Lean.Proofs.Binary

theorem fromNat_sqNat {K a : ℕ} (ha : a < 2 ^ 2 ^ K) :
    (fromNat (sqNat K a) : ConcreteBTField K) = fromNat a * fromNat a := by
  apply ConcreteBTField.toNat_injective
  rw [show (fromNat a : ConcreteBTField K) * fromNat a = concrete_mul (fromNat a) (fromNat a) from rfl,
    toNat_concrete_mul, ConcreteBTField.toNat_fromNat, ConcreteBTField.toNat_fromNat,
    Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt (sqNat_lt ha), sqNat_eq K ha]

theorem fromNat_frobNat {K : ℕ} : ∀ (e : ℕ) {a : ℕ}, a < 2 ^ 2 ^ K →
    (fromNat (frobNat K e a) : ConcreteBTField K) = (fromNat a) ^ 2 ^ e
  | 0, _, _ => by simp [frobNat]
  | e + 1, a, ha => by
    rw [frobNat, Function.iterate_succ_apply, ← frobNat, fromNat_frobNat e (sqNat_lt ha),
      fromNat_sqNat ha, ← pow_two, ← pow_mul, ← pow_succ']

theorem bf16_exp_power_of_2_spec (a : tower.BinaryField16) (n : Std.Usize) :
    tower.BinaryField16.Insts.P3_fieldFieldPrimeCharacteristicRing.exp_power_of_2 a n ⦃ r =>
      r.val < 2 ^ 2 ^ 4 ∧ towerOf 4 r = towerOf 4 a ^ 2 ^ n.val ⦄ := by
  have hA : a.val < 2 ^ 2 ^ 4 := by have := a.hBounds; simpa using this
  unfold tower.BinaryField16.Insts.P3_fieldFieldPrimeCharacteristicRing.exp_power_of_2
  simp only [tower.BinaryField16.BITS]
  step*
  have hmod : towerOf 4 a ^ 2 ^ n.val = towerOf 4 a ^ 2 ^ power.val := by
    rw [pow_two_pow_mod, power_post]; norm_num
  rw [hmod]
  refine WP.spec_bind (Pₘ := fun pv => pv.2.val < 2 ^ 2 ^ 4 ∧ pv.1.val < 2 ^ 3 ∧
    ∃ e, towerOf 4 pv.2 = towerOf 4 a ^ 2 ^ e ∧ e + pv.1.val = power.val) ?_ ?_
  · split
    · step*
      have hg1 : bf1.val < 2 ^ 2 ^ 3 := by scalar_tac
      have hhi : hi.val < 2 ^ 2 ^ 3 := by scalar_tac
      refine ⟨by rw [value1_post]; exact join_lt hg1 hhi, by scalar_tac, 2 ^ 3,
        towerOf_conj lo_post lo_post1 (by rw [towerOf_add bf1_post, towerOf_mul_Z bf_post]) hg1
          value1_post, ?_⟩
      rw [power2_post, i_post]
      omega
    · rw [WP.spec_ok]
      exact ⟨hA, by scalar_tac, 0, by simp, by simp⟩
  · rintro ⟨p1, v⟩ ⟨hv, hp1, e, hve, hep⟩
    dsimp only at hv hp1 hve hep
    show (if p1 = 1#usize then tower.BinaryField16.Insts.P3_fieldFieldPrimeCharacteristicRing.square v
      else if 16#usize ≥ 16#usize then do
        let i1 ← linear.frobenius_16 v p1
        tower.BinaryField16.from_repr i1
      else tower.BinaryField16.Insts.P3_fieldFieldPrimeCharacteristicRing.exp_power_of_2_loop
          { start := 0#usize, «end» := p1 } v) ⦃ r =>
        r.val < 2 ^ 2 ^ 4 ∧ towerOf 4 r = towerOf 4 a ^ 2 ^ power.val ⦄
    split
    · refine WP.spec_mono (bf16_square_spec v) fun r hr => ⟨hr ▸ towerMul_lt _ hv hv, ?_⟩
      rw [towerOf_mul hr, hve, ← pow_two, ← pow_mul, ← pow_succ, ← hep,
        show p1.val = 1 by simp [*]]
    · rw [ite_eq_left (by decide)]
      refine WP.spec_bind (frobenius_16_spec v p1 (by omega)) fun i1 hi1 => ?_
      refine WP.spec_mono (bf16_from_repr_spec i1) fun r hr => ?_
      have hlt : i1.val < 2 ^ 2 ^ 4 := hi1 ▸ frobNat_lt _ hv
      rw [Nat.mod_eq_of_lt hlt] at hr
      refine ⟨hr ▸ hlt, ?_⟩
      have e1 : towerOf 4 r = towerOf 4 v ^ 2 ^ p1.val := by
        simp only [towerOf]; rw [hr, hi1, fromNat_frobNat _ hv]
      rw [e1, hve, ← pow_mul, ← pow_add, hep]

theorem bf32_exp_power_of_2_spec (a : tower.BinaryField32) (n : Std.Usize) :
    tower.BinaryField32.Insts.P3_fieldFieldPrimeCharacteristicRing.exp_power_of_2 a n ⦃ r =>
      r.val < 2 ^ 2 ^ 5 ∧ towerOf 5 r = towerOf 5 a ^ 2 ^ n.val ⦄ := by
  have hA : a.val < 2 ^ 2 ^ 5 := by have := a.hBounds; simpa using this
  unfold tower.BinaryField32.Insts.P3_fieldFieldPrimeCharacteristicRing.exp_power_of_2
  simp only [tower.BinaryField32.BITS]
  step*
  have hmod : towerOf 5 a ^ 2 ^ n.val = towerOf 5 a ^ 2 ^ power.val := by
    rw [pow_two_pow_mod, power_post]; norm_num
  rw [hmod]
  refine WP.spec_bind (Pₘ := fun pv => pv.2.val < 2 ^ 2 ^ 5 ∧ pv.1.val < 2 ^ 4 ∧
    ∃ e, towerOf 5 pv.2 = towerOf 5 a ^ 2 ^ e ∧ e + pv.1.val = power.val) ?_ ?_
  · split
    · step*
      have hg1 : bf1.val < 2 ^ 2 ^ 4 := by scalar_tac
      have hhi : hi.val < 2 ^ 2 ^ 4 := by scalar_tac
      refine ⟨by rw [value1_post]; exact join_lt hg1 hhi, by scalar_tac, 2 ^ 4,
        towerOf_conj lo_post lo_post1 (by rw [towerOf_add bf1_post, towerOf_mul_Z bf_post]) hg1
          value1_post, ?_⟩
      rw [power2_post, i_post]
      omega
    · rw [WP.spec_ok]
      exact ⟨hA, by scalar_tac, 0, by simp, by simp⟩
  · rintro ⟨p1, v⟩ ⟨hv, hp1, e, hve, hep⟩
    dsimp only at hv hp1 hve hep
    show (if p1 = 1#usize then tower.BinaryField32.Insts.P3_fieldFieldPrimeCharacteristicRing.square v
      else if 32#usize ≥ 16#usize then do
        let i1 ← linear.frobenius_32 v p1
        tower.BinaryField32.from_repr i1
      else tower.BinaryField32.Insts.P3_fieldFieldPrimeCharacteristicRing.exp_power_of_2_loop
          { start := 0#usize, «end» := p1 } v) ⦃ r =>
        r.val < 2 ^ 2 ^ 5 ∧ towerOf 5 r = towerOf 5 a ^ 2 ^ power.val ⦄
    split
    · refine WP.spec_mono (bf32_square_spec v) fun r hr => ⟨hr ▸ towerMul_lt _ hv hv, ?_⟩
      rw [towerOf_mul hr, hve, ← pow_two, ← pow_mul, ← pow_succ, ← hep,
        show p1.val = 1 by simp [*]]
    · rw [ite_eq_left (by decide)]
      refine WP.spec_bind (frobenius_32_spec v p1 (by omega)) fun i1 hi1 => ?_
      refine WP.spec_mono (bf32_from_repr_spec i1) fun r hr => ?_
      have hlt : i1.val < 2 ^ 2 ^ 5 := hi1 ▸ frobNat_lt _ hv
      rw [Nat.mod_eq_of_lt hlt] at hr
      refine ⟨hr ▸ hlt, ?_⟩
      have e1 : towerOf 5 r = towerOf 5 v ^ 2 ^ p1.val := by
        simp only [towerOf]; rw [hr, hi1, fromNat_frobNat _ hv]
      rw [e1, hve, ← pow_mul, ← pow_add, hep]

theorem bf64_exp_power_of_2_spec (a : tower.BinaryField64) (n : Std.Usize) :
    tower.BinaryField64.Insts.P3_fieldFieldPrimeCharacteristicRing.exp_power_of_2 a n ⦃ r =>
      r.val < 2 ^ 2 ^ 6 ∧ towerOf 6 r = towerOf 6 a ^ 2 ^ n.val ⦄ := by
  have hA : a.val < 2 ^ 2 ^ 6 := by have := a.hBounds; simpa using this
  unfold tower.BinaryField64.Insts.P3_fieldFieldPrimeCharacteristicRing.exp_power_of_2
  simp only [tower.BinaryField64.BITS]
  step*
  have hmod : towerOf 6 a ^ 2 ^ n.val = towerOf 6 a ^ 2 ^ power.val := by
    rw [pow_two_pow_mod, power_post]; norm_num
  rw [hmod]
  refine WP.spec_bind (Pₘ := fun pv => pv.2.val < 2 ^ 2 ^ 6 ∧ pv.1.val < 2 ^ 5 ∧
    ∃ e, towerOf 6 pv.2 = towerOf 6 a ^ 2 ^ e ∧ e + pv.1.val = power.val) ?_ ?_
  · split
    · step*
      have hg1 : bf1.val < 2 ^ 2 ^ 5 := by scalar_tac
      have hhi : hi.val < 2 ^ 2 ^ 5 := by scalar_tac
      refine ⟨by rw [value1_post]; exact join_lt hg1 hhi, by scalar_tac, 2 ^ 5,
        towerOf_conj lo_post lo_post1 (by rw [towerOf_add bf1_post, towerOf_mul_Z bf_post]) hg1
          value1_post, ?_⟩
      rw [power2_post, i_post]
      omega
    · rw [WP.spec_ok]
      exact ⟨hA, by scalar_tac, 0, by simp, by simp⟩
  · rintro ⟨p1, v⟩ ⟨hv, hp1, e, hve, hep⟩
    dsimp only at hv hp1 hve hep
    show (if p1 = 1#usize then tower.BinaryField64.Insts.P3_fieldFieldPrimeCharacteristicRing.square v
      else if 64#usize ≥ 16#usize then do
        let i1 ← linear.frobenius_64 v p1
        tower.BinaryField64.from_repr i1
      else tower.BinaryField64.Insts.P3_fieldFieldPrimeCharacteristicRing.exp_power_of_2_loop
          { start := 0#usize, «end» := p1 } v) ⦃ r =>
        r.val < 2 ^ 2 ^ 6 ∧ towerOf 6 r = towerOf 6 a ^ 2 ^ power.val ⦄
    split
    · refine WP.spec_mono (bf64_square_spec v) fun r hr => ⟨hr ▸ towerMul_lt _ hv hv, ?_⟩
      rw [towerOf_mul hr, hve, ← pow_two, ← pow_mul, ← pow_succ, ← hep,
        show p1.val = 1 by simp [*]]
    · rw [ite_eq_left (by decide)]
      refine WP.spec_bind (frobenius_64_spec v p1 (by omega)) fun i1 hi1 => ?_
      refine WP.spec_mono (bf64_from_repr_spec i1) fun r hr => ?_
      have hlt : i1.val < 2 ^ 2 ^ 6 := hi1 ▸ frobNat_lt _ hv
      rw [Nat.mod_eq_of_lt hlt] at hr
      refine ⟨hr ▸ hlt, ?_⟩
      have e1 : towerOf 6 r = towerOf 6 v ^ 2 ^ p1.val := by
        simp only [towerOf]; rw [hr, hi1, fromNat_frobNat _ hv]
      rw [e1, hve, ← pow_mul, ← pow_add, hep]

theorem bf128_exp_power_of_2_spec (a : tower.BinaryField128) (n : Std.Usize) :
    tower.BinaryField128.Insts.P3_fieldFieldPrimeCharacteristicRing.exp_power_of_2 a n ⦃ r =>
      r.val < 2 ^ 2 ^ 7 ∧ towerOf 7 r = towerOf 7 a ^ 2 ^ n.val ⦄ := by
  have hA : a.val < 2 ^ 2 ^ 7 := by have := a.hBounds; simpa using this
  unfold tower.BinaryField128.Insts.P3_fieldFieldPrimeCharacteristicRing.exp_power_of_2
  simp only [tower.BinaryField128.BITS]
  step*
  have hmod : towerOf 7 a ^ 2 ^ n.val = towerOf 7 a ^ 2 ^ power.val := by
    rw [pow_two_pow_mod, power_post]; norm_num
  rw [hmod]
  refine WP.spec_bind (Pₘ := fun pv => pv.2.val < 2 ^ 2 ^ 7 ∧ pv.1.val < 2 ^ 6 ∧
    ∃ e, towerOf 7 pv.2 = towerOf 7 a ^ 2 ^ e ∧ e + pv.1.val = power.val) ?_ ?_
  · split
    · step*
      have hg1 : bf1.val < 2 ^ 2 ^ 6 := by scalar_tac
      have hhi : hi.val < 2 ^ 2 ^ 6 := by scalar_tac
      refine ⟨by rw [value1_post]; exact join_lt hg1 hhi, by scalar_tac, 2 ^ 6,
        towerOf_conj lo_post lo_post1 (by rw [towerOf_add bf1_post, towerOf_mul_Z bf_post]) hg1
          value1_post, ?_⟩
      rw [power2_post, i_post]
      omega
    · rw [WP.spec_ok]
      exact ⟨hA, by scalar_tac, 0, by simp, by simp⟩
  · rintro ⟨p1, v⟩ ⟨hv, hp1, e, hve, hep⟩
    dsimp only at hv hp1 hve hep
    show (if p1 = 1#usize then tower.BinaryField128.Insts.P3_fieldFieldPrimeCharacteristicRing.square v
      else if 128#usize ≥ 16#usize then do
        let i1 ← linear.frobenius_128 v p1
        tower.BinaryField128.from_repr i1
      else tower.BinaryField128.Insts.P3_fieldFieldPrimeCharacteristicRing.exp_power_of_2_loop
          { start := 0#usize, «end» := p1 } v) ⦃ r =>
        r.val < 2 ^ 2 ^ 7 ∧ towerOf 7 r = towerOf 7 a ^ 2 ^ power.val ⦄
    split
    · refine WP.spec_mono (bf128_square_spec v) fun r hr => ⟨hr ▸ towerMul_lt _ hv hv, ?_⟩
      rw [towerOf_mul hr, hve, ← pow_two, ← pow_mul, ← pow_succ, ← hep,
        show p1.val = 1 by simp [*]]
    · rw [ite_eq_left (by decide)]
      refine WP.spec_bind (frobenius_128_spec v p1 (by omega)) fun i1 hi1 => ?_
      refine WP.spec_mono (bf128_from_repr_spec i1) fun r hr => ?_
      have hlt : i1.val < 2 ^ 2 ^ 7 := hi1 ▸ frobNat_lt _ hv
      rw [Nat.mod_eq_of_lt hlt] at hr
      refine ⟨hr ▸ hlt, ?_⟩
      have e1 : towerOf 7 r = towerOf 7 v ^ 2 ^ p1.val := by
        simp only [towerOf]; rw [hr, hi1, fromNat_frobNat _ hv]
      rw [e1, hve, ← pow_mul, ← pow_add, hep]

end Plonky3Lean.Proofs.Binary
