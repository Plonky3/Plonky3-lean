module

public import Plonky3Lean.Proofs.Field.Binary.TowerInverse
public import Plonky3Lean.Proofs.Field.Binary.Conjugate

@[expose] public section

/-!
# Powers `x^(2^n)` below `GF(2^16)`

`exp_power_of_2 x n` returns `x^(2^n)`. At level `k`, with `BITS = 2^k`:

- `x^(2^BITS) = x`, so it reduces `n` modulo `BITS`;
- `x^(2^(BITS/2))` is the conjugate `(lo + hi Z) + hi X` (`pow_card_eq_conjugate`), so for
  `n ≥ BITS/2` it conjugates and subtracts `BITS/2`;
- it squares the rest of the way.
-/

open Aeneas Aeneas.Std CoreModels
open p3_binary_field ConcreteBinaryTower ConcreteBinaryTower.Coordinates
open Plonky3Lean.Lib Plonky3Lean.Spec.BinaryField

namespace Plonky3Lean.Proofs.Binary

/-- `x^(2^(BITS m)) = x`. -/
theorem pow_two_pow_mul_card {k : ℕ} (x : ConcreteBTField k) : ∀ m : ℕ, x ^ 2 ^ (2 ^ k * m) = x
  | 0 => by simp
  | m + 1 => by
    rw [Nat.mul_succ, pow_add, pow_mul, pow_two_pow_mul_card x m, pow_card_level]

/-- `x^(2^n) = x^(2^(n mod BITS))`. -/
theorem pow_two_pow_mod {k : ℕ} (x : ConcreteBTField k) (n : ℕ) :
    x ^ 2 ^ n = x ^ 2 ^ (n % 2 ^ k) := by
  conv_lhs => rw [← Nat.div_add_mod n (2 ^ k), pow_add, pow_mul, pow_two_pow_mul_card]

/-- `join(lo + hi Z, hi)`, from the halves `split` returns, is `x^(2^(2^k))`. -/
theorem towerOf_conj {k : ℕ} {ty₁ ty₂ ty₃ ty₄ ty₅ : UScalarTy} {a : UScalar ty₁} {y : UScalar ty₂}
    {a0 : UScalar ty₃} {lo' : UScalar ty₄} {hi : UScalar ty₅}
    (ha0 : a0.val = (a.val &&& (2 ^ 2 ^ k - 1)) % 2 ^ 2 ^ k)
    (hhi : hi.val = (a.val >>> 2 ^ k) % 2 ^ 2 ^ k)
    (hlo' : towerOf k lo' = towerOf k a0 + towerOf k hi * Z k) (hlo'lt : lo'.val < 2 ^ 2 ^ k)
    (hy : y.val = hi.val <<< 2 ^ k ||| lo'.val) :
    towerOf (k + 1) y = towerOf (k + 1) a ^ 2 ^ 2 ^ k := by
  have hhilt : hi.val < 2 ^ 2 ^ k := hhi ▸ Nat.mod_lt _ (by positivity)
  rw [towerOf_join hlo'lt hhilt hy, pow_card_eq_conjugate, conjugate_eq_joinSucc, hlo',
    show towerOf k a0 = low k (towerOf (k + 1) a) by rw [low_towerOf, towerOf, ha0],
    show towerOf k hi = high k (towerOf (k + 1) a) by rw [high_towerOf, towerOf, hhi]]

/-! ## `GF(2^2)` -/

theorem bf2_exp_loop_spec (it : CoreModels.core.ops.range.Range Std.Usize) (v : tower.BinaryField2)
    (hs : it.start.val ≤ it.«end».val) (hv : v.val < 2 ^ 2 ^ 1) :
    tower.BinaryField2.Insts.P3_fieldFieldPrimeCharacteristicRing.exp_power_of_2_loop it v ⦃ r =>
      r.val < 2 ^ 2 ^ 1 ∧ towerOf 1 r = towerOf 1 v ^ 2 ^ (it.«end».val - it.start.val) ⦄ := by
  unfold tower.BinaryField2.Insts.P3_fieldFieldPrimeCharacteristicRing.exp_power_of_2_loop
  refine loop.spec_decr_nat (fun p => p.1.«end».val - p.1.start.val)
    (fun p => p.1.«end» = it.«end» ∧ it.start.val ≤ p.1.start.val ∧
      p.1.start.val ≤ it.«end».val ∧ p.2.val < 2 ^ 2 ^ 1 ∧
      towerOf 1 p.2 = towerOf 1 v ^ 2 ^ (p.1.start.val - it.start.val)) _ _ _ ?_
    ⟨rfl, le_rfl, hs, hv, by simp⟩
  rintro ⟨⟨s, e⟩, w⟩ ⟨he, h1, h2, hw, hpw⟩
  dsimp only at he h1 h2 hpw
  subst he
  unfold tower.BinaryField2.Insts.P3_fieldFieldPrimeCharacteristicRing.exp_power_of_2_loop.body
  by_cases hlt : s.val < it.«end».val
  · obtain ⟨s', hn, hs'⟩ := range_next_lt s it.«end» hlt
    simp only [core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next, hn,
      Aeneas.Std.bind_ok]
    refine WP.spec_bind (bf2_square_spec w) fun w' hw' => ?_
    rw [WP.spec_ok]
    dsimp only
    refine ⟨⟨rfl, by omega, by omega, by rw [hw']; exact towerMul_lt _ hw hw, ?_⟩, by omega⟩
    rw [towerOf_mul hw', hpw, hs', ← pow_two, ← pow_mul, ← pow_succ, Nat.sub_add_comm h1]
  · simp only [core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next,
      range_next_ge s it.«end» (by omega), Aeneas.Std.bind_ok]
    dsimp only at hw
    show WP.spec (RustM.ok (ControlFlow.done w)) _
    rw [WP.spec_ok]
    refine ⟨hw, ?_⟩
    rw [hpw, show s.val = it.«end».val by omega]

theorem bf2_exp_power_of_2_spec (a : tower.BinaryField2) (hA : a.val < 2 ^ 2 ^ 1)
    (n : Std.Usize) :
    tower.BinaryField2.Insts.P3_fieldFieldPrimeCharacteristicRing.exp_power_of_2 a n ⦃ r =>
      r.val < 2 ^ 2 ^ 1 ∧ towerOf 1 r = towerOf 1 a ^ 2 ^ n.val ⦄ := by
  unfold tower.BinaryField2.Insts.P3_fieldFieldPrimeCharacteristicRing.exp_power_of_2
  simp only [tower.BinaryField2.BITS]
  step*
  have hmod : towerOf 1 a ^ 2 ^ n.val = towerOf 1 a ^ 2 ^ power.val := by
    rw [pow_two_pow_mod, power_post, pow_one]
  rw [hmod]
  refine WP.spec_bind (Pₘ := fun pv => pv.2.val < 2 ^ 2 ^ 1 ∧
    ∃ e, towerOf 1 pv.2 = towerOf 1 a ^ 2 ^ e ∧ e + pv.1.val = power.val) ?_ ?_
  · split
    · step*
      case h0 => tower_bound
      have hg1 : g1.val < 2 ^ 2 ^ 0 := by tower_bound
      have hhi : hi.val < 2 ^ 2 ^ 0 := by tower_bound
      refine ⟨by rw [value1_post]; exact join_lt hg1 hhi, 2 ^ 0,
        towerOf_conj lo_post lo_post1 (by rw [towerOf_add g1_post, towerOf_mul_Z g_post]) hg1
          value1_post, ?_⟩
      rw [power2_post, i_post]
      omega
    · rw [WP.spec_ok]
      exact ⟨hA, 0, by simp, by simp⟩
  · rintro ⟨p1, v⟩ ⟨hv, e, hve, hep⟩
    dsimp only at hv hve hep
    split
    · exact absurd ‹2#usize ≥ 16#usize› (by decide)
    show (if p1 = 1#usize then
        tower.BinaryField2.Insts.P3_fieldFieldPrimeCharacteristicRing.square v
      else tower.BinaryField2.Insts.P3_fieldFieldPrimeCharacteristicRing.exp_power_of_2_loop
        { start := 0#usize, «end» := p1 } v) ⦃ r =>
          r.val < 2 ^ 2 ^ 1 ∧ towerOf 1 r = towerOf 1 a ^ 2 ^ power.val ⦄
    split
    · refine WP.spec_mono (bf2_square_spec v) fun r hr => ⟨hr ▸ towerMul_lt _ hv hv, ?_⟩
      rw [towerOf_mul hr, hve, ← pow_two, ← pow_mul, ← pow_succ, ← hep,
        show p1.val = 1 by simp [*]]
    · refine WP.spec_mono (bf2_exp_loop_spec _ v (by simp) hv) fun r ⟨hr, hr'⟩ => ⟨hr, ?_⟩
      rw [hr', hve, ← pow_mul, ← pow_add]
      simp only [show (0#usize : Std.Usize).val = 0 from rfl, Nat.sub_zero, hep]

/-! ## `GF(2^4)` -/

@[step]
theorem bf4_mul_alpha_spec (x : tower.BinaryField4) :
    tower.BinaryField4.mul_alpha x ⦃ y => y.val = towerMul (1 + 1) x.val (zNat (1 + 1)) ⦄ := by
  unfold tower.BinaryField4.mul_alpha; exact bf4_raw_mul_alpha_spec x

theorem bf4_exp_loop_spec (it : CoreModels.core.ops.range.Range Std.Usize) (v : tower.BinaryField4)
    (hs : it.start.val ≤ it.«end».val) (hv : v.val < 2 ^ 2 ^ 2) :
    tower.BinaryField4.Insts.P3_fieldFieldPrimeCharacteristicRing.exp_power_of_2_loop it v ⦃ r =>
      r.val < 2 ^ 2 ^ 2 ∧ towerOf 2 r = towerOf 2 v ^ 2 ^ (it.«end».val - it.start.val) ⦄ := by
  unfold tower.BinaryField4.Insts.P3_fieldFieldPrimeCharacteristicRing.exp_power_of_2_loop
  refine loop.spec_decr_nat (fun p => p.1.«end».val - p.1.start.val)
    (fun p => p.1.«end» = it.«end» ∧ it.start.val ≤ p.1.start.val ∧
      p.1.start.val ≤ it.«end».val ∧ p.2.val < 2 ^ 2 ^ 2 ∧
      towerOf 2 p.2 = towerOf 2 v ^ 2 ^ (p.1.start.val - it.start.val)) _ _ _ ?_
    ⟨rfl, le_rfl, hs, hv, by simp⟩
  rintro ⟨⟨s, e⟩, w⟩ ⟨he, h1, h2, hw, hpw⟩
  dsimp only at he h1 h2 hpw
  subst he
  unfold tower.BinaryField4.Insts.P3_fieldFieldPrimeCharacteristicRing.exp_power_of_2_loop.body
  by_cases hlt : s.val < it.«end».val
  · obtain ⟨s', hn, hs'⟩ := range_next_lt s it.«end» hlt
    simp only [core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next, hn,
      Aeneas.Std.bind_ok]
    refine WP.spec_bind (bf4_square_spec w) fun w' hw' => ?_
    rw [WP.spec_ok]
    dsimp only
    refine ⟨⟨rfl, by omega, by omega, by rw [hw']; exact towerMul_lt _ hw hw, ?_⟩, by omega⟩
    rw [towerOf_mul hw', hpw, hs', ← pow_two, ← pow_mul, ← pow_succ, Nat.sub_add_comm h1]
  · simp only [core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next,
      range_next_ge s it.«end» (by omega), Aeneas.Std.bind_ok]
    dsimp only at hw
    show WP.spec (RustM.ok (ControlFlow.done w)) _
    rw [WP.spec_ok]
    refine ⟨hw, ?_⟩
    rw [hpw, show s.val = it.«end».val by omega]

theorem bf4_exp_power_of_2_spec (a : tower.BinaryField4) (hA : a.val < 2 ^ 2 ^ 2)
    (n : Std.Usize) :
    tower.BinaryField4.Insts.P3_fieldFieldPrimeCharacteristicRing.exp_power_of_2 a n ⦃ r =>
      r.val < 2 ^ 2 ^ 2 ∧ towerOf 2 r = towerOf 2 a ^ 2 ^ n.val ⦄ := by
  unfold tower.BinaryField4.Insts.P3_fieldFieldPrimeCharacteristicRing.exp_power_of_2
  simp only [tower.BinaryField4.BITS]
  step*
  have hmod : towerOf 2 a ^ 2 ^ n.val = towerOf 2 a ^ 2 ^ power.val := by
    rw [pow_two_pow_mod, power_post]; norm_num
  rw [hmod]
  refine WP.spec_bind (Pₘ := fun pv => pv.2.val < 2 ^ 2 ^ 2 ∧
    ∃ e, towerOf 2 pv.2 = towerOf 2 a ^ 2 ^ e ∧ e + pv.1.val = power.val) ?_ ?_
  · split
    · step*
      case h0 => tower_bound
      have hg1 : bf1.val < 2 ^ 2 ^ 1 := by tower_bound
      have hhi : hi.val < 2 ^ 2 ^ 1 := by tower_bound
      refine ⟨by rw [value1_post]; exact join_lt hg1 hhi, 2 ^ 1,
        towerOf_conj lo_post lo_post1 (by rw [towerOf_add bf1_post, towerOf_mul_Z bf_post]) hg1
          value1_post, ?_⟩
      rw [power2_post, i_post]
      omega
    · rw [WP.spec_ok]
      exact ⟨hA, 0, by simp, by simp⟩
  · rintro ⟨p1, v⟩ ⟨hv, e, hve, hep⟩
    dsimp only at hv hve hep
    split
    · exact absurd ‹4#usize ≥ 16#usize› (by decide)
    show (if p1 = 1#usize then
        tower.BinaryField4.Insts.P3_fieldFieldPrimeCharacteristicRing.square v
      else tower.BinaryField4.Insts.P3_fieldFieldPrimeCharacteristicRing.exp_power_of_2_loop
        { start := 0#usize, «end» := p1 } v) ⦃ r =>
          r.val < 2 ^ 2 ^ 2 ∧ towerOf 2 r = towerOf 2 a ^ 2 ^ power.val ⦄
    split
    · refine WP.spec_mono (bf4_square_spec v) fun r hr => ⟨hr ▸ towerMul_lt _ hv hv, ?_⟩
      rw [towerOf_mul hr, hve, ← pow_two, ← pow_mul, ← pow_succ, ← hep,
        show p1.val = 1 by simp [*]]
    · refine WP.spec_mono (bf4_exp_loop_spec _ v (by simp) hv) fun r ⟨hr, hr'⟩ => ⟨hr, ?_⟩
      rw [hr', hve, ← pow_mul, ← pow_add]
      simp only [show (0#usize : Std.Usize).val = 0 from rfl, Nat.sub_zero, hep]

/-! ## `GF(2^8)` -/

theorem bf8_exp_loop_spec (it : CoreModels.core.ops.range.Range Std.Usize) (v : tower.BinaryField8)
    (hs : it.start.val ≤ it.«end».val) (hv : v.val < 2 ^ 2 ^ 3) :
    tower.BinaryField8.Insts.P3_fieldFieldPrimeCharacteristicRing.exp_power_of_2_loop it v ⦃ r =>
      r.val < 2 ^ 2 ^ 3 ∧ towerOf 3 r = towerOf 3 v ^ 2 ^ (it.«end».val - it.start.val) ⦄ := by
  unfold tower.BinaryField8.Insts.P3_fieldFieldPrimeCharacteristicRing.exp_power_of_2_loop
  refine loop.spec_decr_nat (fun p => p.1.«end».val - p.1.start.val)
    (fun p => p.1.«end» = it.«end» ∧ it.start.val ≤ p.1.start.val ∧
      p.1.start.val ≤ it.«end».val ∧ p.2.val < 2 ^ 2 ^ 3 ∧
      towerOf 3 p.2 = towerOf 3 v ^ 2 ^ (p.1.start.val - it.start.val)) _ _ _ ?_
    ⟨rfl, le_rfl, hs, hv, by simp⟩
  rintro ⟨⟨s, e⟩, w⟩ ⟨he, h1, h2, hw, hpw⟩
  dsimp only at he h1 h2 hpw
  subst he
  unfold tower.BinaryField8.Insts.P3_fieldFieldPrimeCharacteristicRing.exp_power_of_2_loop.body
  by_cases hlt : s.val < it.«end».val
  · obtain ⟨s', hn, hs'⟩ := range_next_lt s it.«end» hlt
    simp only [core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next, hn,
      Aeneas.Std.bind_ok]
    refine WP.spec_bind (bf8_square_spec w) fun w' hw' => ?_
    rw [WP.spec_ok]
    dsimp only
    refine ⟨⟨rfl, by omega, by omega, by rw [hw']; exact towerMul_lt _ hw hw, ?_⟩, by omega⟩
    rw [towerOf_mul hw', hpw, hs', ← pow_two, ← pow_mul, ← pow_succ, Nat.sub_add_comm h1]
  · simp only [core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next,
      range_next_ge s it.«end» (by omega), Aeneas.Std.bind_ok]
    dsimp only at hw
    show WP.spec (RustM.ok (ControlFlow.done w)) _
    rw [WP.spec_ok]
    refine ⟨hw, ?_⟩
    rw [hpw, show s.val = it.«end».val by omega]

theorem bf8_exp_power_of_2_spec (a : tower.BinaryField8) (n : Std.Usize) :
    tower.BinaryField8.Insts.P3_fieldFieldPrimeCharacteristicRing.exp_power_of_2 a n ⦃ r =>
      r.val < 2 ^ 2 ^ 3 ∧ towerOf 3 r = towerOf 3 a ^ 2 ^ n.val ⦄ := by
  have hA : a.val < 2 ^ 2 ^ 3 := by have := a.hBounds; simpa using this
  unfold tower.BinaryField8.Insts.P3_fieldFieldPrimeCharacteristicRing.exp_power_of_2
  simp only [tower.BinaryField8.BITS]
  step*
  have hmod : towerOf 3 a ^ 2 ^ n.val = towerOf 3 a ^ 2 ^ power.val := by
    rw [pow_two_pow_mod, power_post]; norm_num
  rw [hmod]
  refine WP.spec_bind (Pₘ := fun pv => pv.2.val < 2 ^ 2 ^ 3 ∧
    ∃ e, towerOf 3 pv.2 = towerOf 3 a ^ 2 ^ e ∧ e + pv.1.val = power.val) ?_ ?_
  · split
    · step*
      case h0 => tower_bound
      have hg1 : bf1.val < 2 ^ 2 ^ 2 := by tower_bound
      have hhi : hi.val < 2 ^ 2 ^ 2 := by tower_bound
      refine ⟨by rw [value1_post]; exact join_lt hg1 hhi, 2 ^ 2,
        towerOf_conj lo_post lo_post1 (by rw [towerOf_add bf1_post, towerOf_mul_Z bf_post]) hg1
          value1_post, ?_⟩
      rw [power2_post, i_post]
      omega
    · rw [WP.spec_ok]
      exact ⟨hA, 0, by simp, by simp⟩
  · rintro ⟨p1, v⟩ ⟨hv, e, hve, hep⟩
    dsimp only at hv hve hep
    split
    · exact absurd ‹8#usize ≥ 16#usize› (by decide)
    show (if p1 = 1#usize then
        tower.BinaryField8.Insts.P3_fieldFieldPrimeCharacteristicRing.square v
      else tower.BinaryField8.Insts.P3_fieldFieldPrimeCharacteristicRing.exp_power_of_2_loop
        { start := 0#usize, «end» := p1 } v) ⦃ r =>
          r.val < 2 ^ 2 ^ 3 ∧ towerOf 3 r = towerOf 3 a ^ 2 ^ power.val ⦄
    split
    · refine WP.spec_mono (bf8_square_spec v) fun r hr => ⟨hr ▸ towerMul_lt _ hv hv, ?_⟩
      rw [towerOf_mul hr, hve, ← pow_two, ← pow_mul, ← pow_succ, ← hep,
        show p1.val = 1 by simp [*]]
    · refine WP.spec_mono (bf8_exp_loop_spec _ v (by simp) hv) fun r ⟨hr, hr'⟩ => ⟨hr, ?_⟩
      rw [hr', hve, ← pow_mul, ← pow_add]
      simp only [show (0#usize : Std.Usize).val = 0 from rfl, Nat.sub_zero, hep]

end Plonky3Lean.Proofs.Binary
