module

public import Mathlib.Tactic.LinearCombination
public import Plonky3Lean.Lib.Array
public import Plonky3Lean.Proofs.Field.Goldilocks.Arith

@[expose] public section

/-!
# Goldilocks: multiplying and dividing by powers of two

The `POWERS_OF_TWO` table, `mul_2exp_u64` and `div_2exp_u64`, for every input and every `u64` exponent.

They rest on `2^96 = -1` and `2^192 = 1` in the field.
-/

open Aeneas Aeneas.Std CoreModels p3_goldilocks Plonky3Lean.Lib
open Plonky3Lean.Spec.Goldilocks

namespace Plonky3Lean.Proofs.P3Goldilocks


/-- `const_add` subtracts `p` once when the sum wraps. -/
theorem const_add.spec (a b : goldilocks.Goldilocks)
    (h : a.value.val + b.value.val < 2 ^ 64 + 18446744069414584321) :
    goldilocks.const_add a b ⦃ r => r.value.val =
      if 2 ^ 64 ≤ a.value.val + b.value.val then a.value.val + b.value.val - 18446744069414584321
      else a.value.val + b.value.val ⦄ := by
  unfold goldilocks.const_add
  rw [NEG_ORDER.eq]
  have ha := u64_lt a.value
  have hb := u64_lt b.value
  step*
  all_goals
    by_cases hs : 2 ^ 64 ≤ a.value.val + b.value.val <;>
      simp only [hs, decide_true, decide_false] at over_post <;> subst over_post <;>
      simp only [Bool.toNat_true, Bool.toNat_false] at i_post
  · simp only [i_post, U64.max_eq]; decide
  · simp only [i_post, U64.max_eq]; decide
  all_goals
    have hs1 : ¬ 2 ^ 64 ≤ sum.val + i2.val := by
      rw [sum_post, i2_post, i_post]; omega
    simp only [hs1, decide_false] at over1_post
    subst over1_post
    simp only [Bool.false_eq_true, ite_false, hs, ite_true]
    step*

/-- Entries below `i` are `2^j mod p`. -/
def Pow2Prefix (arr : Array goldilocks.Goldilocks 96#usize) (i : ℕ) : Prop :=
  ∀ j < i, ∃ x, arr.val[j]? = some x ∧ x.value.val = 2 ^ j % 18446744069414584321

/-- Setting entry `i` to `2^i mod p` extends the prefix. -/
theorem Pow2Prefix.set {arr : Array goldilocks.Goldilocks 96#usize} {i : Std.Usize}
    (h : Pow2Prefix arr i.val) (x : goldilocks.Goldilocks) (hi : i.val < 96)
    (hx : x.value.val = 2 ^ i.val % 18446744069414584321) :
    Pow2Prefix (arr.set i x) (i.val + 1) := by
  intro j hj
  have hlen : arr.val.length = 96 := arr.property
  simp only [Array.set_val_eq, List.getElem?_set]
  by_cases hji : i.val = j
  · subst hji; exact ⟨x, by simp [hlen, hi], hx⟩
  · rw [ite_eq_right hji]; exact h j (by omega)

/-- The first loop fills entries `1` to `63` with `1 << i`. -/
theorem POWERS_OF_TWO_loop0.spec (arr : Array goldilocks.Goldilocks 96#usize) (i : Std.Usize)
    (hi : 1 ≤ i.val) (hi64 : i.val ≤ 64) (h : Pow2Prefix arr i.val) :
    goldilocks.Goldilocks.POWERS_OF_TWO_loop0 arr i ⦃ r => r.2.val = 64 ∧ Pow2Prefix r.1 64 ⦄ := by
  unfold goldilocks.Goldilocks.POWERS_OF_TWO_loop0
  apply loop.spec_decr_nat (fun (x : _ × Std.Usize) => 64 - x.2.val)
    (fun x => 1 ≤ x.2.val ∧ x.2.val ≤ 64 ∧ Pow2Prefix x.1 x.2.val)
  · rintro ⟨a, k⟩ ⟨hk1, hk64, hk⟩
    unfold goldilocks.Goldilocks.POWERS_OF_TWO_loop0.body
    simp only at hk1 hk64 hk ⊢
    split
    · step*
      rename g.value = i1 => g_post
      have hk' : i2.val = k.val + 1 := i2_post
      refine ⟨by omega, by omega, ?_, by omega⟩
      rw [a_post, hk']
      refine hk.set g (by omega) ?_
      rw [g_post, i1_post, Nat.one_shiftLeft, show U64.size = 2 ^ 64 by simp [U64.size, U64.numBits],
        Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by norm_num) i1_post2),
        Nat.mod_eq_of_lt (lt_of_le_of_lt (Nat.pow_le_pow_right (by norm_num) (by omega : k.val ≤ 63))
          (by norm_num))]
    · rename_i hge
      simp only [WP.spec_ok]
      have hk' : k.val = 64 := by rw [UScalar.lt_equiv] at hge; simp at hge; omega
      exact ⟨hk', hk' ▸ hk⟩
  · exact ⟨hi, hi64, h⟩

/-- Doubling `2^(i-1) mod p` with `const_add`'s single correction gives `2^i mod p`. -/
theorem double_pow2 : ∀ k < 32,
    (if 2 ^ 64 ≤ 2 ^ (k + 63) % 18446744069414584321 + 2 ^ (k + 63) % 18446744069414584321 then
      2 ^ (k + 63) % 18446744069414584321 + 2 ^ (k + 63) % 18446744069414584321 - 18446744069414584321
    else 2 ^ (k + 63) % 18446744069414584321 + 2 ^ (k + 63) % 18446744069414584321) =
      2 ^ (k + 64) % 18446744069414584321 := by
  decide

/-- The second loop fills entries `64` to `95` by doubling. -/
theorem POWERS_OF_TWO_loop1.spec (arr : Array goldilocks.Goldilocks 96#usize) (i : Std.Usize)
    (var : goldilocks.Goldilocks) (hi : 64 ≤ i.val) (hi96 : i.val ≤ 96) (h : Pow2Prefix arr i.val)
    (hv : var.value.val = 2 ^ (i.val - 1) % 18446744069414584321) :
    goldilocks.Goldilocks.POWERS_OF_TWO_loop1 arr i var ⦃ r => Pow2Prefix r 96 ⦄ := by
  unfold goldilocks.Goldilocks.POWERS_OF_TWO_loop1
  apply loop.spec_decr_nat (fun (x : _ × Std.Usize × _) => 96 - x.2.1.val)
    (fun x => 64 ≤ x.2.1.val ∧ x.2.1.val ≤ 96 ∧ Pow2Prefix x.1 x.2.1.val ∧
      x.2.2.value.val = 2 ^ (x.2.1.val - 1) % 18446744069414584321)
  · rintro ⟨a, k, v⟩ ⟨hk1, hk96, hk, hkv⟩
    unfold goldilocks.Goldilocks.POWERS_OF_TWO_loop1.body
    simp only at hk1 hk96 hk hkv ⊢
    split
    · rename_i hlt
      have hk96' : k.val < 96 := by rw [UScalar.lt_equiv] at hlt; simpa using hlt
      have hvp : v.value.val < 18446744069414584321 := by rw [hkv]; exact Nat.mod_lt _ (by norm_num)
      step with const_add.spec
      step*
      have hk' : i1.val = k.val + 1 := i1_post
      have hd := double_pow2 (k.val - 64) (by omega)
      rw [show k.val - 64 + 63 = k.val - 1 by omega, show k.val - 64 + 64 = k.val by omega,
        ← hkv] at hd
      refine ⟨by omega, by omega, ?_, ?_, by omega⟩
      · rw [a_post, hk']
        exact hk.set var1 (by omega) (by rw [var1_post, hd])
      · rw [var1_post, hd, hk', Nat.add_sub_cancel]
    · rename_i hge
      simp only [WP.spec_ok]
      have hk' : k.val = 96 := by rw [UScalar.lt_equiv] at hge; simp at hge; omega
      exact hk' ▸ hk
  · exact ⟨hi, hi96, h, hv⟩

/-- `POWERS_OF_TWO[j] = 2^j mod p`, for every `j < 96`. -/
theorem POWERS_OF_TWO.spec : goldilocks.Goldilocks.POWERS_OF_TWO ⦃ r => Pow2Prefix r 96 ⦄ := by
  unfold goldilocks.Goldilocks.POWERS_OF_TWO
    goldilocks.Goldilocks.Insts.P3_fieldFieldPrimeCharacteristicRing.ONE
  step*
  obtain ⟨arr, harr, hall⟩ :=
    array_repeat_eq 96#usize goldilocks.Goldilocks.Insts.CoreCloneClone (fun _ => rfl) g
  rw [harr, bind_ok]
  have h1 : Pow2Prefix arr (1#usize).val := by
    intro j hj
    have : j = 0 := by simp at hj; omega
    subst this
    have hlen : arr.val.length = 96 := arr.property
    refine ⟨g, ?_, by rw [g_post]; rfl⟩
    rw [List.getElem?_eq_getElem (by omega), hall _ (List.getElem_mem _)]
  step with POWERS_OF_TWO_loop0.spec _ _ (by simp) (by simp) h1
  step*
  rename var.value = i1 => var_post
  apply POWERS_OF_TWO_loop1.spec _ _ _ (by omega) (by omega)
    (by rw [powers_of_two1_post]; exact powers_of_two1_post1)
  rw [var_post, i1_post, powers_of_two1_post]
  simp [U64.size, U64.numBits]

/-- A `u64` below `2^32` survives the cast to `usize`. -/
theorem cast_usize_val (x : Std.U64) (hx : x.val < 2 ^ 32) :
    (UScalar.cast .Usize x).val = x.val := by
  rw [UScalar.cast_val_eq, UScalarTy.Usize_numBits_eq]
  rcases System.Platform.numBits_eq with h | h <;> rw [h] <;> omega

/-- An entry of a table satisfying `Pow2Prefix`, read in the field. -/
theorem Pow2Prefix.index {arr : Array goldilocks.Goldilocks 96#usize} (h : Pow2Prefix arr 96)
    (i : Std.Usize) (hi : i.val < 96) :
    arr.index_usize i ⦃ x => (x.value.val : Goldilocks.Field) = 2 ^ i.val ⦄ := by
  obtain ⟨x, hx, hxv⟩ := h i.val hi
  unfold Array.index_usize
  rw [show arr[i]? = some x from hx]
  simp only [WP.spec_ok, hxv]
  rw [ZMod.natCast_mod]; push_cast; rfl

/-- `2^96 = -1` in the field. -/
theorem two_pow_96 : (2 : Goldilocks.Field) ^ 96 = -1 := by
  have h : ((2 ^ 96 : ℕ) : Goldilocks.Field) = ((18446744069414584320 : ℕ) : Goldilocks.Field) :=
    natCast_eq_of_mod (by norm_num)
  have h1 : ((18446744069414584320 : ℕ) : Goldilocks.Field) = -1 := by
    rw [eq_neg_iff_add_eq_zero]
    exact_mod_cast (ZMod.natCast_self _)
  rw [Nat.cast_pow, Nat.cast_ofNat] at h
  rw [h, h1]

/-- `2^192 = 1` in the field. -/
theorem two_pow_192 : (2 : Goldilocks.Field) ^ 192 = 1 := by
  rw [show 192 = 96 * 2 from rfl, pow_mul, two_pow_96]; norm_num

/-- `Mul`, read in the field. -/
theorem mul.field (a b : goldilocks.Goldilocks) :
    goldilocks.Goldilocks.Insts.CoreOpsArithMulGoldilocksGoldilocks.mul a b ⦃ r =>
      (r.value.val : Goldilocks.Field) = a.value.val * b.value.val ⦄ :=
  WP.spec_mono (mul.spec a b) (fun r hr => by rw [natCast_eq_of_mod hr]; push_cast; rfl)

/-- `Neg`, read in the field. -/
theorem neg.field (a : goldilocks.Goldilocks) :
    goldilocks.Goldilocks.Insts.CoreOpsArithNegGoldilocks.neg a ⦃ r =>
      (r.value.val : Goldilocks.Field) = -a.value.val ⦄ :=
  WP.spec_mono (neg.spec a) (fun r hr => by
    have := natCast_eq_of_mod (x := r.value.val + a.value.val) (y := 0) hr
    push_cast at this; exact eq_neg_of_add_eq_zero_left this)

/-- `Add`, read in the field. -/
theorem add.field (a b : goldilocks.Goldilocks) :
    goldilocks.Goldilocks.Insts.CoreOpsArithAddGoldilocksGoldilocks.add a b ⦃ r =>
      (r.value.val : Goldilocks.Field) = a.value.val + b.value.val ⦄ :=
  WP.spec_mono (add.spec a b) (fun r hr => by rw [natCast_eq_of_mod hr]; push_cast; rfl)

/-- `mul_2exp_u64` for an exponent below `192`, where it does not recurse. -/
theorem mul_2exp_u64.spec_lt (a : goldilocks.Goldilocks) (e : Std.U64) (he : e.val < 192) :
    goldilocks.Goldilocks.Insts.P3_fieldFieldPrimeCharacteristicRing.mul_2exp_u64 a e ⦃ r =>
      (r.value.val : Goldilocks.Field) = a.value.val * 2 ^ e.val ⦄ := by
  rw [goldilocks.Goldilocks.Insts.P3_fieldFieldPrimeCharacteristicRing.mul_2exp_u64.eq_def]
  obtain ⟨arr, harr, hP⟩ := WP.spec_imp_exists POWERS_OF_TWO.spec
  split
  · simp only [WP.spec_ok, show (0#64#uscalar : Std.U64).val = 0 from rfl, pow_zero, mul_one]
  · apply WP.spec_mono (add.field a a)
    intro r hr; rw [hr, show (1#64#uscalar : Std.U64).val = 1 from rfl]; ring
  · split
    · rename_i hlt
      rw [UScalar.lt_equiv] at hlt
      have hlt' : e.val < 96 := by simpa using hlt
      rw [harr]
      simp only [bind_ok, lift]
      have hc := cast_usize_val e (by omega)
      apply WP.spec_bind (Pow2Prefix.index hP _ (by rw [hc]; exact hlt'))
      intro g hg
      apply WP.spec_mono (mul.field a g)
      intro r hr; rw [hr, hg, hc]
    · rename_i hge
      rw [UScalar.lt_equiv] at hge
      have hge' : 96 ≤ e.val := by simp at hge; omega
      rw [ite_eq_left (by rw [UScalar.lt_equiv]; simpa using he)]
      apply WP.spec_bind (neg.field a)
      intro g hg
      rw [harr]
      simp only [bind_ok, lift]
      step
      have hc := cast_usize_val i (by omega)
      apply WP.spec_bind (Pow2Prefix.index hP _ (by rw [hc]; omega))
      intro g1 hg1
      apply WP.spec_mono (mul.field g g1)
      intro r hr
      rw [hr, hg, hg1, hc, i_post]
      have : e.val = 96 + (e.val - 96) := by omega
      conv_rhs => rw [this, pow_add, two_pow_96]
      ring

/-- `mul_2exp_u64(a, e)` is `a * 2^e`, for every `u64` exponent. -/
theorem mul_2exp_u64.spec (a : goldilocks.Goldilocks) (e : Std.U64) :
    goldilocks.Goldilocks.Insts.P3_fieldFieldPrimeCharacteristicRing.mul_2exp_u64 a e ⦃ r =>
      (r.value.val : Goldilocks.Field) = a.value.val * 2 ^ e.val ⦄ := by
  by_cases he : e.val < 192
  · exact mul_2exp_u64.spec_lt a e he
  rw [goldilocks.Goldilocks.Insts.P3_fieldFieldPrimeCharacteristicRing.mul_2exp_u64.eq_def]
  split
  · exact absurd (by decide) he
  · exact absurd (by decide) he
  · rw [ite_eq_right (by rw [UScalar.lt_equiv]; simp; omega), ite_eq_right (by rw [UScalar.lt_equiv]; simp; omega)]
    step
    apply WP.spec_mono (mul_2exp_u64.spec_lt a i (by rw [i_post]; omega))
    intro r hr
    rw [hr, i_post]
    conv_rhs => rw [← Nat.mod_add_div e.val 192, pow_add, pow_mul, two_pow_192, one_pow, mul_one]

/-- The literal `p` is zero in the field. -/
theorem p_eq_zero : (18446744069414584321 : Goldilocks.Field) = 0 := by
  have h : ((18446744069414584321 : ℕ) : Goldilocks.Field) = 0 := ZMod.natCast_self _
  exact_mod_cast h

/-- `2^64 = 2^32 - 1` in the field. -/
theorem two_pow_64 : (2 : Goldilocks.Field) ^ 64 = 2 ^ 32 - 1 := by
  have h : ((18446744069414584321 : ℕ) : Goldilocks.Field) = 0 := ZMod.natCast_self _
  have : (18446744069414584321 : Goldilocks.Field) = 2 ^ 64 - 2 ^ 32 + 1 := by norm_num
  push_cast at h
  rw [this] at h
  rw [← sub_eq_zero, ← h]; ring

/-- `halve`, read in the field. -/
theorem halve.field (a : goldilocks.Goldilocks) :
    goldilocks.Goldilocks.Insts.P3_fieldFieldPrimeCharacteristicRing.halve a ⦃ r =>
      (r.value.val : Goldilocks.Field) * 2 = a.value.val ⦄ :=
  WP.spec_mono (halve.spec a) (fun r hr => by
    have := natCast_eq_of_mod hr; push_cast at this; rw [← this]; ring)

/-- `div_2exp_u64(a, e)` is `a / 2^e`: its result times `2^e` is `a`, for every `u64` exponent. -/
theorem div_2exp_u64.spec (a : goldilocks.Goldilocks) (e : Std.U64) :
    goldilocks.Goldilocks.Insts.P3_fieldFieldPrimeCharacteristicRing.div_2exp_u64 a e ⦃ r =>
      (r.value.val : Goldilocks.Field) * 2 ^ e.val = a.value.val ⦄ := by
  unfold goldilocks.Goldilocks.Insts.P3_fieldFieldPrimeCharacteristicRing.div_2exp_u64
  step
  have he : (2 : Goldilocks.Field) ^ e.val = 2 ^ exp1.val := by
    rw [exp1_post, ← Nat.mod_add_div e.val 192, pow_add, pow_mul, two_pow_192, one_pow, mul_one,
      Nat.mod_add_div]
  rw [he]
  have he192 : exp1.val < 192 := by rw [exp1_post]; exact Nat.mod_lt _ (by norm_num)
  clear he exp1_post
  split
  · simp only [WP.spec_ok]
    rw [show (2 : Goldilocks.Field) ^ (↑(0#64#uscalar : UScalar UScalarTy.U64) : ℕ) = 1 from by decide]
    ring
  · apply WP.spec_mono (halve.field a)
    intro r hr; rw [← hr]; rfl
  · split
    · rename_i hrange
      obtain ⟨hr2, hr32⟩ := hrange
      rw [UScalar.le_equiv] at hr2 hr32
      simp only [show (2#u64).val = 2 from rfl, show (32#u64).val = 32 from rfl] at hr2 hr32
      rw [NEG_ORDER.eq]
      have ha := u64_lt a.value
      have hsz : U64.size = 2 ^ 64 := by simp [U64.size, U64.numBits]
      have hpe : 2 ^ exp1.val ≤ 2 ^ 32 := Nat.pow_le_pow_right (by norm_num) hr32
      have hpe2 : 4 ≤ 2 ^ exp1.val := by
        calc 4 = 2 ^ 2 := rfl
          _ ≤ 2 ^ exp1.val := Nat.pow_le_pow_right (by norm_num) hr2
      step
      have hiv : i.val = 2 ^ exp1.val := by
        rw [i_post, Nat.one_shiftLeft, hsz, Nat.mod_eq_of_lt (by omega)]
      clear i_post i_post1
      step
      have hi1 : i1.val = 2 ^ exp1.val - 1 := by rw [i1_post, hiv]
      clear i1_post i1_post1
      step
      have hlo : lo.val = a.value.val % 2 ^ exp1.val := by
        rw [lo_post, UScalar.val_and, hi1, Nat.and_two_pow_sub_one_eq_mod]
      have hlo' : lo.val < 2 ^ exp1.val := by rw [hlo]; exact Nat.mod_lt _ (by positivity)
      clear lo_post lo_post1
      step
      have hhi : hi.val = a.value.val / 2 ^ exp1.val := by
        rw [hi_post, Nat.shiftRight_eq_div_pow]
      have hhi' : hi.val < 2 ^ 62 := by
        rw [hhi, Nat.div_lt_iff_lt_mul (by positivity)]
        calc a.value.val < 2 ^ 64 := ha
          _ = 2 ^ 62 * 4 := by norm_num
          _ ≤ 2 ^ 62 * 2 ^ exp1.val := Nat.mul_le_mul_left _ hpe2
      clear hi_post hi_post1
      step
      step
      have hlo2 : lo.val * 2 ^ (32 - exp1.val) < 2 ^ 32 := by
        calc lo.val * 2 ^ (32 - exp1.val) < 2 ^ exp1.val * 2 ^ (32 - exp1.val) :=
              Nat.mul_lt_mul_of_pos_right hlo' (by positivity)
          _ = 2 ^ 32 := by rw [← pow_add, Nat.add_sub_cancel' hr32]
      have hi3 : i3.val = lo.val * 2 ^ (32 - exp1.val) := by
        rw [i3_post, i2_post, Nat.shiftLeft_eq, hsz, Nat.mod_eq_of_lt (by omega)]
      clear i3_post i3_post1
      have hX : 2 ^ exp1.val * 2 ^ (64 - exp1.val) = 2 ^ 64 := by
        rw [← pow_add, Nat.add_sub_cancel' (by omega)]
      have hY : 2 ^ exp1.val * 2 ^ (32 - exp1.val) = 2 ^ 32 := by
        rw [← pow_add, Nat.add_sub_cancel' hr32]
      have hXY : 2 ^ (32 - exp1.val) ≤ 2 ^ (64 - exp1.val) := Nat.pow_le_pow_right (by norm_num) (by omega)
      have hloX : lo.val * 2 ^ (64 - exp1.val) < 2 ^ 64 := by
        rw [← hX]; exact Nat.mul_lt_mul_of_pos_right hlo' (by positivity)
      step as ⟨aa, haa⟩
      have ha' : aa.val = hi.val + lo.val * 2 ^ (32 - exp1.val) := by rw [haa, hi3]
      clear haa
      step
      step
      have hb : b.val = lo.val * 2 ^ (64 - exp1.val) := by
        rw [b_post, i4_post, Nat.shiftLeft_eq, hsz, Nat.mod_eq_of_lt hloX]
      clear b_post b_post1
      -- The subtraction falls short by less than `p`.
      have hgap : b.val ≤ aa.val + 18446744069414584320 := by
        rw [hb, ha']
        have h1 : lo.val * 2 ^ (64 - exp1.val) ≤ (2 ^ exp1.val - 1) * 2 ^ (64 - exp1.val) :=
          Nat.mul_le_mul_right _ (by omega)
        have h2 : (2 ^ exp1.val - 1) * 2 ^ (64 - exp1.val) = 2 ^ 64 - 2 ^ (64 - exp1.val) := by
          rw [Nat.sub_mul, hX, one_mul]
        have hX32 : 2 ^ 32 ≤ 2 ^ (64 - exp1.val) := Nat.pow_le_pow_right (by norm_num) (by omega)
        omega
      step*
      · rw [show (4294967295#u64).val = 4294967295 from rfl, i6_post]
        split <;> simp [U64.max_eq]
      rename r.value = i8 => r_post
      have hi8 : (i8.val : Goldilocks.Field) = (aa.val : Goldilocks.Field) - (b.val : Goldilocks.Field) := by
        by_cases hbr : aa.val < b.val
        · simp only [hbr, decide_true] at borrow_post
          subst borrow_post
          simp only [ite_true] at i6_post
          have : i8.val = aa.val + 18446744069414584321 - b.val := by
            rw [i8_post, i7_post, i6_post, result_post]; omega
          rw [this, Nat.cast_sub (by omega)]
          push_cast
          rw [p_eq_zero]
          ring
        · simp only [hbr, decide_false] at borrow_post
          subst borrow_post
          simp only [Bool.false_eq_true, ite_false] at i6_post
          have : i8.val = aa.val - b.val := by
            rw [i8_post, i7_post, i6_post, result_post]; omega
          rw [this, Nat.cast_sub (by omega)]
      have hsplit : (a.value.val : Goldilocks.Field) =
          2 ^ exp1.val * (hi.val : Goldilocks.Field) + lo.val := by
        rw [hhi, hlo]
        have := congrArg (Nat.cast : ℕ → Goldilocks.Field) (Nat.div_add_mod a.value.val (2 ^ exp1.val))
        push_cast at this
        exact this.symm
      have hXF : (2 : Goldilocks.Field) ^ exp1.val * 2 ^ (64 - exp1.val) = 2 ^ 32 - 1 := by
        rw [← two_pow_64]
        have := congrArg (Nat.cast : ℕ → Goldilocks.Field) hX
        push_cast at this
        exact this
      have hYF : (2 : Goldilocks.Field) ^ exp1.val * 2 ^ (32 - exp1.val) = 2 ^ 32 := by
        have := congrArg (Nat.cast : ℕ → Goldilocks.Field) hY
        push_cast at this
        exact this
      rw [r_post, hi8, ha', hb, hsplit]
      push_cast
      linear_combination (lo.val : Goldilocks.Field) * hYF - (lo.val : Goldilocks.Field) * hXF
    · rename_i hrange
      step
      apply WP.spec_mono (mul_2exp_u64.spec a i)
      intro r hr
      rw [hr, mul_assoc, ← pow_add, i_post, Nat.sub_add_cancel i_post1, two_pow_192, mul_one]

end Plonky3Lean.Proofs.P3Goldilocks
