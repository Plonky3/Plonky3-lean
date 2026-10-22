module

public import Plonky3Lean.Proofs.Field.Goldilocks.Constants

@[expose] public section

/-!
# Goldilocks: sums and dot products

`Sum::sum`, `sum_array` and `dot_product`, which delay reduction by accumulating in `u128`.

`dot_product` is proved for `N <= 2^31`, the bound its `const` check intends.

The check casts `N` to `u32`, so it also passes for some `N >= 2^32`.
-/

open Aeneas Aeneas.Std CoreModels p3_goldilocks Plonky3Lean.Lib
open Plonky3Lean.Spec.Goldilocks

namespace Plonky3Lean.Proofs.P3Goldilocks


/-- The fold of `Sum::sum` from any accumulator whose total stays below `2^128`. -/
theorem sum_fold.spec (xs : List goldilocks.Goldilocks) (acc : Std.U128)
    (h : acc.val + (xs.map (fun x => x.value.val)).sum < 2 ^ 128) :
    xs.foldlM (fun acc x => acc + UScalar.cast .U128 x.value) acc ⦃ r =>
      r.val = acc.val + (xs.map (fun x => x.value.val)).sum ⦄ := by
  induction xs generalizing acc with
  | nil => exact (WP.spec_ok _).mpr (by simp)
  | cons x xs ih =>
    simp only [List.foldlM_cons, List.map_cons, List.sum_cons] at h ⊢
    have hx := cast_u64_u128_val x.value
    step*

/-- `Sum::sum` never fails while the `u128` total fits, and returns the field sum. -/
theorem sum.spec (xs : List goldilocks.Goldilocks)
    (h : (xs.map (fun x => x.value.val)).sum < 2 ^ 128) :
    goldilocks.Goldilocks.Insts.CoreIterTraitsAccumSumGoldilocks.sum xs ⦃ r =>
      toField r = (xs.map toField).sum ⦄ := by
  unfold goldilocks.Goldilocks.Insts.CoreIterTraitsAccumSumGoldilocks.sum
  apply WP.spec_bind (sum_fold.spec xs 0#u128 (by simpa using h))
  intro s hs
  apply WP.spec_mono (reduce128.spec s)
  intro r hr
  unfold toField
  rw [natCast_eq_of_mod hr, hs]
  simp only [show (0#u128).val = 0 from rfl, zero_add]
  rw [Nat.cast_list_sum, List.map_map]
  rfl

/-- Fewer than `2^64` items always fit: each is below `2^64`. -/
theorem sum_lt_of_length (xs : List goldilocks.Goldilocks) (h : xs.length < 2 ^ 64) :
    (xs.map (fun x => x.value.val)).sum < 2 ^ 128 := by
  have : (xs.map (fun x => x.value.val)).sum ≤ xs.length * (2 ^ 64 - 1) := by
    have := List.sum_le_length_nsmul (xs.map (fun x => x.value.val)) (2 ^ 64 - 1)
      (fun y hy => by
        obtain ⟨x, -, rfl⟩ := List.mem_map.mp hy
        have := u64_lt x.value; omega)
    simpa using this
  calc _ ≤ xs.length * (2 ^ 64 - 1) := this
    _ < 2 ^ 128 := by
      calc xs.length * (2 ^ 64 - 1) ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1) := Nat.mul_le_mul_right _ (by omega)
        _ < 2 ^ 128 := by norm_num

/-- A slice has fewer than `2^64` items. -/
theorem slice_len_lt (s : Slice goldilocks.Goldilocks) : s.val.length < 2 ^ 64 := by
  have := Slice.length_ineq s
  have h2 : Usize.max < 2 ^ 64 := by
    rw [Usize.max]; rcases System.Platform.numBits_eq with h | h <;> simp [Usize.numBits, h]
  omega

/-- `sum_array::<N>` returns the field sum of its `N` inputs, and panics if `N` is not their number. -/
theorem sum_array.spec (N : Std.Usize) (input : Slice goldilocks.Goldilocks)
    (hN : N.val = input.val.length) :
    goldilocks.Goldilocks.Insts.P3_fieldFieldPrimeCharacteristicRing.sum_array N input ⦃ r =>
      toField r = (input.val.map toField).sum ⦄ := by
  unfold goldilocks.Goldilocks.Insts.P3_fieldFieldPrimeCharacteristicRing.sum_array
  have hlen : N.val = input.length := hN
  simp only [massert, hlen, ite_true, bind_ok]
  have hidx : ∀ (i : Std.Usize) (x : goldilocks.Goldilocks), input.val[i.val]? = some x →
      input.index_usize i = .ok x := by
    intro i x h; unfold Slice.index_usize; rw [show input[i]? = some x from h]
  split_ifs with h0 h1 h2 h3
  · have : input.val = [] := List.eq_nil_of_length_eq_zero (by rw [← hN, h0]; rfl)
    unfold goldilocks.Goldilocks.Insts.P3_fieldFieldPrimeCharacteristicRing.ZERO
    step*
    rw [this]; unfold toField; rw [r_post]; rfl
  · obtain ⟨x, hx⟩ := List.length_eq_one_iff.mp (by rw [← hN, h1]; rfl : input.val.length = 1)
    rw [hidx 0#usize x (by rw [hx]; rfl)]
    simp [hx]
  · obtain ⟨x0, x1, hx⟩ := List.length_eq_two.mp (by rw [← hN, h2]; rfl : input.val.length = 2)
    rw [hidx 0#usize x0 (by rw [hx]; rfl), hidx 1#usize x1 (by rw [hx]; rfl)]
    simp only [bind_ok]
    apply WP.spec_mono (add.field x0 x1)
    intro r hr; unfold toField; rw [hr, hx]; simp
  · obtain ⟨x0, x1, x2, hx⟩ := List.length_eq_three.mp (by rw [← hN, h3]; rfl : input.val.length = 3)
    rw [hidx 0#usize x0 (by rw [hx]; rfl), hidx 1#usize x1 (by rw [hx]; rfl)]
    simp only [bind_ok]
    apply WP.spec_bind (add.field x0 x1)
    intro s hs
    rw [hidx 2#usize x2 (by rw [hx]; rfl)]
    simp only [bind_ok]
    apply WP.spec_mono (add.field s x2)
    intro r hr; unfold toField; rw [hr, hs, hx]; simp; ring
  · exact sum.spec _ (sum_lt_of_length _ (slice_len_lt input))

/-- The product of two stored values. -/
def prodVal (xy : goldilocks.Goldilocks × goldilocks.Goldilocks) : ℕ := xy.1.value.val * xy.2.value.val

/-- A product of two `u64` is at most `(2^64 - 1)^2`. -/
theorem prodVal_lt (xy : goldilocks.Goldilocks × goldilocks.Goldilocks) :
    prodVal xy ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1) :=
  Nat.mul_le_mul (by have := u64_lt xy.1.value; omega) (by have := u64_lt xy.2.value; omega)

/-- Its top 32 bits are at most `2^32 - 1`. -/
theorem prodVal_hi (xy : goldilocks.Goldilocks × goldilocks.Goldilocks) :
    prodVal xy / 2 ^ 96 ≤ 2 ^ 32 - 1 := by
  have := prodVal_lt xy
  omega

/-- One step of the fold of `dot_product`. -/
theorem fold_step.spec (lo : Std.U128) (hi : Std.U64) (xy : goldilocks.Goldilocks × goldilocks.Goldilocks)
    (h : hi.val + (2 ^ 32 - 1) < 2 ^ 64) :
    goldilocks.PrimeCharacteristicRingGoldilocks.dot_product.fold_step (lo, hi) xy ⦃ r =>
      r.1.val = (lo.val + prodVal xy) % 2 ^ 128 ∧ r.2.val = hi.val + prodVal xy / 2 ^ 96 ⦄ := by
  unfold goldilocks.PrimeCharacteristicRingGoldilocks.dot_product.fold_step
  have hp := prodVal_hi xy
  have hpl := prodVal_lt xy
  step as ⟨val, hval⟩
  step as ⟨i, hi1, hi2, hi3⟩
  have hiv : i.val = prodVal xy / 2 ^ 96 := by
    rw [hi1, hval, Nat.shiftRight_eq_div_pow]; rfl
  simp only [lift, bind_ok]
  have hc : (UScalar.cast .U64 i).val = prodVal xy / 2 ^ 96 := by
    rw [cast_u128_u64_val, hiv, Nat.mod_eq_of_lt (by omega)]
  step*
  rw [lo_post, hi_post, hval, hc]
  exact ⟨rfl, rfl⟩

/-- The fold of `dot_product` keeps the wrapped total and the sum of the top 32 bits. -/
theorem dot_fold.spec (L : List (goldilocks.Goldilocks × goldilocks.Goldilocks)) (lo : Std.U128) (hi : Std.U64)
    (h : hi.val + L.length * (2 ^ 32 - 1) < 2 ^ 64) :
    L.foldlM goldilocks.PrimeCharacteristicRingGoldilocks.dot_product.fold_step (lo, hi) ⦃ r =>
      r.1.val = (lo.val + (L.map prodVal).sum) % 2 ^ 128 ∧
        r.2.val = hi.val + (L.map (fun xy => prodVal xy / 2 ^ 96)).sum ⦄ := by
  induction L generalizing lo hi with
  | nil =>
    exact (WP.spec_ok _).mpr ⟨by simp [Nat.mod_eq_of_lt (by have := lo.hBounds; simpa using this)], by simp⟩
  | cons xy L ih =>
    simp only [List.foldlM_cons, List.map_cons, List.sum_cons, List.length_cons] at h ⊢
    apply WP.spec_bind (fold_step.spec lo hi xy (by nlinarith))
    rintro ⟨lo1, hi1⟩ ⟨hl, hh⟩
    have hp := prodVal_hi xy
    apply WP.spec_mono (ih lo1 hi1 (by simp only at hh; rw [hh]; nlinarith))
    rintro r ⟨h1, h2⟩
    simp only at hl hh
    refine ⟨?_, ?_⟩
    · rw [h1, hl, Nat.add_mod, Nat.mod_mod, ← Nat.add_mod, Nat.add_assoc]
    · rw [h2, hh, Nat.add_assoc]

/-- The low 96 bits of the products sum without the top bits. -/
theorem sum_split (L : List (goldilocks.Goldilocks × goldilocks.Goldilocks)) :
    (L.map prodVal).sum = (L.map (fun xy => prodVal xy % 2 ^ 96)).sum +
      2 ^ 96 * (L.map (fun xy => prodVal xy / 2 ^ 96)).sum := by
  induction L with
  | nil => simp
  | cons xy L ih =>
    simp only [List.map_cons, List.sum_cons, ih]
    have := Nat.mod_add_div (prodVal xy) (2 ^ 96)
    ring_nf; omega

/-- The low parts sum to at most `n (2^96 - 1)`. -/
theorem sum_low_lt (L : List (goldilocks.Goldilocks × goldilocks.Goldilocks)) :
    (L.map (fun xy => prodVal xy % 2 ^ 96)).sum ≤ L.length * (2 ^ 96 - 1) := by
  have := List.sum_le_length_nsmul (L.map (fun xy => prodVal xy % 2 ^ 96)) (2 ^ 96 - 1)
    (fun y hy => by
      obtain ⟨x, -, rfl⟩ := List.mem_map.mp hy
      have := Nat.mod_lt (prodVal x) (show 0 < 2 ^ 96 by norm_num); omega)
  simpa using this

/-- The top parts sum to at most `n (2^32 - 1)`. -/
theorem sum_high_le (L : List (goldilocks.Goldilocks × goldilocks.Goldilocks)) :
    (L.map (fun xy => prodVal xy / 2 ^ 96)).sum ≤ L.length * (2 ^ 32 - 1) := by
  have := List.sum_le_length_nsmul (L.map (fun xy => prodVal xy / 2 ^ 96)) (2 ^ 32 - 1)
    (fun y hy => by
      obtain ⟨x, -, rfl⟩ := List.mem_map.mp hy
      exact prodVal_hi x)
  simpa using this

/-- `OFFSET = p (2^64 + 2^32 - 1)`, a multiple of `p` above every product of two `u64`. -/
theorem OFFSET.spec :
    goldilocks.PrimeCharacteristicRingGoldilocks.dot_product.OFFSET ⦃ r =>
      r.val = 18446744069414584321 * (2 ^ 64 + 2 ^ 32 - 1) ⦄ := by
  unfold goldilocks.PrimeCharacteristicRingGoldilocks.dot_product.OFFSET goldilocks.P
  step*

/-- The field sum of the pairwise products of two coefficient lists. -/
def dotField (L : List (goldilocks.Goldilocks × goldilocks.Goldilocks)) : Goldilocks.Field :=
  (L.map (fun xy => toField xy.1 * toField xy.2)).sum

/-- The field dot product is the cast of the natural one. -/
theorem dotField_eq (L : List (goldilocks.Goldilocks × goldilocks.Goldilocks)) :
    dotField L = (((L.map prodVal).sum : ℕ) : Goldilocks.Field) := by
  induction L with
  | nil => simp [dotField]
  | cons xy L ih =>
    simp only [dotField, List.map_cons, List.sum_cons] at ih ⊢
    rw [ih, Nat.cast_add]
    congr 1
    unfold toField prodVal; push_cast; rfl

/-- `dot_product::<N>` returns the field dot product, for `N <= 2^31`. -/
theorem dot_product.spec {N : Std.Usize} (lhs rhs : Array goldilocks.Goldilocks N)
    (hN : N.val ≤ 2 ^ 31) :
    goldilocks.Goldilocks.Insts.P3_fieldFieldPrimeCharacteristicRing.dot_product lhs rhs ⦃ r =>
      toField r = dotField (List.zip lhs.val rhs.val) ⦄ := by
  unfold goldilocks.Goldilocks.Insts.P3_fieldFieldPrimeCharacteristicRing.dot_product
  have hl : lhs.val.length = N.val := lhs.property
  have hr : rhs.val.length = N.val := rhs.property
  have hc : (UScalar.cast .U32 N).val = N.val := by
    rw [UScalar.cast_val_eq, UScalarTy.U32_numBits_eq]; omega
  simp only [lift, bind_ok]
  step
  simp only [massert, UScalar.le_equiv, hc, i1_post, Nat.one_shiftLeft]
  rw [ite_eq_left (by simp [U32.size, U32.numBits]; omega)]
  simp only [bind_ok]
  have hidx : ∀ (A : Array goldilocks.Goldilocks N) (i : Std.Usize) (x : goldilocks.Goldilocks),
      A.val[i.val]? = some x → A.index_usize i = .ok x := by
    intro A i x h; unfold Array.index_usize; rw [show A[i]? = some x from h]
  split_ifs with h0 h1 h2
  · have e1 : lhs.val = [] := List.eq_nil_of_length_eq_zero (by rw [hl, h0]; rfl)
    unfold goldilocks.Goldilocks.Insts.P3_fieldFieldPrimeCharacteristicRing.ZERO
    step*
    rw [e1]; unfold toField; rw [r_post]; simp [dotField]
  · obtain ⟨x, hx⟩ := List.length_eq_one_iff.mp (by rw [hl, h1]; rfl : lhs.val.length = 1)
    obtain ⟨y, hy⟩ := List.length_eq_one_iff.mp (by rw [hr, h1]; rfl : rhs.val.length = 1)
    rw [hidx lhs 0#usize x (by rw [hx]; rfl), hidx rhs 0#usize y (by rw [hy]; rfl)]
    simp only [bind_ok]
    apply WP.spec_mono (mul.field x y)
    intro r h; unfold toField; rw [h, hx, hy]; simp [dotField, toField]
  · obtain ⟨x0, x1, hx⟩ := List.length_eq_two.mp (by rw [hl, h2]; rfl : lhs.val.length = 2)
    obtain ⟨y0, y1, hy⟩ := List.length_eq_two.mp (by rw [hr, h2]; rfl : rhs.val.length = 2)
    rw [hidx lhs 0#usize x0 (by rw [hx]; rfl), hidx rhs 0#usize y0 (by rw [hy]; rfl),
      hidx lhs 1#usize x1 (by rw [hx]; rfl), hidx rhs 1#usize y1 (by rw [hy]; rfl)]
    simp only [bind_ok]
    have hp0 := prodVal_lt (x0, y0)
    have hp1 := prodVal_lt (x1, y1)
    simp only [prodVal] at hp0 hp1
    have hdot : dotField (List.zip lhs.val rhs.val) =
        ((x0.value.val * y0.value.val + x1.value.val * y1.value.val : ℕ) : Goldilocks.Field) := by
      rw [hx, hy]; simp [dotField, toField]
    rw [hdot]
    step*
    apply WP.spec_bind OFFSET.spec
    intro off hoff
    step*
    · rename_i hov
      subst hov
      have hge := of_decide_eq_true over_post.symm
      clear over_post
      unfold toField
      apply natCast_eq_of_mod
      rw [r_post, sum_corr_post, sum_post, hoff, long_prod_0_post, long_prod_1_post]
      rw [long_prod_0_post, long_prod_1_post] at hge
      have hA : x0.value.val * y0.value.val ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1) :=
        Nat.mul_le_mul (by have := u64_lt x0.value; omega) (by have := u64_lt y0.value; omega)
      have hB : x1.value.val * y1.value.val ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1) :=
        Nat.mul_le_mul (by have := u64_lt x1.value; omega) (by have := u64_lt y1.value; omega)
      clear hp0 hp1
      generalize x0.value.val * y0.value.val = A at *
      generalize x1.value.val * y1.value.val = B at *
      have e : (A + B) % 2 ^ 128 + 2 ^ 128 - 18446744069414584321 * (2 ^ 64 + 2 ^ 32 - 1) =
          A + B - 18446744069414584321 * (2 ^ 64 + 2 ^ 32 - 1) := by
        have h1 : A + B - 2 ^ 128 < 2 ^ 128 := by omega
        rw [Nat.mod_eq_sub_mod hge, Nat.mod_eq_of_lt h1]; omega
      have h2 : A + B - 18446744069414584321 * (2 ^ 64 + 2 ^ 32 - 1) < 2 ^ 128 := by omega
      rw [e, Nat.mod_eq_of_lt h2]
      exact (mod_p_of_eq _ _ (2 ^ 64 + 2 ^ 32 - 1) (by omega)).symm
    · rename_i hov
      simp only [Bool.not_eq_true] at hov
      subst hov
      have hlt := of_decide_eq_false over_post.symm
      clear over_post
      rw [long_prod_0_post, long_prod_1_post, not_le] at hlt
      unfold toField
      apply natCast_eq_of_mod
      rw [r_post, sum_post, long_prod_0_post, long_prod_1_post, Nat.mod_eq_of_lt hlt]
  · have hL : (List.zip lhs.val rhs.val).length = N.val := by simp [hl, hr]
    have hH := sum_high_le (List.zip lhs.val rhs.val)
    have hA := sum_low_lt (List.zip lhs.val rhs.val)
    have hS := sum_split (List.zip lhs.val rhs.val)
    rw [hL] at hH hA
    rw [dotField_eq]
    apply WP.spec_bind (dot_fold.spec _ 0#u128 0#u64 (by rw [hL]; simp; omega))
    rintro ⟨lph, hi⟩ ⟨h1, h2⟩
    simp only [show (0#u128).val = 0 from rfl, show (0#u64).val = 0 from rfl, zero_add] at h1 h2
    generalize (List.map prodVal (List.zip lhs.val rhs.val)).sum = Sm at *
    generalize (List.map (fun xy => prodVal xy % 2 ^ 96) (List.zip lhs.val rhs.val)).sum = Al at *
    generalize (List.map (fun xy => prodVal xy / 2 ^ 96) (List.zip lhs.val rhs.val)).sum = Hs at *
    have hP : goldilocks.P = 18446744069414584321#u64 := by unfold goldilocks.P; rfl
    rw [hP]
    step*
    all_goals
      have hsz : U128.size = 2 ^ 128 := by simp [U128.size, U128.numBits]
      have hi2 : i2.val = (Hs * 2 ^ 96) % 2 ^ 128 := by
        rw [i2_post, cast_u64_u128_val, h2, Nat.shiftLeft_eq, hsz]
      have hlo : lo.val = Al := by rw [lo_post, h1, hi2, hS]; omega
      have hi3 : (UScalar.cast .U128 i3).val = 18446744069414584321 - Hs := by
        rw [cast_u64_u128_val, i3_post, h2]
    · rw [hlo, hi3]; simp only [U128.max_eq]; omega
    · unfold toField
      rw [natCast_eq_of_mod r_post, sum_post, hlo, hi3, hS]
      have e1 : ((Al + (18446744069414584321 - Hs) : ℕ) : Goldilocks.Field) = (Al : Goldilocks.Field) - Hs := by
        rw [Nat.cast_add, Nat.cast_sub (by omega)]
        rw [show ((18446744069414584321 : ℕ) : Goldilocks.Field) = 0 from by exact_mod_cast p_eq_zero]
        ring
      rw [e1, Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, two_pow_96]; ring

/-- FINDING: the `const` check of `dot_product` casts `N` to `u32` before comparing.

At `N = 2^32 + 3` the check passes, since `N as u32 = 3`.

At that length the `u64` sum of the top 32 bits can reach `2^64`, where `unchecked_add` overflows. -/
theorem dot_product.const_check_truncates (N : Std.Usize) (h : N.val = 2 ^ 32 + 3) :
    (UScalar.cast .U32 N).val ≤ 2 ^ 31 ∧ 2 ^ 64 ≤ N.val * (2 ^ 32 - 1) := by
  rw [UScalar.cast_val_eq, UScalarTy.U32_numBits_eq, h]
  decide

end Plonky3Lean.Proofs.P3Goldilocks
