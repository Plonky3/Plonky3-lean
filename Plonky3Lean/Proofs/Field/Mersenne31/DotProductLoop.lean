import Plonky3Lean.Proofs.Field.Mersenne31.Field

/-!
# Mersenne31: `dot_product`

Products of stored values are accumulated in a `u64`.

Chunks of four are folded with `partial_reduce`, then the remainder is added, then `reduce_64` reduces once.

The accumulator cannot overflow for `N < 2^30`.
-/

open Aeneas Aeneas.Std CoreModels
open p3_mersenne_31
open Plonky3Lean.Spec.Mersenne31 Plonky3Lean.Lib

namespace Plonky3Lean.Proofs.Mersenne31

/-- The product of the stored values at index `j`. -/
def prodAt (lhs rhs : List Element) (j : ℕ) : ℕ :=
  (lhs.getD j ⟨0#u32⟩).value.val * (rhs.getD j ⟨0#u32⟩).value.val

/-- The sum of the first `n` products. -/
def dotNat (lhs rhs : List Element) (n : ℕ) : ℕ := ((List.range n).map (prodAt lhs rhs)).sum

theorem dotNat_succ (lhs rhs : List Element) (n : ℕ) :
    dotNat lhs rhs (n + 1) = dotNat lhs rhs n + prodAt lhs rhs n := by
  simp [dotNat, List.range_succ]

theorem prodAt_lt (lhs rhs : List Element) (hl : ∀ x ∈ lhs, Valid x) (hr : ∀ x ∈ rhs, Valid x)
    (j : ℕ) : prodAt lhs rhs j < 2 ^ 62 := by
  have h1 : (lhs.getD j ⟨0#u32⟩).value.val < 2 ^ 31 := by
    rw [List.getD_eq_getElem?_getD]
    cases h : lhs[j]? with
    | none => simp
    | some x => exact hl x (List.mem_of_getElem? h)
  have h2 : (rhs.getD j ⟨0#u32⟩).value.val < 2 ^ 31 := by
    rw [List.getD_eq_getElem?_getD]
    cases h : rhs[j]? with
    | none => simp
    | some x => exact hr x (List.mem_of_getElem? h)
  unfold prodAt
  calc _ < 2 ^ 31 * 2 ^ 31 := Nat.mul_lt_mul'' h1 h2
    _ = 2 ^ 62 := by norm_num

theorem elem_lt {N : Std.Usize} (v : Array Element N) (hv : ∀ x ∈ v.val, Valid x) (k : ℕ)
    (hk : k < v.val.length) : (UScalar.cast .U64 (v.val[k]'hk).value).val < 2 ^ 31 := by
  rw [cast_u32_u64_val]; exact hv _ (List.getElem_mem hk)

theorem prod_eq {N : Std.Usize} (lhs rhs : Array Element N) (k : ℕ) (hk : k < lhs.val.length)
    (hk' : k < rhs.val.length) :
    (UScalar.cast .U64 (lhs.val[k]'hk).value).val * (UScalar.cast .U64 (rhs.val[k]'hk').value).val =
      prodAt lhs.val rhs.val k := by
  rw [cast_u32_u64_val, cast_u32_u64_val, prodAt, List.getD_eq_getElem _ _ hk,
    List.getD_eq_getElem _ _ hk']

/-- The invariant of the chunk loop. -/
def Inv0 (lhs rhs : List Element) (N : ℕ) (acc : Std.U64) (i : Std.Usize) : Prop :=
  i.val % 4 = 0 ∧ i.val ≤ N ∧ acc.val ≤ i.val / 4 * 2 ^ 34 ∧
    acc.val % 2147483647 = dotNat lhs rhs i.val % 2147483647

theorem loop0.body.spec {N : Std.Usize} (lhs rhs : Array Element N)
    (hl : ∀ x ∈ lhs.val, Valid x) (hr : ∀ x ∈ rhs.val, Valid x) (hN : N.val < 2 ^ 30)
    (acc : Std.U64) (i : Std.Usize) (hinv : Inv0 lhs.val rhs.val N.val acc i) :
    mersenne_31.Mersenne31.Insts.P3_fieldFieldPrimeCharacteristicRing.dot_product_loop0.body
      lhs rhs acc i ⦃ r => match r with
        | .done (acc', i') => acc' = acc ∧ i' = i ∧ N.val < i.val + 4
        | .cont (acc', i') => Inv0 lhs.val rhs.val N.val acc' i' ∧ N.val - i'.val < N.val - i.val ⦄ := by
  obtain ⟨h4, hiN, hacc, hmod⟩ := hinv
  unfold mersenne_31.Mersenne31.Insts.P3_fieldFieldPrimeCharacteristicRing.dot_product_loop0.body
  step*
  all_goals subst_vars
  all_goals
    have hl' := prodAt_lt lhs.val rhs.val hl hr
    try rw [prod_eq lhs rhs _ m m1] at i4_post
    try rw [prod_eq lhs rhs _ m2 m3] at i8_post
    try rw [prod_eq lhs rhs _ m4 m5] at i13_post
    try rw [prod_eq lhs rhs _ m6 m7] at i18_post
  · have := hl' i.val; have := hl' i5.val; scalar_tac
  · have := hl' i.val; have := hl' i5.val; have := hl' i10.val; scalar_tac
  · have := hl' i.val; have := hl' i5.val; have := hl' i10.val; have := hl' i15.val; scalar_tac
  have := hl' i.val; have := hl' i5.val; have := hl' i10.val; have := hl' i15.val
  have hcs : chunk_sum.val < 2 ^ 64 := by scalar_tac
  step with partial_reduce.spec chunk_sum as ⟨q, hq1, hq2⟩
  have hq : q.val < 2 ^ 34 := by rw [hq1]; omega
  have hi1N : i1.val ≤ N.val := by scalar_tac
  have hacc1 : acc.val + q.val ≤ U64.max := by
    have : i.val / 4 * 2 ^ 34 < 2 ^ 62 := by omega
    scalar_tac
  step*
  refine ⟨⟨by omega, hi1N, ?_, ?_⟩, by omega⟩
  · rw [acc1_post, i1_post]; omega
  · rw [acc1_post, i1_post, show i.val + 4 = i.val + 1 + 1 + 1 + 1 by ring, dotNat_succ, dotNat_succ,
      dotNat_succ, dotNat_succ]
    rw [i5_post] at i8_post; rw [i10_post] at i13_post; rw [i15_post] at i18_post
    omega

theorem loop0.spec {N : Std.Usize} (lhs rhs : Array Element N)
    (hl : ∀ x ∈ lhs.val, Valid x) (hr : ∀ x ∈ rhs.val, Valid x) (hN : N.val < 2 ^ 30) :
    mersenne_31.Mersenne31.Insts.P3_fieldFieldPrimeCharacteristicRing.dot_product_loop0
      lhs rhs 0#u64 0#usize ⦃ r => Inv0 lhs.val rhs.val N.val r.1 r.2 ∧ N.val < r.2.val + 4 ⦄ := by
  unfold mersenne_31.Mersenne31.Insts.P3_fieldFieldPrimeCharacteristicRing.dot_product_loop0
  refine loop.spec_decr_nat (fun p => N.val - p.2.val) (fun p => Inv0 lhs.val rhs.val N.val p.1 p.2)
    _ _ _ ?_ ⟨rfl, Nat.zero_le _, by simp, by simp [dotNat]⟩
  rintro ⟨acc, i⟩ hinv
  refine WP.spec_mono (loop0.body.spec lhs rhs hl hr hN acc i hinv) ?_
  rintro (⟨acc', i'⟩ | ⟨acc', i'⟩) h
  · exact h
  · obtain ⟨rfl, rfl, h⟩ := h; exact ⟨hinv, h⟩

/-- The invariant of the remainder loop, entered at `i0`. -/
def Inv1 (lhs rhs : List Element) (N i0 : ℕ) (acc : Std.U64) (i : Std.Usize) : Prop :=
  i0 ≤ i.val ∧ i.val ≤ N ∧ acc.val < 2 ^ 62 + (i.val - i0) * 2 ^ 62 ∧
    acc.val % 2147483647 = dotNat lhs rhs i.val % 2147483647

theorem loop1.body.spec {N : Std.Usize} (lhs rhs : Array Element N)
    (hl : ∀ x ∈ lhs.val, Valid x) (hr : ∀ x ∈ rhs.val, Valid x) (i0 : ℕ) (hi0 : N.val < i0 + 4)
    (acc : Std.U64) (i : Std.Usize) (hinv : Inv1 lhs.val rhs.val N.val i0 acc i) :
    mersenne_31.Mersenne31.Insts.P3_fieldFieldPrimeCharacteristicRing.dot_product_loop1.body
      lhs rhs acc i ⦃ r => match r with
        | .done acc' => acc' = acc ∧ i.val = N.val
        | .cont (acc', i') => Inv1 lhs.val rhs.val N.val i0 acc' i' ∧
            N.val - i'.val < N.val - i.val ⦄ := by
  obtain ⟨hi0i, hiN, hacc, hmod⟩ := hinv
  unfold mersenne_31.Mersenne31.Insts.P3_fieldFieldPrimeCharacteristicRing.dot_product_loop1.body
  step*
  all_goals subst_vars
  all_goals
    have hl' := prodAt_lt lhs.val rhs.val hl hr
  · rw [prod_eq lhs rhs _ m m1] at i3_post
    have := hl' i.val
    have : i.val - i0 ≤ 2 := by scalar_tac
    have : acc.val < 2 ^ 62 + 2 * 2 ^ 62 := by
      calc acc.val < 2 ^ 62 + (i.val - i0) * 2 ^ 62 := hacc
        _ ≤ 2 ^ 62 + 2 * 2 ^ 62 := by gcongr
    scalar_tac
  · rw [prod_eq lhs rhs _ m m1] at i3_post
    have := hl' i.val
    refine ⟨⟨by scalar_tac, by scalar_tac, ?_, ?_⟩, by scalar_tac⟩
    · rw [acc1_post, i3_post, i4_post]
      have : i.val + 1 - i0 = (i.val - i0) + 1 := by omega
      rw [this]; nlinarith
    · rw [acc1_post, i3_post, i4_post, dotNat_succ]; omega

theorem loop1.spec {N : Std.Usize} (lhs rhs : Array Element N)
    (hl : ∀ x ∈ lhs.val, Valid x) (hr : ∀ x ∈ rhs.val, Valid x) (i0 : ℕ) (hi0 : N.val < i0 + 4)
    (acc : Std.U64) (i : Std.Usize) (hinv : Inv1 lhs.val rhs.val N.val i0 acc i) :
    mersenne_31.Mersenne31.Insts.P3_fieldFieldPrimeCharacteristicRing.dot_product_loop1
      lhs rhs acc i ⦃ r => r.val % 2147483647 = dotNat lhs.val rhs.val N.val % 2147483647 ⦄ := by
  unfold mersenne_31.Mersenne31.Insts.P3_fieldFieldPrimeCharacteristicRing.dot_product_loop1
  refine loop.spec_decr_nat (fun p => N.val - p.2.val) (fun p => Inv1 lhs.val rhs.val N.val i0 p.1 p.2)
    _ _ _ ?_ hinv
  rintro ⟨acc, i⟩ hinv
  refine WP.spec_mono (loop1.body.spec lhs rhs hl hr i0 hi0 acc i hinv) ?_
  rintro (⟨acc', i'⟩ | acc') h
  · exact h
  · obtain ⟨rfl, h⟩ := h
    have := hinv.2.2.2
    simp only at this ⊢
    rw [h] at this; exact this

theorem prodAt_eq {N : Std.Usize} (lhs rhs : Array Element N) (k : ℕ) (hk : k < lhs.val.length)
    (hk' : k < rhs.val.length) :
    prodAt lhs.val rhs.val k = (lhs.val[k]'hk).value.val * (rhs.val[k]'hk').value.val := by
  rw [prodAt, List.getD_eq_getElem _ _ hk, List.getD_eq_getElem _ _ hk']

theorem dotNat_small (lhs rhs : List Element) :
    dotNat lhs rhs 1 = prodAt lhs rhs 0 ∧
    dotNat lhs rhs 2 = prodAt lhs rhs 0 + prodAt lhs rhs 1 ∧
    dotNat lhs rhs 3 = prodAt lhs rhs 0 + prodAt lhs rhs 1 + prodAt lhs rhs 2 ∧
    dotNat lhs rhs 4 = prodAt lhs rhs 0 + prodAt lhs rhs 1 + prodAt lhs rhs 2 + prodAt lhs rhs 3 := by
  simp [dotNat, List.range_succ, add_assoc]

theorem dot_product.spec {N : Std.Usize} (lhs rhs : Array Element N)
    (hl : ∀ x ∈ lhs.val, Valid x) (hr : ∀ x ∈ rhs.val, Valid x) (hN : N.val < 2 ^ 30) :
    mersenne_31.Mersenne31.Insts.P3_fieldFieldPrimeCharacteristicRing.dot_product lhs rhs ⦃ r =>
      Valid r ∧ r.value.val % 2147483647 = dotNat lhs.val rhs.val N.val % 2147483647 ⦄ := by
  have hl' := prodAt_lt lhs.val rhs.val hl hr
  unfold mersenne_31.Mersenne31.Insts.P3_fieldFieldPrimeCharacteristicRing.dot_product
  split
  · rename_i h
    simp only [WP.spec_ok, h, dotNat, List.range_zero, List.map_nil, List.sum_nil]
    unfold mersenne_31.Mersenne31.Insts.P3_fieldFieldPrimeCharacteristicRing.ZERO Valid
    decide
  all_goals
    rename_i h
    have hlen : lhs.val.length = N.val := lhs.property
    have hlen' : rhs.val.length = N.val := rhs.property
    obtain ⟨d1, d2, d3, d4⟩ := dotNat_small lhs.val rhs.val
    try have hd := congrArg (dotNat lhs.val rhs.val) h
  · step*
    all_goals subst_vars
    all_goals first
      | exact hl _ (List.getElem_mem _)
      | exact hr _ (List.getElem_mem _)
      | skip
    refine ⟨r_post1, ?_⟩
    rw [r_post2, hd, d1, prodAt_eq lhs rhs 0 (by omega) (by omega)]
  all_goals try (step*; all_goals subst_vars)
  all_goals (try simp only [cast_u32_u64_val] at *)
  all_goals
    have pk : ∀ k (h1 : k < lhs.val.length) (h2 : k < rhs.val.length),
        (lhs.val[k]'h1).value.val * (rhs.val[k]'h2).value.val < 2 ^ 62 := fun k h1 h2 => by
      rw [← prodAt_eq lhs rhs k h1 h2]; exact hl' k
    try have := pk 0 m m1
    try have := pk 1 m2 m3
    try have := pk 2 m4 m5
    try have := pk 3 m6 m7
  all_goals first | scalar_tac | skip
  iterate 3
    · refine ⟨by unfold Valid; omega, ?_⟩
      rw [hd]
      first | rw [d2] | rw [d3] | rw [d4]
      rw [prodAt_eq lhs rhs 0 m m1, prodAt_eq lhs rhs 1 m2 m3]
      try rw [prodAt_eq lhs rhs 2 m4 m5]
      try rw [prodAt_eq lhs rhs 3 m6 m7]
      omega
  refine WP.spec_bind (loop0.spec lhs rhs hl hr hN) ?_
  rintro ⟨acc, i⟩ ⟨⟨h4, hiN, hacc, hmod⟩, hlt⟩
  simp only at h4 hiN hacc hmod hlt
  step with loop1.spec lhs rhs hl hr i.val hlt acc i
    ⟨le_rfl, hiN, by have : i.val / 4 * 2 ^ 34 < 2 ^ 62 := by omega
                     simp only [Nat.sub_self, zero_mul, add_zero]; omega, hmod⟩ as ⟨acc1, h1⟩
  step*
  refine ⟨by unfold Valid; rw [r_post]; omega, by rw [r_post]; omega⟩

end Plonky3Lean.Proofs.Mersenne31

namespace Plonky3Lean.Proofs.Mersenne31

/-- `dot_product` is the field dot product, for `N < 2^30`. -/
theorem dot_product.toField {N : Std.Usize} (lhs rhs : Array Element N)
    (hl : ∀ x ∈ lhs.val, Valid x) (hr : ∀ x ∈ rhs.val, Valid x) (hN : N.val < 2 ^ 30) :
    mersenne_31.Mersenne31.Insts.P3_fieldFieldPrimeCharacteristicRing.dot_product lhs rhs ⦃ r =>
      Valid r ∧ Spec.Mersenne31.toField r = ((List.range N.val).map fun j =>
        Spec.Mersenne31.toField (lhs.val.getD j ⟨0#u32⟩) *
          Spec.Mersenne31.toField (rhs.val.getD j ⟨0#u32⟩)).sum ⦄ := by
  refine WP.spec_mono (dot_product.spec lhs rhs hl hr hN) ?_
  rintro r ⟨hv, hr'⟩
  refine ⟨hv, ?_⟩
  unfold Spec.Mersenne31.toField
  rw [(natCast_eq_iff _ _).mpr hr', dotNat, Nat.cast_list_sum, List.map_map]
  congr 1
  apply List.map_congr_left
  intro j _
  simp [prodAt]

end Plonky3Lean.Proofs.Mersenne31
