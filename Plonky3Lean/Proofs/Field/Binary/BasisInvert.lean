module

public import Plonky3Lean.Proofs.Field.Binary.BasisLinear

@[expose] public section

/-!
# Inverting the change of basis

`invert` runs Gauss-Jordan elimination over `GF(2)` on the columns of a map, replaying every
column operation on the identity. Throughout, each column of `mat` is the map applied to the
same column of `inv` (`GJ`), and the determinant of `mat` stays nonzero, so every pivot search
succeeds (`exists_pivot`) and the `assert!` never fires. At the end `mat` is the identity, so
`inv` holds the columns of the inverse map.
-/

open Aeneas Aeneas.Std CoreModels Polynomial
open p3_binary_field BinaryField
open Plonky3Lean.Lib Plonky3Lean.Spec.BinaryField

namespace Plonky3Lean.Proofs.Binary

/-- Each column of `m` is the map with columns `cols` applied to the same column of `v`, all of
them below `2^bits`, and `m` is nonsingular. -/
def GJ (bits : ℕ) (cols m v : ℕ → ℕ) : Prop :=
  (∀ c < bits, m c = lin cols bits (v c) ∧ m c < 2 ^ bits ∧ v c < 2 ^ bits) ∧
    (rowM bits m).det ≠ 0

/-- `m` agrees with the identity on its first `p` rows. -/
def Reduced (bits p : ℕ) (m : ℕ → ℕ) : Prop :=
  ∀ c < bits, ∀ i < p, (m c).testBit i = decide (c = i)

theorem GJ_add {bits : ℕ} {cols m v : ℕ → ℕ} (h : GJ bits cols m v) {p c : ℕ} (hp : p < bits)
    (hc : c < bits) (hpc : c ≠ p) :
    GJ bits cols (fun r => if r = c then m c ^^^ m p else m r)
      (fun r => if r = c then v c ^^^ v p else v r) := by
  obtain ⟨hcol, hdet⟩ := h
  refine ⟨fun r hr => ?_, by rw [det_rowM_add m hp hc hpc]; exact hdet⟩
  by_cases hrc : r = c
  · subst hrc
    obtain ⟨e1, b1, b1'⟩ := hcol r hr
    obtain ⟨e2, b2, b2'⟩ := hcol p hp
    simp only [↓reduceIte]
    exact ⟨by rw [lin_xor, ← e1, ← e2], Nat.xor_lt_two_pow b1 b2, Nat.xor_lt_two_pow b1' b2'⟩
  · simp only [hrc, ↓reduceIte]
    exact hcol r hr

theorem GJ_swap {bits : ℕ} {cols m v : ℕ → ℕ} (h : GJ bits cols m v) {p c : ℕ} (hp : p < bits)
    (hc : c < bits) :
    GJ bits cols (fun r => if r = c then m p else if r = p then m c else m r)
      (fun r => if r = c then v p else if r = p then v c else v r) := by
  obtain ⟨hcol, hdet⟩ := h
  refine ⟨fun r hr => ?_, det_rowM_swap hp hc hdet⟩
  by_cases hrc : r = c
  · simp only [hrc, ↓reduceIte]; exact hcol p hp
  · by_cases hrp : r = p
    · subst hrp
      simp only [hrc, ↓reduceIte]
      exact hcol c hc
    · simp only [hrc, hrp, ↓reduceIte]; exact hcol r hr

/-! ## Arrays -/

theorem aval_eq_getElem (a : Std.Array Std.U128 128#usize) (c : ℕ) (h : c < a.val.length) :
    aval a c = (a.val[c]).val := by
  rw [aval, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h, Option.getD_some]

theorem aval_swap (a : Std.Array Std.U128 128#usize) (p c : Std.Usize) (hp : p.val < 128)
    (hc : c.val < 128) (x y : Std.U128) (hx : x.val = aval a c.val) (hy : y.val = aval a p.val) :
    aval ((a.set p x).set c y) = fun r =>
      if r = c.val then aval a p.val else if r = p.val then aval a c.val else aval a r := by
  funext r
  rw [aval_set _ _ _ hc, aval_set _ _ _ hp, hx, hy]

theorem aval_xor (a : Std.Array Std.U128 128#usize) (p c : Std.Usize) (hc : c.val < 128)
    (x : Std.U128) (hx : x.val = aval a c.val ^^^ aval a p.val) :
    aval (a.set c x) = fun r => if r = c.val then aval a c.val ^^^ aval a p.val else aval a r := by
  funext r
  rw [aval_set _ _ _ hc, hx]

/-! ## The pivot search -/

theorem invert_search_spec (bits : Std.Usize) (h128 : bits.val ≤ 128)
    (mat : Std.Array Std.U128 128#usize) (pivot : Std.Usize) (hp : pivot.val < bits.val)
    (col : Std.Usize) (hpc : pivot.val ≤ col.val) (hcb : col.val ≤ bits.val)
    (hz : ∀ c, pivot.val ≤ c → c < col.val → (aval mat c).testBit pivot.val = false) :
    clmul.basis.invert_loop1_loop0 bits mat pivot col ⦃ r => pivot.val ≤ r.val ∧
      r.val ≤ bits.val ∧
      (∀ c, pivot.val ≤ c → c < r.val → (aval mat c).testBit pivot.val = false) ∧
      (r.val < bits.val → (aval mat r.val).testBit pivot.val = true) ⦄ := by
  unfold clmul.basis.invert_loop1_loop0
  refine loop.spec_decr_nat (fun c => bits.val - c.val)
    (fun c => pivot.val ≤ c.val ∧ c.val ≤ bits.val ∧
      ∀ c', pivot.val ≤ c' → c' < c.val → (aval mat c').testBit pivot.val = false) _ _ _ ?_
    ⟨hpc, hcb, hz⟩
  rintro c ⟨hc1, hc2, hcz⟩
  unfold clmul.basis.invert_loop1_loop0.body
  step*
  all_goals have hi : aval mat c.val = i.val := by rw [i_post1, aval_eq_getElem]
  all_goals have hb : i2.val = (aval mat c.val >>> pivot.val) &&& 1 := by rw [i2_post, UScalar.val_and, i1_post, hi]; rfl
  · have h0 : (aval mat c.val).testBit pivot.val = false := by
      have : (aval mat c.val >>> pivot.val) &&& 1 = 0 := by rw [← hb, ‹i2 = 0#u128›]; rfl
      rw [shiftRight_and_one_eq] at this
      simpa using this
    refine ⟨by omega, by scalar_tac, fun c' h1 h2 => ?_, by scalar_tac⟩
    by_cases hcc : c' = c.val
    · rw [hcc]; exact h0
    · exact hcz c' h1 (by omega)
  · refine ⟨hc1, hc2, hcz, fun _ => ?_⟩
    have : (aval mat c.val >>> pivot.val) &&& 1 ≠ 0 := by
      rw [← hb]
      intro h
      exact ‹¬i2 = 0#u128› (UScalar.eq_of_val_eq h)
    rw [shiftRight_and_one_eq] at this
    simpa using this

/-! ## Clearing the pivot column -/

theorem invert_elim_spec (bits : Std.Usize) (h128 : bits.val ≤ 128) (cols : ℕ → ℕ)
    (pivot : Std.Usize) (hp : pivot.val < bits.val)
    (mat inv : Std.Array Std.U128 128#usize) (col : Std.Usize) (hcb : col.val ≤ bits.val)
    (hgj : GJ bits.val cols (aval mat) (aval inv)) (hred : Reduced bits.val pivot.val (aval mat))
    (hpiv : (aval mat pivot.val).testBit pivot.val = true)
    (hdone : ∀ c < col.val, c ≠ pivot.val → (aval mat c).testBit pivot.val = false) :
    clmul.basis.invert_loop1_loop1 bits mat inv pivot col ⦃ r =>
      GJ bits.val cols (aval r.1) (aval r.2) ∧ Reduced bits.val pivot.val (aval r.1) ∧
      (aval r.1 pivot.val).testBit pivot.val = true ∧
      ∀ c < bits.val, c ≠ pivot.val → (aval r.1 c).testBit pivot.val = false ⦄ := by
  unfold clmul.basis.invert_loop1_loop1
  refine loop.spec_decr_nat (fun s => bits.val - s.2.2.val)
    (fun s => s.2.2.val ≤ bits.val ∧ GJ bits.val cols (aval s.1) (aval s.2.1) ∧
      Reduced bits.val pivot.val (aval s.1) ∧
      (aval s.1 pivot.val).testBit pivot.val = true ∧
      ∀ c < s.2.2.val, c ≠ pivot.val → (aval s.1 c).testBit pivot.val = false) _ _ _ ?_ ?_
  rotate_left
  · exact ⟨hcb, hgj, hred, hpiv, hdone⟩
  rintro ⟨m, v, c⟩ ⟨hc, hg, hr, hpv, hd⟩
  dsimp only at hc hg hr hpv hd ⊢
  unfold clmul.basis.invert_loop1_loop1.body
  step*
  all_goals have hcb' : c.val < bits.val := by scalar_tac
  rotate_left 2
  · refine ⟨by scalar_tac, hg, hr, hpv, fun c' hc' hne => hd c' ?_ hne, by scalar_tac⟩
    have : c.val = pivot.val := by simpa using ‹¬(c != pivot) = true›
    have : c' ≠ c.val := by rw [this]; exact hne
    omega
  all_goals have hcp : c.val ≠ pivot.val := by simpa using ‹(c != pivot) = true›
  all_goals have hi : aval m c.val = i.val := by rw [i_post1, aval_eq_getElem]
  all_goals have hb : i2.val = if (aval m c.val).testBit pivot.val then 1 else 0 := by rw [i2_post, UScalar.val_and, i1_post, ← hi, ← shiftRight_and_one_eq]; rfl
  · have hbit : (aval m c.val).testBit pivot.val = true := by
      have h1 : i2.val = 1 := by rw [‹i2 = 1#u128›]; rfl
      rw [hb] at h1
      by_contra h
      simp [h] at h1
    have ha : aval a = fun r => if r = c.val then aval m c.val ^^^ aval m pivot.val
        else aval m r := by
      rw [a_post]
      exact aval_xor m pivot c (by omega) i4 (by
        rw [i4_post, UScalar.val_xor, hi, i3_post1, aval_eq_getElem])
    have ha1 : aval a1 = fun r => if r = c.val then aval v c.val ^^^ aval v pivot.val
        else aval v r := by
      rw [a1_post]
      exact aval_xor v pivot c (by omega) i7 (by
        rw [i7_post, UScalar.val_xor, i6_post1, i5_post1, aval_eq_getElem, aval_eq_getElem])
    rw [ha, ha1]
    refine ⟨by scalar_tac, GJ_add hg hp hcb' hcp, fun r hrb i hip => ?_, ?_,
      fun c' hc' hne => ?_, by scalar_tac⟩
    · dsimp only
      split
      · rename_i hrc
        rw [Nat.testBit_xor, ← hrc, hr r hrb i hip, hr pivot.val hp i hip]
        have : pivot.val ≠ i := by omega
        simp [this]
      · exact hr r hrb i hip
    · dsimp only
      rw [ite_eq_right (Ne.symm hcp)]
      exact hpv
    · dsimp only
      split
      · rename_i hrc
        rw [Nat.testBit_xor, hbit, hpv]
        rfl
      · exact hd c' (by scalar_tac) hne
  · have hbit : (aval m c.val).testBit pivot.val = false := by
      by_contra h
      have h1 : i2.val = 1 := by rw [hb]; simp [h]
      exact ‹¬i2 = 1#u128› (UScalar.eq_of_val_eq h1)
    refine ⟨by scalar_tac, hg, hr, hpv, fun c' hc' hne => ?_, by scalar_tac⟩
    by_cases hcc : c' = c.val
    · rw [hcc]; exact hbit
    · exact hd c' (by scalar_tac) hne

/-! ## The pivots -/

theorem reduced_full {bits : ℕ} {m : ℕ → ℕ} (hr : Reduced bits bits m) {c : ℕ} (hc : c < bits)
    (hm : m c < 2 ^ bits) : m c = 2 ^ c := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_two_pow]
  by_cases hi : i < bits
  · rw [hr c hc i hi]
  · rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le hm (Nat.pow_le_pow_right (by norm_num) (by omega)))]
    simp; omega

theorem invert_outer_spec (bits : Std.Usize) (h128 : bits.val ≤ 128) (cols : ℕ → ℕ)
    (mat inv : Std.Array Std.U128 128#usize) (pivot : Std.Usize) (hpb : pivot.val ≤ bits.val)
    (hgj : GJ bits.val cols (aval mat) (aval inv)) (hred : Reduced bits.val pivot.val (aval mat)) :
    clmul.basis.invert_loop1 bits mat inv pivot ⦃ r => ∀ c < bits.val,
      aval r c < 2 ^ bits.val ∧ lin cols bits.val (aval r c) = 2 ^ c ⦄ := by
  unfold clmul.basis.invert_loop1
  refine loop.spec_decr_nat (fun s => bits.val - s.2.2.val)
    (fun s => s.2.2.val ≤ bits.val ∧ GJ bits.val cols (aval s.1) (aval s.2.1) ∧
      Reduced bits.val s.2.2.val (aval s.1)) _ _ _ ?_ ?_
  rotate_left
  · exact ⟨hpb, hgj, hred⟩
  rintro ⟨m, v, p⟩ ⟨hp, hg, hr⟩
  dsimp only at hp hg hr ⊢
  unfold clmul.basis.invert_loop1.body
  split
  · rename_i hpl
    have hpl' : p.val < bits.val := by scalar_tac
    apply WP.spec_bind (invert_search_spec bits h128 m p hpl' p le_rfl (by omega)
      (fun c h1 h2 => absurd h2 (by omega)))
    rintro col ⟨h1, h2, h3, h4⟩
    have hcol : col.val < bits.val := by
      obtain ⟨r, hr1, hr2, hr3⟩ := exists_pivot hg.2 hpl' hr
      by_contra hc
      have := h3 r hr1 (by omega)
      rw [hr3] at this
      exact absurd this (by simp)
    step*
    have hm := aval_swap m p col (by omega) (by omega) i swapped
      (by rw [i_post1, aval_eq_getElem]) (by rw [swapped_post1, aval_eq_getElem])
    have hv := aval_swap v p col (by omega) (by omega) i1 swapped1
      (by rw [i1_post1, aval_eq_getElem]) (by rw [swapped1_post1, aval_eq_getElem])
    rw [← mat1_post, ← a_post] at hm
    rw [← inv1_post, ← a1_post] at hv
    have hred' : Reduced bits.val p.val (aval a) := by
      intro r hrb i' hi'
      rw [hm]
      dsimp only
      split
      · rename_i hrc
        rw [hr p.val hpl' i' hi']
        simp only [decide_eq_decide]
        omega
      · split
        · rename_i _ hrp
          rw [hr col.val hcol i' hi']
          simp only [decide_eq_decide]
          omega
        · exact hr r hrb i' hi'
    have hpiv : (aval a p.val).testBit p.val = true := by
      rw [hm]
      dsimp only
      split
      · rename_i hpc
        have := h4 hcol
        rw [← hpc] at this
        exact this
      · simp only [↓reduceIte]
        exact h4 hcol
    have hgj' : GJ bits.val cols (aval a) (aval a1) := by
      rw [hm, hv]
      exact GJ_swap hg hpl' hcol
    apply WP.spec_bind (invert_elim_spec bits h128 cols p hpl' a a1 0#usize (by simp) hgj' hred'
      hpiv (fun c hc => absurd hc (by simp)))
    rintro ⟨mat2, inv2⟩ ⟨hg2, hr2, hp2, hd2⟩
    step*
    refine ⟨by scalar_tac, hg2, fun r hrb i' hi' => ?_, by scalar_tac⟩
    by_cases hip : i' = p.val
    · subst hip
      by_cases hrp : r = p.val
      · subst hrp; rw [hp2]; simp
      · rw [hd2 r hrb hrp]; simp [hrp]
    · exact hr2 r hrb i' (by scalar_tac)
  · rename_i hpl
    have : p.val = bits.val := by scalar_tac
    rw [this] at hr
    rw [WP.spec_ok]
    intro c hc
    obtain ⟨he, hb1, hb2⟩ := hg.1 c hc
    exact ⟨hb2, by rw [← he]; exact reduced_full hr hc hb1⟩

/-! ## `invert` -/

theorem invert_init_spec (bits : Std.Usize) (h128 : bits.val ≤ 128)
    (inv : Std.Array Std.U128 128#usize) (j : Std.Usize) (hj : j.val ≤ bits.val)
    (hdone : ∀ c < j.val, aval inv c = 2 ^ c) :
    clmul.basis.invert_loop0 bits inv j ⦃ r => ∀ c < bits.val, aval r c = 2 ^ c ⦄ := by
  unfold clmul.basis.invert_loop0
  refine loop.spec_decr_nat (fun s => bits.val - s.2.val)
    (fun s => s.2.val ≤ bits.val ∧ ∀ c < s.2.val, aval s.1 c = 2 ^ c) _ _ _ ?_ ?_
  rotate_left
  · exact ⟨hj, hdone⟩
  rintro ⟨v, n⟩ ⟨hn, hd⟩
  dsimp only at hn hd ⊢
  unfold clmul.basis.invert_loop0.body
  step*
  · refine ⟨by scalar_tac, fun c hc => ?_, by scalar_tac⟩
    rw [a_post, aval_set _ _ _ (by scalar_tac)]
    split
    · rename_i hcn
      rw [i_post, hcn, Nat.one_shiftLeft]
      have : 2 ^ n.val < 2 ^ 128 := Nat.pow_lt_pow_right (by norm_num) i_post2
      exact Nat.mod_eq_of_lt (by simpa [U128.size, U128.numBits] using this)
    · exact hd c (by scalar_tac)

/-- `invert` returns the columns of the inverse of an injective map. -/
theorem invert_spec (cols : Std.Array Std.U128 128#usize) (bits : Std.Usize)
    (h128 : bits.val ≤ 128) (hcols : ∀ c < bits.val, aval cols c < 2 ^ bits.val)
    (hinj : ∀ w < 2 ^ bits.val, lin (aval cols) bits.val w = 0 → w = 0) :
    clmul.basis.invert cols bits ⦃ r => ∀ c < bits.val,
      aval r c < 2 ^ bits.val ∧ lin (aval cols) bits.val (aval r c) = 2 ^ c ⦄ := by
  unfold clmul.basis.invert
  obtain ⟨z, hz, hzall⟩ :=
    Lib.array_repeat_eq 128#usize core.U128.Insts.CoreCloneClone (fun _ => rfl) 0#u128
  rw [hz, Aeneas.Std.bind_ok]
  apply WP.spec_bind (invert_init_spec bits h128 z 0#usize (by simp)
    (fun c hc => absurd hc (by simp)))
  intro inv hinv
  refine invert_outer_spec bits h128 (aval cols) cols inv 0#usize (by simp) ⟨fun c hc => ?_, ?_⟩
    (fun _ _ i hi => absurd hi (by simp))
  · rw [hinv c hc, lin_two_pow _ hc]
    exact ⟨rfl, hcols c hc, Nat.pow_lt_pow_right (by norm_num) hc⟩
  · exact det_rowM_ne_zero hcols hinj

end Plonky3Lean.Proofs.Binary
