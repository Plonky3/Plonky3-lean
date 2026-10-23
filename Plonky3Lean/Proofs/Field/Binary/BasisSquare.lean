module

public import Plonky3Lean.Proofs.Field.Binary.ClmulPaths

@[expose] public section

/-!
# Squaring through a table

Squaring is `GF(2)`-linear in characteristic 2, so in the tower basis it is a matrix.
`square_columns` computes its columns `M(N(e_j)^2)`, and `tower_square_64` applies them a byte at
a time. The result is the tower square (`tower_square_64_spec`), and `square_128` builds the
square at 128 bits from two squares at 64 bits.
-/

open Aeneas Aeneas.Std CoreModels Polynomial
open ConcreteBinaryTower ConcreteBinaryTower.Coordinates
open p3_binary_field BinaryField
open Plonky3Lean.Lib Plonky3Lean.Spec.BinaryField

namespace Plonky3Lean.Proofs.Binary

/-! ## `square_columns` -/

theorem square_inner_spec (bits : Std.Usize) (h128 : bits.val ≤ 128)
    (inverse : Std.Array Std.U128 128#usize) (image column : Std.U128) (i : Std.Usize)
    (hi : i.val ≤ bits.val) (hc : column.val = lin (aval inverse) i.val image.val) :
    clmul.basis.square_columns_loop0_loop0 bits inverse image column i ⦃ r =>
      r.val = lin (aval inverse) bits.val image.val ⦄ := by
  unfold clmul.basis.square_columns_loop0_loop0
  refine loop.spec_decr_nat (fun s => bits.val - s.2.val)
    (fun s => s.2.val ≤ bits.val ∧ s.1.val = lin (aval inverse) s.2.val image.val) _ _ _ ?_
    ⟨hi, hc⟩
  rintro ⟨col, n⟩ ⟨hn, hcol⟩
  dsimp only at hn hcol ⊢
  unfold clmul.basis.square_columns_loop0_loop0.body
  step*
  have hb : i2.val = if image.val.testBit n.val then 1 else 0 := by
    rw [i2_post, UScalar.val_and, i1_post, ← shiftRight_and_one_eq]; rfl
  split
  · rename_i h1
    have hbit : image.val.testBit n.val = true := by
      have : i2.val = 1 := by rw [h1]; rfl
      rw [hb] at this
      by_contra h; simp [h] at this
    step*
    refine ⟨by scalar_tac, ?_, by scalar_tac⟩
    rw [UScalar.val_xor, hcol, x_post1, ← aval_eq_getElem, i3_post, lin, hbit]
    rfl
  · rename_i h1
    have hbit : image.val.testBit n.val = false := by
      by_contra h
      have : i2.val = 1 := by rw [hb]; simp [h]
      exact h1 (UScalar.eq_of_val_eq this)
    step*
    refine ⟨by scalar_tac, ?_, by scalar_tac⟩
    rw [hcol, i3_post, lin, hbit]
    simp

theorem square_outer_spec (bits : Std.Usize) (h1 : 1 ≤ bits.val) (h128 : bits.val ≤ 128)
    (tail : Std.U128) (ht : tail.val < 2 ^ bits.val)
    (cols inverse sq : Std.Array Std.U128 128#usize)
    (hcols : ∀ j < bits.val, aval cols j < 2 ^ bits.val) (j : Std.Usize) (hj : j.val ≤ bits.val)
    (hdone : ∀ j' < j.val, ∃ pm, pm < 2 ^ bits.val ∧
      AdjoinRoot.mk (modPoly bits.val tail.val) (natPoly pm) =
        AdjoinRoot.mk (modPoly bits.val tail.val) (natPoly (aval cols j')) ^ 2 ∧
      aval sq j' = lin (aval inverse) bits.val pm) :
    clmul.basis.square_columns_loop0 bits tail cols inverse sq j ⦃ r => ∀ j' < bits.val,
      ∃ pm, pm < 2 ^ bits.val ∧
        AdjoinRoot.mk (modPoly bits.val tail.val) (natPoly pm) =
          AdjoinRoot.mk (modPoly bits.val tail.val) (natPoly (aval cols j')) ^ 2 ∧
        aval r j' = lin (aval inverse) bits.val pm ⦄ := by
  unfold clmul.basis.square_columns_loop0
  refine loop.spec_decr_nat (fun s => bits.val - s.2.val)
    (fun s => s.2.val ≤ bits.val ∧ ∀ j' < s.2.val, ∃ pm, pm < 2 ^ bits.val ∧
      AdjoinRoot.mk (modPoly bits.val tail.val) (natPoly pm) =
        AdjoinRoot.mk (modPoly bits.val tail.val) (natPoly (aval cols j')) ^ 2 ∧
      aval s.1 j' = lin (aval inverse) bits.val pm) _ _ _ ?_ ⟨hj, hdone⟩
  rintro ⟨sqs, n⟩ ⟨hn, hd⟩
  dsimp only at hn hd ⊢
  unfold clmul.basis.square_columns_loop0.body
  step*
  have hnb : n.val < bits.val := by scalar_tac
  have hiv : i.val = aval cols n.val := by rw [i_post1, aval_eq_getElem]
  have hib : i.val < 2 ^ bits.val := by rw [hiv]; exact hcols n.val hnb
  apply WP.spec_bind (poly_mul_spec i i tail bits h1 h128 hib hib ht)
  rintro image ⟨himb, himg⟩
  apply WP.spec_bind (square_inner_spec bits h128 inverse image 0#u128 0#usize (by simp) rfl)
  intro column hcol
  step*
  refine ⟨by scalar_tac, fun j' hj' => ?_, by scalar_tac⟩
  rw [a_post, aval_set _ _ _ (by omega)]
  by_cases hjn : j' = n.val
  · rw [ite_eq_left hjn]
    refine ⟨image.val, himb, ?_, hcol⟩
    rw [himg, map_mul, hjn, ← hiv, _root_.sq]
  · rw [ite_eq_right hjn]
    exact hd j' (by scalar_tac)

/-- Column `j` of `square_columns` is `M(N(e_j)^2)`: the map `N` sends it to the square of
column `j` of `N`. -/
theorem square_columns_spec (bits : Std.Usize) (h1 : 1 ≤ bits.val) (h128 : bits.val ≤ 128)
    (tail : Std.U128) (ht : tail.val < 2 ^ bits.val) (cols : Std.Array Std.U128 128#usize)
    (hcols : ∀ j < bits.val, aval cols j < 2 ^ bits.val)
    (hinj : ∀ w < 2 ^ bits.val, lin (aval cols) bits.val w = 0 → w = 0) :
    clmul.basis.square_columns bits tail cols ⦃ r => ∀ j < bits.val,
      aval r j < 2 ^ bits.val ∧
      AdjoinRoot.mk (modPoly bits.val tail.val) (natPoly (lin (aval cols) bits.val (aval r j))) =
        AdjoinRoot.mk (modPoly bits.val tail.val) (natPoly (aval cols j)) ^ 2 ⦄ := by
  unfold clmul.basis.square_columns
  apply WP.spec_bind (invert_spec cols bits h128 hcols hinj)
  intro inv hinv
  obtain ⟨z, hz, -⟩ :=
    Lib.array_repeat_eq 128#usize core.U128.Insts.CoreCloneClone (fun _ => rfl) 0#u128
  rw [hz, Aeneas.Std.bind_ok]
  apply WP.spec_mono (square_outer_spec bits h1 h128 tail ht cols inv z hcols 0#usize (by simp)
    (fun _ h => absurd h (by simp)))
  intro r hr j hj
  obtain ⟨pm, hpm, hmk, hrj⟩ := hr j hj
  refine ⟨by rw [hrj]; exact lin_lt _ _ _ (fun c hc => (hinv c hc).1), ?_⟩
  rw [hrj, lin_lin, lin_congr_cols bits.val pm (fun c hc => (hinv c hc).2), lin_two_pow_cols,
    Nat.mod_eq_of_lt hpm, hmk]

/-! ## 64 bits -/

/-- In characteristic 2, squaring a sum squares each term. -/
theorem sq_sum_ite {R : Type} [CommRing R] [CharP R 2] (k : ℕ) (b : ℕ → Bool) (y : ℕ → R) :
    (∑ j ∈ Finset.range k, if b j then y j else 0) ^ 2 =
      ∑ j ∈ Finset.range k, if b j then y j ^ 2 else 0 := by
  have h := map_sum (frobenius R 2) (fun j => if b j then y j else 0) (Finset.range k)
  simp only [frobenius_def] at h
  rw [h]
  apply Finset.sum_congr rfl
  intro j _
  split <;> simp

theorem SQUARE_64_spec : clmul.basis.SQUARE_64 ⦃ T =>
    ∃ c s : ℕ → ℕ, (∀ j < 64, AdjoinRoot.mk (modPoly 64 27) (natPoly (c j)) = colV xi64 6 j) ∧
      (∀ j < 64, s j < 2 ^ 64 ∧ AdjoinRoot.mk (modPoly 64 27) (natPoly (lin c 64 (s j))) =
        AdjoinRoot.mk (modPoly 64 27) (natPoly (c j)) ^ 2) ∧
      ∀ k < 8, ∀ w < 256, cellOf T k w = linB s k w ⦄ := by
  unfold clmul.basis.SQUARE_64
  apply WP.spec_bind COLUMNS_64_spec
  intro cols hcols
  have hsq := square_columns_spec 64#usize (by simp) (by simp) clmul.basis.TAIL_64
    (by rw [TAIL_64_val]; norm_num) cols (fun j hj => (hcols j hj).1)
    (fun w hw h0 => lin_injective (by norm_num) (by norm_num) xi64 6 xi64_rel (aval cols)
      (fun j hj => (hcols j hj).2) hw h0)
  rw [TAIL_64_val] at hsq
  apply WP.spec_bind hsq
  intro sq hsq'
  apply WP.spec_bind (byte_tables_spec sq 64#usize (by simp))
  intro T hT
  apply WP.spec_mono (narrow_spec T)
  intro N hN
  refine ⟨aval cols, aval sq, fun j hj => (hcols j hj).2, fun j hj => hsq' j hj,
    fun k hk w hw => ?_⟩
  rw [hN k hk w hw, hT k (by simpa using hk) w hw,
    Nat.mod_eq_of_lt (linB_lt (b := 8) (fun j hj => (hsq' j hj).1) hk w)]

/-- `tower_square_64` squares in the tower's `GF(2^64)`. -/
theorem tower_square_64_spec (v : Std.U64) :
    clmul.basis.tower_square_64 v ⦃ r => towerOf 6 r = towerOf 6 v ^ 2 ⦄ := by
  unfold clmul.basis.tower_square_64
  apply WP.spec_bind SQUARE_64_spec
  rintro T ⟨c, s, hc, hs, hT⟩
  apply WP.spec_mono (apply_64_spec T s hT v)
  intro r hr
  have := charP_modPoly (n := 64) (tail := 27) (by norm_num) (by norm_num)
  apply N64_injective
  rw [map_pow, N64_apply, N64_apply, towerOf, towerOf,
    ← lin_eq_towerMap xi64 6 c hc (u64_val_lt r), ← lin_eq_towerMap xi64 6 c hc (u64_val_lt v),
    show (2 : ℕ) ^ 6 = 64 from rfl, hr, lin_lin, mk_lin, mk_lin, sq_sum_ite]
  apply Finset.sum_congr rfl
  intro j hj
  rw [(hs j (Finset.mem_range.mp hj)).2]

/-- `square_64`, the table squaring of the tower's `GF(2^64)`. -/
theorem clmul_square_64_spec (v : Std.U64) :
    clmul.square_64 v ⦃ r => towerOf 6 r = towerOf 6 v ^ 2 ⦄ := by
  unfold clmul.square_64
  exact tower_square_64_spec v

end Plonky3Lean.Proofs.Binary
