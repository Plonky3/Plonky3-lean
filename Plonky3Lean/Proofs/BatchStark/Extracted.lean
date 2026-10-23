module

public import P3BatchStark
public import Mathlib.Algebra.BigOperators.Group.List.Basic

@[expose] public section

/-!
# The extracted opening count

The opening-batching challenge is charged one power per column and opening point, two for Circle.

The count is therefore a sum over the committed matrices of width times points:

```text
    main trace           width + r random columns    1 or 2 points
    preprocessed trace   width                       1 or 2 points
    quotient chunks      D + r each                  1 point
    randomization        D + r, when hiding          1 point
    permutation trace    (L + 1) D + r, when L > 0   2 points
```

* p3-uni-stark's count and p3-batch-stark's count are that sum when it fits the word.
* The batch's count adds exactly the permutation trace to the single-instance count.
-/

namespace Plonky3Lean.Proofs.BatchStark.Extracted

open Aeneas Aeneas.Std CoreModels

/-- The random columns a shape appends to each hiding matrix. -/
def shapeR : p3_uni_stark.security.OpeningShape → ℕ
  | .Hiding r => r.val | _ => 0
/-- Whether a shape hides. -/
def shapeZk : p3_uni_stark.security.OpeningShape → Bool
  | .Hiding _ => true | _ => false
/-- The powers a shape charges per column and point. -/
def shapePpo : p3_uni_stark.security.OpeningShape → ℕ
  | .Circle => 2 | _ => 1

/-- The single-instance count, as p3-uni-stark writes it. -/
def uniCount (mw : ℕ) (mn : Bool) (pw : ℕ) (pn : Bool) (q D : ℕ) (o : p3_uni_stark.security.OpeningShape) : ℕ :=
  ((if mn then 2 else 1) * (mw + shapeR o) + (if pn then 2 else 1) * pw + q * (D + shapeR o) +
    (if shapeZk o then D + shapeR o else 0)) * shapePpo o

/-- p3-uni-stark's extracted count is its formula, when that fits the word. -/
theorem uni_spec (mw pw q D : Std.Usize) (mn pn : Bool) (o : p3_uni_stark.security.OpeningShape)
    (h : uniCount mw.val mn pw.val pn q.val D.val o ≤ Usize.max) :
    p3_uni_stark.security.num_batched_openings mw mn pw pn q D o ⦃ r => r.val = uniCount mw.val mn pw.val pn q.val D.val o ⦄ := by
  unfold p3_uni_stark.security.num_batched_openings uniCount at *
  cases o <;> cases mn <;> cases pn <;>
    simp only [p3_uni_stark.security.OpeningShape.num_random_codewords, p3_uni_stark.security.OpeningShape.is_zk,
      p3_uni_stark.security.OpeningShape.powers_per_opening, shapeR, shapeZk, shapePpo,
      Bool.false_eq_true, ↓reduceIte] at * <;>
    step* <;> simp only [Bool.false_eq_true, ↓reduceIte] at * <;> step*

/-- The batch instance's count, as p3-batch-stark writes it. -/
def batchCount (mw : ℕ) (mn : Bool) (pw : ℕ) (pn : Bool) (q L D : ℕ) (o : p3_uni_stark.security.OpeningShape) : ℕ :=
  uniCount mw mn pw pn q D o + (if 0 < L then 2 * ((L + 1) * D + shapeR o) * shapePpo o else 0)

/-- p3-batch-stark's extracted count is its formula, when that fits the word and the extension degree is positive. -/
theorem batch_spec (mw pw q L D : Std.Usize) (mn pn : Bool) (o : p3_uni_stark.security.OpeningShape)
    (hD : 1 ≤ D.val) (h : batchCount mw.val mn pw.val pn q.val L.val D.val o ≤ Usize.max) :
    p3_batch_stark.security.num_batched_openings mw mn pw pn q L D o ⦃ r => r.val = batchCount mw.val mn pw.val pn q.val L.val D.val o ⦄ := by
  unfold p3_batch_stark.security.num_batched_openings
  have hu : uniCount mw.val mn pw.val pn q.val D.val o ≤ Usize.max := le_trans (Nat.le_add_right _ _) h
  have hLD : L.val + 1 ≤ (L.val + 1) * D.val := Nat.le_mul_of_pos_right _ hD
  unfold batchCount at h ⊢
  step with uni_spec
  cases o <;> simp only [p3_uni_stark.security.OpeningShape.num_random_codewords,
      p3_uni_stark.security.OpeningShape.powers_per_opening, shapeR, shapePpo] at * <;>
    split_ifs at * <;> step*

/-- The committed matrices of one batch instance, as (width, points) pairs. -/
def matrices (mw : ℕ) (mn : Bool) (pw : ℕ) (pn : Bool) (q L D : ℕ) (o : p3_uni_stark.security.OpeningShape) :
    List (ℕ × ℕ) :=
  [(mw + shapeR o, if mn then 2 else 1), (pw, if pn then 2 else 1)] ++ List.replicate q (D + shapeR o, 1) ++
    (if shapeZk o then [(D + shapeR o, 1)] else []) ++
    (if 0 < L then [((L + 1) * D + shapeR o, 2)] else [])

/-- **The count is the sum over the committed matrices** of width times points, times the powers per pair. -/
theorem batchCount_eq (mw : ℕ) (mn : Bool) (pw : ℕ) (pn : Bool) (q L D : ℕ)
    (o : p3_uni_stark.security.OpeningShape) :
    batchCount mw mn pw pn q L D o =
      ((matrices mw mn pw pn q L D o).map fun m => m.1 * m.2).sum * shapePpo o := by
  unfold batchCount uniCount matrices
  cases mn <;> cases pn <;> cases shapeZk o <;> by_cases hL : 0 < L <;>
    simp [hL, List.sum_replicate] <;> ring_nf <;> simp

end Plonky3Lean.Proofs.BatchStark.Extracted
