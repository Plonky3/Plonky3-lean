module

public import Plonky3Lean.Proofs.MultilinearUtil.EqBatchCommon
public import Plonky3Lean.Proofs.MultilinearUtil.Next
public import P3MultilinearUtil.Poly

@[expose] public section

/-!
# Multilinear polynomials: tables, folds and evaluation

The equality table of a point is the batched table of that single point.

Fixing a variable of a table interpolates its two halves, or its adjacent pairs, along the challenge.
-/

namespace Plonky3Lean.Proofs.MultilinearUtil

open Plonky3Lean.Spec.MultilinearUtil p3_multilinear_util.mirror p3_multilinear_util.eq_batch.mirror
open p3_multilinear_util.poly.mirror Finset

variable {F : Type _} [Field F]

/-! ## The equality tables -/

/-- The batched table of a single point with weight s is its equality table scaled by s. -/
theorem bt_single (point : List F) (s : F) :
    bt (point.map fun z => [z]) [s] = sTable s point := by
  refine ext_getD 0 (by simp) fun x hx => ?_
  rw [getD_bt _ _ (fun r hr => by simp at hr; obtain ⟨z, _, rfl⟩ := hr; simp)]
  simp only [List.length_singleton, range_one, sum_singleton, List.getD_cons_zero, col,
    List.map_map, Function.comp_def, List.getD_cons_zero, List.map_id', Algebra.algebraMap_self,
    RingHom.id_apply, sTable]
  rw [getD_map_mul]

/-- new_from_point: the equality table of the point scaled by s, for every width and thread count. -/
theorem new_from_point_eq (w T : ℕ) (point : List F) (s : F) (h : point.length < 64) :
    Poly.new_from_point w T point s = some (sTable s point) := by
  by_cases h0 : point.length = 0
  · obtain rfl := List.eq_nil_of_length_eq_zero h0
    simp [Poly.new_from_point, sTable]
  · simp only [Poly.new_from_point, h0, ↓reduceIte, h]
    rw [eval_eq_batch_eq w T false one_pos _ _ _ rfl (fun r hr => by
      simp at hr; obtain ⟨z, _, rfl⟩ := hr; simp) (by simp), bt_single]
    rfl

theorem new_from_point_panics (w T : ℕ) (point : List F) (s : F) (h : 64 ≤ point.length) :
    Poly.new_from_point w T point s = none := by
  simp [Poly.new_from_point, show point.length ≠ 0 by omega, show ¬ point.length < 64 by omega]

/-- Entry y of the successor table is entry y - 1 of the equality table, plus the last entry on the last row. -/
theorem getD_nextTable (p : List F) {y : ℕ} (hy : y < 2 ^ p.length) :
    (nextTable p).getD y 0 =
      (if 0 < y then (eqTable p).getD (y - 1) 0 else 0) +
        (if y = 2 ^ p.length - 1 then (eqTable p).getD y 0 else 0) := by
  have hN := Nat.one_le_two_pow (n := p.length)
  have he : ∀ x < 2 ^ p.length, eq (vertex p.length x) p = (eqTable p).getD x 0 := fun x hx => by
    rw [eqTable, getD_map_range _ _ hx]
  rw [nextTable, getD_map_range _ _ hy,
    show 2 ^ p.length = 2 ^ p.length - 1 + 1 by omega, sum_range_succ]
  rw [show 2 ^ p.length - 1 + 1 = 2 ^ p.length by omega]
  congr 1
  · rw [sum_congr rfl fun x hx => by
      rw [succRepeat, ite_of_pos (show x + 1 < 2 ^ p.length by simp at hx; omega)]]
    by_cases hy0 : 0 < y
    · rw [ite_of_pos hy0, sum_eq_single (y - 1) (fun x _ hx => by rw [ite_of_neg (by omega)])
        (fun h => by simp at h; omega), ite_of_pos (by omega), he _ (by omega)]
    · rw [ite_of_neg hy0]
      exact sum_eq_zero fun x _ => by rw [ite_of_neg (by omega)]
  · rw [show succRepeat p.length (2 ^ p.length - 1) = 2 ^ p.length - 1 by
      unfold succRepeat; split <;> omega]
    by_cases h1 : y = 2 ^ p.length - 1
    · subst h1; simp [he _ (show 2 ^ p.length - 1 < 2 ^ p.length by omega)]
    · simp [Ne.symm h1, h1]

/-- new_next_from_point: the successor table of the point, which repeats the last row. -/
theorem new_next_from_point_eq (w T : ℕ) (p : List F) (h : p.length < 64) :
    Poly.new_next_from_point w T p = some (nextTable p) := by
  simp only [Poly.new_next_from_point, new_from_point_eq w T p 1 h, sTable_one, Option.bind_eq_bind,
    Option.bind_some]
  have hN1 : 1 ≤ 2 ^ p.length := Nat.one_le_two_pow
  have hlen : (eqTable p).length = 2 ^ p.length := by simp
  set res := ((eqTable p).take 1 ++ (eqTable p).take ((eqTable p).length - 1)).set 0 0 with hres
  have hrl : res.length = 2 ^ p.length := by simp [hres, hlen]; omega
  have hres' : ((res.set ((eqTable p).length - 1) (res.getD ((eqTable p).length - 1) 0 +
      (eqTable p).getD ((eqTable p).length - 1) 0))) = nextTable p := by
    refine ext_getD 0 (by simp [hrl, nextTable]) fun y hy => ?_
    simp only [List.length_set, hrl] at hy
    rw [getD_nextTable p (by omega), hlen]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_set, hres, List.length_set,
      List.length_append, List.length_take, hlen]
    have hmin : min 1 (2 ^ p.length) + min (2 ^ p.length - 1) (2 ^ p.length) = 2 ^ p.length := by
      omega
    have hidx : ∀ z, 0 < z → z < 2 ^ p.length →
        ((eqTable p).take 1 ++ (eqTable p).take (2 ^ p.length - 1))[z]? = (eqTable p)[z - 1]? := by
      intro z hz0 hz
      rw [List.getElem?_append_right (by simp; omega), List.getElem?_take]
      simp only [List.length_take, hlen, show min 1 (2 ^ p.length) = 1 by omega]
      rw [ite_of_pos (by omega)]
    simp only [hmin, show 2 ^ p.length - 1 < 2 ^ p.length by omega, ↓reduceIte]
    by_cases h1 : y = 2 ^ p.length - 1 <;> by_cases h0 : y = 0
    · subst h0
      have : 2 ^ p.length = 1 := by omega
      simp [this]
    · subst h1
      simp only [↓reduceIte, show ¬ (0 = 2 ^ p.length - 1) by omega, hidx _ (by omega) hy,
        show 0 < 2 ^ p.length - 1 by omega, Option.getD_some]
    · subst h0
      simp [show ¬ (2 ^ p.length - 1 = 0) by omega, show ¬ (0 = 2 ^ p.length - 1) by omega]
    · simp only [Ne.symm h1, ↓reduceIte, Ne.symm h0, h1, hidx _ (by omega) hy,
        show 0 < y by omega, add_zero]
  rw [hres']
  simp [Poly.new, nextTable, Nat.log_pow]

/-- The extension of the successor table is the weight eval_next computes. -/
theorem mle_nextTable (p r : List F) (h : r.length = p.length) :
    mle (nextTable p) r = nextDone p r + nextOmega p r := by
  rw [nextDone_add_nextOmega, mle, h]
  have hs : ∀ x < 2 ^ p.length, succRepeat p.length x < 2 ^ p.length := fun x hx => by
    unfold succRepeat; split <;> omega
  calc ∑ y ∈ range (2 ^ p.length), eq (vertex p.length y) r * (nextTable p).getD y 0
      = ∑ y ∈ range (2 ^ p.length), ∑ x ∈ range (2 ^ p.length),
          if succRepeat p.length x = y then eq (vertex p.length x) p * eq (vertex p.length y) r
          else 0 := sum_congr rfl fun y hy => by
        rw [nextTable, getD_map_range _ _ (mem_range.mp hy), mul_sum]
        exact sum_congr rfl fun x _ => by split <;> simp [mul_comm]
    _ = ∑ x ∈ range (2 ^ p.length),
          eq (vertex p.length x) p * eq (vertex p.length (succRepeat p.length x)) r := by
        rw [sum_comm]
        exact sum_congr rfl fun x hx => by
          rw [sum_ite_eq, ite_of_pos (mem_range.mpr (hs x (mem_range.mp hx)))]

end Plonky3Lean.Proofs.MultilinearUtil
