module

public import Plonky3Lean.Proofs.MultilinearUtil.Fold

@[expose] public section

/-!
# Evaluation at a point

The recursive evaluation interpolates along the first variable, with the first four levels unrolled.

On a table of 2^n entries and a point of n coordinates it is the multilinear extension.

On a shorter point of at most four coordinates it reads only the first entries, so it evaluates the extension at a point padded with zeros in front.
-/

namespace Plonky3Lean.Proofs.MultilinearUtil

open Plonky3Lean.Spec.MultilinearUtil p3_multilinear_util.mirror p3_multilinear_util.poly.mirror
open Finset

variable {A B : Type _} [Field A] [Field B] [Algebra A B]

theorem mapM_getElem? {α : Type _} [Zero α] (l : List α) {n : ℕ} (h : n ≤ l.length) :
    (List.range n).mapM (l[·]?) = some (l.take n) := by
  rw [mapM_some _ _ (fun i => l.getD i 0) fun i hi => by
    simp only [List.mem_range] at hi
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show i < l.length by omega)]]
  congr 1
  refine List.ext_getElem (by simp; omega) fun i h1 h2 => ?_
  simp only [List.length_take] at h2
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show i < l.length by omega)]

theorem mle_one {K : Type _} [CommRing K] (g : List K) (x : K) :
    mle g [x] = (1 - x) * g.getD 0 0 + x * g.getD 1 0 := by
  simp [mle_cons, List.getD_eq_getElem?_getD]

theorem mapM_getElem?_none {α : Type _} (l : List α) {n : ℕ} (h : l.length < n) :
    (List.range n).mapM (l[·]?) = none := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [List.range_succ, List.mapM_append]
    by_cases hn : l.length < n
    · simp [ih hn]
    · simp [show n = l.length by omega]

/-- Up to four coordinates, the unrolled evaluation reads the first 2^k entries and interpolates them. -/
theorem eval_rec_prefix (evals : List A) : ∀ (point : List B), point.length ≤ 4 →
    2 ^ point.length ≤ evals.length →
    eval_multilinear_recursive evals point =
      some (mle ((evals.take (2 ^ point.length)).map (algebraMap A B)) point)
  | [], _, h => by
    simp only [List.length_nil, pow_zero] at h
    simp [eval_multilinear_recursive, List.getElem?_eq_getElem (show 0 < evals.length by omega),
      List.getD_eq_getElem?_getD]
  | [x], _, h => by
    simp only [List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reducePow] at h ⊢
    simp only [eval_multilinear_recursive, List.getElem?_eq_getElem (show 0 < evals.length by omega),
      List.getElem?_eq_getElem (show 1 < evals.length by omega), Option.bind_eq_bind,
      Option.bind_some, Option.pure_def, Option.some.injEq, mle_one, List.getD_eq_getElem?_getD,
      List.getElem?_map, List.getElem?_take]
    simp only [↓reduceIte, Option.getD_some, Option.map_some, map_sub,
      show (0 : ℕ) < 2 by norm_num, show (1 : ℕ) < 2 by norm_num]
    ring
  | [x0, x1], _, h => by
    simp only [List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reducePow] at h ⊢
    simp only [eval_multilinear_recursive, mapM_getElem? evals h, Option.bind_eq_bind,
      Option.bind_some, Option.pure_def, Option.some.injEq]
    simp [mle_cons, List.getD_eq_getElem?_getD, List.getElem?_drop, List.getElem?_map]
    simp (disch := omega) only [List.getElem?_eq_getElem, Option.getD_some, Option.map_some]
    ring
  | [x0, x1, x2], _, h => by
    simp only [List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reducePow] at h ⊢
    simp only [eval_multilinear_recursive, mapM_getElem? evals h, Option.bind_eq_bind,
      Option.bind_some, Option.pure_def, Option.some.injEq]
    simp [mle_cons, List.getD_eq_getElem?_getD, List.getElem?_drop, List.getElem?_map]
    simp (disch := omega) only [List.getElem?_eq_getElem, Option.getD_some, Option.map_some]
    ring
  | [x0, x1, x2, x3], _, h => by
    simp only [List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reducePow] at h ⊢
    simp only [eval_multilinear_recursive, mapM_getElem? evals h, Option.bind_eq_bind,
      Option.bind_some, Option.pure_def, Option.some.injEq]
    simp [mle_cons, List.getD_eq_getElem?_getD, List.getElem?_drop, List.getElem?_map]
    simp (disch := omega) only [List.getElem?_eq_getElem, Option.getD_some, Option.map_some]
    ring
  | _ :: _ :: _ :: _ :: _ :: _, h, _ => by simp at h; omega

theorem eval_rec_small (evals : List A) (point : List B) (hk : point.length ≤ 4)
    (h : evals.length = 2 ^ point.length) :
    eval_multilinear_recursive evals point = some (mle (evals.map (algebraMap A B)) point) := by
  rw [eval_rec_prefix evals point hk (le_of_eq h.symm), List.take_of_length_le (le_of_eq h)]

/-- On a table of 2^n entries and a point of n coordinates, the recursive evaluation is the extension. -/
theorem eval_rec_eq : ∀ (point : List B) (evals : List A), evals.length = 2 ^ point.length →
    eval_multilinear_recursive evals point = some (mle (evals.map (algebraMap A B)) point)
  | [], evals, h => eval_rec_small evals _ (by simp) h
  | [x], evals, h => eval_rec_small evals _ (by simp) h
  | [x0, x1], evals, h => eval_rec_small evals _ (by simp) h
  | [x0, x1, x2], evals, h => eval_rec_small evals _ (by simp) h
  | [x0, x1, x2, x3], evals, h => eval_rec_small evals _ (by simp) h
  | x :: x1 :: x2 :: x3 :: x4 :: sub, evals, h => by
    have hR : (x :: x1 :: x2 :: x3 :: x4 :: sub).length = (x1 :: x2 :: x3 :: x4 :: sub).length + 1 :=
      rfl
    have hh : evals.length / 2 = 2 ^ (x1 :: x2 :: x3 :: x4 :: sub).length := by
      rw [h, hR, pow_succ]; omega
    have hl : (evals.take (evals.length / 2)).length = 2 ^ (x1 :: x2 :: x3 :: x4 :: sub).length := by
      rw [List.length_take, hh, h, hR, pow_succ]; omega
    have hd : (evals.drop (evals.length / 2)).length = 2 ^ (x1 :: x2 :: x3 :: x4 :: sub).length := by
      rw [List.length_drop, hh, h, hR, pow_succ]; omega
    rw [eval_multilinear_recursive, eval_rec_eq _ _ hl, eval_rec_eq _ _ hd]
    simp only [Option.bind_eq_bind, Option.bind_some, Option.pure_def, Option.some.injEq]
    rw [mle_cons (evals.map (algebraMap A B)) x, ← List.map_take, ← List.map_drop, ← hh]
    ring

theorem mle_take {K : Type _} [CommRing K] (f r : List K) :
    mle (f.take (2 ^ r.length)) r = mle f r :=
  sum_congr rfl fun b hb => by
    simp [List.getD_eq_getElem?_getD, mem_range.mp hb]

/-- Filling the first coordinates with zeros reads the first block of the table. -/
theorem mle_zeros_prefix {K : Type _} [CommRing K] (f r : List K) (j : ℕ) :
    mle f (List.replicate j 0 ++ r) = mle f r := by
  induction j generalizing f with
  | zero => simp
  | succ j ih =>
    rw [List.replicate_succ, List.cons_append, mle_cons, ih, ← mle_take (f.take _), List.take_take,
      min_eq_left (Nat.pow_le_pow_right two_pos (by simp)), mle_take]
    ring

/-- A release build on a point with fewer coordinates, at most four, evaluates the extension at the point padded with zeros in front. -/
theorem eval_rec_short (evals : List A) (point : List B) {n : ℕ} (hk : point.length ≤ 4)
    (hn : point.length ≤ n) (h : evals.length = 2 ^ n) :
    eval_multilinear_recursive evals point = some (mle (evals.map (algebraMap A B))
      (List.replicate (n - point.length) 0 ++ point)) := by
  rw [eval_rec_prefix evals point hk (h ▸ Nat.pow_le_pow_right two_pos hn), mle_zeros_prefix,
    List.map_take, mle_take]

/-- A point with more coordinates than the table has variables, at most four, panics. -/
theorem eval_rec_long_panics (evals : List A) (point : List B) (hk : point.length ≤ 4)
    (h : evals.length < 2 ^ point.length) : eval_multilinear_recursive evals point = none := by
  match point, hk, h with
  | [], _, h =>
    simp only [List.length_nil, pow_zero, Nat.lt_one_iff, List.length_eq_zero_iff] at h
    subst h; rfl
  | [x], _, h =>
    simp only [List.length_singleton, pow_one] at h
    simp [eval_multilinear_recursive, List.getElem?_eq_none (show evals.length ≤ 1 by omega)]
  | [x0, x1], _, h =>
    simp only [eval_multilinear_recursive, mapM_getElem?_none evals (by simpa using h)]
    rfl
  | [x0, x1, x2], _, h =>
    simp only [eval_multilinear_recursive, mapM_getElem?_none evals (by simpa using h)]
    rfl
  | [x0, x1, x2, x3], _, h =>
    simp only [eval_multilinear_recursive, mapM_getElem?_none evals (by simpa using h)]
    rfl
  | _ :: _ :: _ :: _ :: _ :: _, hk, _ => simp at hk; omega

end Plonky3Lean.Proofs.MultilinearUtil