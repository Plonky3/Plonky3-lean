module

public import Plonky3Lean.Proofs.MultilinearUtil.PackedTable
public import P3MultilinearUtil.Mirror.SplitEq

@[expose] public section

/-!
# The factored equality table

The table of z = z_0 ++ z_1 is the outer product of the two half tables:

```text
    eq(z, j |T_1| + i) = eq(z_0, j) eq(z_1, i)
```

So evaluation dots each block of |T_1| entries against the suffix table.

It then weights each block by the prefix table.

The packed suffix table holds the same entries, W lanes at a time.
-/

namespace Plonky3Lean.Proofs.MultilinearUtil

open Plonky3Lean.Spec.MultilinearUtil p3_multilinear_util.mirror p3_multilinear_util.poly.mirror
open p3_multilinear_util.split_eq.mirror Finset

variable {F EF : Type _} [Field F] [Field EF] [Algebra F EF]

/-- The scalar entries a suffix table stores. -/
def _root_.p3_multilinear_util.split_eq.mirror.EqMaybePacked.table {W : ℕ} :
    EqMaybePacked EF W → List EF
  | .Scalar l => l
  | .Packed P => to_ext_iter P

theorem laneSum_eq {W : ℕ} (x : Fin W → EF) : laneSum x = ∑ i, x i := by
  simp [laneSum, List.sum_ofFn]

theorem laneSum_add {W : ℕ} (x y : Fin W → EF) : laneSum (x + y) = laneSum x + laneSum y := by
  simp [laneSum_eq, sum_add_distrib]

theorem laneSum_sum {W : ℕ} (l : List (Fin W → EF)) : laneSum l.sum = (l.map laneSum).sum := by
  induction l with
  | nil => simp [laneSum_eq]
  | cons a l ih => simp [laneSum_add, ih]

theorem laneSum_mulBase {W : ℕ} (p : Fin W → EF) (c : List F) (hc : W ≤ c.length) :
    laneSum (mulBase p fun i => c.getD i 0) =
      (List.zipWith (fun a x => a * algebraMap F EF x) (List.ofFn p) (c.take W)).sum := by
  rw [laneSum_eq, sum_zipWith_getD _ (by simp; omega), List.length_ofFn, Finset.sum_range]
  refine sum_congr rfl fun i _ => ?_
  simp [mulBase, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show (i : ℕ) < c.length by
    omega)]

/-- The packed dot product is the dot product of the unpacked entries. -/
theorem packed_dot {W : ℕ} (P : List (Fin W → EF)) (c : List F) (hc : P.length * W ≤ c.length) :
    laneSum (List.zipWith mulBase P (packN W P.length c)).sum =
      (List.zipWith (fun a x => a * algebraMap F EF x) (to_ext_iter P) c).sum := by
  induction P generalizing c with
  | nil => simp [laneSum_eq, to_ext_iter]
  | cons p P ih =>
    simp only [List.length_cons, Nat.succ_mul] at hc
    rw [List.length_cons, packN, List.zipWith_cons_cons, List.sum_cons, laneSum_add,
      ih _ (by simp; omega), laneSum_mulBase p c (by omega), to_ext_iter_cons]
    conv_rhs => rw [← List.take_append_drop W c]
    rw [List.zipWith_append (by simp; omega), List.sum_append]

/-- The packed dot product over the extension is the dot product of the unpacked entries. -/
theorem packed_dot_ext {W : ℕ} (P : List (Fin W → EF)) (c : List EF) (hc : c.length = P.length * W) :
    laneSum (List.zipWith (· * ·) (packN W P.length c) P).sum =
      (List.zipWith (· * ·) (to_ext_iter P) c).sum := by
  have := packed_dot (F := EF) P c (le_of_eq hc.symm)
  simp only [Algebra.algebraMap_self, RingHom.id_apply] at this
  rw [← this]
  congr 2
  exact List.zipWith_comm_of_comm (fun a b => by funext i; simp [mul_comm])

theorem getD_chunkAt {α : Type _} [Zero α] {c : ℕ} (l : List α) (j : ℕ) {i : ℕ} (hi : i < c) :
    (chunkAt c l j).getD i 0 = l.getD (j * c + i) 0 := by
  simp [chunkAt, List.getD_eq_getElem?_getD, hi, Nat.add_comm]

theorem packN_eq {α : Type _} [Zero α] (W k : ℕ) (c : List α) :
    packN W k c = (List.range k).map fun j (i : Fin W) => c.getD (j * W + i) 0 := by
  induction k generalizing c with
  | zero => rfl
  | succ k ih =>
    rw [packN, ih, List.range_succ_eq_map, List.map_cons, List.map_map]
    congr 1
    · funext i; simp
    · refine List.map_congr_left fun j _ => ?_
      funext i
      simp only [Function.comp, List.getD_eq_getElem?_getD, List.getElem?_drop]
      congr 2; rw [Nat.succ_mul]; omega

theorem mapM_from_ext_slice {W : ℕ} (hW : 0 < W) (c : List EF) {k : ℕ} (hc : c.length = k * W) :
    (chunks W c).mapM (from_ext_slice W) = some (packN W k c) := by
  rw [chunks_eq hW hc, packN_eq, List.mapM_map, mapM_some _ _ (fun j (i : Fin W) =>
    c.getD (j * W + i) 0) fun j hj => by
    simp only [List.mem_range] at hj
    simp only [Function.comp, from_ext_slice, length_chunkAt hc hj, ↓reduceIte, Option.some.injEq]
    funext i
    exact getD_chunkAt c j i.isLt]

/-! ## The suffix table -/

theorem dot_with_base_eq {W : ℕ} (hW : 0 < W) (e : EqMaybePacked EF W) (chunk : List F)
    (h : chunk.length = e.table.length) :
    e.dot_with_base chunk =
      some (List.zipWith (fun a x => a * algebraMap F EF x) e.table chunk).sum := by
  cases e with
  | Scalar l => rfl
  | Packed P =>
    simp only [EqMaybePacked.table, length_to_ext_iter] at h
    simp only [EqMaybePacked.dot_with_base, pack_slice, h, Nat.mul_mod_left, ↓reduceIte,
      Nat.mul_div_cancel _ hW, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
      EqMaybePacked.table]
    rw [packed_dot P chunk (by omega)]

theorem dot_with_ext_eq {W : ℕ} (hW : 0 < W) (e : EqMaybePacked EF W) (chunk : List EF)
    (h : chunk.length = e.table.length) :
    e.dot_with_ext chunk = some (List.zipWith (· * ·) e.table chunk).sum := by
  cases e with
  | Scalar l => rfl
  | Packed P =>
    simp only [EqMaybePacked.table, length_to_ext_iter] at h
    simp only [EqMaybePacked.dot_with_ext, mapM_from_ext_slice hW chunk h, Option.bind_eq_bind,
      Option.bind_some, Option.pure_def, EqMaybePacked.table]
    rw [packed_dot_ext P chunk h]

omit [Field EF] [Algebra F EF] in
theorem num_scalar_evals_eq {W : ℕ} (e : EqMaybePacked EF W) : e.num_scalar_evals = e.table.length := by
  cases e <;> simp [EqMaybePacked.num_scalar_evals, EqMaybePacked.table, length_to_ext_iter]

section New

variable [DecidableEq EF]

/-- The packed constructor builds a suffix table that stores eq(z_1, i) at i. -/
theorem new_packed_table (w T : ℕ) (z : List EF) (h : z.length < 64) :
    ∃ e, EqMaybePacked.new_packed w T z = some e ∧ e.table = eqTable z := by
  by_cases hw : w ≤ z.length
  · refine ⟨.Packed (aTable (packedSeed w z 1) (z.take (z.length - w))), ?_, by
      rw [EqMaybePacked.table, unpack_new_packed w z 1 hw, sTable_one]⟩
    simp only [EqMaybePacked.new_packed, hw, ↓reduceIte,
      new_packed_from_point_eq_aTable w T z 1 one_ne_zero hw, Option.bind_eq_bind,
      Option.bind_some, Option.pure_def]
  · refine ⟨.Scalar (eqTable z), ?_, rfl⟩
    simp [EqMaybePacked.new_packed, hw, EqMaybePacked.new_unpacked, new_from_point_eq w T z 1 h,
      sTable_one]

/-- The constructor splits the point at n / 2.

It stores the scaled prefix table and the suffix table. -/
theorem split_new_packed (w T : ℕ) (point : List EF) (s : EF) (h : point.length < 64) :
    ∃ e, SplitEq.new_packed w T point s = some ⟨sTable s (point.take (point.length / 2)), e⟩ ∧
      e.table = eqTable (point.drop (point.length / 2)) := by
  obtain ⟨e, he, ht⟩ := new_packed_table w T (point.drop (point.length / 2)) (by simp; omega)
  refine ⟨e, ?_, ht⟩
  simp only [SplitEq.new_packed, he, Option.bind_eq_bind, Option.bind_some, Option.pure_def]
  rw [new_from_point_eq w T _ s (by simp; omega)]
  rfl

end New

/-! ## Evaluation -/

theorem sum_range_mul' {M : Type _} [AddCommMonoid M] (a b : ℕ) (f : ℕ → M) :
    ∑ x ∈ range (a * b), f x = ∑ j ∈ range a, ∑ i ∈ range b, f (j * b + i) := by
  induction a with
  | zero => simp
  | succ a ih => rw [Nat.succ_mul, sum_range_add, ih, sum_range_succ]

theorem sum_zip_map {α β : Type _} (L : List α) (M : List β) (dL : α) (dM : β) (g : α × β → EF)
    (h : L.length = M.length) :
    ((L.zip M).map g).sum = ∑ j ∈ range L.length, g (L.getD j dL, M.getD j dM) := by
  induction L generalizing M with
  | nil => simp
  | cons x L ih =>
    obtain ⟨y, M, rfl⟩ := List.exists_cons_of_length_eq_add_one h.symm
    simp [ih M (by simpa using h), sum_range_succ', add_comm]

theorem num_variables_split {W : ℕ} (s : EF) (z0 : List EF) (e : EqMaybePacked EF W) (z1 : List EF)
    (ht : e.table = eqTable z1) : (SplitEq.mk (sTable s z0) e).num_variables = z0.length + z1.length := by
  simp [SplitEq.num_variables, EqMaybePacked.num_variables, num_scalar_evals_eq, ht, Nat.log_pow]

/-- The factored evaluation is scale times the extension at the point.

A constant is the exception: it is returned unscaled. -/
theorem split_eval_base [DecidableEq EF] (w T : ℕ) (point : List EF) (s : EF) (h : point.length < 64)
    (poly : List F) (hp : poly.length = 2 ^ point.length) (hs : s = 1 ∨ 0 < point.length) :
    (SplitEq.new_packed w T point s).bind (fun se => se.eval_base poly) =
      some (s * mle (poly.map (algebraMap F EF)) point) := by
  obtain ⟨e, he, ht⟩ := split_new_packed w T point s h
  rw [he, Option.bind_some]
  set z0 := point.take (point.length / 2) with hz0
  set z1 := point.drop (point.length / 2) with hz1
  have hsplit : point = z0 ++ z1 := (List.take_append_drop _ _).symm
  have hn : point.length = z0.length + z1.length := by rw [hz0, hz1]; simp; omega
  have hnv := num_variables_split s z0 e z1 ht
  have hcs : e.num_scalar_evals = 2 ^ z1.length := by rw [num_scalar_evals_eq, ht]; simp
  have hlog : ¬ (Nat.log 2 poly.length ≠ (SplitEq.mk (sTable s z0) e).num_variables) := by
    rw [hnv, hp, Nat.log_pow (by norm_num), hn]; simp
  have hpl : poly.length = 2 ^ z0.length * 2 ^ z1.length := by rw [hp, hn, pow_add]
  simp only [SplitEq.eval_base, hlog, ↓reduceIte]
  by_cases h1 : poly.length = 1
  · have h0 : point.length = 0 := by
      rw [hp] at h1; exact Nat.pow_eq_one.mp h1 |>.resolve_left (by norm_num)
    obtain rfl : s = 1 := hs.resolve_right (by omega)
    obtain rfl := List.eq_nil_of_length_eq_zero h0
    simp [h1, List.getD_eq_getElem?_getD]
  · have hW : 0 < 2 ^ w := by positivity
    have hch : chunks e.num_scalar_evals poly =
        (List.range (2 ^ z0.length)).map (chunkAt (2 ^ z1.length) poly) := by
      rw [hcs]; exact chunks_eq (by positivity) hpl
    have hlen0 : ¬ ((chunks e.num_scalar_evals poly).length ≠ (sTable s z0).length) := by
      rw [hch]; simp
    simp only [h1, ↓reduceIte, hlen0, Option.bind_eq_bind]
    rw [mapM_some _ _ (fun cw : List F × EF =>
        (List.zipWith (fun a x => a * algebraMap F EF x) e.table cw.1).sum * cw.2) fun cw hcw => by
      have hmem := (List.of_mem_zip hcw).1
      rw [hch] at hmem
      obtain ⟨j, hj, hcj⟩ := List.mem_map.mp hmem
      simp only [List.mem_range] at hj
      rw [dot_with_base_eq hW e _ (by rw [ht, ← hcj, length_chunkAt hpl hj]; simp)]
      rfl]
    simp only [Option.bind_some, Option.pure_def, Option.some.injEq]
    rw [sum_zip_map _ _ [] 0 _ (by rw [hch]; simp), hch, mle_eq_sum, List.length_map,
      List.length_range]
    conv_rhs => rw [hsplit]
    rw [List.length_append, pow_add, sum_range_mul', mul_sum]
    refine sum_congr rfl fun j hj => ?_
    simp only [mem_range] at hj
    rw [getD_map_range _ _ hj]
    rw [sum_zipWith_getD _ (by rw [ht, length_chunkAt hpl hj]; simp), ht, length_eqTable, sum_mul,
      mul_sum]
    refine sum_congr rfl fun i hi => ?_
    simp only [mem_range] at hi
    rw [getD_chunkAt _ _ hi, sTable, getD_map_mul,
      getD_eqTable_append _ _ hj hi, getD_map_ringHom]
    ring

/-- The factored evaluation over the extension, with the same exception. -/
theorem split_eval_ext [DecidableEq EF] (w T : ℕ) (point : List EF) (s : EF) (h : point.length < 64)
    (poly : List EF) (hp : poly.length = 2 ^ point.length) (hs : s = 1 ∨ 0 < point.length) :
    (SplitEq.new_packed w T point s).bind (fun se => se.eval_ext poly) =
      some (s * mle poly point) := by
  obtain ⟨e, he, ht⟩ := split_new_packed w T point s h
  rw [he, Option.bind_some]
  set z0 := point.take (point.length / 2) with hz0
  set z1 := point.drop (point.length / 2) with hz1
  have hsplit : point = z0 ++ z1 := (List.take_append_drop _ _).symm
  have hn : point.length = z0.length + z1.length := by rw [hz0, hz1]; simp; omega
  have hnv := num_variables_split s z0 e z1 ht
  have hcs : e.num_scalar_evals = 2 ^ z1.length := by rw [num_scalar_evals_eq, ht]; simp
  have hlog : ¬ (Nat.log 2 poly.length ≠ (SplitEq.mk (sTable s z0) e).num_variables) := by
    rw [hnv, hp, Nat.log_pow (by norm_num), hn]; simp
  have hpl : poly.length = 2 ^ z0.length * 2 ^ z1.length := by rw [hp, hn, pow_add]
  simp only [SplitEq.eval_ext, hlog, ↓reduceIte]
  by_cases h1 : poly.length = 1
  · have h0 : point.length = 0 := by
      rw [hp] at h1; exact Nat.pow_eq_one.mp h1 |>.resolve_left (by norm_num)
    obtain rfl : s = 1 := hs.resolve_right (by omega)
    obtain rfl := List.eq_nil_of_length_eq_zero h0
    simp [h1, List.getD_eq_getElem?_getD]
  · have hW : 0 < 2 ^ w := by positivity
    have hch : chunks e.num_scalar_evals poly =
        (List.range (2 ^ z0.length)).map (chunkAt (2 ^ z1.length) poly) := by
      rw [hcs]; exact chunks_eq (by positivity) hpl
    have hlen0 : ¬ ((chunks e.num_scalar_evals poly).length ≠ (sTable s z0).length) := by
      rw [hch]; simp
    simp only [h1, ↓reduceIte, hlen0, Option.bind_eq_bind]
    rw [mapM_some _ _ (fun cw : List EF × EF =>
        (List.zipWith (· * ·) e.table cw.1).sum * cw.2) fun cw hcw => by
      have hmem := (List.of_mem_zip hcw).1
      rw [hch] at hmem
      obtain ⟨j, hj, hcj⟩ := List.mem_map.mp hmem
      simp only [List.mem_range] at hj
      rw [dot_with_ext_eq hW e _ (by rw [ht, ← hcj, length_chunkAt hpl hj]; simp)]
      rfl]
    simp only [Option.bind_some, Option.pure_def, Option.some.injEq]
    rw [sum_zip_map _ _ [] 0 _ (by rw [hch]; simp), hch, mle_eq_sum, List.length_map,
      List.length_range]
    conv_rhs => rw [hsplit]
    rw [List.length_append, pow_add, sum_range_mul', mul_sum]
    refine sum_congr rfl fun j hj => ?_
    simp only [mem_range] at hj
    rw [getD_map_range _ _ hj]
    rw [sum_zipWith_getD _ (by rw [ht, length_chunkAt hpl hj]; simp), ht, length_eqTable, sum_mul,
      mul_sum]
    refine sum_congr rfl fun i hi => ?_
    simp only [mem_range] at hi
    rw [getD_chunkAt _ _ hi, sTable, getD_map_mul,
      getD_eqTable_append _ _ hj hi]
    ring

/-- A constant polynomial is returned unscaled, whatever scale the table carries. -/
theorem split_eval_base_constant [DecidableEq EF] (w T : ℕ) (s : EF) (c : F) :
    (SplitEq.new_packed w T [] s).bind (fun se => se.eval_base [c]) = some (algebraMap F EF c) := by
  obtain ⟨e, he, ht⟩ := split_new_packed w T [] s (by simp)
  rw [he, Option.bind_some]
  have hnv := num_variables_split s ([] : List EF) e [] (by simpa using ht)
  simp [SplitEq.eval_base, hnv]

/-- A polynomial with other variables than the table panics. -/
theorem split_eval_base_panics [DecidableEq EF] (w T : ℕ) (point : List EF) (s : EF)
    (h : point.length < 64) (poly : List F) {n : ℕ} (hp : poly.length = 2 ^ n) (hn : n ≠ point.length) :
    (SplitEq.new_packed w T point s).bind (fun se => se.eval_base poly) = none := by
  obtain ⟨e, he, ht⟩ := split_new_packed w T point s h
  rw [he, Option.bind_some]
  have hnv := num_variables_split s (point.take (point.length / 2)) e _ ht
  have hlen : (point.take (point.length / 2)).length + (point.drop (point.length / 2)).length =
      point.length := by simp; omega
  have hc : Nat.log 2 poly.length ≠ (SplitEq.mk (sTable s (point.take (point.length / 2))) e).num_variables := by
    rw [hnv, hlen, hp, Nat.log_pow (by norm_num)]; exact hn
  unfold SplitEq.eval_base
  rw [ite_of_pos hc]
  rfl

/-- Evaluation at a base-field point is the extension at the point.

This holds for every threshold, width and thread count. -/
theorem poly_eval_base_eq [DecidableEq EF] (thr w T : ℕ) (poly : List F) (point : List EF)
    (h : point.length < 64) (hp : poly.length = 2 ^ point.length) :
    Poly.eval_base thr w T poly point = some (mle (poly.map (algebraMap F EF)) point) := by
  unfold Poly.eval_base
  split
  · exact eval_rec_eq point poly hp
  · rename_i hthr
    have := split_eval_base w T point 1 h poly hp (Or.inl rfl)
    rw [one_mul] at this
    exact this

/-- Below the threshold, a shorter point of at most four coordinates is padded with zeros in front. -/
theorem poly_eval_base_short [DecidableEq EF] (thr w T : ℕ) (poly : List F) (point : List EF) {n : ℕ}
    (hk : point.length ≤ 4) (hthr : point.length < thr) (hn : point.length ≤ n)
    (hp : poly.length = 2 ^ n) :
    Poly.eval_base thr w T poly point = some (mle (poly.map (algebraMap F EF))
      (List.replicate (n - point.length) 0 ++ point)) := by
  rw [Poly.eval_base, ite_of_pos hthr, eval_rec_short poly point hk hn hp]

/-- From the threshold on, a point with another number of variables panics. -/
theorem poly_eval_base_mismatch_panics [DecidableEq EF] (thr w T : ℕ) (poly : List F)
    (point : List EF) {n : ℕ} (hthr : thr ≤ point.length) (h : point.length < 64)
    (hp : poly.length = 2 ^ n) (hn : n ≠ point.length) : Poly.eval_base thr w T poly point = none := by
  rw [Poly.eval_base, ite_of_neg (by omega)]
  exact split_eval_base_panics w T point 1 h poly hp hn

/-- Evaluation at an extension point is the extension at the point.

This holds for every threshold, width and thread count. -/
theorem poly_eval_ext_eq [DecidableEq EF] (thr w T : ℕ) (poly point : List EF)
    (h : point.length < 64) (hp : poly.length = 2 ^ point.length) :
    Poly.eval_ext thr w T poly point = some (mle poly point) := by
  unfold Poly.eval_ext
  split
  · rw [eval_rec_eq point poly hp]; simp
  · have := split_eval_ext w T point 1 h poly hp (Or.inl rfl)
    rw [one_mul] at this
    exact this

end Plonky3Lean.Proofs.MultilinearUtil