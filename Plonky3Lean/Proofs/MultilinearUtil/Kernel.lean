module

public import Plonky3Lean.Proofs.MultilinearUtil.SplitEq

@[expose] public section

/-!
# The packed suffix kernel

The kernel splits each packed extension weight into its basis coefficients, one packed base value each.

It dots every coefficient row against the polynomial block, four entries per delayed reduction, and reassembles:

```text
    sum_i w_i x_i = sum_k ( sum_i coeff_k(w_i) x_i ) b_k
```

The reassembly is exact because a basis expansion recovers each weight.
-/

namespace Plonky3Lean.Proofs.MultilinearUtil

open Plonky3Lean.Spec.MultilinearUtil p3_multilinear_util.mirror p3_multilinear_util.poly.mirror
open p3_multilinear_util.split_eq.mirror Finset

variable {F EF : Type _} [Field F] [Field EF] [Algebra F EF]

theorem foldl_groups {ι M : Type _} [AddCommMonoid M] (h : ι → ℕ → M) (z : ι → M) (m : ℕ) (k : ι) :
    (List.range m).foldl (fun (a : ι → M) g k => a k + ((List.range 4).map fun c => h k (4 * g + c)).sum)
      z k = z k + ∑ i ∈ range (4 * m), h k i := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [List.range_succ (n := m), List.foldl_append, List.foldl_cons, List.foldl_nil, ih,
      show 4 * (m + 1) = 4 * m + 4 by ring, sum_range_add]
    simp [List.range_succ, Finset.sum_range_succ, add_assoc]

theorem foldl_tail {ι M : Type _} [AddCommMonoid M] (h : ι → ℕ → M) (G : ℕ) (z : ι → M) (r : ℕ)
    (k : ι) : (List.range r).foldl (fun (a : ι → M) t k => a k + h k (G + t)) z k =
      z k + ∑ t ∈ range r, h k (G + t) := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [List.range_succ (n := r), List.foldl_append, List.foldl_cons, List.foldl_nil, ih,
      sum_range_succ, add_assoc]

/-- The per-coefficient dot product is the full dot product, whatever the grouping. -/
theorem packed_basis_dot_eq {W D : ℕ} (cs : Fin D → List (Fin W → F)) (rhs : List (Fin W → F))
    (k : Fin D) :
    packed_basis_dot cs rhs k = ∑ i ∈ range rhs.length, (cs k).getD i 0 * rhs.getD i 0 := by
  have hG : 4 * (rhs.length / 4) + (rhs.length - 4 * (rhs.length / 4)) = rhs.length := by omega
  unfold packed_basis_dot
  rw [foldl_tail (fun k i => (cs k).getD i 0 * rhs.getD i 0), foldl_groups
    (fun k i => (cs k).getD i 0 * rhs.getD i 0), zero_add, ← sum_range_add, hG]

/-- Reassembling the per-coefficient dot products recovers the lane-wise dot product. -/
theorem fromCoeffs_basis_dot {D W : ℕ} (b : Module.Basis (Fin D) F EF) (eq1 : List (Fin W → EF))
    (piece : List (Fin W → F)) (h : piece.length = eq1.length) (l : Fin W) :
    fromCoeffs b (packed_basis_dot (fun k => eq1.map fun v => coeffOf b v k) piece) l =
      ∑ i ∈ range eq1.length, eq1.getD i 0 l * algebraMap F EF (piece.getD i 0 l) := by
  simp only [fromCoeffs, packed_basis_dot_eq, Finset.sum_apply, Pi.mul_apply, h, Finset.sum_smul]
  rw [Finset.sum_comm]
  refine sum_congr rfl fun i hi => ?_
  simp only [mem_range] at hi
  have hmap : ∀ k, ((eq1.map fun v => coeffOf b v k).getD i 0) l = b.repr (eq1.getD i 0 l) k :=
    fun k => by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, coeffOf]
  simp only [hmap, mul_comm _ (piece.getD i 0 l), mul_smul]
  rw [← Finset.smul_sum, b.sum_repr, Algebra.smul_def, mul_comm]

theorem laneSum_mul_splat {W : ℕ} (x : Fin W → EF) (c : EF) : laneSum (x * fun _ => c) = laneSum x * c := by
  simp [laneSum_eq, Finset.sum_mul]

theorem laneSum_zipWith_mulBase {W : ℕ} (eq1 : List (Fin W → EF)) (piece : List (Fin W → F))
    (h : piece.length = eq1.length) :
    laneSum (List.zipWith mulBase eq1 piece).sum =
      ∑ l : Fin W, ∑ i ∈ range eq1.length, eq1.getD i 0 l * algebraMap F EF (piece.getD i 0 l) := by
  rw [laneSum_eq]
  refine sum_congr rfl fun l _ => ?_
  rw [sum_eq_sum_getD, Finset.sum_apply]
  simp only [List.length_zipWith, h, min_self]
  refine sum_congr rfl fun i hi => ?_
  simp only [mem_range] at hi
  simp [List.getD_eq_getElem?_getD, List.getElem?_zipWith, List.getElem?_eq_getElem hi,
    List.getElem?_eq_getElem (show i < piece.length by omega), mulBase]

theorem foldl_zipIdx_sum {α : Type _} [Zero α] {W : ℕ} (l : List α) (g : ℕ → α → (Fin W → EF)) :
    l.zipIdx.foldl (fun acc wj => acc + g wj.2 wj.1) 0 = ∑ j ∈ range l.length, g j (l.getD j 0) := by
  suffices h : ∀ (k : ℕ) (acc : Fin W → EF), (l.zipIdx k).foldl (fun acc wj => acc + g wj.2 wj.1) acc =
      acc + ∑ j ∈ range l.length, g (k + j) (l.getD j 0) by simpa using h 0 0
  induction l with
  | nil => simp
  | cons a l ih =>
    intro k acc
    rw [List.zipIdx_cons, List.foldl_cons, ih, List.length_cons, sum_range_succ', add_assoc]
    congr 1
    rw [add_comm]
    simp only [List.getD_cons_succ, List.getD_cons_zero, Nat.add_zero]
    congr 1
    exact sum_congr rfl fun x _ => by rw [show k + 1 + x = k + (x + 1) by ring]

theorem packN_block {α : Type _} [Zero α] (W : ℕ) {K n j : ℕ} (c : List α) (h : (j + 1) * n ≤ K) :
    ((packN W K c).drop (j * n)).take n = packN W n (chunkAt (n * W) c j) := by
  rw [packN_eq, packN_eq, ← List.map_drop, ← List.map_take]
  rw [show ((List.range K).drop (j * n)).take n = (List.range n).map (j * n + ·) by
    refine List.ext_getElem (by simp; rw [Nat.succ_mul] at h; omega) fun i h1 h2 => ?_
    simp]
  rw [List.map_map]
  refine List.map_congr_left fun i hi => ?_
  funext l
  simp only [Function.comp, List.mem_range] at hi ⊢
  rw [getD_chunkAt _ _ (show i * W + l < n * W by nlinarith [l.isLt])]
  congr 1; ring

/-- One block of the packed suffix kernel: the lane-wise dot product is the unpacked one. -/
theorem block_dot {W : ℕ} (eq1 : List (Fin W → EF)) (c : List F) (hc : c.length = eq1.length * W) :
    ∑ l : Fin W, ∑ i ∈ range eq1.length,
        eq1.getD i 0 l * algebraMap F EF ((packN W eq1.length c).getD i 0 l) =
      (List.zipWith (fun a x => a * algebraMap F EF x) (to_ext_iter eq1) c).sum := by
  rw [← packed_dot eq1 c (le_of_eq hc.symm), laneSum_zipWith_mulBase _ _ (by simp)]

/-- compress_hi_dot_packed: sum_j eq0[j] times the dot of block j against the unpacked suffix table, on both paths. -/
theorem compress_hi_dot_packed_eq {D W : ℕ} (hW : 0 < W) (b : Module.Basis (Fin D) F EF)
    (eq1 : List (Fin W → EF)) (chunk : List F) (eq0 : List EF)
    (h : chunk.length = eq0.length * (eq1.length * W)) :
    compress_hi_dot_packed b eq1 chunk eq0 = some (∑ j ∈ range eq0.length, eq0.getD j 0 *
      (List.zipWith (fun a x => a * algebraMap F EF x) (to_ext_iter eq1)
        (chunkAt (eq1.length * W) chunk j)).sum) := by
  have hk : chunk.length = (eq0.length * eq1.length) * W := by rw [h]; ring
  have hpack : pack_slice W chunk = some (packN W (eq0.length * eq1.length) chunk) := by
    simp [pack_slice, hk, Nat.mul_div_cancel _ hW]
  have hblock : ∀ j < eq0.length, (chunkAt (eq1.length * W) chunk j).length = eq1.length * W :=
    fun j hj => length_chunkAt (by rw [h]) hj
  have hpiece : ∀ j < eq0.length,
      ((packN W (eq0.length * eq1.length) chunk).drop (j * eq1.length)).take eq1.length =
        packN W eq1.length (chunkAt (eq1.length * W) chunk j) := fun j hj =>
    packN_block W chunk (by nlinarith)
  simp only [compress_hi_dot_packed, hpack, Option.bind_eq_bind, Option.bind_some]
  split
  · simp only [Option.pure_def, Option.some.injEq]
    rw [foldl_zipIdx_sum eq0 (fun j w => fromCoeffs b (packed_basis_dot
      (fun k => eq1.map fun v => coeffOf b v k)
      (((packN W (eq0.length * eq1.length) chunk).drop (j * eq1.length)).take eq1.length)) *
      fun _ => w)]
    rw [laneSum_eq]
    simp only [Finset.sum_apply, Pi.mul_apply]
    rw [Finset.sum_comm]
    refine sum_congr rfl fun j hj => ?_
    simp only [mem_range] at hj
    rw [hpiece j hj, ← block_dot eq1 _ (hblock j hj), mul_comm, Finset.mul_sum]
    refine sum_congr rfl fun l _ => ?_
    rw [fromCoeffs_basis_dot b eq1 _ (by simp) l, mul_comm]
  · simp only [Option.pure_def, Option.some.injEq]
    rcases Nat.eq_zero_or_pos eq1.length with h0 | hn
    · obtain rfl := List.eq_nil_of_length_eq_zero h0
      simp [chunks, packN, to_ext_iter, laneSum_eq]
    · rw [laneSum_sum, List.map_map, chunks_eq hn (show (packN W (eq0.length * eq1.length) chunk).length
        = eq0.length * eq1.length by simp), sum_zip_map _ _ [] 0 _ (by simp)]
      simp only [List.length_map, List.length_range, Function.comp]
      refine sum_congr rfl fun j hj => ?_
      simp only [mem_range] at hj
      rw [getD_map_range _ _ hj, chunkAt, hpiece j hj, laneSum_mul_splat,
        packed_dot eq1 _ (le_of_eq (hblock j hj).symm), mul_comm]

/-! ## Fixing the suffix variables -/

/-- The factored sum: prefix weights times suffix dots is scale times the extension. -/
theorem factored_sum (s : EF) (z0 z1 : List EF) (c : List F)
    (hc : c.length = 2 ^ z0.length * 2 ^ z1.length) :
    ∑ j ∈ range (2 ^ z0.length), (sTable s z0).getD j 0 *
      (List.zipWith (fun a x => a * algebraMap F EF x) (eqTable z1)
        (chunkAt (2 ^ z1.length) c j)).sum = s * mle (c.map (algebraMap F EF)) (z0 ++ z1) := by
  rw [mle_eq_sum, List.length_append, pow_add, sum_range_mul', mul_sum]
  refine sum_congr rfl fun j hj => ?_
  simp only [mem_range] at hj
  rw [sum_zipWith_getD _ (by rw [length_chunkAt hc hj]; simp), length_eqTable, mul_sum, mul_sum]
  refine sum_congr rfl fun i hi => ?_
  simp only [mem_range] at hi
  rw [getD_chunkAt _ _ hi, sTable, getD_map_mul, getD_eqTable_append _ _ hj hi, getD_map_ringHom]
  ring

/-- compress_suffix_dot: on both storages, the prefix weights times the suffix dots. -/
theorem compress_suffix_dot_eq {D W : ℕ} (hW : 0 < W) (b : Module.Basis (Fin D) F EF)
    (e : EqMaybePacked EF W) (chunk : List F) (eq0 : List EF) (he : 0 < e.table.length)
    (h : chunk.length = eq0.length * e.table.length) :
    e.compress_suffix_dot b chunk eq0 = some (∑ j ∈ range eq0.length, eq0.getD j 0 *
      (List.zipWith (fun a x => a * algebraMap F EF x) e.table
        (chunkAt e.table.length chunk j)).sum) := by
  cases e with
  | Scalar l =>
    simp only [EqMaybePacked.compress_suffix_dot, EqMaybePacked.table] at h he ⊢
    rw [chunks_eq he (by rw [h, Nat.mul_comm]), sum_zip_map _ _ [] 0 _ (by simp)]
    simp only [List.length_map, List.length_range, Option.some.injEq]
    exact sum_congr rfl fun j hj => by
      rw [getD_map_range _ _ (mem_range.mp hj), mul_comm]
  | Packed P =>
    simp only [EqMaybePacked.compress_suffix_dot, EqMaybePacked.table, length_to_ext_iter] at h he ⊢
    exact compress_hi_dot_packed_eq hW b P chunk eq0 h

/-- compress_suffix_into: entry j is scale times the extension of block j at the point, the suffix variables fixed. -/
theorem split_compress_suffix [DecidableEq EF] {D : ℕ} (w T : ℕ) (b : Module.Basis (Fin D) F EF)
    (point : List EF) (s : EF) (h : point.length < 64) (poly : List F) (out : List EF) {k : ℕ}
    (hp : poly.length = 2 ^ k * 2 ^ point.length) (ho : out.length = 2 ^ k) :
    (SplitEq.new_packed w T point s).bind (fun se => se.compress_suffix_into b out poly) =
      some ((List.range (2 ^ k)).map fun j =>
        s * mle ((chunkAt (2 ^ point.length) poly j).map (algebraMap F EF)) point) := by
  obtain ⟨e, he, ht⟩ := split_new_packed w T point s h
  rw [he, Option.bind_some]
  set z0 := point.take (point.length / 2) with hz0
  set z1 := point.drop (point.length / 2) with hz1
  have hsplit : point = z0 ++ z1 := (List.take_append_drop _ _).symm
  have hn : point.length = z0.length + z1.length := by rw [hz0, hz1]; simp; omega
  have hnv := num_variables_split s z0 e z1 ht
  rw [← hn] at hnv
  have hlog : Nat.log 2 poly.length = k + point.length := by
    rw [hp, ← pow_add, Nat.log_pow (by norm_num)]
  have hc1 : ¬ (Nat.log 2 poly.length < point.length) := by rw [hlog]; omega
  have hc2 : ¬ (out.length ≠ poly.length / 2 ^ point.length) := by
    rw [hp, Nat.mul_div_cancel _ (by positivity), ho]; simp
  simp only [SplitEq.compress_suffix_into, hnv, hc1, hc2, ↓reduceIte]
  rw [chunks_eq (by positivity) hp, mapM_some _ _ (fun oc : EF × List F =>
      s * mle (oc.2.map (algebraMap F EF)) point) fun oc hoc => by
    obtain ⟨j, hj, hcj⟩ := List.mem_map.mp (List.of_mem_zip hoc).2
    simp only [List.mem_range] at hj
    have hlen : (chunkAt (2 ^ point.length) poly j).length = 2 ^ point.length := length_chunkAt hp hj
    rw [compress_suffix_dot_eq (by positivity) b e _ _ (by rw [ht]; simp)
      (by rw [← hcj, hlen, ht, length_eqTable]; simp [hn, pow_add]), ← hcj]
    have h0 : (sTable s z0).length = 2 ^ z0.length := by simp
    have h1 : e.table.length = 2 ^ z1.length := by rw [ht]; simp
    rw [h0, h1, ht, factored_sum s z0 z1 _ (by rw [hlen, hn, pow_add]), ← hsplit]]
  congr 1
  rw [show (fun oc : EF × List F => s * mle (oc.2.map (algebraMap F EF)) point) =
    (fun c => s * mle (c.map (algebraMap F EF)) point) ∘ Prod.snd from rfl, ← List.map_map,
    List.map_snd_zip (by simp [ho]), List.map_map]
  rfl

/-! ## Accumulating the table -/

theorem getElem?_eq_some_getD {α : Type _} {l : List α} {i : ℕ} (d : α) (h : i < l.length) :
    l[i]? = some (l.getD i d) := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]

theorem accumulate_scalar_into_eq {W : ℕ} (e : EqMaybePacked EF W) (out : List EF) (weight : EF)
    (h : out.length = e.table.length) :
    e.accumulate_scalar_into out weight = List.zipWith (fun o t => o + weight * t) out e.table := by
  cases e with
  | Scalar l =>
    simp only [EqMaybePacked.accumulate_scalar_into, EqMaybePacked.table] at h ⊢
    rw [List.drop_eq_nil_of_le (by omega), List.append_nil]
  | Packed P =>
    simp only [EqMaybePacked.accumulate_scalar_into, EqMaybePacked.table] at h ⊢
    rw [List.drop_eq_nil_of_le (by omega), List.append_nil]
    exact congrArg (fun φ => List.zipWith φ _ _) (by funext o t; ring)

/-- accumulate_into: every entry gains scale times eq(point, x), with the optional extra weight. -/
theorem split_accumulate_into [DecidableEq EF] (w T : ℕ) (point : List EF) (s : EF)
    (h : point.length < 64) (out : List EF) (hout : out.length = 2 ^ point.length) (ws : Option EF) :
    (SplitEq.new_packed w T point s).bind (fun se => se.accumulate_into out ws) =
      some (List.zipWith (fun o t => o + ws.getD 1 * t) out (sTable s point)) := by
  obtain ⟨e, he, ht⟩ := split_new_packed w T point s h
  rw [he, Option.bind_some]
  set z0 := point.take (point.length / 2) with hz0
  set z1 := point.drop (point.length / 2) with hz1
  have hsplit : point = z0 ++ z1 := (List.take_append_drop _ _).symm
  have hn : point.length = z0.length + z1.length := by rw [hz0, hz1]; simp; omega
  have hnv := num_variables_split s z0 e z1 ht
  rw [← hn] at hnv
  have hpl : out.length = 2 ^ z0.length * 2 ^ z1.length := by rw [hout, hn, pow_add]
  have hcs : e.num_scalar_evals = 2 ^ z1.length := by rw [num_scalar_evals_eq, ht]; simp
  have hc : ¬ (Nat.log 2 out.length ≠ point.length ∨ out.length ≠ 2 ^ Nat.log 2 out.length) := by
    rw [hout, Nat.log_pow (by norm_num)]; simp
  simp only [SplitEq.accumulate_into, hnv, hc, ↓reduceIte, Option.some.injEq, hcs]
  rw [chunks_eq (by positivity) hpl]
  set B := 2 ^ z1.length
  set A := 2 ^ z0.length
  have hB : 0 < B := by positivity
  set L := ((List.range A).map (chunkAt B out)).zip (sTable s z0) with hL
  have hLlen : L.length = A := by simp [hL, A]
  have hmem : ∀ cw ∈ L, (e.accumulate_scalar_into cw.1 (cw.2 * ws.getD 1)).length = B := by
    intro cw hcw
    obtain ⟨j, hj, hcj⟩ := List.mem_map.mp (List.of_mem_zip hcw).1
    simp only [List.mem_range] at hj
    rw [accumulate_scalar_into_eq _ _ _ (by rw [← hcj, length_chunkAt hpl hj, ht, length_eqTable])]
    simp [← hcj, length_chunkAt hpl hj, ht]; rfl
  have hlhs : (L.flatMap fun cw => e.accumulate_scalar_into cw.1 (cw.2 * ws.getD 1)).length = A * B := by
    rw [List.length_flatMap, List.map_congr_left (g := fun _ => B) hmem, List.map_const',
      List.sum_replicate, hLlen, smul_eq_mul]
  refine ext_getD 0 (by rw [hlhs]; simp [hpl, hn, pow_add, A, B]) fun x hx => ?_
  rw [hlhs] at hx
  have hj : x / B < A := by rw [Nat.div_lt_iff_lt_mul hB]; exact hx
  have hi : x % B < B := Nat.mod_lt _ hB
  rw [← Nat.div_add_mod x B, Nat.mul_comm B,
    getD_flatMap_const L _ hmem 0 (by rw [hLlen]; exact hj) hi]
  have hL1 : L[x / B]'(by rw [hLlen]; exact hj) = (chunkAt B out (x / B), (sTable s z0).getD (x / B) 0) := by
    simp [hL, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show x / B < (sTable s z0).length
      by simpa using hj)]
  rw [hL1, accumulate_scalar_into_eq _ _ _ (by rw [length_chunkAt hpl hj, ht, length_eqTable])]
  have hidx : x / B * B + x % B < out.length := by rw [hpl]; nlinarith
  have hpt : x / B * B + x % B < (sTable s point).length := by
    have : (sTable s point).length = out.length := by simp [hout]
    omega
  have hch : x % B < (chunkAt B out (x / B)).length := by rw [length_chunkAt hpl hj]; exact hi
  have htab : x % B < e.table.length := by rw [ht]; simpa using hi
  simp only [List.getD_eq_getElem?_getD, List.getElem?_zipWith]
  rw [getElem?_eq_some_getD 0 hch, getElem?_eq_some_getD 0 htab, getElem?_eq_some_getD 0 hidx,
    getElem?_eq_some_getD 0 hpt]
  simp only [Option.getD_some]
  rw [getD_chunkAt _ _ hi, ht]
  rw [← List.getD_eq_getElem?_getD]
  conv_rhs => rw [hsplit]
  simp only [sTable, getD_map_mul]
  rw [getD_eqTable_append _ _ hj hi]
  ring

/-- materialize: the scaled equality table of the point. -/
theorem split_materialize [DecidableEq EF] (w T : ℕ) (point : List EF) (s : EF) (h : point.length < 64) :
    (SplitEq.new_packed w T point s).bind (fun se => se.materialize) = some (sTable s point) := by
  obtain ⟨e, he, ht⟩ := split_new_packed w T point s h
  have hacc := split_accumulate_into w T point s h (List.replicate (2 ^ point.length) 0) (by simp) none
  rw [he, Option.bind_some] at hacc ⊢
  have hn : (point.take (point.length / 2)).length + (point.drop (point.length / 2)).length =
      point.length := by simp; omega
  have hnv := num_variables_split s (point.take (point.length / 2)) e _ ht
  rw [hn] at hnv
  simp only [SplitEq.materialize, hnv, Poly.zero, h, ↓reduceIte, Option.bind_eq_bind, Option.bind_some,
    hacc, Option.some.injEq]
  refine List.ext_getElem (by simp) fun i h1 h2 => ?_
  simp

end Plonky3Lean.Proofs.MultilinearUtil
