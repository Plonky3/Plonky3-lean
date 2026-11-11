module

public import Plonky3Lean.Proofs.BinaryDft.Coset

@[expose] public section

/-!
# The reference transform

The forward reference evaluates sum_k d_k X_k point by point, each W_j from its product definition.

The inverse reference runs the inverse network, each twiddle from the product definition.

Both panic exactly when the height is not a power of two or the domain is wider than the level.
-/

set_option linter.unusedSectionVars false

namespace Plonky3Lean.Proofs.BinaryDft

open Finset Plonky3Lean.Spec.BinaryDft p3_binary_dft.mirror p3_binary_dft.domain.mirror
  p3_binary_dft.naive.mirror p3_binary_dft.lch.mirror p3_dft.mirror Plonky3Lean.Proofs.Dft

variable {F : Type _} [Field F] [DecidableEq F] [CharP F 2] {V : Type _} [AddCommGroup V]
  [Module F V] {L : Level F} (hL : Cantor L)

theorem list_prod_range (n : ℕ) (f : ℕ → F) : ((List.range n).map f).prod = ∏ i ∈ range n, f i := by
  induction n with
  | zero => rfl
  | succ n ih => rw [List.range_succ, List.map_append, List.prod_append, ih, prod_range_succ]; simp

theorem naive_vanishing_eq {j : ℕ} (hj : j ≤ 2 ^ L.logBits) (y : F) :
    p3_binary_dft.naive.mirror.vanishing L j y = some (Spec.BinaryDft.vanishing L.cantor j y) := by
  have hb : ∀ m < 2 ^ j, m < 2 ^ 2 ^ L.logBits := fun m hm =>
    lt_of_lt_of_le hm (Nat.pow_le_pow_right two_pos hj)
  rw [p3_binary_dft.naive.mirror.vanishing, mapM_some _ (fun m => y + point L.cantor m) _
    (fun m hm => by simp [domain_point_eq, hb m (List.mem_range.mp hm)])]
  simp [list_prod_range, Spec.BinaryDft.vanishing, CharTwo.sub_eq_add]

include hL

theorem normalised_eq {j : ℕ} (hj : j < 2 ^ L.logBits) (x : F) :
    normalised_subspace_poly L j x = some (normalized L.cantor j x) := by
  simp [normalised_subspace_poly, naive_vanishing_eq hj.le, Level.cantorBasis, hj,
    vanishing_basis_cantor hL hj, normalized]

theorem basisAt_eq {l : ℕ} (hl : l ≤ 2 ^ L.logBits) (x : F) :
    basisAt L l x = some fun i => if i < 2 ^ l then novel L.cantor l i x else 0 := by
  unfold basisAt
  rw [foldlM_some _ (fun basis j => fun i =>
      if 2 ^ j ≤ i ∧ i < 2 ^ j + 2 ^ j then basis (i - 2 ^ j) * normalized L.cantor j x else basis i)
    _ (fun a j hj => by
      simp [normalised_eq hL (show j < 2 ^ L.logBits by simp at hj; omega)])]
  congr 1
  clear hl
  induction l with
  | zero => funext i; simp [novel]
  | succ l ih =>
    rw [List.range_succ, List.foldl_append, ih]
    funext i
    simp only [List.foldl_cons, List.foldl_nil]
    by_cases h1 : 2 ^ l ≤ i ∧ i < 2 ^ l + 2 ^ l
    · obtain ⟨k, rfl⟩ : ∃ k, i = k + 2 ^ l := ⟨i - 2 ^ l, by omega⟩
      have hk : k < 2 ^ l := by omega
      simp only [h1, and_self, ↓reduceIte, Nat.add_sub_cancel, hk,
        show k + 2 ^ l < 2 ^ (l + 1) by rw [two_pow_succ']; omega]
      rw [novel_succ_high _ l hk]
    · simp only [h1, ↓reduceIte]
      by_cases h2 : i < 2 ^ l
      · simp [h2, show i < 2 ^ (l + 1) by rw [two_pow_succ']; omega, novel_succ_low _ l h2]
      · simp [h2, show ¬ i < 2 ^ (l + 1) by rw [two_pow_succ']; omega]

/-- The forward reference transform of 2^l rows is the additive NTT, with zero rows below. -/
theorem naive_ntt_eq {l : ℕ} (hl : l ≤ 2 ^ L.logBits) (shift : F) (d : ℕ → V) :
    NaiveAdditiveNtt.shifted_ntt_batch L (2 ^ l) d shift =
      some fun r => if r < 2 ^ l then ntt L.cantor l shift d r else 0 := by
  unfold NaiveAdditiveNtt.shifted_ntt_batch
  simp only [log2Strict_pow, Option.bind_eq_bind, Option.bind_some]
  rw [mapM_some _ (fun row => ntt L.cantor l shift d row) _ (fun row hrow => by
    have hr := List.mem_range.mp hrow
    rw [domain_point_eq]
    simp only [lt_of_lt_of_le hr (Nat.pow_le_pow_right two_pos hl), ↓reduceIte, Option.bind_some,
      basisAt_eq hL hl]
    simp only [Option.pure_def, Option.some.injEq, ntt, novelEval]
    exact sum_congr rfl fun i hi => by simp [mem_range.mp hi])]
  simp only [Option.pure_def, Option.bind_some, Option.some.injEq]
  funext r
  by_cases hr : r < 2 ^ l <;> simp [hr, List.getD_eq_getElem?_getD]

/-- The inverse reference transform of 2^l rows is the inverse network of the coset's twiddles. -/
theorem naive_intt_eq {l : ℕ} (hl : l ≤ 2 ^ L.logBits) (shift : F) (x : ℕ → V) :
    NaiveAdditiveNtt.shifted_intt_batch L (2 ^ l) x shift =
      some (mask l x (inetwork (twiddle L.cantor shift) l x)) := by
  unfold NaiveAdditiveNtt.shifted_intt_batch
  simp only [log2Strict_pow, Option.bind_eq_bind, Option.bind_some]
  have hstage : ∀ (a : ℕ → V), ∀ j ∈ List.range l,
      (List.range ((2 ^ l + 2 * 2 ^ j - 1) / (2 * 2 ^ j))).foldlM (fun mat block =>
          (domain_point L (block * 2 ^ (j + 1))).bind fun p =>
            (normalised_subspace_poly L j (shift + p)).bind fun t =>
              pure (blockLoop block (2 ^ j) (fun u v => (u + t • (u + v), u + v)) mat)) a =
        some (stageWith (twiddle L.cantor shift) true l j a) := by
    intro a j hj
    have hj' := List.mem_range.mp hj
    have e : 2 ^ l = 2 ^ (l - j - 1) * (2 * 2 ^ j) := by
      rw [← pow_succ', ← pow_add]; congr 1; omega
    have hcount : (2 ^ l + 2 * 2 ^ j - 1) / (2 * 2 ^ j) = 2 ^ (l - j - 1) := by
      have hpos : 0 < 2 * 2 ^ j := by positivity
      rw [e, show 2 ^ (l - j - 1) * (2 * 2 ^ j) + 2 * 2 ^ j - 1 =
        (2 * 2 ^ j - 1) + 2 ^ (l - j - 1) * (2 * 2 ^ j) by omega,
        Nat.add_mul_div_right _ _ hpos, Nat.div_eq_of_lt (by omega), zero_add]
    rw [hcount, foldlM_some _ (fun mat b => blockLoop b (2 ^ j)
      (ibutterfly (twiddle L.cantor shift j b)) mat) _ (fun mat b hb => by
        have hlt := blocks_lt (L := L) hl hj' (List.mem_range.mp hb)
        rw [domain_point_eq]
        simp only [hlt, ↓reduceIte, normalised_eq hL (show j < 2 ^ L.logBits by
          omega), Option.pure_def]
        rfl)]
    rw [← layer_stageWith _ true hj', ← pairLoop_blocks _ _ (Nat.two_pow_pos j)]
    congr 1
    simp only [pairLoop, blocks, List.foldl_flatMap, blockLoop, List.foldl_map, kop]
    rfl
  rw [foldlM_some _ _ _ hstage]
  congr 1
  conv_lhs => rw [← mask_self (l := l) x]
  rw [foldl_stageWith_mask _ true _ (fun j hj => List.mem_range.mp hj), inetwork_foldl]
  rfl

omit hL in
/-- The reference transforms panic on a height that is not a power of two. -/
theorem naive_panics_height {n : ℕ} (hn : ∀ k, n ≠ 2 ^ k) (shift : F) (d : ℕ → V) :
    NaiveAdditiveNtt.shifted_ntt_batch L n d shift = none ∧
      NaiveAdditiveNtt.shifted_intt_batch L n d shift = none := by
  simp [NaiveAdditiveNtt.shifted_ntt_batch, NaiveAdditiveNtt.shifted_intt_batch,
    log2Strict_eq_none hn]

omit hL in
/-- The forward reference transform panics on a domain wider than the level. -/
theorem naive_ntt_panics_wide {l : ℕ} (hl : 2 ^ L.logBits < l) (shift : F) (d : ℕ → V) :
    NaiveAdditiveNtt.shifted_ntt_batch L (2 ^ l) d shift = none := by
  unfold NaiveAdditiveNtt.shifted_ntt_batch
  simp only [log2Strict_pow, Option.bind_eq_bind, Option.bind_some]
  rw [mapM_none _ (a := 2 ^ 2 ^ L.logBits) (List.mem_range.mpr
    (Nat.pow_lt_pow_right (by norm_num) hl)) (by simp [domain_point_eq])]
  rfl

end Plonky3Lean.Proofs.BinaryDft
