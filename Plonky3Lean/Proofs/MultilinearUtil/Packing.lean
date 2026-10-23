module

public import Plonky3Lean.Proofs.MultilinearUtil.Kernel

@[expose] public section

/-!
# Packed polynomials

Packing groups W consecutive entries, so the lanes are the last log_2 W variables.

Folding the first variable of a packed table pairs the two halves lane by lane, as the scalar fold pairs them entry by entry.
-/

namespace Plonky3Lean.Proofs.MultilinearUtil

open Plonky3Lean.Spec.MultilinearUtil p3_multilinear_util.mirror p3_multilinear_util.poly.mirror
open Finset

theorem packN_take {α : Type _} [Zero α] (W k j : ℕ) (l : List α) (h : j ≤ k) :
    (packN W k l).take j = packN W j l := by
  rw [packN_eq, packN_eq, ← List.map_take, List.take_range, min_eq_left h]

theorem packN_drop {α : Type _} [Zero α] (W k j : ℕ) (l : List α) :
    (packN W (j + k) l).drop j = packN W k (l.drop (j * W)) := by
  rw [packN_eq, packN_eq, ← List.map_drop]
  rw [show (List.range (j + k)).drop j = (List.range k).map (j + ·) by
    refine List.ext_getElem (by simp) fun i h1 h2 => ?_
    simp]
  rw [List.map_map]
  refine List.map_congr_left fun i _ => ?_
  funext l'
  simp only [Function.comp, List.getD_eq_getElem?_getD, List.getElem?_drop]
  congr 2; ring

theorem packN_zipWith {α β γ : Type _} [Zero α] [Zero β] [Zero γ] (W k : ℕ) (g : α → β → γ)
    (hg : g 0 0 = 0) (l1 : List α) (l2 : List β) (hl : l1.length = l2.length) :
    List.zipWith (fun a b => fun i => g (a i) (b i)) (packN W k l1) (packN W k l2) =
      packN W k (List.zipWith g l1 l2) := by
  rw [packN_eq, packN_eq, packN_eq, List.zipWith_map, List.zipWith_self]
  refine List.map_congr_left fun j _ => ?_
  funext i
  simp only [List.getD_eq_getElem?_getD, List.getElem?_zipWith]
  by_cases ht : j * W + i < l1.length
  · simp [List.getElem?_eq_getElem ht, List.getElem?_eq_getElem (show j * W + i < l2.length by omega)]
  · simp [List.getElem?_eq_none (show l1.length ≤ j * W + i by omega),
      List.getElem?_eq_none (show l2.length ≤ j * W + i by omega), hg]

theorem packN_take_list {α : Type _} [Zero α] (W k : ℕ) (l : List α) :
    packN W k l = packN W k (l.take (k * W)) := by
  rw [packN_eq, packN_eq]
  refine List.map_congr_left fun j hj => ?_
  funext i
  simp only [List.mem_range] at hj
  have : j * W + i < k * W := by nlinarith [i.isLt]
  simp [List.getD_eq_getElem?_getD, this]

section Fields

variable {A B : Type _} [Field A] [Field B] [Algebra A B]

/-- pack, then unpack: the table comes back, W consecutive entries per packed value. -/
theorem pack_unpack (w : ℕ) (evals : List B) {n : ℕ} (h : evals.length = 2 ^ n) (hw : w ≤ n) :
    ∃ P, Poly.pack w evals = some P ∧ P.length = 2 ^ (n - w) ∧ Poly.unpack P = evals := by
  have hk : evals.length = 2 ^ (n - w) * 2 ^ w := by rw [h, ← pow_add]; congr 1; omega
  refine ⟨packN (2 ^ w) (2 ^ (n - w)) evals, ?_, by simp, ?_⟩
  · simp only [Poly.pack, h, Nat.log_pow (by norm_num : 1 < 2), show ¬ n < w by omega, ↓reduceIte]
    exact mapM_from_ext_slice (by positivity) evals hk
  · rw [Poly.unpack, to_ext_iter_packN (le_of_eq hk.symm), List.take_of_length_le (le_of_eq hk)]

theorem pack_panics (w : ℕ) (evals : List B) {n : ℕ} (h : evals.length = 2 ^ n) (hw : n < w) :
    Poly.pack w evals = none := by
  simp [Poly.pack, h, Nat.log_pow (by norm_num : 1 < 2), hw]

/-- fix_prefix_var_to_packed: unpacked, the scalar fold of the first variable; the lanes stay the last variables. -/
theorem fix_prefix_var_to_packed_spec (w : ℕ) (evals : List A) (r : B) {n : ℕ}
    (h : evals.length = 2 ^ n) (hw : w < n) :
    ∃ res, Poly.fix_prefix_var_to_packed w evals r = some res ∧
      Poly.unpack res = List.zipWith (fun a0 a1 => r * algebraMap A B (a1 - a0) + algebraMap A B a0)
        (evals.take (evals.length / 2)) (evals.drop (evals.length / 2)) := by
  set W := 2 ^ w
  have hW : 0 < W := by positivity
  set K := 2 ^ (n - w)
  set half := 2 ^ (n - w - 1)
  have hK : K = half + half := by
    simp only [K, half]; rw [← two_mul, ← pow_succ']; congr 1; omega
  have hk : evals.length = K * W := by rw [h, ← pow_add]; congr 1; omega
  have hk2 : evals.length = 2 * (half * W) := by rw [hk, hK]; ring
  have hhalfW : evals.length / 2 = half * W := by omega
  have hpack : pack_slice W evals = some (packN W K evals) := by
    simp [pack_slice, hk, Nat.mul_div_cancel _ hW]
  set g : A → A → B := fun a0 a1 => r * algebraMap A B (a1 - a0) + algebraMap A B a0
  have hop : (fun a0 a1 : Fin W → A => (fun _ => r) * mulBase (fun _ => (1 : B)) (a1 - a0) +
      mulBase (fun _ => (1 : B)) a0) = fun a0 a1 => fun i => g (a0 i) (a1 i) := by
    funext a0 a1 i; simp [mulBase, g]
  have hlen1 : (evals.take (half * W)).length = half * W := by simp; omega
  have hlen2 : ((evals.drop (half * W)).take (half * W)).length = half * W := by
    simp only [List.length_take, List.length_drop]; omega
  have hres : List.zipWith (fun a0 a1 : Fin W → A => (fun _ => r) * mulBase (fun _ => (1 : B)) (a1 - a0) +
      mulBase (fun _ => (1 : B)) a0) ((packN W K evals).take ((packN W K evals).length / 2))
      ((packN W K evals).drop ((packN W K evals).length / 2)) =
      packN W half (List.zipWith g (evals.take (half * W)) ((evals.drop (half * W)).take (half * W))) := by
    rw [hop, length_packN, show K / 2 = half by rw [hK]; omega,
      packN_take W K half evals ((Nat.le_add_right half half).trans (le_of_eq hK.symm)), hK,
      packN_drop W half half evals, packN_take_list W half evals,
      packN_take_list W half (evals.drop (half * W))]
    exact packN_zipWith W half g (by simp [g]) _ _ (by rw [hlen1, hlen2])
  have hL : (List.zipWith g (evals.take (half * W)) ((evals.drop (half * W)).take (half * W))).length =
      half * W := by simp only [List.length_zipWith, hlen1, hlen2, min_self]
  refine ⟨packN W half (List.zipWith g (evals.take (half * W)) ((evals.drop (half * W)).take (half * W))),
    ?_, ?_⟩
  · simp only [Poly.fix_prefix_var_to_packed, h, Nat.log_pow (by norm_num : 1 < 2),
      show ¬ n ≤ w by omega, ↓reduceIte, Option.bind_eq_bind]
    rw [show pack_slice (2 ^ w) evals = some (packN W K evals) from hpack, Option.bind_some, hres,
      Poly_new_pow _ (n := n - w - 1) (by simp; rfl)]
  · rw [Poly.unpack, to_ext_iter_packN (le_of_eq hL.symm), List.take_of_length_le (le_of_eq hL),
      hhalfW, List.take_of_length_le (show (evals.drop (half * W)).length ≤ half * W by simp; omega)]

end Fields

end Plonky3Lean.Proofs.MultilinearUtil
