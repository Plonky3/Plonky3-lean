module

public import Plonky3Lean.Proofs.Stir.DegCor
public import Plonky3Lean.Proofs.Stir.Horner
public import Plonky3Lean.Proofs.Stir.Lists
public import Plonky3Lean.Proofs.Dft.Glue
public import P3Stir

@[expose] public section

/-!
# Combine on a coset

At every point x_p = s g^p of the coset, with step s_p = r x_p, the output is

```text
    sum_i r_i v_i[p] sum_{t <= gap_i} s_p^t
```

which is Definition 4.11's Combine at x_p when r_i and gap_i are its coefficients and degree gaps.

The code divides 1 - s_p^(gap+1) by 1 - s_p, and gives the one lane with s_p = 1 its closed form gap + 1.
-/

namespace Plonky3Lean.Proofs.Stir

open Polynomial Finset p3_stir.mirror p3_stir.utils.mirror p3_dft.mirror Plonky3Lean.Proofs.Dft
open Plonky3Lean.Spec.Stir p3_stir.pcs.plan.mirror

set_option linter.unusedSectionVars false

section Sweep

variable {K : Type _} [Field K]

theorem iterate_mul_eq (a r : K) (k : ℕ) :
    List.iterate (· * r) a k = (List.range k).map fun o => a * r ^ o := by
  refine List.ext_getElem (by simp) fun i h1 h2 => ?_
  rw [List.getElem_iterate, List.getElem_map, List.getElem_range]
  induction i with
  | zero => simp
  | succ i ih => rw [Function.iterate_succ_apply', ih (by simp at h1 ⊢; omega) (by simp at h2 ⊢; omega),
      pow_succ, mul_assoc]

theorem flatMap_range'_chunks (c n : ℕ) : ∀ m : ℕ,
    (List.range m).flatMap (fun i => List.range' (i * c) (min c (n - i * c))) =
      List.range (min n (m * c)) := by
  intro m
  induction m with
  | zero => simp
  | succ m ih =>
    rw [List.range_succ, List.flatMap_append, ih, List.flatMap_singleton]
    by_cases h : n ≤ m * c
    · rw [show n - m * c = 0 by omega, _root_.min_zero, List.range'_zero, List.append_nil,
        min_eq_left h, min_eq_left (by nlinarith)]
    · rw [min_eq_right (by omega : m * c ≤ n), List.range'_eq_map_range, ← List.range_add]
      congr 1
      rw [Nat.succ_mul]
      omega

/-- A chunked sweep is the geometric sequence s r^p, p < n. -/
theorem chunkSweep_eq {c : ℕ} (hc : 0 < c) (n : ℕ) (s r : K) :
    chunkSweep c n s r = (List.range n).map fun p => s * r ^ p := by
  have hm : n ≤ (n + c - 1) / c * c := by
    have := Nat.lt_div_mul_add (a := n + c - 1) hc; omega
  unfold chunkSweep
  have key : ∀ i, List.iterate (· * r) (s * r ^ (i * c)) (min c (n - i * c)) =
      (List.range' (i * c) (min c (n - i * c))).map fun p => s * r ^ p := fun i => by
    rw [iterate_mul_eq, List.range'_eq_map_range, List.map_map]
    exact List.map_congr_left fun o _ => by simp [pow_add, mul_assoc]
  simp only [key, ← List.map_flatMap, flatMap_range'_chunks, min_eq_left hm]

theorem getD_chunkSweep {c : ℕ} (hc : 0 < c) (n : ℕ) (s r : K) {p : ℕ} (hp : p < n) :
    (chunkSweep c n s r).getD p 0 = s * r ^ p := by
  rw [chunkSweep_eq hc, getD_map_range _ _ hp]

end Sweep

section TwoFields

variable {F EF : Type _} [Field F] [Field EF] [Algebra F EF] [DecidableEq F] [DecidableEq EF]

/-- The group loop of combine_on_coset adds r_i v_i[p] (1 - s_p^(gap_i + 1)) at every p, and panics on a group of the wrong length. -/
theorem combine_groups_foldlM {c : ℕ} (hc : 0 < c) (n : ℕ) (g : F) (step_start : EF) :
    ∀ (groups : List (EF × ℕ × List EF)) (acc : List EF), acc.length = n →
      groups.foldlM (fun (result : List EF) (grp : EF × ℕ × List EF) =>
        if grp.2.2.length ≠ n then none
        else some ((List.range n).map fun p =>
            result.getD p 0 + grp.2.2.getD p 0 * (grp.1 -
              (chunkSweep c n (grp.1 * step_start ^ (grp.2.1 + 1)) (algebraMap F EF (g ^ (grp.2.1 + 1)))).getD p 0))) acc =
      if ∀ grp ∈ groups, grp.2.2.length = n then
        some ((List.range n).map fun p => acc.getD p 0 + (groups.map fun grp =>
          grp.2.2.getD p 0 * (grp.1 - grp.1 * (step_start * algebraMap F EF g ^ p) ^ (grp.2.1 + 1))).sum)
      else none := by
  intro groups
  induction groups with
  | nil =>
    intro acc hacc
    simp only [List.foldlM_nil, List.not_mem_nil, IsEmpty.forall_iff, implies_true, ↓reduceIte,
      List.map_nil, List.sum_nil, add_zero]
    congr 1
    refine List.ext_getElem (by simp [hacc]) fun i h1 h2 => ?_
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1]
  | cons grp groups ih =>
    intro acc hacc
    obtain ⟨r_i, gap, values⟩ := grp
    rw [List.foldlM_cons]
    by_cases hv : values.length = n
    · simp only [hv, ne_eq, not_true_eq_false, ↓reduceIte, Option.bind_eq_bind, Option.bind_some]
      rw [ih _ (by simp)]
      simp only [List.mem_cons, forall_eq_or_imp, hv, true_and, List.map_cons, List.sum_cons]
      split_ifs
      · congr 1
        refine List.map_congr_left fun p hp => ?_
        rw [getD_map_range _ _ (List.mem_range.1 hp), getD_chunkSweep hc _ _ _ (List.mem_range.1 hp)]
        simp only [map_pow, mul_pow, ← pow_mul]
        ring_nf
      · rfl
    · simp [hv]

/-- Adding a term per group at one slot. -/
theorem foldl_set_add {α : Type _} (q : ℕ) (t : α → EF) :
    ∀ (gs : List α) (L : List EF), q < L.length →
      gs.foldl (fun res grp => res.set q (res.getD q 0 + t grp)) L =
        L.set q (L.getD q 0 + (gs.map t).sum) := by
  intro gs
  induction gs with
  | nil =>
    intro L hq
    rw [List.foldl_nil, List.map_nil, List.sum_nil, add_zero, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem hq, Option.getD_some, List.set_getElem_self]
  | cons a gs ih =>
    intro L hq
    rw [List.foldl_cons, ih _ (by simpa using hq), List.set_set]
    simp [hq, add_assoc]

/-- The batched sweep at x_p = s g^p: sum_i r_i v_i[p] sum_{t <= gap_i} (x_p r)^t, the lane with x_p r = 1 included, for every chunk size. -/
theorem combine_on_coset_eq {c : ℕ} (hc : 0 < c) (G : Gen F) (hG : GenValid G) {log_domain : ℕ}
    (hl : log_domain ≤ G.adicity) (groups : List (EF × ℕ × List EF)) (r_comb : EF) (shift : F)
    (hgroups : ∀ grp ∈ groups, grp.2.2.length = 2 ^ log_domain) :
    combine_on_coset c G groups r_comb shift log_domain =
      some ((List.range (2 ^ log_domain)).map fun p =>
        let x := algebraMap F EF shift * algebraMap F EF (G.gen log_domain) ^ p
        (groups.map fun grp => grp.1 * grp.2.2.getD p 0 *
          ∑ t ∈ range (grp.2.1 + 1), (x * r_comb) ^ t).sum) := by
  set n := 2 ^ log_domain
  set g := G.gen log_domain
  set ι := algebraMap F EF
  have hg : IsPrimitiveRoot (ι g) n := (hG _ hl).map_of_injective ι.injective
  set step : ℕ → EF := fun p => r_comb * ι shift * ι g ^ p
  have hstep_inj : ∀ p q, p < n → q < n → step p = 1 → step q = 1 → p = q := by
    intro p q hp hq h1 h2
    have h0 : r_comb * ι shift ≠ 0 := fun h => by simp [step, h] at h1
    exact hg.pow_inj hp hq (mul_left_cancel₀ h0 (h1.trans h2.symm))
  unfold combine_on_coset
  simp only [gen_get_of_le G hl, Option.bind_eq_bind, Option.bind_some]
  rw [combine_groups_foldlM hc n g (r_comb * ι shift) groups _ (by simp [n])]
  simp only [eq_true hgroups, ↓reduceIte, Option.bind_some, chunkSweep_eq hc,
    List.map_map, Function.comp_def]
  have hD : ((List.range n).map fun p => 1 - r_comb * ι shift * ι g ^ p) =
      (List.range n).map fun p => 1 - step p := rfl
  have hR : ∀ m p, (List.replicate m (0 : EF)).getD p 0 = 0 := fun m p => by
    simp [List.getD_eq_getElem?_getD, List.getElem?_replicate]; split_ifs <;> rfl
  set R : ℕ → EF := fun p => (groups.map fun grp =>
    grp.2.2.getD p 0 * (grp.1 - grp.1 * (step p) ^ (grp.2.1 + 1))).sum
  have hgeom : ∀ p, ∀ grp : EF × ℕ × List EF, step p ≠ 1 →
      grp.1 * grp.2.2.getD p 0 * ∑ t ∈ range (grp.2.1 + 1), (ι shift * ι g ^ p * r_comb) ^ t =
        grp.2.2.getD p 0 * (grp.1 - grp.1 * step p ^ (grp.2.1 + 1)) * (1 - step p)⁻¹ := by
    intro p grp hs
    rw [geom_sum_closed, show ι shift * ι g ^ p * r_comb = step p by simp only [step]; ring]
    simp only [hs, ↓reduceIte]
    have : 1 - step p ≠ 0 := sub_ne_zero.2 (Ne.symm hs)
    field_simp
  simp only [hR, zero_add]
  change ((batchInv (match List.findIdx? (fun x => decide (x = 0)) ((List.range n).map fun p => 1 - step p) with
      | some p => ((List.range n).map fun p => 1 - step p).set p 1
      | none => (List.range n).map fun p => 1 - step p)).bind fun a =>
    match List.findIdx? (fun x => decide (x = 0)) ((List.range n).map fun p => 1 - step p) with
    | some p => some (List.foldl (fun result grp => result.set p (result.getD p 0 +
        grp.1 * grp.2.2.getD p 0 * ((grp.2.1 + 1 : ℕ) : EF))) (List.zipWith (· * ·) ((List.range n).map R) a) groups)
    | none => some (List.zipWith (· * ·) ((List.range n).map R) a)) = _
  set D := (List.range n).map fun p => 1 - step p with hDdef
  have hDlen : D.length = n := by simp [D]
  have hDget : ∀ p (hp : p < D.length), D[p] = 1 - step p := fun p hp => by simp [D]
  have hsum : ∀ p, R p * (1 - step p)⁻¹ = (groups.map fun grp =>
      grp.2.2.getD p 0 * (grp.1 - grp.1 * step p ^ (grp.2.1 + 1)) * (1 - step p)⁻¹).sum := fun p => by
    simp only [R, List.sum_map_mul_right]
  cases hfind : List.findIdx? (fun x => decide (x = 0)) D with
  | none =>
    have hnz : ∀ p < n, step p ≠ 1 := by
      intro p hp h
      have := List.findIdx?_eq_none_iff.1 hfind D[p] (List.getElem_mem (by omega))
      simp [hDget, h] at this
    have h0 : (0 : EF) ∉ D := by
      simp only [D, List.mem_map, List.mem_range, not_exists, not_and]
      exact fun p hp h => hnz p hp (sub_eq_zero.1 h).symm
    simp only [batchInv, h0, ↓reduceIte, Option.bind_some]
    congr 1
    refine List.ext_getElem (by simp [hDlen]) fun p h1 h2 => ?_
    simp only [List.length_map, List.length_range] at h2
    simp only [List.getElem_zipWith, List.getElem_map, List.getElem_range, hDget, hsum]
    congr 1
    exact List.map_congr_left fun grp _ => (hgeom p grp (hnz p h2)).symm
  | some p0 =>
    obtain ⟨hp0, hD0, -⟩ := List.findIdx?_eq_some_iff_getElem.1 hfind
    have hp0n : p0 < n := hDlen ▸ hp0
    have hs0 : step p0 = 1 := by
      have := hD0; simp only [decide_eq_true_eq, hDget] at this
      rw [sub_eq_zero] at this; exact this.symm
    have hnz : ∀ q < n, q ≠ p0 → step q ≠ 1 := fun q hq hne h => hne (hstep_inj q p0 hq hp0n h hs0)
    have h0 : (0 : EF) ∉ D.set p0 1 := by
      intro hmem
      obtain ⟨q, hq, hqe⟩ := List.getElem_of_mem hmem
      rw [List.length_set] at hq
      rw [List.getElem_set] at hqe
      split_ifs at hqe with hqp
      · exact one_ne_zero hqe
      · rw [hDget] at hqe
        exact hnz q (hDlen ▸ hq) (Ne.symm hqp) (sub_eq_zero.1 hqe).symm
    simp only [batchInv, h0, ↓reduceIte, Option.bind_some]
    congr 1
    rw [foldl_set_add p0 _ groups _ (by simp [hDlen, hp0n])]
    refine List.ext_getElem (by simp [hDlen]) fun q h1 h2 => ?_
    simp only [List.length_map, List.length_range] at h2
    rw [List.getElem_set]
    split_ifs with hq
    · subst hq
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simp [hDlen, h2]),
        Option.getD_some]
      simp only [List.getElem_zipWith, List.getElem_map, List.getElem_set, ↓reduceIte,
        List.getElem_range, inv_one, mul_one]
      have hx : ι shift * ι g ^ p0 * r_comb = 1 := by rw [← hs0]; simp only [step]; ring
      have hR0 : R p0 = 0 := by simp [R, hs0]
      rw [hR0, zero_add]
      simp only [hx, one_pow, sum_const, card_range, nsmul_eq_mul, mul_one]
    · simp only [List.getElem_zipWith, List.getElem_map, List.getElem_set, hq, ↓reduceIte, hDget,
        List.getElem_range]
      rw [hsum]
      congr 1
      exact List.map_congr_left fun grp _ => (hgeom q grp (hnz q h2 (Ne.symm hq))).symm


end TwoFields

section Coefficients

variable {K : Type _} [Field K]

/-- The loop of combine_coefficients: the running exponent is the number of classes plus their gaps. -/
theorem combine_coefficients_fold (r : K) (L : ℕ) (logs : List ℕ) (hlogs : ∀ l ∈ logs, l ≤ L) :
    logs.foldlM (fun (st : List (K × ℕ) × ℕ) log_d =>
      if 2 ^ log_d ≤ 2 ^ L then
        some (st.1 ++ [(r ^ st.2, 2 ^ L - 2 ^ log_d)], st.2 + (1 + (2 ^ L - 2 ^ log_d)))
      else none) ([], 0) =
    some ((List.range logs.length).map (fun i => (ri (2 ^ L) (logs.map (2 ^ ·)) r i,
        2 ^ L - 2 ^ logs.getD i 0)),
      logs.length + ∑ j ∈ range logs.length, (2 ^ L - 2 ^ logs.getD j 0)) := by
  induction logs using List.reverseRecOn with
  | nil => simp
  | append_singleton ls l ih =>
    have hl : l ≤ L := hlogs l (by simp)
    rw [List.foldlM_append, ih fun x hx => hlogs x (by simp [hx])]
    simp only [Option.bind_eq_bind, Option.bind_some, List.foldlM_cons, List.foldlM_nil,
      Nat.pow_le_pow_right two_pos hl, ↓reduceIte, List.length_append, List.length_singleton]
    have hget : ∀ j < ls.length, (ls ++ [l]).getD j 0 = ls.getD j 0 := fun j hj => by
      simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hj]
    have hlast : (ls ++ [l]).getD ls.length 0 = l := by simp [List.getD_eq_getElem?_getD]
    have hmap : ∀ j < ls.length, (List.map (fun x => 2 ^ x) ls ++ [2 ^ l]).getD j 0 =
        (List.map (fun x => 2 ^ x) ls).getD j 0 := fun j hj => by
      rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
        List.getElem?_append_left (by simpa using hj)]
    have hsum : ∀ m ≤ ls.length, ∑ j ∈ range m, (2 ^ L - 2 ^ (ls ++ [l]).getD j 0) =
        ∑ j ∈ range m, (2 ^ L - 2 ^ ls.getD j 0) := fun m hm =>
      sum_congr rfl fun j hj => by rw [hget j (by have := mem_range.1 hj; omega)]
    simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq]
    refine ⟨?_, ?_⟩
    · rw [List.range_succ, List.map_append]
      congr 1
      · refine List.map_congr_left fun i hi => ?_
        have hi' := List.mem_range.1 hi
        simp only [ri, List.map_append, List.map_cons, List.map_nil, hget i hi', Prod.mk.injEq,
          and_true]
        congr 2
        refine sum_congr rfl fun j hj => ?_
        rw [hmap j (by have := mem_range.1 hj; omega)]
      · simp only [List.map_cons, List.map_nil, ri, hlast, List.cons.injEq, Prod.mk.injEq, and_true]
        congr 1
        refine congrArg (ls.length + ·) (sum_congr rfl fun j hj => ?_)
        have hj' := mem_range.1 hj
        rw [List.map_append, List.map_singleton, hmap j hj']
        simp [List.getD_eq_getElem?_getD, hj']
    · rw [sum_range_succ, hlast, hsum _ le_rfl]; ring

/-- The Combine coefficients are Definition 4.11's r_i and the gaps d* - d_i, for class degrees d_i = 2^(log d_i) <= d* = 2^L. -/
theorem combine_coefficients_eq (r : K) (L : ℕ) (logs : List ℕ) (hlogs : ∀ l ∈ logs, l ≤ L) :
    combine_coefficients r L logs = some ((List.range logs.length).map fun i =>
      (ri (2 ^ L) (logs.map (2 ^ ·)) r i, 2 ^ L - 2 ^ logs.getD i 0)) := by
  simp only [combine_coefficients, combine_coefficients_fold r L logs hlogs, Option.map_some]

/-- The Combine coefficients panic on a class degree above d*. -/
theorem combine_coefficients_panics (r : K) (L : ℕ) (logs : List ℕ) (h : ∃ l ∈ logs, L < l) :
    combine_coefficients r L logs = none := by
  suffices hf : ∀ logs : List ℕ, (∃ l ∈ logs, L < l) →
      logs.foldlM (fun (st : List (K × ℕ) × ℕ) log_d =>
        if 2 ^ log_d ≤ 2 ^ L then
          some (st.1 ++ [(r ^ st.2, 2 ^ L - 2 ^ log_d)], st.2 + (1 + (2 ^ L - 2 ^ log_d)))
        else none) ([], 0) = none by
    simp only [combine_coefficients, hf logs h, Option.map_none]
  intro logs
  induction logs using List.reverseRecOn with
  | nil => simp
  | append_singleton ls l ih =>
    intro ⟨x, hx, hLx⟩
    rw [List.foldlM_append]
    rcases List.mem_append.1 hx with hx | hx
    · rw [ih ⟨x, hx, hLx⟩]; rfl
    · rw [List.mem_singleton.1 hx] at hLx
      have : ¬ 2 ^ l ≤ 2 ^ L := not_le.2 (Nat.pow_lt_pow_right (by norm_num) hLx)
      cases (ls.foldlM (fun (st : List (K × ℕ) × ℕ) log_d =>
        if 2 ^ log_d ≤ 2 ^ L then
          some (st.1 ++ [(r ^ st.2, 2 ^ L - 2 ^ log_d)], st.2 + (1 + (2 ^ L - 2 ^ log_d)))
        else none) ([], 0)) <;> simp [this]

end Coefficients

end Plonky3Lean.Proofs.Stir
