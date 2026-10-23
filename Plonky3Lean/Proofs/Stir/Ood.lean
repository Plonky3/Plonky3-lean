module

public import Plonky3Lean.Proofs.Stir.Horner
public import Plonky3Lean.Proofs.Stir.Lists
public import Plonky3Lean.Proofs.Dft.Glue

@[expose] public section

/-!
# The out-of-domain filter

A candidate z lies in the coset s <omega> of size 2^l exactly when z^(2^l) = s^(2^l).

The filter keeps z when it lies outside every excluded coset of positive size and differs from every kept point.

A coset of size one, l = 0, is never excluded.
-/

namespace Plonky3Lean.Proofs.Stir

open Polynomial Finset p3_stir.mirror p3_stir.utils.mirror p3_dft.mirror Plonky3Lean.Proofs.Dft

set_option linter.unusedSectionVars false

variable {F EF : Type _} [Field F] [Field EF] [Algebra F EF] [DecidableEq F] [DecidableEq EF]

theorem foldl_set_if (c : ℕ → Prop) [DecidablePred c] (a : EF) :
    ∀ (t : ℕ) (zp : List EF), t ≤ zp.length → ∀ s,
      ((List.range t).foldl (fun zp s => if c s then zp.set s a else zp) zp).getD s 0 =
        if s < t ∧ c s then a else zp.getD s 0 := by
  intro t zp ht s
  have heq : (fun (zp : List EF) s => if c s then zp.set s a else zp) =
      fun zp s => zp.set s (if c s then a else zp.getD s 0) := by
    funext zp s
    split_ifs
    · rfl
    · rcases Nat.lt_or_ge s zp.length with h | h
      · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h, Option.getD_some,
          List.set_getElem_self]
      · exact (List.set_eq_of_length_le h).symm
  rw [heq, foldl_set_self (fun s x => if c s then a else x) t zp ht s]
  by_cases h1 : s < t <;> by_cases h2 : c s <;> simp [h1, h2]

/-- One step of the filter's squaring loop, as the transcription writes it. -/
def oodStep (logs : List ℕ) (M : ℕ) : List EF × EF → ℕ → List EF × EF := fun st l =>
  let z_pows := (List.range st.1.length).foldl (fun zp s =>
    if logs.getD s 0 = l then zp.set s st.2 else zp) st.1
  (z_pows, if l < M then st.2 ^ 2 else st.2)

/-- The squaring loop of the filter: after the steps l < t, slot s holds z^(2^(log_s)) for log_s < t. -/
theorem ood_loop (logs : List ℕ) (M : ℕ) (z : EF) :
    ∀ t ≤ M + 1,
      let st := (List.range t).foldl (oodStep logs M) (List.replicate logs.length 1, z)
      st.1.length = logs.length ∧ st.2 = z ^ 2 ^ min t M ∧
        ∀ s < logs.length, st.1.getD s 0 = if logs.getD s 0 < t then z ^ 2 ^ logs.getD s 0 else 1 := by
  intro t
  induction t with
  | zero =>
    intro _
    refine ⟨by simp, by simp, fun s hs => ?_⟩
    simp [List.getD_eq_getElem?_getD, hs]
  | succ t ih =>
    intro ht
    obtain ⟨h1, h2, h3⟩ := ih (by omega)
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    generalize (List.range t).foldl (oodStep logs M) (List.replicate logs.length 1, z) = S
      at h1 h2 h3 ⊢
    obtain ⟨zp, acc⟩ := S
    simp only [oodStep] at h1 h2 h3 ⊢
    have hlen : ∀ m, ((List.range m).foldl (fun zp' s =>
        if logs.getD s 0 = t then zp'.set s acc else zp') zp).length = zp.length := by
      intro m; induction m with
      | zero => rfl
      | succ k ihk =>
        rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
        split_ifs <;> simp only [List.length_set, ihk]
    refine ⟨by rw [hlen, h1], ?_, fun s hs => ?_⟩
    · rw [h2]
      split_ifs with hM
      · rw [min_eq_left hM.le, min_eq_left (by omega), ← pow_mul, pow_succ]
      · rw [min_eq_right (by omega), min_eq_right (by omega)]
    · rw [foldl_set_if (fun s => logs.getD s 0 = t) acc zp.length zp le_rfl s, h3 s hs, h2,
        min_eq_left (by omega : t ≤ M)]
      have hs' : s < zp.length := h1 ▸ hs
      simp only [hs', true_and]
      generalize logs.getD s 0 = q
      split_ifs <;> first | omega | rfl | (subst_vars; rfl)

theorem mapM_inverse_pow (doms : List (F × ℕ)) :
    doms.mapM (fun (d : F × ℕ) => (p3_stir.mirror.inverse d.1).map (· ^ 2 ^ d.2)) =
      if ∀ d ∈ doms, d.1 ≠ 0 then some (doms.map fun d => d.1⁻¹ ^ 2 ^ d.2) else none := by
  induction doms with
  | nil => simp
  | cons d ds ih =>
    rw [List.mapM_cons, ih]
    by_cases hd : d.1 = 0
    · simp [p3_stir.mirror.inverse, hd]
    · have hi : p3_stir.mirror.inverse d.1 = some d.1⁻¹ := by simp [p3_stir.mirror.inverse, hd]
      rw [hi]
      by_cases hds : ∀ x ∈ ds, x.1 ≠ 0
      · have hall : ∀ x ∈ d :: ds, x.1 ≠ 0 := by simpa [hd] using hds
        rw [ite_eq_left hds, ite_eq_left hall]; rfl
      · have hall : ¬ ∀ x ∈ d :: ds, x.1 ≠ 0 := fun h' => hds fun x hx => h' x (by simp [hx])
        rw [ite_eq_right hds, ite_eq_right hall]; rfl

/-- The filter holds the shift powers, the log sizes and their maximum.

It panics exactly on a zero shift. -/
theorem oodFilter_new_eq (doms : List (F × ℕ)) :
    OodFilter.new doms = if ∀ d ∈ doms, d.1 ≠ 0 then
      some ⟨doms.map (fun d => d.1⁻¹ ^ 2 ^ d.2), doms.map (·.2), (doms.map (·.2)).foldl max 0⟩
    else none := by
  unfold OodFilter.new
  simp only [Option.bind_eq_bind]
  rw [mapM_inverse_pow]
  split_ifs <;> rfl

theorem le_foldl_max_init (l : List ℕ) (a : ℕ) : a ≤ l.foldl max a := by
  induction l generalizing a with
  | nil => exact le_rfl
  | cons y l ih => exact (le_max_left a y).trans (ih _)

theorem le_foldl_max (l : List ℕ) (a : ℕ) : ∀ x ∈ l, x ≤ l.foldl max a := by
  induction l generalizing a with
  | nil => simp
  | cons y l ih =>
    intro x hx
    rcases List.mem_cons.1 hx with rfl | hx
    · exact (le_max_right a x).trans (le_foldl_max_init l _)
    · exact ih _ x hx

theorem oodFilter_accepts_unfold (f : OodFilter F) (z : EF) (kept : List EF) :
    f.accepts z kept = ((List.range f.log_sizes.length).all (fun s => f.log_sizes.getD s 0 = 0 ||
      ((List.range (f.max_log_size + 1)).foldl (oodStep f.log_sizes f.max_log_size)
        (List.replicate f.log_sizes.length 1, z)).1.getD s 0 * algebraMap F EF (f.shift_inv_pows.getD s 0) != 1) &&
      kept.all fun existing => existing != z) := rfl

/-- OodFilter::accepts: z is kept exactly when z^(2^l) differs from s^(2^l) for every excluded coset with l > 0, and z is new. -/
theorem oodFilter_accepts_eq (doms : List (F × ℕ)) (h : ∀ d ∈ doms, d.1 ≠ 0) (z : EF) (kept : List EF) :
    ∃ f, OodFilter.new doms = some f ∧
      (f.accepts z kept = true ↔ (∀ i < doms.length, (doms.getD i (1, 0)).2 = 0 ∨
          z ^ 2 ^ (doms.getD i (1, 0)).2 ≠ algebraMap F EF (doms.getD i (1, 0)).1 ^ 2 ^ (doms.getD i (1, 0)).2) ∧
        z ∉ kept) := by
  refine ⟨_, by rw [oodFilter_new_eq, ite_eq_left h], ?_⟩
  rw [oodFilter_accepts_unfold]
  set M := (doms.map (·.2)).foldl max 0
  obtain ⟨-, -, hz⟩ := ood_loop (doms.map (·.2)) M z (M + 1) le_rfl
  simp only [List.length_map, Bool.and_eq_true, List.all_eq_true, List.mem_range, Bool.or_eq_true,
    decide_eq_true_eq, bne_iff_ne, ne_eq]
  refine and_congr (forall₂_congr fun i hi => ?_)
    ⟨fun h' hz => h' z hz rfl, fun h' x hx hxz => h' (hxz ▸ hx)⟩
  have hg : doms.getD i (1, 0) = doms[i] := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
  have hl : (doms.map (·.2)).getD i 0 = (doms.getD i (1, 0)).2 := by
    rw [hg, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hi]; rfl
  have hs : (doms.map fun d => d.1⁻¹ ^ 2 ^ d.2).getD i 0 =
      (doms.getD i (1, 0)).1⁻¹ ^ 2 ^ (doms.getD i (1, 0)).2 := by
    rw [hg, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hi]; rfl
  have hle : (doms.getD i (1, 0)).2 ≤ M := by
    rw [← hl]; exact le_foldl_max _ _ _ (by rw [hl, hg]; exact List.mem_map_of_mem (List.getElem_mem hi))
  have hne : (doms.getD i (1, 0)).1 ≠ 0 := h _ (by rw [hg]; exact List.getElem_mem hi)
  simp only [List.length_map] at hz
  rw [hz i (by simpa using hi), hl, hs, ite_eq_left (by omega)]
  refine or_congr Iff.rfl (not_congr ?_)
  have hne' : algebraMap F EF (doms.getD i (1, 0)).1 ^ 2 ^ (doms.getD i (1, 0)).2 ≠ 0 :=
    pow_ne_zero _ ((_root_.map_ne_zero _).2 hne)
  rw [map_pow, map_inv₀, inv_pow, mul_inv_eq_one₀ hne']

/-- z lies in the coset s <omega> of size 2^l exactly when z^(2^l) = s^(2^l). -/
theorem pow_eq_iff_mem_coset {ω s : F} {l : ℕ} (hω : IsPrimitiveRoot ω (2 ^ l)) (hs : s ≠ 0) (z : EF) :
    z ^ 2 ^ l = algebraMap F EF s ^ 2 ^ l ↔ ∃ i < 2 ^ l, z = algebraMap F EF (s * ω ^ i) := by
  have hω' := hω.map_of_injective (algebraMap F EF).injective
  have hs' : algebraMap F EF s ≠ 0 := (_root_.map_ne_zero _).2 hs
  constructor
  · intro h
    have h1 : (z / algebraMap F EF s) ^ 2 ^ l = 1 := by
      rw [div_pow, h, div_self (pow_ne_zero _ hs')]
    obtain ⟨i, hi, he⟩ := hω'.eq_pow_of_pow_eq_one h1
    refine ⟨i, hi, ?_⟩
    rw [map_mul, map_pow, he, mul_div_cancel₀ _ hs']
  · rintro ⟨i, -, rfl⟩
    rw [map_mul, map_pow, mul_pow, ← pow_mul, mul_comm i, pow_mul, hω'.pow_eq_one, one_pow, mul_one]

end Plonky3Lean.Proofs.Stir
