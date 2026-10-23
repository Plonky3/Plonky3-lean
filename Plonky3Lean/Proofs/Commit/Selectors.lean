module

public import Plonky3Lean.Proofs.Commit.Domain

@[expose] public section

/-!
# p3-commit: the selectors on a coset

The prover evaluates the selectors of a subgroup H of order n on a coset t H' of order N >= n.

Write x_m = t omega'^m for the coset's points.

The vectors are the selectors at a point, evaluated at every x_m:

```text
    is_first_row[m]   = (x_m^n - 1) / (x_m - 1)
    is_last_row[m]    = (x_m^n - 1) / (x_m - omega^(-1))
    is_transition[m]  = x_m - omega^(-1)
    inv_vanishing[m]  = 1 / (x_m^n - 1)
```

They are defined exactly when t H' misses H, that is when t^N != 1.
-/

open Polynomial Finset
open p3_commit.domain.mirror p3_field.coset.mirror p3_dft.mirror
open Plonky3Lean.Spec.Commit Plonky3Lean.Proofs.Dft

namespace Plonky3Lean.Proofs.Commit

set_option linter.unusedSectionVars false

variable {K : Type _} [Field K] [DecidableEq K] (G : Gen K)

theorem zipCycle_map (a : List K) (N : ℕ) (f : ℕ → K) :
    zipCycle a ((List.range N).map f) = (List.range N).map fun m => a.getD (m % a.length) 0 * f m := by
  apply List.ext_getElem
  · simp [zipCycle]
  · intro m h1 h2
    simp [zipCycle, List.getElem_zipIdx]

theorem batchInv_map (N : ℕ) (f : ℕ → K) (hf : ∀ m < N, f m ≠ 0) :
    batchInv ((List.range N).map f) = some ((List.range N).map fun m => (f m)⁻¹) := by
  unfold batchInv
  split_ifs with h
  · simp
  · exact absurd (by simpa using hf) h

theorem batchInv_map_none (N : ℕ) (f : ℕ → K) {m : ℕ} (hm : m < N) (hf : f m = 0) :
    batchInv ((List.range N).map f) = none := by
  unfold batchInv
  split_ifs with h
  · exact absurd hf (h _ (List.mem_map.mpr ⟨m, List.mem_range.mpr hm, rfl⟩))
  · rfl

/-- The coset's points, as the coset iterator yields them. -/
theorem iter_eq (c : Coset G) :
    c.iter = (List.range (2 ^ c.log_size)).map fun m => c.shift * c.subgroup_generator ^ m := rfl

/-- If t^N != 1, every power of a subgroup H of order n <= N avoids t H'. -/
theorem point_ne_pow (hV : GenValid G) {c coset : Coset G} (hle : c.log_size ≤ coset.log_size)
    (hdisj : coset.shift ^ 2 ^ coset.log_size ≠ 1) (m i : ℕ) :
    coset.shift * coset.subgroup_generator ^ m ≠ c.subgroup_generator ^ i := by
  intro h
  apply hdisj
  have hc : (c.subgroup_generator ^ i) ^ 2 ^ coset.log_size = 1 := by
    rw [show coset.log_size = c.log_size + (coset.log_size - c.log_size) by omega, pow_add,
      ← pow_mul, mul_comm i, pow_mul, pow_mul, (prim G hV c).pow_eq_one, one_pow, one_pow]
  have hm : (coset.subgroup_generator ^ m) ^ 2 ^ coset.log_size = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, (prim G hV coset).pow_eq_one, one_pow]
  rw [← h, mul_pow, hm, mul_one] at hc
  exact hc

/-- The point's n-th power is s^n omega_r^m, for omega_r of order N / n. -/
theorem point_pow (hN : GenNested G) {c coset : Coset G} (hle : c.log_size ≤ coset.log_size) (m : ℕ) :
    (coset.shift * coset.subgroup_generator ^ m) ^ 2 ^ c.log_size =
      coset.shift ^ 2 ^ c.log_size * G.gen (coset.log_size - c.log_size) ^ m := by
  rw [mul_pow, gen_sub G hN coset.log_size_le hle, ← pow_mul, ← pow_mul, mul_comm m]
  rfl

/-- On a coset missing the subgroup, the selector vectors are the selectors at each point. -/
theorem selectors_on_coset_eq (hV : GenValid G) (hN : GenNested G) {c coset : Coset G}
    (h1 : c.shift = 1) (hle : c.log_size ≤ coset.log_size)
    (hdisj : coset.shift ^ 2 ^ coset.log_size ≠ 1) :
    Coset.selectors_on_coset G c coset = some
      ⟨(List.range (2 ^ coset.log_size)).map fun m =>
          ((coset.shift * coset.subgroup_generator ^ m) ^ 2 ^ c.log_size - 1) *
            (coset.shift * coset.subgroup_generator ^ m - 1)⁻¹,
       (List.range (2 ^ coset.log_size)).map fun m =>
          ((coset.shift * coset.subgroup_generator ^ m) ^ 2 ^ c.log_size - 1) *
            (coset.shift * coset.subgroup_generator ^ m - c.subgroup_generator⁻¹)⁻¹,
       (List.range (2 ^ coset.log_size)).map fun m =>
          coset.shift * coset.subgroup_generator ^ m - c.subgroup_generator⁻¹,
       (List.range (2 ^ coset.log_size)).map fun m =>
          ((coset.shift * coset.subgroup_generator ^ m) ^ 2 ^ c.log_size - 1)⁻¹⟩ := by
  have hne1 : coset.shift ≠ 1 := fun h => hdisj (by simp [h])
  have hr : coset.log_size - c.log_size ≤ G.adicity := by have := coset.log_size_le; omega
  have hωr : IsPrimitiveRoot (G.gen (coset.log_size - c.log_size)) (2 ^ (coset.log_size - c.log_size)) :=
    hV _ hr
  have hpow1 : ∀ m, (coset.shift * coset.subgroup_generator ^ m) ^ 2 ^ c.log_size ≠ 1 := fun m h => by
    apply hdisj
    have := congrArg (· ^ 2 ^ (coset.log_size - c.log_size)) h
    simp only [one_pow, ← pow_mul, ← pow_add, Nat.add_sub_cancel' hle] at this
    rw [mul_pow, ← pow_mul, mul_comm m, pow_mul, (prim G hV coset).pow_eq_one, one_pow, mul_one] at this
    exact this
  have hev : ∀ m, coset.shift ^ 2 ^ c.log_size * G.gen (coset.log_size - c.log_size) ^ m - 1 =
      (coset.shift * coset.subgroup_generator ^ m) ^ 2 ^ c.log_size - 1 := fun m => by
    rw [point_pow G hN hle]
  simp only [Coset.selectors_on_coset, h1, ne_eq, not_true_eq_false, ite_false, hne1,
    not_lt.mpr hle, gen_get_of_le G hr, iter_eq, powersList, List.map_map, Function.comp_def,
    hev, Option.bind_eq_bind, Option.bind_some]
  have hcyc : ∀ m, (coset.shift * coset.subgroup_generator ^ (m % 2 ^ (coset.log_size - c.log_size)))
      ^ 2 ^ c.log_size = (coset.shift * coset.subgroup_generator ^ m) ^ 2 ^ c.log_size := fun m => by
    rw [point_pow G hN hle, point_pow G hN hle, hωr.eq_orderOf, pow_mod_orderOf]
  have hR : 0 < 2 ^ (coset.log_size - c.log_size) := by positivity
  have hget : ∀ (f : ℕ → K) m, ((List.range (2 ^ (coset.log_size - c.log_size))).map f).getD
      (m % ((List.range (2 ^ (coset.log_size - c.log_size))).map f).length) 0 =
      f (m % 2 ^ (coset.log_size - c.log_size)) := fun f m => by
    simp [List.getD_eq_getElem?_getD, Nat.mod_lt _ hR]
  have hlast : c.subgroup_generator ^ (2 ^ c.log_size - 1) = c.subgroup_generator⁻¹ :=
    pow_pred_eq_inv (prim G hV c)
  have b0 := batchInv_map (2 ^ coset.log_size) (fun m => coset.shift * coset.subgroup_generator ^ m - 1)
    fun m _ => sub_ne_zero.mpr (by simpa using point_ne_pow G hV hle hdisj m 0)
  have bl := batchInv_map (2 ^ coset.log_size)
    (fun m => coset.shift * coset.subgroup_generator ^ m - c.subgroup_generator⁻¹)
    fun m _ => sub_ne_zero.mpr (hlast ▸ point_ne_pow G hV hle hdisj m _)
  simp only [p3_commit.domain.mirror.inv, gen_ne_zero G hV c, ite_false, Option.bind_some, pow_zero,
    size_eq, hlast, batchInv_map _ _ fun m _ => sub_ne_zero.mpr (hpow1 m), Option.pure_def, hget,
    hcyc, b0, bl, zipCycle_map]

/-- The selectors on a coset panic exactly when the subgroup's shift is not one, the coset is smaller, or the coset meets the subgroup (t^N = 1). -/
theorem selectors_on_coset_none (hV : GenValid G) (hN : GenNested G) (c coset : Coset G) :
    Coset.selectors_on_coset G c coset = none ↔
      c.shift ≠ 1 ∨ coset.log_size < c.log_size ∨ coset.shift ^ 2 ^ coset.log_size = 1 := by
  constructor
  · intro h
    by_contra hc
    push Not at hc
    rw [selectors_on_coset_eq G hV hN hc.1 hc.2.1 hc.2.2] at h
    exact Option.some_ne_none _ h
  · rintro (h | h | h)
    · simp [Coset.selectors_on_coset, h]
    · simp [Coset.selectors_on_coset, h]
    · by_cases h1 : c.shift = 1
      · by_cases hle : c.log_size ≤ coset.log_size
        · by_cases ht : coset.shift = 1
          · simp [Coset.selectors_on_coset, ht]
          have hω' := prim G hV coset
          obtain ⟨j, hj, hjt⟩ := hω'.eq_pow_of_pow_eq_one h
          have hN0 : 0 < 2 ^ coset.log_size := by positivity
          have hm : (2 ^ coset.log_size - j) % 2 ^ coset.log_size < 2 ^ coset.log_size :=
            Nat.mod_lt _ hN0
          have hx1 : coset.shift * coset.subgroup_generator ^ ((2 ^ coset.log_size - j) %
              2 ^ coset.log_size) - 1 = 0 := by
            rw [← hjt, ← pow_add, ← pow_mod_orderOf, ← hω'.eq_orderOf, Nat.add_mod_mod,
              Nat.add_sub_cancel' hj.le, Nat.mod_self, pow_zero, sub_self]
          have hr : coset.log_size - c.log_size ≤ G.adicity := by have := coset.log_size_le; omega
          simp only [Coset.selectors_on_coset, h1, ne_eq, not_true_eq_false, ite_false, ht,
            not_lt.mpr hle, gen_get_of_le G hr, iter_eq, p3_commit.domain.mirror.inv,
            gen_ne_zero G hV c, Option.bind_eq_bind, Option.bind_some, pow_zero, List.map_map,
            Function.comp_def,
            batchInv_map_none _ (fun m => coset.shift * coset.subgroup_generator ^ m - 1) hm hx1,
            Option.bind_none]
        · simp [Coset.selectors_on_coset, h1, not_le.mp hle]
      · simp [Coset.selectors_on_coset, h1]

/-- Each entry of the selector vectors is the corresponding selector at that coset point. -/
theorem selectors_on_coset_at_point (hV : GenValid G) (hN : GenNested G) {c coset : Coset G}
    (h1 : c.shift = 1) (hle : c.log_size ≤ coset.log_size)
    (hdisj : coset.shift ^ 2 ^ coset.log_size ≠ 1) {sel : LagrangeSelectors (List K)}
    (hsel : Coset.selectors_on_coset G c coset = some sel) (m : ℕ) (hm : m < 2 ^ coset.log_size) :
    Coset.selectors_at_point G c (coset.shift * coset.subgroup_generator ^ m) =
      some ⟨sel.is_first_row.getD m 0, sel.is_last_row.getD m 0, sel.is_transition.getD m 0,
        sel.inv_vanishing.getD m 0⟩ := by
  rw [selectors_on_coset_eq G hV hN h1 hle hdisj, Option.some.injEq] at hsel
  subst hsel
  have hlast : c.subgroup_generator ^ (2 ^ c.log_size - 1) = c.subgroup_generator⁻¹ :=
    pow_pred_eq_inv (prim G hV c)
  have ha : coset.shift * coset.subgroup_generator ^ m - 1 ≠ 0 :=
    sub_ne_zero.mpr (by simpa using point_ne_pow G hV hle hdisj m 0)
  have hb : coset.shift * coset.subgroup_generator ^ m - c.subgroup_generator⁻¹ ≠ 0 :=
    sub_ne_zero.mpr (hlast ▸ point_ne_pow G hV hle hdisj m _)
  have hz : (coset.shift * coset.subgroup_generator ^ m) ^ 2 ^ c.log_size - 1 ≠ 0 := by
    intro h0
    apply hdisj
    have := congrArg (· ^ 2 ^ (coset.log_size - c.log_size)) (sub_eq_zero.mp h0)
    simp only [one_pow, ← pow_mul, ← pow_add, Nat.add_sub_cancel' hle] at this
    rwa [mul_pow, ← pow_mul, mul_comm m, pow_mul, (prim G hV coset).pow_eq_one, one_pow,
      mul_one] at this
  simp [Coset.selectors_at_point, p3_commit.domain.mirror.div, p3_commit.domain.mirror.inv,
    TwoAdicMultiplicativeCoset.shift_inverse, h1, gen_ne_zero G hV c, ha, hb, hz, hm,
    List.getD_eq_getElem?_getD, div_eq_mul_inv]

/-- The prover's coset never panics: a disjoint domain built with a generator g outside the largest two-adic subgroup, over a subgroup of shift one. -/
theorem selectors_on_disjoint_domain (hV : GenValid G) (hN : GenNested G) {c d : Coset G} {g : K}
    {m : ℕ} (h1 : c.shift = 1) (hg : g ^ 2 ^ G.adicity ≠ 1)
    (hd : Coset.try_create_disjoint_domain G c g m = some d) (hle : c.log_size ≤ d.log_size) :
    (Coset.selectors_on_coset G c d).isSome := by
  obtain ⟨hds, -, -⟩ := try_create_disjoint_domain_some G hd
  rw [Option.isSome_iff_ne_none, ne_eq, selectors_on_coset_none G hV hN]
  push Not
  refine ⟨h1, hle, fun h => hg ?_⟩
  rw [hds, h1, one_mul] at h
  rw [show G.adicity = d.log_size + (G.adicity - d.log_size) by have := d.log_size_le; omega,
    pow_add, pow_mul, h, one_pow]

end Plonky3Lean.Proofs.Commit
