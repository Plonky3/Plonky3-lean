module

public import P3Circle.Domain
public import Plonky3Lean.Proofs.Circle.Generator

@[expose] public section

/-!
# p3-circle: twin cosets and standard position cosets

A domain of size 2^n with shift S lists the points S + i g and -S + (i + 1) g, interleaved, for g of order 2^(n - 1).

This is the twin coset of Definition 2.

The standard domain of size 2^n has the generator Q of order 2^(n + 1) as its shift.

Its point k is then (2 k + 1) Q, so its points are the odd multiples of Q:

```text
    k:       0    1    2    3   ...   2^n - 1
    point:   Q   3Q   5Q   7Q   ...   (2^(n+1) - 1) Q = -Q
```
-/

namespace Plonky3Lean.Proofs.Circle

open Plonky3Lean.Spec.Circle p3_circle.point.mirror p3_circle.domain.mirror p3_dft.mirror

set_option linter.unusedSectionVars false

variable {K : Type _} [Field K] [DecidableEq K]

/-! ## Lists -/

theorem interleave_length {α : Type _} (l₁ l₂ : List α) (h : l₁.length = l₂.length) :
    (interleave l₁ l₂).length = 2 * l₁.length := by
  induction l₁ generalizing l₂ with
  | nil => cases l₂ <;> simp_all [interleave]
  | cons a l ih =>
    cases l₂ with
    | nil => simp at h
    | cons b l₂ =>
      simp only [interleave, List.length_cons] at h ⊢
      rw [ih l₂ (by omega)]; ring

/-- Interleaving two maps over the same range: entry k is the first map at k / 2 for even k, the second for odd k. -/
theorem interleave_map_range {α : Type _} (f h : ℕ → α) (m : ℕ) :
    interleave ((List.range m).map f) ((List.range m).map h) =
      (List.range (2 * m)).map fun k => if k % 2 = 0 then f (k / 2) else h (k / 2) := by
  induction m generalizing f h with
  | zero => simp [interleave]
  | succ m ih =>
    rw [show 2 * (m + 1) = 2 * m + 1 + 1 by ring]
    simp only [List.range_succ_eq_map, List.map_cons, List.map_map, interleave]
    rw [ih]
    simp only [List.cons.injEq]
    refine ⟨by simp, by simp, List.map_congr_left fun k _ => ?_⟩
    simp only [Function.comp_apply, Nat.succ_eq_add_one]
    rw [show (k + 1 + 1) % 2 = k % 2 by omega, show (k + 1 + 1) / 2 = k / 2 + 1 by omega]

theorem iterate_add_ofC (s g : C K) (i : ℕ) :
    (fun p => Point.add p (ofC g))^[i] (ofC s) = ofC (s + i • g) := by
  induction i with
  | zero => simp
  | succ i ih => rw [Function.iterate_succ_apply', ih, add_ofC, succ_nsmul, add_assoc]

theorem chain_ofC (s g : C K) (len : ℕ) :
    chain (ofC s) (ofC g) len = (List.range len).map fun i => ofC (s + i • g) := by
  simp only [chain, iterate_add_ofC]

/-! ## Twin cosets -/

/-- Point k of the twin coset with shift S and step g. -/
def twinPoint (S g : C K) (k : ℕ) : C K :=
  if k % 2 = 0 then S + (k / 2) • g else -S + (k / 2 + 1) • g

variable {G : Gen (K × K)}

theorem subgroup_generator_eq (hV : CircleGenValid G) (d : CircleDomain K) (hn : 1 ≤ d.log_n)
    (hG : d.log_n - 1 ≤ G.adicity) :
    CircleDomain.subgroup_generator G d = some (ofC (genPt G (d.log_n - 1))) := by
  rw [CircleDomain.subgroup_generator, generator_eq hV]
  simp [show d.log_n ≠ 0 by omega, hG]

/-- The points of a twin coset of size 2^n, n >= 1, with shift S. -/
theorem points_eq (hV : CircleGenValid G) (n : ℕ) (S : C K) (hn : 1 ≤ n) (hG : n - 1 ≤ G.adicity) :
    CircleDomain.points G ⟨n, ofC S⟩ =
      some ((List.range (2 ^ n)).map fun k => ofC (twinPoint S (genPt G (n - 1)) k)) := by
  simp only [CircleDomain.points, CircleDomain.coset0, CircleDomain.coset1,
    subgroup_generator_eq hV ⟨n, ofC S⟩ hn hG, Option.bind_eq_bind, Option.bind_some, sub_ofC,
    chain_ofC]
  rw [interleave_map_range, show 2 * 2 ^ (n - 1) = 2 ^ n by
    rw [← pow_succ']; congr 1; omega]
  congr 1
  apply List.map_congr_left
  intro k _
  unfold twinPoint
  split_ifs
  · rfl
  · congr 1
    rw [sub_eq_add_neg, succ_nsmul]
    abel

/-- Point idx of a twin coset, at any index. -/
theorem nth_point_eq (hV : CircleGenValid G) (n : ℕ) (S : C K) (hn : 1 ≤ n) (hG : n - 1 ≤ G.adicity)
    (idx : ℕ) :
    CircleDomain.nth_point G ⟨n, ofC S⟩ idx = some (ofC (twinPoint S (genPt G (n - 1)) idx)) := by
  simp only [CircleDomain.nth_point, subgroup_generator_eq hV ⟨n, ofC S⟩ hn hG,
    Option.bind_eq_bind, Option.bind_some, mul_ofC, neg_ofC, add_ofC, twinPoint]
  split_ifs <;> rfl

/-- The vanishing polynomial of a twin coset is v_D of equation (7). -/
theorem vanishing_poly_eq (n : ℕ) (S P : C K) (hn : 1 ≤ n) :
    CircleDomain.vanishing_poly ⟨n, ofC S⟩ (ofC P) = some (vD n S P) := by
  simp [CircleDomain.vanishing_poly, v_n_ofC, hn, vD]

/-- Doubling n - 1 times sends every point of a twin coset of size 2^n to the shift or its conjugate. -/
theorem nsmul_twinPoint (hV : CircleGenValid G) {n : ℕ} (hG : n - 1 ≤ G.adicity)
    (S : C K) (k : ℕ) :
    2 ^ (n - 1) • twinPoint S (genPt G (n - 1)) k =
      if k % 2 = 0 then 2 ^ (n - 1) • S else -(2 ^ (n - 1) • S) := by
  have hg : 2 ^ (n - 1) • genPt G (n - 1) = 0 := by
    rw [← genPt_zero hV, ← genPt_nsmul hV (Nat.zero_le _) hG, Nat.sub_zero]
  unfold twinPoint
  split_ifs <;> simp [smul_add, smul_comm (2 ^ (n - 1)) _ (genPt G (n - 1)), hg]

/-- The vanishing polynomial is zero at every point of the twin coset. -/
theorem vD_twinPoint (hV : CircleGenValid G) {n : ℕ} (hG : n - 1 ≤ G.adicity)
    (S : C K) (k : ℕ) : vD n S (twinPoint S (genPt G (n - 1)) k) = 0 := by
  rw [vD, vn, vn, nsmul_twinPoint hV hG]
  split_ifs <;> simp

/-! ## Standard position cosets -/

/-- The standard domain of size 2^n has the generator of order 2^(n + 1) as its shift. -/
theorem standard_eq (hV : CircleGenValid G) (n : ℕ) (hG : n + 1 ≤ G.adicity) :
    CircleDomain.standard G n = some ⟨n, ofC (genPt G (n + 1))⟩ := by
  simp [CircleDomain.standard, generator_eq hV, hG]

/-- Point k of the standard domain of size 2^n is (2 k + 1) Q, for Q the generator of order 2^(n + 1). -/
theorem twinPoint_standard (hV : CircleGenValid G) {n : ℕ} (hn : 1 ≤ n) (hG : n + 1 ≤ G.adicity)
    (k : ℕ) : twinPoint (genPt G (n + 1)) (genPt G (n - 1)) k = (2 * k + 1) • genPt G (n + 1) := by
  have hg : genPt G (n - 1) = 4 • genPt G (n + 1) := by
    rw [← genPt_nsmul hV (show n - 1 ≤ n + 1 by omega) hG, show n + 1 - (n - 1) = 2 by omega]; rfl
  unfold twinPoint
  simp only [hg, smul_smul]
  split_ifs with hk
  · rw [show k / 2 * 4 = 2 * k by omega, ← succ_nsmul']
  · rw [show (k / 2 + 1) * 4 = (2 * k + 1) + 1 by omega, succ_nsmul]
    abel


/-- The standard domain of size 2^n lists (2 k + 1) Q for k < 2^n, Q the generator of order 2^(n + 1). -/
theorem standard_points (hV : CircleGenValid G) {n : ℕ} (hn : 1 ≤ n) (hG : n + 1 ≤ G.adicity) :
    CircleDomain.points G ⟨n, ofC (genPt G (n + 1))⟩ =
      some ((List.range (2 ^ n)).map fun k => ofC ((2 * k + 1) • genPt G (n + 1))) := by
  rw [points_eq hV n _ hn (by omega)]
  simp only [twinPoint_standard hV hn hG]

theorem addOrderOf_genPt_succ (hV : CircleGenValid G) (h2 : (2 : K) ≠ 0) {n : ℕ}
    (hG : n + 1 ≤ G.adicity) : addOrderOf (genPt G (n + 1)) = 2 ^ (n + 1) :=
  addOrderOf_genPt hV h2 hG

/-- The 2^n points of a standard domain are distinct. -/
theorem standard_nodup (hV : CircleGenValid G) (h2 : (2 : K) ≠ 0) {n : ℕ} (hG : n + 1 ≤ G.adicity) :
    ((List.range (2 ^ n)).map fun k => (2 * k + 1) • genPt G (n + 1)).Nodup := by
  refine List.Nodup.map_on (fun k hk k' hk' h => ?_) List.nodup_range
  rw [nsmul_eq_nsmul_iff_modEq, addOrderOf_genPt_succ hV h2 hG] at h
  simp only [List.mem_range] at hk hk'
  have := Nat.ModEq.eq_of_lt_of_lt h (by rw [pow_succ]; omega) (by rw [pow_succ]; omega)
  omega

/-- A point lies in the standard domain of size 2^n exactly when it is an odd multiple of Q. -/
theorem mem_standard (hV : CircleGenValid G) (h2 : (2 : K) ≠ 0) {n : ℕ} (hG : n + 1 ≤ G.adicity)
    (P : C K) :
    P ∈ (List.range (2 ^ n)).map (fun k => (2 * k + 1) • genPt G (n + 1)) ↔
      ∃ j, P = (2 * j + 1) • genPt G (n + 1) := by
  constructor
  · rintro h
    obtain ⟨k, -, rfl⟩ := List.mem_map.mp h
    exact ⟨k, rfl⟩
  · rintro ⟨j, rfl⟩
    refine List.mem_map.mpr ⟨j % 2 ^ n, List.mem_range.mpr (Nat.mod_lt _ (by positivity)), ?_⟩
    rw [nsmul_eq_nsmul_iff_modEq, addOrderOf_genPt_succ hV h2 hG, pow_succ]
    have := Nat.mod_add_div j (2 ^ n)
    unfold Nat.ModEq
    rw [show 2 * j + 1 = 2 * (j % 2 ^ n) + 1 + 2 ^ n * 2 * (j / 2 ^ n) by
      conv_lhs => rw [← this]
      ring, Nat.add_mul_mod_self_left]

/-- Standard domains of different sizes are disjoint. -/
theorem standard_disjoint (hV : CircleGenValid G) (h2 : (2 : K) ≠ 0) {m n : ℕ} (hmn : m < n)
    (hG : n + 1 ≤ G.adicity) (i j : ℕ) :
    (2 * i + 1) • genPt G (m + 1) ≠ (2 * j + 1) • genPt G (n + 1) := by
  intro h
  rw [← genPt_nsmul hV (show m + 1 ≤ n + 1 by omega) hG, smul_smul, nsmul_eq_nsmul_iff_modEq,
    addOrderOf_genPt_succ hV h2 hG] at h
  have h2' := Nat.ModEq.of_dvd (dvd_pow_self 2 (by omega : n + 1 ≠ 0)) h
  unfold Nat.ModEq at h2'
  rw [Nat.mul_mod, Nat.pow_mod, show n + 1 - (m + 1) = (n - m - 1) + 1 by omega, pow_succ] at h2'
  simp at h2'

/-- The squaring map sends point k of the standard domain of size 2^n to point k of the one of size 2^(n - 1), mod 2^(n - 1). -/
theorem double_standard (hV : CircleGenValid G) (h2 : (2 : K) ≠ 0) {n : ℕ} (hn : 1 ≤ n)
    (hG : n + 1 ≤ G.adicity) (k : ℕ) :
    2 • ((2 * k + 1) • genPt G (n + 1)) = (2 * (k % 2 ^ (n - 1)) + 1) • genPt G (n - 1 + 1) := by
  have hQ : 2 • genPt G (n + 1) = genPt G (n - 1 + 1) := by
    rw [← genPt_nsmul hV (show n - 1 + 1 ≤ n + 1 by omega) hG, show n + 1 - (n - 1 + 1) = 1 by omega,
      pow_one]
  rw [smul_comm, hQ, nsmul_eq_nsmul_iff_modEq, addOrderOf_genPt_succ hV h2 (by omega),
    show n - 1 + 1 = n by omega]
  have := Nat.mod_add_div k (2 ^ (n - 1))
  unfold Nat.ModEq
  rw [show 2 * k + 1 = 2 * (k % 2 ^ (n - 1)) + 1 + 2 ^ n * (k / 2 ^ (n - 1)) by
    conv_lhs => rw [← this]
    rw [show 2 ^ n = 2 * 2 ^ (n - 1) by rw [← pow_succ']; congr 1; omega]
    ring, Nat.add_mul_mod_self_left]

/-- The twin-coset symmetry: point 2^n - 1 - k of a standard domain is the conjugate of point k. -/
theorem standard_twin (hV : CircleGenValid G) (h2 : (2 : K) ≠ 0) {n : ℕ} (hG : n + 1 ≤ G.adicity)
    {k : ℕ} (hk : k < 2 ^ n) :
    (2 * (2 ^ n - 1 - k) + 1) • genPt G (n + 1) = -((2 * k + 1) • genPt G (n + 1)) := by
  rw [eq_neg_iff_add_eq_zero, ← add_nsmul, ← addOrderOf_dvd_iff_nsmul_eq_zero,
    addOrderOf_genPt_succ hV h2 hG, show 2 * (2 ^ n - 1 - k) + 1 + (2 * k + 1) = 2 ^ (n + 1) by
      rw [pow_succ]; omega]


theorem is_standard_standard (hV : CircleGenValid G) {n : ℕ} (hG : n + 1 ≤ G.adicity) :
    CircleDomain.is_standard G ⟨n, ofC (genPt G (n + 1))⟩ = some true := by
  simp [CircleDomain.is_standard, generator_eq hV, hG]

/-- The size of the disjoint domain: the ceiling log of min_size, bumped by one when it equals the current size. -/
def disjointLog (n min_size : ℕ) : ℕ :=
  if p3_commit.domain.mirror.log2Ceil min_size = n then p3_commit.domain.mirror.log2Ceil min_size + 1
  else p3_commit.domain.mirror.log2Ceil min_size

/-- From a standard domain, the disjoint domain is the standard domain of the bumped size, or none when the circle group has no shift of the needed order. -/
theorem try_create_disjoint_domain_eq (hV : CircleGenValid G) {n : ℕ} (hG : n + 1 ≤ G.adicity)
    (min_size : ℕ) :
    CircleDomain.try_create_disjoint_domain G ⟨n, ofC (genPt G (n + 1))⟩ min_size =
      if G.adicity ≤ disjointLog n min_size then some none
      else some (some ⟨disjointLog n min_size, ofC (genPt G (disjointLog n min_size + 1))⟩) := by
  simp only [CircleDomain.try_create_disjoint_domain, is_standard_standard hV hG, Option.bind_eq_bind,
    Option.bind_some, Bool.not_true, Bool.false_eq_true, ↓reduceIte, disjointLog]
  split_ifs <;> simp_all [standard_eq hV]

theorem disjointLog_ne (n min_size : ℕ) : disjointLog n min_size ≠ n := by
  unfold disjointLog; split_ifs <;> omega

/-- The disjoint domain holds at least min_size points. -/
theorem le_two_pow_disjointLog (n min_size : ℕ) : min_size ≤ 2 ^ disjointLog n min_size := by
  have h := Nat.lt_size_self (min_size - 1)
  have : min_size ≤ 2 ^ p3_commit.domain.mirror.log2Ceil min_size := by
    unfold p3_commit.domain.mirror.log2Ceil; omega
  unfold disjointLog
  split_ifs
  · rw [pow_succ]; omega
  · exact this

end Plonky3Lean.Proofs.Circle
