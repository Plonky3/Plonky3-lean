module

public import P3Commit.Domain
public import Plonky3Lean.Proofs.Commit.Coset
public import Plonky3Lean.Proofs.Matrix.Interpolation

@[expose] public section

/-!
# p3-commit: the coset as a polynomial space

Points, disjoint domains, splitting, the vanishing polynomial and the selectors at a point.

Write n = 2^k for the size, s for the shift, omega for the subgroup generator and u = x / s.
-/

open Polynomial Finset
open p3_commit.domain.mirror p3_field.coset.mirror p3_dft.mirror
open Plonky3Lean.Spec.Commit Plonky3Lean.Proofs.Dft

namespace Plonky3Lean.Proofs.Commit

set_option linter.unusedSectionVars false

variable {K : Type _} [Field K] [DecidableEq K] (G : Gen K)

theorem cosetPoints_eq_cosetPt (s ω : K) (k : ℕ) :
    cosetPoints s ω k = Plonky3Lean.Proofs.Matrix.Interp.cosetPt ω s k := rfl

theorem cosetPoints_injective {s ω : K} {k : ℕ} (hω : IsPrimitiveRoot ω (2 ^ k)) (hs : s ≠ 0) :
    Function.Injective (cosetPoints s ω k) :=
  Plonky3Lean.Proofs.Matrix.Interp.cosetPt_injective hω hs

/-- The coset's generator is a primitive root of order its size. -/
theorem prim (hV : GenValid G) (c : Coset G) :
    IsPrimitiveRoot c.subgroup_generator (2 ^ c.log_size) :=
  hV _ c.log_size_le

/-! ## Points -/

theorem size_eq (c : Coset G) : Coset.size G c = 2 ^ c.log_size := rfl

/-- The first point is point 0. -/
theorem first_point_eq (c : Coset G) :
    Coset.first_point G c = cosetPoints c.shift c.subgroup_generator c.log_size ⟨0, by simp⟩ := by
  simp [Coset.first_point, cosetPoints]

/-- The next point of s omega^i is s omega^(i + 1); after point n - 1 it wraps to point 0. -/
theorem next_point_eq (hV : GenValid G) (c : Coset G) (i : ℕ) :
    Coset.next_point G c (c.shift * c.subgroup_generator ^ i) =
      some (c.shift * c.subgroup_generator ^ ((i + 1) % 2 ^ c.log_size)) := by
  rw [Coset.next_point, mul_assoc, ← pow_succ, (prim G hV c).eq_orderOf, pow_mod_orderOf]

/-! ## Disjoint domains -/

theorem log2Ceil_le_iff (m A : ℕ) : log2Ceil m ≤ A ↔ m ≤ 2 ^ A := by
  have := Nat.one_le_two_pow (n := A); rw [log2Ceil, Nat.size_le]; omega

theorem le_pow_log2Ceil (m : ℕ) : m ≤ 2 ^ log2Ceil m := by
  have := Nat.lt_size_self (m - 1); rw [log2Ceil]; omega

/-- A disjoint domain exists exactly for min_size <= 2^adicity, with shift s g and size at least min_size. -/
theorem try_create_disjoint_domain_eq (c : Coset G) (g : K) (hg : g ≠ 0) (m : ℕ) :
    (Coset.try_create_disjoint_domain G c g m).isSome ↔ m ≤ 2 ^ G.adicity := by
  simp [Coset.try_create_disjoint_domain, TwoAdicMultiplicativeCoset.new, c.shift_ne_zero, hg,
    log2Ceil_le_iff]

theorem try_create_disjoint_domain_some {c d : Coset G} {g : K} {m : ℕ}
    (h : Coset.try_create_disjoint_domain G c g m = some d) :
    d.shift = c.shift * g ∧ d.log_size = log2Ceil m ∧ m ≤ Coset.size G d := by
  simp only [Coset.try_create_disjoint_domain, TwoAdicMultiplicativeCoset.new] at h
  split_ifs at h
  cases h
  exact ⟨rfl, rfl, le_pow_log2Ceil m⟩

/-- Every subgroup the table covers lies in the largest one. -/
theorem gen_pow_adicity (hV : GenValid G) {k : ℕ} (hk : k ≤ G.adicity) (i : ℕ) :
    (G.gen k ^ i) ^ 2 ^ G.adicity = 1 := by
  rw [← pow_mul, mul_comm, pow_mul, show G.adicity = k + (G.adicity - k) by omega, pow_add,
    pow_mul, (hV k hk).pow_eq_one, one_pow, one_pow]

/-- If g is outside the largest two-adic subgroup, the disjoint domain s g K meets no coset s H. -/
theorem disjoint (hV : GenValid G) {c d : Coset G} {g : K} {m : ℕ}
    (hg : g ^ 2 ^ G.adicity ≠ 1) (h : Coset.try_create_disjoint_domain G c g m = some d)
    (i : Fin (2 ^ d.log_size)) (j : Fin (2 ^ c.log_size)) :
    cosetPoints d.shift d.subgroup_generator d.log_size i ≠
      cosetPoints c.shift c.subgroup_generator c.log_size j := by
  obtain ⟨hd, -, -⟩ := try_create_disjoint_domain_some G h
  intro heq
  simp only [cosetPoints, hd, mul_assoc] at heq
  have hi := gen_pow_adicity G hV d.log_size_le i
  have hgi : g = G.gen c.log_size ^ j.val * (G.gen d.log_size ^ i.val)⁻¹ := by
    rw [eq_mul_inv_iff_mul_eq₀ (by rintro h0; simp [h0] at hi)]
    exact mul_left_cancel₀ c.shift_ne_zero heq
  apply hg
  rw [hgi, mul_pow, inv_pow, hi, gen_pow_adicity G hV c.log_size_le, inv_one, mul_one]

/-! ## Splitting -/

theorem gen_ne_zero (hV : GenValid G) (c : Coset G) : c.subgroup_generator ≠ 0 :=
  (prim G hV c).ne_zero (by positivity)

/-- Chunk i of a split into 2^l: the shift s omega^i over the subgroup 2^l times smaller. -/
def chunk (hV : GenValid G) (c : Coset G) (l : ℕ) (i : ℕ) : Coset G :=
  ⟨c.shift * c.subgroup_generator ^ i, c.log_size - l,
    mul_ne_zero c.shift_ne_zero (pow_ne_zero _ (gen_ne_zero G hV c)), by have := c.log_size_le; omega⟩

/-- Splitting into 2^l chunks, for l <= k, returns the chunks in order. -/
theorem split_domains_eq (hV : GenValid G) (c : Coset G) {l : ℕ} (hl : l ≤ c.log_size) :
    Coset.split_domains G c (2 ^ l) = some ((List.range (2 ^ l)).map (chunk G hV c l)) := by
  have hnew : ∀ i, (TwoAdicMultiplicativeCoset.new (c.shift * c.subgroup_generator ^ i)
      (c.log_size - l) : Option (Coset G)) = some (chunk G hV c l i) := fun i => by
    simp [TwoAdicMultiplicativeCoset.new, chunk, c.shift_ne_zero, gen_ne_zero G hV c,
      show c.log_size - l ≤ G.adicity by have := c.log_size_le; omega]
  simp only [Coset.split_domains, log2Strict_pow, Option.bind_eq_bind, Option.bind_some, hl,
    ite_true, hnew]
  exact List.mapM_pure

/-- Any other chunk count panics: one that is not a power of two, or above the size. -/
theorem split_domains_none (c : Coset G) {nc : ℕ} (h : ∀ l, nc = 2 ^ l → c.log_size < l) :
    Coset.split_domains G c nc = none := by
  simp only [Coset.split_domains]
  cases hl : log2Strict nc with
  | none => rfl
  | some l =>
    have := h l (log2Strict_eq_some hl)
    simp [show ¬ l ≤ c.log_size by omega]

/-- Point j of chunk i is point i + 2^l j of the coset. -/
theorem chunk_point (hV : GenValid G) (hN : GenNested G) (c : Coset G) {l : ℕ}
    (hl : l ≤ c.log_size) (i j : ℕ) :
    (chunk G hV c l i).shift * (chunk G hV c l i).subgroup_generator ^ j =
      c.shift * c.subgroup_generator ^ (i + 2 ^ l * j) := by
  simp only [chunk, TwoAdicMultiplicativeCoset.subgroup_generator]
  rw [gen_sub G hN c.log_size_le hl, ← pow_mul, pow_add, mul_assoc]

/-- The chunks partition the coset: each point of s H lies in exactly one chunk. -/
theorem split_partition (hV : GenValid G) (hN : GenNested G) (c : Coset G) {l : ℕ}
    (hl : l ≤ c.log_size) (x : K) :
    InCoset c.shift c.subgroup_generator c.log_size x ↔
      ∃! i, i < 2 ^ l ∧ InCoset (chunk G hV c l i).shift (chunk G hV c l i).subgroup_generator
        (chunk G hV c l i).log_size x := by
  have hω := prim G hV c
  have hk : 2 ^ c.log_size = 2 ^ l * 2 ^ (c.log_size - l) := by
    rw [← pow_add]; congr 1; omega
  have hpt : ∀ i (j : Fin (2 ^ (chunk G hV c l i).log_size)), cosetPoints (chunk G hV c l i).shift
      (chunk G hV c l i).subgroup_generator (chunk G hV c l i).log_size j =
      c.shift * c.subgroup_generator ^ (i + 2 ^ l * j.val) := fun i j => chunk_point G hV hN c hl i j
  have hinj : ∀ a b, a < 2 ^ c.log_size → b < 2 ^ c.log_size →
      c.shift * c.subgroup_generator ^ a = c.shift * c.subgroup_generator ^ b → a = b :=
    fun a b ha hb h => hω.pow_inj ha hb (mul_left_cancel₀ c.shift_ne_zero h)
  have hlt : ∀ i (j : ℕ), i < 2 ^ l → j < 2 ^ (c.log_size - l) → i + 2 ^ l * j < 2 ^ c.log_size :=
    fun i j hi hj => by
      rw [hk]; nlinarith [Nat.mul_le_mul_left (2 ^ l) (Nat.succ_le_of_lt hj)]
  constructor
  · rintro ⟨⟨m, hm⟩, rfl⟩
    have hj : m / 2 ^ l < 2 ^ (c.log_size - l) := by
      rw [Nat.div_lt_iff_lt_mul (by positivity), mul_comm, ← hk]; exact hm
    refine ⟨m % 2 ^ l, ⟨Nat.mod_lt _ (by positivity), ⟨m / 2 ^ l, hj⟩, ?_⟩, ?_⟩
    · rw [hpt, Nat.mod_add_div]; rfl
    · rintro i ⟨hi, ⟨j, hj'⟩⟩
      rw [hpt] at hj'
      have := hinj _ _ (hlt i j hi j.isLt) hm (by simpa [cosetPoints] using hj'.symm)
      rw [← this, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hi]
  · rintro ⟨i, ⟨hi, ⟨j, rfl⟩⟩, -⟩
    exact ⟨⟨_, hlt i j hi j.isLt⟩, hpt i j⟩

/-- The inner copy loop writes row i of every chunk below n. -/
theorem foldl_chunks {V : Type _} (rows : ℕ → V) (nc i n : ℕ) (acc : ℕ → ℕ → V) :
    (List.range n).foldl (fun acc chunk =>
      fun ch r => if ch = chunk ∧ r = i then rows (i * nc + chunk) else acc ch r) acc =
      fun ch r => if ch < n ∧ r = i then rows (i * nc + ch) else acc ch r := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.foldl_append, ih]
    funext ch r
    simp only [List.foldl_cons, List.foldl_nil]
    rcases eq_or_ne r i with rfl | hr
    · rcases eq_or_ne ch n with rfl | h
      · simp
      · simp [h, show ch < n + 1 ↔ ch < n by omega]
    · simp [hr]

/-- The outer copy loop writes rows below m of every chunk below nc. -/
theorem foldl_rows {V : Type _} (rows : ℕ → V) (nc m : ℕ) (acc : ℕ → ℕ → V) :
    (List.range m).foldl (fun acc i => (List.range nc).foldl (fun acc chunk =>
      fun ch r => if ch = chunk ∧ r = i then rows (i * nc + chunk) else acc ch r) acc) acc =
      fun ch r => if ch < nc ∧ r < m then rows (r * nc + ch) else acc ch r := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [List.range_succ, List.foldl_append, ih]
    simp only [List.foldl_cons, List.foldl_nil, foldl_chunks]
    funext ch r
    rcases eq_or_ne r m with rfl | hr
    · simp
    · simp [hr, show r < m + 1 ↔ r < m by omega]

/-- Splitting the evaluations into 2^l chunks: row j of chunk i is row i + 2^l j, the value at point j of chunk i. -/
theorem split_evals_eq {V : Type _} [Zero V] (c : Coset G) {l : ℕ} (hl : l ≤ c.log_size)
    (rows : ℕ → V) :
    Coset.split_evals G c (2 ^ l) (Coset.size G c) rows =
      some ((List.range (2 ^ l)).map fun i j =>
        if j < 2 ^ (c.log_size - l) then rows (i + 2 ^ l * j) else 0) := by
  have hdiv : Coset.size G c / 2 ^ l = 2 ^ (c.log_size - l) := by
    rw [size_eq, Nat.pow_div hl (by norm_num)]
  simp only [Coset.split_evals, ne_eq, not_true_eq_false, ite_false, log2Strict_pow, hl, ite_true,
    hdiv, foldl_rows]
  congr 1
  refine List.map_congr_left fun i hi => ?_
  funext j
  have := List.mem_range.mp hi
  by_cases hj : j < 2 ^ (c.log_size - l) <;> simp [hj, this, Nat.add_comm, Nat.mul_comm]

/-- Splitting panics on evaluations of the wrong height. -/
theorem split_evals_height {V : Type _} [Zero V] (c : Coset G) (nc h : ℕ) (rows : ℕ → V)
    (hh : h ≠ Coset.size G c) : Coset.split_evals G c nc h rows = none := by
  simp [Coset.split_evals, hh]

/-! ## The vanishing polynomial -/

/-- Point n - 1, the last point. -/
def lastIdx (k : ℕ) : Fin (2 ^ k) := ⟨2 ^ k - 1, Nat.sub_lt (by positivity) one_pos⟩

theorem eval_vanishing (hV : GenValid G) (c : Coset G) (x : K) :
    (vanishing c.shift c.subgroup_generator c.log_size).eval x =
      x ^ 2 ^ c.log_size - c.shift ^ 2 ^ c.log_size := by
  rw [vanishing, cosetPoints_eq_cosetPt, Plonky3Lean.Proofs.Matrix.Interp.nodal_coset (prim G hV c)]
  simp

/-- The code's vanishing polynomial is the monic one divided by s^n: (x / s)^n - 1. -/
theorem vanishing_poly_at_point_eq (hV : GenValid G) (c : Coset G) (x : K) :
    Coset.vanishing_poly_at_point G c x =
      (vanishing c.shift c.subgroup_generator c.log_size).eval x / c.shift ^ 2 ^ c.log_size := by
  have hs := pow_ne_zero (2 ^ c.log_size) c.shift_ne_zero
  rw [eval_vanishing G hV, Coset.vanishing_poly_at_point, TwoAdicMultiplicativeCoset.shift_inverse,
    mul_pow, inv_pow, sub_div, div_self hs, div_eq_mul_inv]

/-- The vanishing polynomial is zero exactly on the coset. -/
theorem vanishing_poly_at_point_eq_zero (hV : GenValid G) (c : Coset G) (x : K) :
    Coset.vanishing_poly_at_point G c x = 0 ↔ InCoset c.shift c.subgroup_generator c.log_size x := by
  rw [vanishing_poly_at_point_eq G hV, eval_vanishing G hV, inCoset_iff (prim G hV c) c.shift_ne_zero,
    div_eq_zero_iff, sub_eq_zero]
  simp [c.shift_ne_zero]

/-! ## Selectors at a point -/

/-- Off the coset, the Lagrange polynomial of point i is (x^n - s^n) x_i / (n s^n (x - x_i)). -/
theorem eval_lagrange {s ω x : K} {k : ℕ} (hω : IsPrimitiveRoot ω (2 ^ k)) (hs : s ≠ 0)
    (h2 : (2 : K) ≠ 0) (i : Fin (2 ^ k)) (hx : x ≠ cosetPoints s ω k i) :
    (lagrange s ω k i).eval x = (x ^ 2 ^ k - s ^ 2 ^ k) *
      (cosetPoints s ω k i / ((2 ^ k : K) * s ^ 2 ^ k) * (x - cosetPoints s ω k i)⁻¹) := by
  classical
  rw [lagrange, Lagrange.eval_basis_not_at_node (mem_univ i) hx, cosetPoints_eq_cosetPt,
    Plonky3Lean.Proofs.Matrix.Interp.nodal_coset hω,
    Plonky3Lean.Proofs.Matrix.Interp.nodalWeight_coset hω hs h2]
  simp

theorem pow_pred_eq_inv {ω : K} {k : ℕ} (hω : IsPrimitiveRoot ω (2 ^ k)) :
    ω ^ (2 ^ k - 1) = ω⁻¹ := by
  refine eq_inv_of_mul_eq_one_left ?_
  rw [← pow_succ, Nat.sub_add_cancel Nat.one_le_two_pow, hω.pow_eq_one]

/-- The selectors at a point panic exactly when the point lies on the coset. -/
theorem selectors_at_point_none (hV : GenValid G) (c : Coset G) (x : K) :
    Coset.selectors_at_point G c x = none ↔ InCoset c.shift c.subgroup_generator c.log_size x := by
  have hω := prim G hV c
  have hg := gen_ne_zero G hV c
  have hs := c.shift_ne_zero
  rw [inCoset_iff hω hs]
  simp only [Coset.selectors_at_point, p3_commit.domain.mirror.div, p3_commit.domain.mirror.inv,
    TwoAdicMultiplicativeCoset.shift_inverse, hg,
    ite_false]
  constructor
  · intro h
    by_contra hne
    have h1 : x * c.shift⁻¹ - 1 ≠ 0 := by
      intro h0; apply hne; rw [show x = c.shift by field_simp at h0; linear_combination h0]
    have h2 : x * c.shift⁻¹ - c.subgroup_generator⁻¹ ≠ 0 := by
      intro h0
      apply hne
      have hx : x = c.shift * c.subgroup_generator ^ (2 ^ c.log_size - 1) := by
        rw [pow_pred_eq_inv hω]; field_simp at h0 ⊢; linear_combination h0
      rw [hx, mul_pow, ← pow_mul, mul_comm (2 ^ c.log_size - 1), pow_mul, hω.pow_eq_one, one_pow,
        mul_one]
    have h3 : (x * c.shift⁻¹) ^ 2 ^ c.log_size - 1 ≠ 0 := by
      rw [mul_pow, inv_pow, sub_ne_zero, ne_eq, mul_inv_eq_one₀ (pow_ne_zero _ hs)]; exact hne
    simp [h1, h2, h3] at h
  · intro h
    have h3 : (x * c.shift⁻¹) ^ 2 ^ c.log_size - 1 = 0 := by
      rw [mul_pow, inv_pow, h, mul_inv_cancel₀ (pow_ne_zero _ hs), sub_self]
    simp [h3]

/-- Off the coset the selectors are n L_0(x), n omega L_(n-1)(x), (x - s omega^(n-1)) / s and s^n / Z(x), for Z the monic vanishing polynomial. -/
theorem selectors_at_point_some (hV : GenValid G) (h2 : (2 : K) ≠ 0) (c : Coset G) (x : K)
    (hx : ¬ InCoset c.shift c.subgroup_generator c.log_size x) :
    Coset.selectors_at_point G c x = some
      ⟨(2 ^ c.log_size : K) * (lagrange c.shift c.subgroup_generator c.log_size 0).eval x,
       (2 ^ c.log_size : K) * c.subgroup_generator *
         (lagrange c.shift c.subgroup_generator c.log_size (lastIdx c.log_size)).eval x,
       (x - cosetPoints c.shift c.subgroup_generator c.log_size (lastIdx c.log_size)) / c.shift,
       c.shift ^ 2 ^ c.log_size / (vanishing c.shift c.subgroup_generator c.log_size).eval x⟩ := by
  have hω := prim G hV c
  have hg := gen_ne_zero G hV c
  have hs := c.shift_ne_zero
  have hlast : cosetPoints c.shift c.subgroup_generator c.log_size (lastIdx c.log_size) =
      c.shift * c.subgroup_generator⁻¹ := by
    simp [cosetPoints, lastIdx, pow_pred_eq_inv hω]
  have h0 : cosetPoints c.shift c.subgroup_generator c.log_size 0 = c.shift := by
    simp [cosetPoints]
  have hxs : x ≠ c.shift := fun h => hx ⟨0, by rw [h0, h]⟩
  have hxl : x ≠ c.shift * c.subgroup_generator⁻¹ := fun h => hx ⟨lastIdx _, by rw [hlast, h]⟩
  have hxn : x ^ 2 ^ c.log_size - c.shift ^ 2 ^ c.log_size ≠ 0 :=
    sub_ne_zero.mpr fun h => hx ((inCoset_iff hω hs).mpr h)
  have h1 : x * c.shift⁻¹ - 1 ≠ 0 := by
    rw [sub_ne_zero, ne_eq, mul_inv_eq_one₀ hs]; exact hxs
  have h2' : x * c.shift⁻¹ - c.subgroup_generator⁻¹ ≠ 0 := by
    rw [sub_ne_zero, ne_eq, mul_inv_eq_iff_eq_mul₀ hs, mul_comm]; exact hxl
  have h3 : (x * c.shift⁻¹) ^ 2 ^ c.log_size - 1 ≠ 0 := by
    rw [mul_pow, inv_pow, sub_ne_zero, ne_eq, mul_inv_eq_one₀ (pow_ne_zero _ hs)]
    exact sub_ne_zero.mp hxn
  simp only [Coset.selectors_at_point, p3_commit.domain.mirror.div, p3_commit.domain.mirror.inv,
    TwoAdicMultiplicativeCoset.shift_inverse, hg, h1, h2', h3, ite_false, Option.bind_eq_bind,
    Option.bind_some, Option.pure_def]
  rw [eval_lagrange hω hs h2 0 (by rw [h0]; exact hxs),
    eval_lagrange hω hs h2 _ (by rw [hlast]; exact hxl), eval_vanishing G hV, hlast, h0]
  have hx1 : x - c.shift ≠ 0 := sub_ne_zero.mpr hxs
  have hx2 : x - c.shift * c.subgroup_generator⁻¹ ≠ 0 := sub_ne_zero.mpr hxl
  have h2k : (2 : K) ^ c.log_size ≠ 0 := pow_ne_zero _ h2
  simp only [Option.some.injEq, LagrangeSelectors.mk.injEq]
  have hsn := pow_ne_zero (2 ^ c.log_size) hs
  refine ⟨?_, ?_, by field_simp, ?_⟩
  · simp only [mul_pow, inv_pow]; field_simp
  · simp only [mul_pow, inv_pow]; field_simp
  · rw [mul_pow, inv_pow, ← div_eq_mul_inv, div_sub_one hsn, inv_div]

end Plonky3Lean.Proofs.Commit
