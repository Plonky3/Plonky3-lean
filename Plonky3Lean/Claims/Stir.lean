module

public import Plonky3Lean.Proofs.Stir.Geometry
public import Plonky3Lean.Proofs.Stir.VerifierChecks
public import Plonky3Lean.Proofs.Stir.Round
public import Plonky3Lean.Proofs.Stir.Combine
public import Plonky3Lean.Proofs.Stir.Interp
public import Plonky3Lean.Proofs.Commit.BabyBear
public import CompPoly.Fields.BabyBear.Ext4

@[expose] public section

/-!
# p3-stir: claims

The crate is transcribed over a field, not extracted.

The claims are stated at BabyBear F and its quartic extension EF = F[X] / (X^4 - 11).

The specification is STIR, eprint 2024/390, Sections 4 and 5:

```text
    Fold(f, k, a)(y)          = p_y(a),   p_y interpolates f on { x in L : x^k = y }
    PolyFold(f, k, r)         = sum_{l < k} r^l f_l,   f(X) = sum_l X^l f_l(X^k)
    Quotient(f, S, Ans)(x)    = (f(x) - Ans(x)) / V_S(x)       for x not in S
    DegCor(d*, r, f, d)(x)    = f(x) sum_{l <= d* - d} (x r)^l
```

A domain is a coset s <g> of size 2^n.

Its generator is g = G_n, from a table G of two-adic generators.

The claims assume three facts:

- the table is primitive and nested
- 2 is invertible
- the field's generator w satisfies w^(2^adicity) != 1.

BabyBear's table and generator satisfy all three.
-/

open Polynomial Finset
open p3_stir.mirror p3_stir.utils.mirror p3_stir.verifier.mirror p3_stir.pcs.plan.mirror p3_dft.mirror
open Plonky3Lean.Spec.Stir Plonky3Lean.Proofs.Stir Plonky3Lean.Proofs.Dft

set_option linter.unusedSectionVars false

namespace Plonky3Lean.Claims.Stir

local notation "F" => BabyBear.Field
local notation "EF" => BabyBear.Ext4
local notation "ι" => algebraMap BabyBear.Field BabyBear.Ext4

/-! ## Polynomial arithmetic -/

/-- Horner's rule is the value of the coefficient list's polynomial. -/
theorem eval_poly (poly : List EF) (x : EF) : eval_poly poly x = (coeffPoly poly).eval x :=
  eval_poly_eq poly x

/-- The chunked Horner scheme is Horner's rule, for every positive chunk size. -/
theorem eval_poly_parallel {c : ℕ} (hc : 0 < c) (poly : List EF) (x : EF) :
    eval_poly_parallel c poly x = some ((coeffPoly poly).eval x) :=
  eval_poly_parallel_eq hc poly x

/-- Horner's rule at a base point is the value at its image in EF. -/
theorem eval_poly_at_base (poly : List EF) (x : F) :
    eval_poly_at_base poly x = (coeffPoly poly).eval (ι x) :=
  eval_poly_at_base_eq poly x

/-- The vanishing polynomial of a list of roots is prod (X - y).

It has one more coefficient than roots. -/
theorem vanishing_poly_from_roots (roots : List EF) :
    coeffPoly (vanishing_poly_from_roots roots) = (roots.map fun r => X - C r).prod ∧
      (vanishing_poly_from_roots roots).length = roots.length + 1 :=
  vanishing_poly_from_roots_eq roots

/-- Reduction modulo X^n - c keeps the value at every y with y^n = c. -/
theorem reduce_mod_x_pow_minus_c {n : ℕ} (hn : 0 < n) (poly : List EF) (c : F) :
    ∃ r, reduce_mod_x_pow_minus_c poly n c = some r ∧ r.length = n ∧
      ∀ y : EF, y ^ n = ι c → (coeffPoly r).eval y = (coeffPoly poly).eval y :=
  reduce_mod_x_pow_minus_c_eq hn poly c

/-- Reduction modulo X^0 - c panics. -/
theorem reduce_mod_x_pow_minus_c.panics (poly : List EF) (c : F) :
    p3_stir.utils.mirror.reduce_mod_x_pow_minus_c poly 0 c = none :=
  reduce_mod_x_pow_minus_c_panics poly c

/-- Newton interpolation on distinct points gives the interpolant of degree below n. -/
theorem interpolate_poly (points values : List EF) (hlen : points.length = values.length)
    (hnd : points.Nodup) (hne : points ≠ []) :
    ∃ cs, p3_stir.utils.mirror.interpolate_poly points values = some cs ∧
      coeffPoly cs = Lagrange.interpolate (range points.length) (fun i => points.getD i 0)
        (fun i => values.getD i 0) :=
  interpolate_poly_eq points values hlen hnd hne

/-- Newton interpolation panics on lengths that differ and on a repeated point. -/
theorem interpolate_poly.panics (points values : List EF)
    (h : points.length ≠ values.length ∨ ¬ points.Nodup) :
    p3_stir.utils.mirror.interpolate_poly points values = none :=
  interpolate_poly_panics points values h

/-- The barycentric formula on a coset of the 2^k-th roots of unity is the interpolant. -/
theorem lagrange_interpolate_at {ζ x0 : F} {k : ℕ} (hζ : IsPrimitiveRoot ζ (2 ^ k)) (hx0 : x0 ≠ 0)
    (ys : List EF) (hys : ys.length = 2 ^ k) (point : EF) :
    p3_stir.utils.mirror.lagrange_interpolate_at (shiftedPowersList ζ x0 (2 ^ k)) ys point =
      some ((Lagrange.interpolate (range (2 ^ k)) (fun l => ι (x0 * ζ ^ l))
        (fun l => ys.getD l 0)).eval point) :=
  lagrange_interpolate_at_eq hζ (by rw [Nat.cast_pow, Nat.cast_ofNat]; exact pow_ne_zero _ (by decide))
    hx0 ys hys point

/-- Adding coefficient lists adds the polynomials. -/
theorem add_polys (a b : List EF) : coeffPoly (p3_stir.utils.mirror.add_polys a b) = coeffPoly a + coeffPoly b :=
  add_polys_eq a b

/-! ## Folding (Section 4.4) -/

/-- The codeword fold by 2^a on s <g>, at challenge gamma / s, is Fold(f, 2^a, gamma).

This holds at every point (s g^j)^(2^a) of L^k. -/
theorem fold_codeword (G : Gen F) (hG : GenValid G) (hN : GenNested G) {a n : ℕ} (ha : a ≤ n)
    (hn : n ≤ G.adicity) (c : List EF) (hc : c.length = 2 ^ n) {s : F} (hs : s ≠ 0) (f : EF → EF)
    (hf : ∀ i < 2 ^ n, f (ι s * ι (G.gen n) ^ i) = c.getD i 0) (γ : EF) :
    p3_stir.utils.mirror.fold_codeword G c (γ * ι s⁻¹) a n =
      some ((List.range (2 ^ (n - a))).map fun j =>
        fold (cosetSet (ι s) (ι (G.gen n)) n) f (2 ^ a) γ ((ι s * ι (G.gen n) ^ j) ^ 2 ^ a)) :=
  fold_codeword_fold G hG hN (by decide) ha hn c hc hs f hf γ

/-- The coefficient fold is PolyFold(f, 2^a, gamma) of Definition 4.7. -/
theorem fold_poly_coeffs (coeffs : List EF) (γ : EF) (a : ℕ) :
    ∃ out, p3_stir.utils.mirror.fold_poly_coeffs coeffs γ a = some out ∧
      coeffPoly out = polyFold (coeffPoly coeffs) (2 ^ a) γ :=
  fold_poly_coeffs_eq coeffs γ a

/-- Fact 4.6: f(x) = sum_{l < k} x^l f_l(x^k). -/
theorem split_parts (f : EF[X]) {k : ℕ} (hk : 0 < k) (x : EF) :
    f.eval x = ∑ l ∈ range k, x ^ l * (splitPart f k l).eval (x ^ k) :=
  eval_eq_sum_splitPart f hk x

/-- On k distinct points x with x^k = y, the fold of a polynomial is PolyFold at y. -/
theorem fold_of_polynomial {k : ℕ} (hk : 0 < k) {v : ℕ → EF} (hv : Set.InjOn v (range k : Set ℕ))
    {y : EF} (hy : ∀ l < k, v l ^ k = y) (f : EF[X]) (α : EF) :
    (Lagrange.interpolate (range k) v fun l => f.eval (v l)).eval α = (polyFold f k α).eval y :=
  eval_interpolate_fiber hk hv hy f α

/-- PolyFold divides the degree bound by k. -/
theorem polyFold_degree {f : EF[X]} {k d : ℕ} (hk : 0 < k) (hf : f.degree < (k * d : ℕ)) (r : EF) :
    (polyFold f k r).degree < d :=
  degree_polyFold_lt hk hf r

/-! ## Degree correction and Combine (Section 4.5) -/

/-- Fact 4.10: the geometric sum in closed form, with e + 1 at ratio one. -/
theorem geometric_sum (q : EF) (e : ℕ) :
    ∑ l ∈ range (e + 1), q ^ l = if q = 1 then ((e + 1 : ℕ) : EF) else (1 - q ^ (e + 1)) / (1 - q) :=
  geom_sum_closed q e

/-- The degree-correction factor is DegCor(d*, r, f, d) at x.

This includes the case x r = 1.

It never panics. -/
theorem eval_degree_correction (f : EF → EF) (x r : EF) (dstar d : ℕ) :
    p3_stir.utils.mirror.eval_degree_correction (f x) x r (dstar - d) = some (degCor dstar d r f x) :=
  eval_degree_correction_degCor f x r dstar d

/-- Degree correction raises a degree bound d to d*. -/
theorem degCor_degree {dstar d : ℕ} (hd : d ≤ dstar) (r : EF) {f : EF[X]} (hf : f.degree < d) :
    (polyDegCor dstar d r f).degree < dstar :=
  degree_polyDegCor_lt hd r hf

/-- The batched sweep at every point x_p = s g^p is

sum_i r_i v_i[p] sum_{t <= gap_i} (x_p r)^t.

This holds for every chunk size, and includes the lane x_p r = 1. -/
theorem combine_on_coset {c : ℕ} (hc : 0 < c) (G : Gen F) (hG : GenValid G) {n : ℕ}
    (hn : n ≤ G.adicity) (groups : List (EF × ℕ × List EF)) (r : EF) (s : F)
    (hgroups : ∀ grp ∈ groups, grp.2.2.length = 2 ^ n) :
    p3_stir.utils.mirror.combine_on_coset c G groups r s n =
      some ((List.range (2 ^ n)).map fun p =>
        (groups.map fun grp => grp.1 * grp.2.2.getD p 0 *
          ∑ t ∈ range (grp.2.1 + 1), ((ι s * ι (G.gen n) ^ p) * r) ^ t).sum) :=
  combine_on_coset_eq hc G hG hn groups r s hgroups

/-- The Combine coefficients are the r_i of Definition 4.11, with gaps d* - d_i.

This holds for class degrees at most d*. -/
theorem combine_coefficients (r : EF) (L : ℕ) (logs : List ℕ) (h : ∀ l ∈ logs, l ≤ L) :
    p3_stir.pcs.plan.mirror.combine_coefficients r L logs = some ((List.range logs.length).map fun i =>
      (ri (2 ^ L) (logs.map (2 ^ ·)) r i, 2 ^ L - 2 ^ logs.getD i 0)) :=
  combine_coefficients_eq r L logs h

/-- The Combine coefficients panic on a class degree above d*. -/
theorem combine_coefficients.panics (r : EF) (L : ℕ) (logs : List ℕ) (h : ∃ l ∈ logs, L < l) :
    p3_stir.pcs.plan.mirror.combine_coefficients r L logs = none :=
  combine_coefficients_panics r L logs h

/-! ## Quotients and one round (Sections 4.2 and 5.1) -/

/-- The answer check accepts exactly when ans(rho) is the interpolant at rho.

This holds for distinct nodes, and rho off them. -/
theorem check_ans_interpolates (ans pts vals : List EF) (ρ : EF) (hlen : pts.length = vals.length)
    (hne : pts ≠ []) (hnodup : pts.Nodup) (hρ : ρ ∉ pts) :
    p3_stir.utils.mirror.check_ans_interpolates ans pts vals ρ = some (decide ((coeffPoly ans).eval ρ =
      (Lagrange.interpolate (range pts.length) (fun i => pts.getD i 0) (fun i => vals.getD i 0)).eval ρ)) :=
  check_ans_interpolates_eq ans pts vals ρ hlen hne hnodup hρ

/-- The virtual oracle read on a fiber.

- it is rejected when a fiber point is an interpolation point
- otherwise each point x reads (v - Ans(x)) / Z(x) sum_{t <= |G|} (x r)^t. -/
theorem materialize_virtual_fiber {ζ u0 s : F} {arity : ℕ} (hζ : IsPrimitiveRoot ζ arity)
    (harity : 0 < arity) (row : List EF) (hrow : row.length = arity) (r : EF) (ans pts : List EF) :
    p3_stir.verifier.mirror.materialize_virtual_fiber row (shiftedPowersList ζ u0 arity) s
        (some (finish_ctx r ans pts)) =
      if ∃ l < arity, ι (s * (u0 * ζ ^ l)) ∈ pts then some none
      else some (some ((List.range arity).map fun l =>
        virtualVal r ans pts (ι (s * (u0 * ζ ^ l))) (row.getD l 0))) :=
  by convert materialize_virtual_fiber_eq hζ harity row hrow r ans pts

/-- Off the points, the virtual oracle of an honest round is the next polynomial:

DegCor(d, r, PolyQuotient(PolyFold(f), G), d - |G|). -/
theorem virtual_oracle (f : EF[X]) (k : ℕ) (rFold rComb : EF) (pts ans : List EF) {d : ℕ}
    (hnd : pts.Nodup) (hd : pts.length ≤ d)
    (hans : coeffPoly ans = ansPoly pts.toFinset fun y => (polyFold f k rFold).eval y)
    {x : EF} (hx : x ∉ pts) :
    virtualVal rComb ans pts x ((polyFold f k rFold).eval x) =
      (nextPoly f k rFold rComb pts.toFinset d).eval x :=
  virtualVal_eq_nextPoly f k rFold rComb pts ans hnd hd hans hx

/-- Off G, the next polynomial is DegCor of Quotient.

This is how Construction 5.2 defines the next oracle. -/
theorem next_polynomial (f : EF[X]) (k : ℕ) (rFold rComb : EF) (G : Finset EF) (d : ℕ) (fill : EF → EF)
    {x : EF} (hx : x ∉ G) :
    (nextPoly f k rFold rComb G d).eval x =
      degCor d (d - G.card) rComb
        (quotient (fun y => (polyFold f k rFold).eval y) G (fun y => (polyFold f k rFold).eval y) fill) x :=
  eval_nextPoly f k rFold rComb G d fill hx

/-- Round completeness.

An honest input of degree below k d gives a next polynomial of degree below d. -/
theorem round_completeness (f : EF[X]) {k d : ℕ} (hk : 0 < k) (hf : f.degree < (k * d : ℕ))
    (rFold rComb : EF) (G : Finset EF) (hG : G.card ≤ d) :
    (nextPoly f k rFold rComb G d).degree < d :=
  degree_nextPoly_lt f hk hf rFold rComb G hG

/-! ## The verifier's queries (Construction 5.2) -/

/-- A round-0 query j folds its fiber at gamma / s.

The result is Fold(f, 2^a, gamma) at (s g^j)^(2^a). -/
theorem query_fold_value.initial (G : Gen F) (hG : GenValid G) {a n : ℕ} (ha : a ≤ n)
    (hn : n ≤ G.adicity) {s : F} (hs : s ≠ 0) {j : ℕ} (hj : j < 2 ^ (n - a)) (row : List EF)
    (hrow : row.length = 2 ^ a) (f : EF → EF)
    (hf : ∀ l < 2 ^ a, f (ι s * ι (G.gen n) ^ (j + l * 2 ^ (n - a))) = row.getD l 0) (γ : EF)
    (round : Option ℕ) (q : ℕ) :
    query_fold_value row j (G.gen n) (G.gen n ^ 2 ^ (n - a)) (2 ^ a) s (γ * ι s⁻¹) none round q =
      pure (fold (cosetSet (ι s) (ι (G.gen n)) n) f (2 ^ a) γ ((ι s * ι (G.gen n) ^ j) ^ 2 ^ a)) :=
  query_fold_value_initial G hG ha hn (by decide) hs hj row hrow f hf γ round q

/-- A later query is rejected when its fiber meets the interpolation points.

Otherwise it folds the virtual oracle. -/
theorem query_fold_value.virtual (G : Gen F) (hG : GenValid G) {a n : ℕ} (ha : a ≤ n)
    (hn : n ≤ G.adicity) {s : F} (hs : s ≠ 0) {j : ℕ} (hj : j < 2 ^ (n - a)) (row : List EF)
    (hrow : row.length = 2 ^ a) (r : EF) (ans pts : List EF) (f : EF → EF)
    (hf : ∀ l < 2 ^ a, f (ι s * ι (G.gen n) ^ (j + l * 2 ^ (n - a))) =
      virtualVal r ans pts (ι s * ι (G.gen n) ^ (j + l * 2 ^ (n - a))) (row.getD l 0))
    (γ : EF) (round : Option ℕ) (q : ℕ) :
    query_fold_value row j (G.gen n) (G.gen n ^ 2 ^ (n - a)) (2 ^ a) s (γ * ι s⁻¹)
        (some (finish_ctx r ans pts)) round q =
      if ∃ l < 2 ^ a, ι s * ι (G.gen n) ^ (j + l * 2 ^ (n - a)) ∈ pts then
        throw (StirError.InvalidRoundConsistency round q)
      else pure (fold (cosetSet (ι s) (ι (G.gen n)) n) f (2 ^ a) γ ((ι s * ι (G.gen n) ^ j) ^ 2 ^ a)) :=
  by convert query_fold_value_virtual G hG ha hn (by decide) hs hj row hrow r ans pts f hf γ round q

/-- The fold challenge is gamma / s.

A zero shift panics. -/
theorem set_gamma (γ : EF) (s : F) :
    p3_stir.verifier.mirror.set_gamma γ s = if s = 0 then none else some (γ / ι s) :=
  set_gamma_eq γ s

/-- One fiber folded at gamma / s is Fold(f, 2^a, gamma) at (s g^j)^(2^a).

The domain is L = s <g>, of size 2^(m + a). -/
theorem fold_fiber (G : Gen F) (hG : GenValid G) {a m : ℕ} (hn : m + a ≤ G.adicity) {s : F}
    (hs : s ≠ 0) {j : ℕ} (hj : j < 2 ^ m) (fiber : List EF) (hfib : fiber.length = 2 ^ a) (f : EF → EF)
    (hf : ∀ l < 2 ^ a, f (ι s * ι (G.gen (m + a)) ^ (j + l * 2 ^ m)) = fiber.getD l 0) (γ : EF) :
    p3_stir.utils.mirror.fold_fiber G fiber j m a (γ * ι s⁻¹) =
      some (fold (cosetSet (ι s) (ι (G.gen (m + a))) (m + a)) f (2 ^ a) γ
        ((ι s * ι (G.gen (m + a)) ^ j) ^ 2 ^ a)) :=
  fold_fiber_eq G hG hn (by decide) hs hj fiber hfib f hf γ

/-- Laying out an external source's fibers in draw order never panics, if the source never panics. -/
theorem external_fibers_in_draw_order.no_panic (indices : List ℕ) (arity : ℕ) (round : Option ℕ)
    (source : List ℕ → VM (List (List EF))) (hsrc : ∀ l, (source l).run.isSome) :
    (p3_stir.verifier.mirror.external_fibers_in_draw_order indices arity round source).run.isSome :=
  external_fibers_no_panic indices arity round source hsrc

/-- The query loop records each distinct index once.

Index j sits at its point s^k g_k^j, with one answer per point. -/
theorem fold_queries (G : Gen F) (round : ℕ) (fold_shift : F) (fold_log current_log arity : ℕ)
    (current_shift : F) (fold_beta : EF) (prev_ctx : Option (VirtualRoundContext EF))
    (query_indices : List ℕ) (rows : List (List EF)) (st : QueryState F EF)
    (h : p3_stir.verifier.mirror.fold_queries G round fold_shift fold_log current_log arity
      current_shift fold_beta prev_ctx query_indices rows = pure st) :
    st.seen.Nodup ∧ st.query_points = st.seen.map (fun j => ι fold_shift * ι (G.gen fold_log ^ j)) ∧
      (∀ j ∈ st.seen, j ∈ query_indices) ∧ st.query_answers.length = st.seen.length :=
  fold_queries_seen G round fold_shift fold_log current_log arity current_shift fold_beta prev_ctx
    query_indices rows st h

/-- The query point of index j on L^k is (s g^j)^(2^a). -/
theorem fold_point (G : Gen F) (hN : GenNested G) {a n : ℕ} (ha : a ≤ n) (hn : n ≤ G.adicity)
    (s : F) (j : ℕ) : s ^ 2 ^ a * G.gen (n - a) ^ j = (s * G.gen n ^ j) ^ 2 ^ a :=
  fold_point_eq G hN ha hn s j

/-- A round's geometry:

- the arity is 2^a
- the fold domain is s^(2^a) <g^(2^a)>
- the next domain has half the size, shifted by w.

It panics for a > n or n = 0. -/
theorem round_geometry (w s : F) (n a : ℕ) :
    p3_stir.verifier.mirror.round_geometry w s n a =
      if a ≤ n ∧ 1 ≤ n then some (2 ^ a, s ^ 2 ^ a, n - a, n - 1, s ^ 2 ^ a * w) else none :=
  round_geometry_eq w s n a

/-- A candidate z is kept exactly when both hold:

- z^(2^l) != s^(2^l) for every excluded coset with l > 0
- z is new.

A coset with l = 0 is never excluded. -/
theorem ood_filter (doms : List (F × ℕ)) (h : ∀ d ∈ doms, d.1 ≠ 0) (z : EF) (kept : List EF) :
    ∃ f, OodFilter.new doms = some f ∧
      (f.accepts z kept = true ↔ (∀ i < doms.length, (doms.getD i (1, 0)).2 = 0 ∨
          z ^ 2 ^ (doms.getD i (1, 0)).2 ≠ ι (doms.getD i (1, 0)).1 ^ 2 ^ (doms.getD i (1, 0)).2) ∧
        z ∉ kept) :=
  oodFilter_accepts_eq doms h z kept

/-- z^(2^l) = s^(2^l) exactly when z lies in s <g> of size 2^l. -/
theorem coset_membership {ω s : F} {l : ℕ} (hω : IsPrimitiveRoot ω (2 ^ l)) (hs : s ≠ 0) (z : EF) :
    z ^ 2 ^ l = ι s ^ 2 ^ l ↔ ∃ i < 2 ^ l, z = ι (s * ω ^ i) :=
  pow_eq_iff_mem_coset hω hs z

/-- A point of the next domain is neither an accepted out-of-domain point nor a query point.

So the next round never reads the virtual oracle at an interpolation point. -/
theorem next_domain_avoids_points (G : Gen F) (hG : GenValid G) {w s : F} (hw : w ^ 2 ^ G.adicity ≠ 1)
    (hs : s ≠ 0) {a n : ℕ} (ha : a ≤ n) (hn : n ≤ G.adicity) (ood qs : List EF)
    (hood : ∀ z ∈ ood, z ^ 2 ^ (n - 1) ≠ ι (s ^ 2 ^ a * w) ^ 2 ^ (n - 1))
    (hq : ∀ y ∈ qs, ∃ j, y = ι (s ^ 2 ^ a * G.gen (n - a) ^ j)) (i : ℕ) :
    ι (s ^ 2 ^ a * w * G.gen (n - 1) ^ i) ∉ ood ++ qs :=
  next_point_not_mem G hG hw hs ha hn ood qs hood hq i

/-! ## The verifier never panics on a malformed answer polynomial -/

/-- The sent answer polynomial is accepted exactly when both hold:

- it has at most the maximum number of coefficients
- it is empty only when that maximum is 0. -/
theorem check_ans_length (round : ℕ) (ans : List EF) (max : ℕ) :
    p3_stir.verifier.mirror.check_ans_length round ans max = pure () ↔
      ans.length ≤ max ∧ (ans ≠ [] ∨ max = 0) :=
  check_ans_length_ok round ans max

/-- The compact encoding on distinct points rebuilds the interpolant. -/
theorem resolve_ans_polynomial.compact (round : ℕ) (points values : List EF)
    (hlen : points.length = values.length) (hnd : points.Nodup) (hne : points ≠ []) :
    ∃ cs, resolve_ans_polynomial round true [] points values = pure cs ∧
      coeffPoly cs = Lagrange.interpolate (range points.length) (fun i => points.getD i 0)
        (fun i => values.getD i 0) :=
  resolve_compact_eq round points values hlen hnd hne

/-- Resolving the answer polynomial never panics, whatever the proof carries. -/
theorem resolve_ans_polynomial.no_panic (round : ℕ) (compact : Bool) (sent points values : List EF) :
    (resolve_ans_polynomial round compact sent points values).run.isSome :=
  resolve_ans_polynomial_no_panic round compact sent points values

/-! ## BabyBear -/

/-- BabyBear's generator table is primitive and nested up to 27.

Its generator lies outside the subgroup of order 2^27. -/
theorem babyBear.facts :
    ∃ t g, Plonky3Lean.Spec.BabyBear.TwoAdicParams.TWO_ADIC_GENERATORS = .ok t ∧
      Plonky3Lean.Spec.BabyBear.FieldParams.MONTY_GEN = .ok g ∧
      (genOfTable (t.val.map Plonky3Lean.Spec.BabyBear.toField)).adicity = 27 ∧
      GenValid (genOfTable (t.val.map Plonky3Lean.Spec.BabyBear.toField)) ∧
      GenNested (genOfTable (t.val.map Plonky3Lean.Spec.BabyBear.toField)) ∧
      Plonky3Lean.Spec.BabyBear.toField g ^ 2 ^ 27 ≠ 1 :=
  Plonky3Lean.Proofs.Commit.babyBear_facts

end Plonky3Lean.Claims.Stir
