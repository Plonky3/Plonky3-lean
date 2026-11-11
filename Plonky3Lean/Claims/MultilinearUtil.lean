module

public import Plonky3Lean.Proofs.MultilinearUtil.Packing
public import Plonky3Lean.Proofs.MultilinearUtil.Extracted
public import CompPoly.Fields.BabyBear.Ext4

@[expose] public section

/-!
# p3-multilinear-util: claims

The equality polynomial of two points is extracted, generic over the field traits.

The rest of the crate is transcribed over a field.

The transcription claims are stated at BabyBear F and its quartic extension EF = F[X] / (X^4 - 11).

The specification is the multilinear extension of a table, Thaler, Section 3.5:

```text
    f~(r) = sum_{b in {0,1}^n} eq(b, r) f(b)
    eq(x, r) = prod_i (x_i r_i + (1 - x_i)(1 - r_i))
```

Entry b of a table is the vertex whose coordinate 0 is the most significant bit of b.

A packed value has W = 2^w lanes.

Every claim holds for every w, every thread count and every task split.
-/

open Plonky3Lean.Spec.MultilinearUtil Plonky3Lean.Proofs.MultilinearUtil MvPolynomial Finset
open p3_multilinear_util.mirror p3_multilinear_util.point.mirror p3_multilinear_util.eq_batch.mirror
open p3_multilinear_util.poly.mirror p3_multilinear_util.split_eq.mirror

set_option linter.unusedSectionVars false

namespace Plonky3Lean.Claims.MultilinearUtil

local notation "F" => BabyBear.Field
local notation "EF" => BabyBear.Ext4

/-! ## The multilinear extension -/

/-- Lemma 3.6: the extension has degree at most 1 in each variable. -/
theorem mle_isMultilinear (f : List EF) (n : ℕ) : IsMultilinear (mlePoly f n) :=
  mlePoly_isMultilinear f n

/-- The extension agrees with the table on the cube. -/
theorem mle_vertex (f : List EF) {n b : ℕ} (hb : b < 2 ^ n) :
    MvPolynomial.eval (vertexFn n b) (mlePoly f n) = f.getD b 0 :=
  eval_mlePoly_vertex f hb

/-- Lemma 3.6: the extension is unique.

A polynomial of degree at most 1 in each variable that agrees with the table on the cube is the extension. -/
theorem mle_unique {n : ℕ} (f : List EF) {p : MvPolynomial (Fin n) EF} (hp : IsMultilinear p)
    (hf : ∀ b < 2 ^ n, MvPolynomial.eval (vertexFn n b) p = f.getD b 0) : p = mlePoly f n :=
  eq_mlePoly f hp hf

/-- The extension at a point is the sum of eq(b, r) f(b). -/
theorem mle_eval (f : List EF) {n : ℕ} (r : Fin n → EF) :
    MvPolynomial.eval r (mlePoly f n) = mle f (List.ofFn r) :=
  eval_mlePoly f r

/-- Coordinate 0 is the top bit.

The table of (c, r) is the table of r scaled by 1 - c, followed by the table of r scaled by c. -/
theorem eqTable_top_bit (c : EF) (r : List EF) :
    eqTable (c :: r) = (eqTable r).map (· * (1 - c)) ++ (eqTable r).map (· * c) :=
  eqTable_cons c r

/-- The last coordinate is the bottom bit.

Entry 2 b + e of the table of r ++ [c] is entry b of the table of r, times eq(e, c). -/
theorem eqTable_bottom_bit (c : EF) (r : List EF) (b : ℕ) (e : Bool) :
    eq (vertex (r.length + 1) (Nat.bit e b)) (r ++ [c]) =
      eq (vertex r.length b) r * (if e then c else 1 - c) :=
  getElem_eqTable_snoc c r b e

/-! ## Points -/

/-- The big-endian equality table is the table of the point, coordinate 0 on the top bit.

This holds for every packing width and task split. -/
theorem equality_weights_msb (W task_len : ℕ) (p : List EF) (h : p.length < 64) :
    Point.equality_weights_msb W task_len p = some (eqTable p) :=
  equality_table_eq W task_len p .Msb h

/-- The little-endian equality table is the table of the reversed point, coordinate 0 on the bottom bit. -/
theorem equality_weights_lsb (W task_len : ℕ) (p : List EF) (h : p.length < 64) :
    Point.equality_weights_lsb W task_len p = some (eqTable p.reverse) :=
  equality_table_eq W task_len p .Lsb h

/-- Both equality tables panic when 2^n overflows a 64-bit word. -/
theorem equality_weights.panics (W task_len : ℕ) (p : List EF) (h : 64 ≤ p.length) :
    Point.equality_weights_msb W task_len p = none ∧ Point.equality_weights_lsb W task_len p = none :=
  ⟨equality_table_panics W task_len p .Msb h, equality_table_panics W task_len p .Lsb h⟩

/-- The equality weight at a vertex b is eq(b, p) for b < 2^n, and nothing above. -/
theorem equality_at_vertex (p : List EF) {v : ℕ} (hv : v < 2 ^ 64) :
    Point.equality_at_vertex p v =
      if v < 2 ^ p.length then some (eq (vertex p.length v) p) else none :=
  equality_at_vertex_eq p hv

/-- The hypercube point of a value is its vertex, coordinate 0 on the top bit. -/
theorem hypercube {value n : ℕ} (hn : n < 64) (hv : value < 2 ^ n) :
    Point.hypercube value n = some (vertex n value : List EF) :=
  hypercube_eq hn hv

/-- The hypercube point panics for a value >= 2^n, and for n >= 64. -/
theorem hypercube.panics {value n : ℕ} (h : 64 ≤ n ∨ 2 ^ n ≤ value) :
    Point.hypercube value n = (none : Option (List EF)) :=
  hypercube_panics h

/-- Expanding a univariate point y gives coordinate i equal to y^(2^(n - 1 - i)). -/
theorem expand_from_univariate (y : EF) (n : ℕ) :
    Point.expand_from_univariate y n = (List.range n).map fun i => y ^ 2 ^ (n - 1 - i) :=
  expand_from_univariate_eq y n

/-- At the expanded point, the polynomial with coefficients c evaluates to sum_b c_b y^b.

The index b is read big-endian. -/
theorem expand_from_univariate.univariate (c : List EF) (y : EF) (n : ℕ) :
    MvPolynomial.eval (fun i : Fin n => (Point.expand_from_univariate y n).getD i 0)
      (coeffPoly c n) = ∑ b ∈ range (2 ^ n), c.getD b 0 * y ^ b :=
  eval_coeffPoly_expand c y n

/-- The equality evaluation is eq(p, q), for a base point and an extension point of the same length. -/
theorem eval_eq {p : List F} {q : List EF} (h : p.length = q.length) :
    Point.eval_eq p q = some (eq (p.map (algebraMap F EF)) q) :=
  eval_eq_eq h

/-- The equality evaluation panics on points of different lengths. -/
theorem eval_eq.panics {p : List F} {q : List EF} (h : p.length ≠ q.length) :
    Point.eval_eq p q = none :=
  eval_eq_panics h

/-- The select evaluation is the extension, at the point, of the table of the powers var^b. -/
theorem eval_select (var : F) (point : List EF) :
    Point.eval_select var point = mle (powTable (algebraMap F EF var) point.length) point :=
  eval_select_eq var point

/-- The successor evaluation splits into completed and boundary weights.

They add up to sum_x eq(x, p) eq(succ(x), r), with the last vertex repeated. -/
theorem eval_next (p r : List F) (h : p.length = r.length) :
    ∃ c d o, Point.eval_next p r = some (c, d, o) ∧
      d + o = ∑ x ∈ range (2 ^ p.length),
        eq (vertex p.length x) p * eq (vertex p.length (succRepeat p.length x)) r :=
  ⟨_, _, _, eval_next_eq p r h, nextDone_add_nextOmega p r⟩

/-- The successor evaluation panics on a point and a row of different lengths. -/
theorem eval_next.panics (p r : List F) (h : p.length ≠ r.length) : Point.eval_next p r = none :=
  eval_next_panics p r h

/-! ## Batched equality tables -/

/-- The batched equality table has entry x equal to sum_i g_i eq(x, z_i).

It is written over the output or added to it.

This holds for every packing width and thread count. -/
theorem eval_eq_batch (w T : ℕ) (initialized : Bool) {m : ℕ} (hm : 0 < m) (rows : List (List EF))
    (out g : List EF) (hg : g.length = m) (hrows : ∀ r ∈ rows, m ≤ r.length)
    (hout : out.length = 2 ^ rows.length) (x : ℕ) :
    ∃ res, p3_multilinear_util.eq_batch.mirror.eval_eq_batch w T initialized m rows out g = some res ∧
      res.getD x 0 = (if initialized then out.getD x 0 else 0) + ∑ i ∈ range m,
        g.getD i 0 * (eqTable (col rows i)).getD x 0 := by
  refine ⟨_, eval_eq_batch_eq w T initialized hm rows out g hg hrows hout, ?_⟩
  have hb := getD_bt rows g (fun r hr => hg ▸ hrows r hr) x
  simp only [Algebra.algebraMap_self, RingHom.coe_id, List.map_id] at hb
  rw [← hg, ← hb]
  cases initialized
  · simp [addOrSet]
  · by_cases hx : x < 2 ^ rows.length
    · simp [addOrSet, List.getD_eq_getElem?_getD, List.getElem?_zipWith,
        List.getElem?_eq_getElem (show x < out.length by omega),
        List.getElem?_eq_getElem (show x < (bt rows g).length by simpa using hx)]
    · simp only [addOrSet, ↓reduceIte, List.getD_eq_getElem?_getD]
      rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (show out.length ≤ x by omega),
        List.getElem?_eq_none (show (bt rows g).length ≤ x by simp; omega)]
      simp

/-- The same batched table, for base-field points and extension weights. -/
theorem eval_eq_base_batch (w T : ℕ) (initialized : Bool) {m : ℕ} (hm : 0 < m)
    (rows : List (List F)) (out g : List EF) (hg : g.length = m) (hrows : ∀ r ∈ rows, m ≤ r.length)
    (hout : out.length = 2 ^ rows.length) :
    p3_multilinear_util.eq_batch.mirror.eval_eq_base_batch w T initialized m rows out g =
      some (addOrSet initialized out (bt rows g)) :=
  eval_eq_base_batch_eq w T initialized hm rows out g hg hrows hout

/-- The batched table, entry by entry: sum_i g_i eq(x, z_i), with the base points mapped into EF. -/
theorem batched_table (rows : List (List F)) (g : List EF) (hg : ∀ r ∈ rows, g.length ≤ r.length)
    (x : ℕ) : (bt rows g).getD x 0 = ∑ i ∈ range g.length,
      g.getD i 0 * (eqTable ((col rows i).map (algebraMap F EF))).getD x 0 :=
  getD_bt rows g hg x

/-- With no point, the output comes back untouched.

This holds even when it should be overwritten with zeros. -/
theorem eval_eq_batch.empty (w T : ℕ) (initialized : Bool) (rows : List (List EF)) (out : List EF) :
    p3_multilinear_util.eq_batch.mirror.eval_eq_batch w T initialized 0 rows out [] = some out := by
  simp [p3_multilinear_util.eq_batch.mirror.eval_eq_batch, eval_eq_batch_common]

/-! ## Polynomials -/

/-- The table built from a point holds scale times eq(point, x) at every x. -/
theorem new_from_point (w T : ℕ) (point : List EF) (s : EF) (h : point.length < 64) :
    Poly.new_from_point w T point s = some ((eqTable point).map (s * ·)) :=
  new_from_point_eq w T point s h

/-- The table built from a point panics when 2^n overflows a 64-bit word. -/
theorem new_from_point.panics (w T : ℕ) (point : List EF) (s : EF) (h : 64 ≤ point.length) :
    Poly.new_from_point w T point s = none :=
  new_from_point_panics w T point s h

/-- The successor table has entry y equal to the sum of eq(x, p) over the x whose successor is y.

The last vertex is its own successor. -/
theorem new_next_from_point (w T : ℕ) (p : List EF) (h : p.length < 64) :
    Poly.new_next_from_point w T p = some (nextTable p) :=
  new_next_from_point_eq w T p h

/-- The extension of the successor table is the sum of the completed and boundary weights. -/
theorem nextTable_eval_next (p r : List EF) (h : r.length = p.length) :
    ∃ c d o, Point.eval_next p r = some (c, d, o) ∧ mle (nextTable p) r = d + o :=
  ⟨_, _, _, eval_next_eq p r h.symm, mle_nextTable p r h⟩

/-- The recursive evaluation is the extension.

This holds for a table of 2^n entries and a point of n coordinates. -/
theorem eval_multilinear_recursive (point : List EF) (evals : List F)
    (h : evals.length = 2 ^ point.length) :
    p3_multilinear_util.poly.mirror.eval_multilinear_recursive evals point =
      some (mle (evals.map (algebraMap F EF)) point) :=
  eval_rec_eq point evals h

/-- In a release build, a short point is padded with zeros in front.

This holds for a point of k <= 4 coordinates and a table of 2^n entries, with k <= n. -/
theorem eval_multilinear_recursive.short (evals : List F) (point : List EF) {n : ℕ}
    (hk : point.length ≤ 4) (hn : point.length ≤ n) (h : evals.length = 2 ^ n) :
    p3_multilinear_util.poly.mirror.eval_multilinear_recursive evals point =
      some (mle (evals.map (algebraMap F EF)) (List.replicate (n - point.length) 0 ++ point)) :=
  eval_rec_short evals point hk hn h

/-- A point of k <= 4 coordinates on a table shorter than 2^k panics. -/
theorem eval_multilinear_recursive.long (evals : List F) (point : List EF) (hk : point.length ≤ 4)
    (h : evals.length < 2 ^ point.length) :
    p3_multilinear_util.poly.mirror.eval_multilinear_recursive evals point = none :=
  eval_rec_long_panics evals point hk h

/-- Evaluating a base table gives the extension at the point.

This holds for every threshold, packing width and thread count. -/
theorem eval_base (thr w T : ℕ) (poly : List F) (point : List EF) (h : point.length < 64)
    (hp : poly.length = 2 ^ point.length) :
    p3_multilinear_util.split_eq.mirror.Poly.eval_base thr w T poly point =
      some (mle (poly.map (algebraMap F EF)) point) :=
  poly_eval_base_eq thr w T poly point h hp

/-- Evaluating a table over the extension gives the extension at the point. -/
theorem eval_ext (thr w T : ℕ) (poly point : List EF) (h : point.length < 64)
    (hp : poly.length = 2 ^ point.length) :
    p3_multilinear_util.split_eq.mirror.Poly.eval_ext thr w T poly point = some (mle poly point) :=
  poly_eval_ext_eq thr w T poly point h hp

/-- Below the threshold, a point with fewer coordinates, at most four, does not panic.

It is evaluated as if padded with zeros in front. -/
theorem eval_base.short (thr w T : ℕ) (poly : List F) (point : List EF) {n : ℕ}
    (hk : point.length ≤ 4) (hthr : point.length < thr) (hn : point.length ≤ n)
    (hp : poly.length = 2 ^ n) :
    p3_multilinear_util.split_eq.mirror.Poly.eval_base thr w T poly point =
      some (mle (poly.map (algebraMap F EF)) (List.replicate (n - point.length) 0 ++ point)) :=
  poly_eval_base_short thr w T poly point hk hthr hn hp

/-- From the threshold on, a point with another number of variables panics. -/
theorem eval_base.panics (thr w T : ℕ) (poly : List F) (point : List EF) {n : ℕ}
    (hthr : thr ≤ point.length) (h : point.length < 64) (hp : poly.length = 2 ^ n)
    (hn : n ≠ point.length) :
    p3_multilinear_util.split_eq.mirror.Poly.eval_base thr w T poly point = none :=
  poly_eval_base_mismatch_panics thr w T poly point hthr h hp hn

/-- Fixing the first variable in place gives the table of the restriction to x_0 = r, half as long. -/
theorem fix_prefix_var_mut (evals : List EF) (r : F) {n : ℕ} (h : evals.length = 2 ^ (n + 1)) :
    ∃ res, Poly.fix_prefix_var_mut evals r = some res ∧ res.length = 2 ^ n ∧
      ∀ r' : List EF, r'.length = n → mle res r' = mle evals (algebraMap F EF r :: r') :=
  fix_prefix_var_mut_spec evals r h

/-- Fixing the first variable in place panics on a constant. -/
theorem fix_prefix_var_mut.panics (evals : List EF) (r : F) (h : evals.length = 1) :
    Poly.fix_prefix_var_mut evals r = none :=
  fix_prefix_var_mut_panics evals r h

/-- Summing out the first variable in place gives the table of p(0, x) + p(1, x). -/
theorem sum_prefix_var_mut (evals : List EF) {n : ℕ} (h : evals.length = 2 ^ (n + 1)) :
    (Poly.sum_prefix_var_mut evals).length = 2 ^ n ∧ ∀ r' : List EF, r'.length = n →
      mle (Poly.sum_prefix_var_mut evals) r' = mle evals (0 :: r') + mle evals (1 :: r') :=
  sum_prefix_var_mut_spec evals h

/-- Fixing the first variable maps a base table to the restriction to x_0 = r, over the extension. -/
theorem fix_prefix_var (evals : List F) (r : EF) {n : ℕ} (h : evals.length = 2 ^ (n + 1)) :
    ∃ res, Poly.fix_prefix_var evals r = some res ∧ res.length = 2 ^ n ∧
      ∀ r' : List EF, r'.length = n → mle res r' = mle (evals.map (algebraMap F EF)) (r :: r') :=
  fix_prefix_var_spec evals r h

/-- Fixing the first variable at one index gives that entry of the restriction.

It panics past the residual cube. -/
theorem fix_prefix_var_at (evals : List F) (r : EF) {index : ℕ}
    (hi : index + evals.length / 2 < evals.length) :
    Poly.fix_prefix_var_at evals r index = some ((1 - r) * algebraMap F EF (evals.getD index 0) +
      r * algebraMap F EF (evals.getD (index + evals.length / 2) 0)) :=
  fix_prefix_var_at_eq evals r hi

/-- Fixing the last variable in place gives the restriction to x_{n-1} = r.

This holds whichever path the cost model takes. -/
theorem fix_suffix_var_mut (split : Bool) (evals : List EF) (r : F) {n : ℕ}
    (h : evals.length = 2 ^ (n + 1)) :
    ∃ res, Poly.fix_suffix_var_mut split evals r = some res ∧
      ∀ r' : List EF, r'.length = n → mle res r' = mle evals (r' ++ [algebraMap F EF r]) := by
  refine ⟨_, fix_suffix_var_mut_eq split evals r (N := 2 ^ n) (by rw [h, pow_succ]; ring)
    (by positivity), fun r' hr => ?_⟩
  rw [← hr, mle_pairFold]

/-- Fixing the last variable maps a base table to the restriction to x_{n-1} = r, over the extension. -/
theorem fix_suffix_var (evals : List F) (r : EF) {n : ℕ} (h : evals.length = 2 ^ (n + 1)) :
    ∃ res, Poly.fix_suffix_var evals r = some res ∧
      ∀ r' : List EF, r'.length = n → mle res r' = mle (evals.map (algebraMap F EF)) (r' ++ [r]) := by
  refine ⟨_, fix_suffix_var_eq evals r (N := 2 ^ n) (by rw [h, pow_succ]; ring) (by positivity)
    ⟨n, rfl⟩, fun r' hr => ?_⟩
  rw [← hr, mle_pairFold]

/-- The packed table built from a point unpacks to scale times eq(point, x).

The lanes are the last log_2 W variables. -/
theorem new_packed_from_point (w T : ℕ) (point : List EF) (s : EF) (hs : s ≠ 0)
    (hw : w ≤ point.length) :
    ∃ P, Poly.new_packed_from_point w T point s = some P ∧ to_ext_iter P = (eqTable point).map (s * ·) :=
  ⟨_, new_packed_from_point_eq_aTable w T point s hs hw, unpack_new_packed w point s hw⟩

/-- The packed table built from a point panics on a zero scale, and on fewer than log_2 W coordinates. -/
theorem new_packed_from_point.panics (w T : ℕ) (point : List EF) (s : EF) (h : s = 0 ∨ point.length < w) :
    Poly.new_packed_from_point w T point s = none := by
  rcases h with rfl | h <;> simp [Poly.new_packed_from_point, *]

/-- Packing, then unpacking, gives the table back. -/
theorem pack_unpack (w : ℕ) (evals : List EF) {n : ℕ} (h : evals.length = 2 ^ n) (hw : w ≤ n) :
    ∃ P, Poly.pack w evals = some P ∧ P.length = 2 ^ (n - w) ∧ Poly.unpack P = evals :=
  Plonky3Lean.Proofs.MultilinearUtil.pack_unpack w evals h hw

/-- Fixing the first variable into a packed table unpacks to the scalar fold of the first variable. -/
theorem fix_prefix_var_to_packed (w : ℕ) (evals : List F) (r : EF) {n : ℕ}
    (h : evals.length = 2 ^ n) (hw : w < n) :
    ∃ res, Poly.fix_prefix_var_to_packed w evals r = some res ∧
      Poly.unpack res = List.zipWith (fun a0 a1 => r * algebraMap F EF (a1 - a0) + algebraMap F EF a0)
        (evals.take (evals.length / 2)) (evals.drop (evals.length / 2)) :=
  fix_prefix_var_to_packed_spec w evals r h hw

/-! ## The factored table -/

/-- Evaluating with the factored table gives scale times the extension at the point.

This holds when the scale is 1 or the point is not empty. -/
theorem split_eval_base (w T : ℕ) (point : List EF) (s : EF) (h : point.length < 64)
    (poly : List F) (hp : poly.length = 2 ^ point.length) (hs : s = 1 ∨ 0 < point.length) :
    (SplitEq.new_packed w T point s).bind (fun se => se.eval_base poly) =
      some (s * mle (poly.map (algebraMap F EF)) point) :=
  Plonky3Lean.Proofs.MultilinearUtil.split_eval_base w T point s h poly hp hs

/-- A constant polynomial is returned unscaled, whatever the scale of the table. -/
theorem split_eval_base.constant (w T : ℕ) (s : EF) (c : F) :
    (SplitEq.new_packed w T [] s).bind (fun se => se.eval_base [c]) = some (algebraMap F EF c) :=
  split_eval_base_constant w T s c

/-- Compressing the suffix gives entry j equal to scale times the extension of block j at the point.

This holds for every basis of EF over F. -/
theorem compress_suffix_into {D : ℕ} (w T : ℕ) (b : Module.Basis (Fin D) F EF) (point : List EF)
    (s : EF) (h : point.length < 64) (poly : List F) (out : List EF) {k : ℕ}
    (hp : poly.length = 2 ^ k * 2 ^ point.length) (ho : out.length = 2 ^ k) :
    (SplitEq.new_packed w T point s).bind (fun se => se.compress_suffix_into b out poly) =
      some ((List.range (2 ^ k)).map fun j =>
        s * mle ((chunkAt (2 ^ point.length) poly j).map (algebraMap F EF)) point) :=
  split_compress_suffix w T b point s h poly out hp ho

/-- Accumulating the factored table adds weight times scale times eq(point, x) to every entry.

An absent weight counts as 1. -/
theorem accumulate_into (w T : ℕ) (point : List EF) (s : EF) (h : point.length < 64)
    (out : List EF) (hout : out.length = 2 ^ point.length) (ws : Option EF) :
    (SplitEq.new_packed w T point s).bind (fun se => se.accumulate_into out ws) =
      some (List.zipWith (fun o t => o + ws.getD 1 * t) out ((eqTable point).map (s * ·))) :=
  split_accumulate_into w T point s h out hout ws

/-- Materializing the factored table gives the table of scale times eq(point, x). -/
theorem materialize (w T : ℕ) (point : List EF) (s : EF) (h : point.length < 64) :
    (SplitEq.new_packed w T point s).bind (fun se => se.materialize) =
      some ((eqTable point).map (s * ·)) :=
  split_materialize w T point s h

/-! ## The extracted equality polynomial

Each claim holds for any base field K, any extension L of it, and any instances of the field traits.

It assumes one thing of those instances: each member the code calls computes the operation it names.
-/

section Extracted

open CoreModels Aeneas Aeneas.Std

variable {K L : Type} [Field K] [Field L] [Algebra K L]
  {inst : p3_field.field.Field K} {einst : p3_field.field.ExtensionField L K}

/-- The shipped equality polynomial returns what its transcription returns, panics included. -/
theorem point.eval_eq.eq_mirror (h : ExtComputes inst einst) (p : Slice K) (q : Slice L) :
    p3_multilinear_util.hax_roots.eval_eq inst einst p q = ofOption (Point.eval_eq p.val q.val) :=
  eval_eq_eq_mirror h p q

/-- On points of the same length, the shipped equality polynomial is the product over i of

```text
    p_i q_i + (1 - p_i)(1 - q_i)
```

with each base coordinate p_i mapped into the extension. -/
theorem point.eval_eq.eq_spec (h : ExtComputes inst einst) {p : Slice K} {q : Slice L}
    (hl : p.val.length = q.val.length) :
    p3_multilinear_util.hax_roots.eval_eq inst einst p q =
      .ok (eq (p.val.map (algebraMap K L)) q.val) := by
  rw [eval_eq_eq_mirror h, eval_eq_eq hl, ofOption]

/-- The shipped equality polynomial panics exactly on points of different lengths. -/
theorem point.eval_eq.panics (h : ExtComputes inst einst) {p : Slice K} {q : Slice L}
    (hl : p.val.length ≠ q.val.length) :
    p3_multilinear_util.hax_roots.eval_eq inst einst p q = .fail .panic := by
  rw [eval_eq_eq_mirror h, eval_eq_panics hl, ofOption]

end Extracted

end Plonky3Lean.Claims.MultilinearUtil
