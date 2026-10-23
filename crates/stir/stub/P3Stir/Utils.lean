/-
Transcriptions of p3-stir's polynomial utilities (stir/src/utils.rs).

A polynomial is its coefficient list, constant term first.

Domain points, shifts and twiddles live in the base field F, and values and challenges in the extension EF.
-/
module

public import P3Stir.Model

@[expose] public section

namespace p3_stir.utils.mirror

open p3_stir.mirror p3_dft.mirror

section OneField

variable {K : Type _} [Field K] [DecidableEq K]

/-- eval_poly: Horner's rule, from the top coefficient down. -/
def eval_poly (poly : List K) (point : K) : K :=
  poly.reverse.foldl (fun acc coeff => acc * point + coeff) 0

/-- eval_poly_parallel: Horner on each chunk of the given size, then Horner over the chunk values with ratio point^chunk_size.

The cost model picks the chunk size; a chunk spanning the whole polynomial falls back to eval_poly. -/
def eval_poly_parallel (chunk_size : ℕ) (poly : List K) (point : K) : Option K :=
  if chunk_size ≥ poly.length then some (eval_poly poly point)
  else do
    let point_pow_chunk := point ^ chunk_size
    let cs ← chunks chunk_size poly
    some ((cs.map fun chunk => eval_poly chunk point).reverse.foldl
      (fun acc chunk_val => acc * point_pow_chunk + chunk_val) 0)

/-- divide_by_linear: synthetic division by X - point, which asserts the polynomial is not empty. -/
def divide_by_linear (poly : List K) (point : K) : Option (List K × K) :=
  if poly = [] then none
  else
    let n := poly.length
    let (quotient, carry) := (List.range (n - 1)).reverse.foldl
      (fun (st : List K × K) i =>
        let carry := poly.getD (i + 1) 0 + st.2 * point
        (st.1.set i carry, carry))
      (List.replicate (n - 1) 0, 0)
    some (quotient, poly.getD 0 0 + carry * point)

/-- add_polys: entry i is a_i + b_i, a missing entry read as zero. -/
def add_polys (a b : List K) : List K :=
  (List.range (max a.length b.length)).map fun i =>
    (if i < a.length then a.getD i 0 else 0) + (if i < b.length then b.getD i 0 else 0)

/-- eval_degree_correction: value times 1 + step + ... + step^gap, step = point r_comb, in closed form. -/
def eval_degree_correction (value point r_comb : K) (gap : ℕ) : Option K :=
  let step := point * r_comb
  if step = 1 then some (value * ((gap + 1 : ℕ) : K))
  else do
    let inv ← inverse (1 - step)
    some (value * ((1 - step ^ (gap + 1)) * inv))

/-- vanishing_poly_from_roots: multiply 1 by X - root for each root, updating the coefficients in place. -/
def vanishing_poly_from_roots (roots : List K) : List K :=
  roots.foldl (fun coeffs root =>
    let coeffs := coeffs ++ [0]
    let coeffs := (List.range (coeffs.length - 1)).reverse.foldl
      (fun cs i' => let i := i' + 1; cs.set i (cs.getD (i - 1) 0 - cs.getD i 0 * root)) coeffs
    coeffs.set 0 (-(coeffs.getD 0 0) * root)) [1]

/-- The distinctness assertions of interpolate_poly: points i and j differ for every j < i. -/
def allDistinct (points : List K) : Bool :=
  (List.range points.length).all fun i => (List.range i).all fun j =>
    points.getD i 0 != points.getD j 0

/-- interpolate_poly: Newton's divided differences, expanded into coefficients, trailing zeros removed down to one.

It asserts equal lengths and distinct points. -/
def interpolate_poly (points values : List K) : Option (List K) :=
  if points.length ≠ values.length then none
  else if !allDistinct points then none
  else
    let n := points.length
    if n = 0 then some []
    else do
      let denominators := (List.range (n - 1)).flatMap fun k' => let k := k' + 1;
        (List.range (n - k)).map fun i' => let i := i' + k; points.getD i 0 - points.getD (i - k) 0
      let denominator_inverses ← batchInv denominators
      -- The table of divided differences, one stage per k.
      let (dd, _) := (List.range (n - 1)).foldl (fun (st : List K × ℕ) k' =>
        let k := k' + 1
        let width := n - k
        let inverses := (denominator_inverses.drop st.2).take width
        let dd := (List.range (n - k)).reverse.foldl (fun dd i' => let i := i' + k;
          dd.set i ((dd.getD i 0 - dd.getD (i - 1) 0) * inverses.getD (i - k) 0)) st.1
        (dd, st.2 + width)) (values, 0)
      -- The Newton expansion, one basis polynomial at a time.
      let coeffs := (List.replicate n (0 : K)).set 0 (dd.getD 0 0)
      let (coeffs, _) := (List.range (n - 1)).foldl (fun (st : List K × List K) k' =>
        let k := k' + 1
        let pk := points.getD (k - 1) 0
        let basis := st.2
        let new_basis := (List.range basis.length).foldl (fun nb i =>
          let b := basis.getD i 0
          let nb := nb.set (i + 1) (nb.getD (i + 1) 0 + b)
          nb.set i (nb.getD i 0 - b * pk)) (List.replicate (basis.length + 1) 0)
        let coeffs := (List.range new_basis.length).foldl (fun cs i =>
          cs.set i (cs.getD i 0 + dd.getD k 0 * new_basis.getD i 0)) st.1
        (coeffs, new_basis)) (coeffs, [1])
      some (stripZeros coeffs)
where
  /-- Pop the last coefficient while it is zero and more than one remains. -/
  stripZeros (l : List K) : List K :=
    (List.range l.length).foldl (fun cs _ =>
      if cs.getLast? = some 0 ∧ cs.length > 1 then cs.dropLast else cs) l

/-- check_ans_interpolates: compare ans(rho) with the barycentric interpolant at rho, cross-multiplied. -/
def check_ans_interpolates (ans points values : List K) (rho : K) : Option Bool :=
  if points.length ≠ values.length then some false
  else if points = [] then some (ans.all fun c => c = 0)
  else if rho ∈ points then some false
  else do
    let n := points.length
    let weightDenoms := (List.range n).map fun i =>
      ((List.range n).filter (· ≠ i)).foldl (fun p j => p * (points.getD i 0 - points.getD j 0)) 1
    let denominators := weightDenoms ++ points.map fun y => rho - y
    if 0 ∈ denominators.take n then some false
    else do
      let inverses ← batchInv denominators
      let weights := inverses.take n
      let diff_invs := inverses.drop n
      let (numerator, denominator) := (List.range n).foldl (fun (st : K × K) i =>
        let term := weights.getD i 0 * diff_invs.getD i 0
        (st.1 + term * values.getD i 0, st.2 + term)) (0, 0)
      some (decide (eval_poly ans rho * denominator = numerator))

end OneField

section TwoFields

variable {F EF : Type _} [Field F] [Field EF] [Algebra F EF] [DecidableEq F] [DecidableEq EF]

/-- An extension element times a base element. -/
local infixl:70 " ⋆ " => fun (a : EF) (b : F) => a * algebraMap F EF b

/-- combine_on_coset: sum_i r_i f_i(x) (1 + s + ... + s^gap_i), s = r_comb x, at every point x of shift <g>.

The geometric sums are swept in chunks of c and divided by 1 - s in one batch inversion; the one lane where s = 1, if any, is given its closed form gap_i + 1 afterwards. -/
def combine_on_coset (c : ℕ) (G : Gen F) (groups : List (EF × ℕ × List EF)) (r_comb : EF)
    (shift : F) (log_domain : ℕ) : Option (List EF) := do
  let n := 2 ^ log_domain
  let g ← G.get log_domain
  let step_start := r_comb ⋆ shift
  let denoms : List EF := (chunkSweep c n step_start (algebraMap F EF g)).map fun step => 1 - step
  let degenerate := denoms.findIdx? (· = 0)
  let denoms := match degenerate with
    | some p => denoms.set p 1
    | none => denoms
  let inv_denoms ← batchInv denoms
  let result ← groups.foldlM (fun (result : List EF) (grp : EF × ℕ × List EF) =>
    let (r_i, gap, values) := grp
    if values.length ≠ n then none
    else
      let g_hi := g ^ (gap + 1)
      let r_step_start_hi := r_i * step_start ^ (gap + 1)
      let sweep := chunkSweep c n r_step_start_hi (algebraMap F EF g_hi)
      some ((List.range n).map fun p =>
        result.getD p 0 + values.getD p 0 * (r_i - sweep.getD p 0))) (List.replicate n 0)
  let result := List.zipWith (· * ·) result inv_denoms
  match degenerate with
  | some p => some (groups.foldl (fun (result : List EF) (grp : EF × ℕ × List EF) =>
      let (r_i, gap, values) := grp
      result.set p (result.getD p 0 + r_i * values.getD p 0 * ((gap + 1 : ℕ) : EF))) result)
  | none => some result

/-- eval_poly_at_base: Horner's rule at a base-field point. -/
def eval_poly_at_base (poly : List EF) (point : F) : EF :=
  poly.reverse.foldl (fun acc coeff => acc ⋆ point + coeff) 0

/-- reduce_mod_x_pow_minus_c: block q of n coefficients is scaled by c^q and added onto the n slots. -/
def reduce_mod_x_pow_minus_c (poly : List EF) (n : ℕ) (c : F) : Option (List EF) := do
  let blocks ← chunks n poly
  let (remainder, _) := blocks.foldl (fun (st : List EF × F) block =>
    ((List.range n).map fun i =>
      if i < block.length then st.1.getD i 0 + block.getD i 0 ⋆ st.2 else st.1.getD i 0,
     st.2 * c)) (List.replicate n 0, 1)
  some remainder

/-- next_domain_shift: shift^(2^log_arity) times the field's generator. -/
def next_domain_shift (generator current_shift : F) (log_arity : ℕ) : F :=
  current_shift ^ 2 ^ log_arity * generator

/-- fold_domain_params: the fold's domain before the re-commitment shift. -/
def fold_domain_params (current_shift : F) (current_log_domain log_arity : ℕ) : Option (ℕ × F) := do
  let log_size ← subChecked current_log_domain log_arity
  some (log_size, current_shift ^ 2 ^ log_arity)

/-- OodFilter: shift^(-2^log_size) and log_size of each excluded domain, and the largest log_size. -/
structure OodFilter (F : Type _) where
  shift_inv_pows : List F
  log_sizes : List ℕ
  max_log_size : ℕ

/-- OodFilter::new, which panics when a shift is zero. -/
def OodFilter.new (excluded_domains : List (F × ℕ)) : Option (OodFilter F) := do
  let shift_inv_pows ← excluded_domains.mapM fun (shift, log_size) =>
    (inverse shift).map (· ^ 2 ^ log_size)
  some ⟨shift_inv_pows, excluded_domains.map (·.2), (excluded_domains.map (·.2)).foldl max 0⟩

/-- OodFilter::accepts: one squaring chain records z^(2^log_size) for each domain; z is kept when it lies outside every domain of positive log_size and differs from every kept point. -/
def OodFilter.accepts (filter : OodFilter F) (candidate : EF) (kept : List EF) : Bool :=
  let z := candidate
  let (z_pows, _) := (List.range (filter.max_log_size + 1)).foldl (fun (st : List EF × EF) l =>
    let z_pows := (List.range st.1.length).foldl (fun zp s =>
      if filter.log_sizes.getD s 0 = l then zp.set s st.2 else zp) st.1
    (z_pows, if l < filter.max_log_size then st.2 ^ 2 else st.2))
    (List.replicate filter.log_sizes.length 1, z)
  let outside_all_domains := (List.range filter.log_sizes.length).all fun s =>
    filter.log_sizes.getD s 0 = 0 || z_pows.getD s 0 ⋆ filter.shift_inv_pows.getD s 0 != 1
  outside_all_domains && kept.all fun existing => existing != z

/-- fold_pass: one arity-2 pass, (lo + hi)/2 + (lo - hi) (g^(-j)/2) beta with lo, hi entries j and j + height. -/
def fold_pass (G : Gen F) (src : List EF) (beta : EF) (log_domain_size : ℕ) : Option (List EF) := do
  let height := src.length / 2
  let g ← G.get log_domain_size
  let g_orig_inv ← inverse g
  let halve_inv_powers := shiftedPowersList g_orig_inv ((1 : F) / 2) height
  some ((List.range height).map fun j =>
    let lo := src.getD j 0
    let hi := src.getD (j + height) 0
    (lo + hi) / 2 + (lo - hi) ⋆ halve_inv_powers.getD j 0 * beta)

/-- fold_codeword: log_arity arity-2 passes at beta, beta^2, beta^4, ..., which asserts at least one point is left. -/
def fold_codeword (G : Gen F) (codeword : List EF) (beta : EF) (log_arity log_domain_size : ℕ) :
    Option (List EF) := do
  let arity := 2 ^ log_arity
  let new_height := codeword.length / arity
  if new_height = 0 then none
  else if log_arity = 0 then some codeword
  else do
    let data ← fold_pass G codeword beta log_domain_size
    let (data, _, _) ← (List.range (log_arity - 1)).foldlM (fun (st : List EF × EF × ℕ) _ => do
      let current_beta := st.2.1 ^ 2
      let cur_log_domain ← subChecked st.2.2 1
      let data ← fold_pass G st.1 current_beta cur_log_domain
      some (data, current_beta, cur_log_domain)) (data, beta, log_domain_size)
    if data.length ≠ new_height then none else some data

/-- fold_poly_coeffs: the Horner value at gamma of each block of 2^log_arity coefficients. -/
def fold_poly_coeffs (coeffs : List EF) (gamma : EF) (log_arity : ℕ) : Option (List EF) := do
  let blocks ← chunks (2 ^ log_arity) coeffs
  some (blocks.map fun block => eval_poly block gamma)

/-- lagrange_eval_at: the barycentric interpolant through (xs_i, ys_i) at point, a node answered directly. -/
def lagrange_eval_at (xs : List F) (ys : List EF) (point : EF) : Option EF :=
  let n := xs.length
  if ys.length ≠ n then none
  else match (List.range n).find? (fun i => point = algebraMap F EF (xs.getD i 0)) with
  | some i => some (ys.getD i 0)
  | none => do
    let weights := (List.range n).map fun i => (List.range n).foldl (fun w j =>
      if i ≠ j then w * (xs.getD i 0 - xs.getD j 0) else w) 1
    let weights ← batchInv weights
    let diffs := xs.map fun x => point - algebraMap F EF x
    let (num, den) ← (List.range n).foldlM (fun (st : EF × EF) i => do
      let inv ← inverse (diffs.getD i 0)
      let term := algebraMap F EF (weights.getD i 0) * inv
      some (st.1 + term * ys.getD i 0, st.2 + term)) (0, 0)
    let den_inv ← inverse den
    some (num * den_inv)

/-- lagrange_interpolate_at: the interpolant at point through a coset of the n-th roots of unity, n = 2^k, with weights x_i / (n x_0^n).

It asserts equal lengths and a power-of-two length; a node is answered directly. -/
def lagrange_interpolate_at (xs : List F) (ys : List EF) (point : EF) : Option EF :=
  let n := xs.length
  if ys.length ≠ n then none
  else if n = 0 then some 0
  else match (List.range n).find? (fun i => point = algebraMap F EF (xs.getD i 0)) with
  | some i => some (ys.getD i 0)
  | none => do
    let log_n ← log2Strict n
    let coset_power := xs.getD 0 0 ^ 2 ^ log_n
    let weight_scale ← inverse ((n : F) * coset_power)
    let diffs := xs.map fun x => point - algebraMap F EF x
    let diff_invs ← batchInv diffs
    let l_point := diffs.prod
    let result := (List.range n).foldl (fun acc i =>
      acc + ys.getD i 0 ⋆ (xs.getD i 0 * weight_scale) * diff_invs.getD i 0) 0
    some (result * l_point)

/-- fold_fiber: interpolate the fiber at the nodes g^j zeta^l, zeta = g^(new height), and evaluate at beta. -/
def fold_fiber (G : Gen F) (fiber : List EF) (j log_new_height log_arity : ℕ) (beta : EF) :
    Option EF := do
  let arity := 2 ^ log_arity
  if fiber.length ≠ arity then none
  else do
    let new_height := 2 ^ log_new_height
    let g ← G.get (log_new_height + log_arity)
    let x0 := g ^ j
    let step := g ^ new_height
    let xs := shiftedPowersList step x0 arity
    lagrange_interpolate_at xs fiber beta

end TwoFields

end p3_stir.utils.mirror
