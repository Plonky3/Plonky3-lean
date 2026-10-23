/-
Transcriptions of the twin-coset domains of the circle and their polynomial space.

What a transcription abstracts, beyond the model of the points:

* an iterator is the list it yields, and itertools' interleave alternates two lists, then appends what is left;
* a matrix is its list of rows;
* the thread count of the parallel point chain is a parameter, at least one;
* a parallel loop whose items write disjoint outputs runs its items in order;
* the circle two-adicity is the adicity of the generator table;
* an inverse of zero panics, and so does a batch inversion with a zero entry;
* an assertion panics, and a debug assertion and a subtraction below zero are checked, as in a debug build;
* a panic is none, and a returned option that may also panic is an option inside an option.

Loops and the order of operations are kept.
-/
module

public import P3Circle.Point

@[expose] public section

namespace p3_circle.domain.mirror

open p3_dft.mirror p3_circle.point.mirror p3_commit.domain.mirror

/-- A twin coset of size 2^log_n: the points shift + i g and -shift + (i + 1) g, interleaved, for g of order 2^(log_n - 1). -/
structure CircleDomain (K : Type _) where
  log_n : ℕ
  shift : Point K
deriving DecidableEq

variable {K : Type _} [Field K] [DecidableEq K]

/-- Alternate the entries of two lists, then append the rest of the longer one. -/
def interleave {α : Type _} : List α → List α → List α
  | [], bs => bs
  | a :: rest, [] => a :: rest
  | a :: rest, b :: bs => a :: b :: interleave rest bs

/-- The first len points of the chain seed, seed + g, seed + 2 g, ... -/
def chain (seed g : Point K) (len : ℕ) : List (Point K) :=
  (List.range len).map fun i => (fun p => Point.add p g)^[i] seed

/-- The chunked point chain: below the threshold the plain chain, else chunks reseeded by a scalar multiplication. -/
def parallel_point_chain (threads : ℕ) (seed g : Point K) (len : ℕ) : List (Point K) :=
  if len < 2 ^ 10 then chain seed g len
  else
    let num_chunks := min (max threads 1) len
    let chunk_len := (len + num_chunks - 1) / num_chunks
    ((List.range ((len + chunk_len - 1) / chunk_len)).map fun c =>
      let chunk_start := c * chunk_len
      let this_len := min chunk_len (len - chunk_start)
      chain (Point.add seed (Point.mul g chunk_start)) g this_len).flatten

/-- The zigzag 0, 1, ..., len - 1, len - 1, ..., 1, 0, 0, 1, ... -/
def forward_backward_index (i len : ℕ) : ℕ :=
  let i := i % (2 * len)
  if i < len then i else 2 * len - 1 - i

variable (G : Gen (K × K))

namespace CircleDomain

/-- The constructor. -/
def new (log_n : ℕ) (shift : Point K) : CircleDomain K := ⟨log_n, shift⟩

/-- The standard position coset of size 2^log_n: the shift is the generator of order 2^(log_n + 1). -/
def standard (log_n : ℕ) : Option (CircleDomain K) :=
  (Point.generator G (log_n + 1)).map fun shift => ⟨log_n, shift⟩

/-- Whether the shift is the generator of order 2^(log_n + 1). -/
def is_standard (d : CircleDomain K) : Option Bool :=
  (Point.generator G (d.log_n + 1)).map fun g => decide (d.shift = g)

/-- The generator of order 2^(log_n - 1); log_n = 0 underflows. -/
def subgroup_generator (d : CircleDomain K) : Option (Point K) :=
  if d.log_n = 0 then none else Point.generator G (d.log_n - 1)

/-- The half coset shift, shift + g, ..., of 2^(log_n - 1) points. -/
def coset0 (d : CircleDomain K) : Option (List (Point K)) := do
  let g ← subgroup_generator G d
  some (chain d.shift g (2 ^ (d.log_n - 1)))

/-- The half coset g - shift, 2 g - shift, ..., of 2^(log_n - 1) points. -/
def coset1 (d : CircleDomain K) : Option (List (Point K)) := do
  let g ← subgroup_generator G d
  some (chain (Point.sub g d.shift) g (2 ^ (d.log_n - 1)))

/-- The points: the two half cosets interleaved. -/
def points (d : CircleDomain K) : Option (List (Point K)) := do
  let c0 ← coset0 G d
  let c1 ← coset1 G d
  some (interleave c0 c1)

/-- The points, each half coset built by the chunked chain. -/
def points_vec (threads : ℕ) (d : CircleDomain K) : Option (List (Point K)) := do
  let g ← subgroup_generator G d
  let half := 2 ^ (d.log_n - 1)
  let c0 := parallel_point_chain threads d.shift g half
  let c1 := parallel_point_chain threads (Point.sub g d.shift) g half
  some (interleave c0 c1)

/-- Point idx: shift + (idx / 2) g at an even index, -shift + (idx / 2 + 1) g at an odd one. -/
def nth_point (d : CircleDomain K) (idx : ℕ) : Option (Point K) := do
  let (idx, lsb) := (idx / 2, idx % 2)
  let g ← subgroup_generator G d
  if lsb = 0 then some (Point.add d.shift (Point.mul g idx))
  else some (Point.add (Point.neg d.shift) (Point.mul g (idx + 1)))

/-- The vanishing polynomial v_n(at) - v_n(shift). -/
def vanishing_poly (d : CircleDomain K) (at_ : Point K) : Option K := do
  let a ← Point.v_n at_ d.log_n
  let b ← Point.v_n d.shift d.log_n
  some (a - b)

/-- The number of points. -/
def size (d : CircleDomain K) : ℕ := 2 ^ d.log_n

/-- The first point, on the projective line; it panics when the shift is (-1, 0). -/
def first_point (d : CircleDomain K) : Option K :=
  Point.to_projective_line d.shift

/-- The next point after x, on the projective line, for a standard domain; none otherwise. -/
def next_point (d : CircleDomain K) (x : K) : Option (Option K) := do
  let std ← is_standard G d
  if std then do
    let p ← Point.from_projective_line x
    let g ← Point.generator G d.log_n
    some (Point.to_projective_line (Point.add p g))
  else some none

/-- A standard domain of size at least min_size, other than this size, for a standard domain.

None for a nonstandard domain, or when the circle has no shift of the needed order. -/
def try_create_disjoint_domain (d : CircleDomain K) (min_size : ℕ) :
    Option (Option (CircleDomain K)) := do
  let std ← is_standard G d
  if !std then some none
  else
    let log_n := log2Ceil min_size
    let log_n := if log_n = d.log_n then log_n + 1 else log_n
    if G.adicity ≤ log_n then some none
    else (standard G log_n).map some

/-- The first num_chunks points as shifts of twin cosets num_chunks times smaller.

It asserts a standard domain and a power-of-two chunk count no larger than the size. -/
def split_domains (d : CircleDomain K) (num_chunks : ℕ) : Option (List (CircleDomain K)) := do
  let std ← is_standard G d
  if !std then none
  else
    let log_chunks ← log2Strict num_chunks
    if log_chunks ≤ d.log_n then do
      let pts ← points G d
      some ((pts.take num_chunks).map fun shift => ⟨d.log_n - log_chunks, shift⟩)
    else none

/-- Distribute the rows over num_chunks matrices by the zigzag index.

It asserts at least two rows per chunk. -/
def split_evals (num_chunks : ℕ) (rows : List (List K)) : Option (List (List (List K))) := do
  let log_chunks ← log2Strict num_chunks
  if rows.length / 2 ^ (log_chunks + 1) ≥ 1 then
    some ((List.range num_chunks).map fun c =>
      (rows.zipIdx.filter fun r => forward_backward_index r.2 num_chunks = c).map Prod.fst)
  else none

/-- The vanishing polynomial at the point of the projective line x. -/
def vanishing_poly_at_point (d : CircleDomain K) (point : K) : Option K := do
  let p ← Point.from_projective_line point
  vanishing_poly d p

/-- The selectors at the point of the projective line x, with one shared batch inversion.

With z the vanishing polynomial and k = s_p_at_p(-shift), they are z / v_tilde(shift), z / v_tilde(-shift), 1 - z / (k v_tilde(-shift)) and 1 / z. -/
def selectors_at_point (d : CircleDomain K) (point : K) : Option (LagrangeSelectors K) := do
  let point ← Point.from_projective_line point
  let neg_shift := Point.neg d.shift
  let k ← Point.s_p_at_p neg_shift d.log_n
  let z ← vanishing_poly d point
  let (num_shift, den_shift) := Point.recip_v_tilde_p_num_den d.shift point
  let (num_negshift, den_negshift) := Point.recip_v_tilde_p_num_den neg_shift point
  let den_negshift_k := den_negshift * k
  let inv ← batchInv [den_shift, den_negshift_k, z]
  let inv_den_shift := inv.getD 0 0
  let inv_den_negshift_k := inv.getD 1 0
  let inv_z := inv.getD 2 0
  let z_inv_dk := z * num_negshift * inv_den_negshift_k
  some ⟨z * num_shift * inv_den_shift, z_inv_dk * k, 1 - z_inv_dk, inv_z⟩

/-- The selectors at every point of another domain, with three batch inversions. -/
def selectors_on_coset (d coset : CircleDomain K) : Option (LagrangeSelectors (List K)) := do
  let pts ← points G coset
  let neg_shift := Point.neg d.shift
  let k ← Point.s_p_at_p neg_shift d.log_n
  let shift_v_n ← Point.v_n d.shift d.log_n
  let z_vals ← pts.mapM fun at_ => (Point.v_n at_ d.log_n).map (· - shift_v_n)
  let den_shift := pts.map fun at_ => (Point.recip_v_tilde_p_num_den d.shift at_).2
  let den_negshift_k := pts.map fun at_ => (Point.recip_v_tilde_p_num_den neg_shift at_).2 * k
  let inv_vanishing ← batchInv z_vals
  let inv_den_shift ← batchInv den_shift
  let inv_den_negshift_k ← batchInv den_negshift_k
  let row := fun (i : ℕ) =>
    let at_ := pts.getD i (Point.ZERO)
    let z := z_vals.getD i 0
    let num_shift := (Point.recip_v_tilde_p_num_den d.shift at_).1
    let num_negshift := (Point.recip_v_tilde_p_num_den neg_shift at_).1
    let z_inv_dk := z * num_negshift * inv_den_negshift_k.getD i 0
    (z * num_shift * inv_den_shift.getD i 0, z_inv_dk * k, 1 - z_inv_dk)
  let rows := (List.range pts.length).map row
  some ⟨rows.map (·.1), rows.map (·.2.1), rows.map (·.2.2), inv_vanishing⟩

end CircleDomain

end p3_circle.domain.mirror
