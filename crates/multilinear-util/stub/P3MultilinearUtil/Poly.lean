/-
Transcriptions of the multilinear polynomial methods of p3-multilinear-util.

A polynomial is its table of evaluations over the cube, a list of 2^n entries.

The table entries live in A and the challenges in K.

Each method's bounds say whether A is a K-algebra or the reverse.

The evaluation dispatch and the in-place folds take the cost model's choice as a parameter.
-/
module

public import P3MultilinearUtil.EqBatch

@[expose] public section

namespace p3_multilinear_util.poly.mirror

open p3_multilinear_util.mirror p3_multilinear_util.eq_batch.mirror

/-- new: the table, which asserts its length is a power of two. -/
def Poly.new {A : Type _} (evals : List A) : Option (List A) :=
  if evals.length ≠ 0 ∧ 2 ^ Nat.log 2 evals.length = evals.length then some evals else none

/-- as_constant: the only entry of a table of one entry. -/
def Poly.as_constant {A : Type _} (evals : List A) : Option A :=
  if evals.length = 1 then evals.head? else none

/-- zero: 2^n zeros.

The shift panics when n >= 64. -/
def Poly.zero {A : Type _} [Zero A] (num_variables : ℕ) : Option (List A) :=
  if num_variables < 64 then some (List.replicate (2 ^ num_variables) 0) else none

/-- truncate_to_half: keep the lower half, which asserts the table is not constant. -/
def Poly.truncate_to_half {A : Type _} (evals : List A) : Option (List A) :=
  if evals.length ≤ 1 then none else some (evals.take (evals.length / 2))

/-- pad_zeros: zeros up to 2^n entries.

It asserts n is at least the current variable count. -/
def Poly.pad_zeros {A : Type _} [Zero A] (evals : List A) (num_variables : ℕ) : Option (List A) :=
  if Nat.log 2 evals.length ≤ num_variables ∧ num_variables < 64 then
    some (evals.take (2 ^ num_variables) ++
      List.replicate (2 ^ num_variables - evals.length) 0)
  else none

section Fields

variable {F : Type _} [Field F]

/-- new_from_point: scale eq(point, x) for every x, through the batched table of one point.

The constant case is the scale.
The size 2^n must fit a usize. -/
def Poly.new_from_point (w T : ℕ) (point : List F) (scale : F) : Option (List F) :=
  if point.length = 0 then some [scale]
  else if point.length < 64 then
    eval_eq_batch w T false 1 (point.map fun z => [z]) (List.replicate (2 ^ point.length) 0) [scale]
  else none

/-- new_next_from_point: the equality table shifted up one row.

The last weight is kept on the last row. -/
def Poly.new_next_from_point (w T : ℕ) (point : List F) : Option (List F) := do
  let res ← Poly.new_from_point w T point 1
  let n := res.length
  let last := res.getD (n - 1) 0
  let res := res.take 1 ++ res.take (n - 1)
  let res := res.set 0 0
  let res := res.set (n - 1) (res.getD (n - 1) 0 + last)
  Poly.new res

end Fields

section Folds

variable {K A : Type _} [Field K] [CommRing A] [Algebra K A]

/-- fix_prefix_var_mut: p[i] += (p[i + mid] - p[i]) r over the lower half, then keep it. -/
def Poly.fix_prefix_var_mut (evals : List A) (r : K) : Option (List A) :=
  if evals.length = 1 then none
  else
    let mid := evals.length / 2
    some (List.zipWith (fun a0 a1 => a0 + (a1 - a0) * algebraMap K A r) (evals.take mid)
      (evals.drop mid))

/-- sum_prefix_var_mut: p[i] += p[i + mid], then keep the lower half.

A constant is left alone. -/
def Poly.sum_prefix_var_mut (evals : List A) : List A :=
  if evals.length = 1 then evals
  else
    let mid := evals.length / 2
    List.zipWith (· + ·) (evals.take mid) (evals.drop mid)

/-- fix_prefix_var_mut_monomial: p[i] += p[i + mid] r over the lower half, in the monomial basis. -/
def Poly.fix_prefix_var_mut_monomial (evals : List A) (r : K) : Option (List A) :=
  if evals.length = 1 then none
  else
    let mid := evals.length / 2
    some (List.zipWith (fun a0 a1 => a0 + a1 * algebraMap K A r) (evals.take mid) (evals.drop mid))

/-- The in-place suffix fold: entry i reads entries 2 i and 2 i + 1, ahead of the write. -/
def Poly.fix_suffix_var_mut_whole (evals : List A) (r : K) (mid : ℕ) : List A :=
  ((List.range mid).foldl (fun v i =>
    let lo := v.getD (2 * i) 0
    let hi := v.getD (2 * i + 1) 0
    v.set i ((hi - lo) * algebraMap K A r + lo)) evals).take mid

/-- The split suffix fold: the folded pairs, collected into a new buffer. -/
def Poly.fix_suffix_var_mut_split (evals : List A) (r : K) : List A :=
  (chunks 2 evals).map fun a => (a.getD 1 0 - a.getD 0 0) * algebraMap K A r + a.getD 0 0

/-- fix_suffix_var_mut: asserts the table is not constant, then folds in place or splits. -/
def Poly.fix_suffix_var_mut (split : Bool) (evals : List A) (r : K) : Option (List A) :=
  if evals.length = 1 then none
  else
    let mid := evals.length / 2
    some (if split then Poly.fix_suffix_var_mut_split evals r
      else Poly.fix_suffix_var_mut_whole evals r mid)

end Folds

section Extension

variable {A B : Type _} [Field A] [Field B] [Algebra A B]

/-- fix_prefix_var: (1 - r) p(0, x) + r p(1, x), into the larger field.

It asserts the table is not constant. -/
def Poly.fix_prefix_var (evals : List A) (r : B) : Option (List B) :=
  if evals.length ≤ 1 then none
  else
    let half := evals.length / 2
    Poly.new (List.zipWith (fun a0 a1 => r * algebraMap A B (a1 - a0) + algebraMap A B a0)
      (evals.take half) (evals.drop half))

/-- fix_prefix_var_at: one entry of the prefix fold.

The reads panic past the end. -/
def Poly.fix_prefix_var_at (evals : List A) (r : B) (index : ℕ) : Option B := do
  let half := evals.length / 2
  let lo ← evals[index]?
  let hi ← evals[index + half]?
  pure (r * algebraMap A B (hi - lo) + algebraMap A B lo)

/-- fix_suffix_var: the adjacent pairs folded at r.

It asserts the table is not constant. -/
def Poly.fix_suffix_var (evals : List A) (r : B) : Option (List B) :=
  if evals.length = 1 then none
  else Poly.new ((chunks 2 evals).map fun a =>
    r * algebraMap A B (a.getD 1 0 - a.getD 0 0) + algebraMap A B (a.getD 0 0))

/-- fix_prefix_var_to_packed: the prefix fold on packed lanes.

It asserts n > log_2 W. -/
def Poly.fix_prefix_var_to_packed (w : ℕ) (evals : List A) (r : B) :
    Option (List (Fin (2 ^ w) → B)) := do
  if Nat.log 2 evals.length ≤ w then none
  let poly ← pack_slice (2 ^ w) evals
  let half := poly.length / 2
  Poly.new (List.zipWith (fun a0 a1 => (fun _ => r) * mulBase (fun _ => 1) (a1 - a0) +
    mulBase (fun _ => 1) a0) (poly.take half) (poly.drop half))

/-- pack: W consecutive extension values per packed value.

It asserts n >= log_2 W. -/
def Poly.pack (w : ℕ) (evals : List B) : Option (List (Fin (2 ^ w) → B)) :=
  if Nat.log 2 evals.length < w then none
  else (chunks (2 ^ w) evals).mapM (from_ext_slice (2 ^ w))

/-- unpack: the lanes of every packed value, in order. -/
def Poly.unpack {W : ℕ} (packed : List (Fin W → B)) : List B := to_ext_iter packed

/-- eval_multilinear_recursive in a release build.

It unrolls up to four variables, then splits on the first.

The reads panic past the end of the table. -/
def eval_multilinear_recursive : List A → List B → Option B
  | evals, [] => do pure (algebraMap A B (← evals[0]?))
  | evals, [x] => do
    let e0 ← evals[0]?; let e1 ← evals[1]?
    pure (x * algebraMap A B (e1 - e0) + algebraMap A B e0)
  | evals, [x0, x1] => do
    let e ← (List.range 4).mapM (evals[·]?)
    let a0 := x1 * algebraMap A B (e.getD 1 0 - e.getD 0 0) + algebraMap A B (e.getD 0 0)
    let a1 := x1 * algebraMap A B (e.getD 3 0 - e.getD 2 0) + algebraMap A B (e.getD 2 0)
    pure (a0 + (a1 - a0) * x0)
  | evals, [x0, x1, x2] => do
    let e ← (List.range 8).mapM (evals[·]?)
    let a00 := x2 * algebraMap A B (e.getD 1 0 - e.getD 0 0) + algebraMap A B (e.getD 0 0)
    let a01 := x2 * algebraMap A B (e.getD 3 0 - e.getD 2 0) + algebraMap A B (e.getD 2 0)
    let a10 := x2 * algebraMap A B (e.getD 5 0 - e.getD 4 0) + algebraMap A B (e.getD 4 0)
    let a11 := x2 * algebraMap A B (e.getD 7 0 - e.getD 6 0) + algebraMap A B (e.getD 6 0)
    let a0 := a00 + x1 * (a01 - a00)
    let a1 := a10 + x1 * (a11 - a10)
    pure (a0 + (a1 - a0) * x0)
  | evals, [x0, x1, x2, x3] => do
    let e ← (List.range 16).mapM (evals[·]?)
    let a000 := x3 * algebraMap A B (e.getD 1 0 - e.getD 0 0) + algebraMap A B (e.getD 0 0)
    let a001 := x3 * algebraMap A B (e.getD 3 0 - e.getD 2 0) + algebraMap A B (e.getD 2 0)
    let a010 := x3 * algebraMap A B (e.getD 5 0 - e.getD 4 0) + algebraMap A B (e.getD 4 0)
    let a011 := x3 * algebraMap A B (e.getD 7 0 - e.getD 6 0) + algebraMap A B (e.getD 6 0)
    let a100 := x3 * algebraMap A B (e.getD 9 0 - e.getD 8 0) + algebraMap A B (e.getD 8 0)
    let a101 := x3 * algebraMap A B (e.getD 11 0 - e.getD 10 0) + algebraMap A B (e.getD 10 0)
    let a110 := x3 * algebraMap A B (e.getD 13 0 - e.getD 12 0) + algebraMap A B (e.getD 12 0)
    let a111 := x3 * algebraMap A B (e.getD 15 0 - e.getD 14 0) + algebraMap A B (e.getD 14 0)
    let a00 := a000 + x2 * (a001 - a000)
    let a01 := a010 + x2 * (a011 - a010)
    let a10 := a100 + x2 * (a101 - a100)
    let a11 := a110 + x2 * (a111 - a110)
    let a0 := a00 + x1 * (a01 - a00)
    let a1 := a10 + x1 * (a11 - a10)
    pure (a0 + (a1 - a0) * x0)
  | evals, x :: x1 :: x2 :: x3 :: x4 :: sub => do
    let half := evals.length / 2
    let f0 ← eval_multilinear_recursive (evals.take half) (x1 :: x2 :: x3 :: x4 :: sub)
    let f1 ← eval_multilinear_recursive (evals.drop half) (x1 :: x2 :: x3 :: x4 :: sub)
    pure (f0 + (f1 - f0) * x)

end Extension

section Packed

/-- eq_serial: entry 0 is the scale, then each coordinate from the last doubles the filled prefix.

It asserts the output has 2^n entries, and it writes every one of them. -/
def eq_serial {K A : Type _} [Field K] [CommRing A] [Algebra K A] (out : List A) (point : List K)
    (scale : A) : Option (List A) :=
  if out.length ≠ 2 ^ point.length then none
  else some (point.reverse.zipIdx.foldl (fun out vi =>
    let lo := out.take (2 ^ vi.2)
    let hi := out.drop (2 ^ vi.2)
    let hi' := (lo.zip hi).map fun p => p.1 * algebraMap K A vi.1
    let lo' := (lo.zip hi').map fun q => q.1 - q.2
    lo' ++ (hi' ++ hi.drop (2 ^ vi.2))) (out.set 0 scale))

variable {EF : Type _} [Field EF] [DecidableEq EF]

/-- new_packed_from_point: scale eq(point, x), with the last log_2 W variables in the lanes.

It asserts the scale is nonzero and n >= log_2 W.

The remaining variables are expanded serially, or split into one chunk per thread. -/
def Poly.new_packed_from_point (w T : ℕ) (point : List EF) (scale : EF) :
    Option (List (Fin (2 ^ w) → EF)) := do
  let n := point.length
  if scale = 0 then none
  if n < w then none
  let point_rest := point.take (n - w)
  let point_init := point.drop (n - w)
  let init ← eq_serial (List.replicate (2 ^ w) 0) point_init scale
  let seed ← from_ext_slice (2 ^ w) init
  let log_chunks := Nat.clog 2 T
  if point_rest.length ≤ log_chunks + 1 then
    eq_serial (List.replicate (2 ^ point_rest.length) 0) point_rest seed
  else
    let leading := point_rest.take log_chunks
    let middle := point_rest.drop log_chunks
    let buffer ← eq_serial (List.replicate (2 ^ log_chunks) 0) leading seed
    let parts ← ((chunks (2 ^ middle.length) (List.replicate (2 ^ point_rest.length) 0)).zip
      buffer).mapM fun cs => eq_serial cs.1 middle cs.2
    pure parts.flatten

end Packed

end p3_multilinear_util.poly.mirror
