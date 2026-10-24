/-
Transcriptions of the factored equality table of p3-multilinear-util.

The table eq(z, x) of a point z is stored as two factors:

* the prefix half, scaled
* the suffix half, scalar or packed.

The extension EF has the basis b over the base field F, as the packed extension stores its coefficients.

A packed extension value holds, for each basis index k, the packed coefficients k of its lanes.

The delayed-reduction dot products of the packing return the exact dot product.
-/
module

public import P3MultilinearUtil.Mirror.Poly
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.Algebra.BigOperators.Fin

@[expose] public section

namespace p3_multilinear_util.split_eq.mirror

open p3_multilinear_util.mirror p3_multilinear_util.poly.mirror

variable {F EF : Type _} [Field F] [Field EF] [Algebra F EF] [DecidableEq EF]

/-- The suffix-half table, stored as scalars or as packed values of W = 2^w lanes. -/
inductive EqMaybePacked (EF : Type _) (W : ℕ) where
  | Scalar : List EF → EqMaybePacked EF W
  | Packed : List (Fin W → EF) → EqMaybePacked EF W

/-- new_unpacked: the scalar table eq(point, x). -/
def EqMaybePacked.new_unpacked (w T : ℕ) (point : List EF) : Option (EqMaybePacked EF (2 ^ w)) := do
  pure (.Scalar (← Poly.new_from_point w T point 1))

/-- new_packed: the packed table when the point has at least log_2 W coordinates.

Otherwise it is the scalar table. -/
def EqMaybePacked.new_packed (w T : ℕ) (point : List EF) : Option (EqMaybePacked EF (2 ^ w)) :=
  if w ≤ point.length then do pure (.Packed (← Poly.new_packed_from_point w T point 1))
  else EqMaybePacked.new_unpacked w T point

/-- The number of scalar entries of the table. -/
def EqMaybePacked.num_scalar_evals {W : ℕ} : EqMaybePacked EF W → ℕ
  | .Scalar eq1 => eq1.length
  | .Packed eq1 => eq1.length * W

/-- The number of variables of the table. -/
def EqMaybePacked.num_variables {W : ℕ} (e : EqMaybePacked EF W) : ℕ :=
  Nat.log 2 e.num_scalar_evals

/-- dot_with_base: sum_i eq1[i] chunk[i].

The packed arm packs the chunk, which asserts whole lanes. -/
def EqMaybePacked.dot_with_base {W : ℕ} (e : EqMaybePacked EF W) (chunk : List F) : Option EF :=
  match e with
  | .Scalar eq1 => some (List.zipWith (fun a c => a * algebraMap F EF c) eq1 chunk).sum
  | .Packed eq1 => do
    let packed ← pack_slice W chunk
    pure (laneSum (List.zipWith mulBase eq1 packed).sum)

/-- dot_with_ext: sum_i eq1[i] chunk[i].

The packed arm groups the chunk W entries at a time. -/
def EqMaybePacked.dot_with_ext {W : ℕ} (e : EqMaybePacked EF W) (chunk : List EF) : Option EF :=
  match e with
  | .Scalar eq1 => some (List.zipWith (· * ·) eq1 chunk).sum
  | .Packed eq1 => do
    let packed ← (chunks W chunk).mapM (from_ext_slice W)
    pure (laneSum (List.zipWith (· * ·) packed eq1).sum)

/-- dot_with_ext_packed: both sides packed.

The scalar arm is unreachable and panics. -/
def EqMaybePacked.dot_with_ext_packed {W : ℕ} (e : EqMaybePacked EF W) (chunk : List (Fin W → EF)) :
    Option EF :=
  match e with
  | .Packed eq1 => some (laneSum (List.zipWith (· * ·) chunk eq1).sum)
  | .Scalar _ => none

/-- accumulate_scalar_into: out[i] += weight eq1[i], unpacking the lanes when packed. -/
def EqMaybePacked.accumulate_scalar_into {W : ℕ} (e : EqMaybePacked EF W) (out : List EF)
    (weight : EF) : List EF :=
  match e with
  | .Scalar eq1 =>
    List.zipWith (fun o w1 => o + weight * w1) out eq1 ++ out.drop eq1.length
  | .Packed eq1 =>
    let lanes := to_ext_iter eq1
    List.zipWith (fun o w1 => o + w1 * weight) out lanes ++ out.drop lanes.length

/-- compress_prefix_into: out[j] += w0 eq1[i] chunk[i |out| + j]. -/
def EqMaybePacked.compress_prefix_into {W : ℕ} (e : EqMaybePacked EF W) (out : List EF)
    (chunk : List F) (w0 : EF) : List EF :=
  let size_inner := out.length
  match e with
  | .Scalar eq1 =>
    ((chunks size_inner chunk).zip eq1).foldl (fun out cw =>
      let w := w0 * cw.2
      List.zipWith (fun acc f => acc + w * algebraMap F EF f) out cw.1) out
  | .Packed eq1 =>
    ((chunks (size_inner * W) chunk).zip eq1).foldl (fun out cw =>
      ((chunks size_inner cw.1).zip (List.ofFn (cw.2 * fun _ => w0))).foldl (fun out cw' =>
        List.zipWith (fun acc f => acc + cw'.2 * algebraMap F EF f) out cw'.1) out) out

/-- The per-coefficient dot product.

It runs D accumulators over aligned groups of four, then the tail. -/
def packed_basis_dot {W D : ℕ} (cs : Fin D → List (Fin W → F)) (rhs : List (Fin W → F)) :
    Fin D → Fin W → F :=
  let n := rhs.length
  let groups := n / 4
  let main := (List.range groups).foldl (fun (a : Fin D → Fin W → F) g =>
    fun k => a k + ((List.range 4).map fun c =>
      (cs k).getD (4 * g + c) 0 * rhs.getD (4 * g + c) 0).sum) (fun _ => 0)
  (List.range (n - 4 * groups)).foldl (fun (a : Fin D → Fin W → F) t =>
    fun k => a k + (cs k).getD (4 * groups + t) 0 * rhs.getD (4 * groups + t) 0) main

/-- The basis coefficient k of a packed extension value.

It packs the coefficients k of its lanes. -/
noncomputable def coeffOf {D W : ℕ} (b : Module.Basis (Fin D) F EF) (v : Fin W → EF) (k : Fin D) : Fin W → F :=
  fun l => b.repr (v l) k

/-- The packed extension value with the packed basis coefficients a. -/
noncomputable def fromCoeffs {D W : ℕ} (b : Module.Basis (Fin D) F EF) (a : Fin D → Fin W → F) : Fin W → EF :=
  fun l => ∑ k, a k l • b k

/-- compress_hi_dot_packed: sum_j eq0[j] sum_i eq1[i] chunk[j N + i].

It splits by basis coefficient when D <= 8 and N <= 128.

The chunk is packed, which asserts whole lanes. -/
noncomputable def compress_hi_dot_packed {D W : ℕ} (b : Module.Basis (Fin D) F EF) (eq1 : List (Fin W → EF))
    (chunk : List F) (eq0 : List EF) : Option EF := do
  let n := eq1.length
  let chunk_packed ← pack_slice W chunk
  if n ≤ 128 ∧ D ≤ 8 then
    let cs : Fin D → List (Fin W → F) := fun k => eq1.map fun v => coeffOf b v k
    let acc := eq0.zipIdx.foldl (fun (acc : Fin W → EF) wj =>
      let piece := (chunk_packed.drop (wj.2 * n)).take n
      let a := packed_basis_dot cs piece
      acc + fromCoeffs b a * fun _ => wj.1) 0
    pure (laneSum acc)
  else
    let sum := ((chunks n chunk_packed).zip eq0).map (fun pw =>
      (List.zipWith mulBase eq1 pw.1).sum * fun _ => pw.2) |>.sum
    pure (laneSum sum)

/-- compress_suffix_dot: sum_j eq0[j] sum_i eq1[i] chunk[j |eq1| + i]. -/
noncomputable def EqMaybePacked.compress_suffix_dot {D W : ℕ} (b : Module.Basis (Fin D) F EF)
    (e : EqMaybePacked EF W) (chunk : List F) (eq0 : List EF) : Option EF :=
  match e with
  | .Scalar eq1 => some ((chunks eq1.length chunk).zip eq0 |>.map (fun cw =>
      (List.zipWith (fun a c => a * algebraMap F EF c) eq1 cw.1).sum * cw.2)).sum
  | .Packed eq1 => compress_hi_dot_packed b eq1 chunk eq0

/-- dot_with_base_shifted: the chunk against the leading entries of the table.

The packed arm adds the tail lanes. -/
def EqMaybePacked.dot_with_base_shifted {W : ℕ} (e : EqMaybePacked EF W) (chunk : List F) :
    Option EF :=
  if e.num_scalar_evals < chunk.length then none
  else match e with
  | .Scalar eq1 => some (List.zipWith (fun a c => a * algebraMap F EF c) (eq1.take chunk.length)
      chunk).sum
  | .Packed eq1 =>
    let (packed, suffix) := pack_slice_with_suffix W chunk
    let sum := if packed.isEmpty then 0 else laneSum (List.zipWith mulBase eq1 packed).sum
    if suffix.isEmpty then some sum
    else do
      let w1 ← eq1[packed.length]?
      pure (sum + (List.zipWith (fun a c => a * algebraMap F EF c) (List.ofFn w1) suffix).sum)

/-- last_scalar: the last entry of the table.

On an empty table the unwrap panics. -/
def EqMaybePacked.last_scalar {W : ℕ} : EqMaybePacked EF W → Option EF
  | .Scalar eq1 => eq1.getLast?
  | .Packed eq1 => do (List.ofFn (← eq1.getLast?)).getLast?

/-- The factored table: the prefix-half table eq0, scaled, and the suffix-half table eq1. -/
structure SplitEq (EF : Type _) (W : ℕ) where
  eq0 : List EF
  eq1 : EqMaybePacked EF W

/-- new_unpacked: the point split at n / 2.

The scale goes into the prefix half. -/
def SplitEq.new_unpacked (w T : ℕ) (point : List EF) (scale : EF) : Option (SplitEq EF (2 ^ w)) := do
  let z0 := point.take (point.length / 2)
  let z1 := point.drop (point.length / 2)
  let eq0 ← Poly.new_from_point w T z0 scale
  let eq1 ← EqMaybePacked.new_unpacked w T z1
  pure ⟨eq0, eq1⟩

/-- new_packed: the same, with the suffix half packed when it can be. -/
def SplitEq.new_packed (w T : ℕ) (point : List EF) (scale : EF) : Option (SplitEq EF (2 ^ w)) := do
  let z0 := point.take (point.length / 2)
  let z1 := point.drop (point.length / 2)
  let eq0 ← Poly.new_from_point w T z0 scale
  let eq1 ← EqMaybePacked.new_packed w T z1
  pure ⟨eq0, eq1⟩

/-- The number of variables: those of the two halves. -/
def SplitEq.num_variables {W : ℕ} (s : SplitEq EF W) : ℕ :=
  Nat.log 2 s.eq0.length + s.eq1.num_variables

/-- eval_base: asserts the polynomial has the table's variables.

A constant is returned as is.

Block j of the polynomial dots against eq1 and is scaled by eq0[j]. -/
def SplitEq.eval_base {W : ℕ} (s : SplitEq EF W) (poly : List F) : Option EF := do
  if Nat.log 2 poly.length ≠ s.num_variables then none
  if poly.length = 1 then return algebraMap F EF (poly.getD 0 0)
  let cs := s.eq1.num_scalar_evals
  if (chunks cs poly).length ≠ s.eq0.length then none
  let parts ← ((chunks cs poly).zip s.eq0).mapM fun cw => do
    pure ((← s.eq1.dot_with_base cw.1) * cw.2)
  pure parts.sum

/-- eval_ext: the same, for a polynomial over the extension. -/
def SplitEq.eval_ext {W : ℕ} (s : SplitEq EF W) (poly : List EF) : Option EF := do
  if Nat.log 2 poly.length ≠ s.num_variables then none
  if poly.length = 1 then return poly.getD 0 0
  let cs := s.eq1.num_scalar_evals
  if (chunks cs poly).length ≠ s.eq0.length then none
  let parts ← ((chunks cs poly).zip s.eq0).mapM fun cw => do
    pure ((← s.eq1.dot_with_ext cw.1) * cw.2)
  pure parts.sum

/-- accumulate_into: out[x] += scale eq(point, x).

It asserts the output has 2^k entries. -/
def SplitEq.accumulate_into {W : ℕ} (s : SplitEq EF W) (out : List EF) (scale : Option EF) :
    Option (List EF) :=
  if Nat.log 2 out.length ≠ s.num_variables ∨ out.length ≠ 2 ^ Nat.log 2 out.length then none
  else
    let w_scale := scale.getD 1
    let cs := s.eq1.num_scalar_evals
    some (((chunks cs out).zip s.eq0).flatMap fun cw =>
      s.eq1.accumulate_scalar_into cw.1 (cw.2 * w_scale))

/-- materialize: the full table, accumulated into zeros. -/
def SplitEq.materialize {W : ℕ} (s : SplitEq EF W) : Option (List EF) := do
  let out ← Poly.zero s.num_variables
  s.accumulate_into out none

/-- compress_suffix_into: entry j is the dot of block j against the whole factored table.

It asserts the sizes. -/
noncomputable def SplitEq.compress_suffix_into {D W : ℕ} (b : Module.Basis (Fin D) F EF) (s : SplitEq EF W)
    (out : List EF) (poly : List F) : Option (List EF) := do
  if Nat.log 2 poly.length < s.num_variables then none
  if out.length ≠ poly.length / 2 ^ s.num_variables then none
  let suffix_rows := 2 ^ s.num_variables
  (out.zip (chunks suffix_rows poly)).mapM fun oc => s.eq1.compress_suffix_dot b oc.2 s.eq0

/-- Poly::eval_base: the recursive evaluation below the threshold.

From the threshold on, it uses the factored table. -/
def Poly.eval_base (thr w T : ℕ) (evals : List F) (point : List EF) : Option EF :=
  if point.length < thr then eval_multilinear_recursive evals point
  else do (← SplitEq.new_packed w T point 1).eval_base evals

/-- Poly::eval_ext: the same, for a table over the extension. -/
def Poly.eval_ext (thr w T : ℕ) (evals : List EF) (point : List EF) : Option EF :=
  if point.length < thr then eval_multilinear_recursive evals point
  else do (← SplitEq.new_packed w T point 1).eval_ext evals

end p3_multilinear_util.split_eq.mirror
