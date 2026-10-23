/-
Transcriptions of the point methods of p3-multilinear-util.

A point is the list of its coordinates.

The objects are those of the model; the thread split of the equality table is the parameter task_len.
-/
module

public import P3MultilinearUtil.Model
public import Mathlib.Algebra.Field.Basic
public import Mathlib.Data.Nat.Log

@[expose] public section

namespace p3_multilinear_util.point.mirror

open p3_multilinear_util.mirror

variable {F EF : Type _} [Field F] [Field EF] [Algebra F EF]

/-- Which end of a point binds bit 0 of a table index. -/
inductive BitOrder where
  | Msb
  | Lsb

/-- split_at, which asserts pos <= n. -/
def Point.split_at (p : List F) (pos : ℕ) : Option (List F × List F) :=
  if pos ≤ p.length then some (p.take pos, p.drop pos) else none

/-- The coordinates in reverse order. -/
def Point.reversed (p : List F) : List F := p.reverse

/-- Split each weight of low into its bit-0 share, kept in low, and its bit-1 share, written to high.

high is only written, and has the length of low.

Whole lanes are processed packed, and the tail one entry at a time. -/
def split_by_coordinate (W : ℕ) (low : List F) (coordinate : F) : List F × List F :=
  let (low_packed, low_tail) := pack_slice_with_suffix W low
  let packed_coordinate : Fin W → F := splat coordinate
  let packed := low_packed.map fun l => let h := l * packed_coordinate; (l - h, h)
  let tail := low_tail.map fun l => let h := l * coordinate; (l - h, h)
  (to_ext_iter (packed.map Prod.fst) ++ tail.map Prod.fst,
    to_ext_iter (packed.map Prod.snd) ++ tail.map Prod.snd)

/-- The coordinate that enters at step k of the doubling. -/
def entering (p : List F) (order : BitOrder) (k : ℕ) : F :=
  match order with
  | .Msb => p.getD (p.length - 1 - k) 0
  | .Lsb => p.getD k 0

/-- The single-threaded table: out[0] = scale, then each coordinate doubles the filled prefix.

It debug-asserts that out has 2^n entries. -/
def Point.fill_equality_table_serial (W : ℕ) (p : List F) (out : List F) (order : BitOrder)
    (scale : F) : Option (List F) :=
  if out.length ≠ 2 ^ p.length then none
  else
    some ((List.range p.length).foldl (fun out k =>
      let (low, high) := split_by_coordinate W (out.take (2 ^ k)) (entering p order k)
      low ++ high ++ out.drop (2 ^ (k + 1))) (out.set 0 scale))

/-- The coordinates binding the high and the low index bits: the high bits are bound at the high-bit end of the point. -/
def high_low (p : List F) (order : BitOrder) (low_variables : ℕ) : List F × List F :=
  match order with
  | .Msb => (p.take (p.length - low_variables), p.drop (p.length - low_variables))
  | .Lsb => (p.drop low_variables, p.take low_variables)

/-- The table as chunks of 2^low_variables entries: serial seeds over the high variables, then one task per chunk. -/
def Point.fill_equality_table_in_chunks (W : ℕ) (p : List F) (out : List F) (order : BitOrder)
    (scale : F) (low_variables : ℕ) : Option (List F) := do
  if p.length < low_variables then none
  let high_variables := p.length - low_variables
  if high_variables = 0 then Point.fill_equality_table_serial W p out order scale
  else
    let (high, low) := high_low p order low_variables
    let seeds ← Point.fill_equality_table_serial W high (List.replicate (2 ^ high_variables) 0)
      order scale
    let parts ← ((chunks (2 ^ low_variables) out).zip seeds).mapM fun cs =>
      Point.fill_equality_table_serial W low cs.1 order cs.2
    pure (parts.flatten ++ out.drop (seeds.length * 2 ^ low_variables))

/-- The split chosen by the cost model: one task when W > 1, and log_2 of the task length otherwise. -/
def Point.fill_equality_table (W task_len : ℕ) (p : List F) (out : List F) (order : BitOrder)
    (scale : F) : Option (List F) :=
  let task_len := if W > 1 then out.length else task_len
  let low_variables := min (Nat.clog 2 task_len) p.length
  Point.fill_equality_table_in_chunks W p out order scale low_variables

/-- The table under a bit order, which panics when 2^n overflows a usize. -/
def Point.equality_table (W task_len : ℕ) (p : List F) (order : BitOrder) : Option (List F) :=
  if p.length < 64 then
    Point.fill_equality_table W task_len p (List.replicate (2 ^ p.length) 0) order 1
  else none

/-- equality_weights_msb: coordinate zero binds the most significant index bit. -/
def Point.equality_weights_msb (W task_len : ℕ) (p : List F) : Option (List F) :=
  Point.equality_table W task_len p .Msb

/-- equality_weights_lsb: coordinate zero binds the least significant index bit. -/
def Point.equality_weights_lsb (W task_len : ℕ) (p : List F) : Option (List F) :=
  Point.equality_table W task_len p .Lsb

/-- One step of equality_at_vertex: the factor of the low bit, then the bits shifted down. -/
def vertexStep (acc : List F × ℕ) (coordinate : F) : List F × ℕ :=
  let bit := acc.2 % 2
  (acc.1 ++ [if bit = 0 then 1 - coordinate else coordinate], acc.2 / 2)

/-- equality_at_vertex: none when the vertex has a bit at or above n, else the product from the last coordinate. -/
def Point.equality_at_vertex (p : List F) (vertex : ℕ) : Option F :=
  if p.length < 64 ∧ vertex >>> p.length ≠ 0 then none
  else some ((p.reverse.foldl vertexStep ([], vertex)).1.foldl (· * ·) 1)

/-- hypercube: value in big-endian, coordinate i is bit n - 1 - i; it asserts value < 2^n. -/
def Point.hypercube (value num_variables : ℕ) : Option (List F) :=
  if 64 ≤ num_variables then none
  else if value < 2 ^ num_variables then
    some ((List.range num_variables).map fun i =>
      if (value >>> (num_variables - 1 - i)) % 2 = 1 then 1 else 0)
  else none

/-- expand_from_univariate: from the last index down, each entry is the running power, then squared. -/
def Point.expand_from_univariate (point : F) (num_variables : ℕ) : List F :=
  ((List.range num_variables).reverse.foldl (fun (acc : List F × F) i =>
    (acc.1.set i acc.2, acc.2 * acc.2)) (List.replicate num_variables 0, point)).1

/-- eval_eq: the product of 2 l r - l - r + 1, which asserts the points have the same length. -/
def Point.eval_eq (p : List F) (q : List EF) : Option EF :=
  if p.length ≠ q.length then none
  else some ((List.zipWith (fun l r => (r + r) * algebraMap F EF l - algebraMap F EF l - r + 1)
    p q).foldl (· * ·) 1)

/-- One step of eval_select: the factor r (var - 1) + 1, then var squared. -/
def selectStep (acc : List EF × F) (r : EF) : List EF × F :=
  (acc.1 ++ [r * algebraMap F EF (-1 + acc.2) + 1], acc.2 * acc.2)

/-- eval_select: the product of the factors, from the last coordinate. -/
def Point.eval_select (var : F) (point : List EF) : EF :=
  (point.reverse.foldl selectStep ([], var)).1.foldl (· * ·) 1

/-- One step of eval_next, on the next higher bit. -/
def evalNextStep (acc : F × F × F) (bits : F × F) : F × F × F :=
  let (carry, done, omega) := acc
  let (point_bit, row_bit) := bits
  let eq := (row_bit + row_bit) * point_bit - point_bit - row_bit + 1
  let prev_carry := carry
  let carry := prev_carry * point_bit * (1 - row_bit)
  let done := done * eq + prev_carry * (1 - point_bit) * row_bit
  let omega := omega * (point_bit * row_bit)
  (carry, done, omega)

/-- eval_next: the carry, completed and boundary weights, folded from the last coordinate; it asserts equal lengths. -/
def Point.eval_next (point row : List F) : Option (F × F × F) :=
  if point.length ≠ row.length then none
  else some ((point.zip row).reverse.foldl evalNextStep (1, 0, 1))

/-- The common value of a list, which panics when it is empty or has two different values. -/
def allEqualValue (l : List ℕ) : Option ℕ :=
  match l with
  | [] => none
  | a :: t => if t.all (· = a) then some a else none

/-- transpose: entry j n + i is coordinate j of point i, or row k - 1 - j when reversed. -/
def Point.transpose (points : List (List F)) (rev_order : Bool) : Option (List F × ℕ) := do
  let k ← allEqualValue (points.map List.length)
  let n := points.length
  let flat := points.zipIdx.foldl (fun flat pi =>
    pi.1.zipIdx.foldl (fun flat cj =>
      if rev_order then flat.set ((k - 1 - cj.2) * n + pi.2) cj.1
      else flat.set (cj.2 * n + pi.2) cj.1) flat) (List.replicate (k * n) 0)
  pure (flat, n)

end p3_multilinear_util.point.mirror
