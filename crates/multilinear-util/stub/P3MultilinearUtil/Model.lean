/-
The objects the transcriptions of p3-multilinear-util are written in.

* The base field F and the extension EF are mathlib fields, and EF is an F-algebra.
* A product of an extension element by a base element maps the base element into EF first.
* A vector or a slice is a list, and a panic is none.
* A usize has 64 bits, so 2^n fits exactly when n < 64.
* The packing width is W = 2^w, for every w.
* A packed value is its W lanes, a function on Fin W, and packed arithmetic acts lane by lane.
* A parallel loop whose items write disjoint outputs runs its items in order.
* A parallel reduction adds its partial results, which field addition makes independent of the split.
* The thread count and the task sizes of the cost model are parameters, for every value.
* A debug assertion panics, as in a debug build.

Loops, branches and the order of operations are kept.
-/
module

public import Mathlib.Algebra.Algebra.Pi
public import Mathlib.Algebra.BigOperators.Group.List.Basic
public import Mathlib.Data.List.Range

@[expose] public section

namespace p3_multilinear_util.mirror

variable {K : Type _}

/-- The first k groups of W consecutive entries, each as a packed value. -/
def packN (W : ℕ) [Zero K] : ℕ → List K → List (Fin W → K)
  | 0, _ => []
  | k + 1, l => (fun i => l.getD i 0) :: packN W k (l.drop W)

/-- pack_slice: the slice as packed values, which asserts its length is a multiple of W. -/
def pack_slice (W : ℕ) [Zero K] (l : List K) : Option (List (Fin W → K)) :=
  if l.length % W = 0 then some (packN W (l.length / W) l) else none

/-- pack_slice_with_suffix: the longest prefix of whole groups, packed, and the rest. -/
def pack_slice_with_suffix (W : ℕ) [Zero K] (l : List K) : List (Fin W → K) × List K :=
  (packN W (l.length / W) l, l.drop (l.length - l.length % W))

/-- to_ext_iter: the lanes of each packed value, in lane order. -/
def to_ext_iter {W : ℕ} (v : List (Fin W → K)) : List K := v.flatMap List.ofFn

/-- from_ext_slice: W consecutive values as one packed value, which asserts the slice has W entries. -/
def from_ext_slice (W : ℕ) [Zero K] (l : List K) : Option (Fin W → K) :=
  if l.length = W then some fun i => l.getD i 0 else none

/-- The broadcast of a value to every lane. -/
def splat {W : ℕ} (a : K) : Fin W → K := fun _ => a

/-- A packed product of extension lanes by base lanes. -/
def mulBase {F EF : Type _} [CommSemiring F] [Semiring EF] [Algebra F EF] {W : ℕ}
    (x : Fin W → EF) (y : Fin W → F) : Fin W → EF :=
  fun i => x i * algebraMap F EF (y i)

/-- The sum of the lanes of a packed value. -/
def laneSum {W : ℕ} [AddCommMonoid K] (x : Fin W → K) : K := (List.ofFn x).sum

/-- chunks(c): consecutive pieces of c entries, the last one possibly shorter.

The size c is positive. -/
def chunks (c : ℕ) (l : List K) : List (List K) :=
  (List.range ((l.length + c - 1) / c)).map fun j => (l.drop (j * c)).take c

/-- The dot product of two sequences, truncated to the shorter one. -/
def dot [Mul K] [Add K] [Zero K] (a b : List K) : K := (List.zipWith (· * ·) a b).foldr (· + ·) 0

end p3_multilinear_util.mirror
