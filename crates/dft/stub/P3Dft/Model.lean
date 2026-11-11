/-
The objects the transcriptions of p3-dft are written in.

A matrix of height h is its rows, a function from row indices to a vector space V over the field K.

For a matrix of width w, V is the space of rows Fin w -> K.

Rows at index h and above are not part of the matrix, and nothing reads them.

A panic is none.
-/
module

public import Mathlib.Algebra.Field.Basic
public import Mathlib.Algebra.Module.Basic
public import Mathlib.Algebra.Order.Group.Nat
public import Mathlib.Data.Nat.Log
public import Mathlib.Data.List.Range

@[expose] public section

namespace p3_dft.mirror

/-- The field's two-adic generators: the table of generators, and the largest index it accepts. -/
structure Gen (K : Type _) where
  adicity : ℕ
  gen : ℕ → K

/-- The generator of the subgroup of order 2^bits, which asserts bits <= adicity. -/
def Gen.get {K : Type _} (G : Gen K) (bits : ℕ) : Option K :=
  if bits ≤ G.adicity then some (G.gen bits) else none

/-- The strict base-2 logarithm, which asserts its input is a power of two. -/
def log2Strict (n : ℕ) : Option ℕ :=
  if n ≠ 0 ∧ 2 ^ Nat.log 2 n = n then some (Nat.log 2 n) else none

/-- Apply a two-input operation to rows p and q, writing its outputs back to p and q. -/
def bfly {V : Type _} (f : V → V → V × V) (p q : ℕ) (x : ℕ → V) : ℕ → V :=
  fun i => if i = p then (f (x p) (x q)).1 else if i = q then (f (x p) (x q)).2 else x i

/-- The (block, pair) indices of nb blocks of m pairs each: blocks outer, pairs inner. -/
def blocks (nb m : ℕ) : List (ℕ × ℕ) :=
  (List.range nb).flatMap fun b => (List.range m).map fun s => (b, s)

/-- Visit (block, pair) indices in order, applying op b s to rows b 2m + s and b 2m + s + m. -/
def pairLoop {V : Type _} (order : List (ℕ × ℕ)) (m : ℕ) (op : ℕ → ℕ → V → V → V × V)
    (x : ℕ → V) : ℕ → V :=
  order.foldl (fun acc bs => bfly (op bs.1 bs.2) (bs.1 * (2 * m) + bs.2)
    (bs.1 * (2 * m) + bs.2 + m) acc) x

/-- Exchange rows i and j. -/
def swapRows {V : Type _} (i j : ℕ) (x : ℕ → V) : ℕ → V :=
  fun r => if r = i then x j else if r = j then x i else x r

variable {K : Type _} [Field K] {V : Type _} [AddCommGroup V] [Module K V]

/-- The k-bit reversal, as p3-util computes it: bit j of the result is bit k - 1 - j of i. -/
def bitRev : ℕ → ℕ → ℕ
  | 0, _ => 0
  | k + 1, i => (i % 2) * 2 ^ k + bitRev k (i / 2)

/-- A vector of length n in bit-reversed order, for n = 2^k: entry i is entry rev_k(i). -/
def revIndex (n : ℕ) (l : List K) : List K :=
  (List.range n).map fun i => l.getD (bitRev (Nat.log 2 n) i) 0

/-- The powers 1, g, g^2, ..., g^(n - 1), as the powers iterator collects them. -/
def powersList (g : K) (n : ℕ) : List K := (List.range n).map fun i => g ^ i

/-- The shifted powers s, s g, s g^2, ..., s g^(n - 1). -/
def shiftedPowersList (g s : K) (n : ℕ) : List K := (List.range n).map fun i => s * g ^ i

/-- Multiply every row by a scalar. -/
def scaleRows (c : K) (x : ℕ → V) : ℕ → V := fun i => c • x i

end p3_dft.mirror
