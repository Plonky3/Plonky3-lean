module

public import Plonky3Lean.Spec.MultilinearUtil
public import Mathlib.Data.List.Pairwise

@[expose] public section

/-!
# Multiset buses and offline memory checking

A bus is a multiset equality between the tuples one side pushes and the tuples the other side pulls.

The check follows Blum, Evans, Gemmell, Kannan and Naor, "Checking the correctness of memories" (FOCS 1991), in its grand-product form.

A tuple of 2^m slots is compressed to its multilinear extension at a random point r.

Each side multiplies its compressed tuples, each shifted by a random offset gamma:

```text
    fingerprint(t, r) = sum_b eq(b, r) t_b
    leaf(t)           = gamma - fingerprint(t, r)
    prod_i leaf(a_i)  = prod_j leaf(b_j)     <->     {a_i} = {b_j}, up to the Schwartz-Zippel error
```

An inactive row contributes the identity, through the gate 1 + (x - 1) s with s in {0, 1}.

A memory is a list of accesses: a read or a write, a cell, a time and a value.

It is consistent when every read returns the value of the latest earlier write to its cell, or the initial value when there is none.
-/

namespace Plonky3Lean.Spec.Bus

open Plonky3Lean.Spec.MultilinearUtil MvPolynomial

variable {K : Type _} [CommRing K]

/-! ## Fingerprints and grand products -/

/-- The fingerprint of a tuple at the point r: its multilinear extension at r. -/
def fingerprint (t r : List K) : K := mle t r

/-- The leaf of a tuple: the offset minus its fingerprint. -/
def leaf (γ : K) (r t : List K) : K := γ - fingerprint t r

/-- The grand product of the leaves of one side. -/
def grandProduct (γ : K) (r : List K) (ts : List (List K)) : K := (ts.map (leaf γ r)).prod

/-- The gated leaf 1 + (x - 1) s: the leaf x on an active row, the identity on an inactive one. -/
def gate (s x : K) : K := 1 + (x - 1) * s

/-- The fingerprint as a polynomial in the m point coordinates, numbered 1 to m. -/
noncomputable def fingerprintPoly (m : ℕ) (t : List K) : MvPolynomial (Fin (m + 1)) K :=
  rename Fin.succ (mlePoly t m)

/-- The grand product as a polynomial: the offset is variable 0 and the point is variables 1 to m. -/
noncomputable def productPoly (m : ℕ) (ts : List (List K)) : MvPolynomial (Fin (m + 1)) K :=
  (ts.map fun t => X 0 - fingerprintPoly m t).prod

/-! ## Memory checking -/

/-- One memory access: a read or a write, a cell, a time and a value. -/
structure Access (V : Type _) where
  write : Bool
  addr : ℕ
  time : ℕ
  value : V
  deriving DecidableEq

variable {V : Type _}

/-- Two accesses to one cell never share a time. -/
def TimesDistinct (accs : List (Access V)) : Prop :=
  accs.Pairwise fun x y => x.addr = y.addr → x.time ≠ y.time

/-- Every read returns the value of the latest earlier write to its cell, or the cell's initial value when no write precedes it. -/
def ReadsLastWrite (init : ℕ → V) (accs : List (Access V)) : Prop :=
  ∀ y ∈ accs, y.write = false →
    (∃ w ∈ accs, w.write ∧ w.addr = y.addr ∧ w.time < y.time ∧ w.value = y.value ∧
      ∀ w' ∈ accs, w'.write → w'.addr = y.addr → w'.time < y.time → w'.time ≤ w.time) ∨
    ((∀ w ∈ accs, w.write → w.addr = y.addr → y.time ≤ w.time) ∧ y.value = init y.addr)

/-- A consistent memory: distinct times on each cell, and every read sees the last write. -/
def Consistent (init : ℕ → V) (accs : List (Access V)) : Prop :=
  TimesDistinct accs ∧ ReadsLastWrite init accs

end Plonky3Lean.Spec.Bus
