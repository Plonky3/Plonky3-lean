module

public import Plonky3Lean.Spec.MultiStark
public import Plonky3Lean.Proofs.MultilinearUtil.Unique
public import Plonky3Lean.Proofs.MultilinearUtil.Next

@[expose] public section

/-!
# Extensions of row tables

The extension of a table at a vertex is the table's entry there.

The equality weights of a point sum to one.

Read a table of 2^n rows on the low bits of a wider cube's row index.

At p ++ s it has the same extension as the narrow table at s:

```text
    sum_{b < 2^(k + n)} eq(b, p ++ s) f(b mod 2^n)  =  sum_{c < 2^n} eq(c, s) f(c)
```

That is why the verifier evaluates a shorter table at the suffix of the bound point.
-/

namespace Plonky3Lean.Proofs.MultiStark

open Plonky3Lean.Spec.MultiStark Plonky3Lean.Spec.MultilinearUtil Plonky3Lean.Proofs.MultilinearUtil
  Finset

variable {K : Type _} [Field K]

/-- Fixing the first coordinate: the extension at (c, r) interpolates the low and the high half. -/
theorem ext_cons (f : ℕ → K) (c : K) (r : List K) :
    rowExt f (c :: r) = (1 - c) * rowExt f r + c * rowExt (fun b => f (2 ^ r.length + b)) r := by
  simp only [rowExt, List.length_cons, pow_succ, mul_two, sum_range_add, mul_sum]
  congr 1 <;> refine sum_congr rfl fun b hb => ?_ <;> simp only [mem_range] at hb
  · rw [vertex_low hb]; simp; ring
  · rw [vertex_high hb]; simp; ring

/-- The equality weights of a point sum to one. -/
theorem sum_eq_vertex (r : List K) : ∑ b ∈ range (2 ^ r.length), eq (vertex r.length b) r = 1 := by
  have h := fun r : List K => (show rowExt (fun _ => (1 : K)) r = ∑ b ∈ range (2 ^ r.length),
    eq (vertex r.length b) r by simp [rowExt])
  rw [← h]
  induction r with
  | nil => simp [rowExt, vertex]
  | cons c r ih => rw [ext_cons, ih]; ring

/-- At a vertex, the extension is the table entry. -/
theorem ext_vertex (f : ℕ → K) {n b : ℕ} (hb : b < 2 ^ n) : rowExt f (vertex n b) = f b := by
  unfold rowExt
  rw [length_vertex, sum_eq_single_of_mem b (mem_range.mpr hb) fun c hc hcb => by
    simp [eq_vertex_vertex (mem_range.mp hc) hb, hcb]]
  simp [eq_vertex_vertex hb hb]

/-- **The suffix point.**

A table read on the low n bits has, at p ++ s, the extension of the narrow table at s. -/
theorem ext_mod_append (f : ℕ → K) (p s : List K) :
    rowExt (fun b => f (b % 2 ^ s.length)) (p ++ s) = rowExt f s := by
  induction p generalizing f with
  | nil =>
    simp only [List.nil_append, rowExt]
    exact sum_congr rfl fun b hb => by simp only [Nat.mod_eq_of_lt (mem_range.mp hb)]
  | cons c p ih =>
    rw [List.cons_append, ext_cons]
    have hshift : (fun b => f ((2 ^ (p ++ s).length + b) % 2 ^ s.length)) =
        fun b => f (b % 2 ^ s.length) := by
      funext b
      rw [List.length_append, pow_add, Nat.mul_add_mod_self_right]
    rw [hshift, ih]; ring

/-- The extension as a mathlib polynomial is the extension of the table of its first 2^m entries. -/
theorem ext_eq_eval_mlePoly (f : ℕ → K) {m : ℕ} (x : Fin m → K) :
    rowExt f (List.ofFn x) = MvPolynomial.eval x (mlePoly ((List.range (2 ^ m)).map f) m) := by
  rw [eval_mlePoly]
  simp only [mle, rowExt, List.length_ofFn]
  exact sum_congr rfl fun b hb => by
    simp [List.getD_eq_getElem?_getD, mem_range.mp hb]

end Plonky3Lean.Proofs.MultiStark
