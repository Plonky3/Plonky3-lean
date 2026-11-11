module

public import Plonky3Lean.Proofs.MultiStark.Ext

@[expose] public section

/-!
# Aligned blocks of a padded table

A padded table of 2^m leaves holds blocks.

A block of 2^n leaves starts at a multiple c 2^n of its own height:

```text
    leaves:  | block c = 0 | block c = 1 | ... | padding |
               2^n leaves    2^n leaves
```

At a point p ++ s, with s of length n, the block's share of the extension is

```text
    eq(vertex c, p) * (extension of the block's own table at s)
```

So a verifier rebuilds the opening of the whole table from the blocks, one weight each.

Padding that holds zero contributes nothing.

Padding that holds one contributes one minus the weights of the blocks.
-/

namespace Plonky3Lean.Proofs.MultiStark

open Plonky3Lean.Spec.MultiStark Plonky3Lean.Spec.MultilinearUtil Plonky3Lean.Proofs.MultilinearUtil
  Finset

variable {K : Type _} [Field K]

/-- The extension reads the table only on the cube. -/
theorem rowExt_congr {f g : ℕ → K} {r : List K} (h : ∀ x < 2 ^ r.length, f x = g x) :
    rowExt f r = rowExt g r :=
  sum_congr rfl fun x hx => by rw [h x (mem_range.mp hx)]

theorem rowExt_zero (r : List K) : rowExt (fun _ => (0 : K)) r = 0 := by simp [rowExt]

theorem rowExt_add (f g : ℕ → K) (r : List K) :
    rowExt (fun x => f x + g x) r = rowExt f r + rowExt g r := by
  simp [rowExt, mul_add, sum_add_distrib]

theorem rowExt_smul (a : K) (f : ℕ → K) (r : List K) :
    rowExt (fun x => a * f x) r = a * rowExt f r := by
  simp only [rowExt, mul_sum]; exact sum_congr rfl fun _ _ => by ring

theorem rowExt_const (a : K) (r : List K) : rowExt (fun _ => a) r = a := by
  have := rowExt_smul a (fun _ => (1 : K)) r
  simp only [mul_one] at this
  rw [this, show rowExt (fun _ => (1 : K)) r = 1 by simpa [rowExt] using sum_eq_vertex r, mul_one]

theorem rowExt_sum {ι : Type _} (s : Finset ι) (f : ι → ℕ → K) (r : List K) :
    rowExt (fun x => ∑ i ∈ s, f i x) r = ∑ i ∈ s, rowExt (f i) r := by
  simp only [rowExt, mul_sum]; exact sum_comm

/-- The table of one block: g on the leaves c 2^n, ..., c 2^n + 2^n - 1, and zero elsewhere. -/
def blockTable (n c : ℕ) (g : ℕ → K) (x : ℕ) : K := if x / 2 ^ n = c then g (x % 2 ^ n) else 0

/-- **One aligned block.**

At p ++ s, the block's extension is eq(vertex c, p) times its own table's extension at s. -/
theorem ext_blockTable (g : ℕ → K) (s : List K) :
    ∀ (p : List K) {c : ℕ}, c < 2 ^ p.length →
      rowExt (blockTable s.length c g) (p ++ s) = eq (vertex p.length c) p * rowExt g s
  | [], c, hc => by
    obtain rfl : c = 0 := by simpa using hc
    simp only [List.nil_append, List.length_nil, vertex, List.range_zero, List.map_nil, eq_nil,
      one_mul]
    exact rowExt_congr fun x hx => by
      simp [blockTable, Nat.div_eq_of_lt hx, Nat.mod_eq_of_lt hx]
  | a :: p, c, hc => by
    rw [List.cons_append, ext_cons]
    have hsh : ∀ x, (2 ^ (p ++ s).length + x) / 2 ^ s.length = 2 ^ p.length + x / 2 ^ s.length :=
      fun x => by
        rw [List.length_append, pow_add, Nat.add_comm (2 ^ p.length * 2 ^ s.length) x,
          Nat.add_mul_div_right _ _ (by positivity), Nat.add_comm]
    have hmod : ∀ x, (2 ^ (p ++ s).length + x) % 2 ^ s.length = x % 2 ^ s.length := fun x => by
      rw [List.length_append, pow_add, Nat.add_comm, Nat.add_mul_mod_self_right]
    by_cases hlow : c < 2 ^ p.length
    · have hhigh : rowExt (fun x => blockTable s.length c g (2 ^ (p ++ s).length + x)) (p ++ s) = 0 :=
        (rowExt_congr fun x _ => by
          simp only [blockTable, hsh]; split_ifs with h
          · generalize x / 2 ^ s.length = q at h; omega
          · rfl).trans (rowExt_zero _)
      rw [hhigh, ext_blockTable g s p hlow, List.length_cons, vertex_low hlow, eq_cons]
      ring
    · obtain ⟨c', rfl⟩ : ∃ c', c = 2 ^ p.length + c' := ⟨c - 2 ^ p.length, by omega⟩
      have hc' : c' < 2 ^ p.length := by simp [pow_succ] at hc; omega
      have hlow0 : rowExt (blockTable s.length (2 ^ p.length + c') g) (p ++ s) = 0 := by
        refine (rowExt_congr fun x hx => ?_).trans (rowExt_zero _)
        have : x / 2 ^ s.length < 2 ^ p.length := by
          rw [Nat.div_lt_iff_lt_mul (by positivity), ← pow_add]
          simpa [Nat.add_comm] using hx
        simp only [blockTable]; split_ifs with h
        · exact absurd h (by omega)
        · rfl
      have hhigh : rowExt (fun x => blockTable s.length (2 ^ p.length + c') g (2 ^ (p ++ s).length + x))
          (p ++ s) = rowExt (blockTable s.length c' g) (p ++ s) :=
        rowExt_congr fun x _ => by simp only [blockTable, hsh, hmod, Nat.add_left_cancel_iff]
      rw [hlow0, hhigh, ext_blockTable g s p hc', List.length_cons, vertex_high hc', eq_cons]
      ring

end Plonky3Lean.Proofs.MultiStark
