module

public import Mathlib.Data.List.Basic

@[expose] public section

/-!
# Sponges and truncated permutations

The sponge construction of Bertoni, Daemen, Peeters and Van Assche, "Cryptographic sponge functions" (2011), Algorithm 1, in overwrite mode.

A state is a list of `w` cells.

The first `r` cells are the rate and the rest the capacity.

The permutation is any function on states.

```text
    state:  [ s_0 ... s_{r-1} | s_r ... s_{w-1} ]
              rate (outer)      capacity (inner)
```

* **Absorbing.** Each block of input overwrites the front of the rate, then the permutation runs.

* **Squeezing.** The digest is the first `out` cells of the final state.

Two paddings are specified.

* **No padding.** The input is cut into blocks of `r` cells, and the last block may be shorter.

  A short block overwrites only its own cells, so the rest of the rate keeps its old value.

* **10-padding with a capacity domain separator.** A short final block, or an empty input, is completed with the sentinel `d(0)` and zeros.

  An input that ends on a block boundary instead has `d` applied to the first capacity cell before the last permutation.

The truncated permutation compresses `n` chunks by writing them side by side into a zero state, permuting, and keeping the first chunk.

Nothing here refers to the model.
-/

namespace Plonky3Lean.Spec.Sponge

variable {T : Type}

/-- The input cut into blocks of `r` items, in order; the last block may be shorter, and no block is empty. -/
def blocks (r : ℕ) : List T → List (List T)
  | [] => []
  | x :: xs => if r = 0 then [] else (x :: xs).take r :: blocks r ((x :: xs).drop (max r 1))
termination_by l => l.length
decreasing_by simp only [List.length_drop, List.length_cons]; omega

/-- The state `s` with its first cells replaced by `b`. -/
def overwrite (s b : List T) : List T := b ++ s.drop b.length

/-- One absorption: overwrite the front of the rate with the block, then permute. -/
def absorb (f : List T → List T) (s b : List T) : List T := f (overwrite s b)

/-- The padding-free sponge: absorb every block from the zero state, then keep the first `out` cells. -/
def paddingFree (f : List T → List T) (zero : T) (w r out : ℕ) (m : List T) : List T :=
  ((blocks r m).foldl (absorb f) (List.replicate w zero)).take out

/-- The blocks of the 10-padding, and whether the capacity domain separator applies.

An input that is nonempty and a whole number of blocks keeps its blocks, and the separator applies.

Any other input gets one more block: what is left after the whole blocks, then `d(0)`, then zeros up to `r` cells.

```text
    r = 3:  []         ->  [[d0, 0, 0]],               false
            [a]        ->  [[a, d0, 0]],               false
            [a, b, c]  ->  [[a, b, c]],                true
            [a, b, c, e] -> [[a, b, c], [e, d0, 0]],   false
```
-/
def pad10Blocks (zero d0 : T) (r : ℕ) (m : List T) : List (List T) × Bool :=
  if m ≠ [] ∧ m.length % r = 0 then (blocks r m, true)
  else
    let k := m.length / r * r
    (blocks r (m.take k) ++ [m.drop k ++ d0 :: List.replicate (r - (m.length - k) - 1) zero], false)

/-- The 10-padded sponge.

Every block but the last is absorbed as usual.

The last block overwrites the rate; with the separator, `d` is applied to the first capacity cell; then the permutation runs.
-/
def pad10 (f : List T → List T) (d : T → T) (zero : T) (w r out : ℕ) (m : List T) : List T :=
  let p := pad10Blocks zero (d zero) r m
  let s := p.1.dropLast.foldl (absorb f) (List.replicate w zero)
  let s' := overwrite s (p.1.getLastD [])
  let s'' := if p.2 then s'.set r (d (s'.getD r zero)) else s'
  (f s'').take out

/-- The truncated permutation: the chunks side by side, zeros up to `w`, the permutation, and the first `chunk` cells. -/
def truncated (f : List T → List T) (zero : T) (w chunk : ℕ) (input : List (List T)) : List T :=
  (f (input.flatten ++ List.replicate (w - input.flatten.length) zero)).take chunk

end Plonky3Lean.Spec.Sponge
