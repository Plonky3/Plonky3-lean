module

public import Plonky3Lean.Spec.Sponge
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Data.Nat.Cast.Defs

@[expose] public section

/-!
# The duplex construction over a field

The duplex construction of Bertoni, Daemen, Peeters and Van Assche (SAC 2011), Section 3.

Their paper is "Duplexing the sponge: single-pass authenticated encryption and other applications".

A duplex object keeps a state of w cells and a permutation f of states.

Each duplexing call takes an input block sigma of at most r cells.

It pads the block into the first r cells (the rate), applies f, and returns the new rate.

The cells here are field elements.

The rate is overwritten rather than added to.

This is the overwrite mode of Bertoni et al., "Sponge-based pseudo-random number generators" (CHES 2010).

The padding writes zeros after the block.

It adds the block length to the first cell after the rate.

A call with an empty block is a blank call: it applies f and nothing else.

```text
    blank call:       [ s_0 ... s_{r-1}        | s_r              s_{r+1} ... ]
    absorbing call:   [ sigma_0 ... 0 ... 0    | s_r + len(sigma)  s_{r+1} ... ]
```

# Transcripts

A Fiat-Shamir transcript alternates two kinds of phases.

* An observing phase absorbs a run of values, cut into blocks of r, one absorbing call per block.
* A sampling phase reads output cells, last rate cell first.
  It makes a blank call whenever a rate has been read in full.

The first sample of a phase reads the rate of the last absorbing call.

So it depends on every value observed before it.

```text
    r = 2, observe a b c, sample 3 times:

      call 1:  f([a, b | s_2 + 2, ...])       = t     (block [a, b])
      call 2:  f([c, 0 | t_2 + 1, ...])       = u     (block [c])
      samples: u_1, u_0, then blank call f(u) = v, sample v_1
```

Nothing here refers to the model.
-/

namespace Plonky3Lean.Spec.Duplex

open Plonky3Lean.Spec.Sponge

variable {F : Type} [AddMonoidWithOne F]

/-- The padded state of a duplexing call on state s with block sigma, for rate r.

An empty block leaves the state as it is.

A nonempty block overwrites the rate with itself and zeros, and adds its length to cell r. -/
def pad (r : ℕ) (s sigma : List F) : List F :=
  if sigma = [] then s
  else sigma ++ List.replicate (r - sigma.length) 0 ++ (s.getD r 0 + (sigma.length : F)) :: s.drop (r + 1)

/-- One duplexing call: pad, then permute. -/
def duplex (f : List F → List F) (r : ℕ) (s sigma : List F) : List F := f (pad r s sigma)

/-- A run of n blank calls. -/
def blank (f : List F → List F) : ℕ → List F → List F
  | 0, s => s
  | n + 1, s => blank f n (f s)

/-- An observing phase: one absorbing call per block of r. -/
def absorbRun (f : List F → List F) (r : ℕ) (s xs : List F) : List F :=
  (blocks r xs).foldl (duplex f r) s

/-- The j-th sample of a phase whose first readable rate is that of state s.

Samples read a rate from its last cell down, then move to the next blank call. -/
def phaseSample (f : List F → List F) (r : ℕ) (s : List F) (j : ℕ) : F :=
  (blank f (j / r) s).getD (r - 1 - j % r) 0

/-- The state whose rate a phase reads first.

After observations, it is the state of the last absorbing call.

With no observation, it is the state of a blank call. -/
def phaseFirst (f : List F → List F) (r : ℕ) (s xs : List F) : List F :=
  if xs = [] then f s else absorbRun f r s xs

/-- The samples of one phase: the values xs observed, then k samples drawn, from state s. -/
def phase (f : List F → List F) (r : ℕ) (s xs : List F) (k : ℕ) : List F :=
  (List.range k).map (phaseSample f r (phaseFirst f r s xs))

/-- The state after a phase that draws k > 0 samples.

It is the state of the last call whose rate was read. -/
def phaseState (f : List F → List F) (r : ℕ) (s xs : List F) (k : ℕ) : List F :=
  blank f ((k - 1) / r) (phaseFirst f r s xs)

/-- The samples of a transcript, given as its phases.

Each phase is the values observed, then a number of samples. -/
def transcript (f : List F → List F) (r : ℕ) : List F → List (List F × ℕ) → List F
  | _, [] => []
  | s, (xs, k) :: ps => phase f r s xs k ++ transcript f r (phaseState f r s xs k) ps

/-- A list of phases is well formed when:

- each phase draws a sample
- each phase after the first observes a value.

Two phases that break this are one phase. -/
def WellFormed (ps : List (List F × ℕ)) : Prop :=
  (∀ p ∈ ps, 0 < p.2) ∧ ∀ p ∈ ps.drop 1, p.1 ≠ []

end Plonky3Lean.Spec.Duplex
