/-
The objects the transcriptions of p3-sumcheck are written in.

* The extension field EF is a mathlib field, and the base field F is any type.
* A vector or a slice is a list, and a panic is none.
* A debug assertion panics, as in a debug build.
* The Fiat-Shamir sponge is its history: the list of steps absorbed so far.
* A challenge is a function of that history, and a grinding check is a predicate on it.
* The domain separator is one seed step that carries the numbers its pattern hashes.

Loops, branches, early returns and the order of transcript steps are kept.
-/
module

public import Mathlib.Algebra.Field.Basic

@[expose] public section

namespace p3_sumcheck.mirror

/-- One step a Fiat-Shamir transcript absorbs. -/
inductive Step (F EF : Type _) where
  /-- The domain separator: a protocol name and the numbers of its shape. -/
  | seed (name : String) (shape : List ℕ)
  /-- A prover message of extension elements. -/
  | message (values : List EF)
  /-- A grinding witness, checked at the given difficulty. -/
  | pow (bits : ℕ) (witness : F)
  /-- A challenge drawn. -/
  | challenge

/-- The sponge: what it samples and which witnesses it accepts, both as functions of its history. -/
structure Sponge (F EF : Type _) where
  sample : List (Step F EF) → EF
  grind : List (Step F EF) → ℕ → F → Bool

end p3_sumcheck.mirror
