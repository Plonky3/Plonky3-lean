module

public import Mathlib.Data.List.Basic

@[expose] public section

/-!
# The multi-height Merkle tree

This is the tree Plonky3's Merkle MMCS commits to.

It is read from that crate's documentation and from the builder's description of one node.

# Overview

The tallest matrices fill the leaf layer.

Leaf i is the hash of row i of each of them, concatenated.

The layer is padded with a default digest z to the width the next fold needs.

Each layer above folds s children into one node, where s is 2 or the full arity N.

Some layers also take in the rows of shorter matrices:

```text
    folded = C(child_{s j}, ..., child_{s j + s - 1}, z, ..., z)
    node_j = folded                         no matrix enters here
    node_j = C(folded, H(rows_j), z, ...)   matrices enter here, j below their height
    node_j = C(folded, z, z, ...)           matrices enter here, j at or past their height
```

The padding slots of a fold, and the slots past the second of an injection, hold z.
-/

namespace Plonky3Lean.Spec.MerkleTree

variable {F D : Type _}

/-- One layer of the tree: how many children each node folds, and what enters it.

What enters is either nothing, or the matrices' height and the hash of their rows at each node. -/
structure LayerSpec (D : Type _) where
  step : ℕ
  inj : Option (ℕ × (ℕ → D))

/-- The fold of s children starting at start of the layer L, padded with pad. -/
def fold (c : List D → D) (pad : List D) (z : D) (L : ℕ → D) (s start : ℕ) : D :=
  c ((List.range pad.length).map fun k => if k < s then L (start + k) else pad.getD k z)

/-- Node j of the layer above L. -/
def node (c : List D → D) (pad : List D) (z : D) (L : ℕ → D) (l : LayerSpec D) (j : ℕ) : D :=
  let folded := fold c pad z L l.step (j * l.step)
  match l.inj with
  | none => folded
  | some (height, rows) => c ((pad.set 0 folded).set 1 (if j < height then rows j else z))

/-- The layers of the tree, from the leaf layer L0 up through the given layer specifications. -/
def layers (c : List D → D) (pad : List D) (z : D) (L0 : ℕ → D) : List (LayerSpec D) → List (ℕ → D)
  | [] => [L0]
  | l :: rest => L0 :: layers c pad z (node c pad z L0 l) rest

/-- The top layer: the cap, or the root when the cap is one digest. -/
def top (c : List D → D) (pad : List D) (z : D) (L0 : ℕ → D) : List (LayerSpec D) → ℕ → D
  | [] => L0
  | l :: rest => top c pad z (node c pad z L0 l) rest

/-- The siblings an honest prover sends for leaf i.

At each layer, they are the other children of the path's node, in order. -/
def path (c : List D → D) (pad : List D) (z : D) (L0 : ℕ → D) : List (LayerSpec D) → ℕ → List D
  | [], _ => []
  | l :: rest, i =>
    ((List.range l.step).filter (· ≠ i % l.step)).map (fun k => L0 (i / l.step * l.step + k)) ++
      path c pad z (node c pad z L0 l) rest (i / l.step)

end Plonky3Lean.Spec.MerkleTree
