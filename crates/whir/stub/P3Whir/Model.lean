/-
The objects the transcriptions of p3-whir are written in.

* The fields, the sponge and its history are those of the p3-sumcheck transcriptions.
* A query-index draw is a function of the history, the bit width and the count.
* A commitment is absorbed as the extension elements of an encoding.
* A Merkle multi-opening check is a predicate on the root, the dimensions, the indices, the rows and the proof.
* The two-adic generator of order 2^bits is a function of bits, and it panics past the two-adicity.
* The layout that batches the opening claims is its seed step and the constraint it builds from its challenge.
* The opening and closing brackets of a delegated sumcheck absorb nothing.

Loops, branches, early returns and the order of transcript steps are kept.
-/
module

public import P3Sumcheck

@[expose] public section

namespace p3_whir.mirror

open p3_sumcheck.mirror

/-- The sponge of a WHIR run: the sumcheck sponge, and the query indices it draws. -/
structure WSponge (F EF : Type _) extends Sponge F EF where
  /-- count indices of the given bit width, drawn after the history. -/
  indices : List (Step F EF) → ℕ → ℕ → List ℕ

/-- The base-field Merkle scheme and its extension view, as their multi-opening checks. -/
structure Mmcs (F EF Com MP : Type _) where
  /-- verify_multi_batch on base-field rows, for one matrix of the given (height, width). -/
  verifyBase : Com → ℕ × ℕ → List ℕ → List (List F) → MP → Bool
  /-- The same through ExtensionMmcs, on extension rows. -/
  verifyExt : Com → ℕ × ℕ → List ℕ → List (List EF) → MP → Bool

/-- two_adic_generator: the generator of order 2^bits, which asserts bits is at most the two-adicity. -/
def two_adic_generator {F : Type _} (adicity : ℕ) (gen : ℕ → F) (bits : ℕ) : Option F :=
  if bits ≤ adicity then some (gen bits) else none

end p3_whir.mirror
