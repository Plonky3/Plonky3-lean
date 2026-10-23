/-
The objects the transcriptions of p3-binary-pcs are written in.

* The fields, the sponge and its history are those of the p3-sumcheck transcriptions.
* A draw of query pairs is a function of the history, the bit width and the count.
* Its values lie below two to the width, and there are as many as asked for, as the rejection loop guarantees when it returns.
* A commitment is absorbed as the extension elements of an encoding.
* A Merkle multi-opening check is a function of the root, the dimensions, the indices, the rows and the proof.
* A tower level is the level of the p3-binary-dft transcriptions: its bit width and its Cantor basis.

Loops, branches, early returns and the order of transcript steps are kept.

A panic is none.
-/
module

public import P3Sumcheck
public import P3BinaryDft

@[expose] public section

namespace p3_binary_pcs.mirror

open p3_sumcheck.mirror

/-- The sponge of a binary PCS run: the sumcheck sponge, and the query pairs it draws. -/
structure PSponge (F EF : Type _) extends Sponge F EF where
  /-- count pair indices of the given bit width, drawn after the history. -/
  pairs : List (Step F EF) → (width count : ℕ) → Fin count → Fin (2 ^ width)

/-- The two Merkle schemes, as their multi-opening checks: the base one over the alphabet, the round one over the challenge field. -/
structure Mmcs (F EF ComT ComX MPT MPX E : Type _) where
  /-- verify_multi_batch of the base scheme, for one matrix of the given (width, height). -/
  verifyBase : ComT → ℕ × ℕ → List ℕ → List (List F) → MPT → Except E Unit
  /-- verify_multi_batch of the round scheme. -/
  verifyRound : ComX → ℕ × ℕ → List ℕ → List (List EF) → MPX → Except E Unit

end p3_binary_pcs.mirror
