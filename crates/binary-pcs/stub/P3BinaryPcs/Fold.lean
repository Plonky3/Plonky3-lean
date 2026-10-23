/-
Transcriptions of fold.rs: one fold pair, one round of the tower-basis route, and one coset.

The alphabet F sits in the challenge field EF through its algebra map.

The domain points come from the alphabet's own level.

The packed route is not transcribed.
-/
module

public import P3BinaryPcs.Model

@[expose] public section

namespace p3_binary_pcs.fold.mirror

open p3_binary_dft.mirror p3_binary_dft.domain.mirror

variable {F EF : Type _} [Field F] [Field EF] [Algebra F EF]

/-- fold_pair: the novel-basis halves f_1 = lo + hi and f_0 = lo + x f_1 at x the point of 2 index, combined as f_0 + beta (f_0 + f_1).

The doubled index wraps at the word. -/
def fold_pair (L : Level F) (index : ℕ) (beta : EF) (lo hi : F) : Option EF := do
  let x ← domain_point L (2 * index % 2 ^ 64)
  let f1 := lo + hi
  let f0 := lo + x * f1
  pure (beta * algebraMap F EF (f0 + f1) + algebraMap F EF f0)

/-- FOLD_GRAIN: the output symbols one task owns. -/
def FOLD_GRAIN : ℕ := 2 ^ 10

/-- fold_round: each task of FOLD_GRAIN outputs evaluates its first point, then walks the domain by the steps table.

A trailing unpaired symbol is dropped. -/
def fold_round (L : Level F) (codeword : List F) (beta : EF) : Option (List EF) := do
  let num_pairs := codeword.length / 2
  let steps ← domain_point_steps L (trailingZeros num_pairs.nextPowerOfTwo)
  let tasks := (num_pairs + FOLD_GRAIN - 1) / FOLD_GRAIN
  let chunks ← (List.range tasks).mapM fun task => do
    let start := task * FOLD_GRAIN
    let x0 ← domain_point L (2 * start % 2 ^ 64)
    let out ← (List.range (min FOLD_GRAIN (num_pairs - start))).foldlM
      (fun (acc : F × List EF) offset => do
        let x ← if offset ≠ 0 then (steps[trailingZeros (start + offset)]?).map (acc.1 + ·)
          else pure acc.1
        let lo := codeword.getD (2 * (start + offset)) 0
        let hi := codeword.getD (2 * (start + offset) + 1) 0
        let f1 := lo + hi
        let f0 := lo + x * f1
        pure (x, acc.2 ++ [beta * algebraMap F EF (f0 + f1) + algebraMap F EF f0])) (x0, [])
    pure out.2
  pure chunks.flatten

/-- One in-place layer of fold_coset: the live prefix of `len` symbols, folded at the offset of the coset. -/
def coset_layer (L : Level EF) (coset_index len : ℕ) (beta : EF) (scratch : List EF) :
    Option (List EF) :=
  (List.range len).mapM fun i =>
    fold_pair L (coset_index * len + i) beta (scratch.getD (2 * i) 0) (scratch.getD (2 * i + 1) 0)

/-- fold_coset: the first round reads the alphabet, every later one folds the live prefix in place.

It asserts one symbol per leaf of the challenge tree, and panics without a challenge.

Writing slot i reads slots 2 i and 2 i + 1, which no earlier write of the layer touched, so the layer is a map of the prefix. -/
def fold_coset (LF : Level F) (LE : Level EF) (coset_index : ℕ) (values : List F)
    (challenges : List EF) : Option EF := do
  if values.length ≠ 2 ^ challenges.length then none
  let beta0 ← challenges.head?
  let len := values.length / 2
  let first ← (List.range len).mapM fun i =>
    fold_pair LF (coset_index * len + i) beta0 (values.getD (2 * i) 0) (values.getD (2 * i + 1) 0)
  let (_, scratch) ← challenges.tail.foldlM (fun (acc : ℕ × List EF) beta => do
    let len := acc.1 / 2
    let layer ← coset_layer LE coset_index len beta acc.2
    pure (len, layer ++ acc.2.drop len)) (len, first)
  scratch.head?

end p3_binary_pcs.fold.mirror
