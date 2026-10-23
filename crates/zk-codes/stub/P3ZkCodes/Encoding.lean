/-
Transcriptions of the encoding traits' default methods.

What a transcription abstracts:

* a matrix is its height, its width and its entries, read by row and column;
* the single-message encoding is a parameter, of the shape of the Reed-Solomon transcription.

Loops, branches and the order of operations are kept.
-/
module

public import Mathlib.Algebra.Field.Basic
public import Mathlib.Data.List.Range

@[expose] public section

namespace p3_zk_codes.encoding.mirror

/-- A matrix: its height, its width, and entry (row, column). -/
structure Mat (K : Type _) where
  height : ℕ
  width : ℕ
  get : ℕ → ℕ → K

variable {K : Type _} [Field K]

/-- Interleave single-column codewords into one matrix: row r is the r-th entry of each codeword.

The batch must be nonempty, and every codeword must be one column of the first codeword's height.

Row r of column c is entry r w + c of the flat buffer. -/
def stack_codewords (codewords : List (Mat K)) : Option (Mat K) := do
  match codewords with
  | [] => none
  | c0 :: _ =>
    let height := c0.height
    let width := codewords.length
    let values ← codewords.zipIdx.foldlM (fun (values : ℕ → K) cc =>
      let (codeword, column) := cc
      if codeword.width ≠ 1 then none
      else if codeword.height ≠ height then none
      else some ((List.range codeword.height).foldl (fun acc row =>
        fun i => if i = row * width + column then codeword.get row 0 else acc i) values))
      (fun _ => 0)
    pure ⟨height, width, fun r c => values (r * width + c)⟩

/-- The default batch encoding: assert the batch shape, encode each pair, and interleave the codewords. -/
def encode_batch_with_randomness (encode_with_randomness : List K → List K → Option (Mat K))
    (messages randomness : List (List K)) : Option (Mat K) := do
  if messages.isEmpty then none
  else if messages.length ≠ randomness.length then none
  else
    let codewords ← (messages.zip randomness).mapM fun mr => encode_with_randomness mr.1 mr.2
    stack_codewords codewords

end p3_zk_codes.encoding.mirror
