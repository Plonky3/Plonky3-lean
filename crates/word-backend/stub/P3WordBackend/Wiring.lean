/-
Transcriptions of shift/wiring.rs: a word read at a bit point, and the transpose of a fixed shift.

The weights are a Lean list over a ring.

Reading an index past its end panics.

The word operations are those of p3-word's extraction.
-/
module

public import P3Word

@[expose] public section

namespace p3_word_backend.shift.wiring.mirror

open Aeneas Aeneas.Std p3_word

variable {W R : Type} [AddCommMonoid R]

/-- The entry at an index, or a panic past the end. -/
def at? (weights : List R) (i : ℕ) : RustM R :=
  match weights[i]? with
  | some w => .ok w
  | none => .fail .panic

/-- The sum of the weights at the set bits of a 64-bit pattern, below a bit count. -/
def setBitsSum (bits : ℕ) (pattern : ℕ) (weights : List R) : RustM R :=
  ((List.range bits).filter fun bit => (pattern >>> bit) &&& 1 = 1).foldlM
    (fun acc bit => do let w ← at? weights bit; .ok (acc + w)) 0

/-- One word's bit multilinear at a point: the weights of its set bits, summed. -/
def evaluate_word (inst : word.Word W) (w : W) (weights : List R) : RustM R := do
  let bits ← inst.to_u64 w
  let n ← inst.BITS
  setBitsSum n.val bits.val weights

/-- The transpose of one shift applied to a table of output weights.

The identity keeps the table.

Otherwise column $j$ sums the weights of the bits the basis word $2^j$ reaches. -/
def shift_transpose (inst : word.Word W) (s : shift.Shift W) (output : List R) :
    RustM (List R) := do
  let identity ← shift.Shift.is_identity inst s
  if identity then .ok output
  else
    let n ← inst.BITS
    (List.range n.val).mapM fun input => do
      let basis ← inst.from_low_bits ⟨BitVec.ofNat _ (2 ^ input)⟩
      let shifted ← shift.Shift.apply inst s basis
      let bits ← inst.to_u64 shifted
      setBitsSum n.val bits.val output

/-- The transpose of a two-slot sequence: the outer slot first, then the inner one. -/
def shift_weights (inst : word.Word W) (shifts : Array (shift.Shift W) 2#usize)
    (output : List R) : RustM (List R) := do
  let inner ← Array.index_usize shifts 0#usize
  let outer ← Array.index_usize shifts 1#usize
  let intermediate ← shift_transpose inst outer output
  shift_transpose inst inner intermediate

end p3_word_backend.shift.wiring.mirror
