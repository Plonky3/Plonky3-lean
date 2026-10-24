/-
Transcriptions of integer_mul: the exponent lift of a full-width product.

The challenge field is a Lean field.

Its generator is a parameter, read as the Rust constant of the same name.

A word is the natural number of its bits.

Every table index stays below the table's length, which the proofs check.
-/
module

public import P3Word

@[expose] public section

namespace p3_word_backend.integer_mul.mirror

variable {F : Type _} [Field F]

/-- The tree a reduction walks: the factor tree or the result tree. -/
inductive Tree where
  | Factor
  | Result
deriving DecidableEq

/-- Layers between the root and the leaves of a tree, for words of $2^k$ bits. -/
def Tree.depth (k : ℕ) : Tree → ℕ
  | .Factor => 2 * k
  | .Result => k + 1

/-- The reduction of one statement: row and bit variables, or nothing without a product. -/
structure IntegerMulReduction where
  row_variables : ℕ
  bit_variables : ℕ

/-- Nothing when the statement declares no product.

Otherwise the rows are padded to the next power of two. -/
def IntegerMulReduction.new (relations bit_variables : ℕ) : Option IntegerMulReduction :=
  if relations = 0 then none
  else some ⟨Nat.log2 relations.nextPowerOfTwo, bit_variables⟩

/-- The word width. -/
def IntegerMulReduction.width (r : IntegerMulReduction) : ℕ := 2 ^ r.bit_variables

/-- The field check.

It refuses a field whose order has at most twice the word width in bits. -/
def check_field (order : ℕ) (width : ℕ) : Except ℕ Unit :=
  if order.size ≤ 2 * width then .error (2 * width) else .ok ()

/-- The successive squares of the generator, as many as asked for. -/
def generator_squarings (g : F) (count : ℕ) : List F :=
  List.iterate (fun p => p ^ 2) g count

/-- The factor-tree weights, with $i$ major and $j$ minor. -/
def factor_weights (g : F) (width : ℕ) : List F :=
  let powers := generator_squarings g (2 * width - 1)
  (List.range width).flatMap fun i => ((powers.drop i).take width).map (· - 1)

/-- The result-tree weights, one per bit of the two limbs. -/
def result_weights (g : F) (width : ℕ) : List F :=
  (generator_squarings g (2 * width)).map (· - 1)

/-- The factor-tree leaves of every row, addressed $(row, i, j)$.

Leaf $(i, j)$ is the power of bit pair $(i, j)$ when both bits are set, and one otherwise. -/
def factor_leaves (left right : List ℕ) (width : ℕ) (powers : List F) : List F :=
  (left.zip right).flatMap fun (a, b) =>
    (List.range width).flatMap fun i =>
      (List.range width).map fun j =>
        if (a >>> i) &&& (b >>> j) &&& 1 = 1 then powers.getD (i + j) 1 else 1

/-- The result-tree leaves of every row, addressed $(row, t)$.

Leaf $t$ is the power of bit $t$ of the two limbs when that bit is set, and one otherwise. -/
def result_leaves (low high : List ℕ) (width : ℕ) (powers : List F) : List F :=
  (low.zip high).flatMap fun (lo, hi) =>
    let limbs := lo ||| (hi <<< width)
    (List.range (2 * width)).map fun t =>
      if (limbs >>> t) &&& 1 = 1 then powers.getD t 1 else 1

/-- One layer up a product tree: each pair of adjacent entries is multiplied. -/
def layer_above (below : List F) : List F :=
  (List.range (below.length / 2)).map fun r => below.getD (2 * r) 0 * below.getD (2 * r + 1) 0

/-- Every layer of a product tree above its leaves, root first, leaves last. -/
def product_layers (leaves : List F) (depth : ℕ) : List (List F) :=
  ((List.range depth).foldl (fun layers _ => layer_above (layers.headD []) :: layers) [leaves])

end p3_word_backend.integer_mul.mirror
