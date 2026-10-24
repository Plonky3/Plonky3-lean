/-
Transcriptions of the two-adic multiplicative coset.

What a transcription abstracts:

- the field is a mathlib field K
- the field's two-adic generators are a table gen, defined up to the index adicity
- the private fields carry the constructor's invariant: a nonzero shift and a size the table covers
- the cached inverse of the shift is its inverse in K
- an iterator is the list it yields
- a panic is none.

Loops, branches and early returns are kept.
-/
module

public import Mathlib.Algebra.Field.Basic
public import Mathlib.Data.List.Range

@[expose] public section

namespace p3_field.coset.mirror

variable {K : Type _} [Field K] [DecidableEq K] {adicity : ℕ} {gen : ℕ → K}

/-- The coset shift H of the subgroup H of order 2^log_size. -/
structure TwoAdicMultiplicativeCoset (K : Type _) [Field K] (adicity : ℕ) (gen : ℕ → K) where
  shift : K
  log_size : ℕ
  shift_ne_zero : shift ≠ 0
  log_size_le : log_size ≤ adicity

namespace TwoAdicMultiplicativeCoset

/-- The constructor: a zero shift, or a size beyond the table, returns nothing. -/
def new (shift : K) (log_size : ℕ) : Option (TwoAdicMultiplicativeCoset K adicity gen) :=
  if h : shift ≠ 0 ∧ log_size ≤ adicity then some ⟨shift, log_size, h.1, h.2⟩ else none

/-- The generator of the subgroup: the table's entry at the coset's size. -/
def subgroup_generator (c : TwoAdicMultiplicativeCoset K adicity gen) : K := gen c.log_size

/-- The inverse of the shift, which the constructor caches. -/
def shift_inverse (c : TwoAdicMultiplicativeCoset K adicity gen) : K := c.shift⁻¹

/-- The number of elements, 2^log_size. -/
def size (c : TwoAdicMultiplicativeCoset K adicity gen) : ℕ := 2 ^ c.log_size

/-- The same shift over a subgroup 2^k times smaller, for k the log scale factor.

It is nothing if that underflows. -/
def shrink_coset (c : TwoAdicMultiplicativeCoset K adicity gen) (log_scale_factor : ℕ) :
    Option (TwoAdicMultiplicativeCoset K adicity gen) :=
  if h : log_scale_factor ≤ c.log_size then
    some ⟨c.shift, c.log_size - log_scale_factor, c.shift_ne_zero, by have := c.log_size_le; omega⟩
  else none

/-- The image of the coset under x |-> x^(2^k), for k the log scale factor.

It is the shrunk coset, with the shift raised. -/
def exp_power_of_2 (c : TwoAdicMultiplicativeCoset K adicity gen) (log_scale_factor : ℕ) :
    Option (TwoAdicMultiplicativeCoset K adicity gen) :=
  (c.shrink_coset log_scale_factor).map fun d =>
    ⟨c.shift ^ 2 ^ log_scale_factor, d.log_size, pow_ne_zero _ c.shift_ne_zero, d.log_size_le⟩

/-- Replace the shift.

Inverting a zero shift panics. -/
def set_shift (c : TwoAdicMultiplicativeCoset K adicity gen) (shift : K) :
    Option (TwoAdicMultiplicativeCoset K adicity gen) :=
  if h : shift ≠ 0 then some ⟨shift, c.log_size, h, c.log_size_le⟩ else none

/-- Multiply the shift by a scale.

Inverting a zero product panics. -/
def shift_by (c : TwoAdicMultiplicativeCoset K adicity gen) (scale : K) :
    Option (TwoAdicMultiplicativeCoset K adicity gen) :=
  c.set_shift (c.shift * scale)

/-- One iteration of the membership loop.

Return on a match, otherwise square both sides. -/
def containsStep : (K × K) ⊕ Bool → Unit → (K × K) ⊕ Bool
  | .inr b, _ => .inr b
  | .inl (s, e), _ => if e = s then .inr true else .inl (s ^ 2, e ^ 2)

/-- Membership: log_size rounds of the loop, then a final comparison. -/
def contains (c : TwoAdicMultiplicativeCoset K adicity gen) (element : K) : Bool :=
  match (List.replicate c.log_size ()).foldl containsStep (.inl (c.shift, element)) with
  | .inr b => b
  | .inl (s, e) => decide (e = s)

/-- The bit loop of the generator power.

Bit j of the exponent multiplies by gen (log_size - j). -/
def generator_exp_loop : ℕ → ℕ → K → ℕ → K
  | 0, _, acc, _ => acc
  | fuel + 1, exp, acc, i =>
    if exp = 0 then acc
    else generator_exp_loop fuel (exp / 2) (if exp % 2 ≠ 0 then acc * gen i else acc) (i - 1)

/-- The generator to the power exp mod size, one table entry per set bit. -/
def generator_exp (c : TwoAdicMultiplicativeCoset K adicity gen) (exp : ℕ) : K :=
  generator_exp_loop (gen := gen) (exp % c.size) (exp % c.size) 1 c.log_size

/-- Element index of the coset: the shift times a power of the generator. -/
def element (c : TwoAdicMultiplicativeCoset K adicity gen) (index : ℕ) : K :=
  c.shift * c.generator_exp index

/-- The elements in order: shift, shift g, shift g^2, ..., size of them. -/
def iter (c : TwoAdicMultiplicativeCoset K adicity gen) : List K :=
  (List.range c.size).map fun i => c.shift * c.subgroup_generator ^ i

end TwoAdicMultiplicativeCoset

end p3_field.coset.mirror
