/-
Transcriptions, over natural numbers and lists, of parts of the challengers.

These parts need p3-field's big-integer surface or SIMD packing (docs/extractor-issues.md 62).

What a transcription abstracts:

- a field element is its canonical value, a natural number below the order
- a big-integer loop is a loop over natural numbers, with fuel well above its trip count
- a packed permutation over SIMD lanes is the scalar permutation, applied lane by lane.

Branches, assertions and the order of operations are kept.
-/
module

public import Mathlib.Data.List.Basic
public import Mathlib.Data.Nat.Log
public import Mathlib.Data.Nat.Cast.Defs

@[expose] public section

namespace p3_challenger.mirror

/-! ## p3-field helpers (field/src/helpers.rs) -/

/-- The squeeze limb count (helpers.rs:319).

It counts the powers of p whose product with p stays below q, minus one.

The loop multiplies by p > 1, so it runs at most log_2 q times.

256 rounds of fuel cover any q < 2^256. -/
def squeezeLoop (p q : ℕ) : ℕ → ℕ → ℕ → ℕ
  | 0, _, count => count
  | fuel + 1, power, count => if power * p < q then squeezeLoop p q fuel (power * p) (count + 1) else count

def squeeze_field_order_num_limbs (p q : ℕ) : ℕ := squeezeLoop p q 256 1 0 - 1

/-- The most limbs that pack injectively (helpers.rs:197).

It is the largest k with d (1 + 2^b + ... + 2^(b (k-1))) < q, for d the largest digit. -/
def maxPackedLoop (maxDigit b q : ℕ) : ℕ → ℕ → ℕ → ℕ → ℕ
  | 0, k, _, _ => k
  | fuel + 1, k, maxVal, power =>
    if maxVal + maxDigit * power ≥ q then k
    else maxPackedLoop maxDigit b q fuel (k + 1) (maxVal + maxDigit * power) (power * 2 ^ b)

/-- The absorb radix width (helpers.rs:164): the bit length of p - 1. -/
def absorb_radix_bits (p : ℕ) : ℕ := Nat.log 2 (p - 1) + 1

/-- The most base-field limbs one absorb packs injectively (helpers.rs:238). -/
def max_absorb_injective_limbs (p q : ℕ) : ℕ := maxPackedLoop (p - 1) (absorb_radix_bits p) q 256 0 0 1

/-! ## The multi-field challenger (challenger/src/multi_field_challenger.rs) -/

/-- Why the multi-field constructor refuses. -/
inductive NewError
  | fieldOrderNotIncreasing
  | absorbLengthTagOverflow

/-- The multi-field constructor at the pinned commit (multi_field_challenger.rs:118).

It checks the two orders and the length tag, nothing more. -/
def MultiField32Challenger.new (p q rate : ℕ) : Except NewError Unit :=
  if p ≥ q then .error .fieldOrderNotIncreasing
  else if max_absorb_injective_limbs p q * rate > 255 then .error .absorbLengthTagOverflow
  else .ok ()

/-- The first n base-p digits of x (helpers.rs:340). -/
def split_pf_to_field_order_limbs (p x : ℕ) : ℕ → List ℕ
  | 0 => []
  | n + 1 => x % p :: split_pf_to_field_order_limbs p (x / p) n

/-- The squeeze refill: the limbs of every output cell, in order.

Upstream: multi_field_challenger.rs:177. -/
def refill (p n : ℕ) (outputs : List ℕ) : List ℕ :=
  outputs.flatMap (fun x => split_pf_to_field_order_limbs p x n)

/-- The tail of the multi-field sampler (multi_field_challenger.rs:294).

With an empty queue, refill from the rate cells, then pop.

None is the panic on an empty output buffer. -/
def sampleFromQueue (p n : ℕ) (queue rate : List ℕ) : Option ℕ :=
  let queue' := if queue = [] then refill p n rate else queue
  queue'.getLast?

/-! ## The SIMD grinding search (challenger/src/grinding_challenger.rs) -/

/-- The pre-permutation state the duplex grind builds for one candidate.

Upstream: grinding_challenger.rs:208 and :268.

- buffered inputs fill the first cells
- the candidate takes the next one
- the rest of the rate is zero
- the length tag is added to the first cell past the rate
- the capacity is kept. -/
def grindState {F : Type} [AddMonoidWithOne F] (rate width : ℕ) (s inb : List F) (w : F) : List F :=
  (List.range width).map fun i =>
    if i < inb.length then inb.getD i 0
    else if i = inb.length then w
    else if i < rate then 0
    else if i = rate then s.getD rate 0 + ((inb.length + 1 : ℕ) : F)
    else s.getD i 0

end p3_challenger.mirror
