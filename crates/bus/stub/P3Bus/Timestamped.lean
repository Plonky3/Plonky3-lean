/-
Transcriptions of the timestamped read-write memory: its clock, its gap proof, its orbit checks, and its range tables.

These do not extract: they are generic over the field traits.

The crate's dependencies also fail to compile in the extraction variant (docs/extractor-issues.md 180).

Each definition transcribes one Rust item, named in the crate's mirror entries.

What a transcription abstracts:

- the clock field C is a mathlib field
- its generator g and its order are parameters, read through the field trait
- the bus field is C itself, so embedding a clock value is the identity
- big-integer arithmetic is natural-number arithmetic
- a builder is the declaring builder record
- a panic is none.

Loops, branches and the order of operations are kept.
-/
module

public import P3Bus.Builder

@[expose] public section

namespace p3_bus.timestamped.mirror

open p3_air.builder.mirror p3_bus.mirror

/-- Bits of each gap digit. -/
def CLOCK_RANGE_BITS : ℕ := 16

/-- Bits of the largest gap one access proves. -/
def CLOCK_GAP_BITS : ℕ := 2 * CLOCK_RANGE_BITS

/-- The errors of the timestamped memory that the orbit checks raise. -/
inductive TimestampedMemoryError where
  | ClockOrbitTooShort (orbit_bits minimum_bits : ℕ)
  | TooManyAccesses (pulls gap_bits : ℕ)
  | TupleCountOverflow
  deriving DecidableEq

/-- The order of the clock tick, |C| - 1. -/
def clock_orbit (order : ℕ) : ℕ := order - 1

/-- The orbit check of the memory constructor.

A gap of up to 2^32 must never be a multiple of the orbit. -/
def check_orbit (order : ℕ) : Except TimestampedMemoryError Unit :=
  let orbit := clock_orbit order
  if orbit ≤ 2 ^ CLOCK_GAP_BITS then .error (.ClockOrbitTooShort orbit.size (CLOCK_GAP_BITS + 1))
  else .ok ()

/-- The access bound against a bus.

n pulls climb at most n 2^32 ticks, which must stay below the orbit. -/
def check_accesses (order pulls : ℕ) : Except TimestampedMemoryError Unit :=
  if pulls * 2 ^ CLOCK_GAP_BITS ≥ clock_orbit order then .error (.TooManyAccesses pulls CLOCK_GAP_BITS)
  else .ok ()

variable {C : Type _} [Field C]

/-- The step between two high factors, g^(-2^16). -/
def high_step (g : C) : C := (g ^ 2 ^ CLOCK_RANGE_BITS)⁻¹

/-- The factors of a gap d = (j + 1) + 2^16 m.

The low factor is g^(j + 1), and the high factor is g^(-2^16 m).

It is none outside 1 to 2^32. -/
def gap_factors (g : C) (gap : ℕ) : Option (C × C) :=
  if gap = 0 ∨ gap > 2 ^ CLOCK_GAP_BITS then none
  else
    let low_digit := (gap - 1) % 2 ^ CLOCK_RANGE_BITS
    let high_digit := (gap - 1) / 2 ^ CLOCK_RANGE_BITS
    some (g ^ (low_digit + 1), high_step g ^ high_digit)

/-- The time of slot k on a row at clock g^0, which is g^k. -/
def slot_offset (g : C) (slot : ℕ) : C := g ^ slot

/-- The low factor on row j of the range table, g^(j + 1). -/
def ClockRangeAir.low (g : C) (row : ℕ) : C := g ^ (row + 1)

/-- The high factor on row j of the range table, g^(-2^16 j). -/
def ClockRangeAir.high (g : C) (row : ℕ) : C := high_step g ^ row

/-- The gap constraint of one timestamped access, on a builder.

It asserts previous * low = now * high, with now = clock * g^slot. -/
def gap_constraint {S : Type _} (B : AirBuilder C C S) (s : S) (g : C) (clock : C) (slot : ℕ)
    (previous low high : C) : S :=
  let now := B.mul clock (slot_offset g slot)
  B.assert_eq s (B.mul previous low) (B.mul now high)

end p3_bus.timestamped.mirror
