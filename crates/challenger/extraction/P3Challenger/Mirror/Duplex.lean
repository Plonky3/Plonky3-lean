/-
Transcriptions of the duplex challenger's sampling methods.

aeneas does not elaborate them: each builds its output with a closure over the challenger (docs/extractor-issues.md 60), and the uniform sampler picks a strategy with a `const` generic (item 61).

What a transcription abstracts:

* the sampled type is the base field, so the closure of `from_basis_coefficients_fn` runs once;
* the strategy trait is unfolded into a flag that says whether to reject or to fail.

Loops, branches, assertions and the order of operations are kept.
-/
module

public import P3Challenger.Extraction

@[expose] public section

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM ControlFlow Error

namespace p3_challenger.duplex_challenger.mirror

variable {F P : Type} {W R : Std.Usize}

/-- `<DuplexChallenger as CanSample<F>>::sample` at the base field (`duplex_challenger.rs:253`).

Duplex if inputs are pending or no output is left, then pop the last output. -/
def sample (copyInst : core.marker.Copy F)
    (permInst : p3_symmetric.permutation.CryptographicPermutation P (Std.Array F W))
    (ringInst : p3_field.field.PrimeCharacteristicRing F)
    (c : DuplexChallenger F P W R) : RustM (F × DuplexChallenger F P W R) := do
  let b ← alloc.vec.Vec.is_empty c.input_buffer
  let c1 ←
    if !b then DuplexChallenger.duplexing copyInst permInst ringInst c
    else do
      let b1 ← alloc.vec.Vec.is_empty c.output_buffer
      if b1 then DuplexChallenger.duplexing copyInst permInst ringInst c else ok c
  let (o, v) ← alloc.vec.Vec.pop c1.output_buffer
  let t ← core.option.Option.expect o (toStr "Output buffer should be non-empty")
  ok (t, { c1 with output_buffer := v })

/-- `<DuplexChallenger as CanSampleBits<usize>>::sample_bits` (`duplex_challenger.rs:282`).

Assert `bits < usize::BITS` and `2^bits < p`, sample, and keep the low `bits` bits of the canonical value. -/
def sample_bits (copyInst : core.marker.Copy F)
    (permInst : p3_symmetric.permutation.CryptographicPermutation P (Std.Array F W))
    (ringInst : p3_field.field.PrimeCharacteristicRing F)
    (pf64 : p3_field.field.PrimeField64 F)
    (c : DuplexChallenger F P W R) (bits : Std.Usize) : RustM (Std.Usize × DuplexChallenger F P W R) := do
  let i ← lift (UScalar.cast .Usize core.num.Usize.BITS)
  massert (bits < i)
  let i1 ← 1#u64 <<< bits
  let i2 ← pf64.ORDER_U64
  massert (i1 < i2)
  let (rand_f, c1) ← sample copyInst permInst ringInst c
  let i3 ← pf64.as_canonical_u64 rand_f
  let rand_usize ← lift (UScalar.cast .Usize i3)
  let i4 ← 1#usize <<< bits
  let i5 ← i4 - 1#usize
  let i6 ← lift (rand_usize &&& i5)
  ok (i6, c1)

end p3_challenger.duplex_challenger.mirror
