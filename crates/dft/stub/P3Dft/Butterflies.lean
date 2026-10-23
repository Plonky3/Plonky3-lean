/-
Transcriptions of the butterflies of p3-dft.

What a transcription abstracts:

* a packed value is a row, a vector in V, and its arithmetic is elementwise;
* multiplying a row by a field element is the scalar action.
-/
module

public import P3Dft.Model

@[expose] public section

namespace p3_dft.butterflies.mirror

/-- The butterfly without a twiddle: the sum and the difference. -/
def TwiddleFreeButterfly.apply {V : Type _} [AddCommGroup V] (x_1 x_2 : V) : V × V :=
  (x_1 + x_2, x_1 - x_2)

variable {K : Type _} [Field K] {V : Type _} [AddCommGroup V] [Module K V]

/-- The decimation-in-time butterfly: it multiplies the second input by the twiddle, then adds and subtracts. -/
def DitButterfly.apply (t : K) (x_1 x_2 : V) : V × V :=
  let x_2_twiddle := t • x_2
  (x_1 + x_2_twiddle, x_1 - x_2_twiddle)

/-- The decimation-in-frequency butterfly: it adds and subtracts, then multiplies the difference by the twiddle. -/
def DifButterfly.apply (t : K) (x_1 x_2 : V) : V × V :=
  (x_1 + x_2, t • (x_1 - x_2))

/-- The decimation-in-frequency butterfly for a zero second input, which ignores that input. -/
def DifButterflyZeros.apply (t : K) (x_1 _x_2 : V) : V × V :=
  (x_1, t • x_1)

/-- A scaled decimation-in-time butterfly: its twiddle, its scale, and their product. -/
structure ScaledDitButterfly (K : Type _) where
  twiddle : K
  scale : K
  twiddle_times_scale : K

/-- The constructor, which precomputes the product of the twiddle and the scale. -/
def ScaledDitButterfly.new (twiddle scale : K) : ScaledDitButterfly K :=
  { twiddle, scale, twiddle_times_scale := twiddle * scale }

/-- The scaled butterfly: it scales the first input, multiplies the second by the precomputed product, then adds and subtracts. -/
def ScaledDitButterfly.apply (b : ScaledDitButterfly K) (x_1 x_2 : V) : V × V :=
  let x_1_scale := b.scale • x_1
  let x_2_twiddle_scale := b.twiddle_times_scale • x_2
  (x_1_scale + x_2_twiddle_scale, x_1_scale - x_2_twiddle_scale)

/-! ## Rows of field elements

A row is a list of field elements.

On the extraction target a packed value is one field element, so a row has no unpacked suffix.

The unrolled loops take four elements of each row at a time, then the remaining ones.

The two rows are taken to have the same length, which the Rust asserts only in debug builds. -/

section rows

variable {F : Type _} [Field F]

/-- The row form of the decimation-in-time butterfly, unrolled by four. -/
def DitButterfly.apply_to_rows (t : F) : List F → List F → List F × List F
  | a1 :: b1 :: c1 :: d1 :: r1, a2 :: b2 :: c2 :: d2 :: r2 =>
    let a2t := a2 * t
    let b2t := b2 * t
    let c2t := c2 * t
    let d2t := d2 * t
    let rest := DitButterfly.apply_to_rows t r1 r2
    ((a1 + a2t) :: (b1 + b2t) :: (c1 + c2t) :: (d1 + d2t) :: rest.1,
      (a1 - a2t) :: (b1 - b2t) :: (c1 - c2t) :: (d1 - d2t) :: rest.2)
  | r1, r2 =>
    ((r1.zip r2).map fun p => p.1 + p.2 * t, (r1.zip r2).map fun p => p.1 - p.2 * t)

/-- The row form of the decimation-in-frequency butterfly, unrolled by four. -/
def DifButterfly.apply_to_rows (t : F) : List F → List F → List F × List F
  | a1 :: b1 :: c1 :: d1 :: r1, a2 :: b2 :: c2 :: d2 :: r2 =>
    let rest := DifButterfly.apply_to_rows t r1 r2
    ((a1 + a2) :: (b1 + b2) :: (c1 + c2) :: (d1 + d2) :: rest.1,
      (a1 - a2) * t :: (b1 - b2) * t :: (c1 - c2) * t :: (d1 - d2) * t :: rest.2)
  | r1, r2 =>
    ((r1.zip r2).map fun p => p.1 + p.2, (r1.zip r2).map fun p => (p.1 - p.2) * t)

/-- The row form of the scaled butterfly, unrolled by four. -/
def ScaledDitButterfly.apply_to_rows (b : ScaledDitButterfly F) : List F → List F → List F × List F
  | a1 :: b1 :: c1 :: d1 :: r1, a2 :: b2 :: c2 :: d2 :: r2 =>
    let a1s := a1 * b.scale
    let b1s := b1 * b.scale
    let c1s := c1 * b.scale
    let d1s := d1 * b.scale
    let a2t := a2 * b.twiddle_times_scale
    let b2t := b2 * b.twiddle_times_scale
    let c2t := c2 * b.twiddle_times_scale
    let d2t := d2 * b.twiddle_times_scale
    let rest := ScaledDitButterfly.apply_to_rows b r1 r2
    ((a1s + a2t) :: (b1s + b2t) :: (c1s + c2t) :: (d1s + d2t) :: rest.1,
      (a1s - a2t) :: (b1s - b2t) :: (c1s - c2t) :: (d1s - d2t) :: rest.2)
  | r1, r2 =>
    ((r1.zip r2).map fun p => p.1 * b.scale + p.2 * b.twiddle_times_scale,
      (r1.zip r2).map fun p => p.1 * b.scale - p.2 * b.twiddle_times_scale)

/-- The row form of the butterfly for a zero second row: the second row becomes the first times the twiddle. -/
def DifButterflyZeros.apply_to_rows (t : F) (r1 r2 : List F) : List F × List F :=
  (r1, (r1.zip r2).map fun p => p.1 * t)

end rows

end p3_dft.butterflies.mirror
