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

end p3_dft.butterflies.mirror
