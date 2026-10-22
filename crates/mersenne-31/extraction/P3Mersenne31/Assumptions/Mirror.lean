/-
# `p3-mersenne-31`: what the scoped extraction does not produce

The items below reach p3-field's generic `Complex<F>` or `core::iter`, which aeneas rejects (docs/extractor-issues.md, 9 and 11).

Each is transcribed operation by operation, with aeneas's integer widths and checked semantics.

The arithmetic they call (`new`, `new_reduced`, `Add`, `Sub`, `from_u62`) is extracted.

* `Sum::sum`, over the list of items the iterator yields, and `sum_array`.
* The `Complex<Mersenne31>` constants of `complex.rs` and `extension.rs`, and `mul_by_w`.

`Complex<F>` is `BinomialExtensionField<F, 2>`, a `repr(transparent)` wrapper of `value: [F; 2]`.

It is modelled by that array, `[real, imag]`.
-/
module

public import P3Mersenne31.Extraction

@[expose] public section
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM ControlFlow Error

namespace p3_mersenne_31

/-! ## Accumulation (`mersenne-31/src/mersenne_31.rs`) -/

/-- `<Mersenne31 as Sum>::sum`. Upstream line 637.

```
let sum = iter.map(|x| x.value as u64).sum::<u64>();
from_u62(sum)
```

`u64::sum` folds with `+`, which is checked in a debug build. -/
def mersenne_31.Mersenne31.Insts.CoreIterTraitsAccumSumMersenne31.sum
    (iter : List mersenne_31.Mersenne31) : RustM mersenne_31.Mersenne31 := do
  let sum ← iter.foldlM (fun acc x => acc + UScalar.cast .U64 x.value) 0#u64
  mersenne_31.from_u62 sum

/-- `<Mersenne31 as PrimeCharacteristicRing>::sum_array::<N>`. Upstream line 281.

```
assert_eq!(N, input.len());
match N {
    0 => Self::ZERO,
    1 => input[0],
    2 => input[0] + input[1],
    3 => input[0] + input[1] + input[2],
    4 => (input[0] + input[1]) + (input[2] + input[3]),
    5 => { let lhs = input[0] + input[1]; let rhs = input[2] + input[3]; lhs + rhs + input[4] }
    _ => input.iter().copied().sum(),
}
``` -/
def mersenne_31.Mersenne31.Insts.P3_fieldFieldPrimeCharacteristicRing.sum_array
    (N : Std.Usize) (input : Slice mersenne_31.Mersenne31) : RustM mersenne_31.Mersenne31 := do
  let add := mersenne_31.Mersenne31.Insts.CoreOpsArithAddMersenne31Mersenne31.add
  massert (N = input.length)
  if N = 0#usize then ok mersenne_31.Mersenne31.Insts.P3_fieldFieldPrimeCharacteristicRing.ZERO
  else if N = 1#usize then Slice.index_usize input 0#usize
  else if N = 2#usize then do
    let a ← Slice.index_usize input 0#usize
    let b ← Slice.index_usize input 1#usize
    add a b
  else if N = 3#usize then do
    let a ← Slice.index_usize input 0#usize
    let b ← Slice.index_usize input 1#usize
    let ab ← add a b
    let c ← Slice.index_usize input 2#usize
    add ab c
  else if N = 4#usize then do
    let a ← Slice.index_usize input 0#usize
    let b ← Slice.index_usize input 1#usize
    let ab ← add a b
    let c ← Slice.index_usize input 2#usize
    let d ← Slice.index_usize input 3#usize
    let cd ← add c d
    add ab cd
  else if N = 5#usize then do
    let a ← Slice.index_usize input 0#usize
    let b ← Slice.index_usize input 1#usize
    let lhs ← add a b
    let c ← Slice.index_usize input 2#usize
    let d ← Slice.index_usize input 3#usize
    let rhs ← add c d
    let s ← add lhs rhs
    let e ← Slice.index_usize input 4#usize
    add s e
  else mersenne_31.Mersenne31.Insts.CoreIterTraitsAccumSumMersenne31.sum input.val

/-! ## The complex extension (`mersenne-31/src/complex.rs`) -/

/-- `Complex::new_complex(Self::new(re), Self::new(im))`, the form of every table entry. -/
def complex.new_complex_new (re im : Std.U32) : RustM (Array mersenne_31.Mersenne31 2#usize) := do
  let a ← mersenne_31.Mersenne31.new re
  let b ← mersenne_31.Mersenne31.new im
  ok (Array.make 2#usize [a, b])

/-- `Mersenne31::CIRCLE_TWO_ADIC_GENERATORS`. Upstream line 16: 32 entries `Complex::new_complex(Self::new(re), Self::new(im))`.

The `else` branch is unreachable, since `mapM` keeps the length. -/
def complex.Mersenne31.CIRCLE_TWO_ADIC_GENERATORS :
    RustM (Array (Array mersenne_31.Mersenne31 2#usize) 32#usize) :=
  [(1#u32, 0#u32), (2147483646#u32, 0#u32), (0#u32, 2147483646#u32),
    (32768#u32, 2147450879#u32), (590768354#u32, 978592373#u32),
    (1179735656#u32, 1241207368#u32), (1567857810#u32, 456695729#u32),
    (1774253895#u32, 1309288441#u32), (736262640#u32, 1553669210#u32),
    (1819216575#u32, 1662816114#u32), (1323191254#u32, 1936974060#u32),
    (605622498#u32, 1964232216#u32), (343674985#u32, 501786993#u32),
    (1995316534#u32, 149306621#u32), (2107600913#u32, 1378821388#u32),
    (541476169#u32, 2101081972#u32), (2135874973#u32, 483411332#u32),
    (2097144245#u32, 1684033590#u32), (1662322247#u32, 670236780#u32),
    (1172215635#u32, 595888646#u32), (241940101#u32, 323856519#u32),
    (1957194259#u32, 2139647100#u32), (1957419629#u32, 1541039442#u32),
    (1062045235#u32, 1824580421#u32), (1929382196#u32, 1664698822#u32),
    (1889294251#u32, 331248939#u32), (1214231414#u32, 1646302518#u32),
    (1765392370#u32, 461136547#u32), (1629751483#u32, 66485474#u32),
    (1501355827#u32, 1439063420#u32), (509778402#u32, 800467507#u32),
    (311014874#u32, 1584694829#u32)].mapM (fun c => complex.new_complex_new c.1 c.2) >>=
    fun l => if h : l.length = 32 then ok (Array.from l h) else fail .panic

/-- `<Mersenne31 as ComplexExtendable>::COMPLEX_GENERATOR`. Upstream line 61: `Complex::new_complex(Self::new(12), Self::ONE)`. -/
def complex.Mersenne31.COMPLEX_GENERATOR : RustM (Array mersenne_31.Mersenne31 2#usize) := do
  let a ← mersenne_31.Mersenne31.new 12#u32
  ok (Array.make 2#usize [a, mersenne_31.Mersenne31.Insts.P3_fieldFieldPrimeCharacteristicRing.ONE])

/-- `<Mersenne31 as ComplexExtendable>::circle_two_adic_generator`. Upstream line 63.

```
assert!(bits <= Self::CIRCLE_TWO_ADICITY);
Self::CIRCLE_TWO_ADIC_GENERATORS[bits]
```

`CIRCLE_TWO_ADICITY` is `31`. -/
def complex.Mersenne31.circle_two_adic_generator (bits : Std.Usize) :
    RustM (Array mersenne_31.Mersenne31 2#usize) := do
  massert (bits <= 31#usize)
  let a ← complex.Mersenne31.CIRCLE_TWO_ADIC_GENERATORS
  Array.index_usize a bits

/-! ## Binomial extensions of `Complex<Mersenne31>` (`mersenne-31/src/extension.rs`) -/

/-- `<Mersenne31 as HasComplexBinomialExtension<2>>::W`. Upstream line 72: `Complex::new_complex(Self::TWO, Self::ONE)`. -/
def extension.Mersenne31.QUADRATIC_W : Array mersenne_31.Mersenne31 2#usize :=
  Array.make 2#usize [mersenne_31.Mersenne31.Insts.P3_fieldFieldPrimeCharacteristicRing.TWO,
    mersenne_31.Mersenne31.Insts.P3_fieldFieldPrimeCharacteristicRing.ONE]

/-- `<Mersenne31 as HasComplexBinomialExtension<2>>::DTH_ROOT`. Upstream line 75: `Complex::new_real(Self::new(2147483646))`. -/
def extension.Mersenne31.QUADRATIC_DTH_ROOT : RustM (Array mersenne_31.Mersenne31 2#usize) := do
  let a ← mersenne_31.Mersenne31.new 2147483646#u32
  ok (Array.make 2#usize [a, mersenne_31.Mersenne31.Insts.P3_fieldFieldPrimeCharacteristicRing.ZERO])

/-- `<Mersenne31 as HasComplexBinomialExtension<2>>::mul_by_w`. Upstream line 89.

```
let re = z.real();
let im = z.imag();
Complex::new_complex(re + re - im, re + im + im)
``` -/
def extension.Mersenne31.mul_by_w (z : Array mersenne_31.Mersenne31 2#usize) :
    RustM (Array mersenne_31.Mersenne31 2#usize) := do
  let re ← Array.index_usize z 0#usize
  let im ← Array.index_usize z 1#usize
  let a ← mersenne_31.Mersenne31.Insts.CoreOpsArithAddMersenne31Mersenne31.add re re
  let a1 ← mersenne_31.Mersenne31.Insts.CoreOpsArithSubMersenne31Mersenne31.sub a im
  let b ← mersenne_31.Mersenne31.Insts.CoreOpsArithAddMersenne31Mersenne31.add re im
  let b1 ← mersenne_31.Mersenne31.Insts.CoreOpsArithAddMersenne31Mersenne31.add b im
  ok (Array.make 2#usize [a1, b1])

/-- The `bits == 33` entry of `<Mersenne31 as HasTwoAdicComplexBinomialExtension<2>>::complex_ext_two_adic_generator`. Upstream line 102.

```
[Complex::ZERO, Complex::new_complex(Self::new_reduced(1437746044), Self::new_reduced(946469285))]
``` -/
def extension.Mersenne31.QUADRATIC_EXT_TWO_ADIC_GENERATOR_33 :
    RustM (Array (Array mersenne_31.Mersenne31 2#usize) 2#usize) := do
  let a ← mersenne_31.Mersenne31.new_reduced 1437746044#u32
  let b ← mersenne_31.Mersenne31.new_reduced 946469285#u32
  let zero := mersenne_31.Mersenne31.Insts.P3_fieldFieldPrimeCharacteristicRing.ZERO
  ok (Array.make 2#usize [Array.make 2#usize [zero, zero], Array.make 2#usize [a, b]])

/-- `<Mersenne31 as HasComplexBinomialExtension<3>>::W`. Upstream line 134: `Complex::new_imag(Self::new(5))`. -/
def extension.Mersenne31.CUBIC_W : RustM (Array mersenne_31.Mersenne31 2#usize) := do
  let a ← mersenne_31.Mersenne31.new 5#u32
  ok (Array.make 2#usize [mersenne_31.Mersenne31.Insts.P3_fieldFieldPrimeCharacteristicRing.ZERO, a])

/-- `<Mersenne31 as HasComplexBinomialExtension<3>>::DTH_ROOT`. Upstream line 137: `Complex::new_real(Self::new(634005911))`. -/
def extension.Mersenne31.CUBIC_DTH_ROOT : RustM (Array mersenne_31.Mersenne31 2#usize) := do
  let a ← mersenne_31.Mersenne31.new 634005911#u32
  ok (Array.make 2#usize [a, mersenne_31.Mersenne31.Insts.P3_fieldFieldPrimeCharacteristicRing.ZERO])

end p3_mersenne_31
