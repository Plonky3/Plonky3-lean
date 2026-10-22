/-
# `p3-goldilocks`: what the scoped extraction does not produce

The items below are translated by charon but not emitted by aeneas (docs/extractor-issues.md, 4).

Each is transcribed operation by operation, with aeneas's integer widths and checked or wrapping semantics.

The names are those aeneas would generate, so a future emission collides with its transcription.

* `Sub::sub` and `PartialEq::eq`.
* The overrides `halve`, `div_2exp_u64`, `sum_array` and `dot_product`.
* `Sum::sum`, over the list of items the iterator yields.
* The `QuotientMap` conversions from `u64`, `u128`, `i64` and `i128`.

`halve` and `dot_product` read their local constants from the extraction.

`unchecked_add` and `unchecked_sub` are undefined behaviour on overflow.

They are transcribed as checked operators, so a proof of no failure proves no overflow.
-/
import P3Goldilocks.Extraction
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM ControlFlow Error

namespace p3_goldilocks

/-! ## Operators (`goldilocks/src/goldilocks.rs`) -/

/-- `<Goldilocks as Sub>::sub`. Upstream line 723.

```
let (diff, under) = self.value.overflowing_sub(rhs.value);
let (mut diff, under) = diff.overflowing_sub(u64::from(under) * Self::NEG_ORDER);
if under {
    unsafe { assert_unchecked(self.value < Self::NEG_ORDER - 1 && rhs.value > Self::ORDER_U64); }
    branch_hint();
    diff -= Self::NEG_ORDER;
}
Self::new(diff)
``` -/
def goldilocks.Goldilocks.Insts.CoreOpsArithSubGoldilocksGoldilocks.sub
    (self rhs : goldilocks.Goldilocks) : RustM goldilocks.Goldilocks := do
  let (diff, under) ← core.num.U64.overflowing_sub self.value rhs.value
  let i ← core.U64.Insts.CoreConvertFromBool.from under
  let i1 ← goldilocks.Goldilocks.NEG_ORDER
  let i2 ← i * i1
  let (diff1, under1) ← core.num.U64.overflowing_sub diff i2
  let diff2 ←
    if under1 then do
      let i3 ← i1 - 1#u64
      let b ←
        if self.value < i3 then
          ok (rhs.value > goldilocks.Goldilocks.Insts.P3_fieldFieldPrimeField64.ORDER_U64)
        else ok false
      core.hint.assert_unchecked b
      p3_util.branch_hint
      diff1 - i1
    else ok diff1
  goldilocks.Goldilocks.new diff2

/-- `<Goldilocks as PartialEq>::eq`. Upstream line 200:
`self.as_canonical_u64() == other.as_canonical_u64()`. -/
def goldilocks.Goldilocks.Insts.CoreCmpPartialEqGoldilocks.eq
    (self other : goldilocks.Goldilocks) : RustM Bool := do
  let i ← goldilocks.Goldilocks.Insts.P3_fieldFieldPrimeField64.as_canonical_u64 self
  let i1 ← goldilocks.Goldilocks.Insts.P3_fieldFieldPrimeField64.as_canonical_u64 other
  ok (i = i1)

/-! ## `PrimeCharacteristicRing` overrides -/

/-- `<Goldilocks as PrimeCharacteristicRing>::halve`. Upstream line 290.

```
let lo_bit = self.value & 1;
let half = self.value >> 1;
let mask = 0u64.wrapping_sub(lo_bit);
Self::new(half.wrapping_add(mask & HALF_P_PLUS_1))
``` -/
def goldilocks.Goldilocks.Insts.P3_fieldFieldPrimeCharacteristicRing.halve
    (self : goldilocks.Goldilocks) : RustM goldilocks.Goldilocks := do
  let lo_bit ← lift (self.value &&& 1#u64)
  let half ← self.value >>> 1#i32
  let mask ← core.num.U64.wrapping_sub 0#u64 lo_bit
  let i ← goldilocks.PrimeCharacteristicRingGoldilocks.halve.HALF_P_PLUS_1
  let i1 ← lift (mask &&& i)
  let i2 ← core.num.U64.wrapping_add half i1
  goldilocks.Goldilocks.new i2

/-- `<Goldilocks as PrimeCharacteristicRing>::div_2exp_u64`. Upstream line 326.

```
exp %= 192;
match exp {
    0 => *self,
    1 => self.halve(),
    2..=32 => {
        let lo = self.value & ((1u64 << exp) - 1);
        let hi = self.value >> exp;
        let a = hi + (lo << (32 - exp));
        let b = lo << (64 - exp);
        let (result, borrow) = a.overflowing_sub(b);
        Self::new(result.wrapping_sub(Self::NEG_ORDER * u64::from(borrow)))
    }
    _ => self.mul_2exp_u64(192 - exp),
}
``` -/
def goldilocks.Goldilocks.Insts.P3_fieldFieldPrimeCharacteristicRing.div_2exp_u64
    (self : goldilocks.Goldilocks) (exp : Std.U64) : RustM goldilocks.Goldilocks := do
  let exp1 ← exp % 192#u64
  match exp1 with
  | 0#uscalar => ok self
  | 1#uscalar => goldilocks.Goldilocks.Insts.P3_fieldFieldPrimeCharacteristicRing.halve self
  | _ =>
    if 2#u64 <= exp1 ∧ exp1 <= 32#u64 then do
      let i ← 1#u64 <<< exp1
      let i1 ← i - 1#u64
      let lo ← lift (self.value &&& i1)
      let hi ← self.value >>> exp1
      let i2 ← 32#u64 - exp1
      let i3 ← lo <<< i2
      let a ← hi + i3
      let i4 ← 64#u64 - exp1
      let b ← lo <<< i4
      let (result, borrow) ← core.num.U64.overflowing_sub a b
      let i5 ← goldilocks.Goldilocks.NEG_ORDER
      let i6 ← core.U64.Insts.CoreConvertFromBool.from borrow
      let i7 ← i5 * i6
      let i8 ← core.num.U64.wrapping_sub result i7
      goldilocks.Goldilocks.new i8
    else do
      let i ← 192#u64 - exp1
      goldilocks.Goldilocks.Insts.P3_fieldFieldPrimeCharacteristicRing.mul_2exp_u64 self i

/-- `<Goldilocks as Sum>::sum`. Upstream line 814.

```
let sum = iter.map(|x| x.value as u128).sum::<u128>();
reduce128(sum)
```

The iterator is the list of the items it yields, in order.
`Sum for u128` folds from `0` with `+`, which overflow-checks as the build does. -/
def goldilocks.Goldilocks.Insts.CoreIterTraitsAccumSumGoldilocks.sum
    (iter : List goldilocks.Goldilocks) : RustM goldilocks.Goldilocks := do
  let sum ← iter.foldlM (fun acc x => acc + UScalar.cast .U128 x.value) 0#u128
  goldilocks.reduce128 sum

/-- `<Goldilocks as PrimeCharacteristicRing>::sum_array::<N>`. Upstream line 350.

```
assert_eq!(N, input.len());
match N {
    0 => Self::ZERO,
    1 => input[0],
    2 => input[0] + input[1],
    3 => input[0] + input[1] + input[2],
    _ => input.iter().copied().sum(),
}
``` -/
def goldilocks.Goldilocks.Insts.P3_fieldFieldPrimeCharacteristicRing.sum_array
    (N : Std.Usize) (input : Slice goldilocks.Goldilocks) : RustM goldilocks.Goldilocks := do
  massert (N = input.length)
  if N = 0#usize then goldilocks.Goldilocks.Insts.P3_fieldFieldPrimeCharacteristicRing.ZERO
  else if N = 1#usize then Slice.index_usize input 0#usize
  else if N = 2#usize then do
    let x0 ← Slice.index_usize input 0#usize
    let x1 ← Slice.index_usize input 1#usize
    goldilocks.Goldilocks.Insts.CoreOpsArithAddGoldilocksGoldilocks.add x0 x1
  else if N = 3#usize then do
    let x0 ← Slice.index_usize input 0#usize
    let x1 ← Slice.index_usize input 1#usize
    let s ← goldilocks.Goldilocks.Insts.CoreOpsArithAddGoldilocksGoldilocks.add x0 x1
    let x2 ← Slice.index_usize input 2#usize
    goldilocks.Goldilocks.Insts.CoreOpsArithAddGoldilocksGoldilocks.add s x2
  else goldilocks.Goldilocks.Insts.CoreIterTraitsAccumSumGoldilocks.sum input.val

/-- One step of the fold in `dot_product`, upstream line 398.

```
|(acc_lo, acc_hi), val| {
    let val_hi = (val >> 96) as u64;
    unsafe { (acc_lo.wrapping_add(val), acc_hi.unchecked_add(val_hi)) }
}
```

`val` is `mul_wide(x.value, y.value)`, from the preceding `map`. -/
def goldilocks.PrimeCharacteristicRingGoldilocks.dot_product.fold_step
    (acc : Std.U128 × Std.U64) (xy : goldilocks.Goldilocks × goldilocks.Goldilocks) :
    RustM (Std.U128 × Std.U64) := do
  let (acc_lo, acc_hi) := acc
  let val ← goldilocks.mul_wide xy.1.value xy.2.value
  let i ← val >>> 96#i32
  let val_hi ← lift (UScalar.cast .U64 i)
  let lo ← core.num.U128.wrapping_add acc_lo val
  let hi ← acc_hi + val_hi
  ok (lo, hi)

/-- `<Goldilocks as PrimeCharacteristicRing>::dot_product::<N>`. Upstream line 365.

```
const { assert!((N as u32) <= (1 << 31)); }
match N {
    0 => Self::ZERO,
    1 => lhs[0] * rhs[0],
    2 => {
        let long_prod_0 = mul_wide(lhs[0].value, rhs[0].value);
        let long_prod_1 = mul_wide(lhs[1].value, rhs[1].value);
        let (sum, over) = long_prod_0.overflowing_add(long_prod_1);
        let sum_corr = sum.wrapping_sub(OFFSET);
        if over { reduce128(sum_corr) } else { reduce128(sum) }
    }
    _ => {
        let (lo_plus_hi, hi) = lhs.iter().zip(rhs)
            .map(|(x, y)| mul_wide(x.value, y.value))
            .fold((0_u128, 0_u64), |(acc_lo, acc_hi), val| { .. });
        let lo = lo_plus_hi.wrapping_sub((hi as u128) << 96);
        let sum = unsafe { lo.unchecked_add(P.unchecked_sub(hi) as u128) };
        reduce128(sum)
    }
}
```

The `const` block is a runtime `massert`, as aeneas renders one, with `N as u32` a truncating cast.
The `zip` of two arrays of length `N` is the list of their `N` pairs. -/
def goldilocks.Goldilocks.Insts.P3_fieldFieldPrimeCharacteristicRing.dot_product
    {N : Std.Usize} (lhs rhs : Array goldilocks.Goldilocks N) :
    RustM goldilocks.Goldilocks := do
  let i ← lift (UScalar.cast .U32 N)
  let i1 ← 1#u32 <<< 31#i32
  massert (i <= i1)
  if N = 0#usize then goldilocks.Goldilocks.Insts.P3_fieldFieldPrimeCharacteristicRing.ZERO
  else if N = 1#usize then do
    let x ← Array.index_usize lhs 0#usize
    let y ← Array.index_usize rhs 0#usize
    goldilocks.Goldilocks.Insts.CoreOpsArithMulGoldilocksGoldilocks.mul x y
  else if N = 2#usize then do
    let x0 ← Array.index_usize lhs 0#usize
    let y0 ← Array.index_usize rhs 0#usize
    let long_prod_0 ← goldilocks.mul_wide x0.value y0.value
    let x1 ← Array.index_usize lhs 1#usize
    let y1 ← Array.index_usize rhs 1#usize
    let long_prod_1 ← goldilocks.mul_wide x1.value y1.value
    let (sum, over) ← core.num.U128.overflowing_add long_prod_0 long_prod_1
    let offset ← goldilocks.PrimeCharacteristicRingGoldilocks.dot_product.OFFSET
    let sum_corr ← core.num.U128.wrapping_sub sum offset
    if over then goldilocks.reduce128 sum_corr else goldilocks.reduce128 sum
  else do
    let (lo_plus_hi, hi) ←
      (List.zip lhs.val rhs.val).foldlM
        goldilocks.PrimeCharacteristicRingGoldilocks.dot_product.fold_step (0#u128, 0#u64)
    let i2 ← (UScalar.cast .U128 hi) <<< 96#i32
    let lo ← core.num.U128.wrapping_sub lo_plus_hi i2
    let i3 ← goldilocks.P - hi
    let sum ← lo + UScalar.cast .U128 i3
    goldilocks.reduce128 sum

/-! ## `QuotientMap` conversions -/

/-- `<Goldilocks as QuotientMap<u64>>::from_int`. Upstream line 590: `Self::new(int)`. -/
def goldilocks.Goldilocks.Insts.P3_fieldIntegersQuotientMapU64.from_int
    (int : Std.U64) : RustM goldilocks.Goldilocks :=
  goldilocks.Goldilocks.new int

/-- `<Goldilocks as QuotientMap<u64>>::from_canonical_checked`. Upstream line 598:
`(int < Self::ORDER_U64).then(|| Self::new(int))`. -/
def goldilocks.Goldilocks.Insts.P3_fieldIntegersQuotientMapU64.from_canonical_checked
    (int : Std.U64) : RustM (core.option.Option goldilocks.Goldilocks) := do
  if int < goldilocks.Goldilocks.Insts.P3_fieldFieldPrimeField64.ORDER_U64 then do
    let g ← goldilocks.Goldilocks.new int
    ok (core.option.Option.Some g)
  else ok core.option.Option.None

/-- `<Goldilocks as QuotientMap<u128>>::from_int`. Upstream line 562:
`Self::new(reduce128(int).as_canonical_u64())`. -/
def goldilocks.Goldilocks.Insts.P3_fieldIntegersQuotientMapU128.from_int
    (int : Std.U128) : RustM goldilocks.Goldilocks := do
  let g ← goldilocks.reduce128 int
  let i ← goldilocks.Goldilocks.Insts.P3_fieldFieldPrimeField64.as_canonical_u64 g
  goldilocks.Goldilocks.new i

/-- `<Goldilocks as QuotientMap<u128>>::from_canonical_checked`. Upstream line 570:
`(int < Self::ORDER_U64 as u128).then(|| Self::new(int as u64))`. -/
def goldilocks.Goldilocks.Insts.P3_fieldIntegersQuotientMapU128.from_canonical_checked
    (int : Std.U128) : RustM (core.option.Option goldilocks.Goldilocks) := do
  let i ← lift (UScalar.cast .U128 goldilocks.Goldilocks.Insts.P3_fieldFieldPrimeField64.ORDER_U64)
  if int < i then do
    let g ← goldilocks.Goldilocks.new (UScalar.cast .U64 int)
    ok (core.option.Option.Some g)
  else ok core.option.Option.None

/-- `<Goldilocks as QuotientMap<u128>>::from_canonical_unchecked`. Upstream line 579:
`Self::new(int as u64)`. -/
def goldilocks.Goldilocks.Insts.P3_fieldIntegersQuotientMapU128.from_canonical_unchecked
    (int : Std.U128) : RustM goldilocks.Goldilocks :=
  goldilocks.Goldilocks.new (UScalar.cast .U64 int)

/-- `<Goldilocks as QuotientMap<i64>>::from_int`. Upstream line 618.

```
if int >= 0 { Self::new(int as u64) }
else { Self::new(Self::ORDER_U64.wrapping_add_signed(int)) }
``` -/
def goldilocks.Goldilocks.Insts.P3_fieldIntegersQuotientMapI64.from_int
    (int : Std.I64) : RustM goldilocks.Goldilocks := do
  if int >= 0#i64 then do
    let i ← lift (IScalar.hcast .U64 int)
    goldilocks.Goldilocks.new i
  else do
    let i ← core.num.U64.wrapping_add_signed
      goldilocks.Goldilocks.Insts.P3_fieldFieldPrimeField64.ORDER_U64 int
    goldilocks.Goldilocks.new i

/-- `<Goldilocks as QuotientMap<i64>>::from_canonical_checked`. Upstream line 630.

```
const POS_BOUND: i64 = (P >> 1) as i64;
const NEG_BOUND: i64 = -POS_BOUND;
match int {
    0..=POS_BOUND => Some(Self::new(int as u64)),
    NEG_BOUND..0 => Some(Self::new(Self::ORDER_U64.wrapping_add_signed(int))),
    _ => None,
}
```

`POS_BOUND = 2^63 - 2^31`, which aeneas inlines as a literal. -/
def goldilocks.Goldilocks.Insts.P3_fieldIntegersQuotientMapI64.from_canonical_checked
    (int : Std.I64) : RustM (core.option.Option goldilocks.Goldilocks) := do
  if 0#i64 <= int ∧ int <= 9223372034707292160#i64 then do
    let i ← lift (IScalar.hcast .U64 int)
    let g ← goldilocks.Goldilocks.new i
    ok (core.option.Option.Some g)
  else if (-9223372034707292160)#i64 <= int ∧ int < 0#i64 then do
    let i ← core.num.U64.wrapping_add_signed
      goldilocks.Goldilocks.Insts.P3_fieldFieldPrimeField64.ORDER_U64 int
    let g ← goldilocks.Goldilocks.new i
    ok (core.option.Option.Some g)
  else ok core.option.Option.None

/-- `<Goldilocks as QuotientMap<i64>>::from_canonical_unchecked`. Upstream line 646:
`Self::from_int(int)`. -/
def goldilocks.Goldilocks.Insts.P3_fieldIntegersQuotientMapI64.from_canonical_unchecked
    (int : Std.I64) : RustM goldilocks.Goldilocks :=
  goldilocks.Goldilocks.Insts.P3_fieldIntegersQuotientMapI64.from_int int

/-- `<Goldilocks as QuotientMap<i128>>::from_int`, from `quotient_map_large_iint!`
(`field/src/integers.rs:377`).

```
if int >= 0 { Self::from_int(int as u128) }
else { -Self::from_int(int.unsigned_abs()) }
``` -/
def goldilocks.Goldilocks.Insts.P3_fieldIntegersQuotientMapI128.from_int
    (int : Std.I128) : RustM goldilocks.Goldilocks := do
  if int >= 0#i128 then do
    let i ← lift (IScalar.hcast .U128 int)
    goldilocks.Goldilocks.Insts.P3_fieldIntegersQuotientMapU128.from_int i
  else do
    let i ← core.num.I128.unsigned_abs int
    let g ← goldilocks.Goldilocks.Insts.P3_fieldIntegersQuotientMapU128.from_int i
    goldilocks.Goldilocks.Insts.CoreOpsArithNegGoldilocks.neg g

/-- `<Goldilocks as QuotientMap<i128>>::from_canonical_checked`, from
`quotient_map_large_iint!` (`field/src/integers.rs:389`).

```
let int_small = TryInto::<i64>::try_into(int).ok();
int_small.map(Self::from_canonical_checked)?
``` -/
def goldilocks.Goldilocks.Insts.P3_fieldIntegersQuotientMapI128.from_canonical_checked
    (int : Std.I128) : RustM (core.option.Option goldilocks.Goldilocks) := do
  let r ← core.I64.Insts.CoreConvertTryFromI128TryFromIntError.try_from int
  match r with
  | core.result.Result.Ok int_small =>
    goldilocks.Goldilocks.Insts.P3_fieldIntegersQuotientMapI64.from_canonical_checked int_small
  | core.result.Result.Err _ => ok core.option.Option.None

/-- `<Goldilocks as QuotientMap<i128>>::from_canonical_unchecked`, from
`quotient_map_large_iint!` (`field/src/integers.rs:401`):
`Self::from_canonical_unchecked(int as i64)`. -/
def goldilocks.Goldilocks.Insts.P3_fieldIntegersQuotientMapI128.from_canonical_unchecked
    (int : Std.I128) : RustM goldilocks.Goldilocks := do
  let i ← lift (IScalar.cast .I64 int)
  goldilocks.Goldilocks.Insts.P3_fieldIntegersQuotientMapI64.from_canonical_unchecked i

end p3_goldilocks
