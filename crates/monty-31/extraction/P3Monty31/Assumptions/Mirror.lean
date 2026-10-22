/-
# `p3-monty-31`: what p3-baby-bear and p3-koala-bear use from it that aeneas does not supply

Most of p3-monty-31 comes from its scoped extraction, `P3Monty31/Extraction/`
(the `data_traits`, `mds`, `poseidon1`/`poseidon2` parameter traits,
`MontyField31` itself, `MontyField31::new`, `new_monty`, `new_array`,
`new_2d_array`, the `Add`/`Sub`/`Mul`/`Neg` impls, the `utils` reductions and
conversions, the `Clone` impl). This file holds what that extraction does not
produce:

* `PrimeCharacteristicRing::halve`, which wraps the extracted `utils::halve_u32`.
  charon does not translate it at all: it is a provided method of
  `PrimeCharacteristicRing` that MontyField31 overrides and nothing calls, which
  charon skips even as a root (docs/extractor-issues.md, 4). Its body is one line
  and is transcribed below.
* squaring, exponentiation, multiplication by powers of two, inversion and the
  integer conversions (`QuotientMap`), which reach p3-field's trait hierarchy
  (docs/extractor-issues.md, 9) or implement a generic trait charon cannot root.
* the `no_packing` Poseidon layer types and their constructor impls. On a
  target with no SIMD these are the layers baby-bear's Poseidon instances use.
  The constructor bodies are one struct literal each and are transcribed.
* memberless `Field` and `PrimeField` witnesses for `MontyField31`. Both
  traits are memberless in `P3Monty31.Assumptions.P3Field`, so the witnesses carry no
  content.
-/
module

public import P3Monty31.Extraction
public import P3Util
public import P3Poseidon1
public import P3Poseidon2

@[expose] public section
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM ControlFlow Error

namespace p3_monty_31

/-! ## Scalar arithmetic (`monty-31/src/monty_31.rs`) -/

/-- `<MontyField31<FP> as PrimeCharacteristicRing>::halve`. Upstream line 225:
`Self::new_monty(halve_u32::<FP>(self.value))`. -/
def monty_31.MontyField31.halve {FP : Type}
    (data_traitsFieldParametersInst : data_traits.FieldParameters FP)
    (self : monty_31.MontyField31 FP) : RustM (monty_31.MontyField31 FP) := do
  let v ← utils.halve_u32 data_traitsFieldParametersInst self.value
  monty_31.MontyField31.new_monty
    data_traitsFieldParametersInst.PackedMontyParametersInst.MontyParametersInst v

/-! ## Powers of two and inversion -/

/-- Squaring, the trait default at this field (`field/src/field.rs:160`).

```rust
self.dup() * self.dup()
```
-/
def monty_31.MontyField31.square {FP : Type}
    (data_traitsFieldParametersInst : data_traits.FieldParameters FP)
    (self : monty_31.MontyField31 FP) : RustM (monty_31.MontyField31 FP) :=
  monty_31.MontyField31.Insts.CoreOpsArithMulMontyField31MontyField31.mul
    data_traitsFieldParametersInst.PackedMontyParametersInst.MontyParametersInst self self

/-- One iteration of the exponentiation loop, at bit `j` of the exponent.

- Multiply the product by the current power when the bit is set.
- Then square the current power.
-/
def monty_31.MontyField31.exp_u64.step {FP : Type}
    (data_traitsFieldParametersInst : data_traits.FieldParameters FP) (power : Std.U64)
    (acc : monty_31.MontyField31 FP × monty_31.MontyField31 FP) (j : ℕ) :
    RustM (monty_31.MontyField31 FP × monty_31.MontyField31 FP) := do
  let product ←
    if power.val.testBit j then
      monty_31.MontyField31.Insts.CoreOpsArithMulMontyField31MontyField31.mul
        data_traitsFieldParametersInst.PackedMontyParametersInst.MontyParametersInst
        acc.2 acc.1
    else ok acc.2
  let current ← monty_31.MontyField31.square data_traitsFieldParametersInst acc.1
  ok (current, product)

/-- Exponentiation, the trait default at this field (`field/src/field.rs:219`).

It is square-and-multiply over the exponent's bits, least significant first.

```rust
for j in 0..bits_u64(power) {
    if (power >> j) & 1 != 0 { product *= current.dup(); }
    current = current.square();
}
```

The loop is a fold over `j < 64 - leading_zeros(power)`.

Its test `(power >> j) & 1 != 0` is bit `j` of `power`, and the shift cannot fail since `j < 64`. -/
def monty_31.MontyField31.exp_u64 {FP : Type}
    (data_traitsFieldParametersInst : data_traits.FieldParameters FP)
    (self : monty_31.MontyField31 FP) (power : Std.U64) : RustM (monty_31.MontyField31 FP) := do
  let product ← data_traitsFieldParametersInst.MONTY_ONE
  let lz ← core.num.U64.leading_zeros power
  let bits ← 64#u32 - lz
  let acc ← (List.range bits.val).foldlM
    (monty_31.MontyField31.exp_u64.step data_traitsFieldParametersInst power) (self, product)
  ok acc.2

/-- Multiplication by `2^exp` (`monty-31/src/monty_31.rs:230`).

- `exp = 0`: the element itself.
- `exp = 1`: the element added to itself.
- `exp < 64`: a product with the table entry for `2^exp`.
- Otherwise: a product with two raised to `exp`.
-/
def monty_31.MontyField31.mul_2exp_u64 {FP : Type}
    (data_traitsFieldParametersInst : data_traits.FieldParameters FP)
    (self : monty_31.MontyField31 FP) (exp : Std.U64) : RustM (monty_31.MontyField31 FP) := do
  let mp := data_traitsFieldParametersInst.PackedMontyParametersInst.MontyParametersInst
  if exp = 0#u64 then ok self
  else if exp = 1#u64 then monty_31.MontyField31.Insts.CoreOpsArithAddMontyField31MontyField31.add mp self self
  else if exp < 64#u64 then do
    let table ← monty_31.MontyField31.MONTY_POWERS_OF_TWO data_traitsFieldParametersInst
    let e ← Array.index_usize table (UScalar.cast .Usize exp)
    monty_31.MontyField31.Insts.CoreOpsArithMulMontyField31MontyField31.mul mp self e
  else do
    let two ← data_traitsFieldParametersInst.MONTY_TWO
    let e ← monty_31.MontyField31.exp_u64 data_traitsFieldParametersInst two exp
    monty_31.MontyField31.Insts.CoreOpsArithMulMontyField31MontyField31.mul mp self e

/-- Inversion (`monty-31/src/monty_31.rs:458`).

- Zero gives `None`, comparing stored values as the derived equality does.
- Otherwise the binary GCD gives `v`, with `v · a ≡ 2^60 (mod p)`.
- `2^30 · p + v` is reduced, then multiplied by `2^36`.

The `i64` addition is checked.

The cast to `u64` reinterprets the bits.
-/
def monty_31.MontyField31.try_inverse {FP : Type}
    (data_traitsFieldParametersInst : data_traits.FieldParameters FP)
    (self : monty_31.MontyField31 FP) : RustM (Option (monty_31.MontyField31 FP)) := do
  let mp := data_traitsFieldParametersInst.PackedMontyParametersInst.MontyParametersInst
  let zero ← data_traitsFieldParametersInst.MONTY_ZERO
  if self.value = zero.value then ok none
  else do
    let prime ← mp.PRIME
    let gcd_inverse ← p3_util.gcd_inversion_prime_field_32 31#u32 self.value prime
    let shifted ← (UScalar.hcast .I64 prime) <<< 30#i32
    let sum ← shifted + gcd_inverse
    let pos_inverse := IScalar.hcast .U64 sum
    let r ← utils.monty_reduce mp pos_inverse
    let uncorrected_value ← monty_31.MontyField31.new_monty mp r
    let bits ← mp.MONTY_BITS
    let three_bits ← 3#u32 * bits
    let exp ← three_bits - 60#u32
    let v ← monty_31.MontyField31.mul_2exp_u64 data_traitsFieldParametersInst uncorrected_value
      (UScalar.cast .U64 exp)
    ok (some v)

/-! ## Integers into the field (`monty-31/src/monty_31.rs:518`) -/

/-- Checked conversion from `u32`.

```rust
(int < FP::PRIME).then(|| Self::new(int))
```
-/
def monty_31.MontyField31.Insts.P3_fieldIntegersQuotientMapU32.from_canonical_checked
    {FP : Type} (data_traitsFieldParametersInst : data_traits.FieldParameters FP)
    (int : Std.U32) : RustM (Option (monty_31.MontyField31 FP)) := do
  let mp := data_traitsFieldParametersInst.PackedMontyParametersInst.MontyParametersInst
  let prime ← mp.PRIME
  if int < prime then do
    let v ← monty_31.MontyField31.new mp int
    ok (some v)
  else ok none

/-- Conversion from `i32`.

```rust
Self::new_monty(to_monty_signed::<FP>(int))
```
-/
def monty_31.MontyField31.Insts.P3_fieldIntegersQuotientMapI32.from_int
    {FP : Type} (data_traitsFieldParametersInst : data_traits.FieldParameters FP)
    (int : Std.I32) : RustM (monty_31.MontyField31 FP) := do
  let mp := data_traitsFieldParametersInst.PackedMontyParametersInst.MontyParametersInst
  let v ← utils.to_monty_signed mp int
  monty_31.MontyField31.new_monty mp v

/-- Checked conversion from `i32`.

The bound is `(PRIME >> 1) as i32`, that is `(p - 1)/2`.

Inside `[-bound, bound]` it converts, and outside it returns `None`.
-/
def monty_31.MontyField31.Insts.P3_fieldIntegersQuotientMapI32.from_canonical_checked
    {FP : Type} (data_traitsFieldParametersInst : data_traits.FieldParameters FP)
    (int : Std.I32) : RustM (Option (monty_31.MontyField31 FP)) := do
  let mp := data_traitsFieldParametersInst.PackedMontyParametersInst.MontyParametersInst
  let prime ← mp.PRIME
  let half ← prime >>> 1#i32
  let bound := UScalar.hcast .I32 half
  if int <= bound then do
    let neg_bound ← IScalar.neg bound
    if int >= neg_bound then do
      let v ← utils.to_monty_signed mp int
      let e ← monty_31.MontyField31.new_monty mp v
      ok (some e)
    else ok none
  else ok none

/-- Conversion from `u64`.

```rust
Self::new_monty(to_monty_64::<FP>(int))
```
-/
def monty_31.MontyField31.Insts.P3_fieldIntegersQuotientMapU64.from_int
    {FP : Type} (data_traitsFieldParametersInst : data_traits.FieldParameters FP)
    (int : Std.U64) : RustM (monty_31.MontyField31 FP) := do
  let mp := data_traitsFieldParametersInst.PackedMontyParametersInst.MontyParametersInst
  let v ← utils.to_monty_64 mp int
  monty_31.MontyField31.new_monty mp v

/-- Checked conversion from `u64`.

```rust
(int < FP::PRIME as u64).then(|| Self::new(int as u32))
```
-/
def monty_31.MontyField31.Insts.P3_fieldIntegersQuotientMapU64.from_canonical_checked
    {FP : Type} (data_traitsFieldParametersInst : data_traits.FieldParameters FP)
    (int : Std.U64) : RustM (Option (monty_31.MontyField31 FP)) := do
  let mp := data_traitsFieldParametersInst.PackedMontyParametersInst.MontyParametersInst
  let prime ← mp.PRIME
  if int < UScalar.cast .U64 prime then do
    let v ← monty_31.MontyField31.new mp (UScalar.cast .U32 int)
    ok (some v)
  else ok none

/-- Conversion from `i64`.

```rust
Self::new_monty(to_monty_64_signed::<FP>(int))
```
-/
def monty_31.MontyField31.Insts.P3_fieldIntegersQuotientMapI64.from_int
    {FP : Type} (data_traitsFieldParametersInst : data_traits.FieldParameters FP)
    (int : Std.I64) : RustM (monty_31.MontyField31 FP) := do
  let mp := data_traitsFieldParametersInst.PackedMontyParametersInst.MontyParametersInst
  let v ← utils.to_monty_64_signed mp int
  monty_31.MontyField31.new_monty mp v

/-- Checked conversion from `i64`.

The bound is `(PRIME >> 1) as i64`, that is `(p - 1)/2`.

Inside `[-bound, bound]` the input fits an `i32` and converts.

Outside it returns `None`.
-/
def monty_31.MontyField31.Insts.P3_fieldIntegersQuotientMapI64.from_canonical_checked
    {FP : Type} (data_traitsFieldParametersInst : data_traits.FieldParameters FP)
    (int : Std.I64) : RustM (Option (monty_31.MontyField31 FP)) := do
  let mp := data_traitsFieldParametersInst.PackedMontyParametersInst.MontyParametersInst
  let prime ← mp.PRIME
  let half ← prime >>> 1#i32
  let bound := UScalar.hcast .I64 half
  if int <= bound then do
    let neg_bound ← IScalar.neg bound
    if int >= neg_bound then do
      let v ← utils.to_monty_signed mp (IScalar.cast .I32 int)
      let e ← monty_31.MontyField31.new_monty mp v
      ok (some e)
    else ok none
  else ok none

/-- Conversion from `u128`.

```rust
Self::new_monty(to_monty::<FP>((int % (FP::PRIME as u128)) as u32))
```
-/
def monty_31.MontyField31.Insts.P3_fieldIntegersQuotientMapU128.from_int
    {FP : Type} (data_traitsFieldParametersInst : data_traits.FieldParameters FP)
    (int : Std.U128) : RustM (monty_31.MontyField31 FP) := do
  let mp := data_traitsFieldParametersInst.PackedMontyParametersInst.MontyParametersInst
  let prime ← mp.PRIME
  let r ← int % UScalar.cast .U128 prime
  let v ← utils.to_monty mp (UScalar.cast .U32 r)
  monty_31.MontyField31.new_monty mp v

/-- Checked conversion from `u128`.

```rust
(int < FP::PRIME as u128).then(|| Self::new(int as u32))
```
-/
def monty_31.MontyField31.Insts.P3_fieldIntegersQuotientMapU128.from_canonical_checked
    {FP : Type} (data_traitsFieldParametersInst : data_traits.FieldParameters FP)
    (int : Std.U128) : RustM (Option (monty_31.MontyField31 FP)) := do
  let mp := data_traitsFieldParametersInst.PackedMontyParametersInst.MontyParametersInst
  let prime ← mp.PRIME
  if int < UScalar.cast .U128 prime then do
    let v ← monty_31.MontyField31.new mp (UScalar.cast .U32 int)
    ok (some v)
  else ok none

/-- Conversion from `i128`.

```rust
Self::new_monty(to_monty_signed::<FP>((int % (FP::PRIME as i128)) as i32))
```
-/
def monty_31.MontyField31.Insts.P3_fieldIntegersQuotientMapI128.from_int
    {FP : Type} (data_traitsFieldParametersInst : data_traits.FieldParameters FP)
    (int : Std.I128) : RustM (monty_31.MontyField31 FP) := do
  let mp := data_traitsFieldParametersInst.PackedMontyParametersInst.MontyParametersInst
  let prime ← mp.PRIME
  let r ← int % UScalar.hcast .I128 prime
  let v ← utils.to_monty_signed mp (IScalar.cast .I32 r)
  monty_31.MontyField31.new_monty mp v

/-- Checked conversion from `i128`.

The bound is `(PRIME >> 1) as i128`, that is `(p - 1)/2`.

Inside `[-bound, bound]` the input fits an `i32` and converts.

Outside it returns `None`.
-/
def monty_31.MontyField31.Insts.P3_fieldIntegersQuotientMapI128.from_canonical_checked
    {FP : Type} (data_traitsFieldParametersInst : data_traits.FieldParameters FP)
    (int : Std.I128) : RustM (Option (monty_31.MontyField31 FP)) := do
  let mp := data_traitsFieldParametersInst.PackedMontyParametersInst.MontyParametersInst
  let prime ← mp.PRIME
  let half ← prime >>> 1#i32
  let bound := UScalar.hcast .I128 half
  if int <= bound then do
    let neg_bound ← IScalar.neg bound
    if int >= neg_bound then do
      let v ← utils.to_monty_signed mp (IScalar.cast .I32 int)
      let e ← monty_31.MontyField31.new_monty mp v
      ok (some e)
    else ok none
  else ok none

/-- `impl<FP: FieldParameters> PrimeField for MontyField31<FP>`
(`monty-31/src/monty_31.rs:671`). `PrimeField` has no members here. -/
def monty_31.MontyField31.Insts.P3_fieldFieldPrimeField {FP : Type}
    (_data_traitsFieldParametersInst : data_traits.FieldParameters FP) :
    p3_field.field.PrimeField (monty_31.MontyField31 FP) := {}

/-- `impl<FP: FieldParameters> Field for MontyField31<FP>`
(`monty-31/src/monty_31.rs:432`). `Field` has no members here. -/
def monty_31.MontyField31.Insts.P3_fieldFieldField {FP : Type}
    (_data_traitsFieldParametersInst : data_traits.FieldParameters FP) :
    p3_field.field.Field (monty_31.MontyField31 FP) := {}

/-! ## `no_packing::poseidon1` (`monty-31/src/no_packing/poseidon1.rs`) -/

/-- Upstream line 14. aeneas orders type parameters before const generics. -/
structure no_packing.poseidon1.Poseidon1InternalLayerMonty31 (MP : Type)
    (ILP : Type) (WIDTH : Std.Usize) where
  internal_constants :
    p3_poseidon1.internal.PartialRoundConstants (monty_31.MontyField31 MP) WIDTH
  _phantom : core.marker.PhantomData ILP

/-- Upstream line 25. -/
structure no_packing.poseidon1.Poseidon1ExternalLayerMonty31 (MP : Type)
    (MU : Type) (WIDTH : Std.Usize) where
  external_constants :
    p3_poseidon1.external.FullRoundConstants (monty_31.MontyField31 MP) WIDTH
  _mds : core.marker.PhantomData MU

/-- Upstream line 30: `Self { internal_constants, _phantom: PhantomData }`. -/
def no_packing.poseidon1.Poseidon1InternalLayerMonty31.Insts.P3_poseidon1InternalPartialRoundLayerConstructorMontyField31WIDTH
    {FP ILP : Type} {WIDTH : Std.Usize}
    (data_traitsFieldParametersInst : data_traits.FieldParameters FP)
    (_PartialRoundBaseParametersInst :
      poseidon1.PartialRoundBaseParameters ILP FP WIDTH) :
    p3_poseidon1.internal.PartialRoundLayerConstructor
      (no_packing.poseidon1.Poseidon1InternalLayerMonty31 FP ILP WIDTH)
      (monty_31.MontyField31 FP) WIDTH := {
  p3_fieldfieldFieldInst :=
    monty_31.MontyField31.Insts.P3_fieldFieldField data_traitsFieldParametersInst
  new_from_constants := fun internal_constants =>
    ok { internal_constants, _phantom := () }
}

/-- Upstream line 44: `Self { external_constants, _mds: PhantomData }`. -/
def no_packing.poseidon1.Poseidon1ExternalLayerMonty31.Insts.P3_poseidon1ExternalFullRoundLayerConstructorMontyField31WIDTH
    {FP MU : Type} (WIDTH : Std.Usize)
    (data_traitsFieldParametersInst : data_traits.FieldParameters FP)
    (_mdsMDSUtilsInst : mds.MDSUtils MU) :
    p3_poseidon1.external.FullRoundLayerConstructor
      (no_packing.poseidon1.Poseidon1ExternalLayerMonty31 FP MU WIDTH)
      (monty_31.MontyField31 FP) WIDTH := {
  p3_fieldfieldFieldInst :=
    monty_31.MontyField31.Insts.P3_fieldFieldField data_traitsFieldParametersInst
  new_from_constants := fun external_constants =>
    ok { external_constants, _mds := () }
}

/-! ## `no_packing::poseidon2` (`monty-31/src/no_packing/poseidon2.rs`) -/

/-- Upstream line 14. -/
structure no_packing.poseidon2.Poseidon2InternalLayerMonty31 (MP : Type)
    (ILP : Type) (WIDTH : Std.Usize) where
  internal_constants : alloc.vec.Vec (monty_31.MontyField31 MP)
  _phantom : core.marker.PhantomData ILP

/-- Upstream line 25. -/
structure no_packing.poseidon2.Poseidon2ExternalLayerMonty31 (MP : Type)
    (WIDTH : Std.Usize) where
  external_constants :
    p3_poseidon2.external.ExternalLayerConstants (monty_31.MontyField31 MP) WIDTH

/-- Upstream line 28: `Self { internal_constants, _phantom: PhantomData }`. -/
def no_packing.poseidon2.Poseidon2InternalLayerMonty31.Insts.P3_poseidon2InternalInternalLayerConstructorMontyField31
    {FP ILP : Type} {WIDTH : Std.Usize}
    (data_traitsFieldParametersInst : data_traits.FieldParameters FP)
    (_InternalLayerBaseParametersInst :
      poseidon2.InternalLayerBaseParameters ILP FP WIDTH) :
    p3_poseidon2.internal.InternalLayerConstructor
      (no_packing.poseidon2.Poseidon2InternalLayerMonty31 FP ILP WIDTH)
      (monty_31.MontyField31 FP) := {
  p3_fieldfieldFieldInst :=
    monty_31.MontyField31.Insts.P3_fieldFieldField data_traitsFieldParametersInst
  new_from_constants := fun internal_constants =>
    ok { internal_constants, _phantom := () }
}

/-- Upstream line 41: `Self { external_constants }`. -/
def no_packing.poseidon2.Poseidon2ExternalLayerMonty31.Insts.P3_poseidon2ExternalExternalLayerConstructorMontyField31WIDTH
    {FP : Type} (WIDTH : Std.Usize)
    (data_traitsFieldParametersInst : data_traits.FieldParameters FP) :
    p3_poseidon2.external.ExternalLayerConstructor
      (no_packing.poseidon2.Poseidon2ExternalLayerMonty31 FP WIDTH)
      (monty_31.MontyField31 FP) WIDTH := {
  p3_fieldfieldFieldInst :=
    monty_31.MontyField31.Insts.P3_fieldFieldField data_traitsFieldParametersInst
  new_from_constants := fun external_constants =>
    ok { external_constants }
}

end p3_monty_31
