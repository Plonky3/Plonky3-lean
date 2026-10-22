/-
# `p3-monty-31`: what p3-baby-bear uses from it that aeneas does not supply

Most of p3-monty-31 comes from its scoped extraction, `P3Monty31/Extraction/`
(the `data_traits`, `mds`, `poseidon1`/`poseidon2` parameter traits,
`MontyField31` itself, `MontyField31::new`, `utils::to_monty`, the `Clone`
impl). This file holds what that extraction does not produce:

* `MontyField31::new_array`, `MontyField31::new_2d_array`. They are in the LLBC
  with bodies, but aeneas drops them without a diagnostic
  (docs/extractor-issues.md, 4). They are transcribed below: an elementwise
  `new`, left to right, as the Rust `while` loops are.
* `MontyField31::new_monty` and the scalar arithmetic impls that wrap the
  extracted `utils` functions: `Add`, `Sub`, `Mul`, `Neg` and
  `PrimeCharacteristicRing::halve`. Like `new_array`, charon translates the
  first five (with bodies) but leaves them out of the declaration order aeneas
  reads, so they are not emitted (docs/extractor-issues.md, 4). `halve` is
  not translated at all: it is a provided method of `PrimeCharacteristicRing`
  that nothing calls, which charon skips even as a root. Each body is one line
  and is transcribed below; the arithmetic itself (`utils::add`, `sub`,
  `monty_reduce`, `halve_u32`) is extracted.
* the `no_packing` Poseidon layer types and their constructor impls. On a
  target with no SIMD these are the layers baby-bear's Poseidon instances use.
  The constructor bodies are one struct literal each and are transcribed.
* memberless `Field` and `PrimeField` witnesses for `MontyField31`. Both
  traits are memberless in `P3Monty31.Assumptions.P3Field`, so the witnesses carry no
  content.
-/
import P3Monty31.Extraction
import P3Util
import P3Poseidon1
import P3Poseidon2
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM ControlFlow Error

namespace p3_monty_31

/-- [p3_monty_31::monty_31::MontyField31::new_array]. Upstream:
`monty-31/src/monty_31.rs:88`, `while i < N { output[i] = Self::new(input[i]) }`.
The `else` branch is unreachable (`mapM` preserves length); it is a `panic`
rather than a proof only to keep this a plain transcription. -/
def monty_31.MontyField31.new_array {MP : Type}
    (data_traitsMontyParametersInst : data_traits.MontyParameters MP)
    {N : Std.Usize} (input : Array Std.U32 N) :
    RustM (Array (monty_31.MontyField31 MP) N) :=
  input.val.mapM (monty_31.MontyField31.new data_traitsMontyParametersInst) >>=
    fun l => if h : l.length = N.val then ok ⟨l, h⟩ else fail .panic

/-- [p3_monty_31::monty_31::MontyField31::new_2d_array]. Upstream:
`monty-31/src/monty_31.rs:101`, `new_array` on each row, left to right. -/
def monty_31.MontyField31.new_2d_array {MP : Type}
    (data_traitsMontyParametersInst : data_traits.MontyParameters MP)
    {N M : Std.Usize} (input : Array (Array Std.U32 N) M) :
    RustM (Array (Array (monty_31.MontyField31 MP) N) M) :=
  input.val.mapM (monty_31.MontyField31.new_array data_traitsMontyParametersInst) >>=
    fun l => if h : l.length = M.val then ok ⟨l, h⟩ else fail .panic

/-! ## Scalar arithmetic (`monty-31/src/monty_31.rs`) -/

/-- [p3_monty_31::monty_31::MontyField31::new_monty]. Upstream line 71:
`Self { value, _phantom: PhantomData }`, with no reduction. -/
def monty_31.MontyField31.new_monty {MP : Type}
    (_data_traitsMontyParametersInst : data_traits.MontyParameters MP) (value : Std.U32) :
    RustM (monty_31.MontyField31 MP) :=
  ok { value := value, _phantom := () }

/-- `<MontyField31<FP> as Add>::add`. Upstream line 733:
`Self::new_monty(add::<FP>(self.value, rhs.value))`. -/
def monty_31.MontyField31.add {MP : Type}
    (data_traitsMontyParametersInst : data_traits.MontyParameters MP)
    (self rhs : monty_31.MontyField31 MP) : RustM (monty_31.MontyField31 MP) := do
  let v ← utils.add data_traitsMontyParametersInst self.value rhs.value
  monty_31.MontyField31.new_monty data_traitsMontyParametersInst v

/-- `<MontyField31<FP> as Sub>::sub`. Upstream line 742:
`Self::new_monty(sub::<FP>(self.value, rhs.value))`. -/
def monty_31.MontyField31.sub {MP : Type}
    (data_traitsMontyParametersInst : data_traits.MontyParameters MP)
    (self rhs : monty_31.MontyField31 MP) : RustM (monty_31.MontyField31 MP) := do
  let v ← utils.sub data_traitsMontyParametersInst self.value rhs.value
  monty_31.MontyField31.new_monty data_traitsMontyParametersInst v

/-- `<MontyField31<FP> as Mul>::mul`. Upstream line 760:
`let long_prod = self.value as u64 * rhs.value as u64;`
`Self::new_monty(monty_reduce::<FP>(long_prod))`. The `*` is Rust's checked
`u64` multiplication, as aeneas renders it. -/
def monty_31.MontyField31.mul {MP : Type}
    (data_traitsMontyParametersInst : data_traits.MontyParameters MP)
    (self rhs : monty_31.MontyField31 MP) : RustM (monty_31.MontyField31 MP) := do
  let i ← lift (UScalar.cast .U64 self.value)
  let i1 ← lift (UScalar.cast .U64 rhs.value)
  let long_prod ← i * i1
  let v ← utils.monty_reduce data_traitsMontyParametersInst long_prod
  monty_31.MontyField31.new_monty data_traitsMontyParametersInst v

/-- `<MontyField31<FP> as Neg>::neg`. Upstream line 751: `Self::ZERO - self`,
where `ZERO` is `FP::MONTY_ZERO` (line 214). -/
def monty_31.MontyField31.neg {FP : Type}
    (data_traitsFieldParametersInst : data_traits.FieldParameters FP)
    (self : monty_31.MontyField31 FP) : RustM (monty_31.MontyField31 FP) := do
  let zero ← data_traitsFieldParametersInst.MONTY_ZERO
  monty_31.MontyField31.sub
    data_traitsFieldParametersInst.PackedMontyParametersInst.MontyParametersInst zero self

/-- `<MontyField31<FP> as PrimeCharacteristicRing>::halve`. Upstream line 225:
`Self::new_monty(halve_u32::<FP>(self.value))`. -/
def monty_31.MontyField31.halve {FP : Type}
    (data_traitsFieldParametersInst : data_traits.FieldParameters FP)
    (self : monty_31.MontyField31 FP) : RustM (monty_31.MontyField31 FP) := do
  let v ← utils.halve_u32 data_traitsFieldParametersInst self.value
  monty_31.MontyField31.new_monty
    data_traitsFieldParametersInst.PackedMontyParametersInst.MontyParametersInst v

/-! ## Powers of two and inversion (`monty-31/src/monty_31.rs`) -/

/-- `<MontyField31<FP> as PrimeCharacteristicRing>::square`, the trait default
(`field/src/field.rs:160`): `self.dup() * self.dup()`. -/
def monty_31.MontyField31.square {FP : Type}
    (data_traitsFieldParametersInst : data_traits.FieldParameters FP)
    (self : monty_31.MontyField31 FP) : RustM (monty_31.MontyField31 FP) :=
  monty_31.MontyField31.mul
    data_traitsFieldParametersInst.PackedMontyParametersInst.MontyParametersInst self self

/-- One iteration of the `exp_u64` loop at bit `j` of `power`: multiply
`product` by `current` when the bit is set, then square `current`. -/
def monty_31.MontyField31.exp_u64.step {FP : Type}
    (data_traitsFieldParametersInst : data_traits.FieldParameters FP) (power : Std.U64)
    (acc : monty_31.MontyField31 FP × monty_31.MontyField31 FP) (j : ℕ) :
    RustM (monty_31.MontyField31 FP × monty_31.MontyField31 FP) := do
  let product ←
    if power.val.testBit j then
      monty_31.MontyField31.mul
        data_traitsFieldParametersInst.PackedMontyParametersInst.MontyParametersInst
        acc.2 acc.1
    else ok acc.2
  let current ← monty_31.MontyField31.square data_traitsFieldParametersInst acc.1
  ok (current, product)

/-- `<MontyField31<FP> as PrimeCharacteristicRing>::exp_u64`, the trait default
(`field/src/field.rs:219`): square-and-multiply over the `bits_u64(power)` low
bits of `power`, least significant first.

The loop `for j in 0..bits_u64(power)` is a fold over `j < 64 - leading_zeros(power)`.

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

/-- `MontyField31::<FP>::MONTY_POWERS_OF_TWO` (line 115): entry `0` is
`FP::MONTY_ONE`, entry `i` for `1 <= i < 64` is `new_monty(to_monty_64(1 << i))`. -/
def monty_31.MontyField31.MONTY_POWERS_OF_TWO {FP : Type}
    (data_traitsFieldParametersInst : data_traits.FieldParameters FP) :
    RustM (Array (monty_31.MontyField31 FP) 64#usize) := do
  let mp := data_traitsFieldParametersInst.PackedMontyParametersInst.MontyParametersInst
  let one ← data_traitsFieldParametersInst.MONTY_ONE
  let rest ← (List.range' 1 63).mapM fun i => do
    let v ← utils.to_monty_64 mp ⟨BitVec.ofNat 64 (2 ^ i)⟩
    monty_31.MontyField31.new_monty mp v
  (if h : (one :: rest).length = 64 then ok ⟨one :: rest, h⟩ else fail .panic :
    RustM (Array (monty_31.MontyField31 FP) 64#usize))

/-- `<MontyField31<FP> as PrimeCharacteristicRing>::mul_2exp_u64` (line 230):
`self` for `exp = 0`, `self + self` for `exp = 1`, a multiplication by
`MONTY_POWERS_OF_TWO[exp]` for `exp < 64`, and by `TWO.exp_u64(exp)` beyond. -/
def monty_31.MontyField31.mul_2exp_u64 {FP : Type}
    (data_traitsFieldParametersInst : data_traits.FieldParameters FP)
    (self : monty_31.MontyField31 FP) (exp : Std.U64) : RustM (monty_31.MontyField31 FP) := do
  let mp := data_traitsFieldParametersInst.PackedMontyParametersInst.MontyParametersInst
  if exp = 0#u64 then ok self
  else if exp = 1#u64 then monty_31.MontyField31.add mp self self
  else if exp < 64#u64 then do
    let table ← monty_31.MontyField31.MONTY_POWERS_OF_TWO data_traitsFieldParametersInst
    let e ← Array.index_usize table (UScalar.cast .Usize exp)
    monty_31.MontyField31.mul mp self e
  else do
    let two ← data_traitsFieldParametersInst.MONTY_TWO
    let e ← monty_31.MontyField31.exp_u64 data_traitsFieldParametersInst two exp
    monty_31.MontyField31.mul mp self e

/-- `<MontyField31<FP> as Field>::try_inverse` (line 458).

- `None` when `self == ZERO`, compared on the stored value as the derived `PartialEq` does.
- Otherwise `v = gcd_inversion_prime_field_32::<31>(self.value, PRIME)`.
- Then `monty_reduce(((PRIME as i64) << 30 + v) as u64)`, multiplied by `2^(3 · MONTY_BITS - 60)`.

The `i64` addition is checked, and the cast to `u64` reinterprets the bits. -/
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

/-! ## Integers into the field (`QuotientMap`, `monty-31/src/monty_31.rs:518`) -/

/-- `QuotientMap<u32>::from_canonical_checked`: `(int < PRIME).then(|| Self::new(int))`. -/
def monty_31.MontyField31.Insts.P3_fieldIntegersQuotientMapU32.from_canonical_checked
    {FP : Type} (data_traitsFieldParametersInst : data_traits.FieldParameters FP)
    (int : Std.U32) : RustM (Option (monty_31.MontyField31 FP)) := do
  let mp := data_traitsFieldParametersInst.PackedMontyParametersInst.MontyParametersInst
  let prime ← mp.PRIME
  if int < prime then do
    let v ← monty_31.MontyField31.new mp int
    ok (some v)
  else ok none

/-- `QuotientMap<i32>::from_int`: `Self::new_monty(to_monty_signed(int))`. -/
def monty_31.MontyField31.Insts.P3_fieldIntegersQuotientMapI32.from_int
    {FP : Type} (data_traitsFieldParametersInst : data_traits.FieldParameters FP)
    (int : Std.I32) : RustM (monty_31.MontyField31 FP) := do
  let mp := data_traitsFieldParametersInst.PackedMontyParametersInst.MontyParametersInst
  let v ← utils.to_monty_signed mp int
  monty_31.MontyField31.new_monty mp v

/-- `QuotientMap<i32>::from_canonical_checked`, with `bound = (PRIME >> 1) as i32`:
`Some(new_monty(to_monty_signed(int)))` when `-bound <= int <= bound`, else `None`. -/
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

/-- `QuotientMap<u64>::from_int`: `Self::new_monty(to_monty_64(int))`. -/
def monty_31.MontyField31.Insts.P3_fieldIntegersQuotientMapU64.from_int
    {FP : Type} (data_traitsFieldParametersInst : data_traits.FieldParameters FP)
    (int : Std.U64) : RustM (monty_31.MontyField31 FP) := do
  let mp := data_traitsFieldParametersInst.PackedMontyParametersInst.MontyParametersInst
  let v ← utils.to_monty_64 mp int
  monty_31.MontyField31.new_monty mp v

/-- `QuotientMap<u64>::from_canonical_checked`:
`(int < PRIME as u64).then(|| Self::new(int as u32))`. -/
def monty_31.MontyField31.Insts.P3_fieldIntegersQuotientMapU64.from_canonical_checked
    {FP : Type} (data_traitsFieldParametersInst : data_traits.FieldParameters FP)
    (int : Std.U64) : RustM (Option (monty_31.MontyField31 FP)) := do
  let mp := data_traitsFieldParametersInst.PackedMontyParametersInst.MontyParametersInst
  let prime ← mp.PRIME
  if int < UScalar.cast .U64 prime then do
    let v ← monty_31.MontyField31.new mp (UScalar.cast .U32 int)
    ok (some v)
  else ok none

/-- `QuotientMap<i64>::from_int`: `Self::new_monty(to_monty_64_signed(int))`. -/
def monty_31.MontyField31.Insts.P3_fieldIntegersQuotientMapI64.from_int
    {FP : Type} (data_traitsFieldParametersInst : data_traits.FieldParameters FP)
    (int : Std.I64) : RustM (monty_31.MontyField31 FP) := do
  let mp := data_traitsFieldParametersInst.PackedMontyParametersInst.MontyParametersInst
  let v ← utils.to_monty_64_signed mp int
  monty_31.MontyField31.new_monty mp v

/-- `QuotientMap<i64>::from_canonical_checked`, with `bound = (PRIME >> 1) as i64`:
`Some(new_monty(to_monty_signed(int as i32)))` when `-bound <= int <= bound`, else `None`. -/
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

/-- `QuotientMap<u128>::from_int`:
`Self::new_monty(to_monty((int % (PRIME as u128)) as u32))`. -/
def monty_31.MontyField31.Insts.P3_fieldIntegersQuotientMapU128.from_int
    {FP : Type} (data_traitsFieldParametersInst : data_traits.FieldParameters FP)
    (int : Std.U128) : RustM (monty_31.MontyField31 FP) := do
  let mp := data_traitsFieldParametersInst.PackedMontyParametersInst.MontyParametersInst
  let prime ← mp.PRIME
  let r ← int % UScalar.cast .U128 prime
  let v ← utils.to_monty mp (UScalar.cast .U32 r)
  monty_31.MontyField31.new_monty mp v

/-- `QuotientMap<u128>::from_canonical_checked`:
`(int < PRIME as u128).then(|| Self::new(int as u32))`. -/
def monty_31.MontyField31.Insts.P3_fieldIntegersQuotientMapU128.from_canonical_checked
    {FP : Type} (data_traitsFieldParametersInst : data_traits.FieldParameters FP)
    (int : Std.U128) : RustM (Option (monty_31.MontyField31 FP)) := do
  let mp := data_traitsFieldParametersInst.PackedMontyParametersInst.MontyParametersInst
  let prime ← mp.PRIME
  if int < UScalar.cast .U128 prime then do
    let v ← monty_31.MontyField31.new mp (UScalar.cast .U32 int)
    ok (some v)
  else ok none

/-- `QuotientMap<i128>::from_int`:
`Self::new_monty(to_monty_signed((int % (PRIME as i128)) as i32))`. -/
def monty_31.MontyField31.Insts.P3_fieldIntegersQuotientMapI128.from_int
    {FP : Type} (data_traitsFieldParametersInst : data_traits.FieldParameters FP)
    (int : Std.I128) : RustM (monty_31.MontyField31 FP) := do
  let mp := data_traitsFieldParametersInst.PackedMontyParametersInst.MontyParametersInst
  let prime ← mp.PRIME
  let r ← int % UScalar.hcast .I128 prime
  let v ← utils.to_monty_signed mp (IScalar.cast .I32 r)
  monty_31.MontyField31.new_monty mp v

/-- `QuotientMap<i128>::from_canonical_checked`, with `bound = (PRIME >> 1) as i128`:
`Some(new_monty(to_monty_signed(int as i32)))` when `-bound <= int <= bound`, else `None`. -/
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
