module

public import Aeneas
public import CoreModels

@[expose] public section

/-!
# Extensions to the Lean libraries of hax's backend

Declarations that the pinned `Aeneas` and `CoreModels` libraries lack and that
generated or stub code needs in order to elaborate. They model Rust's
`core`/`alloc`, not Plonky3, so they are shared by every crate.

Each declaration here is a candidate to upstream to `cryspen/hax-lean` or
`cryspen/aeneas`, and is deleted once the pinned revision provides it.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM ControlFlow Error

namespace CoreModels

/-- `impl<T: ?Sized> Clone for PhantomData<T>`, whose body is `Self`
(`library/core/src/marker.rs`). Referenced by the derived `Clone` for
`MontyField31`. -/
def core.marker.PhantomData.Insts.CoreCloneClone.clone {T : Type}
    (self : core.marker.PhantomData T) : RustM (core.marker.PhantomData T) :=
  ok self

/-- `impl<T: ?Sized + AsRef<U>, U: ?Sized> AsRef<U> for &T`, whose body is
`<T as AsRef<U>>::as_ref(*self)` (`library/core/src/convert/mod.rs`). aeneas
erases shared references, so `&T` is `T` and the impl is the inner one.
Referenced by baby-bear's `TwoAdicData<&'static [MontyField31<_>]>` impl. -/
def core.Shared0T.Insts.CoreConvertAsRef {T U : Type}
    (convertAsRefInst : core.convert.AsRef T U) : core.convert.AsRef T U :=
  { as_ref := convertAsRefInst.as_ref }

/-- `u64::reverse_bits` (`library/core/src/num/uint_macros.rs`).

Bit `i` of the result is bit `63 - i` of the operand.

p3-binary-field's portable carry-less multiply calls it. -/
def core.num.U64.reverse_bits (x : Std.U64) : RustM Std.U64 :=
  ok ⟨x.bv.reverse⟩

/-- `usize::trailing_zeros` (`library/core/src/num/uint_macros.rs`): the index of the
lowest set bit, or the width for zero.

p3-binary-field's basis tables call it, at build time in Rust. -/
def core.num.Usize.trailing_zeros (x : Std.Usize) : RustM Std.U32 :=
  ok ⟨BitVec.ofNat 32 (((List.range UScalarTy.Usize.numBits).find? fun i => x.val.testBit i).getD
    UScalarTy.Usize.numBits)⟩

/-- `Ord::min`, the provided method (`library/core/src/cmp.rs`).

It returns `other` exactly when `other < self`, as `core::cmp::min(self, other)` does, whose model is reused.

p3-mersenne-31's `reduce_64` calls it. -/
def core.cmp.Ord.min.default {Self : Type} (OrdInst : core.cmp.Ord Self)
    (self other : Self) : RustM Self :=
  core.cmp.min OrdInst self other

/-- `<u32 as Ord>::min`, the provided method `Ord::min` at `u32`.

The generated code calls it by name, as a method of CoreModels' `Ord` instance for `u32`,
which does not define it. -/
def core.U32.Insts.CoreCmpOrd.min (self other : Std.U32) : RustM Std.U32 :=
  core.cmp.Ord.min.default core.U32.Insts.CoreCmpOrd self other

/-- `<usize as Ord>::min`, the provided method `Ord::min` at `usize`.
p3-blake3's `chunk` clamps a chunk's end to the message length with it. -/
def core.Usize.Insts.CoreCmpOrd.min (self other : Std.Usize) : RustM Std.Usize :=
  core.cmp.Ord.min.default core.Usize.Insts.CoreCmpOrd self other

/-- `bool::then` (`library/core/src/bool.rs`):
`if self { Some(f()) } else { None }`. -/
def core.bool.Bool.then {T F : Type} (FnOnceInst : core.ops.function.FnOnce F Unit T)
    (self : Bool) (f : F) : RustM (core.option.Option T) :=
  if self then do
    let x ← FnOnceInst.call_once f ()
    ok (core.option.Option.Some x)
  else ok core.option.Option.None

/-- `i64::unsigned_abs` (`library/core/src/num/int_macros.rs`):
`self.wrapping_abs() as u64`, the magnitude, which fits in `u64` even for `i64::MIN`. -/
def core.num.I64.unsigned_abs (x : Std.I64) : RustM Std.U64 :=
  ok ⟨BitVec.ofNat _ x.val.natAbs⟩

/-- `core::hint::assert_unchecked(cond)` (`library/core/src/hint.rs`).

A false `cond` is undefined behaviour, so it is modelled as a failure (`undef`).

A proof that a caller does not fail therefore proves `cond` at every call. -/
def core.hint.assert_unchecked (cond : Bool) : RustM Unit :=
  if cond then ok () else fail .undef

/-- `u64::wrapping_add_signed`, whose body is `self.wrapping_add(rhs as Self)`
(`library/core/src/num/uint_macros.rs`). -/
def core.num.U64.wrapping_add_signed (self : Std.U64) (rhs : Std.I64) : RustM Std.U64 :=
  core.num.U64.wrapping_add self (IScalar.hcast .U64 rhs)

/-- `i128::unsigned_abs`, whose body is `self.wrapping_abs() as u128`
(`library/core/src/num/int_macros.rs`): `|self|`, which fits in a `u128` even
for `i128::MIN`. -/
def core.num.I128.unsigned_abs (self : Std.I128) : RustM Std.U128 :=
  ok ⟨BitVec.ofNat _ self.val.natAbs⟩

/-- `u32::wrapping_add_signed`: `self + rhs` modulo `2^32`, with `rhs` signed.

Rust computes `self.wrapping_add(rhs as Self)` (`library/core/src/num/uint_macros.rs`).

The cast reinterprets the bits of `rhs`.

p3-monty-31's signed conversions into Montgomery form use it. -/
def core.num.U32.wrapping_add_signed (self : Std.U32) (rhs : Std.I32) : RustM Std.U32 :=
  ok (self.wrapping_add (IScalar.hcast .U32 rhs))

/-- `fmt::rt::Argument::new_display` (`library/core/src/fmt/rt.rs`): one argument
of a formatted message. `fmt.Arguments` is `Unit`, so what an argument displays is
not modelled; only the panic it reaches is.

p3-blake2s's scalar `hash_many` formats its `assert!` message with it. -/
def core.fmt.rt.Argument.new_display {T : Type} (_displayInst : core.fmt.Display T) (_x : T) :
    RustM core.fmt.rt.Argument :=
  ok ⟨.Placeholder ()⟩

/-! ## Iterators

aeneas projects `fold` and `reduce` from an `Iterator` dictionary, and refers to the
`Sum`/`Product` traits, `Iterator::sum` and the `IntoIterator` impl of `&[T; N]`.
`CoreModels`' `Iterator` carries only `next`; these are its provided methods, driven by
`next` through `CoreModels`' own defaults. -/

/-- `Iterator::fold`, as a projection of the dictionary. -/
abbrev core.iter.traits.iterator.Iterator.fold {Self Item : Type}
    (IteratorInst : core.iter.traits.iterator.Iterator Self Item) {B F : Type}
    (FnInst : core.ops.function.FnMut F (B × Item) B) (self : Self) (init : B) (f : F) :
    RustM B :=
  core.iter.traits.iterator.Iterator.fold.default IteratorInst FnInst self init f

/-- `Iterator::reduce`, as a projection of the dictionary. -/
abbrev core.iter.traits.iterator.Iterator.reduce {Self Item : Type}
    (IteratorInst : core.iter.traits.iterator.Iterator Self Item) {F : Type}
    (FnInst : core.ops.function.FnMut F (Item × Item) Item) (self : Self) (f : F) :
    RustM (core.option.Option Item) :=
  core.iter.traits.iterator.Iterator.reduce.default IteratorInst FnInst self f

/-- Trait declaration: `core::iter::traits::accum::Sum`. -/
structure core.iter.traits.accum.Sum (Self A : Type) where
  sum : forall {I : Type}, core.iter.traits.iterator.Iterator I A → I → RustM Self

/-- Trait declaration: `core::iter::traits::accum::Product`. -/
structure core.iter.traits.accum.Product (Self A : Type) where
  product : forall {I : Type}, core.iter.traits.iterator.Iterator I A → I → RustM Self

/-- `Iterator::sum`: `S::sum(self)`. -/
def core.iter.traits.iterator.Iterator.sum.default {Self Item S : Type}
    (IteratorInst : core.iter.traits.iterator.Iterator Self Item)
    (SumInst : core.iter.traits.accum.Sum S Item) (self : Self) : RustM S :=
  SumInst.sum IteratorInst self

/-- `Iterator::product`: `P::product(self)`. -/
def core.iter.traits.iterator.Iterator.product.default {Self Item P : Type}
    (IteratorInst : core.iter.traits.iterator.Iterator Self Item)
    (ProductInst : core.iter.traits.accum.Product P Item) (self : Self) : RustM P :=
  ProductInst.product IteratorInst self

/-- `impl IntoIterator for &[T; N]`: the slice iterator over the array. -/
def core.SharedAArray.Insts.CoreIterTraitsCollectIntoIteratorSharedATIter.into_iter
    {T : Type} {N : Std.Usize} (self : Array T N) : RustM (core.slice.iter.Iter T) := do
  let s ← core.array.Array.as_slice self
  core.slice.Slice.iter s

@[reducible]
def core.SharedAArray.Insts.CoreIterTraitsCollectIntoIteratorSharedATIter (T : Type)
    (N : Std.Usize) :
    core.iter.traits.collect.IntoIterator (Array T N) T (core.slice.iter.Iter T) := {
  iteratorIteratorInst := core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT T
  into_iter := core.SharedAArray.Insts.CoreIterTraitsCollectIntoIteratorSharedATIter.into_iter
}

/-- `bool::then_some` (`library/core/src/bool.rs`): `if self { Some(t) } else { None }`. -/
def core.bool.Bool.then_some {T : Type} (self : Bool) (t : T) :
    RustM (core.option.Option T) :=
  ok (if self then core.option.Option.Some t else core.option.Option.None)

/-- `u128::trailing_zeros` (`library/core/src/num/uint_macros.rs`): the number of
trailing zero bits, `128` for zero. -/
def core.num.U128.trailing_zeros (x : Std.U128) : RustM Std.U32 :=
  ok ⟨BitVec.ofNat 32 (((List.range 128).find? fun i => x.val.testBit i).getD 128)⟩

/-- `Range::contains` (`library/core/src/ops/range.rs`), the inherent method:
`<Self as RangeBounds<Idx>>::contains(self, item)`. The first dictionary is the
`Idx: PartialOrd<Idx>` bound of the impl block, which the body does not use. -/
def core.ops.range.Range.contains {Idx U : Type} (_ : core.cmp.PartialOrd Idx Idx)
    (IdxU : core.cmp.PartialOrd Idx U) (UIdx : core.cmp.PartialOrd U Idx)
    (self : core.ops.range.Range Idx) (item : U) : RustM Bool :=
  core.ops.range.RangeBounds.contains.default
    (core.ops.range.Range.Insts.CoreOpsRangeRangeBounds Idx) IdxU UIdx self item

/-- `u64::trailing_zeros` (`library/core/src/num/uint_macros.rs`).

It counts the trailing zero bits, and gives `64` for zero.

p3-security's fixed-point ceiling logarithm calls it on a power of two. -/
def core.num.U64.trailing_zeros (x : Std.U64) : RustM Std.U32 :=
  ok ⟨BitVec.ofNat 32 (((List.range 64).find? fun i => x.val.testBit i).getD 64)⟩

/-- `core::num::nonzero::ZeroablePrimitive` (`library/core/src/num/nonzero.rs`).

It is the sealed trait of the primitives that a nonzero wrapper can hold.

Only the zero test is modelled. -/
structure core.num.nonzero.ZeroablePrimitive (T : Type) where
  is_zero : T → Bool

/-- `impl ZeroablePrimitive for u64`. -/
def core.U64.Insts.CoreNumNonzeroZeroablePrimitiveNonZeroU64Inner :
    core.num.nonzero.ZeroablePrimitive Std.U64 :=
  { is_zero := fun x => x.val = 0 }

/-- `core::num::NonZero<T>`, represented by its value.

Its only constructor checks for zero, so every value the model builds is nonzero. -/
def core.num.nonzero.NonZero (T : Type) : Type := T

/-- `NonZero::new` (`library/core/src/num/nonzero.rs`) returns `Some` exactly for a nonzero value. -/
def core.num.nonzero.NonZero.new {T : Type} (inst : core.num.nonzero.ZeroablePrimitive T)
    (n : T) : RustM (core.option.Option (core.num.nonzero.NonZero T)) :=
  ok (if inst.is_zero n then core.option.Option.None else core.option.Option.Some n)

/-- `NonZero::get` (`library/core/src/num/nonzero.rs`): the wrapped value. -/
def core.num.nonzero.NonZero.get {T : Type} (_ : core.num.nonzero.ZeroablePrimitive T)
    (self : core.num.nonzero.NonZero T) : RustM T :=
  ok self

/-- `impl PartialEq for str` (`library/core/src/str/traits.rs`), byte-wise equality.

Derived equality on a struct with a `&'static str` field calls it. -/
def core.Str.Insts.CoreCmpPartialEqStr.eq (self other : Str) : RustM Bool :=
  ok (decide (self = other))

/-- A word shifted right by the shift amount modulo the word size.

Aeneas models it as a pure function, and the generated code binds it. -/
def core.num.Usize.wrapping_shr (x : Std.Usize) (s : Std.U32) : RustM Std.Usize :=
  ok (Aeneas.Std.core.num.Usize.wrapping_shr x s)

/-- The wrapped right shift, with a flag set when the amount is at least the word size. -/
def core.num.Usize.overflowing_shr (x : Std.Usize) (s : Std.U32) :
    RustM (Std.Usize × Bool) :=
  ok (Aeneas.Std.core.num.Usize.wrapping_shr x s, decide (UScalarTy.Usize.numBits ≤ s.val))

/-- A word with its bits in reverse order: bit i moves to bit w - 1 - i. -/
def core.num.Usize.reverse_bits (x : Std.Usize) : RustM Std.Usize :=
  ok ⟨x.bv.reverse⟩

/-- A vector borrowed as a slice.

The model stores a vector as its elements, so this is the identity. -/
def alloc.vec.Vec.Insts.CoreBorrowBorrowSlice (T : Type _) :
    core.borrow.Borrow (alloc.vec.Vec T) (Slice T) :=
  { borrow := rust_primitives.sequence.seq_to_slice }

/-- A shared reference borrowed as its target.

Aeneas erases shared references, so this is the identity. -/
def core.Shared0T.Insts.CoreBorrowBorrow (T : Type _) : core.borrow.Borrow T T :=
  { borrow := fun x => ok x }

/-- Mutable borrowing.

It returns the borrow and the function that writes it back, as aeneas encodes a mutable result. -/
structure core.borrow.BorrowMut (Self : Type _) (Borrowed : Type _) where
  coreborrowBorrowSelfBorrowedInst : core.borrow.Borrow Self Borrowed
  borrow_mut : Self → RustM (Borrowed × (Borrowed → Self))

/-- A vector borrowed mutably as a slice, the identity on the modelled elements. -/
def alloc.vec.Vec.Insts.CoreBorrowBorrowMutSlice (T : Type _) (_A : Type _) :
    core.borrow.BorrowMut (alloc.vec.Vec T) (Slice T) :=
  { coreborrowBorrowSelfBorrowedInst := alloc.vec.Vec.Insts.CoreBorrowBorrowSlice T
    borrow_mut := rust_primitives.sequence.seq_to_slice_mut }

/-- The smallest power of two at least x, so 1 for 0.

Rust panics on overflow in a debug build and returns 0 in a release build.

This is the debug build, as for every arithmetic operation of the model. -/
def core.num.Usize.next_power_of_two (x : Std.Usize) : RustM Std.Usize :=
  if x.val.nextPowerOfTwo < 2 ^ UScalarTy.Usize.numBits then
    ok ⟨BitVec.ofNat _ x.val.nextPowerOfTwo⟩
  else fail .panic

/-- The larger of two words, the second one on a tie. -/
def core.Usize.Insts.CoreCmpOrd.max (self other : Std.Usize) : RustM Std.Usize :=
  ok (if other < self then self else other)

/-- The exact length of an iterator.

The model reads the iterator's own length. -/
def core.iter.traits.exact_size.ExactSizeIterator.len.default {Self Item : Type _}
    (inst : core.iter.traits.exact_size.ExactSizeIterator Self Item) (self : Self) :
    RustM Std.Usize :=
  inst.len self

/-- Exchanges the contents of two slices, and panics unless their lengths are equal. -/
def core.slice.Slice.swap_with_slice {T : Type _} (a b : Slice T) : RustM (Slice T × Slice T) :=
  if a.length = b.length then ok (b, a) else fail .panic

/-- The length of a range of words: end - start, or 0 when start >= end. -/
def core.ops.range.RangeUsize.Insts.CoreIterTraitsExact_sizeExactSizeIteratorUsize :
    core.iter.traits.exact_size.ExactSizeIterator (core.ops.range.Range Std.Usize) Std.Usize := {
  iteratorIteratorInst :=
    core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator core.Usize.Insts.CoreIterRangeStep
  len := fun r => ok ⟨BitVec.ofNat _ (r.«end».val - r.start.val)⟩
}

/-- Word subtraction clamped at 0.

The Aeneas model of this operation has no exposed body, so nothing can be proved about it.

Generated code that needs the value calls this exposed copy instead. -/
def core.num.Usize.saturating_sub_exposed (x y : Std.Usize) : RustM Std.Usize :=
  ok ⟨BitVec.ofNat _ (x.val - y.val)⟩

end CoreModels
