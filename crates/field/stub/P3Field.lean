/-
# `p3-field`: hand-written interface

aeneas cannot translate p3-field's trait hierarchy: `PrimeCharacteristicRing`,
`Algebra`, `Field`, `PrimeField` and `PackedField` are mutually recursive
through their associated types (`PrimeSubfield: PrimeField`,
`Packing: PackedField`), and a scoped extraction pulls in the traits' default
method bodies (`sqrt`, `tonelli_shanks`, …), which fail on their own. See
docs/extractor-issues.md, 9.

Every trait here is a Lean `structure`, as aeneas would emit one, but it declares
only the members that p3-baby-bear and the scoped dependency extractions
actually project. Instances are passed in as parameters, so anything proved
about code generic over one of these traits holds for *every* implementation,
which is weaker than assuming `opaque` ring operations. Field
names and argument order follow aeneas's naming scheme exactly, so the
generated code elaborates against them unchanged.
-/
module

public import Aeneas
public import CoreModels

@[expose] public section
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM ControlFlow Error

namespace p3_field

/-- [p3_field::dup::Dup]. Upstream: `field/src/dup.rs`, a blanket
`impl<T: Copy> Dup for T` whose body is `*self`. -/
structure dup.Dup (Self : Type) where
  dup : Self → RustM Self

/-- [p3_field::field::PrimeCharacteristicRing], restricted to the members the
extraction uses. Upstream: `field/src/field.rs:55`. -/
structure field.PrimeCharacteristicRing (Self : Type) where
  coreopsarithAddInst : core.ops.arith.Add Self Self Self
  coreopsarithSubInst : core.ops.arith.Sub Self Self Self
  coreopsarithAddAssignInst : core.ops.arith.AddAssign Self Self
  dupDupInst : dup.Dup Self
  double : Self → RustM Self
  halve : Self → RustM Self
  div_2exp_u64 : Self → Std.U64 → RustM Self
  ZERO : RustM Self
  from_u8 : Std.U8 → RustM Self
  from_u16 : Std.U16 → RustM Self

/-- [p3_field::field::Algebra], restricted to the members the extraction uses.

Upstream: `field/src/field.rs:711`. -/
structure field.Algebra (Self F : Type) where
  PrimeCharacteristicRingInst : field.PrimeCharacteristicRing Self
  coreopsarithAddInst : core.ops.arith.Add Self F Self
  coreopsarithAddAssignInst : core.ops.arith.AddAssign Self F
  coreopsarithMulInst : core.ops.arith.Mul Self F Self

/-- [p3_field::integers::QuotientMap], restricted to the member the extraction uses.

Upstream: `field/src/integers.rs`. -/
structure integers.QuotientMap (Self Int : Type) where
  from_canonical_checked : Int → RustM (core.option.Option Self)

instance {Self : Type} : Inhabited (field.Algebra Self Self) :=
  ⟨{ PrimeCharacteristicRingInst :=
      { coreopsarithAddInst := ⟨fun _ _ => fail .panic⟩
        coreopsarithSubInst := ⟨fun _ _ => fail .panic⟩
        coreopsarithAddAssignInst := ⟨fun _ _ => fail .panic⟩
        dupDupInst := ⟨fun _ => fail .panic⟩
        double := fun _ => fail .panic
        halve := fun _ => fail .panic
        div_2exp_u64 := fun _ _ => fail .panic
        ZERO := fail .panic
        from_u8 := fun _ => fail .panic
        from_u16 := fun _ => fail .panic }
     coreopsarithAddInst := ⟨fun _ _ => fail .panic⟩
     coreopsarithAddAssignInst := ⟨fun _ _ => fail .panic⟩
     coreopsarithMulInst := ⟨fun _ _ => fail .panic⟩ }⟩

/-- The `Copy` witness of a `Field` whose model does not give one.

Assumed: no model that builds a `Field` instance projects it. -/
opaque field.Field.unmodelledCopy (Self : Type) : core.marker.Copy Self :=
  ⟨⟨fun x => ok x, fun _ x => ok x⟩⟩

/-- The `Algebra<Self>` witness of a `Field` whose model does not give one.

Assumed: no model that builds a `Field` instance projects it. -/
opaque field.Field.unmodelledAlgebra (Self : Type) : field.Algebra Self Self

/-- `Field::bits` of a `Field` whose model does not give it.

Assumed: no model that builds a `Field` instance projects it. -/
opaque field.Field.unmodelledBits (Self : Type) : RustM Std.Usize := fail .panic

/-- [p3_field::field::Field], restricted to the members the extraction uses.

Upstream: `field/src/field.rs:1059`.

A model that only passes instances through, as p3-monty-31's, builds one with `{}` and leaves every member assumed. -/
structure field.Field (Self : Type) where
  coremarkerCopyInst : core.marker.Copy Self := field.Field.unmodelledCopy Self
  AlgebraInst : field.Algebra Self Self := field.Field.unmodelledAlgebra Self
  bits : RustM Std.Usize := field.Field.unmodelledBits Self

instance {Self : Type} : Inhabited (field.Field Self) := ⟨{}⟩

instance {Self : Type} : Inhabited (integers.QuotientMap Self Std.U64) :=
  ⟨⟨fun _ => fail .panic⟩⟩

/-- The `Field` supertrait witness of a `PrimeField` whose model does not give one.

Assumed: no model that builds a `PrimeField` instance projects it. -/
opaque field.PrimeField.unmodelledField (Self : Type) : field.Field Self

/-- The `QuotientMap<u64>` witness of a `PrimeField` whose model does not give one.

Assumed: no model that builds a `PrimeField` instance projects it. -/
opaque field.PrimeField.unmodelledQuotientMapU64 (Self : Type) : integers.QuotientMap Self Std.U64

/-- [p3_field::field::PrimeField], restricted to the members the extraction uses.

Upstream: `field/src/field.rs:1264`.

A model that only passes instances through builds one with `{}`, as for `Field`. -/
structure field.PrimeField (Self : Type) where
  FieldInst : field.Field Self := field.PrimeField.unmodelledField Self
  integersQuotientMapSelfU64Inst : integers.QuotientMap Self Std.U64 :=
    field.PrimeField.unmodelledQuotientMapU64 Self

/-- [p3_field::field::PrimeField64], restricted to the members the extraction uses.

Upstream: `field/src/field.rs:1267`. -/
structure field.PrimeField64 (Self : Type) where
  PrimeFieldInst : field.PrimeField Self
  ORDER_U64 : RustM Std.U64
  as_canonical_u64 : Self → RustM Std.U64
  to_unique_u64 : Self → RustM Std.U64

/-- [p3_field::field::PrimeField32], restricted to the members the extraction uses.

Upstream: `field/src/field.rs:1289`. -/
structure field.PrimeField32 (Self : Type) where
  PrimeField64Inst : field.PrimeField64 Self
  ORDER_U32 : RustM Std.U32
  as_canonical_u32 : Self → RustM Std.U32
  to_unique_u32 : Self → RustM Std.U32

/-- [p3_field::field::BasedVectorSpace], restricted to the members the extraction uses.

Upstream: `field/src/field.rs:445`. -/
structure field.BasedVectorSpace (Self F : Type) where
  PrimeCharacteristicRingInst : field.PrimeCharacteristicRing F
  from_basis_coefficients_fn : forall {Fn : Type}, core.ops.function.FnMut Fn Std.Usize F →
    Fn → RustM (Self × Fn)

/-- `impl<F: PrimeCharacteristicRing> BasedVectorSpace<F> for F` (`field/src/field.rs:630`).

Its only basis coefficient is the element itself: the closure runs once, at index 0. -/
@[reducible]
def field.BasedVectorSpace.Blanket {F : Type} (inst : field.PrimeCharacteristicRing F) :
    field.BasedVectorSpace F F := {
  PrimeCharacteristicRingInst := inst
  from_basis_coefficients_fn := fun FnMutInst c => FnMutInst.call_mut c 0#usize
}

/-- [p3_field::field::UniformSamplingField]. Upstream: `field/src/field.rs:613`.
Complete: the trait has exactly these two associated constants. -/
structure field.UniformSamplingField (Self : Type) where
  MAX_SINGLE_SAMPLE_BITS : RustM Std.Usize
  SAMPLING_BITS_M : RustM (Array Std.U64 64#usize)

/-- [p3_field::exponentiation::exp_1420470955]: `val ^ 1420470955`, via an addition chain.

Upstream: `field/src/exponentiation.rs:37`.

Assumed: its body is a chain of `square`/`mul` calls on a `PrimeCharacteristicRing` whose methods are not modelled here. -/
opaque exponentiation.exp_1420470955 {R : Type}
    (PrimeCharacteristicRingInst : field.PrimeCharacteristicRing R) (val : R) :
    RustM R

/-- [p3_field::exponentiation::exp_1725656503]: `val ^ 1725656503`, via an
addition chain. Upstream: `field/src/exponentiation.rs:62`. Assumed: its body
is a chain of `square`/`mul` calls on a `PrimeCharacteristicRing` whose methods
are not modelled here. -/
opaque exponentiation.exp_1725656503 {R : Type}
    (PrimeCharacteristicRingInst : field.PrimeCharacteristicRing R) (val : R) :
    RustM R

/-- [p3_field::helpers::halve_u32]: `x / 2` in `F_P`, for `x < P`. Upstream:
`field/src/helpers.rs:113`, `let shift = (P + 1) >> 1; let half = x >> 1;`
`if x & 1 == 0 { half } else { half + shift }`. Transcribed as aeneas renders
it: `+` is checked, and the `else` addition happens only in that branch. -/
def helpers.halve_u32 (P : Std.U32) (x : Std.U32) : RustM Std.U32 := do
  let i ← P + 1#u32
  let shift ← i >>> 1#i32
  let half ← x >>> 1#i32
  let i1 ← lift (x &&& 1#u32)
  if i1 = 0#u32 then ok half else half + shift

end p3_field
