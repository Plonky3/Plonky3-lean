/-
# p3-field: hand-written interface

aeneas cannot translate p3-field's trait hierarchy (docs/extractor-issues.md, 9).

The ring, algebra, field, prime field and packed field traits are mutually recursive.

The recursion runs through their associated types: the prime subfield and the packing.

A scoped extraction also pulls in the traits' default method bodies, such as the square root.

Those bodies fail on their own.

Every trait here is a Lean structure, as aeneas would emit one.

It declares only the members that p3-baby-bear and the scoped dependency extractions project.

Instances are passed in as parameters.

So a proof about code generic over one of these traits holds for every implementation.

That is weaker than assuming opaque ring operations.

Field names and argument order follow aeneas's naming scheme exactly.

So the generated code elaborates against them unchanged.
-/
module

public import Aeneas
public import CoreModels
public import HaxExt

@[expose] public section
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM ControlFlow Error

namespace p3_field

/-- The duplication trait (field/src/dup.rs).

Upstream it is a blanket implementation for every copyable type, returning a copy. -/
structure dup.Dup (Self : Type) where
  dup : Self → RustM Self

/-- The prime characteristic ring trait, restricted to the members the extraction uses.

Upstream: field/src/field.rs:55. -/
structure field.PrimeCharacteristicRing (Self : Type) where
  coreopsarithAddInst : core.ops.arith.Add Self Self Self
  coreopsarithSubInst : core.ops.arith.Sub Self Self Self
  coreopsarithAddAssignInst : core.ops.arith.AddAssign Self Self
  dupDupInst : dup.Dup Self
  double : Self → RustM Self
  halve : Self → RustM Self
  div_2exp_u64 : Self → Std.U64 → RustM Self
  ZERO : RustM Self
  ONE : RustM Self
  NEG_ONE : RustM Self
  square : Self → RustM Self
  from_bool : Bool → RustM Self
  zero_vec : Std.Usize → RustM (alloc.vec.Vec Self)
  from_u8 : Std.U8 → RustM Self
  from_u16 : Std.U16 → RustM Self
  coreitertraitsaccumProductInst : core.iter.traits.accum.Product Self Self

/-- The algebra trait, restricted to the members the extraction uses.

Upstream: field/src/field.rs:711. -/
structure field.Algebra (Self F : Type) where
  PrimeCharacteristicRingInst : field.PrimeCharacteristicRing Self
  coreopsarithAddInst : core.ops.arith.Add Self F Self
  coreopsarithSubInst : core.ops.arith.Sub Self F Self
  coreopsarithAddAssignInst : core.ops.arith.AddAssign Self F
  coreopsarithMulInst : core.ops.arith.Mul Self F Self
  coreopsarithMulAssignInst : core.ops.arith.MulAssign Self F

/-- The quotient map trait, restricted to the member the extraction uses.

Upstream: field/src/integers.rs. -/
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
        ONE := fail .panic
        NEG_ONE := fail .panic
        square := fun _ => fail .panic
        from_bool := fun _ => fail .panic
        zero_vec := fun _ => fail .panic
        from_u8 := fun _ => fail .panic
        from_u16 := fun _ => fail .panic
        coreitertraitsaccumProductInst := ⟨fun _ _ => fail .panic⟩ }
     coreopsarithAddInst := ⟨fun _ _ => fail .panic⟩
     coreopsarithSubInst := ⟨fun _ _ => fail .panic⟩
     coreopsarithAddAssignInst := ⟨fun _ _ => fail .panic⟩
     coreopsarithMulInst := ⟨fun _ _ => fail .panic⟩
     coreopsarithMulAssignInst := ⟨fun _ _ => fail .panic⟩ }⟩

/-- The copy witness of a field whose model does not give one.

Assumed: no model that builds a field instance projects it. -/
opaque field.Field.unmodelledCopy (Self : Type) : core.marker.Copy Self :=
  ⟨⟨fun x => ok x, fun _ x => ok x⟩⟩

/-- The witness that a field is an algebra over itself, for a model that does not give one.

Assumed: no model that builds a field instance projects it. -/
opaque field.Field.unmodelledAlgebra (Self : Type) : field.Algebra Self Self

/-- The bit count of a field whose model does not give it.

Assumed: no model that builds a field instance projects it. -/
opaque field.Field.unmodelledBits (Self : Type) : RustM Std.Usize := fail .panic

/-- The field trait, restricted to the members the extraction uses.

Upstream: field/src/field.rs:1059.

A model that only passes instances through, as p3-monty-31's, builds one with empty braces.

That leaves every member assumed. -/
structure field.Field (Self : Type) where
  coremarkerCopyInst : core.marker.Copy Self := field.Field.unmodelledCopy Self
  AlgebraInst : field.Algebra Self Self := field.Field.unmodelledAlgebra Self
  bits : RustM Std.Usize := field.Field.unmodelledBits Self

instance {Self : Type} : Inhabited (field.Field Self) := ⟨{}⟩

/-- The field's algebra over itself, under the name aeneas gives it in code that also names the extension field trait. -/
abbrev field.Field.AlgebraSelfSelfSelf_Clause0_Clause0_PrimeSubfieldInst {Self : Type}
    (inst : field.Field Self) : field.Algebra Self Self :=
  inst.AlgebraInst

/-- The extension field trait, restricted to the members the extraction uses.

Upstream: field/src/field.rs:1336.

It names two rings on the extension: the field's own, and the algebra's over the base. -/
structure field.ExtensionField (Self Base : Type) where
  FieldInst : field.Field Self
  AlgebraSelfBaseSelf_Clause1_Clause0_PrimeSubfieldInst : field.Algebra Self Base

instance {Self : Type} : Inhabited (integers.QuotientMap Self Std.U64) :=
  ⟨⟨fun _ => fail .panic⟩⟩

/-- The field supertrait witness of a prime field whose model does not give one.

Assumed: no model that builds a prime field instance projects it. -/
opaque field.PrimeField.unmodelledField (Self : Type) : field.Field Self

/-- The quotient map witness from 64-bit integers, for a prime field whose model does not give one.

Assumed: no model that builds a prime field instance projects it. -/
opaque field.PrimeField.unmodelledQuotientMapU64 (Self : Type) : integers.QuotientMap Self Std.U64

/-- The prime field trait, restricted to the members the extraction uses.

Upstream: field/src/field.rs:1264.

A model that only passes instances through builds one with empty braces, as for the field trait. -/
structure field.PrimeField (Self : Type) where
  FieldInst : field.Field Self := field.PrimeField.unmodelledField Self
  integersQuotientMapSelfU64Inst : integers.QuotientMap Self Std.U64 :=
    field.PrimeField.unmodelledQuotientMapU64 Self

/-- The 64-bit prime field trait, restricted to the members the extraction uses.

Upstream: field/src/field.rs:1267. -/
structure field.PrimeField64 (Self : Type) where
  PrimeFieldInst : field.PrimeField Self
  ORDER_U64 : RustM Std.U64
  as_canonical_u64 : Self → RustM Std.U64
  to_unique_u64 : Self → RustM Std.U64

/-- The 32-bit prime field trait, restricted to the members the extraction uses.

Upstream: field/src/field.rs:1289. -/
structure field.PrimeField32 (Self : Type) where
  PrimeField64Inst : field.PrimeField64 Self
  ORDER_U32 : RustM Std.U32
  as_canonical_u32 : Self → RustM Std.U32
  to_unique_u32 : Self → RustM Std.U32

/-- The trait of a vector space with a basis, restricted to the members the extraction uses.

Upstream: field/src/field.rs:445. -/
structure field.BasedVectorSpace (Self F : Type) where
  PrimeCharacteristicRingInst : field.PrimeCharacteristicRing F
  from_basis_coefficients_fn : forall {Fn : Type}, core.ops.function.FnMut Fn Std.Usize F →
    Fn → RustM (Self × Fn)

/-- Every ring as a vector space over itself (field/src/field.rs:630).

Its only basis coefficient is the element itself, so the closure runs once, at index 0. -/
@[reducible]
def field.BasedVectorSpace.Blanket {F : Type} (inst : field.PrimeCharacteristicRing F) :
    field.BasedVectorSpace F F := {
  PrimeCharacteristicRingInst := inst
  from_basis_coefficients_fn := fun FnMutInst c => FnMutInst.call_mut c 0#usize
}

/-- The uniform sampling trait (field/src/field.rs:613).

It is complete: the trait has exactly these two associated constants. -/
structure field.UniformSamplingField (Self : Type) where
  MAX_SINGLE_SAMPLE_BITS : RustM Std.Usize
  SAMPLING_BITS_M : RustM (Array Std.U64 64#usize)

/-- The power val^1420470955, by an addition chain.

Upstream: field/src/exponentiation.rs:37.

Assumed: its body is a chain of squarings and products, and those ring methods are not modelled here. -/
opaque exponentiation.exp_1420470955 {R : Type}
    (PrimeCharacteristicRingInst : field.PrimeCharacteristicRing R) (val : R) :
    RustM R

/-- The power val^1725656503, by an addition chain.

Upstream: field/src/exponentiation.rs:62.

Assumed: its body is a chain of squarings and products, and those ring methods are not modelled here. -/
opaque exponentiation.exp_1725656503 {R : Type}
    (PrimeCharacteristicRingInst : field.PrimeCharacteristicRing R) (val : R) :
    RustM R

/-- Halve x in F_P, for x < P (field/src/helpers.rs:113).

Upstream computes it as follows:

```text
shift = (P + 1) >> 1
half  = x >> 1
x even:  half
x odd:   half + shift
```

It is transcribed as aeneas renders it.

Each addition is checked, and the odd-case addition happens only in that branch. -/
def helpers.halve_u32 (P : Std.U32) (x : Std.U32) : RustM Std.U32 := do
  let i ← P + 1#u32
  let shift ← i >>> 1#i32
  let half ← x >>> 1#i32
  let i1 ← lift (x &&& 1#u32)
  if i1 = 0#u32 then ok half else half + shift

end p3_field
