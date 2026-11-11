/-
The tower-level trait of p3-binary-field, as the Lean structure aeneas would emit for it.

aeneas emits only the crate it runs on, and this scoped extraction does not reach the trait.

Code generic over a tower level, in the crates above, projects these members.

Instances are passed in as parameters.

So a proof about such code holds for every implementation.
-/
module

public import Aeneas
public import CoreModels
public import P3Field

@[expose] public section
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc

namespace p3_binary_field

/-- The tower-level trait, restricted to the members the extractions use.

Upstream: binary-field/src/tower.rs:52.

The associated type of the backing integer is the second parameter, as aeneas writes it. -/
structure tower.TowerLevel (Self Repr : Type) where
  LOG_BITS : RustM Std.Usize
  p3_fieldfieldFieldInst : p3_field.field.Field Self
  cantor_basis : Std.Usize → RustM Self

end p3_binary_field
