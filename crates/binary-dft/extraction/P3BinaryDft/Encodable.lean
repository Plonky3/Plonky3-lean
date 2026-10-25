/-
The encodable-level trait of p3-binary-dft, as the Lean structure aeneas would emit for it.

aeneas emits only the crate it runs on, and this scoped extraction does not reach the trait.

Instances are passed in as parameters, so a proof about code generic over it holds for every implementation.
-/
module

public import Aeneas
public import CoreModels
public import P3BinaryField

@[expose] public section
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc

namespace p3_binary_dft

/-- A tower level with the encoder this crate uses for it, restricted to the members the extractions use.

Upstream: binary-dft/src/encoder.rs:41.

The encoder and the backing integer are parameters, as aeneas writes associated types. -/
structure encoder.EncodableLevel (Self Encoder Repr : Type) where
  p3_binary_fieldtowerTowerLevelInst : p3_binary_field.tower.TowerLevel Self Repr

end p3_binary_dft
