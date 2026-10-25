/-
The type layout the transforms read: the size in bytes of one element.

The transforms compare a buffer's byte size with a cache budget to pick a schedule.

Every schedule computes the same transform, so no claim depends on the size.
-/
module

public import Aeneas
public import CoreModels

@[expose] public section
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc

/-- The size in bytes of a type.

Assumed: the model does not compute type layouts, and no claim depends on the value. -/
opaque core.mem.size_of (T : Type _) : RustM Std.Usize := .ok 1#usize

/-- The size in bytes of a slice: its length times the element size.

A slice fits in memory, so the product never exceeds a word in Rust. -/
def core.mem.size_of_val {T : Type _} (s : Slice T) : RustM Std.Usize := do
  let n ← core.mem.size_of T
  .ok ⟨BitVec.ofNat _ (s.length * n.val)⟩
