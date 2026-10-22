import Aeneas
import CoreModels

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

/-- `Ord::min`, the provided method (`library/core/src/cmp.rs`), which returns
`other` exactly when `other < self`. It is `core::cmp::min(self, other)`, whose
model is reused. Referenced by p3-mersenne-31's `reduce_64`. -/
def core.cmp.Ord.min.default {Self : Type} (OrdInst : core.cmp.Ord Self)
    (self other : Self) : RustM Self :=
  core.cmp.min OrdInst self other

/-- `bool::then` (`library/core/src/bool.rs`):
`if self { Some(f()) } else { None }`. -/
def core.bool.Bool.then {T F : Type} (FnOnceInst : core.ops.function.FnOnce F Unit T)
    (self : Bool) (f : F) : RustM (core.option.Option T) :=
  if self then do
    let x ← FnOnceInst.call_once f ()
    ok (core.option.Option.Some x)
  else ok core.option.Option.None

/-- `u32::wrapping_add_signed` (`library/core/src/num/uint_macros.rs`):
`self.wrapping_add(rhs as Self)`. -/
def core.num.U32.wrapping_add_signed (x : Std.U32) (y : Std.I32) : RustM Std.U32 := do
  let y' ← lift (IScalar.hcast .U32 y)
  core.num.U32.wrapping_add x y'

/-- `i64::unsigned_abs` (`library/core/src/num/int_macros.rs`):
`self.wrapping_abs() as u64`, the magnitude, which fits in `u64` even for `i64::MIN`. -/
def core.num.I64.unsigned_abs (x : Std.I64) : RustM Std.U64 :=
  ok ⟨BitVec.ofNat _ x.val.natAbs⟩

/-- `i128::unsigned_abs`, as for `i64`. -/
def core.num.I128.unsigned_abs (x : Std.I128) : RustM Std.U128 :=
  ok ⟨BitVec.ofNat _ x.val.natAbs⟩

end CoreModels
