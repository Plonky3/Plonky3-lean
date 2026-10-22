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

end CoreModels
