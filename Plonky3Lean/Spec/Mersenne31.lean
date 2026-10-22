module

public import CompPoly.Fields.Mersenne31
public import P3Mersenne31
public import ToCompPoly.Fields.Mersenne.Extension

@[expose] public section

/-!
# Mersenne31: what the model's values mean

A Rust `Mersenne31` is a `u32` that holds the element itself, not a Montgomery form.

* **The invariant.** The stored value fits in 31 bits, `value < 2^31`, as the field's doc comment requires (`mersenne-31/src/mersenne_31.rs:37`).

  So `value` is in `[0, p]` for `p = 2^31 - 1`, and zero has two representations, `0` and `p`.

  `Valid` is this invariant, and nothing more.

* **An element.** `toField` reads the stored value in CompPoly's `Mersenne31.Field` (`ZMod p`), where `p` and `0` are both zero.

  `Canonical` says the stored value is in `[0, p)`, the stricter form that `as_canonical_u32` returns.

* **A complex element.** `Complex<Mersenne31>` stores `[real, imag]`.

  `toComplex` reads it as `real + imag · i` in `F[i]`.

* **A cubic element.** `[Mersenne31; 3]` stores the coefficients of `1, X, X^2`.

  `toCubic` reads it in `F[X] / (X^3 - 5)`.

* **A QM31 element.** `[Complex<Mersenne31>; 2]` stores `c_0 + c_1 · u`, with `u^2 = 2 + i`.

  `toQM31` reads it in `F[i][Y] / (Y^2 - (2 + i))`.
-/

open Aeneas Aeneas.Std CoreModels
open p3_mersenne_31

namespace Plonky3Lean.Spec.Mersenne31

/-- A Mersenne31 field element as the model has it: Rust's `Mersenne31`, one `u32`. -/
abbrev Element := mersenne_31.Mersenne31

/-- The representation invariant: the stored value fits in 31 bits. -/
def Valid (x : Element) : Prop :=
  x.value.val < 2 ^ 31

/-- The stored value is fully reduced, in `[0, p)`. -/
def Canonical (x : Element) : Prop :=
  x.value.val < Mersenne31.fieldSize

/-- The field element a stored value stands for. -/
def toField (x : Element) : Mersenne31.Field :=
  (x.value.val : Mersenne31.Field)

open Polynomial in
/-- The element of `F[X] / (X^3 - 5)` that three coefficients stand for. -/
noncomputable def toCubic (c : Array Element 3#usize) : AdjoinRoot (X ^ 3 - C (5 : Mersenne31.Field)) :=
  AdjoinRoot.mk _ (CoeffList.toPoly (c.val.map toField))

/-- The element `real + imag · i` of `F[i]` that `[real, imag]` stands for. -/
noncomputable def toComplex (c : Array Element 2#usize) : Mersenne31.Complex :=
  Mersenne31.Complex.mk (toField (c.val.getD 0 ⟨0#u32⟩)) (toField (c.val.getD 1 ⟨0#u32⟩))

/-- The element `c_0 + c_1 · u` of QM31 that `[c_0, c_1]` stands for. -/
noncomputable def toQM31 (c : Array (Array Element 2#usize) 2#usize) : Mersenne31.QM31 :=
  AdjoinRoot.of _ (toComplex (c.val.getD 0 (Array.repeat 2#usize ⟨0#u32⟩))) +
    AdjoinRoot.of _ (toComplex (c.val.getD 1 (Array.repeat 2#usize ⟨0#u32⟩))) * AdjoinRoot.root _

end Plonky3Lean.Spec.Mersenne31
