module

public import P3MultilinearUtil
public import Plonky3Lean.Lib.Yields
public import Plonky3Lean.Proofs.MultilinearUtil.PointForms

@[expose] public section

/-!
# The extracted equality polynomial

hax extracts the equality polynomial of two points, generic over the field traits.

Its theorems assume one thing of the two instances: each member it calls computes the operation it names.

Under that assumption it returns what its transcription computes.

It panics exactly when the transcription does.

So every theorem about the transcription holds for the shipped code.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open Plonky3Lean.Lib

namespace Plonky3Lean.Proofs.MultilinearUtil

variable {F EF : Type} [Field F] [Field EF] [Algebra F EF]

/-- The members of the two instances that the equality polynomial calls compute:

- one, in the base field;
- doubling, in the extension;
- the product, sum and difference of an extension element and a base element;
- the difference of two extension elements;
- the product of everything an iterator yields. -/
structure ExtComputes (inst : p3_field.field.Field F) (einst : p3_field.field.ExtensionField EF F) :
    Prop where
  one : inst.AlgebraInst.PrimeCharacteristicRingInst.ONE = .ok 1
  double : ∀ a : EF,
    einst.AlgebraSelfBaseSelf_Clause1_Clause0_PrimeSubfieldInst.PrimeCharacteristicRingInst.double a =
      .ok (a + a)
  mul : ∀ (a : EF) (b : F),
    einst.AlgebraSelfBaseSelf_Clause1_Clause0_PrimeSubfieldInst.coreopsarithMulInst.mul a b =
      .ok (a * algebraMap F EF b)
  add : ∀ (a : EF) (b : F),
    einst.AlgebraSelfBaseSelf_Clause1_Clause0_PrimeSubfieldInst.coreopsarithAddInst.add a b =
      .ok (a + algebraMap F EF b)
  sub_base : ∀ (a : EF) (b : F),
    einst.AlgebraSelfBaseSelf_Clause1_Clause0_PrimeSubfieldInst.coreopsarithSubInst.sub a b =
      .ok (a - algebraMap F EF b)
  sub : ∀ a b : EF, einst.FieldInst.AlgebraInst.coreopsarithSubInst.sub a b = .ok (a - b)
  product : ∀ {I : Type} (it : core.iter.traits.iterator.Iterator I EF) (s : I) (l : List EF),
    Yields it s l →
      einst.AlgebraSelfBaseSelf_Clause1_Clause0_PrimeSubfieldInst.PrimeCharacteristicRingInst.coreitertraitsaccumProductInst.product
        it s = .ok l.prod

/-- A transcription's result in the monad: none is a panic. -/
def ofOption {α : Type} : Option α → RustM α
  | some a => .ok a
  | none => .fail .panic

variable {inst : p3_field.field.Field F} {einst : p3_field.field.ExtensionField EF F}

/-- The extracted equality polynomial returns what its transcription computes. -/
theorem eval_eq_eq_mirror (h : ExtComputes inst einst) (p : Slice F) (q : Slice EF) :
    p3_multilinear_util.hax_roots.eval_eq inst einst p q =
      ofOption (p3_multilinear_util.point.mirror.Point.eval_eq p.val q.val) := by
  unfold p3_multilinear_util.hax_roots.eval_eq p3_multilinear_util.point.PointFVec.eval_eq
  simp only [core.slice.Slice.len, core.slice.Slice.iter, rust_primitives.sequence.seq_from_slice,
    core.iter.traits.iterator.Iterator.zip.default, core.iter.traits.iterator.Iterator.map.default,
    core.SharedASlice.Insts.CoreIterTraitsCollectIntoIteratorSharedATIter.into_iter,
    core.iter.adapters.zip.Zip.new, core.iter.adapters.map.Map.new,
    core.iter.traits.iterator.Iterator.product.default, rust_primitives.slice.slice_length]
  by_cases hl : p.val.length = q.val.length
  · have hlen : Slice.len p = Slice.len q := UScalar.eq_of_val_eq (by simpa using hl)
    have hc : ∀ (c : p3_multilinear_util.point.PointFVec.eval_eq.closure inst einst) (x : F × EF),
        (p3_multilinear_util.point.PointFVec.eval_eq.closure.Insts.CoreOpsFunctionFnMutTuplePairShared0FShared1EFEF
          inst einst).call_mut c x =
          .ok ((x.2 + x.2) * algebraMap F EF x.1 - algebraMap F EF x.1 - x.2 + 1, c) := by
      rintro c ⟨l, r⟩
      simp [p3_multilinear_util.point.PointFVec.eval_eq.closure.Insts.CoreOpsFunctionFnMutTuplePairShared0FShared1EFEF.call_mut,
        h.one, h.double, h.mul, h.add, h.sub_base, h.sub]
    simp only [hlen, Std.bind_ok, ↓reduceIte]
    repeat erw [Std.bind_ok]
    refine (h.product _ _ _ (yields_map _ () _ (hc ())
      (yields_zip (yields_slice _ p rfl) (yields_slice _ q rfl)))).trans ?_
    simp [ofOption, p3_multilinear_util.point.mirror.Point.eval_eq, hl, foldl_mul_one,
      ← List.map_uncurry_zip_eq_zipWith, Function.uncurry_def]
  · have hlen : Slice.len p ≠ Slice.len q := fun e => hl (by simpa using congrArg UScalar.val e)
    simp [hlen, ofOption, p3_multilinear_util.point.mirror.Point.eval_eq, hl,
      core.fmt.Arguments.from_str]

end Plonky3Lean.Proofs.MultilinearUtil
