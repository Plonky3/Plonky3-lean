module

public import Plonky3Lean.Proofs.WordBackend.Columns
public import Plonky3Lean.Proofs.WordBackend.LiftSound
public import Plonky3Lean.Proofs.Word.Models

@[expose] public section

/-!
# The backend's relation checks are the scalar verifier

The backend checks each relation on its packed columns, one row and one bit at a time:

```text
    zero      value(row, bit) = 0
    AND       left(row, bit) * right(row, bit) = output(row, bit)
    product   factor lift(row) = result lift(row),  and  a(row, 0) * b(row, 0) = lo(row, 0)
```

On a flat system whose addresses are in range, those checks accept exactly when the scalar verifier does.
-/

open Aeneas Aeneas.Std CoreModels p3_word Plonky3Lean.Proofs.Word
open p3_word_backend.columns.mirror p3_word_backend.integer_mul.mirror

set_option linter.unusedSectionVars false

namespace Plonky3Lean.Proofs.WordBackend

variable {W : Type}

/-- The AND rows of the columns: left, right and output side by side. -/
def andRows (c : OperationColumns W) : List (W × W × W) :=
  c.and_left.zip (c.and_right.zip c.and_output)

/-- The product rows of the columns: both factors and both limbs side by side. -/
def mulRows (c : OperationColumns W) : List (W × W × W × W) :=
  c.mul_left.zip (c.mul_right.zip (c.mul_low.zip c.mul_high))

/-- The columns pass the three row checks. -/
def Accepts (zeroOK : W → Prop) (andOK : W → W → W → Prop) (mulOK : W → W → W → W → Prop)
    (c : OperationColumns W) : Prop :=
  (∀ v ∈ c.zero, zeroOK v) ∧ (∀ r ∈ andRows c, andOK r.1 r.2.1 r.2.2) ∧
    (∀ r ∈ mulRows c, mulOK r.1 r.2.1 r.2.2.1 r.2.2.2)

variable [DecidableEq W] {inst : word.Word W} (M : Model inst)

theorem opVal_eq_val {sys : system.ConstraintSystem W} {pub wit : Slice W}
    (hp : pub.len = UScalar.cast .Usize sys.public_len)
    (hw : wit.len = UScalar.cast .Usize sys.witness_len)
    {op : constraint.Operand W} (h : opIn sys op) : opVal M pub wit op = some (val M pub wit op) := by
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 (opVal_isSome M hp hw h)
  simp [val, hv]

/-- On scalar columns, the word-level row checks accept exactly when the scalar verifier does. -/
theorem accepts_iff (sys : system.ConstraintSystem W) (pub wit : Slice W)
    (hp : pub.len = UScalar.cast .Usize sys.public_len)
    (hw : wit.len = UScalar.cast .Usize sys.witness_len) (hin : validateSpec sys = .Ok ()) :
    Accepts (· = M.zero) (fun l r o => M.andf l r = o) (fun a b lo hi => M.mulf a b = (lo, hi))
        (colsOf M sys pub wit) ↔
      verifySpec M sys pub wit = .Ok () := by
  obtain ⟨hz, ha, hm⟩ := (validateSpec_ok sys).1 hin
  have e := fun {op : constraint.Operand W} (i : opIn sys op) => opVal_eq_val M hp hw i
  rw [verifySpec_ok]
  simp only [Accepts, andRows, mulRows, colsOf, List.zip_map', List.mem_map, forall_exists_index,
    and_imp, forall_apply_eq_imp_iff₂, hp, hw, true_and]
  refine and_congr ?_ (and_congr ?_ ?_)
  · exact forall₂_congr fun c hc => by rw [e (hz c hc)]; simp
  · refine forall₂_congr fun c hc => ?_
    obtain ⟨i1, i2, i3⟩ := ha c hc
    simp [andHolds, e i1, e i2, e i3]
  · refine forall₂_congr fun c hc => ?_
    obtain ⟨i1, i2, i3, i4⟩ := hm c hc
    simp [mulHolds, e i1, e i2, e i3, e i4]

/-! ## The bit-level checks, at 32 and at 64 bits -/

theorem zero32_iff (v : word.Word32) : v = M32.zero ↔ ∀ i < 32, v.bv.getLsbD i = false := by
  constructor
  · rintro rfl i _; show (0 : BitVec 32).getLsbD i = false; simp
  · intro h
    apply UScalar.eq_of_val_eq
    show v.bv.toNat = (0 : BitVec 32).toNat
    congr 1
    ext i hi
    simpa [BitVec.getLsbD_eq_getElem hi] using h i hi

theorem zero64_iff (v : word.Word64) : v = M64.zero ↔ ∀ i < 64, v.bv.getLsbD i = false := by
  constructor
  · rintro rfl i _; show (0 : BitVec 64).getLsbD i = false; simp
  · intro h
    apply UScalar.eq_of_val_eq
    show v.bv.toNat = (0 : BitVec 64).toNat
    congr 1
    ext i hi
    simpa [BitVec.getLsbD_eq_getElem hi] using h i hi

theorem and32_iff (l r o : word.Word32) :
    M32.andf l r = o ↔ ∀ i < 32, (l.bv.getLsbD i && r.bv.getLsbD i) = o.bv.getLsbD i := by
  show (⟨l.bv &&& r.bv⟩ : word.Word32) = o ↔ _
  constructor
  · rintro rfl i _; simp
  · intro h
    obtain ⟨o⟩ := o
    congr 1
    ext i hi
    simpa [BitVec.getLsbD_eq_getElem hi] using h i hi

theorem and64_iff (l r o : word.Word64) :
    M64.andf l r = o ↔ ∀ i < 64, (l.bv.getLsbD i && r.bv.getLsbD i) = o.bv.getLsbD i := by
  show (⟨l.bv &&& r.bv⟩ : word.Word64) = o ↔ _
  constructor
  · rintro rfl i _; simp
  · intro h
    obtain ⟨o⟩ := o
    congr 1
    ext i hi
    simpa [BitVec.getLsbD_eq_getElem hi] using h i hi

variable {F : Type _} [Field F]

/-- The product check of one row: the two lifts agree and so do the low bits. -/
def LiftOK (g : F) (w : ℕ) (a b lo hi : ℕ) : Prop :=
  (factor_leaves [a] [b] w (generator_squarings g (2 * w))).prod =
      (result_leaves [lo] [hi] w (generator_squarings g (2 * w))).prod ∧
    a % 2 * (b % 2) = lo % 2

theorem mul32_lift_iff {n : ℕ} (g : F) (hg : orderOf g = 2 ^ n - 1)
    (hcheck : check_field (2 ^ n) 32 = .ok ()) (a b lo hi : word.Word32) :
    M32.mulf a b = (lo, hi) ↔ LiftOK g 32 a.val b.val lo.val hi.val := by
  show mul32 a b = (lo, hi) ↔ _
  rw [mul32_iff, LiftOK, row_sound g hg hcheck (by norm_num) a.hBounds b.hBounds lo.hBounds
    hi.hBounds]

theorem mul64_lift_iff {n : ℕ} (g : F) (hg : orderOf g = 2 ^ n - 1)
    (hcheck : check_field (2 ^ n) 64 = .ok ()) (a b lo hi : word.Word64) :
    M64.mulf a b = (lo, hi) ↔ LiftOK g 64 a.val b.val lo.val hi.val := by
  show mul64 a b = (lo, hi) ↔ _
  rw [mul64_iff, LiftOK, row_sound g hg hcheck (by norm_num) a.hBounds b.hBounds lo.hBounds
    hi.hBounds]

omit [DecidableEq W] in
theorem accepts_congr {z z' : W → Prop} {a a' : W → W → W → Prop} {m m' : W → W → W → W → Prop}
    (hz : ∀ v, z v ↔ z' v) (ha : ∀ l r o, a l r o ↔ a' l r o)
    (hm : ∀ x y lo hi, m x y lo hi ↔ m' x y lo hi) (c : OperationColumns W) :
    Accepts z a m c ↔ Accepts z' a' m' c := by
  simp only [Accepts, hz, ha, hm]

/-- At 32 bits, the columns are built without panicking.

The backend's bit-level checks on them accept exactly when the scalar verifier does. -/
theorem backend32 {n : ℕ} (sys : system.ConstraintSystem word.Word32) (pub wit : Slice word.Word32)
    (hv : SysValid M32 sys) (hp : pub.len = UScalar.cast .Usize sys.public_len)
    (hw : wit.len = UScalar.cast .Usize sys.witness_len) (hin : validateSpec sys = .Ok ())
    (g : F) (hg : orderOf g = 2 ^ n - 1) (hcheck : check_field (2 ^ n) 32 = .ok ()) :
    ∃ cols, OperationColumns.new I32w packedAdd32 (.Flat sys) pub.val wit.val = .ok (.ok cols) ∧
      (Accepts (fun v => ∀ i < 32, v.bv.getLsbD i = false)
          (fun l r o => ∀ i < 32, (l.bv.getLsbD i && r.bv.getLsbD i) = o.bv.getLsbD i)
          (fun a b lo hi => LiftOK g 32 a.val b.val lo.val hi.val) cols ↔
        verifySpec M32 sys pub wit = .Ok ()) :=
  ⟨_, columns_flat M32 sys pub wit hv hp hw hin,
    (accepts_congr (fun v => (zero32_iff v).symm) (fun l r o => (and32_iff l r o).symm)
      (fun a b lo hi => (mul32_lift_iff g hg hcheck a b lo hi).symm) _).trans
      (accepts_iff M32 sys pub wit hp hw hin)⟩

/-- At 64 bits, the columns are built without panicking.

The backend's bit-level checks on them accept exactly when the scalar verifier does. -/
theorem backend64 {n : ℕ} (sys : system.ConstraintSystem word.Word64) (pub wit : Slice word.Word64)
    (hv : SysValid M64 sys) (hp : pub.len = UScalar.cast .Usize sys.public_len)
    (hw : wit.len = UScalar.cast .Usize sys.witness_len) (hin : validateSpec sys = .Ok ())
    (g : F) (hg : orderOf g = 2 ^ n - 1) (hcheck : check_field (2 ^ n) 64 = .ok ()) :
    ∃ cols, OperationColumns.new I64w packedAdd64 (.Flat sys) pub.val wit.val = .ok (.ok cols) ∧
      (Accepts (fun v => ∀ i < 64, v.bv.getLsbD i = false)
          (fun l r o => ∀ i < 64, (l.bv.getLsbD i && r.bv.getLsbD i) = o.bv.getLsbD i)
          (fun a b lo hi => LiftOK g 64 a.val b.val lo.val hi.val) cols ↔
        verifySpec M64 sys pub wit = .Ok ()) :=
  ⟨_, columns_flat M64 sys pub wit hv hp hw hin,
    (accepts_congr (fun v => (zero64_iff v).symm) (fun l r o => (and64_iff l r o).symm)
      (fun a b lo hi => (mul64_lift_iff g hg hcheck a b lo hi).symm) _).trans
      (accepts_iff M64 sys pub wit hp hw hin)⟩

end Plonky3Lean.Proofs.WordBackend
