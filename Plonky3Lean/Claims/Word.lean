module

public import Plonky3Lean.Proofs.Word.Validate

@[expose] public section

/-!
# p3-word: claims

What this repository asserts about word gadgets, at the Plonky3 commit pinned in `plonky3/`.

The model is the scoped extraction in `crates/word`.
The system and composition loops take the reshaped bodies of pre-patches `word/020` and `word/030`.
Differential tests equate them with the shipped ones.

Words are 32 or 64 bits wide.
The word trait is sealed, so no other width exists.

A term is a word read at an address, then transformed by at most two shifts.
-/

open Aeneas Aeneas.Std CoreModels p3_word
open Plonky3Lean.Proofs.Word

namespace Plonky3Lean.Claims.P3Word

/-- A 32-bit shift panics exactly on the amounts the specification marks.

Otherwise it computes its bit-vector meaning. -/
theorem Shift.apply.word32 (s : shift.Shift word.Word32) (x : word.Word32) :
    shift.Shift.apply I32w s x =
      if panics32 s.kind s.amount.val then RustM.fail .panic
      else RustM.ok ⟨sem32 s.kind s.amount.val x.bv⟩ :=
  apply32_eq s x

/-- A 64-bit shift panics exactly on the amounts the specification marks.

Otherwise it computes its bit-vector meaning. -/
theorem Shift.apply.word64 (s : shift.Shift word.Word64) (x : word.Word64) :
    shift.Shift.apply I64w s x =
      if panics64 s.kind s.amount.val then RustM.fail .panic
      else RustM.ok ⟨sem64 s.kind s.amount.val x.bv⟩ :=
  apply64_eq s x

/-- The 32-bit shift constructor refuses lane shifts and amounts of 32 or more, and normalises a zero amount. -/
theorem Shift.new.word32 (k : shift.ShiftKind) (amt : Std.Usize) :
    shift.Shift.new I32w k amt = RustM.ok
      (if isLane k then .Err .Lane32RequiresWord64
       else if 32 ≤ amt.val then .Err (.AmountOutOfRange amt 32#u32)
       else .Ok ⟨if amt.val = 0 then .LogicalLeft else k, UScalar.cast .U8 amt, ()⟩) :=
  new32_eq k amt

/-- The 64-bit shift constructor refuses amounts at or above the operation width, and normalises a zero amount. -/
theorem Shift.new.word64 (k : shift.ShiftKind) (amt : Std.Usize) :
    shift.Shift.new I64w k amt = RustM.ok
      (if opWidth 64 k ≤ amt.val then
         .Err (.AmountOutOfRange amt (if isLane k then 32#u32 else 64#u32))
       else .Ok ⟨if amt.val = 0 then .LogicalLeft else k, UScalar.cast .U8 amt, ()⟩) :=
  new64_eq k amt

/-- A 32-bit shift the constructor accepted never panics, and computes the requested operation. -/
theorem Shift.apply.of_new32 {k : shift.ShiftKind} {amt : Std.Usize} {s : shift.Shift word.Word32}
    (h : shift.Shift.new I32w k amt = RustM.ok (.Ok s)) (x : word.Word32) :
    shift.Shift.apply I32w s x = RustM.ok ⟨sem32 k amt.val x.bv⟩ :=
  apply32_of_new h x

/-- A 64-bit shift the constructor accepted never panics, and computes the requested operation. -/
theorem Shift.apply.of_new64 {k : shift.ShiftKind} {amt : Std.Usize} {s : shift.Shift word.Word64}
    (h : shift.Shift.new I64w k amt = RustM.ok (.Ok s)) (x : word.Word64) :
    shift.Shift.apply I64w s x = RustM.ok ⟨sem64 k amt.val x.bv⟩ :=
  apply64_of_new h x

/-- On a system whose terms never panic, the verifier returns its specification. -/
theorem ConstraintSystem.verify.eq {W : Type} [DecidableEq W] {inst : word.Word W} (M : Model inst)
    (sys : system.ConstraintSystem W) (pub wit : Slice W) (hv : SysValid M sys) :
    system.ConstraintSystem.verify inst sys pub wit = .ok (verifySpec M sys pub wit) :=
  verify_eq M sys pub wit hv

/-- The verifier's specification accepts exactly when two conditions hold.

- Both segments have their declared lengths.
- Every relation holds.

The relations mean the following.

- A zero relation holds when its operand denotes the zero word.
- An AND relation holds when the output is the bitwise AND of the two inputs.
- A product relation holds when the two limbs are the full product of the two inputs. -/
theorem verifySpec.ok_iff {W : Type} [DecidableEq W] {inst : word.Word W} (M : Model inst)
    (sys : system.ConstraintSystem W) (pub wit : Slice W) :
    verifySpec M sys pub wit = .Ok () ↔
      pub.len = UScalar.cast .Usize sys.public_len ∧
      wit.len = UScalar.cast .Usize sys.witness_len ∧
      (∀ c ∈ (vecSlice sys.zero_constraints).val, opVal M pub wit c.value = some M.zero) ∧
      (∀ c ∈ (vecSlice sys.and_constraints).val, andHolds M pub wit c = true) ∧
      (∀ c ∈ (vecSlice sys.integer_mul_constraints).val, mulHolds M pub wit c = true) :=
  verifySpec_ok M sys pub wit

/-- The 32-bit product model returns limbs $(lo, hi)$ exactly when $a b = lo + 2^{32} hi$. -/
theorem mul32.iff (a b lo hi : word.Word32) :
    mul32 a b = (lo, hi) ↔ a.val * b.val = lo.val + 2 ^ 32 * hi.val :=
  mul32_iff a b lo hi

/-- The 64-bit product model returns limbs $(lo, hi)$ exactly when $a b = lo + 2^{64} hi$. -/
theorem mul64.iff (a b lo hi : word.Word64) :
    mul64 a b = (lo, hi) ↔ a.val * b.val = lo.val + 2 ^ 64 * hi.val :=
  mul64_iff a b lo hi

/-- An address constructor accepts exactly the positions below $2^{32}$. -/
theorem ValueIndex.new.eq (seg : index.Segment) (pos : Std.Usize) :
    index.ValueIndex.new seg pos =
      .ok (if pos.val < 2 ^ 32 then .Ok ⟨seg, UScalar.cast .U32 pos⟩
        else .Err (.PositionTooLarge pos)) :=
  value_index_new_eq seg pos

/-- Decoding the code of a shift kind returns that kind. -/
theorem ShiftKind.code.round_trip (k : shift.ShiftKind) :
    (do let c ← shift.ShiftKind.code k; shift.ShiftKind.from_code c) = .ok (.Some k) :=
  shift_code_round_trip k

/-- Codes of 8 or more decode to no shift kind. -/
theorem ShiftKind.from_code.none (c : Std.U8) (h : 8 ≤ c.val) :
    shift.ShiftKind.from_code c = .ok .None :=
  shift_from_code_none c h

/-- The system constructor bounds the segments, then the families, then validates every address. -/
theorem ConstraintSystem.new.eq {W : Type} (inst : word.Word W) (pl wl : Std.Usize)
    (z : CoreModels.alloc.vec.Vec (constraint.ZeroConstraint W))
    (a : CoreModels.alloc.vec.Vec (constraint.AndConstraint W))
    (m : CoreModels.alloc.vec.Vec (constraint.IntegerMulConstraint W)) :
    system.ConstraintSystem.new inst pl wl z a m = .ok (newSpec pl wl z a m) :=
  system_new_eq inst pl wl z a m

/-- The system constructor succeeds exactly on bounded segments and families whose addresses validate. -/
theorem ConstraintSystem.new.ok_iff {W : Type} (inst : word.Word W) (pl wl : Std.Usize)
    (z : CoreModels.alloc.vec.Vec (constraint.ZeroConstraint W))
    (a : CoreModels.alloc.vec.Vec (constraint.AndConstraint W))
    (m : CoreModels.alloc.vec.Vec (constraint.IntegerMulConstraint W))
    (s : system.ConstraintSystem W) :
    system.ConstraintSystem.new inst pl wl z a m = .ok (.Ok s) ↔
      pl.val < 2 ^ 32 ∧ wl.val < 2 ^ 32 ∧ (vecSlice z).val.length < 2 ^ 32 ∧
      (vecSlice a).val.length < 2 ^ 32 ∧ (vecSlice m).val.length < 2 ^ 32 ∧
      validateSpec (sysOf pl wl z a m) = .Ok () ∧ s = sysOf pl wl z a m :=
  system_new_ok inst pl wl z a m s

/-- Address validation accepts exactly the systems whose every term addresses a word inside its segment. -/
theorem validateSpec.ok_iff {W : Type} (sys : system.ConstraintSystem W) :
    validateSpec sys = .Ok () ↔
      (∀ r ∈ (vecSlice sys.zero_constraints).val, opIn sys r.value) ∧
      (∀ r ∈ (vecSlice sys.and_constraints).val,
        opIn sys r.left ∧ opIn sys r.right ∧ opIn sys r.output) ∧
      (∀ r ∈ (vecSlice sys.integer_mul_constraints).val,
        opIn sys r.left ∧ opIn sys r.right ∧ opIn sys r.low ∧ opIn sys r.high) :=
  validateSpec_ok sys

/-- A gadget's interface width is the sum of its inputs and outputs, and must equal its public length. -/
theorem Component.new.eq {W : Type} (inst : word.Word W) (body : system.ConstraintSystem W)
    (i o : Std.Usize) :
    component.Component.new inst body i o = .ok
      (if i.val + o.val < 2 ^ UScalarTy.Usize.numBits then
        (if i.val + o.val = body.public_len.val then
          .Ok ⟨body, UScalar.cast .U32 i, UScalar.cast .U32 o⟩
        else .Err (.InterfaceMismatch i o (UScalar.cast .Usize body.public_len)))
      else .Err (.InterfaceTooWide i o)) :=
  component_new_eq inst body i o

/-- A composition built from gadgets of bounded width is laid out: instance blocks are packed one after the other. -/
theorem Composition.new.laid_out {W : Type} (inst : word.Word W)
    (callsV : CoreModels.alloc.vec.Vec (component.ComponentCall W))
    (hwf : ∀ c ∈ (vecSlice callsV).val, slotsP c < 2 ^ 32) :
    ∃ r, component.Composition.new inst callsV = .ok r ∧
      ∀ comp, r = .Ok comp → LaidOut comp ∧ comp.calls = callsV :=
  composition_new_laid_out inst callsV hwf

/-- On a laid-out composition, readdressing returns its specification. -/
theorem Composition.resolve.eq {W : Type} (inst : word.Word W) (comp : component.Composition W)
    (hl : LaidOut comp) (k i : Std.Usize) (idx : index.ValueIndex) :
    component.Composition.resolve inst comp k i idx = .ok (resolveSpec comp k i idx) :=
  resolve_eq inst comp hl k i idx

/-- On a laid-out composition, readdressing is injective.

Two successes with the same address share the call, the instance and the local address. -/
theorem Composition.resolve.injective {W : Type} (inst : word.Word W) (comp : component.Composition W)
    (hl : LaidOut comp) {k₁ k₂ i₁ i₂ : Std.Usize} {idx₁ idx₂ r : index.ValueIndex}
    (h₁ : component.Composition.resolve inst comp k₁ i₁ idx₁ = .ok (.Ok r))
    (h₂ : component.Composition.resolve inst comp k₂ i₂ idx₂ = .ok (.Ok r)) :
    k₁ = k₂ ∧ i₁ = i₂ ∧ idx₁ = idx₂ :=
  resolve_injective inst comp hl h₁ h₂

/-- On a laid-out composition, a successful readdressing keeps the segment and lands inside the composed segment. -/
theorem Composition.resolve.lt_len {W : Type} (inst : word.Word W) (comp : component.Composition W)
    (hl : LaidOut comp) {k i : Std.Usize} {idx r : index.ValueIndex}
    (h : component.Composition.resolve inst comp k i idx = .ok (.Ok r)) :
    r.segment = idx.segment ∧ r.position.val < lenOf comp idx.segment :=
  resolve_lt_len inst comp hl h

/-- The interface lookup panics on a caller segment shorter than the range it resolved.

It returns a result, so the panic is a defect. -/
theorem Composition.interface.panics {W : Type} (inst : word.Word W) (comp : component.Composition W)
    (pub : Slice W) (k i st en : Std.Usize)
    (hr : component.Composition.interface_range inst comp k i = .ok (.Ok (st, en)))
    (hlen : pub.val.length < en.val) :
    component.Composition.interface inst comp pub k i = .fail .panic :=
  interface_panics inst comp pub k i st en hr hlen

end Plonky3Lean.Claims.P3Word
