module

public import Plonky3Lean.Proofs.Word.Relations

@[expose] public section

/-!
# The scalar verifier

The verifier checks both segment lengths, then every relation, families in zero, AND, then product order.

It reports the first relation that fails.
-/

open Aeneas Aeneas.Std CoreModels p3_word
open Plonky3Lean.Lib

namespace Plonky3Lean.Proofs.Word

/-- A vector, read as the slice it holds. -/
abbrev vecSlice {T : Type} (v : CoreModels.alloc.vec.Vec T) : Slice T := v

theorem vec_len_eq {T : Type} (v : CoreModels.alloc.vec.Vec T) :
    CoreModels.alloc.vec.Vec.len v = .ok (vecSlice v).len := rfl

theorem vec_index_eq {T : Type} (v : CoreModels.alloc.vec.Vec T) (i : Std.Usize)
    (h : i.val < v.val.length) :
    CoreModels.alloc.vec.Vec.Insts.CoreOpsIndexIndex.index
      (CoreModels.core.Usize.Insts.CoreSliceIndexSliceIndexSliceT T) v i = .ok (v.val[i.val]) := by
  simp only [CoreModels.alloc.vec.Vec.Insts.CoreOpsIndexIndex.index,
    CoreModels.alloc.vec.Vec.Insts.CoreOpsDerefDerefSlice.deref, CoreModels.alloc.vec.Vec.as_slice,
    CoreModels.rust_primitives.sequence.seq_to_slice, CoreModels.core.Slice.Insts.CoreOpsIndexIndex.index,
    CoreModels.core.Usize.Insts.CoreSliceIndexSliceIndexSliceT.get,
    CoreModels.rust_primitives.slice.slice_length, CoreModels.rust_primitives.slice.slice_index]
  erw [bind_ok, bind_ok, ite_eq_left (show i < Slice.len (vecSlice v) by simpa using h),
    slice_index_eq (vecSlice v) i h, bind_ok, bind_ok]

/-- The `usize` that has a given value. -/
def uOf (k : ℕ) : Std.Usize := ⟨BitVec.ofNat _ k⟩

theorem uOf_val {k : ℕ} (h : k < 2 ^ UScalarTy.Usize.numBits) : (uOf k).val = k := by
  show (BitVec.ofNat _ k).toNat = k
  rw [BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt h

theorem uOf_self (i : Std.Usize) : uOf i.val = i :=
  UScalar.eq_of_val_eq (uOf_val i.hBounds)

theorem succ_eq (i : Std.Usize) (h : i.val + 1 < 2 ^ UScalarTy.Usize.numBits) :
    (i + 1#usize : RustM Std.Usize) = .ok (uOf (i.val + 1)) := by
  have hmax : i.val + (1#usize : Std.Usize).val ≤ UScalar.max .Usize := by
    simp only [UScalar.max, show (1#usize : Std.Usize).val = 1 from rfl]; omega
  obtain ⟨z, hz, hv⟩ := spec_imp_exists (UScalar.add_bv_spec hmax)
  rw [hz]
  congr 1
  exact UScalar.eq_of_val_eq (by rw [hv.1, uOf_val (by omega)]; rfl)

/-- The outcome of checking one relation family from position `i` on: the first failing position, or success. -/
def famSpec {R : Type} (xs : List R) (p : R → Bool) (kind : system.ConstraintKind) (i : ℕ) :
    CoreModels.core.result.Result Unit system.VerificationError :=
  match (xs.drop i).findIdx? (fun r => !p r) with
  | some k => .Err (.Unsatisfied kind (uOf (i + k)))
  | none => .Ok ()

/-- One step of a family check: the shape the three reshaped verifier loops share. -/
def famBody {R : Type} (xs : CoreModels.alloc.vec.Vec R) (kind : system.ConstraintKind)
    (sat : R → RustM Bool) (i : Std.Usize) :
    RustM (ControlFlow Std.Usize (CoreModels.core.result.Result Unit system.VerificationError)) := do
  let n ← CoreModels.alloc.vec.Vec.len xs
  if i < n then
    let r ← CoreModels.alloc.vec.Vec.Insts.CoreOpsIndexIndex.index
      (CoreModels.core.Usize.Insts.CoreSliceIndexSliceIndexSliceT R) xs i
    let b ← sat r
    if b then
      let j ← i + 1#usize
      .ok (.cont j)
    else .ok (.done (.Err (.Unsatisfied kind i)))
  else .ok (.done (.Ok ()))

theorem fam_loop {R : Type} (xs : CoreModels.alloc.vec.Vec R) (kind : system.ConstraintKind)
    (sat : R → RustM Bool) (p : R → Bool) (hsat : ∀ r ∈ xs.val, sat r = .ok (p r)) :
    ∀ n (i : Std.Usize), xs.val.length - i.val = n → i.val ≤ xs.val.length →
      loop (famBody xs kind sat) i = .ok (famSpec xs.val p kind i.val) := by
  have hlen : xs.val.length < 2 ^ UScalarTy.Usize.numBits := by
    have h := xs.property
    rw [← UScalar.max_USize_eq] at h
    simp only [UScalar.max] at h
    have : 0 < 2 ^ UScalarTy.Usize.numBits := Nat.two_pow_pos _
    omega
  intro n
  induction n with
  | zero =>
    intro i hn hi
    have he : i.val = xs.val.length := by omega
    rw [loop]
    have hlt : ¬ i < (vecSlice xs).len := by
      rw [UScalar.lt_equiv]; simp [he]
    simp only [famBody, vec_len_eq, bind_ok, hlt, ite_false]
    simp [famSpec, he]
  | succ n ih =>
    intro i hn hi
    have hlt' : i.val < xs.val.length := by omega
    have hlt : i < (vecSlice xs).len := by
      rw [UScalar.lt_equiv]; simpa using hlt'
    rw [loop]
    simp only [famBody, vec_len_eq, bind_ok, hlt, ite_true, vec_index_eq xs i hlt',
      hsat _ (List.getElem_mem hlt')]
    have hd : xs.val.drop i.val = xs.val[i.val] :: xs.val.drop (i.val + 1) :=
      List.drop_eq_getElem_cons hlt'
    cases hp : p xs.val[i.val] with
    | false =>
      simp [famSpec, hd, hp, List.findIdx?_cons, uOf_self]
    | true =>
      simp only [ite_true, succ_eq i (by omega), bind_ok]
      rw [ih (uOf (i.val + 1)) (by rw [uOf_val (by omega)]; omega)
        (by rw [uOf_val (by omega)]; omega), uOf_val (by omega)]
      simp only [famSpec, hd, List.findIdx?_cons, hp, Bool.not_true]
      cases h : List.findIdx? (fun r => !p r) (List.drop (i.val + 1) xs.val) <;>
        simp [Nat.add_assoc, Nat.add_comm 1]

variable {W : Type} [DecidableEq W] {inst : word.Word W} (M : Model inst)

/-- Every term of every relation applies without panicking. -/
def SysValid (sys : system.ConstraintSystem W) : Prop :=
  (∀ c ∈ (vecSlice sys.zero_constraints).val, OpValid M c.value) ∧
  (∀ c ∈ (vecSlice sys.and_constraints).val, OpValid M c.left ∧ OpValid M c.right ∧ OpValid M c.output) ∧
  (∀ c ∈ (vecSlice sys.integer_mul_constraints).val,
    OpValid M c.left ∧ OpValid M c.right ∧ OpValid M c.low ∧ OpValid M c.high)

/-- What the scalar verifier returns.

- A public segment of the wrong length is reported first, then a witness of the wrong length.
- Then the first failing relation is reported, families in zero, AND, then product order. -/
def verifySpec (sys : system.ConstraintSystem W) (pub wit : Slice W) :
    CoreModels.core.result.Result Unit system.VerificationError :=
  if pub.len ≠ UScalar.cast .Usize sys.public_len then
    .Err (.PublicLength (UScalar.cast .Usize sys.public_len) pub.len)
  else if wit.len ≠ UScalar.cast .Usize sys.witness_len then
    .Err (.WitnessLength (UScalar.cast .Usize sys.witness_len) wit.len)
  else
    match famSpec (vecSlice sys.zero_constraints).val
        (fun c => decide (opVal M pub wit c.value = some M.zero)) .Zero 0 with
    | .Err e => .Err e
    | .Ok () =>
      match famSpec (vecSlice sys.and_constraints).val (andHolds M pub wit) .And 0 with
      | .Err e => .Err e
      | .Ok () => famSpec (vecSlice sys.integer_mul_constraints).val (mulHolds M pub wit) .IntegerMul 0

theorem verify_zero_family_eq (sys : system.ConstraintSystem W) (pub wit : Slice W)
    (hv : SysValid M sys) :
    system.reshaped.ConstraintSystem.verify_zero_family inst sys pub wit =
      .ok (famSpec (vecSlice sys.zero_constraints).val
        (fun c => decide (opVal M pub wit c.value = some M.zero)) .Zero 0) := by
  show loop (famBody sys.zero_constraints .Zero
    (fun c => constraint.ZeroConstraint.is_satisfied inst c pub wit)) 0#usize = _
  exact fam_loop _ _ _ _ (fun c hc => zero_sat M pub wit c (hv.1 c hc)) _ _ rfl (by simp)

theorem verify_and_family_eq (sys : system.ConstraintSystem W) (pub wit : Slice W)
    (hv : SysValid M sys) :
    system.reshaped.ConstraintSystem.verify_and_family inst sys pub wit =
      .ok (famSpec (vecSlice sys.and_constraints).val (andHolds M pub wit) .And 0) := by
  show loop (famBody sys.and_constraints .And
    (fun c => constraint.AndConstraint.is_satisfied inst c pub wit)) 0#usize = _
  exact fam_loop _ _ _ _ (fun c hc => and_sat M pub wit c (hv.2.1 c hc).1 (hv.2.1 c hc).2.1
    (hv.2.1 c hc).2.2) _ _ rfl (by simp)

theorem verify_mul_family_eq (sys : system.ConstraintSystem W) (pub wit : Slice W)
    (hv : SysValid M sys) :
    system.reshaped.ConstraintSystem.verify_integer_mul_family inst sys pub wit =
      .ok (famSpec (vecSlice sys.integer_mul_constraints).val (mulHolds M pub wit) .IntegerMul 0) := by
  show loop (famBody sys.integer_mul_constraints .IntegerMul
    (fun c => constraint.IntegerMulConstraint.is_satisfied inst c pub wit)) 0#usize = _
  obtain ⟨_, _, h⟩ := hv
  exact fam_loop _ _ _ _ (fun c hc => mul_sat M pub wit c (h c hc).1 (h c hc).2.1 (h c hc).2.2.1
    (h c hc).2.2.2) _ _ rfl (by simp)

/-- The scalar verifier, on a system whose shifts are all valid, returns the reference outcome. -/
theorem verify_eq (sys : system.ConstraintSystem W) (pub wit : Slice W) (hv : SysValid M sys) :
    system.ConstraintSystem.verify inst sys pub wit = .ok (verifySpec M sys pub wit) := by
  simp only [system.ConstraintSystem.verify, system.reshaped.ConstraintSystem.reshaped_verify,
    CoreModels.core.slice.Slice.len, CoreModels.rust_primitives.slice.slice_length,
    system.ConstraintSystem.impl.public_len, system.ConstraintSystem.impl.witness_len, bind_ok,
    verify_zero_family_eq M sys pub wit hv, verify_and_family_eq M sys pub wit hv,
    verify_mul_family_eq M sys pub wit hv, verifySpec, bne_iff_ne, ne_eq]
  split_ifs <;> try rfl
  generalize famSpec (vecSlice sys.zero_constraints).val _ _ 0 = r1
  generalize famSpec (vecSlice sys.and_constraints).val _ _ 0 = r2
  cases r1 <;> cases r2 <;>
    simp [CoreModels.core.result.Result.Insts.CoreOpsTry_traitTryTResultInfallibleE.branch,
      CoreModels.core.result.Result.Insts.CoreOpsTry_traitFromResidualResultInfallibleE.from_residual,
      CoreModels.core.convert.From.Blanket.from]

theorem famSpec_ok {R : Type} (xs : List R) (p : R → Bool) (kind : system.ConstraintKind) :
    famSpec xs p kind 0 = .Ok () ↔ ∀ x ∈ xs, p x = true := by
  unfold famSpec
  cases h : (xs.drop 0).findIdx? (fun r => !p r) with
  | some k =>
    simp only [List.drop_zero, List.findIdx?_eq_some_iff_getElem] at h
    obtain ⟨hk, hp, -⟩ := h
    simp only [reduceCtorEq, false_iff, not_forall]
    exact ⟨_, List.getElem_mem hk, by simpa using hp⟩
  | none =>
    simp only [List.drop_zero, List.findIdx?_eq_none_iff] at h
    simpa using h

/-- A system accepts exactly when both segments have their declared lengths and every relation holds. -/
theorem verifySpec_ok (sys : system.ConstraintSystem W) (pub wit : Slice W) :
    verifySpec M sys pub wit = .Ok () ↔
      pub.len = UScalar.cast .Usize sys.public_len ∧
      wit.len = UScalar.cast .Usize sys.witness_len ∧
      (∀ c ∈ (vecSlice sys.zero_constraints).val, opVal M pub wit c.value = some M.zero) ∧
      (∀ c ∈ (vecSlice sys.and_constraints).val, andHolds M pub wit c = true) ∧
      (∀ c ∈ (vecSlice sys.integer_mul_constraints).val, mulHolds M pub wit c = true) := by
  unfold verifySpec
  split_ifs with h1 h2
  · simp [h1]
  · simp [h2]
  · simp only [not_not] at h1 h2
    have e1 := famSpec_ok (vecSlice sys.zero_constraints).val
      (fun c => decide (opVal M pub wit c.value = some M.zero)) .Zero
    have e2 := famSpec_ok (vecSlice sys.and_constraints).val (andHolds M pub wit) .And
    have e3 := famSpec_ok (vecSlice sys.integer_mul_constraints).val (mulHolds M pub wit) .IntegerMul
    revert e1 e2 e3
    generalize famSpec (vecSlice sys.zero_constraints).val _ _ 0 = r1
    generalize famSpec (vecSlice sys.and_constraints).val _ _ 0 = r2
    generalize famSpec (vecSlice sys.integer_mul_constraints).val _ _ 0 = r3
    intro e1 e2 e3
    cases r1 <;> cases r2 <;> simp_all

end Plonky3Lean.Proofs.Word
