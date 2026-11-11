module

public import Plonky3Lean.Proofs.Word.Layout2

@[expose] public section

/-!
# Address validation

A system is accepted only when every term of every relation addresses a word inside its segment.

The first term outside its segment is reported, with its family, relation, role and position.
-/

open Aeneas Aeneas.Std CoreModels p3_word
open Plonky3Lean.Lib

namespace Plonky3Lean.Proofs.Word

variable {W : Type}

/-- The declared length of a segment of a system. -/
def sysLen (sys : system.ConstraintSystem W) : index.Segment → Std.Usize
  | .Public => UScalar.cast .Usize sys.public_len
  | .Witness => UScalar.cast .Usize sys.witness_len

/-- Whether a term addresses a word inside its declared segment. -/
def inRange (sys : system.ConstraintSystem W) (t : shift.ShiftedValue W) : Bool :=
  decide (t.index.position.val < (sysLen sys t.index.segment).val)

/-- What validating one operand returns: the first term outside its segment, counted from `k`. -/
def opCheck (sys : system.ConstraintSystem W) (kind : system.ConstraintKind) (c : Std.Usize)
    (role : system.OperandRole) : ℕ → List (shift.ShiftedValue W) →
    CoreModels.core.result.Result Unit system.SystemError
  | _, [] => .Ok ()
  | k, t :: ts =>
    if inRange sys t then opCheck sys kind c role (k + 1) ts
    else .Err (.IndexOutOfBounds kind c role (uOf k) t.index.segment t.index.position
      (sysLen sys t.index.segment))

theorem opCheck_ok (sys : system.ConstraintSystem W) (kind : system.ConstraintKind) (c : Std.Usize)
    (role : system.OperandRole) (k : ℕ) (ts : List (shift.ShiftedValue W)) :
    opCheck sys kind c role k ts = .Ok () ↔ ∀ t ∈ ts, inRange sys t = true := by
  induction ts generalizing k with
  | nil => simp [opCheck]
  | cons t ts ih =>
    simp only [opCheck, List.mem_cons, forall_eq_or_imp]
    split_ifs with h <;> simp [h, ih]

/-- The iterator over an operand's (position, index) pairs. -/
abbrev IdxIter (W : Type) := CoreModels.core.iter.adapters.map.Map
  (CoreModels.core.iter.adapters.enumerate.Enumerate
    (CoreModels.core.slice.iter.Iter (shift.ShiftedValue W)))
  (constraint.Operand.indices.closure W)

theorem idx_next_nil (inst : word.Word W) (st : IdxIter W) (hs : (iterSlice st.iter.iter).val = []) :
    ∃ st' : IdxIter W, CoreModels.core.iter.adapters.map.Map.Insts.CoreIterTraitsIteratorIterator.next
      (CoreModels.core.iter.adapters.enumerate.Enumerate.Insts.CoreIterTraitsIteratorIteratorPairUsizeClause0_Item
        (CoreModels.core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT (shift.ShiftedValue W)))
      (constraint.Operand.indices.closure.Insts.CoreOpsFunctionFnMutTuplePairUsizeShared0ShiftedValuePairUsizeValueIndex
        inst) st = .ok (.None, st') := by
  refine ⟨{ st with iter := { st.iter with iter := st.iter.iter } }, ?_⟩
  simp only [CoreModels.core.iter.adapters.map.Map.Insts.CoreIterTraitsIteratorIterator.next,
    CoreModels.core.iter.adapters.enumerate.Enumerate.Insts.CoreIterTraitsIteratorIteratorPairUsizeClause0_Item.next,
    iter_next_nil _ hs, bind_ok, Aeneas.Std.uncurry_apply_pair]

theorem idx_next_cons (inst : word.Word W) (st : IdxIter W) (t : shift.ShiftedValue W)
    (ts : List (shift.ShiftedValue W)) (hs : (iterSlice st.iter.iter).val = t :: ts)
    (hc : st.iter.count.val + 1 < 2 ^ UScalarTy.Usize.numBits) :
    ∃ st' : IdxIter W, (iterSlice st'.iter.iter).val = ts ∧ st'.iter.count.val = st.iter.count.val + 1 ∧
      CoreModels.core.iter.adapters.map.Map.Insts.CoreIterTraitsIteratorIterator.next
      (CoreModels.core.iter.adapters.enumerate.Enumerate.Insts.CoreIterTraitsIteratorIteratorPairUsizeClause0_Item
        (CoreModels.core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT (shift.ShiftedValue W)))
      (constraint.Operand.indices.closure.Insts.CoreOpsFunctionFnMutTuplePairUsizeShared0ShiftedValuePairUsizeValueIndex
        inst) st = .ok (.Some (st.iter.count, t.index), st') := by
  obtain ⟨s', hn, hs'⟩ := iter_next_cons st.iter.iter t ts hs
  refine ⟨⟨⟨s', uOf (st.iter.count.val + 1)⟩, st.f⟩, hs', uOf_val hc, ?_⟩
  simp only [CoreModels.core.iter.adapters.map.Map.Insts.CoreIterTraitsIteratorIterator.next,
    CoreModels.core.iter.adapters.enumerate.Enumerate.Insts.CoreIterTraitsIteratorIteratorPairUsizeClause0_Item.next,
    hn, bind_ok, Aeneas.Std.uncurry_apply_pair, succ_eq _ hc,
    constraint.Operand.indices.closure.Insts.CoreOpsFunctionFnMutTuplePairUsizeShared0ShiftedValuePairUsizeValueIndex.call_mut,
    shift.ShiftedValue.impl.index]

theorem vbody_cons (inst : word.Word W) (sys : system.ConstraintSystem W)
    (kind : system.ConstraintKind) (c : Std.Usize) (role : system.OperandRole) (st st' : IdxIter W)
    (t : shift.ShiftedValue W)
    (hn : CoreModels.core.iter.adapters.map.Map.Insts.CoreIterTraitsIteratorIterator.next
      (CoreModels.core.iter.adapters.enumerate.Enumerate.Insts.CoreIterTraitsIteratorIteratorPairUsizeClause0_Item
        (CoreModels.core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT (shift.ShiftedValue W)))
      (constraint.Operand.indices.closure.Insts.CoreOpsFunctionFnMutTuplePairUsizeShared0ShiftedValuePairUsizeValueIndex
        inst) st = .ok (.Some (st.iter.count, t.index), st')) :
    system.ConstraintSystem.validate_operand_loop.body inst sys kind c role st =
      .ok (if t.index.position.val < (sysLen sys t.index.segment).val then .cont st'
        else .done (.Err (.IndexOutOfBounds kind c role st.iter.count t.index.segment t.index.position
          (sysLen sys t.index.segment)))) := by
  have h32 := two_pow_32_le
  obtain ⟨⟨seg, pos⟩, sh⟩ := t
  have hpos : (UScalar.cast .Usize pos).val = pos.val := cast_usize_val _ (by decide)
  simp only [system.ConstraintSystem.validate_operand_loop.body, hn, bind_ok,
    Aeneas.Std.uncurry_apply_pair, index.ValueIndex.impl.segment, index.ValueIndex.impl.position,
    lift_eq, GE.ge, UScalar.le_equiv, hpos]
  cases seg <;>
  · simp only [system.ConstraintSystem.impl.public_len, system.ConstraintSystem.impl.witness_len,
      bind_ok, sysLen]
    split_ifs with h1 h2 h2
    all_goals first | (exfalso; omega) | simp only [h2, ite_true, ite_false]

theorem validate_operand_loop_eq (inst : word.Word W) (sys : system.ConstraintSystem W)
    (kind : system.ConstraintKind) (c : Std.Usize) (role : system.OperandRole) :
    ∀ (ts : List (shift.ShiftedValue W)) (st : IdxIter W),
      (iterSlice st.iter.iter).val = ts → st.iter.count.val + ts.length < 2 ^ UScalarTy.Usize.numBits →
      system.ConstraintSystem.validate_operand_loop inst st sys kind c role =
        .ok (opCheck sys kind c role st.iter.count.val ts) := by
  intro ts
  induction ts with
  | nil =>
    intro st hs _
    obtain ⟨st', hn⟩ := idx_next_nil inst st hs
    rw [system.ConstraintSystem.validate_operand_loop, loop]
    simp only [system.ConstraintSystem.validate_operand_loop.body, hn, bind_ok,
      Aeneas.Std.uncurry_apply_pair, opCheck]
  | cons t ts ih =>
    intro st hs hb
    simp only [List.length_cons] at hb
    obtain ⟨st', hs', hc', hn⟩ := idx_next_cons inst st t ts hs (by omega)
    rw [system.ConstraintSystem.validate_operand_loop, loop, vbody_cons inst sys kind c role st st' t hn]
    simp only [opCheck, inRange, decide_eq_true_eq]
    split_ifs
    · rw [bind_ok, ← hc']
      exact ih st' hs' (by omega)
    · rw [bind_ok, uOf_self]

/-- The first of two checks to fail, or the second when the first passes. -/
def rthen {E : Type} (r k : CoreModels.core.result.Result Unit E) : CoreModels.core.result.Result Unit E :=
  match r with
  | .Err e => .Err e
  | .Ok _ => k

theorem try_unit_eq {E α : Type} (r : CoreModels.core.result.Result Unit E)
    (k : RustM (CoreModels.core.result.Result α E)) :
    (do
      let cf ← CoreModels.core.result.Result.Insts.CoreOpsTry_traitTry.branch r
      match cf with
      | CoreModels.core.ops.control_flow.ControlFlow.Continue _ => k
      | CoreModels.core.ops.control_flow.ControlFlow.Break residual =>
        CoreModels.core.result.Result.Insts.CoreOpsTry_traitFromResidualResultNeverE.from_residual α
          (CoreModels.core.convert.From.Blanket E) residual) =
      (match r with
      | .Ok _ => k
      | .Err e => .ok (.Err e)) := by
  cases r <;> simp [CoreModels.core.result.Result.Insts.CoreOpsTry_traitTryTResultInfallibleE.branch,
    CoreModels.core.result.Result.Insts.CoreOpsTry_traitFromResidualResultInfallibleE.from_residual,
    CoreModels.core.convert.From.Blanket.from]

/-- A slice, read as an iterator over it. -/
def sliceIter {T : Type} (sl : Slice T) : CoreModels.core.slice.iter.Iter T := sl

theorem slice_iter_eq {T : Type} (sl : Slice T) :
    CoreModels.core.slice.Slice.iter sl = .ok (sliceIter sl) :=
  bind_tc_ok (α := _root_.rust_primitives.sequence.Seq T) _ _

theorem validate_operand_eq (inst : word.Word W) (sys : system.ConstraintSystem W)
    (kind : system.ConstraintKind) (c : Std.Usize) (role : system.OperandRole)
    (op : constraint.Operand W) :
    system.ConstraintSystem.validate_operand inst sys kind c role op =
      .ok (opCheck sys kind c role 0 (vecSlice op.terms).val) := by
  have hlen : (vecSlice op.terms).val.length < 2 ^ UScalarTy.Usize.numBits := by
    have h := op.terms.property
    rw [← UScalar.max_USize_eq] at h; simp only [UScalar.max] at h
    have : 0 < 2 ^ UScalarTy.Usize.numBits := Nat.two_pow_pos _
    have h2 : (vecSlice op.terms).val.length = op.terms.val.length := rfl
    omega
  simp only [system.ConstraintSystem.validate_operand, constraint.Operand.indices, vec_deref_eq,
    bind_ok, CoreModels.core.iter.traits.iterator.Iterator.enumerate.default,
    CoreModels.core.iter.adapters.enumerate.Enumerate.new,
    CoreModels.core.iter.traits.iterator.Iterator.map.default,
    CoreModels.core.iter.adapters.map.Map.new, slice_iter_eq]
  exact validate_operand_loop_eq inst sys kind c role _ ⟨⟨sliceIter (vecSlice op.terms), 0#usize⟩, ()⟩
    rfl (by simpa using hlen)

theorem zero_relation_check (inst : word.Word W) (sys : system.ConstraintSystem W) (c : Std.Usize)
    (rel : constraint.ZeroConstraint W) :
    (do
      let o ← constraint.ZeroConstraint.impl.value inst rel
      system.ConstraintSystem.validate_operand inst sys .Zero c .Value o) =
      .ok (opCheck sys .Zero c .Value 0 (vecSlice rel.value.terms).val) := by
  simp only [constraint.ZeroConstraint.impl.value, bind_tc_ok, validate_operand_eq]

theorem and_relation_eq (inst : word.Word W) (sys : system.ConstraintSystem W) (c : Std.Usize)
    (rel : constraint.AndConstraint W) :
    system.reshaped.ConstraintSystem.validate_and_relation inst sys c rel =
      .ok (rthen (opCheck sys .And c .Left 0 (vecSlice rel.left.terms).val)
        (rthen (opCheck sys .And c .Right 0 (vecSlice rel.right.terms).val)
          (opCheck sys .And c .Output 0 (vecSlice rel.output.terms).val))) := by
  simp only [system.reshaped.ConstraintSystem.validate_and_relation,
    constraint.AndConstraint.impl.left, constraint.AndConstraint.impl.right,
    constraint.AndConstraint.impl.output, bind_ok, validate_operand_eq]
  generalize opCheck sys .And c .Left 0 _ = r1
  generalize opCheck sys .And c .Right 0 _ = r2
  cases r1 <;> cases r2 <;>
    simp [CoreModels.core.result.Result.Insts.CoreOpsTry_traitTryTResultInfallibleE.branch,
      CoreModels.core.result.Result.Insts.CoreOpsTry_traitFromResidualResultInfallibleE.from_residual,
      CoreModels.core.convert.From.Blanket.from, rthen]

theorem mul_relation_eq (inst : word.Word W) (sys : system.ConstraintSystem W) (c : Std.Usize)
    (rel : constraint.IntegerMulConstraint W) :
    system.reshaped.ConstraintSystem.validate_integer_mul_relation inst sys c rel =
      .ok (rthen (opCheck sys .IntegerMul c .Left 0 (vecSlice rel.left.terms).val)
        (rthen (opCheck sys .IntegerMul c .Right 0 (vecSlice rel.right.terms).val)
          (rthen (opCheck sys .IntegerMul c .Low 0 (vecSlice rel.low.terms).val)
            (opCheck sys .IntegerMul c .High 0 (vecSlice rel.high.terms).val)))) := by
  simp only [system.reshaped.ConstraintSystem.validate_integer_mul_relation,
    constraint.IntegerMulConstraint.impl.left, constraint.IntegerMulConstraint.impl.right,
    constraint.IntegerMulConstraint.impl.low, constraint.IntegerMulConstraint.impl.high, bind_ok,
    validate_operand_eq]
  generalize opCheck sys .IntegerMul c .Left 0 _ = r1
  generalize opCheck sys .IntegerMul c .Right 0 _ = r2
  generalize opCheck sys .IntegerMul c .Low 0 _ = r3
  cases r1 <;> cases r2 <;> cases r3 <;>
    simp [CoreModels.core.result.Result.Insts.CoreOpsTry_traitTryTResultInfallibleE.branch,
      CoreModels.core.result.Result.Insts.CoreOpsTry_traitFromResidualResultInfallibleE.from_residual,
      CoreModels.core.convert.From.Blanket.from, rthen]

/-- One step of a family validation: the shape the three reshaped validation loops share. -/
def vfamBody {R : Type} (xs : CoreModels.alloc.vec.Vec R)
    (chk : Std.Usize → R → RustM (CoreModels.core.result.Result Unit system.SystemError))
    (i : Std.Usize) :
    RustM (ControlFlow Std.Usize (CoreModels.core.result.Result Unit system.SystemError)) := do
  let n ← CoreModels.alloc.vec.Vec.len xs
  if i < n then
    let r ← CoreModels.alloc.vec.Vec.Insts.CoreOpsIndexIndex.index
      (CoreModels.core.Usize.Insts.CoreSliceIndexSliceIndexSliceT R) xs i
    let res ← chk i r
    let cf ← CoreModels.core.result.Result.Insts.CoreOpsTry_traitTry.branch res
    match cf with
    | CoreModels.core.ops.control_flow.ControlFlow.Continue _ =>
      let j ← i + 1#usize
      .ok (.cont j)
    | CoreModels.core.ops.control_flow.ControlFlow.Break residual =>
      let r1 ← CoreModels.core.result.Result.Insts.CoreOpsTry_traitFromResidualResultNeverE.from_residual
        Unit (CoreModels.core.convert.From.Blanket system.SystemError) residual
      .ok (.done r1)
  else .ok (.done (.Ok ()))

/-- What validating a family from position `i` on returns: the first failing relation's error. -/
def vfamSpec {R E : Type} (f : ℕ → R → CoreModels.core.result.Result Unit E) :
    ℕ → List R → CoreModels.core.result.Result Unit E
  | _, [] => .Ok ()
  | i, x :: xs => rthen (f i x) (vfamSpec f (i + 1) xs)

theorem vfam_loop {R : Type} (xs : CoreModels.alloc.vec.Vec R)
    (chk : Std.Usize → R → RustM (CoreModels.core.result.Result Unit system.SystemError))
    (f : ℕ → R → CoreModels.core.result.Result Unit system.SystemError)
    (hchk : ∀ c r, r ∈ (vecSlice xs).val → chk c r = .ok (f c.val r)) :
    ∀ n (i : Std.Usize), (vecSlice xs).val.length - i.val = n → i.val ≤ (vecSlice xs).val.length →
      loop (vfamBody xs chk) i = .ok (vfamSpec f i.val ((vecSlice xs).val.drop i.val)) := by
  have hlen : (vecSlice xs).val.length < 2 ^ UScalarTy.Usize.numBits := by
    have h := xs.property
    rw [← UScalar.max_USize_eq] at h
    simp only [UScalar.max] at h
    have : 0 < 2 ^ UScalarTy.Usize.numBits := Nat.two_pow_pos _
    have h2 : (vecSlice xs).val.length = xs.val.length := rfl
    omega
  intro n
  induction n with
  | zero =>
    intro i hn hi
    have he : i.val = (vecSlice xs).val.length := by omega
    have hlt : ¬ i < (vecSlice xs).len := by rw [UScalar.lt_equiv]; simp [he]
    rw [loop]
    simp only [vfamBody, vec_len_eq, bind_ok, hlt, ite_false]
    simp [he, vfamSpec]
  | succ n ih =>
    intro i hn hi
    have hlt' : i.val < (vecSlice xs).val.length := by omega
    have hlt : i < (vecSlice xs).len := by rw [UScalar.lt_equiv]; simpa using hlt'
    have hd : (vecSlice xs).val.drop i.val = (vecSlice xs).val[i.val] :: (vecSlice xs).val.drop (i.val + 1) :=
      List.drop_eq_getElem_cons hlt'
    rw [loop]
    simp only [vfamBody, vec_len_eq, bind_ok, hlt, ite_true, vec_index_eq xs i hlt',
      hchk _ _ (List.getElem_mem hlt')]
    rw [hd, vfamSpec]
    cases hf : f i.val (vecSlice xs).val[i.val] with
    | Err e =>
      simp [CoreModels.core.result.Result.Insts.CoreOpsTry_traitTryTResultInfallibleE.branch,
        CoreModels.core.result.Result.Insts.CoreOpsTry_traitFromResidualResultInfallibleE.from_residual,
        CoreModels.core.convert.From.Blanket.from, rthen]
    | Ok u =>
      simp only [CoreModels.core.result.Result.Insts.CoreOpsTry_traitTryTResultInfallibleE.branch,
        bind_ok, succ_eq i (by omega), rthen]
      rw [ih (uOf (i.val + 1)) (by rw [uOf_val (by omega)]; omega) (by rw [uOf_val (by omega)]; omega),
        uOf_val (by omega)]

/-- The zero family's check of relation `c`. -/
def zeroChk (sys : system.ConstraintSystem W) (c : ℕ) (r : constraint.ZeroConstraint W) :=
  opCheck sys .Zero (uOf c) .Value 0 (vecSlice r.value.terms).val

/-- The AND family's check of relation `c`. -/
def andChk (sys : system.ConstraintSystem W) (c : ℕ) (r : constraint.AndConstraint W) :=
  rthen (opCheck sys .And (uOf c) .Left 0 (vecSlice r.left.terms).val)
    (rthen (opCheck sys .And (uOf c) .Right 0 (vecSlice r.right.terms).val)
      (opCheck sys .And (uOf c) .Output 0 (vecSlice r.output.terms).val))

/-- The product family's check of relation `c`. -/
def mulChk (sys : system.ConstraintSystem W) (c : ℕ) (r : constraint.IntegerMulConstraint W) :=
  rthen (opCheck sys .IntegerMul (uOf c) .Left 0 (vecSlice r.left.terms).val)
    (rthen (opCheck sys .IntegerMul (uOf c) .Right 0 (vecSlice r.right.terms).val)
      (rthen (opCheck sys .IntegerMul (uOf c) .Low 0 (vecSlice r.low.terms).val)
        (opCheck sys .IntegerMul (uOf c) .High 0 (vecSlice r.high.terms).val)))

/-- What address validation returns: families in zero, AND, then product order. -/
def validateSpec (sys : system.ConstraintSystem W) :
    CoreModels.core.result.Result Unit system.SystemError :=
  rthen (vfamSpec (zeroChk sys) 0 (vecSlice sys.zero_constraints).val)
    (rthen (vfamSpec (andChk sys) 0 (vecSlice sys.and_constraints).val)
      (vfamSpec (mulChk sys) 0 (vecSlice sys.integer_mul_constraints).val))

theorem validate_eq (inst : word.Word W) (sys : system.ConstraintSystem W) :
    system.reshaped.ConstraintSystem.reshaped_validate inst sys = .ok (validateSpec sys) := by
  have hz : system.reshaped.ConstraintSystem.validate_zero_family inst sys =
      .ok (vfamSpec (zeroChk sys) 0 (vecSlice sys.zero_constraints).val) := by
    have hb : (fun c => system.reshaped.ConstraintSystem.validate_zero_family_loop.body inst sys c) =
        vfamBody sys.zero_constraints
          (fun c r => system.ConstraintSystem.validate_operand inst sys .Zero c .Value r.value) := by
      funext c
      simp only [system.reshaped.ConstraintSystem.validate_zero_family_loop.body, vfamBody,
        constraint.ZeroConstraint.impl.value, bind_ok]
      rfl
    show loop _ 0#usize = _
    rw [hb]
    exact vfam_loop _ _ _ (fun c r _ => by rw [validate_operand_eq, zeroChk, uOf_self]) _ _ rfl (by simp)
  have ha : system.reshaped.ConstraintSystem.validate_and_family inst sys =
      .ok (vfamSpec (andChk sys) 0 (vecSlice sys.and_constraints).val) :=
    vfam_loop (chk := fun c r => system.reshaped.ConstraintSystem.validate_and_relation inst sys c r)
      _ _ (fun c r _ => by rw [and_relation_eq, andChk, uOf_self]) _ _ rfl (by simp)
  have hm : system.reshaped.ConstraintSystem.validate_integer_mul_family inst sys =
      .ok (vfamSpec (mulChk sys) 0 (vecSlice sys.integer_mul_constraints).val) :=
    vfam_loop (chk := fun c r => system.reshaped.ConstraintSystem.validate_integer_mul_relation inst sys c r)
      _ _ (fun c r _ => by rw [mul_relation_eq, mulChk, uOf_self]) _ _ rfl (by simp)
  simp only [system.reshaped.ConstraintSystem.reshaped_validate, hz, ha, hm, bind_ok, validateSpec]
  generalize vfamSpec (zeroChk sys) 0 _ = r1
  generalize vfamSpec (andChk sys) 0 _ = r2
  cases r1 <;> cases r2 <;>
    simp [CoreModels.core.result.Result.Insts.CoreOpsTry_traitTryTResultInfallibleE.branch,
      CoreModels.core.result.Result.Insts.CoreOpsTry_traitFromResidualResultInfallibleE.from_residual,
      CoreModels.core.convert.From.Blanket.from, rthen]

theorem constraint_count_eq (inst : word.Word W) (kind : system.ConstraintKind) (len : Std.Usize) :
    system.ConstraintSystem.validate_constraint_count inst kind len =
      .ok (if len.val < 2 ^ 32 then .Ok () else .Err (.TooManyConstraints kind len)) := by
  simp only [system.ConstraintSystem.validate_constraint_count, u32_try_from_eq, bind_ok]
  split_ifs <;> simp [CoreModels.core.result.Result.is_err]

/-- The system a successful constructor returns. -/
def sysOf (pl wl : Std.Usize) (z : CoreModels.alloc.vec.Vec (constraint.ZeroConstraint W))
    (a : CoreModels.alloc.vec.Vec (constraint.AndConstraint W))
    (m : CoreModels.alloc.vec.Vec (constraint.IntegerMulConstraint W)) : system.ConstraintSystem W :=
  ⟨UScalar.cast .U32 pl, UScalar.cast .U32 wl, z, a, m⟩

/-- What the system constructor returns.

- Each segment length, then each family size, is bounded by 32 bits, in that order.
- Then every term address is validated, families in zero, AND, then product order. -/
def newSpec (pl wl : Std.Usize) (z : CoreModels.alloc.vec.Vec (constraint.ZeroConstraint W))
    (a : CoreModels.alloc.vec.Vec (constraint.AndConstraint W))
    (m : CoreModels.alloc.vec.Vec (constraint.IntegerMulConstraint W)) :
    CoreModels.core.result.Result (system.ConstraintSystem W) system.SystemError :=
  if 2 ^ 32 ≤ pl.val then .Err (.SegmentTooLong .Public pl)
  else if 2 ^ 32 ≤ wl.val then .Err (.SegmentTooLong .Witness wl)
  else if 2 ^ 32 ≤ (vecSlice z).val.length then .Err (.TooManyConstraints .Zero (vecSlice z).len)
  else if 2 ^ 32 ≤ (vecSlice a).val.length then .Err (.TooManyConstraints .And (vecSlice a).len)
  else if 2 ^ 32 ≤ (vecSlice m).val.length then .Err (.TooManyConstraints .IntegerMul (vecSlice m).len)
  else match validateSpec (sysOf pl wl z a m) with
    | .Ok _ => .Ok (sysOf pl wl z a m)
    | .Err e => .Err e

theorem system_new_eq (inst : word.Word W) (pl wl : Std.Usize)
    (z : CoreModels.alloc.vec.Vec (constraint.ZeroConstraint W))
    (a : CoreModels.alloc.vec.Vec (constraint.AndConstraint W))
    (m : CoreModels.alloc.vec.Vec (constraint.IntegerMulConstraint W)) :
    system.ConstraintSystem.new inst pl wl z a m = .ok (newSpec pl wl z a m) := by
  simp only [system.ConstraintSystem.new, system.reshaped.ConstraintSystem.reshaped_new,
    u32_try_from_eq, bind_ok, vec_len_eq, constraint_count_eq]
  unfold newSpec
  simp only [Nat.reducePow]
  by_cases h1 : 4294967296 ≤ pl.val
  · simp [show ¬ pl.val < 4294967296 by omega, h1, CoreModels.core.result.Result.map_err,
      system.reshaped.ConstraintSystem.reshaped_new.closure.Insts.CoreOpsFunctionFnOnceTupleTryFromIntErrorSystemError.call_once,
      CoreModels.core.result.Result.Insts.CoreOpsTry_traitTryTResultInfallibleE.branch,
      CoreModels.core.result.Result.Insts.CoreOpsTry_traitFromResidualResultInfallibleE.from_residual,
      CoreModels.core.convert.From.Blanket.from]
  by_cases h2 : 4294967296 ≤ wl.val
  · simp [show pl.val < 4294967296 by omega, show ¬ wl.val < 4294967296 by omega, h1, h2,
      CoreModels.core.result.Result.map_err,
      system.reshaped.ConstraintSystem.reshaped_new.closure_1.Insts.CoreOpsFunctionFnOnceTupleTryFromIntErrorSystemError.call_once,
      CoreModels.core.result.Result.Insts.CoreOpsTry_traitTryTResultInfallibleE.branch,
      CoreModels.core.result.Result.Insts.CoreOpsTry_traitFromResidualResultInfallibleE.from_residual,
      CoreModels.core.convert.From.Blanket.from]
  simp only [show pl.val < 4294967296 by omega, show wl.val < 4294967296 by omega, h1, h2,
    CoreModels.core.result.Result.map_err, ite_true, ite_false, bind_ok,
    CoreModels.core.result.Result.Insts.CoreOpsTry_traitTryTResultInfallibleE.branch]
  by_cases h3 : 4294967296 ≤ (vecSlice z).val.length
  · simp [show ¬ (vecSlice z).val.length < 4294967296 by omega, h3, CoreModels.core.result.Result.Insts.CoreOpsTry_traitTryTResultInfallibleE.branch,
      CoreModels.core.result.Result.Insts.CoreOpsTry_traitFromResidualResultInfallibleE.from_residual,
      CoreModels.core.convert.From.Blanket.from]
  by_cases h4 : 4294967296 ≤ (vecSlice a).val.length
  · simp [show (vecSlice z).val.length < 4294967296 by omega,
      show ¬ (vecSlice a).val.length < 4294967296 by omega, h3, h4, CoreModels.core.result.Result.Insts.CoreOpsTry_traitTryTResultInfallibleE.branch,
      CoreModels.core.result.Result.Insts.CoreOpsTry_traitFromResidualResultInfallibleE.from_residual,
      CoreModels.core.convert.From.Blanket.from]
  by_cases h5 : 4294967296 ≤ (vecSlice m).val.length
  · simp [show (vecSlice z).val.length < 4294967296 by omega,
      show (vecSlice a).val.length < 4294967296 by omega,
      show ¬ (vecSlice m).val.length < 4294967296 by omega, h3, h4, h5, CoreModels.core.result.Result.Insts.CoreOpsTry_traitTryTResultInfallibleE.branch,
      CoreModels.core.result.Result.Insts.CoreOpsTry_traitFromResidualResultInfallibleE.from_residual,
      CoreModels.core.convert.From.Blanket.from]
  have hz : (vecSlice z).len.val < 4294967296 := by simp only [Slice.len_val, Slice.length]; omega
  have ha : (vecSlice a).len.val < 4294967296 := by simp only [Slice.len_val, Slice.length]; omega
  have hm : (vecSlice m).len.val < 4294967296 := by simp only [Slice.len_val, Slice.length]; omega
  simp only [hz, ha, hm, h3, h4, h5, ite_true, ite_false, bind_ok, validate_eq]
  unfold sysOf
  cases validateSpec _ <;> simp [CoreModels.core.result.Result.Insts.CoreOpsTry_traitTryTResultInfallibleE.branch,
      CoreModels.core.result.Result.Insts.CoreOpsTry_traitFromResidualResultInfallibleE.from_residual,
      CoreModels.core.convert.From.Blanket.from]

theorem rthen_ok {E : Type} (r k : CoreModels.core.result.Result Unit E) :
    rthen r k = .Ok () ↔ r = .Ok () ∧ k = .Ok () := by
  cases r <;> simp [rthen]

theorem vfamSpec_ok {R E : Type} (f : ℕ → R → CoreModels.core.result.Result Unit E) (P : R → Prop)
    (hf : ∀ i x, f i x = .Ok () ↔ P x) (i : ℕ) (xs : List R) :
    vfamSpec f i xs = .Ok () ↔ ∀ x ∈ xs, P x := by
  induction xs generalizing i with
  | nil => simp [vfamSpec]
  | cons x xs ih => simp [vfamSpec, rthen_ok, hf, ih]

/-- Every term of an operand addresses a word inside its segment. -/
def opIn (sys : system.ConstraintSystem W) (o : constraint.Operand W) : Prop :=
  ∀ t ∈ (vecSlice o.terms).val, inRange sys t = true

/-- Address validation accepts exactly the systems whose every operand stays in range. -/
theorem validateSpec_ok (sys : system.ConstraintSystem W) :
    validateSpec sys = .Ok () ↔
      (∀ r ∈ (vecSlice sys.zero_constraints).val, opIn sys r.value) ∧
      (∀ r ∈ (vecSlice sys.and_constraints).val,
        opIn sys r.left ∧ opIn sys r.right ∧ opIn sys r.output) ∧
      (∀ r ∈ (vecSlice sys.integer_mul_constraints).val,
        opIn sys r.left ∧ opIn sys r.right ∧ opIn sys r.low ∧ opIn sys r.high) := by
  unfold validateSpec
  rw [rthen_ok, rthen_ok,
    vfamSpec_ok _ (fun r => opIn sys r.value) (by intro i x; simp [zeroChk, opCheck_ok, opIn]),
    vfamSpec_ok _ (fun r => opIn sys r.left ∧ opIn sys r.right ∧ opIn sys r.output)
      (by intro i x; simp [andChk, rthen_ok, opCheck_ok, opIn]),
    vfamSpec_ok _ (fun r => opIn sys r.left ∧ opIn sys r.right ∧ opIn sys r.low ∧ opIn sys r.high)
      (by intro i x; simp [mulChk, rthen_ok, opCheck_ok, opIn])]

/-- The constructor succeeds exactly on bounded segments and families whose terms stay in range. -/
theorem system_new_ok (inst : word.Word W) (pl wl : Std.Usize)
    (z : CoreModels.alloc.vec.Vec (constraint.ZeroConstraint W))
    (a : CoreModels.alloc.vec.Vec (constraint.AndConstraint W))
    (m : CoreModels.alloc.vec.Vec (constraint.IntegerMulConstraint W))
    (s : system.ConstraintSystem W) :
    system.ConstraintSystem.new inst pl wl z a m = .ok (.Ok s) ↔
      pl.val < 2 ^ 32 ∧ wl.val < 2 ^ 32 ∧ (vecSlice z).val.length < 2 ^ 32 ∧
      (vecSlice a).val.length < 2 ^ 32 ∧ (vecSlice m).val.length < 2 ^ 32 ∧
      validateSpec (sysOf pl wl z a m) = .Ok () ∧ s = sysOf pl wl z a m := by
  rw [system_new_eq]
  unfold newSpec
  split_ifs with h1 h2 h3 h4 h5 <;> simp_all
  cases validateSpec (sysOf pl wl z a m) <;> simp [eq_comm]

end Plonky3Lean.Proofs.Word
