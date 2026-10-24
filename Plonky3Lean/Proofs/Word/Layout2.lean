module

public import Plonky3Lean.Proofs.Word.Composition

@[expose] public section

/-!
# The layout a composition records

Building a composition packs its calls' blocks one after the other.

Any segment or family past the address space is refused with an error.
-/

open Aeneas Aeneas.Std CoreModels p3_word
open Plonky3Lean.Lib

namespace Plonky3Lean.Proofs.Word

theorem checked_mul_eq (x y : Std.Usize) :
    CoreModels.core.num.Usize.checked_mul x y =
      .ok (if x.val * y.val < 2 ^ UScalarTy.Usize.numBits then .Some (uOf (x.val * y.val)) else .None) := by
  simp only [CoreModels.core.num.Usize.checked_mul, CoreModels.core.num.Usize.overflowing_mul,
    CoreModels.rust_primitives.arithmetic.overflowing_mul_usize, bind_ok,
    CoreModels.uoverflowing_mul]
  show (if decide (2 ^ UScalarTy.Usize.numBits ≤ x.val * y.val) = true then
      RustM.ok CoreModels.core.option.Option.None
    else RustM.ok (CoreModels.core.option.Option.Some (uOf (x.val * y.val)))) = _
  by_cases h : x.val * y.val < 2 ^ UScalarTy.Usize.numBits
  · rw [decide_eq_false (by omega)]; simp only [Bool.false_eq_true, ite_false, h, ite_true]
  · rw [decide_eq_true (by omega)]; simp only [ite_true, h, ite_false]

theorem checked_add_eq (x y : Std.Usize) :
    CoreModels.core.num.Usize.checked_add x y =
      .ok (if x.val + y.val < 2 ^ UScalarTy.Usize.numBits then .Some (uOf (x.val + y.val)) else .None) := by
  have h := overflowing_add_val x y
  simp only [UScalar.size] at h
  simp only [CoreModels.core.num.Usize.checked_add, CoreModels.core.num.Usize.overflowing_add,
    CoreModels.rust_primitives.arithmetic.overflowing_add_usize, bind_ok]
  generalize UScalar.overflowing_add x y = r at h ⊢
  obtain ⟨z, b⟩ := r
  obtain ⟨h1, h2⟩ := h
  simp only at h1 h2
  subst h1
  show (if decide (2 ^ UScalarTy.Usize.numBits ≤ x.val + y.val) = true then
      RustM.ok CoreModels.core.option.Option.None
    else RustM.ok (CoreModels.core.option.Option.Some z)) = _
  by_cases h : x.val + y.val < 2 ^ UScalarTy.Usize.numBits
  · rw [decide_eq_false (by omega)]; simp only [Bool.false_eq_true, ite_false, h, ite_true]
    exact congrArg _ (congrArg _ (UScalar.eq_of_val_eq (by rw [h2, uOf_val h, Nat.mod_eq_of_lt h])))
  · rw [decide_eq_true (by omega)]; simp only [ite_true, h, ite_false]

/-- Growing a segment by `slots * instances` words, or the oversized-segment error. -/
theorem extend_segment_eq (total slots m : Std.Usize) (seg : index.Segment) :
    component.CompositionError.extend_segment total slots m seg =
      .ok (if total.val + slots.val * m.val < 2 ^ UScalarTy.Usize.numBits then
        .Ok (uOf (total.val + slots.val * m.val))
      else .Err (.SegmentTooLong seg CoreModels.core.num.Usize.MAX)) := by
  simp only [component.CompositionError.extend_segment, checked_mul_eq, bind_ok]
  by_cases h1 : slots.val * m.val < 2 ^ UScalarTy.Usize.numBits
  · have hv : (uOf (slots.val * m.val)).val = slots.val * m.val := uOf_val h1
    simp only [h1, ite_true, CoreModels.core.option.Option.and_then,
      component.CompositionError.extend_segment.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeOptionUsize.call_once,
      checked_add_eq, hv, bind_ok]
    split_ifs <;> rfl
  · have : ¬ total.val + slots.val * m.val < 2 ^ UScalarTy.Usize.numBits := by omega
    simp only [h1, this, ite_false, CoreModels.core.option.Option.and_then,
      CoreModels.core.option.Option.ok_or, bind_ok]

/-- Growing a family by `count * instances` relations, or the oversized-family error. -/
theorem extend_family_eq (total count m : Std.Usize) (kind : system.ConstraintKind) :
    component.CompositionError.extend_family total count m kind =
      .ok (if total.val + count.val * m.val < 2 ^ UScalarTy.Usize.numBits then
        .Ok (uOf (total.val + count.val * m.val))
      else .Err (.TooManyConstraints kind CoreModels.core.num.Usize.MAX)) := by
  simp only [component.CompositionError.extend_family, checked_mul_eq, bind_ok]
  by_cases h1 : count.val * m.val < 2 ^ UScalarTy.Usize.numBits
  · have hv : (uOf (count.val * m.val)).val = count.val * m.val := uOf_val h1
    simp only [h1, ite_true, CoreModels.core.option.Option.and_then,
      component.CompositionError.extend_family.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeOptionUsize.call_once,
      checked_add_eq, hv, bind_ok]
    split_ifs <;> rfl
  · have : ¬ total.val + count.val * m.val < 2 ^ UScalarTy.Usize.numBits := by omega
    simp only [h1, this, ite_false, CoreModels.core.option.Option.and_then,
      CoreModels.core.option.Option.ok_or, bind_ok]

variable {W : Type}

theorem bound_segment_eq (len : Std.Usize) (seg : index.Segment) :
    component.CompositionError.bound_segment len seg =
      .ok (if len.val < 2 ^ 32 then .Ok (UScalar.cast .U32 len) else .Err (.SegmentTooLong seg len)) := by
  simp only [component.CompositionError.bound_segment, u32_try_from_eq, bind_ok]
  split_ifs <;> simp [CoreModels.core.result.Result.map_err,
    component.CompositionError.bound_segment.closure.Insts.CoreOpsFunctionFnOnceTupleTryFromIntErrorCompositionError.call_once]

theorem bound_family_eq (inst : word.Word W) (len : Std.Usize) (kind : system.ConstraintKind) :
    component.reshaped.Composition.bound_family inst len kind =
      .ok (if len.val < 2 ^ 32 then .Ok (UScalar.cast .U32 len)
        else .Err (.TooManyConstraints kind len)) := by
  simp only [component.reshaped.Composition.bound_family, u32_try_from_eq, bind_ok]
  split_ifs <;> simp [CoreModels.core.result.Result.map_err,
    component.reshaped.Composition.bound_family.closure.Insts.CoreOpsFunctionFnOnceTupleTryFromIntErrorCompositionError.call_once]

theorem relation_counts_eq (inst : word.Word W) (c : component.Component W) :
    component.Component.relation_counts inst c =
      .ok (Std.Array.make 3#usize [(vecSlice c.body.zero_constraints).len,
        (vecSlice c.body.and_constraints).len, (vecSlice c.body.integer_mul_constraints).len]) := by
  simp only [component.Component.relation_counts, system.ConstraintSystem.impl.zero_constraints,
    system.ConstraintSystem.impl.and_constraints, system.ConstraintSystem.impl.integer_mul_constraints,
    vec_deref_eq, bind_ok, CoreModels.core.slice.Slice.len, CoreModels.rust_primitives.slice.slice_length]

/-- A vector with one more item. -/
def vecPush {T : Type} (v : CoreModels.alloc.vec.Vec T) (x : T)
    (h : (vecSlice v).val.length + 1 ≤ Usize.max) : CoreModels.alloc.vec.Vec T :=
  Slice.from ((vecSlice v).val ++ [x]) (by simpa using h)

theorem vecPush_val {T : Type} (v : CoreModels.alloc.vec.Vec T) (x : T)
    (h : (vecSlice v).val.length + 1 ≤ Usize.max) :
    (vecSlice (vecPush v x h)).val = (vecSlice v).val ++ [x] := by
  simp [vecPush, vecSlice]

theorem vec_push_eq {T : Type} (v : CoreModels.alloc.vec.Vec T) (x : T)
    (h : (vecSlice v).val.length + 1 ≤ Usize.max) :
    CoreModels.alloc.vec.Vec.push v x = .ok (vecPush v x h) := by
  simp only [CoreModels.alloc.vec.Vec.push, CoreModels.rust_primitives.sequence.seq_push]
  rw [dite_eq_left (by simpa using h)]
  exact bind_tc_ok (α := _root_.rust_primitives.sequence.Seq T) _ _

theorem interface_slots_eq (inst : word.Word W) (c : component.ComponentCall W)
    (h : slotsP c < 2 ^ 32) :
    component.Component.interface_slots inst c.component = .ok (uOf (slotsP c)) :=
  segment_slots_eq inst c .Public h

theorem local_slots_eq (inst : word.Word W) (c : component.ComponentCall W) :
    component.Component.local_slots inst c.component = .ok (uOf (slotsW c)) := by
  have h := segment_slots_eq inst c .Witness c.component.body.witness_len.hBounds
  exact h

/-- The block sizes of a list of calls in a segment. -/
def zs (calls : List (component.ComponentCall W)) (seg : index.Segment) : List ℕ :=
  List.zipWith (· * ·) (calls.map (·.instances.val)) (calls.map (slotsOf · seg))

/-- The layout loop's state after `j` calls. -/
structure Inv (calls : List (component.ComponentCall W)) (j : ℕ) (P Wt : Std.Usize)
    (bases : CoreModels.alloc.vec.Vec component.CallBase) (idx : Std.Usize) : Prop where
  idx : idx.val = j
  le : j ≤ calls.length
  pub : P.val = pref (zs calls .Public) j
  wit : Wt.val = pref (zs calls .Witness) j
  blen : (vecSlice bases).val.length = j
  base : ∀ k (h : k < (vecSlice bases).val.length) seg,
    (baseOf (vecSlice bases).val[k] seg).val = pref (zs calls seg) k

theorem index3_0 {T : Type} (a b c : T) (h : [a, b, c].length = (3#usize).val) :
    Std.Array.index_usize (Std.Array.make 3#usize [a, b, c] h) 0#usize = .ok a :=
  index_make _ _ _ (by simp)

theorem index3_1 {T : Type} (a b c : T) (h : [a, b, c].length = (3#usize).val) :
    Std.Array.index_usize (Std.Array.make 3#usize [a, b, c] h) 1#usize = .ok b :=
  index_make _ _ _ (by simp)

theorem index3_2 {T : Type} (a b c : T) (h : [a, b, c].length = (3#usize).val) :
    Std.Array.index_usize (Std.Array.make 3#usize [a, b, c] h) 2#usize = .ok c :=
  index_make _ _ _ (by simp)

/-- What one step of the layout loop may return before the last call. -/
def StepOk (calls : List (component.ComponentCall W)) (j : ℕ)
    (x : ControlFlow (Std.Usize × Std.Usize × Std.Usize × Std.Usize × Std.Usize ×
      CoreModels.alloc.vec.Vec component.CallBase × Std.Usize)
      (CoreModels.core.result.Result (component.Composition W) component.CompositionError)) : Prop :=
  match x with
  | .cont (P, Wt, _, _, _, bases, idx) => Inv calls (j + 1) P Wt bases idx
  | .done r => ∀ comp, r ≠ .Ok comp

theorem new_body_step (inst : word.Word W) (callsV : CoreModels.alloc.vec.Vec (component.ComponentCall W))
    (hwf : ∀ c ∈ (vecSlice callsV).val, slotsP c < 2 ^ 32) {j : ℕ}
    {P Wt Z A Pr idx : Std.Usize} {bases : CoreModels.alloc.vec.Vec component.CallBase}
    (hinv : Inv (vecSlice callsV).val j P Wt bases idx) (hj : j < (vecSlice callsV).val.length) :
    ∃ x, component.reshaped.Composition.reshaped_new_loop.body inst callsV P Wt Z A Pr bases idx =
      .ok x ∧ StepOk (vecSlice callsV).val j x := by
  have hlt : idx < (vecSlice callsV).len := by rw [UScalar.lt_equiv]; simp [hinv.idx, hj]
  have hidx : idx.val < callsV.val.length := by rw [hinv.idx]; exact hj
  set c := (vecSlice callsV).val[j] with hc
  have hcj : callsV.val[idx.val] = c := by simp [hc, hinv.idx]
  simp only [component.reshaped.Composition.reshaped_new_loop.body, vec_len_eq, bind_ok, hlt,
    ite_true, vec_index_eq callsV idx hidx, hcj, u32_try_from_eq]
  have hmax : (vecSlice bases).val.length + 1 ≤ Usize.max := by
    have h1 := callsV.property
    have h2 : (vecSlice callsV).val.length = callsV.val.length := rfl
    rw [hinv.blen]; omega
  have hw := hwf c (List.getElem_mem hj)
  by_cases hm : c.instances.val < 2 ^ 32
  · simp only [hm, ite_true, CoreModels.core.result.Result.is_err, bind_ok, Bool.false_eq_true,
      ite_false, vec_push_eq bases _ hmax, relation_counts_eq, interface_slots_eq inst c hw,
      local_slots_eq, extend_segment_eq, extend_family_eq]
    have h32 := two_pow_32_le
    have hsw : slotsW c < 2 ^ 32 := c.component.body.witness_len.hBounds
    have hn : idx.val + 1 < 2 ^ UScalarTy.Usize.numBits := by
      have h1 := callsV.property
      have h2 : (vecSlice callsV).val.length = callsV.val.length := rfl
      rw [← UScalar.max_USize_eq] at h1; simp only [UScalar.max] at h1; omega
    simp only [uOf_val (show slotsP c < 2 ^ UScalarTy.Usize.numBits by omega),
      uOf_val (show slotsW c < 2 ^ UScalarTy.Usize.numBits by omega),
      index3_0, index3_1, index3_2, succ_eq idx hn]
    split_ifs with h1 h2
    all_goals simp (config := { failIfUnchanged := false }) only [CoreModels.core.result.Result.Insts.CoreOpsTry_traitTryTResultInfallibleE.branch,
      CoreModels.core.result.Result.Insts.CoreOpsTry_traitFromResidualResultInfallibleE.from_residual,
      CoreModels.core.convert.From.Blanket.from, bind_ok, RustM.ok.injEq, exists_eq_left',
      StepOk, ne_eq, reduceCtorEq, not_false_eq_true, implies_true]
    all_goals (try split_ifs)
    all_goals simp (config := { failIfUnchanged := false }) only [CoreModels.core.result.Result.Insts.CoreOpsTry_traitTryTResultInfallibleE.branch,
      CoreModels.core.result.Result.Insts.CoreOpsTry_traitFromResidualResultInfallibleE.from_residual,
      CoreModels.core.convert.From.Blanket.from, bind_ok, RustM.ok.injEq, exists_eq_left',
      reduceCtorEq, not_false_eq_true, implies_true]
    have hzlen : ∀ seg, j < (zs (vecSlice callsV).val seg).length := by intro seg; simp [zs, hj]
    have hzj : ∀ seg, (zs (vecSlice callsV).val seg)[j]'(hzlen seg) = c.instances.val * slotsOf c seg := by
      intro seg; simp [zs, hc]
    refine ⟨by rw [uOf_val hn, hinv.idx], hj, ?_, ?_, ?_, ?_⟩
    · rw [uOf_val (by omega), pref_succ _ _ (hzlen _), hzj, ← hinv.pub]; simp only [slotsOf]; ring
    · rw [uOf_val (by omega), pref_succ _ _ (hzlen _), hzj, ← hinv.wit]; simp only [slotsOf]; ring
    · rw [vecPush_val]; simp [hinv.blen]
    · intro k hk seg
      simp only [vecPush_val] at hk ⊢
      rw [List.length_append, hinv.blen] at hk
      by_cases hkj : k < j
      · rw [List.getElem_append_left (by rw [hinv.blen]; exact hkj)]
        exact hinv.base k (by rw [hinv.blen]; exact hkj) seg
      · have hk' : k = j := by simp at hk; omega
        subst hk'
        rw [List.getElem_append_right (by rw [hinv.blen])]
        simp only [hinv.blen, Nat.sub_self, List.getElem_cons_zero]
        cases seg
        · exact hinv.pub
        · exact hinv.wit
  · refine ⟨.done (.Err (.TooManyInstances idx c.instances)),
      by simp [show ¬ c.instances.val < 4294967296 from hm, CoreModels.core.result.Result.is_err], ?_⟩
    simp [StepOk]

/-- What the layout loop may return: an error, or a laid-out composition of the given calls. -/
def NewOk (callsV : CoreModels.alloc.vec.Vec (component.ComponentCall W))
    (r : CoreModels.core.result.Result (component.Composition W) component.CompositionError) : Prop :=
  ∀ comp, r = .Ok comp → LaidOut comp ∧ comp.calls = callsV

theorem pref_length (sizes : List ℕ) : pref sizes sizes.length = sizes.sum := by
  simp [pref]

theorem new_body_last (inst : word.Word W) (callsV : CoreModels.alloc.vec.Vec (component.ComponentCall W))
    {P Wt Z A Pr idx : Std.Usize} {bases : CoreModels.alloc.vec.Vec component.CallBase}
    (hinv : Inv (vecSlice callsV).val (vecSlice callsV).val.length P Wt bases idx) :
    ∃ r, component.reshaped.Composition.reshaped_new_loop.body inst callsV P Wt Z A Pr bases idx =
      .ok (.done r) ∧ NewOk callsV r := by
  have hnlt : ¬ idx < (vecSlice callsV).len := by rw [UScalar.lt_equiv]; simp [hinv.idx]
  simp only [component.reshaped.Composition.reshaped_new_loop.body, vec_len_eq, bind_ok, hnlt,
    ite_false, bound_segment_eq, bound_family_eq]
  split_ifs with h1 h2
  all_goals simp (config := { failIfUnchanged := false }) only [
    CoreModels.core.result.Result.Insts.CoreOpsTry_traitTryTResultInfallibleE.branch,
    CoreModels.core.result.Result.Insts.CoreOpsTry_traitFromResidualResultInfallibleE.from_residual,
    CoreModels.core.convert.From.Blanket.from, bind_ok, RustM.ok.injEq, ControlFlow.done.injEq,
    exists_eq_left', NewOk, reduceCtorEq, false_imp_iff, implies_true]
  intro comp hcomp
  cases hcomp
  refine ⟨⟨?_, ?_, ?_⟩, rfl⟩
  · exact hinv.blen
  · intro k hk seg
    exact hinv.base k hk seg
  · intro seg
    change (zs (vecSlice callsV).val seg).sum = _
    rw [← pref_length, show (zs (vecSlice callsV).val seg).length = (vecSlice callsV).val.length by
      simp [zs]]
    cases seg
    · rw [← hinv.pub]; exact (cast_u32_val P (by omega)).symm
    · rw [← hinv.wit]; exact (cast_u32_val Wt (by omega)).symm

/-- The empty vector. -/
def emptyVec (T : Type) : CoreModels.alloc.vec.Vec T := Slice.new T

theorem new_loop (inst : word.Word W) (callsV : CoreModels.alloc.vec.Vec (component.ComponentCall W))
    (hwf : ∀ c ∈ (vecSlice callsV).val, slotsP c < 2 ^ 32) :
    ∀ m j (P Wt Z A Pr idx : Std.Usize) (bases : CoreModels.alloc.vec.Vec component.CallBase),
      (vecSlice callsV).val.length - j = m → Inv (vecSlice callsV).val j P Wt bases idx →
      ∃ r, component.reshaped.Composition.reshaped_new_loop inst callsV P Wt Z A Pr bases idx =
        .ok r ∧ NewOk callsV r := by
  intro m
  induction m with
  | zero =>
    intro j P Wt Z A Pr idx bases hm hinv
    have hj : j = (vecSlice callsV).val.length := by have := hinv.le; omega
    subst hj
    obtain ⟨r, hb, hr⟩ := new_body_last inst callsV (Z := Z) (A := A) (Pr := Pr) hinv
    refine ⟨r, ?_, hr⟩
    rw [component.reshaped.Composition.reshaped_new_loop, loop]
    simp only [hb, bind_ok]
  | succ m ih =>
    intro j P Wt Z A Pr idx bases hm hinv
    obtain ⟨x, hb, hx⟩ := new_body_step inst callsV hwf (Z := Z) (A := A) (Pr := Pr) hinv (by omega)
    rw [component.reshaped.Composition.reshaped_new_loop, loop]
    simp only [hb, bind_ok]
    match x, hx with
    | .done r, hx => exact ⟨r, rfl, fun comp h => absurd h (hx comp)⟩
    | .cont (P', Wt', Z', A', Pr', bases', idx'), hx =>
      exact ih (j + 1) P' Wt' Z' A' Pr' idx' bases' (by omega) hx

/-- Building a composition from well-formed calls never panics.

When it succeeds, the composition holds the given calls and is laid out. -/
theorem composition_new_laid_out (inst : word.Word W)
    (callsV : CoreModels.alloc.vec.Vec (component.ComponentCall W))
    (hwf : ∀ c ∈ (vecSlice callsV).val, slotsP c < 2 ^ 32) :
    ∃ r, component.Composition.new inst callsV = .ok r ∧
      ∀ comp, r = .Ok comp → LaidOut comp ∧ comp.calls = callsV := by
  simp only [component.Composition.new, component.reshaped.Composition.reshaped_new, vec_len_eq,
    bind_ok, CoreModels.alloc.vec.Vec.with_capacity, CoreModels.alloc.vec.Vec.new]
  have hinv : Inv (vecSlice callsV).val 0 0#usize 0#usize (emptyVec component.CallBase) 0#usize :=
    ⟨rfl, Nat.zero_le _, rfl, rfl, rfl, fun k hk => absurd hk (by simp [emptyVec])⟩
  obtain ⟨r, hr, hn⟩ := new_loop inst callsV hwf _ 0 0#usize 0#usize 0#usize 0#usize 0#usize 0#usize
    (emptyVec component.CallBase) rfl hinv
  refine ⟨r, ?_, hn⟩
  rw [← hr]
  have hin : (do let s ← CoreModels.rust_primitives.sequence.seq_empty component.CallBase; RustM.ok s :
      RustM (CoreModels.alloc.vec.Vec component.CallBase)) = .ok (emptyVec component.CallBase) :=
    bind_tc_ok (α := _root_.rust_primitives.sequence.Seq component.CallBase) _ _
  rw [hin]
  exact bind_tc_ok (α := CoreModels.alloc.vec.Vec component.CallBase) _ _

/-- Declaring a gadget: its interface must add up without overflow and cover its public segment exactly.

- Two widths whose sum overflows are refused as too wide.
- A sum other than the body's public length is refused as a mismatch.
- Otherwise the gadget keeps both widths. -/
theorem component_new_eq (inst : word.Word W) (body : system.ConstraintSystem W) (i o : Std.Usize) :
    component.Component.new inst body i o = .ok
      (if i.val + o.val < 2 ^ UScalarTy.Usize.numBits then
        (if i.val + o.val = body.public_len.val then
          .Ok ⟨body, UScalar.cast .U32 i, UScalar.cast .U32 o⟩
        else .Err (.InterfaceMismatch i o (UScalar.cast .Usize body.public_len)))
      else .Err (.InterfaceTooWide i o)) := by
  have h32 := two_pow_32_le
  have hb : (UScalar.cast .Usize body.public_len).val = body.public_len.val :=
    cast_usize_val _ (by decide)
  simp only [component.Component.new, checked_add_eq, bind_ok, system.ConstraintSystem.impl.public_len]
  by_cases h1 : i.val + o.val < 2 ^ UScalarTy.Usize.numBits
  · have hv : (uOf (i.val + o.val)).val = i.val + o.val := uOf_val h1
    simp only [h1, ite_true, CoreModels.core.option.Option.ok_or, bind_ok,
      CoreModels.core.result.Result.Insts.CoreOpsTry_traitTryTResultInfallibleE.branch, bne_iff_ne,
      ne_eq, UScalar.eq_equiv, hv, hb, lift_eq]
    split_ifs <;> rfl
  · simp only [h1, ite_false, CoreModels.core.option.Option.ok_or, bind_ok,
      CoreModels.core.result.Result.Insts.CoreOpsTry_traitTryTResultInfallibleE.branch,
      CoreModels.core.result.Result.Insts.CoreOpsTry_traitFromResidualResultInfallibleE.from_residual,
      CoreModels.core.convert.From.Blanket.from]

/-- A declared gadget's interface fits in 32 bits, as the layout needs. -/
theorem component_new_slots {inst : word.Word W} {body : system.ConstraintSystem W} {i o : Std.Usize}
    {comp : component.Component W} (h : component.Component.new inst body i o = .ok (.Ok comp))
    (m : Std.Usize) : slotsP ⟨comp, m⟩ < 2 ^ 32 := by
  rw [component_new_eq, RustM.ok.injEq] at h
  have hp : body.public_len.val < 2 ^ 32 := body.public_len.hBounds
  split_ifs at h with h1 h2
  cases h
  simp only [slotsP]
  rw [cast_u32_val _ (by omega), cast_u32_val _ (by omega)]
  omega

end Plonky3Lean.Proofs.Word
