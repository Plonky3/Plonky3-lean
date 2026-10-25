module

public import Plonky3Lean.Proofs.Word.Layout2
public import Plonky3Lean.Proofs.Word.Validate

@[expose] public section

/-!
# Lowering a composition to one flat system

Lowering copies every relation of every instance of every call into one system.

Each copy reads its words at the composed addresses of its instance:

```text
    slot s of instance i of call k   ->   block start of call k + i * width + s
```

The families keep their order: calls in order, then instances, then the body's relations.

A flat witness satisfies the lowered system exactly when every instance's body holds on its own block.
-/

open Aeneas Aeneas.Std CoreModels p3_word
open Plonky3Lean.Lib

namespace Plonky3Lean.Proofs.Word

variable {W : Type}

theorem vec_with_capacity_eq {T : Type} (c : Std.Usize) :
    CoreModels.alloc.vec.Vec.with_capacity T c = .ok (emptyVec T) := by
  simp only [CoreModels.alloc.vec.Vec.with_capacity, CoreModels.alloc.vec.Vec.new,
    CoreModels.rust_primitives.sequence.seq_empty]
  exact (bind_tc_ok _ _).trans rfl

theorem usize_max_eq : Usize.max + 1 = 2 ^ UScalarTy.Usize.numBits := by
  rw [← UScalar.max_USize_eq]; simp only [UScalar.max]; have := Nat.two_pow_pos UScalarTy.Usize.numBits
  omega

theorem usize_max_lt : Usize.max < 2 ^ UScalarTy.Usize.numBits := by
  have := usize_max_eq; omega

theorem slice_len_eq {T : Type} (s : Slice T) : CoreModels.core.slice.Slice.len s = .ok s.len := rfl

/-- A loop that pushes the image of each item of a list returns the pushed vector. -/
theorem push_loop {R T : Type} (xs : List R) (g : R → T) (hxs : xs.length ≤ Usize.max)
    (body : CoreModels.alloc.vec.Vec T × Std.Usize →
      RustM (ControlFlow (CoreModels.alloc.vec.Vec T × Std.Usize) (CoreModels.alloc.vec.Vec T)))
    (hstep : ∀ acc (j : Std.Usize) (hj : j.val < xs.length)
      (h : (vecSlice acc).val.length + 1 ≤ Usize.max),
      body (acc, j) = .ok (.cont (vecPush acc (g xs[j.val]) h, uOf (j.val + 1))))
    (hdone : ∀ acc (j : Std.Usize), j.val = xs.length → body (acc, j) = .ok (.done acc)) :
    ∀ n acc (j : Std.Usize), xs.length - j.val = n → j.val ≤ xs.length →
      (vecSlice acc).val.length + (xs.length - j.val) ≤ Usize.max →
      ∃ v, loop body (acc, j) = .ok v ∧
        (vecSlice v).val = (vecSlice acc).val ++ (xs.drop j.val).map g := by
  have hm := usize_max_lt
  intro n
  induction n with
  | zero =>
    intro acc j hn hj _
    refine ⟨acc, by rw [loop, hdone acc j (by omega), bind_ok], ?_⟩
    simp [List.drop_eq_nil_of_le (show xs.length ≤ j.val by omega)]
  | succ n ih =>
    intro acc j hn hj hb
    have hlt : j.val < xs.length := by omega
    have h1 : (vecSlice acc).val.length + 1 ≤ Usize.max := by omega
    have hu : (uOf (j.val + 1)).val = j.val + 1 := uOf_val (by omega)
    obtain ⟨v, hv, hval⟩ := ih (vecPush acc (g xs[j.val]) h1) (uOf (j.val + 1)) (by omega)
      (by omega) (by rw [vecPush_val, hu]; simp; omega)
    refine ⟨v, by rw [loop, hstep acc j hlt h1, bind_ok]; exact hv, ?_⟩
    rw [hval, vecPush_val, hu, List.drop_eq_getElem_cons hlt]
    simp only [List.map_cons, List.append_assoc, List.singleton_append]

/-! ## Moving one instance's relations to their composed addresses -/

/-- The composed address of a local address of instance `i` of call `k`. -/
def remapIdx (comp : component.Composition W) (k i : ℕ) (idx : index.ValueIndex) : index.ValueIndex :=
  ⟨idx.segment, ⟨BitVec.ofNat 32 (packed (counts comp) (widths comp idx.segment) k i idx.position.val)⟩⟩

/-- A term read at its composed address. -/
def remapTerm (comp : component.Composition W) (k i : ℕ) (t : shift.ShiftedValue W) :
    shift.ShiftedValue W :=
  { t with index := remapIdx comp k i t.index }

/-- An operand read at its composed addresses. -/
def remapOp (comp : component.Composition W) (k i : ℕ) (o : constraint.Operand W) :
    constraint.Operand W :=
  ⟨Slice.from ((vecSlice o.terms).val.map (remapTerm comp k i)) (by simp)⟩

theorem remapOp_terms (comp : component.Composition W) (k i : ℕ) (o : constraint.Operand W) :
    (vecSlice (remapOp comp k i o).terms).val = (vecSlice o.terms).val.map (remapTerm comp k i) := by
  simp [remapOp, vecSlice]

/-- Every term of an operand lies inside one instance's block of a call. -/
def OpFits (c : component.ComponentCall W) (o : constraint.Operand W) : Prop :=
  ∀ t ∈ (vecSlice o.terms).val, t.index.position.val < slotsOf c t.index.segment

theorem lenOf_lt (comp : component.Composition W) (seg : index.Segment) : lenOf comp seg < 2 ^ 32 := by
  cases seg
  · exact comp.public_len.hBounds
  · exact comp.witness_len.hBounds

/-- A slot inside an instance's block has its packed position inside the composed segment. -/
theorem packed_lt (comp : component.Composition W) (hl : LaidOut comp) {k i s : ℕ} (seg : index.Segment)
    (hk : k < (callsOf comp).length) (hi : i < ((callsOf comp)[k]).instances.val)
    (hs : s < slotsOf (callsOf comp)[k] seg) :
    packed (counts comp) (widths comp seg) k i s < lenOf comp seg := by
  have t := packed_lt_total (counts comp) (widths comp seg) (by simp [counts, widths]) (k := k)
    (i := i) (s := s) (by simp [counts, hk])
    (by simp [counts, hk, List.getD_eq_getElem?_getD]; exact hi)
    (by simp [widths, hk, List.getD_eq_getElem?_getD]; exact hs)
  rwa [hl.total] at t

theorem remap_operand_eq (inst : word.Word W) (comp : component.Composition W) (hl : LaidOut comp)
    {k : ℕ} (hk : k < (callsOf comp).length) (i : Std.Usize)
    (hi : i.val < ((callsOf comp)[k]).instances.val) (o : constraint.Operand W)
    (hfit : OpFits (callsOf comp)[k] o) :
    component.reshaped.Composition.remap_operand inst comp ((basesOf comp)[k]'(hl.len ▸ hk))
      ((callsOf comp)[k]).component i o = .ok (remapOp comp k i.val o) := by
  have h32 := two_pow_32_le
  have hblock := block_le comp hl hk
  set c := (callsOf comp)[k] with hc
  have hkb : k < (basesOf comp).length := hl.len ▸ hk
  simp only [component.reshaped.Composition.remap_operand, constraint.Operand.impl.terms, vec_deref_eq,
    bind_ok, slice_len_eq, vec_with_capacity_eq]
  obtain ⟨v, hv, hval⟩ := push_loop (vecSlice o.terms).val (remapTerm comp k i.val)
    (vecSlice o.terms).property
    (fun (m, t) => component.reshaped.Composition.remap_operand_loop.body inst comp
      ((basesOf comp)[k]'hkb) c.component i (vecSlice o.terms) m t) (fun acc j hj h => by
      have ht := hfit _ (List.getElem_mem hj)
      set t := (vecSlice o.terms).val[j.val] with htdef
      have hw : slotsOf c t.index.segment < 2 ^ 32 := by
        have := hblock t.index.segment
        have : slotsOf c t.index.segment ≤ c.instances.val * slotsOf c t.index.segment :=
          Nat.le_mul_of_pos_left _ (by omega)
        omega
      have hp := packed_lt comp hl t.index.segment hk hi ht
      have hlen := lenOf_lt comp t.index.segment
      have hbase := hl.base k hkb t.index.segment
      have hgw : (widths comp t.index.segment).getD k 0 = slotsOf c t.index.segment := by
        simp [widths, hk, hc, List.getD_eq_getElem?_getD]
      have hpe : packed (counts comp) (widths comp t.index.segment) k i.val t.index.position.val =
          (baseOf (basesOf comp)[k] t.index.segment).val + i.val * slotsOf c t.index.segment +
            t.index.position.val := by
        rw [hbase, packed, hgw]
      have hlt : j < (vecSlice o.terms).len := by rw [UScalar.lt_equiv]; simpa using hj
      simp only [component.reshaped.Composition.remap_operand_loop.body, slice_len_eq, hlt, ite_true,
        bind_ok, slice_index_eq _ _ hj, ← htdef, shift.ShiftedValue.impl.index,
        index.ValueIndex.impl.segment]
      rw [position_eq inst comp _ c i t.index hw (by omega), bind_ok, ← hpe,
        composed_index_eq inst _ _ (by omega), bind_ok]
      simp only [shift.ShiftedValue.with_index, bind_ok, vec_push_eq _ _ h,
        succ_eq j (by have := usize_max_lt; have := (vecSlice o.terms).property; omega)]
      rfl)
    (fun acc j hj => by
      have hlt : ¬ j < (vecSlice o.terms).len := by rw [UScalar.lt_equiv]; simp [hj]
      simp only [component.reshaped.Composition.remap_operand_loop.body, slice_len_eq, bind_ok, hlt,
        ite_false]) _ (emptyVec _) 0#usize rfl (by simp) (by simp [emptyVec])
  simp only [component.reshaped.Composition.remap_operand_loop]
  erw [hv, bind_ok]
  simp only [constraint.Operand.new, remapOp]
  congr 2
  apply Slice.ext
  simpa [emptyVec, vecSlice] using hval

/-! ## One instance's relations -/

/-- A zero relation read at the composed addresses of instance `i` of call `k`. -/
def remapZero (comp : component.Composition W) (k i : ℕ) (r : constraint.ZeroConstraint W) :
    constraint.ZeroConstraint W := ⟨remapOp comp k i r.value⟩

/-- An AND relation read at the composed addresses of instance `i` of call `k`. -/
def remapAnd (comp : component.Composition W) (k i : ℕ) (r : constraint.AndConstraint W) :
    constraint.AndConstraint W :=
  ⟨remapOp comp k i r.left, remapOp comp k i r.right, remapOp comp k i r.output⟩

/-- A product relation read at the composed addresses of instance `i` of call `k`. -/
def remapMul (comp : component.Composition W) (k i : ℕ) (r : constraint.IntegerMulConstraint W) :
    constraint.IntegerMulConstraint W :=
  ⟨remapOp comp k i r.left, remapOp comp k i r.right, remapOp comp k i r.low, remapOp comp k i r.high⟩

/-- The zero relations of a call's body. -/
abbrev zerosOf (c : component.ComponentCall W) := (vecSlice c.component.body.zero_constraints).val

/-- The AND relations of a call's body. -/
abbrev andsOf (c : component.ComponentCall W) := (vecSlice c.component.body.and_constraints).val

/-- The product relations of a call's body. -/
abbrev mulsOf (c : component.ComponentCall W) := (vecSlice c.component.body.integer_mul_constraints).val

/-- Every operand of a call's body lies inside one instance's block. -/
structure BodyFits (c : component.ComponentCall W) : Prop where
  zero : ∀ r ∈ zerosOf c, OpFits c r.value
  and : ∀ r ∈ andsOf c, OpFits c r.left ∧ OpFits c r.right ∧ OpFits c r.output
  mul : ∀ r ∈ mulsOf c, OpFits c r.left ∧ OpFits c r.right ∧ OpFits c r.low ∧ OpFits c r.high

section Family

variable (inst : word.Word W) (comp : component.Composition W) (hl : LaidOut comp) {k : ℕ}
  (hk : k < (callsOf comp).length) (i : Std.Usize) (hi : i.val < ((callsOf comp)[k]).instances.val)
  (hfit : BodyFits (callsOf comp)[k])
include hl hi hfit

theorem lower_zero_eq (acc : CoreModels.alloc.vec.Vec (constraint.ZeroConstraint W))
    (hb : (vecSlice acc).val.length + (zerosOf (callsOf comp)[k]).length ≤ Usize.max) :
    ∃ v, component.reshaped.Composition.lower_zero inst comp ((basesOf comp)[k]'(hl.len ▸ hk))
      ((callsOf comp)[k]).component i acc = .ok v ∧
      (vecSlice v).val = (vecSlice acc).val ++ (zerosOf (callsOf comp)[k]).map (remapZero comp k i.val) := by
  have hs := (vecSlice ((callsOf comp)[k]).component.body.zero_constraints).property
  obtain ⟨v, hv, hval⟩ := push_loop (zerosOf (callsOf comp)[k]) (remapZero comp k i.val) hs
    (fun (m, t) => component.reshaped.Composition.lower_zero_loop.body inst comp
      ((basesOf comp)[k]'(hl.len ▸ hk)) ((callsOf comp)[k]).component i
      (vecSlice ((callsOf comp)[k]).component.body.zero_constraints) m t) (fun acc j hj h => by
      have hlt : j < (vecSlice ((callsOf comp)[k]).component.body.zero_constraints).len := by
        rw [UScalar.lt_equiv]; simpa using hj
      simp only [component.reshaped.Composition.lower_zero_loop.body, slice_len_eq, bind_ok, hlt,
        ite_true, slice_index_eq _ _ hj, constraint.ZeroConstraint.impl.value,
        remap_operand_eq inst comp hl hk i hi _ (hfit.zero _ (List.getElem_mem hj)),
        constraint.ZeroConstraint.new, vec_push_eq _ _ h, succ_eq j (by have := usize_max_lt; omega)]
      rfl)
    (fun acc j hj => by
      have hlt : ¬ j < (vecSlice ((callsOf comp)[k]).component.body.zero_constraints).len := by
        rw [UScalar.lt_equiv]; simp [hj]
      simp only [component.reshaped.Composition.lower_zero_loop.body, slice_len_eq, bind_ok, hlt,
        ite_false]) _ acc 0#usize rfl (by simp) (by simpa using hb)
  refine ⟨v, ?_, by simpa using hval⟩
  simp only [component.reshaped.Composition.lower_zero, component.Component.impl.body,
    system.ConstraintSystem.impl.zero_constraints, vec_deref_eq, bind_ok,
    component.reshaped.Composition.lower_zero_loop]
  exact hv

theorem lower_and_eq (acc : CoreModels.alloc.vec.Vec (constraint.AndConstraint W))
    (hb : (vecSlice acc).val.length + (andsOf (callsOf comp)[k]).length ≤ Usize.max) :
    ∃ v, component.reshaped.Composition.lower_and inst comp ((basesOf comp)[k]'(hl.len ▸ hk))
      ((callsOf comp)[k]).component i acc = .ok v ∧
      (vecSlice v).val = (vecSlice acc).val ++ (andsOf (callsOf comp)[k]).map (remapAnd comp k i.val) := by
  have hs := (vecSlice ((callsOf comp)[k]).component.body.and_constraints).property
  obtain ⟨v, hv, hval⟩ := push_loop (andsOf (callsOf comp)[k]) (remapAnd comp k i.val) hs
    (fun (m, t) => component.reshaped.Composition.lower_and_loop.body inst comp
      ((basesOf comp)[k]'(hl.len ▸ hk)) ((callsOf comp)[k]).component i
      (vecSlice ((callsOf comp)[k]).component.body.and_constraints) m t) (fun acc j hj h => by
      have hlt : j < (vecSlice ((callsOf comp)[k]).component.body.and_constraints).len := by
        rw [UScalar.lt_equiv]; simpa using hj
      have hf := hfit.and _ (List.getElem_mem hj)
      simp only [component.reshaped.Composition.lower_and_loop.body, slice_len_eq, bind_ok, hlt,
        ite_true, slice_index_eq _ _ hj, constraint.AndConstraint.impl.left,
        constraint.AndConstraint.impl.right, constraint.AndConstraint.impl.output,
        remap_operand_eq inst comp hl hk i hi _ hf.1, remap_operand_eq inst comp hl hk i hi _ hf.2.1,
        remap_operand_eq inst comp hl hk i hi _ hf.2.2,
        constraint.AndConstraint.new, vec_push_eq _ _ h, succ_eq j (by have := usize_max_lt; omega)]
      rfl)
    (fun acc j hj => by
      have hlt : ¬ j < (vecSlice ((callsOf comp)[k]).component.body.and_constraints).len := by
        rw [UScalar.lt_equiv]; simp [hj]
      simp only [component.reshaped.Composition.lower_and_loop.body, slice_len_eq, bind_ok, hlt,
        ite_false]) _ acc 0#usize rfl (by simp) (by simpa using hb)
  refine ⟨v, ?_, by simpa using hval⟩
  simp only [component.reshaped.Composition.lower_and, component.Component.impl.body,
    system.ConstraintSystem.impl.and_constraints, vec_deref_eq, bind_ok,
    component.reshaped.Composition.lower_and_loop]
  exact hv

theorem lower_product_eq (acc : CoreModels.alloc.vec.Vec (constraint.IntegerMulConstraint W))
    (hb : (vecSlice acc).val.length + (mulsOf (callsOf comp)[k]).length ≤ Usize.max) :
    ∃ v, component.reshaped.Composition.lower_product inst comp ((basesOf comp)[k]'(hl.len ▸ hk))
      ((callsOf comp)[k]).component i acc = .ok v ∧
      (vecSlice v).val = (vecSlice acc).val ++ (mulsOf (callsOf comp)[k]).map (remapMul comp k i.val) := by
  have hs := (vecSlice ((callsOf comp)[k]).component.body.integer_mul_constraints).property
  obtain ⟨v, hv, hval⟩ := push_loop (mulsOf (callsOf comp)[k]) (remapMul comp k i.val) hs
    (fun (m, t) => component.reshaped.Composition.lower_product_loop.body inst comp
      ((basesOf comp)[k]'(hl.len ▸ hk)) ((callsOf comp)[k]).component i
      (vecSlice ((callsOf comp)[k]).component.body.integer_mul_constraints) m t) (fun acc j hj h => by
      have hlt : j < (vecSlice ((callsOf comp)[k]).component.body.integer_mul_constraints).len := by
        rw [UScalar.lt_equiv]; simpa using hj
      have hf := hfit.mul _ (List.getElem_mem hj)
      simp only [component.reshaped.Composition.lower_product_loop.body, slice_len_eq, bind_ok, hlt,
        ite_true, slice_index_eq _ _ hj, constraint.IntegerMulConstraint.impl.left,
        constraint.IntegerMulConstraint.impl.right, constraint.IntegerMulConstraint.impl.low,
        constraint.IntegerMulConstraint.impl.high,
        remap_operand_eq inst comp hl hk i hi _ hf.1, remap_operand_eq inst comp hl hk i hi _ hf.2.1,
        remap_operand_eq inst comp hl hk i hi _ hf.2.2.1, remap_operand_eq inst comp hl hk i hi _ hf.2.2.2,
        constraint.IntegerMulConstraint.new, vec_push_eq _ _ h, succ_eq j (by have := usize_max_lt; omega)]
      rfl)
    (fun acc j hj => by
      have hlt : ¬ j < (vecSlice ((callsOf comp)[k]).component.body.integer_mul_constraints).len := by
        rw [UScalar.lt_equiv]; simp [hj]
      simp only [component.reshaped.Composition.lower_product_loop.body, slice_len_eq, bind_ok, hlt,
        ite_false]) _ acc 0#usize rfl (by simp) (by simpa using hb)
  refine ⟨v, ?_, by simpa using hval⟩
  simp only [component.reshaped.Composition.lower_product, component.Component.impl.body,
    system.ConstraintSystem.impl.integer_mul_constraints, vec_deref_eq, bind_ok,
    component.reshaped.Composition.lower_product_loop]
  exact hv

end Family

/-! ## One call, instance by instance -/

/-- The relations of instances `j` to `j + n - 1`, instance by instance. -/
def callRels {R : Type} (fam : List R) (f : ℕ → R → R) (j n : ℕ) : List R :=
  (List.range' j n).flatMap fun i => fam.map (f i)

theorem callRels_length {R : Type} (fam : List R) (f : ℕ → R → R) (j n : ℕ) :
    (callRels fam f j n).length = n * fam.length := by
  induction n generalizing j with
  | zero => simp [callRels]
  | succ n ih =>
    simp only [callRels, List.range'_succ, List.flatMap_cons, List.length_append, List.length_map] at ih ⊢
    rw [ih]; ring

theorem callRels_succ {R : Type} (fam : List R) (f : ℕ → R → R) (j n : ℕ) :
    callRels fam f j (n + 1) = fam.map (f j) ++ callRels fam f (j + 1) n := by
  simp [callRels, List.range'_succ]

theorem lower_call_loop_eq (inst : word.Word W) (comp : component.Composition W) (hl : LaidOut comp)
    {k : ℕ} (hk : k < (callsOf comp).length) (hfit : BodyFits (callsOf comp)[k]) :
    ∀ n Z A P (j : Std.Usize), ((callsOf comp)[k]).instances.val - j.val = n →
      j.val ≤ ((callsOf comp)[k]).instances.val →
      (vecSlice Z).val.length + n * (zerosOf (callsOf comp)[k]).length ≤ Usize.max →
      (vecSlice A).val.length + n * (andsOf (callsOf comp)[k]).length ≤ Usize.max →
      (vecSlice P).val.length + n * (mulsOf (callsOf comp)[k]).length ≤ Usize.max →
      ∃ Z' A' P', component.reshaped.Composition.lower_call_loop inst comp.calls comp.bases
        comp.public_len comp.witness_len comp.relation_counts Z A P (callsOf comp)[k]
        ((basesOf comp)[k]'(hl.len ▸ hk)) j = .ok (Z', A', P') ∧
        (vecSlice Z').val = (vecSlice Z).val ++
          callRels (zerosOf (callsOf comp)[k]) (remapZero comp k) j.val n ∧
        (vecSlice A').val = (vecSlice A).val ++
          callRels (andsOf (callsOf comp)[k]) (remapAnd comp k) j.val n ∧
        (vecSlice P').val = (vecSlice P).val ++
          callRels (mulsOf (callsOf comp)[k]) (remapMul comp k) j.val n := by
  have hm := usize_max_lt
  have hiv := ((callsOf comp)[k]).instances.hBounds
  intro n
  induction n with
  | zero =>
    intro Z A P j hn hj _ _ _
    have hnlt : ¬ j < ((callsOf comp)[k]).instances := by rw [UScalar.lt_equiv]; omega
    refine ⟨Z, A, P, ?_, by simp [callRels], by simp [callRels], by simp [callRels]⟩
    rw [component.reshaped.Composition.lower_call_loop, loop]
    simp [component.reshaped.Composition.lower_call_loop.body, hnlt]
  | succ n ih =>
    intro Z A P j hn hj hZ hA hP
    have hlt : j < ((callsOf comp)[k]).instances := by rw [UScalar.lt_equiv]; omega
    have hi : j.val < ((callsOf comp)[k]).instances.val := by omega
    obtain ⟨Z1, hz1, hZ1⟩ := lower_zero_eq inst comp hl hk j hi hfit Z (by nlinarith)
    obtain ⟨A1, ha1, hA1⟩ := lower_and_eq inst comp hl hk j hi hfit A (by nlinarith)
    obtain ⟨P1, hp1, hP1⟩ := lower_product_eq inst comp hl hk j hi hfit P (by nlinarith)
    have hu : (uOf (j.val + 1)).val = j.val + 1 := uOf_val (by omega)
    obtain ⟨Z', A', P', h, h1, h2, h3⟩ := ih Z1 A1 P1 (uOf (j.val + 1)) (by omega) (by omega)
      (by rw [hZ1]; simp; nlinarith) (by rw [hA1]; simp; nlinarith) (by rw [hP1]; simp; nlinarith)
    refine ⟨Z', A', P', ?_, ?_, ?_, ?_⟩
    · rw [component.reshaped.Composition.lower_call_loop, loop]
      simp only [component.reshaped.Composition.lower_call_loop.body, hlt, ite_true, hz1,
        ha1, hp1, bind_ok, succ_eq j (by omega)]
      exact h
    · rw [h1, hZ1, hu, callRels_succ, List.append_assoc]
    · rw [h2, hA1, hu, callRels_succ, List.append_assoc]
    · rw [h3, hP1, hu, callRels_succ, List.append_assoc]

/-! ## Every call, in order -/

/-- One family of the lowered system over the first `j` calls: calls, then instances, then relations. -/
def lowerList {R : Type} (comp : component.Composition W) (fam : component.ComponentCall W → List R)
    (f : ℕ → ℕ → R → R) (j : ℕ) : List R :=
  (List.range j).flatMap fun k =>
    match (callsOf comp)[k]? with
    | some c => callRels (fam c) (f k) 0 c.instances.val
    | none => []

theorem lowerList_succ {R : Type} (comp : component.Composition W)
    (fam : component.ComponentCall W → List R) (f : ℕ → ℕ → R → R) {j : ℕ}
    (hj : j < (callsOf comp).length) :
    lowerList comp fam f (j + 1) =
      lowerList comp fam f j ++ callRels (fam (callsOf comp)[j]) (f j) 0 ((callsOf comp)[j]).instances.val := by
  simp [lowerList, List.range_succ, List.getElem?_eq_getElem hj]

theorem lowerList_length {R : Type} (comp : component.Composition W)
    (fam : component.ComponentCall W → List R) (f : ℕ → ℕ → R → R) (kind : system.ConstraintKind)
    (hfam : ∀ c, (fam c).length = relsOf c kind) :
    ∀ j ≤ (callsOf comp).length, (lowerList comp fam f j).length = pref (famSizes comp kind) j := by
  intro j
  induction j with
  | zero => simp [lowerList, pref]
  | succ j ih =>
    intro hj
    rw [lowerList_succ _ _ _ (by omega), List.length_append, ih (by omega), callRels_length, hfam,
      pref_succ _ _ (by simp [famSizes, counts]; omega)]
    simp [famSizes, counts]

theorem mem_lowerList {R : Type} (comp : component.Composition W)
    (fam : component.ComponentCall W → List R) (f : ℕ → ℕ → R → R) (x : R) :
    x ∈ lowerList comp fam f (callsOf comp).length ↔
      ∃ k, ∃ hk : k < (callsOf comp).length, ∃ i < ((callsOf comp)[k]).instances.val,
        ∃ r ∈ fam (callsOf comp)[k], x = f k i r := by
  simp only [lowerList, List.mem_flatMap, List.mem_range]
  constructor
  · rintro ⟨k, hk, hx⟩
    rw [List.getElem?_eq_getElem hk] at hx
    simp only [callRels, List.mem_flatMap, List.mem_range'_1, List.mem_map] at hx
    obtain ⟨i, hi, r, hr, rfl⟩ := hx
    exact ⟨k, hk, i, by omega, r, hr, rfl⟩
  · rintro ⟨k, hk, i, hi, r, hr, rfl⟩
    refine ⟨k, hk, ?_⟩
    rw [List.getElem?_eq_getElem hk]
    simp only [callRels, List.mem_flatMap, List.mem_range'_1, List.mem_map]
    exact ⟨i, by omega, r, hr, rfl⟩

theorem lower_loop_eq (inst : word.Word W) (comp : component.Composition W) (hl : LaidOut comp)
    (hfit : ∀ k (hk : k < (callsOf comp).length), BodyFits (callsOf comp)[k]) :
    ∀ n Z A P (j : Std.Usize), (callsOf comp).length - j.val = n → j.val ≤ (callsOf comp).length →
      (vecSlice Z).val = lowerList comp zerosOf (remapZero comp) j.val →
      (vecSlice A).val = lowerList comp andsOf (remapAnd comp) j.val →
      (vecSlice P).val = lowerList comp mulsOf (remapMul comp) j.val →
      ∃ Z' A' P', component.reshaped.Composition.reshaped_lower_loop inst comp Z A P j =
        .ok (comp.calls, comp.bases, comp.public_len, comp.witness_len, comp.relation_counts,
          Z', A', P') ∧
        (vecSlice Z').val = lowerList comp zerosOf (remapZero comp) (callsOf comp).length ∧
        (vecSlice A').val = lowerList comp andsOf (remapAnd comp) (callsOf comp).length ∧
        (vecSlice P').val = lowerList comp mulsOf (remapMul comp) (callsOf comp).length := by
  have hm := usize_max_eq
  have h32 := two_pow_32_le
  have hcl : (callsOf comp).length ≤ Usize.max := (vecSlice comp.calls).property
  intro n
  induction n with
  | zero =>
    intro Z A P j hn hj hZ hA hP
    have he : j.val = (callsOf comp).length := by omega
    have hnlt : ¬ j < (vecSlice comp.calls).len := by rw [UScalar.lt_equiv]; simp [he]
    refine ⟨Z, A, P, ?_, he ▸ hZ, he ▸ hA, he ▸ hP⟩
    rw [component.reshaped.Composition.reshaped_lower_loop, loop]
    simp [component.reshaped.Composition.reshaped_lower_loop.body, vec_len_eq, he]
  | succ n ih =>
    intro Z A P j hn hj hZ hA hP
    have hjl : j.val < (callsOf comp).length := by omega
    have hlt : j < (vecSlice comp.calls).len := by rw [UScalar.lt_equiv]; simpa using hjl
    have hfam := hl.fam
    have bound : ∀ (kind : system.ConstraintKind) {R : Type} (fam : component.ComponentCall W → List R)
        (f : ℕ → ℕ → R → R), (∀ c, (fam c).length = relsOf c kind) →
        (lowerList comp fam f j.val).length +
          ((callsOf comp)[j.val]).instances.val * (fam (callsOf comp)[j.val]).length < 2 ^ 32 := by
      intro kind R fam f hf
      have e := lowerList_length comp fam f kind hf (j.val + 1) (by omega)
      rw [lowerList_succ _ _ _ hjl, List.length_append, callRels_length] at e
      have := pref_le_sum (famSizes comp kind) (j.val + 1)
      have := hfam kind
      omega
    have bz := bound .Zero zerosOf (remapZero comp) (fun _ => rfl)
    have ba := bound .And andsOf (remapAnd comp) (fun _ => rfl)
    have bp := bound .IntegerMul mulsOf (remapMul comp) (fun _ => rfl)
    obtain ⟨Z1, A1, P1, hc, h1, h2, h3⟩ := lower_call_loop_eq inst comp hl hjl (hfit _ hjl)
      ((callsOf comp)[j.val]).instances.val Z A P 0#usize rfl (by simp) (by rw [hZ]; omega) (by rw [hA]; omega) (by rw [hP]; omega)
    have hu : (uOf (j.val + 1)).val = j.val + 1 := uOf_val (by omega)
    obtain ⟨Z', A', P', h, r1, r2, r3⟩ := ih Z1 A1 P1 (uOf (j.val + 1)) (by omega) (by omega)
      (by rw [h1, hZ, hu, lowerList_succ _ _ _ hjl]; rfl) (by rw [h2, hA, hu, lowerList_succ _ _ _ hjl]; rfl)
      (by rw [h3, hP, hu, lowerList_succ _ _ _ hjl]; rfl)
    have hjb : j.val < comp.bases.val.length := show j.val < (basesOf comp).length from hl.len ▸ hjl
    have hstep : component.reshaped.Composition.reshaped_lower_loop.body inst comp Z A P j =
        .ok (.cont (Z1, A1, P1, uOf (j.val + 1))) := by
      simp only [component.reshaped.Composition.reshaped_lower_loop.body, vec_len_eq, hlt, ite_true,
        bind_ok, component.reshaped.Composition.lower_call]
      rw [vec_index_eq comp.calls j hjl, bind_ok, vec_index_eq comp.bases j hjb, bind_ok]
      erw [hc]
      simp only [bind_ok, succ_eq j (by omega)]
      rfl
    refine ⟨Z', A', P', ?_, r1, r2, r3⟩
    rw [component.reshaped.Composition.reshaped_lower_loop, loop]
    simp only [hstep, bind_ok]
    exact h

/-! ## The lowered system -/

/-- What the lowered system holds.

- The segment lengths of the composition.
- In each family, the relations of every instance of every call, moved to their composed addresses. -/
structure LowerOf (comp : component.Composition W) (s : system.ConstraintSystem W) : Prop where
  pub : s.public_len = comp.public_len
  wit : s.witness_len = comp.witness_len
  zero : (vecSlice s.zero_constraints).val = lowerList comp zerosOf (remapZero comp) (callsOf comp).length
  and : (vecSlice s.and_constraints).val = lowerList comp andsOf (remapAnd comp) (callsOf comp).length
  mul : (vecSlice s.integer_mul_constraints).val =
    lowerList comp mulsOf (remapMul comp) (callsOf comp).length

theorem remapIdx_position (comp : component.Composition W) (hl : LaidOut comp) {k i : ℕ}
    (hk : k < (callsOf comp).length) (hi : i < ((callsOf comp)[k]).instances.val)
    {idx : index.ValueIndex} (h : idx.position.val < slotsOf (callsOf comp)[k] idx.segment) :
    (remapIdx comp k i idx).position.val =
      packed (counts comp) (widths comp idx.segment) k i idx.position.val := by
  have := packed_lt comp hl idx.segment hk hi h
  have := lenOf_lt comp idx.segment
  show (⟨BitVec.ofNat 32 _⟩ : Std.U32).val = _
  rw [ofNat32_val, Nat.mod_eq_of_lt (by omega)]

theorem cast_cast_u32 (x : Std.U32) : UScalar.cast .U32 (UScalar.cast .Usize x) = x :=
  UScalar.eq_of_val_eq (by
    rw [cast_u32_val _ (by rw [cast_usize_val _ (by decide)]; exact x.hBounds), cast_usize_val _ (by decide)])

theorem opIn_remap (comp : component.Composition W) (hl : LaidOut comp) {k i : ℕ}
    (hk : k < (callsOf comp).length) (hi : i < ((callsOf comp)[k]).instances.val)
    {o : constraint.Operand W} (hfit : OpFits (callsOf comp)[k] o) (s : system.ConstraintSystem W)
    (hp : s.public_len = comp.public_len) (hw : s.witness_len = comp.witness_len) :
    opIn s (remapOp comp k i o) := by
  intro t ht
  rw [remapOp_terms, List.mem_map] at ht
  obtain ⟨t, ht, rfl⟩ := ht
  have hf := hfit t ht
  have hlt := packed_lt comp hl t.index.segment hk hi hf
  simp only [inRange, remapTerm]
  apply decide_eq_true
  rw [remapIdx_position comp hl hk hi hf]
  show _ < (sysLen s t.index.segment).val
  cases h : t.index.segment <;> rw [h] at hlt <;>
    simp only [sysLen, hp, hw, cast_usize_val _ (show UScalarTy.U32.numBits ≤ 32 by decide)] <;>
    exact hlt

theorem relation_counts_ok (inst : word.Word W) (comp : component.Composition W) :
    ∃ a b c h, component.Composition.impl.relation_counts inst comp =
      .ok (Std.Array.make 3#usize [a, b, c] h) := by
  have hl : comp.relation_counts.val.length = 3 := comp.relation_counts.property
  simp only [component.Composition.impl.relation_counts, index_usize_eq _ _ (show (0#usize).val <
    comp.relation_counts.val.length by simp [hl]), index_usize_eq _ _ (show (1#usize).val <
    comp.relation_counts.val.length by simp [hl]), index_usize_eq _ _ (show (2#usize).val <
    comp.relation_counts.val.length by simp [hl]), bind_ok, lift_eq]
  exact ⟨_, _, _, rfl, rfl⟩

/-- Lowering a laid-out composition of well-formed gadgets never fails and never panics. -/
theorem lower_eq (inst : word.Word W) (comp : component.Composition W) (hl : LaidOut comp)
    (hfit : ∀ k (hk : k < (callsOf comp).length), BodyFits (callsOf comp)[k]) :
    ∃ s, component.Composition.lower inst comp = .ok (.Ok s) ∧ LowerOf comp s := by
  obtain ⟨a, b, c, h, hrc⟩ := relation_counts_ok inst comp
  obtain ⟨Z, A, P, hloop, hZ, hA, hP⟩ := lower_loop_eq inst comp hl hfit _ (emptyVec _) (emptyVec _)
    (emptyVec _) 0#usize rfl (by simp) (by simp [emptyVec, lowerList]) (by simp [emptyVec, lowerList])
    (by simp [emptyVec, lowerList])
  have hlen : ∀ kind {R : Type} (fam : component.ComponentCall W → List R) (f : ℕ → ℕ → R → R),
      (∀ c, (fam c).length = relsOf c kind) →
      (lowerList comp fam f (callsOf comp).length).length < 2 ^ 32 := by
    intro kind R fam f hf
    rw [lowerList_length comp fam f kind hf _ le_rfl,
      show (callsOf comp).length = (famSizes comp kind).length by simp [famSizes, counts], pref_length]
    exact hl.fam kind
  have bz := hlen .Zero zerosOf (remapZero comp) (fun _ => rfl)
  have ba := hlen .And andsOf (remapAnd comp) (fun _ => rfl)
  have bp := hlen .IntegerMul mulsOf (remapMul comp) (fun _ => rfl)
  have hv : validateSpec (sysOf (UScalar.cast .Usize comp.public_len) (UScalar.cast .Usize comp.witness_len)
      Z A P) = .Ok () := by
    have hp : (sysOf (UScalar.cast .Usize comp.public_len) (UScalar.cast .Usize comp.witness_len)
        Z A P).public_len = comp.public_len := cast_cast_u32 _
    have hw : (sysOf (UScalar.cast .Usize comp.public_len) (UScalar.cast .Usize comp.witness_len)
        Z A P).witness_len = comp.witness_len := cast_cast_u32 _
    rw [validateSpec_ok]
    refine ⟨fun r hr => ?_, fun r hr => ?_, fun r hr => ?_⟩
    · change r ∈ (vecSlice Z).val at hr
      rw [hZ, mem_lowerList] at hr
      obtain ⟨k, hk, i, hi, r, hr, rfl⟩ := hr
      exact opIn_remap comp hl hk hi ((hfit k hk).zero r hr) _ hp hw
    · change r ∈ (vecSlice A).val at hr
      rw [hA, mem_lowerList] at hr
      obtain ⟨k, hk, i, hi, r, hr, rfl⟩ := hr
      have hf := (hfit k hk).and r hr
      exact ⟨opIn_remap comp hl hk hi hf.1 _ hp hw, opIn_remap comp hl hk hi hf.2.1 _ hp hw,
        opIn_remap comp hl hk hi hf.2.2 _ hp hw⟩
    · change r ∈ (vecSlice P).val at hr
      rw [hP, mem_lowerList] at hr
      obtain ⟨k, hk, i, hi, r, hr, rfl⟩ := hr
      have hf := (hfit k hk).mul r hr
      exact ⟨opIn_remap comp hl hk hi hf.1 _ hp hw, opIn_remap comp hl hk hi hf.2.1 _ hp hw,
        opIn_remap comp hl hk hi hf.2.2.1 _ hp hw, opIn_remap comp hl hk hi hf.2.2.2 _ hp hw⟩
  refine ⟨sysOf (UScalar.cast .Usize comp.public_len) (UScalar.cast .Usize comp.witness_len) Z A P, ?_,
    ⟨cast_cast_u32 _, cast_cast_u32 _, hZ, hA, hP⟩⟩
  simp only [component.Composition.lower, component.reshaped.Composition.reshaped_lower, hrc, bind_ok,
    index3_0, index3_1, index3_2, vec_with_capacity_eq]
  erw [hloop]
  simp only [bind_ok, component.Composition.impl.public_len, component.Composition.impl.witness_len,
    system_new_eq, newSpec]
  have h1 : (UScalar.cast .Usize comp.public_len).val < 2 ^ 32 := by
    rw [cast_usize_val _ (by decide)]; exact comp.public_len.hBounds
  have h2 : (UScalar.cast .Usize comp.witness_len).val < 2 ^ 32 := by
    rw [cast_usize_val _ (by decide)]; exact comp.witness_len.hBounds
  rw [← hZ] at bz; rw [← hA] at ba; rw [← hP] at bp
  show RustM.ok (if _ then _ else _) = _
  split_ifs <;> try omega
  rw [hv]

/-! ## What the lowered system accepts -/

/-- The words of instance `i` of call `k` in a composed segment. -/
def block (comp : component.Composition W) (k i : ℕ) (seg : index.Segment) (s : Slice W) : Slice W :=
  Slice.from ((s.val.drop (packed (counts comp) (widths comp seg) k i 0)).take ((widths comp seg).getD k 0))
    (by have := s.property; simp only [List.length_take, List.length_drop]; omega)

theorem block_val (comp : component.Composition W) (k i : ℕ) (seg : index.Segment) (s : Slice W) :
    (block comp k i seg s).val =
      (s.val.drop (packed (counts comp) (widths comp seg) k i 0)).take ((widths comp seg).getD k 0) := by
  simp [block]

theorem widths_getD (comp : component.Composition W) {k : ℕ} (hk : k < (callsOf comp).length)
    (seg : index.Segment) : (widths comp seg).getD k 0 = slotsOf (callsOf comp)[k] seg := by
  simp [widths, hk, List.getD_eq_getElem?_getD]

/-- A word of an instance's block is the word at its composed address. -/
theorem lookup_remap (comp : component.Composition W) (hl : LaidOut comp) {k i : ℕ}
    (hk : k < (callsOf comp).length) (hi : i < ((callsOf comp)[k]).instances.val) (pub wit : Slice W)
    {idx : index.ValueIndex} (h : idx.position.val < slotsOf (callsOf comp)[k] idx.segment) :
    lookup pub wit (remapIdx comp k i idx) =
      lookup (block comp k i .Public pub) (block comp k i .Witness wit) idx := by
  have hpos := remapIdx_position comp hl hk hi h
  have hw := widths_getD comp hk idx.segment
  simp only [lookup] at hpos ⊢
  rw [hpos]
  have hseg : (remapIdx comp k i idx).segment = idx.segment := rfl
  rw [hseg]
  cases hs : idx.segment <;> rw [hs] at h hw <;>
    simp only [segOf, block_val, hw, List.getElem?_take_of_lt h, List.getElem?_drop] <;> rfl

/-- Moving a term to another address keeps its meaning and whether it panics. -/
structure IndexFree {W : Type} [DecidableEq W] {inst : word.Word W} (M : Model inst) : Prop where
  valid : ∀ t j, M.valid t → M.valid { t with index := j }
  term : ∀ t j w, M.term { t with index := j } w = M.term t w

theorem evalSpec_cons_some (xorf : W → W → W) (f : shift.ShiftedValue W → W → W) (pub wit : Slice W)
    (t : shift.ShiftedValue W) (ts : List (shift.ShiftedValue W)) (v w : W)
    (h : lookup pub wit t.index = some w) :
    evalSpec xorf f pub wit (t :: ts) v = evalSpec xorf f pub wit ts (xorf v (f t w)) := by
  simp [evalSpec, h]

theorem evalSpec_cons_none (xorf : W → W → W) (f : shift.ShiftedValue W → W → W) (pub wit : Slice W)
    (t : shift.ShiftedValue W) (ts : List (shift.ShiftedValue W)) (v : W)
    (h : lookup pub wit t.index = none) :
    evalSpec xorf f pub wit (t :: ts) v = .Err (missing pub wit t.index) := by
  simp [evalSpec, h]

section Semantics

variable [DecidableEq W] {inst : word.Word W} (M : Model inst)

/-- The value an evaluation returns, if any. -/
def okOf (r : CoreModels.core.result.Result W constraint.EvaluationError) : Option W :=
  match r with
  | .Ok v => some v
  | .Err _ => none

theorem opVal_eq_okOf (pub wit : Slice W) (o : constraint.Operand W) :
    opVal M pub wit o = okOf (evalSpec M.xorf M.term pub wit o.terms.val M.zero) := rfl

variable {M}

/-- An operand read at its composed addresses denotes what it denotes on its instance's block. -/
theorem opVal_remap (hM : IndexFree M) (comp : component.Composition W) (hl : LaidOut comp) {k i : ℕ}
    (hk : k < (callsOf comp).length) (hi : i < ((callsOf comp)[k]).instances.val)
    (pub wit : Slice W) {o : constraint.Operand W} (hfit : OpFits (callsOf comp)[k] o) :
    opVal M pub wit (remapOp comp k i o) =
      opVal M (block comp k i .Public pub) (block comp k i .Witness wit) o := by
  rw [opVal_eq_okOf, opVal_eq_okOf]
  change okOf (evalSpec _ _ _ _ (vecSlice (remapOp comp k i o).terms).val _) =
    okOf (evalSpec _ _ _ _ (vecSlice o.terms).val _)
  rw [remapOp_terms]
  have hfit' : ∀ t ∈ (vecSlice o.terms).val, t.index.position.val < slotsOf (callsOf comp)[k] t.index.segment :=
    hfit
  generalize (vecSlice o.terms).val = ts at hfit' ⊢
  generalize M.zero = v
  induction ts generalizing v with
  | nil => rfl
  | cons t ts ih =>
    have ht := hfit' t (by simp)
    have hl' := lookup_remap comp hl hk hi pub wit ht
    rw [List.map_cons]
    cases h : lookup (block comp k i .Public pub) (block comp k i .Witness wit) t.index with
    | none =>
      rw [evalSpec_cons_none _ _ _ _ _ _ _ h, evalSpec_cons_none _ _ _ _ _ _ _ (by rw [← h]; exact hl')]
      rfl
    | some w =>
      rw [evalSpec_cons_some _ _ _ _ _ _ _ _ h, evalSpec_cons_some _ _ _ _ _ _ _ _ (by rw [← h]; exact hl'),
        remapTerm, hM.term]
      apply ih
      intro t ht
      exact hfit' t (by simp [ht])

theorem andHolds_remap (hM : IndexFree M) (comp : component.Composition W) (hl : LaidOut comp) {k i : ℕ}
    (hk : k < (callsOf comp).length) (hi : i < ((callsOf comp)[k]).instances.val) (pub wit : Slice W)
    {r : constraint.AndConstraint W}
    (hf : OpFits (callsOf comp)[k] r.left ∧ OpFits (callsOf comp)[k] r.right ∧
      OpFits (callsOf comp)[k] r.output) :
    andHolds M pub wit (remapAnd comp k i r) =
      andHolds M (block comp k i .Public pub) (block comp k i .Witness wit) r := by
  simp only [andHolds, remapAnd, opVal_remap hM comp hl hk hi pub wit hf.1,
    opVal_remap hM comp hl hk hi pub wit hf.2.1, opVal_remap hM comp hl hk hi pub wit hf.2.2]

theorem mulHolds_remap (hM : IndexFree M) (comp : component.Composition W) (hl : LaidOut comp) {k i : ℕ}
    (hk : k < (callsOf comp).length) (hi : i < ((callsOf comp)[k]).instances.val) (pub wit : Slice W)
    {r : constraint.IntegerMulConstraint W}
    (hf : OpFits (callsOf comp)[k] r.left ∧ OpFits (callsOf comp)[k] r.right ∧
      OpFits (callsOf comp)[k] r.low ∧ OpFits (callsOf comp)[k] r.high) :
    mulHolds M pub wit (remapMul comp k i r) =
      mulHolds M (block comp k i .Public pub) (block comp k i .Witness wit) r := by
  simp only [mulHolds, remapMul, opVal_remap hM comp hl hk hi pub wit hf.1,
    opVal_remap hM comp hl hk hi pub wit hf.2.1, opVal_remap hM comp hl hk hi pub wit hf.2.2.1,
    opVal_remap hM comp hl hk hi pub wit hf.2.2.2]

omit [DecidableEq W] in
/-- On a segment of the composed length, an instance's block has one instance's width. -/
theorem block_length (comp : component.Composition W) (hl : LaidOut comp) {k i : ℕ}
    (hk : k < (callsOf comp).length) (hi : i < ((callsOf comp)[k]).instances.val)
    (seg : index.Segment) (s : Slice W) (hs : s.val.length = lenOf comp seg) :
    (block comp k i seg s).val.length = slotsOf (callsOf comp)[k] seg := by
  rw [block_val, List.length_take, List.length_drop, widths_getD comp hk]
  by_cases hw : slotsOf (callsOf comp)[k] seg = 0
  · simp [hw]
  · have := packed_lt comp hl seg hk hi (s := slotsOf (callsOf comp)[k] seg - 1) (by omega)
    simp only [packed] at this ⊢
    omega

omit [DecidableEq W] in
theorem len_cast_iff (s : Slice W) (n : Std.U32) :
    s.len = UScalar.cast .Usize n ↔ s.val.length = n.val := by
  constructor
  · intro h
    have := congrArg UScalar.val h
    rwa [cast_usize_val _ (by decide), Slice.len_val] at this
  · intro h
    exact UScalar.eq_of_val_eq (by rw [cast_usize_val _ (by decide), Slice.len_val]; exact h)

/-- A flat witness satisfies the lowered system exactly when two conditions hold.

- Both segments have the composed lengths.
- Every instance of every call satisfies its body on its own block of words. -/
theorem lower_verify_iff (hM : IndexFree M) (comp : component.Composition W) (hl : LaidOut comp)
    (hfit : ∀ k (hk : k < (callsOf comp).length), BodyFits (callsOf comp)[k])
    (hwf : ∀ k (hk : k < (callsOf comp).length),
      slotsP (callsOf comp)[k] = ((callsOf comp)[k]).component.body.public_len.val)
    {s : system.ConstraintSystem W} (hs : LowerOf comp s) (pub wit : Slice W) :
    verifySpec M s pub wit = .Ok () ↔
      pub.val.length = comp.public_len.val ∧ wit.val.length = comp.witness_len.val ∧
      ∀ k (hk : k < (callsOf comp).length), ∀ i < ((callsOf comp)[k]).instances.val,
        verifySpec M ((callsOf comp)[k]).component.body
          (block comp k i .Public pub) (block comp k i .Witness wit) = .Ok () := by
  rw [verifySpec_ok, len_cast_iff, len_cast_iff, hs.pub, hs.wit, hs.zero, hs.and, hs.mul]
  refine and_congr_right fun hp => and_congr_right fun hw => ?_
  have hbody : ∀ k (hk : k < (callsOf comp).length), ∀ i < ((callsOf comp)[k]).instances.val,
      (verifySpec M ((callsOf comp)[k]).component.body
        (block comp k i .Public pub) (block comp k i .Witness wit) = .Ok () ↔
      (∀ r ∈ zerosOf (callsOf comp)[k],
        opVal M (block comp k i .Public pub) (block comp k i .Witness wit) r.value = some M.zero) ∧
      (∀ r ∈ andsOf (callsOf comp)[k],
        andHolds M (block comp k i .Public pub) (block comp k i .Witness wit) r = true) ∧
      (∀ r ∈ mulsOf (callsOf comp)[k],
        mulHolds M (block comp k i .Public pub) (block comp k i .Witness wit) r = true)) := by
    intro k hk i hi
    rw [verifySpec_ok, len_cast_iff, len_cast_iff, block_length comp hl hk hi .Public pub hp,
      block_length comp hl hk hi .Witness wit hw]
    simp only [slotsOf, hwf k hk, slotsW, true_and]
  simp only [mem_lowerList]
  constructor
  · rintro ⟨hz, ha, hm⟩ k hk i hi
    refine (hbody k hk i hi).2 ⟨fun r hr => ?_, fun r hr => ?_, fun r hr => ?_⟩
    · rw [← opVal_remap hM comp hl hk hi pub wit ((hfit k hk).zero r hr)]
      exact hz _ ⟨k, hk, i, hi, r, hr, rfl⟩
    · rw [← andHolds_remap hM comp hl hk hi pub wit ((hfit k hk).and r hr)]
      exact ha _ ⟨k, hk, i, hi, r, hr, rfl⟩
    · rw [← mulHolds_remap hM comp hl hk hi pub wit ((hfit k hk).mul r hr)]
      exact hm _ ⟨k, hk, i, hi, r, hr, rfl⟩
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · rintro _ ⟨k, hk, i, hi, r, hr, rfl⟩
      rw [remapZero, opVal_remap hM comp hl hk hi pub wit ((hfit k hk).zero r hr)]
      exact ((hbody k hk i hi).1 (h k hk i hi)).1 r hr
    · rintro _ ⟨k, hk, i, hi, r, hr, rfl⟩
      rw [andHolds_remap hM comp hl hk hi pub wit ((hfit k hk).and r hr)]
      exact ((hbody k hk i hi).1 (h k hk i hi)).2.1 r hr
    · rintro _ ⟨k, hk, i, hi, r, hr, rfl⟩
      rw [mulHolds_remap hM comp hl hk hi pub wit ((hfit k hk).mul r hr)]
      exact ((hbody k hk i hi).1 (h k hk i hi)).2.2 r hr

end Semantics

/-! ## From the gadget invariants -/

/-- What the gadget constructor guarantees of every call.

- The interface covers the body's public segment exactly.
- Every term of the body addresses a word inside its segment. -/
def CallsWF (comp : component.Composition W) : Prop :=
  ∀ c ∈ callsOf comp, slotsP c = c.component.body.public_len.val ∧ validateSpec c.component.body = .Ok ()

theorem opFits_of_opIn {c : component.ComponentCall W} (hp : slotsP c = c.component.body.public_len.val)
    {o : constraint.Operand W} (h : opIn c.component.body o) : OpFits c o := by
  intro t ht
  have := h t ht
  simp only [inRange, decide_eq_true_eq] at this
  cases hs : t.index.segment <;> rw [hs] at this <;>
    simpa [sysLen, slotsOf, slotsW, hp, cast_usize_val _ (show UScalarTy.U32.numBits ≤ 32 by decide)]
      using this

theorem bodyFits_of_wf {comp : component.Composition W} (hwf : CallsWF comp) {k : ℕ}
    (hk : k < (callsOf comp).length) : BodyFits (callsOf comp)[k] := by
  obtain ⟨hp, hv⟩ := hwf _ (List.getElem_mem hk)
  obtain ⟨hz, ha, hm⟩ := (validateSpec_ok _).1 hv
  exact ⟨fun r hr => opFits_of_opIn hp (hz r hr),
    fun r hr => ⟨opFits_of_opIn hp (ha r hr).1, opFits_of_opIn hp (ha r hr).2.1,
      opFits_of_opIn hp (ha r hr).2.2⟩,
    fun r hr => ⟨opFits_of_opIn hp (hm r hr).1, opFits_of_opIn hp (hm r hr).2.1,
      opFits_of_opIn hp (hm r hr).2.2.1, opFits_of_opIn hp (hm r hr).2.2.2⟩⟩

section Sound

variable [DecidableEq W] {inst : word.Word W} {M : Model inst}

theorem opValid_remap (hM : IndexFree M) (comp : component.Composition W) (k i : ℕ)
    {o : constraint.Operand W} (h : OpValid M o) : OpValid M (remapOp comp k i o) := by
  intro t ht
  change t ∈ (vecSlice (remapOp comp k i o).terms).val at ht
  rw [remapOp_terms, List.mem_map] at ht
  obtain ⟨t, ht, rfl⟩ := ht
  exact hM.valid _ _ (h t ht)

theorem sysValid_lower (hM : IndexFree M) (comp : component.Composition W)
    (hv : ∀ c ∈ callsOf comp, SysValid M c.component.body) {s : system.ConstraintSystem W}
    (hs : LowerOf comp s) : SysValid M s := by
  refine ⟨fun r hr => ?_, fun r hr => ?_, fun r hr => ?_⟩
  · change r ∈ (vecSlice s.zero_constraints).val at hr
    rw [hs.zero, mem_lowerList] at hr
    obtain ⟨k, hk, i, hi, r, hr, rfl⟩ := hr
    exact opValid_remap hM comp k i ((hv _ (List.getElem_mem hk)).1 r hr)
  · change r ∈ (vecSlice s.and_constraints).val at hr
    rw [hs.and, mem_lowerList] at hr
    obtain ⟨k, hk, i, hi, r, hr, rfl⟩ := hr
    have h := (hv _ (List.getElem_mem hk)).2.1 r hr
    exact ⟨opValid_remap hM comp k i h.1, opValid_remap hM comp k i h.2.1,
      opValid_remap hM comp k i h.2.2⟩
  · change r ∈ (vecSlice s.integer_mul_constraints).val at hr
    rw [hs.mul, mem_lowerList] at hr
    obtain ⟨k, hk, i, hi, r, hr, rfl⟩ := hr
    have h := (hv _ (List.getElem_mem hk)).2.2 r hr
    exact ⟨opValid_remap hM comp k i h.1, opValid_remap hM comp k i h.2.1,
      opValid_remap hM comp k i h.2.2.1, opValid_remap hM comp k i h.2.2.2⟩

/-- Lowering a laid-out composition of well-formed gadgets never fails and never panics.

The flat verifier then accepts exactly when two conditions hold.

- Both segments have the composed lengths.
- The gadget's own verifier accepts every instance of every call on its block of words. -/
theorem lower_sound (hM : IndexFree M) (comp : component.Composition W) (hl : LaidOut comp)
    (hwf : CallsWF comp) (hv : ∀ c ∈ callsOf comp, SysValid M c.component.body) :
    ∃ s, component.Composition.lower inst comp = .ok (.Ok s) ∧ LowerOf comp s ∧
      ∀ pub wit : Slice W,
        (system.ConstraintSystem.verify inst s pub wit = .ok (.Ok ()) ↔
          pub.val.length = comp.public_len.val ∧ wit.val.length = comp.witness_len.val ∧
          ∀ k (hk : k < (callsOf comp).length), ∀ i < ((callsOf comp)[k]).instances.val,
            system.ConstraintSystem.verify inst ((callsOf comp)[k]).component.body
              (block comp k i .Public pub) (block comp k i .Witness wit) = .ok (.Ok ())) := by
  obtain ⟨s, hlow, hs⟩ := lower_eq inst comp hl (fun k hk => bodyFits_of_wf hwf hk)
  refine ⟨s, hlow, hs, fun pub wit => ?_⟩
  rw [verify_eq M s pub wit (sysValid_lower hM comp hv hs), RustM.ok.injEq,
    lower_verify_iff hM comp hl (fun k hk => bodyFits_of_wf hwf hk)
      (fun k hk => (hwf _ (List.getElem_mem hk)).1) hs]
  refine and_congr_right fun _ => and_congr_right fun _ => ?_
  refine forall_congr' fun k => forall_congr' fun hk => forall_congr' fun i => forall_congr' fun _ => ?_
  rw [verify_eq M _ _ _ (hv _ (List.getElem_mem hk)), RustM.ok.injEq]

end Sound

/-- A composition built from gadgets the constructors accepted lowers without failing or panicking.

The flat verifier then accepts exactly the witnesses on which every instance satisfies its gadget. -/
theorem lower_sound_of_new [DecidableEq W] {inst : word.Word W} {M : Model inst} (hM : IndexFree M)
    (callsV : CoreModels.alloc.vec.Vec (component.ComponentCall W)) {comp : component.Composition W}
    (hnew : component.Composition.new inst callsV = .ok (.Ok comp))
    (hwf : ∀ c ∈ (vecSlice callsV).val,
      slotsP c = c.component.body.public_len.val ∧ validateSpec c.component.body = .Ok ())
    (hv : ∀ c ∈ (vecSlice callsV).val, SysValid M c.component.body) :
    ∃ s, component.Composition.lower inst comp = .ok (.Ok s) ∧
      ∀ pub wit : Slice W,
        (system.ConstraintSystem.verify inst s pub wit = .ok (.Ok ()) ↔
          pub.val.length = comp.public_len.val ∧ wit.val.length = comp.witness_len.val ∧
          ∀ k (hk : k < (callsOf comp).length), ∀ i < ((callsOf comp)[k]).instances.val,
            system.ConstraintSystem.verify inst ((callsOf comp)[k]).component.body
              (block comp k i .Public pub) (block comp k i .Witness wit) = .ok (.Ok ())) := by
  obtain ⟨r, hr, hn⟩ := composition_new_laid_out inst callsV (fun c hc => by
    rw [(hwf c hc).1]; exact c.component.body.public_len.hBounds)
  rw [hnew, RustM.ok.injEq] at hr
  obtain ⟨hl, hcalls⟩ := hn comp hr.symm
  have hc : callsOf comp = (vecSlice callsV).val := by rw [callsOf, hcalls]
  obtain ⟨s, h1, -, h2⟩ := lower_sound hM comp hl (fun c h => hwf c (hc ▸ h)) (fun c h => hv c (hc ▸ h))
  exact ⟨s, h1, h2⟩

theorem indexFree32 : IndexFree M32 := ⟨fun _ _ h => h, fun _ _ _ => rfl⟩

theorem indexFree64 : IndexFree M64 := ⟨fun _ _ h => h, fun _ _ _ => rfl⟩

end Plonky3Lean.Proofs.Word
