module

public import Plonky3Lean.Proofs.Word.Index
public import Plonky3Lean.Proofs.Word.Layout
public import Plonky3Lean.Proofs.Word.Models

@[expose] public section

/-!
# Composed addressing

A composition gives each call a block of the public segment and a block of the witness segment.

Readdressing a component-local slot names the word at

```text
    block start + instance * slots per instance + slot
```

It refuses an unknown call, an unknown instance and a slot past one instance's width.
-/

open Aeneas Aeneas.Std CoreModels p3_word
open Plonky3Lean.Lib

namespace Plonky3Lean.Proofs.Word

theorem usize_mul_eq (x y : Std.Usize) (h : x.val * y.val < 2 ^ UScalarTy.Usize.numBits) :
    (x * y : RustM Std.Usize) = .ok (uOf (x.val * y.val)) := by
  have hmax : x.val * y.val ≤ UScalar.max .Usize := by simp only [UScalar.max]; omega
  obtain ⟨z, hz, hv⟩ := spec_imp_exists (UScalar.mul_spec hmax)
  rw [hz]
  exact congrArg _ (UScalar.eq_of_val_eq (by rw [hv, uOf_val h]))

theorem usize_add_eq (x y : Std.Usize) (h : x.val + y.val < 2 ^ UScalarTy.Usize.numBits) :
    (x + y : RustM Std.Usize) = .ok (uOf (x.val + y.val)) := by
  have hmax : x.val + y.val ≤ UScalar.max .Usize := by simp only [UScalar.max]; omega
  obtain ⟨z, hz, hv⟩ := spec_imp_exists (UScalar.add_bv_spec hmax)
  rw [hz]
  exact congrArg _ (UScalar.eq_of_val_eq (by rw [hv.1, uOf_val h]))

theorem cast_usize_val {ty : UScalarTy} (x : UScalar ty) (h : ty.numBits ≤ 32) :
    (UScalar.cast .Usize x).val = x.val :=
  UScalar.cast_val_mod_pow_greater_numBits_eq _ _ (by
    simp only [UScalarTy.numBits] at *; rcases System.Platform.numBits_eq with e | e <;> omega)

theorem two_pow_32_le : 2 ^ 32 ≤ 2 ^ UScalarTy.Usize.numBits := by
  apply Nat.pow_le_pow_right (by norm_num)
  simp only [UScalarTy.Usize_numBits_eq]
  rcases System.Platform.numBits_eq with e | e <;> omega

variable {W : Type}

/-- The interface slots one instance of a call owns. -/
def slotsP (c : component.ComponentCall W) : ℕ :=
  c.component.public_inputs.val + c.component.public_outputs.val

/-- The private slots one instance of a call owns. -/
def slotsW (c : component.ComponentCall W) : ℕ := c.component.body.witness_len.val

/-- The slots one instance of a call owns in a segment. -/
def slotsOf (c : component.ComponentCall W) : index.Segment → ℕ
  | .Public => slotsP c
  | .Witness => slotsW c

/-- The calls of a composition. -/
abbrev callsOf (comp : component.Composition W) := (vecSlice comp.calls).val

/-- The block starts of a composition. -/
abbrev basesOf (comp : component.Composition W) := (vecSlice comp.bases).val

/-- The instance counts. -/
def counts (comp : component.Composition W) : List ℕ := (callsOf comp).map (·.instances.val)

/-- The per-instance widths in a segment. -/
def widths (comp : component.Composition W) (seg : index.Segment) : List ℕ :=
  (callsOf comp).map (slotsOf · seg)

/-- The start a call's block has in a segment. -/
def baseOf (b : component.CallBase) : index.Segment → Std.Usize
  | .Public => b.public
  | .Witness => b.witness

/-- The segment length a composition records. -/
def lenOf (comp : component.Composition W) : index.Segment → ℕ
  | .Public => comp.public_len.val
  | .Witness => comp.witness_len.val

/-- A composition is laid out when its blocks are packed one after the other.

- There is one block start per call.
- In each segment, call `k`'s block starts after the blocks of the calls before it.
- The recorded segment lengths are the totals. -/
structure LaidOut (comp : component.Composition W) : Prop where
  len : (basesOf comp).length = (callsOf comp).length
  base : ∀ k (h : k < (basesOf comp).length) seg,
    (baseOf (basesOf comp)[k] seg).val = pref (List.zipWith (· * ·) (counts comp) (widths comp seg)) k
  total : ∀ seg, (List.zipWith (· * ·) (counts comp) (widths comp seg)).sum = lenOf comp seg

/-- What readdressing returns.

- An unknown call, then an unknown instance, then a slot past the width, are refused in that order.
- Otherwise the slot is moved to its packed position in the composed segment. -/
def resolveSpec (comp : component.Composition W) (k i : Std.Usize) (idx : index.ValueIndex) :
    CoreModels.core.result.Result index.ValueIndex component.CompositionError :=
  match (callsOf comp)[k.val]? with
  | none => .Err (.UnknownCall k (vecSlice comp.calls).len)
  | some c =>
    if c.instances.val ≤ i.val then .Err (.UnknownInstance k i c.instances)
    else if slotsOf c idx.segment ≤ idx.position.val then
      .Err (.UnknownSlot k idx.segment idx.position (uOf (slotsOf c idx.segment)))
    else .Ok ⟨idx.segment, ⟨BitVec.ofNat 32
      (packed (counts comp) (widths comp idx.segment) k.val i.val idx.position.val)⟩⟩

theorem vec_deref_eq {T : Type} (v : CoreModels.alloc.vec.Vec T) :
    CoreModels.alloc.vec.Vec.Insts.CoreOpsDerefDerefSlice.deref v = .ok (vecSlice v) := rfl

theorem base_eq (inst : word.Word W) (comp : component.Composition W) (k : Std.Usize) :
    component.Composition.base inst comp k =
      .ok (match (basesOf comp)[k.val]? with
        | some b => .Ok b
        | none => .Err (.UnknownCall k (vecSlice comp.calls).len)) := by
  simp only [component.Composition.base, vec_deref_eq, bind_ok, slice_get_usize_eq, vec_len_eq]
  cases (basesOf comp)[k.val]? <;> rfl

theorem check_instance_eq (inst : word.Word W) (comp : component.Composition W) (k i : Std.Usize) :
    component.Composition.check_instance inst comp k i =
      .ok (match (callsOf comp)[k.val]? with
        | some c => if c.instances.val ≤ i.val then .Err (.UnknownInstance k i c.instances) else .Ok c
        | none => .Err (.UnknownCall k (vecSlice comp.calls).len)) := by
  simp only [component.Composition.check_instance, vec_deref_eq, bind_ok, slice_get_usize_eq,
    vec_len_eq]
  cases (callsOf comp)[k.val]? with
  | none =>
    simp [CoreModels.core.option.Option.ok_or,
      CoreModels.core.result.Result.Insts.CoreOpsTry_traitTryTResultInfallibleE.branch,
      CoreModels.core.result.Result.Insts.CoreOpsTry_traitFromResidualResultInfallibleE.from_residual,
      CoreModels.core.convert.From.Blanket.from]
  | some c =>
    simp only [CoreModels.core.option.Option.ok_or, bind_ok,
      CoreModels.core.result.Result.Insts.CoreOpsTry_traitTryTResultInfallibleE.branch,
      GE.ge, UScalar.le_equiv]
    split_ifs <;> rfl

theorem segment_slots_eq (inst : word.Word W) (c : component.ComponentCall W) (seg : index.Segment)
    (h : slotsOf c seg < 2 ^ 32) :
    component.reshaped.Composition.segment_slots inst c.component seg = .ok (uOf (slotsOf c seg)) := by
  have h32 := two_pow_32_le
  cases seg
  · simp only [component.reshaped.Composition.segment_slots, component.Component.interface_slots,
      component.Component.impl.public_inputs, component.Component.impl.public_outputs, bind_ok]
    have hb : (UScalar.cast .Usize c.component.public_inputs).val +
        (UScalar.cast .Usize c.component.public_outputs).val < 2 ^ UScalarTy.Usize.numBits := by
      rw [cast_usize_val _ (by decide), cast_usize_val _ (by decide)]
      simp only [slotsOf, slotsP] at h; omega
    rw [usize_add_eq _ _ hb, cast_usize_val _ (by decide), cast_usize_val _ (by decide)]; rfl
  · simp only [component.reshaped.Composition.segment_slots, component.Component.local_slots,
      system.ConstraintSystem.impl.witness_len]
    exact congrArg _ (UScalar.eq_of_val_eq (by
      rw [cast_usize_val _ (by decide), uOf_val (by omega)]; rfl))

/-- In a laid-out composition, a call with an instance has a block inside its segment. -/
theorem block_le (comp : component.Composition W) (hl : LaidOut comp) {k : ℕ}
    (hk : k < (callsOf comp).length) (seg : index.Segment) :
    ((callsOf comp)[k]).instances.val * slotsOf (callsOf comp)[k] seg < 2 ^ 32 := by
  have hz : k < (List.zipWith (· * ·) (counts comp) (widths comp seg)).length := by
    simp [counts, widths, hk]
  have hle : (List.zipWith (· * ·) (counts comp) (widths comp seg))[k] ≤
      (List.zipWith (· * ·) (counts comp) (widths comp seg)).sum := List.le_sum_of_mem (List.getElem_mem hz)
  rw [hl.total seg] at hle
  have hlen : lenOf comp seg < 2 ^ 32 := by
    cases seg
    · exact comp.public_len.hBounds
    · exact comp.witness_len.hBounds
  simp only [List.getElem_zipWith, counts, widths, List.getElem_map] at hle
  omega

theorem position_eq (inst : word.Word W) (comp : component.Composition W) (b : component.CallBase)
    (c : component.ComponentCall W) (i : Std.Usize) (idx : index.ValueIndex)
    (hs : slotsOf c idx.segment < 2 ^ 32)
    (hsum : (baseOf b idx.segment).val + i.val * slotsOf c idx.segment + idx.position.val < 2 ^ 32) :
    component.Composition.position inst comp b c.component i idx =
      .ok (uOf ((baseOf b idx.segment).val + i.val * slotsOf c idx.segment + idx.position.val)) := by
  have h32 := two_pow_32_le
  have hseg := segment_slots_eq inst c idx.segment hs
  obtain ⟨seg, pos⟩ := idx
  simp only at hs hsum hseg ⊢
  generalize hw : slotsOf c seg = w at hs hsum hseg ⊢
  have hu : (uOf w).val = w := uOf_val (by omega)
  have hm : (uOf (i.val * w)).val = i.val * w := uOf_val (by omega)
  cases seg <;>
  · simp only [component.reshaped.Composition.segment_slots] at hseg
    simp only [baseOf] at hsum ⊢
    simp only [component.Composition.position, index.ValueIndex.impl.segment,
      index.ValueIndex.impl.position, bind_ok, hseg, lift_eq, Aeneas.Std.uncurry_apply_pair]
    rw [usize_mul_eq i (uOf w) (by rw [hu]; omega), bind_ok]
    rw [hu, usize_add_eq _ (uOf (i.val * w)) (by rw [hm]; omega), bind_ok]
    rw [hm, usize_add_eq _ _ (by rw [uOf_val (by omega), cast_usize_val _ (by decide)]; omega)]
    rw [uOf_val (by omega), cast_usize_val _ (by decide)]

theorem composed_index_eq (inst : word.Word W) (seg : index.Segment) (p : ℕ) (hp : p < 2 ^ 32) :
    component.reshaped.Composition.composed_index inst seg (uOf p) =
      .ok ⟨seg, ⟨BitVec.ofNat 32 p⟩⟩ := by
  have h32 := two_pow_32_le
  have hv : (uOf p).val = p := uOf_val (by omega)
  have hc : UScalar.cast .U32 (uOf p) = ⟨BitVec.ofNat 32 p⟩ := by
    apply UScalar.eq_of_val_eq
    rw [cast_u32_val _ (by omega), hv, ofNat32_val, Nat.mod_eq_of_lt hp]
  cases seg <;>
    simp [component.reshaped.Composition.composed_index, index.ValueIndex.public,
      index.ValueIndex.witness, value_index_new_eq, hv, show p < 4294967296 from hp, hc,
      CoreModels.core.result.Result.expect]

/-- Readdressing in a laid-out composition returns the reference outcome, and never panics. -/
theorem resolve_eq (inst : word.Word W) (comp : component.Composition W) (hl : LaidOut comp)
    (k i : Std.Usize) (idx : index.ValueIndex) :
    component.Composition.resolve inst comp k i idx = .ok (resolveSpec comp k i idx) := by
  simp only [component.Composition.resolve, component.reshaped.Composition.reshaped_resolve,
    base_eq, bind_ok, resolveSpec]
  by_cases hk : k.val < (callsOf comp).length
  · have hkb : k.val < (basesOf comp).length := hl.len ▸ hk
    rw [List.getElem?_eq_getElem hkb, List.getElem?_eq_getElem hk]
    simp only [CoreModels.core.result.Result.Insts.CoreOpsTry_traitTryTResultInfallibleE.branch,
      bind_ok, check_instance_eq, List.getElem?_eq_getElem hk]
    have h32 := two_pow_32_le
    have hblock := block_le comp hl hk idx.segment
    set c := (callsOf comp)[k.val] with hc
    by_cases hi : c.instances.val ≤ i.val
    · simp [hi, CoreModels.core.result.Result.Insts.CoreOpsTry_traitTryTResultInfallibleE.branch,
        CoreModels.core.result.Result.Insts.CoreOpsTry_traitFromResidualResultInfallibleE.from_residual,
        CoreModels.core.convert.From.Blanket.from]
    · have hw : slotsOf c idx.segment < 2 ^ 32 := by
        have : slotsOf c idx.segment ≤ c.instances.val * slotsOf c idx.segment :=
          Nat.le_mul_of_pos_left _ (by omega)
        omega
      have hwv : (uOf (slotsOf c idx.segment)).val = slotsOf c idx.segment := uOf_val (by omega)
      simp only [hi, ite_false, bind_ok,
        CoreModels.core.result.Result.Insts.CoreOpsTry_traitTryTResultInfallibleE.branch,
        index.ValueIndex.impl.segment, index.ValueIndex.impl.position, lift_eq,
        segment_slots_eq inst c idx.segment hw, GE.ge, UScalar.le_equiv, hwv,
        cast_usize_val _ (show UScalarTy.U32.numBits ≤ 32 by decide)]
      by_cases hs : slotsOf c idx.segment ≤ idx.position.val
      · simp [hs]
      · have hbase := hl.base k.val hkb idx.segment
        have hmk : k.val < (counts comp).length := by simp [counts, hk]
        have hgm : (counts comp).getD k.val 0 = c.instances.val := by
          simp [counts, hk, hc, List.getD_eq_getElem?_getD]
        have hgw : (widths comp idx.segment).getD k.val 0 = slotsOf c idx.segment := by
          simp [widths, hk, hc, List.getD_eq_getElem?_getD]
        have htot := packed_lt_total (counts comp) (widths comp idx.segment)
          (by simp [counts, widths]) (i := i.val) (s := idx.position.val) hmk (by omega) (by omega)
        rw [hl.total] at htot
        have hlen : lenOf comp idx.segment < 2 ^ 32 := by
          cases idx.segment
          · exact comp.public_len.hBounds
          · exact comp.witness_len.hBounds
        have hp : packed (counts comp) (widths comp idx.segment) k.val i.val idx.position.val =
            (baseOf (basesOf comp)[k.val] idx.segment).val + i.val * slotsOf c idx.segment +
              idx.position.val := by
          rw [hbase, packed, hgw]
        simp only [hs, ite_false]
        rw [position_eq inst comp _ c i idx hw (by omega), bind_ok, ← hp,
          composed_index_eq inst _ _ (by omega), bind_ok]
  · have hkb : ¬ k.val < (basesOf comp).length := hl.len ▸ hk
    rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega)]
    simp [CoreModels.core.result.Result.Insts.CoreOpsTry_traitTryTResultInfallibleE.branch,
      CoreModels.core.result.Result.Insts.CoreOpsTry_traitFromResidualResultInfallibleE.from_residual,
      CoreModels.core.convert.From.Blanket.from]

/-- A successful readdressing names an in-range triple, at its packed position. -/
theorem resolveSpec_ok {comp : component.Composition W} {k i : Std.Usize} {idx r : index.ValueIndex}
    (h : resolveSpec comp k i idx = .Ok r) :
    ∃ hk : k.val < (callsOf comp).length,
      i.val < ((callsOf comp)[k.val]).instances.val ∧
      idx.position.val < slotsOf (callsOf comp)[k.val] idx.segment ∧
      r = ⟨idx.segment, ⟨BitVec.ofNat 32
        (packed (counts comp) (widths comp idx.segment) k.val i.val idx.position.val)⟩⟩ := by
  unfold resolveSpec at h
  by_cases hk : k.val < (callsOf comp).length
  · rw [List.getElem?_eq_getElem hk] at h
    simp only at h
    split_ifs at h with h1 h2
    cases h
    exact ⟨hk, by omega, by omega, rfl⟩
  · rw [List.getElem?_eq_none (by omega)] at h
    cases h

/-- Two successful readdressings into one segment name the same word only for the same triple. -/
theorem resolve_injective (inst : word.Word W) (comp : component.Composition W) (hl : LaidOut comp)
    {k₁ k₂ i₁ i₂ : Std.Usize} {idx₁ idx₂ r : index.ValueIndex}
    (h₁ : component.Composition.resolve inst comp k₁ i₁ idx₁ = .ok (.Ok r))
    (h₂ : component.Composition.resolve inst comp k₂ i₂ idx₂ = .ok (.Ok r)) :
    k₁ = k₂ ∧ i₁ = i₂ ∧ idx₁ = idx₂ := by
  rw [resolve_eq inst comp hl, RustM.ok.injEq] at h₁ h₂
  obtain ⟨hk₁, hi₁, hs₁, rfl⟩ := resolveSpec_ok h₁
  obtain ⟨hk₂, hi₂, hs₂, he⟩ := resolveSpec_ok h₂
  obtain ⟨seg₁, pos₁⟩ := idx₁
  obtain ⟨seg₂, pos₂⟩ := idx₂
  simp only [index.ValueIndex.mk.injEq] at he ⊢
  obtain ⟨rfl, hp⟩ := he
  simp only at hs₁ hs₂
  have hlenw : (counts comp).length = (widths comp seg₁).length := by simp [counts, widths]
  have hm : (counts comp).length = (callsOf comp).length := by simp [counts]
  have gm : ∀ k (hk : k < (callsOf comp).length),
      (counts comp).getD k 0 = ((callsOf comp)[k]).instances.val := by
    intro k hk; simp [counts, hk, List.getD_eq_getElem?_getD]
  have gw : ∀ k (hk : k < (callsOf comp).length),
      (widths comp seg₁).getD k 0 = slotsOf (callsOf comp)[k] seg₁ := by
    intro k hk; simp [widths, hk, List.getD_eq_getElem?_getD]
  have hlen : lenOf comp seg₁ < 2 ^ 32 := by
    cases seg₁
    · exact comp.public_len.hBounds
    · exact comp.witness_len.hBounds
  have t₁ := packed_lt_total _ _ hlenw (hm ▸ hk₁) (i := i₁.val) (s := pos₁.val)
    (by rw [gm _ hk₁]; exact hi₁) (by rw [gw _ hk₁]; exact hs₁)
  have t₂ := packed_lt_total _ _ hlenw (hm ▸ hk₂) (i := i₂.val) (s := pos₂.val)
    (by rw [gm _ hk₂]; exact hi₂) (by rw [gw _ hk₂]; exact hs₂)
  rw [hl.total] at t₁ t₂
  have hv := congrArg UScalar.val hp
  rw [ofNat32_val, ofNat32_val, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hv
  obtain ⟨a, b, c⟩ := packed_injective _ _ hlenw (hm ▸ hk₁) (by rw [gm _ hk₁]; exact hi₁)
    (by rw [gw _ hk₁]; exact hs₁) (hm ▸ hk₂) (by rw [gm _ hk₂]; exact hi₂)
    (by rw [gw _ hk₂]; exact hs₂) hv
  exact ⟨UScalar.eq_of_val_eq a, UScalar.eq_of_val_eq b, rfl, UScalar.eq_of_val_eq c⟩

/-- A successful readdressing lands inside the composed segment. -/
theorem resolve_lt_len (inst : word.Word W) (comp : component.Composition W) (hl : LaidOut comp)
    {k i : Std.Usize} {idx r : index.ValueIndex}
    (h : component.Composition.resolve inst comp k i idx = .ok (.Ok r)) :
    r.segment = idx.segment ∧ r.position.val < lenOf comp idx.segment := by
  rw [resolve_eq inst comp hl, RustM.ok.injEq] at h
  obtain ⟨hk, hi, hs, rfl⟩ := resolveSpec_ok h
  have hlenw : (counts comp).length = (widths comp idx.segment).length := by simp [counts, widths]
  have hm : (counts comp).length = (callsOf comp).length := by simp [counts]
  have t := packed_lt_total _ _ hlenw (hm ▸ hk) (i := i.val) (s := idx.position.val)
    (by simp [counts, hk, List.getD_eq_getElem?_getD]; exact hi)
    (by simp [widths, hk, List.getD_eq_getElem?_getD]; exact hs)
  rw [hl.total] at t
  have hlen : lenOf comp idx.segment < 2 ^ 32 := by
    cases idx.segment
    · exact comp.public_len.hBounds
    · exact comp.witness_len.hBounds
  refine ⟨rfl, ?_⟩
  show (⟨BitVec.ofNat 32 _⟩ : Std.U32).val < _
  rw [ofNat32_val, Nat.mod_eq_of_lt (by omega)]
  exact t

end Plonky3Lean.Proofs.Word
