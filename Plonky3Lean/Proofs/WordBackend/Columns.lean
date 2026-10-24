module

public import P3WordBackend
public import Plonky3Lean.Proofs.Word.Validate
public import Plonky3Lean.Proofs.Word.Composition
public import Plonky3Lean.Proofs.WordBackend.Lift

@[expose] public section

/-!
# The packed relation columns are the scalar operand values

A column entry reads, shifts and XORs the terms of one operand, as the scalar evaluator does.

So on a flat statement whose addresses are in range, each column holds the scalar value of its operand.

The columns of a statement are built without panicking exactly when every operand denotes a word.
-/

open Aeneas Aeneas.Std CoreModels p3_word Plonky3Lean.Proofs.Word
open p3_word_backend.columns.mirror

set_option linter.unusedSectionVars false

namespace Plonky3Lean.Proofs.WordBackend

variable {W : Type} [DecidableEq W] {inst : word.Word W} (M : Model inst)

theorem get_eq (pub wit : Slice W) (i : index.ValueIndex) :
    p3_word_backend.columns.mirror.get pub.val wit.val i = lookup pub wit i := by
  unfold p3_word_backend.columns.mirror.get lookup segOf; cases i.segment <;> rfl

/-- The scalar value of an operand, or zero when a term lies outside its segment. -/
def val (pub wit : Slice W) (op : constraint.Operand W) : W := (opVal M pub wit op).getD M.zero

theorem readTerm_some {pub wit : Slice W} {t : shift.ShiftedValue W} {w : W} (acc : W)
    (h : lookup pub wit t.index = some w) (hv : M.valid t) :
    readTerm inst M.xorf pub.val wit.val RustM.ok acc t = RustM.ok (M.xorf acc (M.term t w)) := by
  simp [readTerm, get_eq, h, M.happly t w hv]

theorem readTerm_none {pub wit : Slice W} {t : shift.ShiftedValue W} (acc : W)
    (h : lookup pub wit t.index = none) :
    readTerm inst M.xorf pub.val wit.val RustM.ok acc t = RustM.fail .panic := by
  simp [readTerm, get_eq, h]

theorem foldl_eval (pub wit : Slice W) (ts : List (shift.ShiftedValue W))
    (hv : ∀ t ∈ ts, M.valid t) (acc : W) :
    ts.foldlM (readTerm inst M.xorf pub.val wit.val RustM.ok) acc =
      match ts.find? (fun t => (lookup pub wit t.index).isNone) with
      | some _ => RustM.fail .panic
      | none => RustM.ok (ts.foldl (fun acc t =>
          M.xorf acc (M.term t ((lookup pub wit t.index).getD acc))) acc) := by
  induction ts generalizing acc with
  | nil => rfl
  | cons t ts ih =>
    simp only [List.foldlM_cons, List.find?_cons, List.foldl_cons]
    cases h : lookup pub wit t.index with
    | none => simp [readTerm_none M acc h]
    | some w =>
      simp only [readTerm_some M acc h (hv t (by simp)), Aeneas.Std.bind_tc_ok, Option.isNone_some,
        Option.getD_some]
      exact ih (fun t' ht' => hv t' (by simp [ht'])) _

/-- One operand evaluates to its scalar value, or panics when a term lies outside its segment. -/
theorem evaluate_eq (pub wit : Slice W) (op : constraint.Operand W) (hv : OpValid M op) :
    evaluate inst M.xorf pub.val wit.val RustM.ok op =
      match opVal M pub wit op with
      | some v => RustM.ok v
      | none => RustM.fail .panic := by
  unfold evaluate opVal evalSpec
  rw [M.hzero, bind_ok, foldl_eval M pub wit (vlist op.terms) hv M.zero]
  split <;> rename_i h <;> simp only [vlist] at h <;> simp [h]

theorem lookup_isSome {sys : system.ConstraintSystem W} {pub wit : Slice W}
    (hp : pub.len = UScalar.cast .Usize sys.public_len)
    (hw : wit.len = UScalar.cast .Usize sys.witness_len)
    {t : shift.ShiftedValue W} (hr : inRange sys t = true) : (lookup pub wit t.index).isSome := by
  unfold inRange sysLen at hr
  unfold lookup segOf
  have hp' := congrArg UScalar.val hp
  have hw' := congrArg UScalar.val hw
  rw [Slice.len_val] at hp' hw'
  unfold Slice.length at hp' hw'
  cases hs : t.index.segment <;> simp only [hs, decide_eq_true_eq] at hr ⊢ <;>
    exact Option.isSome_iff_exists.2 ⟨_, List.getElem?_eq_getElem (by omega)⟩

theorem opVal_isSome {sys : system.ConstraintSystem W} {pub wit : Slice W}
    (hp : pub.len = UScalar.cast .Usize sys.public_len)
    (hw : wit.len = UScalar.cast .Usize sys.witness_len)
    {op : constraint.Operand W} (h : opIn sys op) : (opVal M pub wit op).isSome := by
  unfold opVal evalSpec
  have hnone : (vecSlice op.terms).val.find? (fun t => (lookup pub wit t.index).isNone) = none := by
    rw [List.find?_eq_none]
    intro t ht
    have := lookup_isSome hp hw (h t ht)
    cases hl : lookup pub wit t.index <;> simp_all
  rw [hnone]; rfl

/-- The scalar columns of a flat system: each operand's value, in the backend's order. -/
def colsOf (sys : system.ConstraintSystem W) (pub wit : Slice W) : OperationColumns W where
  zero := (vecSlice sys.zero_constraints).val.map fun c => val M pub wit c.value
  and_left := (vecSlice sys.and_constraints).val.map fun c => val M pub wit c.left
  and_right := (vecSlice sys.and_constraints).val.map fun c => val M pub wit c.right
  and_output := (vecSlice sys.and_constraints).val.map fun c => val M pub wit c.output
  mul_left := (vecSlice sys.integer_mul_constraints).val.map fun c => val M pub wit c.left
  mul_right := (vecSlice sys.integer_mul_constraints).val.map fun c => val M pub wit c.right
  mul_low := (vecSlice sys.integer_mul_constraints).val.map fun c => val M pub wit c.low
  mul_high := (vecSlice sys.integer_mul_constraints).val.map fun c => val M pub wit c.high

theorem evaluate_in {sys : system.ConstraintSystem W} {pub wit : Slice W}
    (hp : pub.len = UScalar.cast .Usize sys.public_len)
    (hw : wit.len = UScalar.cast .Usize sys.witness_len)
    {op : constraint.Operand W} (hv : OpValid M op) (h : opIn sys op) :
    evaluate inst M.xorf pub.val wit.val RustM.ok op = RustM.ok (val M pub wit op) := by
  rw [evaluate_eq M pub wit op hv]
  obtain ⟨v, hv'⟩ := Option.isSome_iff_exists.1 (opVal_isSome M hp hw h)
  simp [hv', val]

theorem len_eq_of_len {s : Slice W} {n : Std.U32}
    (h : s.len = UScalar.cast .Usize n) : s.val.length = n.val := by
  have := congrArg UScalar.val h
  rw [Slice.len_val, cast_usize_val _ (by decide)] at this
  exact this

/-- On a flat system whose addresses are in range, the columns are the scalar operand values. -/
theorem columns_flat (sys : system.ConstraintSystem W) (pub wit : Slice W) (hv : SysValid M sys)
    (hp : pub.len = UScalar.cast .Usize sys.public_len)
    (hw : wit.len = UScalar.cast .Usize sys.witness_len) (hin : validateSpec sys = .Ok ()) :
    OperationColumns.new inst M.xorf (.Flat sys) pub.val wit.val =
      RustM.ok (.ok (colsOf M sys pub wit)) := by
  obtain ⟨hz, ha, hm⟩ := (validateSpec_ok sys).1 hin
  obtain ⟨vz, va, vm⟩ := hv
  have ev := fun {op : constraint.Operand W} (v : OpValid M op) (i : opIn sys op) =>
    evaluate_in M hp hw v i
  unfold OperationColumns.new check_shape Statement.public_len Statement.witness_len
  rw [len_eq_of_len hp, len_eq_of_len hw]
  simp only [ne_eq, not_true_eq_false, ↓reduceIte]
  unfold OperationColumns.extend
  simp only []
  rw [mapM_ok _ (fun c => val M pub wit c.value) (vlist sys.zero_constraints)
    (fun c hc => ev (vz c hc) (hz c hc))]
  rw [mapM_ok _ (fun c => (val M pub wit c.left, val M pub wit c.right, val M pub wit c.output))
    (vlist sys.and_constraints) (fun c hc => by
      obtain ⟨v1, v2, v3⟩ := va c hc; obtain ⟨i1, i2, i3⟩ := ha c hc
      simp [ev v1 i1, ev v2 i2, ev v3 i3])]
  rw [mapM_ok _ (fun c => (val M pub wit c.left, val M pub wit c.right, val M pub wit c.low,
      val M pub wit c.high)) (vlist sys.integer_mul_constraints) (fun c hc => by
      obtain ⟨v1, v2, v3, v4⟩ := vm c hc; obtain ⟨i1, i2, i3, i4⟩ := hm c hc
      simp [ev v1 i1, ev v2 i2, ev v3 i3, ev v4 i4])]
  simp [colsOf, OperationColumns.empty, Function.comp_def]

end Plonky3Lean.Proofs.WordBackend
