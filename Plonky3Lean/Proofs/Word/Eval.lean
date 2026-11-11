module

public import Plonky3Lean.Proofs.Word.Shift

@[expose] public section

/-!
# Operands: XOR sums of shifted words

An operand evaluates its terms in order.

Each term reads one word from its segment, shifts it and XORs it in.

The first term whose position lies outside its segment ends the evaluation with an error.
-/

open Aeneas Aeneas.Std CoreModels p3_word
open Plonky3Lean.Lib

namespace Plonky3Lean.Proofs.Word

variable {W : Type} (inst : word.Word W)

/-- The segment a term addresses. -/
def segOf (pub wit : Slice W) : index.Segment → Slice W
  | .Public => pub
  | .Witness => wit

/-- The word a term addresses, if its position lies inside its segment. -/
def lookup (pub wit : Slice W) (i : index.ValueIndex) : Option W :=
  (segOf pub wit i.segment).val[i.position.val]?

/-- The error naming a term whose position lies outside its segment. -/
def missing (pub wit : Slice W) (i : index.ValueIndex) : constraint.EvaluationError :=
  ⟨i.segment, i.position, (segOf pub wit i.segment).len⟩

/-- Evaluation, term by term: read, shift, XOR. -/
def evalTerms (xorf : W → W → W) (pub wit : Slice W) :
    List (shift.ShiftedValue W) → W → RustM (CoreModels.core.result.Result W constraint.EvaluationError)
  | [], v => .ok (.Ok v)
  | t :: ts, v =>
    match lookup pub wit t.index with
    | none => .ok (.Err (missing pub wit t.index))
    | some w => do
      let u ← shift.ShiftedValue.apply inst t w
      evalTerms xorf pub wit ts (xorf v u)

/-- A slice iterator, read as the slice of the items it has left. -/
abbrev iterSlice {T : Type} (s : CoreModels.core.slice.iter.Iter T) : Slice T := s

theorem iter_next_nil {T : Type} (s : CoreModels.core.slice.iter.Iter T) (hs : (iterSlice s).val = []) :
    CoreModels.core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.next s =
      .ok (.None, s) := by
  have hl : Slice.len (iterSlice s) = 0#usize := UScalar.eq_of_val_eq (by simp [hs])
  simp only [CoreModels.core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.next,
    CoreModels.rust_primitives.sequence.seq_len, bind_ok]
  rw [ite_eq_left hl]

theorem iter_next_cons {T : Type} (s : CoreModels.core.slice.iter.Iter T) (t : T) (ts : List T)
    (hs : (iterSlice s).val = t :: ts) :
    ∃ s' : CoreModels.core.slice.iter.Iter T,
      CoreModels.core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.next s =
        .ok (.Some t, s') ∧ (iterSlice s').val = ts := by
  have hl : ¬ Slice.len (iterSlice s) = 0#usize := fun e => by
    have := congrArg UScalar.val e; simp [hs] at this
  obtain ⟨s', hr, hs'⟩ := seq_remove_head (iterSlice s) t ts hs
  refine ⟨s', ?_, hs'⟩
  simp only [CoreModels.core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.next,
    CoreModels.rust_primitives.sequence.seq_len, bind_ok]
  rw [ite_eq_right hl, hr, bind_ok]
  rfl

theorem body_nil (pub wit : Slice W) (s : CoreModels.core.slice.iter.Iter (shift.ShiftedValue W))
    (hs : (iterSlice s).val = []) (v : W) :
    constraint.Operand.evaluate_loop.body inst pub wit s v = .ok (.done (.Ok v)) := by
  rw [constraint.Operand.evaluate_loop.body, iter_next_nil s hs, bind_ok]
  rfl

theorem body_cons (xorf : W → W → W)
    (hx : ∀ a b, inst.sealedSealedInst.xor a b = .ok (xorf a b)) (pub wit : Slice W)
    (s : CoreModels.core.slice.iter.Iter (shift.ShiftedValue W)) (t : shift.ShiftedValue W)
    (ts : List (shift.ShiftedValue W)) (hs : (iterSlice s).val = t :: ts) (v : W) :
    ∃ s' : CoreModels.core.slice.iter.Iter (shift.ShiftedValue W), (iterSlice s').val = ts ∧
      constraint.Operand.evaluate_loop.body inst pub wit s v =
        (match lookup pub wit t.index with
        | none => .ok (.done (.Err (missing pub wit t.index)))
        | some w => (do let u ← shift.ShiftedValue.apply inst t w; .ok (.cont (s', xorf v u)))) := by
  obtain ⟨s', hn, hs'⟩ := iter_next_cons s t ts hs
  refine ⟨s', hs', ?_⟩
  simp only [constraint.Operand.evaluate_loop.body, hn, bind_ok]
  obtain ⟨⟨seg, pos⟩, sh⟩ := t
  have hpos : (UScalar.cast .Usize pos).val = pos.val :=
    UScalar.cast_val_mod_pow_greater_numBits_eq _ _ (by simp [UScalarTy.numBits])
  cases seg <;>
  · simp only [shift.ShiftedValue.impl.index, index.ValueIndex.impl.segment,
      index.ValueIndex.impl.position, lift_eq, bind_ok, slice_get_usize_eq,
      core.option.OptionShared0T.copied, lookup, segOf, Aeneas.Std.uncurry_apply_pair, hpos]
    split <;> rename_i h <;>
      simp [h, hx, missing, segOf, CoreModels.core.option.Option.ok_or_else,
        constraint.Operand.evaluate.closure.Insts.CoreOpsFunctionFnOnceTupleEvaluationError.call_once,
        index.ValueIndex.impl.segment, index.ValueIndex.impl.position,
        CoreModels.core.result.Result.Insts.CoreOpsTry_traitTryTResultInfallibleE.branch,
        CoreModels.core.result.Result.Insts.CoreOpsTry_traitFromResidualResultInfallibleE.from_residual,
        CoreModels.core.slice.Slice.len, CoreModels.rust_primitives.slice.slice_length,
        CoreModels.core.convert.From.Blanket.from]

theorem evaluate_loop_eq (xorf : W → W → W)
    (hx : ∀ a b, inst.sealedSealedInst.xor a b = .ok (xorf a b)) (pub wit : Slice W)
    (ts : List (shift.ShiftedValue W)) :
    ∀ (s : CoreModels.core.slice.iter.Iter (shift.ShiftedValue W)) (v : W),
      (iterSlice s).val = ts →
      constraint.Operand.evaluate_loop inst s pub wit v = evalTerms inst xorf pub wit ts v := by
  induction ts with
  | nil =>
    intro s v hs
    rw [constraint.Operand.evaluate_loop, loop]
    simp only [body_nil inst pub wit s hs, bind_ok, evalTerms]
  | cons t ts ih =>
    intro s v hs
    obtain ⟨s', hs', hb⟩ := body_cons inst xorf hx pub wit s t ts hs v
    rw [constraint.Operand.evaluate_loop, loop]
    simp only [hb, evalTerms]
    cases lookup pub wit t.index with
    | none => simp only [bind_ok]
    | some w =>
      simp only [Aeneas.Std.bind_assoc, bind_ok]
      congr 1
      funext u
      exact ih s' _ hs'

theorem into_iter_eq {T : Type} (v : CoreModels.alloc.vec.Vec T) :
    CoreModels.alloc.SharedAVec.Insts.CoreIterTraitsCollectIntoIteratorSharedATIter.into_iter v =
      .ok (show CoreModels.core.slice.iter.Iter T from v) := by
  unfold CoreModels.alloc.SharedAVec.Insts.CoreIterTraitsCollectIntoIteratorSharedATIter.into_iter
    CoreModels.alloc.vec.Vec.as_slice CoreModels.core.slice.Slice.iter
  rw [CoreModels.rust_primitives.sequence.seq_to_slice]
  refine (bind_tc_ok (α := Slice T) v _).trans ?_
  exact bind_tc_ok (α := CoreModels.core.slice.iter.Iter T) v _

/-- Evaluating an operand starts from zero and walks its terms in order. -/
theorem evaluate_eq (xorf : W → W → W) (z : W) (hz : inst.ZERO = .ok z)
    (hx : ∀ a b, inst.sealedSealedInst.xor a b = .ok (xorf a b)) (op : constraint.Operand W)
    (pub wit : Slice W) :
    constraint.Operand.evaluate inst op pub wit = evalTerms inst xorf pub wit op.terms.val z := by
  simp only [constraint.Operand.evaluate, hz, bind_ok, into_iter_eq]
  exact evaluate_loop_eq inst xorf hx pub wit _ _ z rfl

/-- The outcome of evaluation when no shift panics.

- The first term outside its segment names the error.
- Otherwise the result is the XOR of every shifted word, in order. -/
def evalSpec (xorf : W → W → W) (f : shift.ShiftedValue W → W → W) (pub wit : Slice W)
    (ts : List (shift.ShiftedValue W)) (v : W) :
    CoreModels.core.result.Result W constraint.EvaluationError :=
  match ts.find? (fun t => (lookup pub wit t.index).isNone) with
  | some t => .Err (missing pub wit t.index)
  | none => .Ok (ts.foldl (fun acc t => xorf acc (f t ((lookup pub wit t.index).getD acc))) v)

theorem evalTerms_eq (xorf : W → W → W) (f : shift.ShiftedValue W → W → W)
    (pub wit : Slice W) (ts : List (shift.ShiftedValue W))
    (hf : ∀ t ∈ ts, ∀ w, shift.ShiftedValue.apply inst t w = .ok (f t w)) (v : W) :
    evalTerms inst xorf pub wit ts v = .ok (evalSpec xorf f pub wit ts v) := by
  induction ts generalizing v with
  | nil => rfl
  | cons t ts ih =>
    simp only [evalTerms, evalSpec, List.find?_cons]
    cases h : lookup pub wit t.index with
    | none => simp
    | some w =>
      simp only [Option.isNone_some, List.foldl_cons, hf t (by simp), bind_ok, h,
        Option.getD_some]
      rw [ih (fun t ht => hf t (by simp [ht]))]
      rfl

end Plonky3Lean.Proofs.Word
