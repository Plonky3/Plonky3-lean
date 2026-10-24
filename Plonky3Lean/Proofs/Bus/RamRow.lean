module

public import Plonky3Lean.Proofs.Bus.Adder

@[expose] public section

/-!
# The memory constraints on one row

The constraints are evaluated by a builder that collects every asserted value.

A row satisfies them when every collected value is zero.

Whenever its enabling factor is nonzero, the strict comparison then gives a nonzero gap and

```text
    value(right) = value(left) + value(delta)
```
-/

namespace Plonky3Lean.Proofs.Bus

open p3_bus.ram.mirror p3_bus.mirror p3_air.builder.mirror Finset

set_option linter.unusedSectionVars false

variable {F : Type _} [Field F] [DecidableEq F]

/-- The collecting state: the asserted values and the recorded declarations. -/
structure Collect (F : Type _) where
  asserts : List F
  records : List (String × BusDirection × List F × BusActivation F)

/-- Append asserted values. -/
def Collect.app (s : Collect F) (l : List F) : Collect F := { s with asserts := s.asserts ++ l }

theorem Collect.app_app (s : Collect F) (l l' : List F) : (s.app l).app l' = s.app (l ++ l') := by
  simp [Collect.app]

/-- Every asserted value is zero. -/
def Collect.Holds (s : Collect F) : Prop := ∀ x ∈ s.asserts, x = 0

theorem Collect.holds_app {s : Collect F} {l : List F} :
    (s.app l).Holds ↔ s.Holds ∧ ∀ x ∈ l, x = 0 := by
  simp [Collect.Holds, Collect.app, or_imp, forall_and]

/-- The collecting builder of one row: a window and the three selectors. -/
def rowBuilder (main : RowWindow F) (first last trans : F) : BusBuilder F F (Collect F) where
  toExprOps := fieldExprOps F
  main _ := main
  preprocessed _ := ⟨[], []⟩
  is_first_row _ := first
  is_last_row _ := last
  is_transition _ := trans
  assert_zero s x := s.app [x]
  public_values _ := []
  periodic_values _ := []
  record s b d f a := { s with records := s.records ++ [(b, d, f, a)] }

/-- A builder over the field whose assertions collect their value times a fixed condition. -/
structure IsCollect (B : AirBuilder F F (Collect F)) (c : F) : Prop where
  ops : B.toExprOps = fieldExprOps F
  assert : ∀ s x, B.assert_zero s x = s.app [c * x]

theorem isCollect_row (main : RowWindow F) (first last trans : F) :
    IsCollect (rowBuilder main first last trans).toAirBuilder 1 :=
  ⟨rfl, fun s x => by simp [rowBuilder]⟩

theorem IsCollect.when {B : AirBuilder F F (Collect F)} {c : F} (hB : IsCollect B c) (d : F) :
    IsCollect (B.when d) (c * d) :=
  ⟨by simp [AirBuilder.when, hB.ops], fun s x => by
    simp [AirBuilder.when, hB.assert, hB.ops, fieldExprOps, mul_assoc]⟩

/-- A loop whose every step appends values fixed by its index appends their concatenation. -/
theorem foldlM_app (G : ℕ → Option (List F)) (body : Collect F → ℕ → Option (Collect F))
    (hbody : ∀ s i, body s i = (G i).map s.app) (ls : ℕ → List F) :
    ∀ (n : ℕ), (∀ i < n, G i = some (ls i)) → ∀ (s : Collect F),
      (List.range n).foldlM body s = some (s.app ((List.range n).flatMap ls))
  | 0, _, s => by simp [Collect.app]
  | n + 1, hG, s => by
    rw [List.range_succ, List.foldlM_append, foldlM_app G body hbody ls n
      (fun i hi => hG i (by omega)) s]
    simp [hbody, hG n (by omega), Collect.app_app]

/-- The same, with each step's values given on the loop's range only. -/
theorem foldlM_app' (body : Collect F → ℕ → Option (Collect F)) (ls : ℕ → List F) :
    ∀ (n : ℕ), (∀ s, ∀ i < n, body s i = some (s.app (ls i))) → ∀ (s : Collect F),
      (List.range n).foldlM body s = some (s.app ((List.range n).flatMap ls))
  | 0, _, s => by simp [Collect.app]
  | n + 1, hb, s => by
    rw [List.range_succ, List.foldlM_append, foldlM_app' body ls n
      (fun s i hi => hb s i (by omega)) s]
    simp [hb _ n (by omega), Collect.app_app]

theorem getElem?_of_lt {l : List F} {i : ℕ} (h : i < l.length) : l[i]? = some (l.getD i 0) := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]

/-- The running flag a digit is compared against.

It is the digit itself, then the or of the previous flag and the digit. -/
def running (delta nonzero : List F) (i : ℕ) : F :=
  if i = 0 then delta.getD 0 0
  else p3_bus.ram.mirror.or (fieldExprOps F) (nonzero.getD (i - 1) 0) (delta.getD i 0)

/-- The three values one digit of the comparison asserts, before the enabling factors. -/
def digitAsserts (left right delta carry nonzero : List F) (i : ℕ) : List F :=
  [right.getD i 0 - xor3 (fieldExprOps F) (left.getD i 0) (delta.getD i 0) (carry.getD i 0),
   carry.getD (i + 1) 0 - majority (fieldExprOps F) (left.getD i 0) (delta.getD i 0) (carry.getD i 0),
   nonzero.getD i 0 - running delta nonzero i]

/-- **The comparison asserts**, in order:

- the zero carry in
- three values per digit
- the zero carry out
- the nonzero gap. -/
theorem strict_increase_eq {B : AirBuilder F F (Collect F)} {c : F} (hB : IsCollect B c)
    (s : Collect F) (en : F) {left right delta carry nonzero : List F}
    (hr : right.length = left.length) (hd : left.length ≤ delta.length)
    (hc : left.length < carry.length) (hn : left.length ≤ nonzero.length) (h0 : 0 < left.length) :
    assert_strict_increase B s en left right delta carry nonzero = some (s.app
      ([c * (en * carry.getD 0 0)] ++
        (List.range left.length).flatMap (fun i =>
          (digitAsserts left right delta carry nonzero i).map (fun x => c * (en * x))) ++
        [c * (en * carry.getD left.length 0),
         c * (en * (1 - nonzero.getD (left.length - 1) 0))])) := by
  obtain ⟨hops, hassert⟩ := hB
  unfold assert_strict_increase
  simp only [hr, hd, hc, hn, and_self, not_true_eq_false, ite_false, Nat.ne_of_gt h0,
    getElem?_of_lt (by omega : 0 < carry.length), getElem?_of_lt hc,
    getElem?_of_lt (by omega : left.length - 1 < nonzero.length), Option.bind_eq_bind,
    Option.bind_some]
  rw [foldlM_app (fun i => if i < left.length then
      some ((digitAsserts left right delta carry nonzero i).map (fun x => c * (en * x))) else none)
    _ ?hb (fun i => (digitAsserts left right delta carry nonzero i).map (fun x => c * (en * x))) _
    (fun i hi => by simp [hi])]
  · simp [hassert, hops, fieldExprOps, Collect.app_app]
  case hb =>
    intro s i
    by_cases hi : i < left.length
    · rw [getElem?_of_lt hi, getElem?_of_lt (by omega : i < delta.length),
        getElem?_of_lt (by omega : i < carry.length), getElem?_of_lt (by omega : i < right.length),
        getElem?_of_lt (by omega : i + 1 < carry.length), getElem?_of_lt (by omega : i < nonzero.length)]
      by_cases h0 : i = 0
      · simp [h0, List.ne_nil_of_length_pos (by omega : 0 < left.length), hassert, hops, fieldExprOps, digitAsserts, running,
          Collect.app_app]
      · rw [getElem?_of_lt (by omega : i - 1 < nonzero.length)]
        simp [h0, hi, hassert, hops, fieldExprOps, digitAsserts, running, Collect.app_app]
    · simp [hi]


/-- **The comparison is an unsigned strict order.**

Suppose that:

- the comparison's asserts vanish
- its enabling factors are nonzero
- the earlier key and the gap are bits.

Then right = left + delta as k-digit numbers, with a nonzero gap. -/
theorem strict_increase_sound {c en : F} (hc : c ≠ 0) (hen : en ≠ 0)
    {left right delta carry nonzero : List F} (hk : 0 < left.length)
    (hl : ∀ i < left.length, IsBit (left.getD i 0)) (hd : ∀ i < left.length, IsBit (delta.getD i 0))
    (hz : ∀ x ∈ [c * (en * carry.getD 0 0)] ++
        (List.range left.length).flatMap (fun i =>
          (digitAsserts left right delta carry nonzero i).map (fun x => c * (en * x))) ++
        [c * (en * carry.getD left.length 0),
         c * (en * (1 - nonzero.getD (left.length - 1) 0))], x = 0) :
    pv right left.length = pv left left.length + pv delta left.length ∧ 0 < pv delta left.length := by
  have hce : ∀ x : F, c * (en * x) = 0 → x = 0 := fun x h => by simpa [hc, hen] using h
  have hdig : ∀ i < left.length, ∀ x ∈ digitAsserts left right delta carry nonzero i, x = 0 :=
    fun i hi x hx => hce x (hz _ (List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inr
      (List.mem_flatMap.2 ⟨i, List.mem_range.2 hi, List.mem_map.2 ⟨x, hx, rfl⟩⟩))))))
  have h0 := hce _ (hz (c * (en * carry.getD 0 0)) (by simp))
  have hcar := hce _ (hz (c * (en * carry.getD left.length 0)) (by simp))
  have hnz := hce _ (hz (c * (en * (1 - nonzero.getD (left.length - 1) 0))) (by simp))
  have hdig' : ∀ i < left.length,
      right.getD i 0 = xor3 (fieldExprOps F) (left.getD i 0) (delta.getD i 0) (carry.getD i 0) ∧
      carry.getD (i + 1) 0 = majority (fieldExprOps F) (left.getD i 0) (delta.getD i 0)
        (carry.getD i 0) ∧ nonzero.getD i 0 = running delta nonzero i := fun i hi => by
    have := hdig i hi
    simp only [digitAsserts, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at this
    exact ⟨sub_eq_zero.1 this.1, sub_eq_zero.1 this.2.1, sub_eq_zero.1 this.2.2⟩
  obtain ⟨-, hrip⟩ := ripple left.length hl hd h0 (fun i hi => (hdig' i hi).1)
    (fun i hi => (hdig' i hi).2.1)
  rw [hcar] at hrip
  simp only [nb, zero_ne_one, ite_false, mul_zero, add_zero] at hrip
  refine ⟨hrip, ?_⟩
  obtain ⟨-, hor⟩ := running_or (delta := delta) (nonzero := nonzero) (left.length - 1)
    (fun i hi => hd i (by omega)) (by rw [(hdig' 0 hk).2.2]; simp [running])
    (fun i hi => by rw [(hdig' (i + 1) (by omega)).2.2]; simp [running])
  obtain ⟨i, hi, h1⟩ := hor.1 (by linear_combination -hnz)
  exact pv_pos (by omega) h1

end Plonky3Lean.Proofs.Bus
