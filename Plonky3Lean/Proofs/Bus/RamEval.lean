module

public import Plonky3Lean.Proofs.Bus.RamRow

@[expose] public section

/-!
# The memory constraints, evaluated

A validated statement lays its columns out back to back:

```text
    op | cell digits | clock digits | value | same | gap digits | carries | flags | [closing]
```

On rows of that width, each constraint group appends a fixed list of values to the collecting builder.
-/

namespace Plonky3Lean.Proofs.Bus

open p3_bus.ram.mirror p3_bus.mirror p3_air.builder.mirror Finset

set_option linter.unusedSectionVars false

variable {F : Type _} [Field F] [DecidableEq F]

/-- The layout a validated statement produces. -/
def stdLayout (st : RamStatement) : RamLayout :=
  let ab := st.address_bits
  let tb := st.timestamp_bits
  let vw := st.value_width
  let cb := max ab tb
  { address_bits := ab, timestamp_bits := tb, value_width := vw, compare_bits := cb,
    operation := 0, address := 1, timestamp := 1 + ab, value := 1 + ab + tb,
    same_address := 1 + ab + tb + vw, compare_delta := 1 + ab + tb + vw + 1,
    compare_carry := 1 + ab + tb + vw + 1 + cb,
    compare_nonzero := 1 + ab + tb + vw + 1 + cb + (cb + 1),
    group_end := 1 + ab + tb + vw + 1 + cb + (cb + 1) + cb,
    width := 1 + ab + tb + vw + 1 + cb + (cb + 1) + cb + if st.boundary.is_segment then 1 else 0 }

theorem take_bind {β : Type} {n c : ℕ} {f : ℕ × ℕ → Except RamError β} {v : β}
    (h : (take n c >>= f) = .ok v) : f (n, n + c) = .ok v := by
  unfold take checked_add at h
  split_ifs at h
  · exact h
  · cases h

theorem layout_of_new {st : RamStatement} {L : RamLayout} (h : RamLayout.new st = .ok L) :
    st.validate = .ok () ∧ L = stdLayout st := by
  unfold RamLayout.new at h
  cases hv : st.validate with
  | error e => simp [hv] at h; cases h
  | ok u =>
    refine ⟨rfl, ?_⟩
    rw [hv] at h
    replace h := take_bind h; dsimp only at h
    replace h := take_bind h; dsimp only at h
    replace h := take_bind h; dsimp only at h
    replace h := take_bind h; dsimp only at h
    replace h := take_bind h; dsimp only at h
    replace h := take_bind h; dsimp only at h
    replace h := take_bind h; dsimp only at h
    replace h := take_bind h; dsimp only at h
    cases h
    simp only [stdLayout, zero_add]

/-- A valid statement has at least two accesses, 1 to 64 cell and clock digits, and a nonempty value. -/
theorem validate_dims {st : RamStatement} (h : st.validate = .ok ()) :
    2 ≤ st.access_count ∧ 1 ≤ st.address_bits ∧ st.address_bits ≤ 64 ∧ 1 ≤ st.timestamp_bits ∧
      st.timestamp_bits ≤ 64 ∧ 1 ≤ st.value_width := by
  unfold RamStatement.validate at h
  simp only [MIN_RAM_ACCESS_COUNT, MAX_RAM_BIT_WIDTH] at h
  by_cases c1 : st.access_count < 2
  · rw [ite_eq_left c1] at h; cases h
  rw [ite_eq_right c1] at h
  by_cases c2 : ¬(st.access_count ≠ 0 ∧ st.access_count &&& (st.access_count - 1) = 0)
  · rw [ite_eq_left c2] at h; cases h
  rw [ite_eq_right c2] at h
  by_cases c3 : st.address_bits = 0 ∨ st.address_bits > 64
  · rw [ite_eq_left c3] at h; cases h
  rw [ite_eq_right c3] at h
  by_cases c4 : st.timestamp_bits = 0 ∨ st.timestamp_bits > 64
  · rw [ite_eq_left c4] at h; cases h
  rw [ite_eq_right c4] at h
  by_cases c5 : st.value_width = 0
  · rw [ite_eq_left c5] at h; cases h
  omega

theorem flatMap_singleton_eq {α β : Type _} (f : α → β) (l : List α) :
    l.flatMap (fun x => [f x]) = l.map f := by
  induction l <;> simp_all

/-- x (x - 1), which vanishes exactly on the bits. -/
def bc (x : F) : F := x * (x - 1)

theorem bc_eq_zero {x : F} : bc x = 0 ↔ IsBit x := by
  simp [bc, IsBit, sub_eq_zero]

/-- The values the booleanity group asserts: every cell, clock and gap digit of the row. -/
def boolAsserts (L : RamLayout) (cur : List F) : List F :=
  (List.range L.address_bits).map (fun i => bc (cur.getD (L.address + i) 0)) ++
  (List.range L.timestamp_bits).map (fun i => bc (cur.getD (L.timestamp + i) 0)) ++
  (List.range L.compare_bits).map (fun i => bc (cur.getD (L.compare_delta + i) 0))

theorem booleanity_eq {st : RamStatement} {B : AirBuilder F F (Collect F)} {c : F}
    (hB : IsCollect B c) (s : Collect F) {cur : List F} (hcur : (B.main s).current = cur)
    (hw : cur.length = (stdLayout st).width) :
    (RamAir.mk st (stdLayout st)).eval_booleanity B s =
      some (s.app ((boolAsserts (stdLayout st) cur).map (c * ·))) := by
  have hloop : ∀ (off n : ℕ), off + n ≤ cur.length → ∀ s,
      (List.range n).foldlM (fun s bit => (cur[off + bit]?).bind fun x =>
        some (B.assert_bool s x)) s =
      some (s.app ((List.range n).flatMap fun i => [c * bc (cur.getD (off + i) 0)])) :=
    fun off n hn s => foldlM_app' _ _ n (fun s i hi => by
      rw [getElem?_of_lt (by omega)]
      simp [AirBuilder.assert_bool, AirBuilder.bool_check, hB.assert, hB.ops, fieldExprOps, bc]) s
  unfold RamAir.eval_booleanity
  simp only [hcur, Option.bind_eq_bind, Option.pure_def]
  simp only [stdLayout] at hw ⊢
  rw [hloop _ _ (by omega), Option.bind_some, hloop _ _ (by omega), Option.bind_some,
    hloop _ _ (by omega)]
  simp [Collect.app_app, boolAsserts, flatMap_singleton_eq, Function.comp_def]

section RowBuilder

variable (m : RowWindow F) (first last trans : F)

@[simp] theorem rowBuilder_main (s : Collect F) : (rowBuilder m first last trans).main s = m := rfl
@[simp] theorem rowBuilder_first (s : Collect F) :
    (rowBuilder m first last trans).is_first_row s = first := rfl
@[simp] theorem rowBuilder_last (s : Collect F) :
    (rowBuilder m first last trans).is_last_row s = last := rfl
@[simp] theorem rowBuilder_trans (s : Collect F) :
    (rowBuilder m first last trans).is_transition s = trans := rfl
@[simp] theorem rowBuilder_mul (x y : F) : (rowBuilder m first last trans).mul x y = x * y := rfl
@[simp] theorem rowBuilder_sub (x y : F) : (rowBuilder m first last trans).sub x y = x - y := rfl
@[simp] theorem rowBuilder_add (x y : F) : (rowBuilder m first last trans).add x y = x + y := rfl
@[simp] theorem rowBuilder_const (x : F) : (rowBuilder m first last trans).const x = x := rfl

end RowBuilder

theorem obind_some {α β : Type _} (a : α) (f : α → Option β) : (some a >>= f) = f a := rfl

theorem slice_eq {E : Type _} {l : List E} {a n : ℕ} (h : a + n ≤ l.length) :
    slice l a n = some ((l.drop a).take n) := by
  simp [slice, h]

theorem length_slice {E : Type _} {l : List E} {a n : ℕ} (h : a + n ≤ l.length) :
    ((l.drop a).take n).length = n := by
  simp; omega

theorem getD_slice {l : List F} {a n i : ℕ} (hi : i < n) :
    ((l.drop a).take n).getD i 0 = l.getD (a + i) 0 := by
  simp [List.getD_eq_getElem?_getD, hi]

/-- The values the opening rule of a self-contained proof asserts: a read's value components. -/
def startAsserts (L : RamLayout) (row : List F) : List F :=
  (List.range L.value_width).map fun k => (1 - row.getD L.operation 0) * row.getD (L.value + k) 0

theorem run_start_eq {st : RamStatement} (hsp : st.boundary = .SingleProof)
    {B : AirBuilder F F (Collect F)} {c : F} (hB : IsCollect B c) (s : Collect F) {row : List F}
    (hw : row.length = (stdLayout st).width) :
    (RamAir.mk st (stdLayout st)).eval_run_start B s row =
      some (s.app ((startAsserts (stdLayout st) row).map (c * ·))) := by
  unfold RamAir.eval_run_start
  simp only [hsp, Option.bind_eq_bind, Option.pure_def]
  simp only [stdLayout] at hw ⊢
  rw [getElem?_of_lt (by omega), Option.bind_some, foldlM_app' _
    (fun k => [c * ((1 - row.getD 0 0) * row.getD (1 + st.address_bits + st.timestamp_bits + k) 0)])
    _ (fun s k hk => by
      rw [getElem?_of_lt (by omega)]
      simp [hB.assert, hB.ops, fieldExprOps])]
  simp [startAsserts, flatMap_singleton_eq, Function.comp_def]

/-- The values one strict comparison asserts. -/
def strictAsserts (c en : F) (left right delta carry nonzero : List F) : List F :=
  [c * (en * carry.getD 0 0)] ++
    (List.range left.length).flatMap (fun i =>
      (digitAsserts left right delta carry nonzero i).map (fun x => c * (en * x))) ++
    [c * (en * carry.getD left.length 0), c * (en * (1 - nonzero.getD (left.length - 1) 0))]

/-- The values the order group asserts on a row of a self-contained proof. -/
def orderAsserts (L : RamLayout) (first trans : F) (cur nxt : List F) : List F :=
  let same := nxt.getD L.same_address 0
  let delta := (nxt.drop L.compare_delta).take L.compare_bits
  let carry := (nxt.drop L.compare_carry).take (L.compare_bits + 1)
  let nonzero := (nxt.drop L.compare_nonzero).take L.compare_bits
  [first * cur.getD L.same_address 0] ++ (startAsserts L cur).map (first * ·) ++
  (List.range L.address_bits).map (fun b =>
    trans * (same * (nxt.getD (L.address + b) 0 - cur.getD (L.address + b) 0))) ++
  strictAsserts trans (1 - same) ((cur.drop L.address).take L.address_bits)
    ((nxt.drop L.address).take L.address_bits) delta carry nonzero ++
  strictAsserts trans same ((cur.drop L.timestamp).take L.timestamp_bits)
    ((nxt.drop L.timestamp).take L.timestamp_bits) delta carry nonzero ++
  (List.range L.value_width).map (fun k => trans * ((1 - nxt.getD L.operation 0) *
    (nxt.getD (L.value + k) 0 - same * cur.getD (L.value + k) 0)))

theorem order_eq {st : RamStatement} (hsp : st.boundary = .SingleProof)
    (hv : st.validate = .ok ()) (first last trans : F) (s : Collect F) {cur nxt : List F}
    (hc : cur.length = (stdLayout st).width) (hn : nxt.length = (stdLayout st).width) :
    (RamAir.mk st (stdLayout st)).eval_order (rowBuilder ⟨cur, nxt⟩ first last trans).toAirBuilder s =
      some (s.app (orderAsserts (stdLayout st) first trans cur nxt)) := by
  obtain ⟨-, hab, -, htb, -, -⟩ := validate_dims hv
  have hfirst := (isCollect_row (F := F) ⟨cur, nxt⟩ first last trans).when first
  have htrans := (isCollect_row (F := F) ⟨cur, nxt⟩ first last trans).when trans
  unfold RamAir.eval_order
  dsimp only [AirBuilder.when_first_row, AirBuilder.when_transition, rowBuilder_main,
    rowBuilder_first, rowBuilder_trans]
  have hw := hc
  simp only [stdLayout] at hw
  have L1 : (stdLayout st).same_address < cur.length := by simp [stdLayout]; omega
  have L2 : (stdLayout st).same_address < nxt.length := by simp [stdLayout] at hn ⊢; omega
  have L3 : (stdLayout st).compare_delta + (stdLayout st).compare_bits ≤ nxt.length := by
    simp [stdLayout] at hn ⊢; omega
  have L4 : (stdLayout st).compare_carry + ((stdLayout st).compare_bits + 1) ≤ nxt.length := by
    simp [stdLayout] at hn ⊢; omega
  have L5 : (stdLayout st).compare_nonzero + (stdLayout st).compare_bits ≤ nxt.length := by
    simp [stdLayout] at hn ⊢; omega
  have L6 : (stdLayout st).address + (stdLayout st).address_bits ≤ cur.length := by
    simp [stdLayout]; omega
  have L7 : (stdLayout st).address + (stdLayout st).address_bits ≤ nxt.length := by
    simp [stdLayout] at hn ⊢; omega
  have L8 : (stdLayout st).timestamp + (stdLayout st).timestamp_bits ≤ cur.length := by
    simp [stdLayout]; omega
  have L9 : (stdLayout st).timestamp + (stdLayout st).timestamp_bits ≤ nxt.length := by
    simp [stdLayout] at hn ⊢; omega
  have L10 : (stdLayout st).operation < nxt.length := by simp [stdLayout] at hn ⊢; omega
  have L11 : (stdLayout st).value + (stdLayout st).value_width ≤ cur.length := by
    simp [stdLayout]; omega
  have L12 : (stdLayout st).value + (stdLayout st).value_width ≤ nxt.length := by
    simp [stdLayout] at hn ⊢; omega
  have hcb : (stdLayout st).address_bits ≤ (stdLayout st).compare_bits ∧
      (stdLayout st).timestamp_bits ≤ (stdLayout st).compare_bits := by simp [stdLayout]
  rw [getElem?_of_lt L1, obind_some, hfirst.assert, run_start_eq hsp hfirst _ hc,
    obind_some, getElem?_of_lt L2, obind_some,
    foldlM_app' _ (fun b => [1 * trans * (nxt.getD (stdLayout st).same_address 0 *
      (nxt.getD ((stdLayout st).address + b) 0 - cur.getD ((stdLayout st).address + b) 0))]) _
      (fun s b hb => by
        rw [getElem?_of_lt (by omega), getElem?_of_lt (by omega)]
        simp [htrans.assert]),
    obind_some, slice_eq L3, obind_some, slice_eq L4, obind_some,
    slice_eq L5, obind_some, slice_eq L6, obind_some, slice_eq L7, obind_some,
    strict_increase_eq htrans _ _ (by rw [length_slice L7, length_slice L6])
      (by rw [length_slice L6, length_slice L3]; exact hcb.1)
      (by rw [length_slice L6, length_slice L4]; omega)
      (by rw [length_slice L6, length_slice L5]; exact hcb.1)
      (by rw [length_slice L6]; simp [stdLayout]; omega),
    obind_some, slice_eq L8, obind_some, slice_eq L9, obind_some,
    strict_increase_eq htrans _ _ (by rw [length_slice L9, length_slice L8])
      (by rw [length_slice L8, length_slice L3]; exact hcb.2)
      (by rw [length_slice L8, length_slice L4]; omega)
      (by rw [length_slice L8, length_slice L5]; exact hcb.2)
      (by rw [length_slice L8]; simp [stdLayout]; omega),
    obind_some, getElem?_of_lt L10, obind_some,
    foldlM_app' _ (fun k => [1 * trans * ((1 - nxt.getD (stdLayout st).operation 0) *
      (nxt.getD ((stdLayout st).value + k) 0 - nxt.getD (stdLayout st).same_address 0 *
        cur.getD ((stdLayout st).value + k) 0))]) _
      (fun s k hk => by
        rw [getElem?_of_lt (by omega), getElem?_of_lt (by omega)]
        simp [htrans.assert, hsp])]
  simp only [Collect.app_app, orderAsserts, strictAsserts, flatMap_singleton_eq, one_mul,
    length_slice L6, length_slice L8]
  simp [hsp, RamBoundary.is_segment]

theorem push_asserts (m : RowWindow F) (first last trans : F) (s : Collect F) (bus : String)
    (d : BusDirection) (fields : List F) (act : BusActivation F) :
    ∃ l, ((rowBuilder m first last trans).push_bus_interaction s bus d fields act).asserts =
      s.asserts ++ l := by
  unfold BusBuilder.push_bus_interaction
  cases act <;> simp [rowBuilder, Collect.app]

theorem declare_asserts {st : RamStatement} (m : RowWindow F) (first last trans : F)
    {s s' : Collect F} (h : (RamAir.mk st (stdLayout st)).declare (rowBuilder m first last trans) s = some s') :
    ∃ l, s'.asserts = s.asserts ++ l := by
  unfold RamAir.declare at h
  cases hb : st.boundary with
  | SingleProof =>
    simp only [hb, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨access, -, bus, -, rfl⟩ := h
    exact push_asserts m first last trans s bus .Pull access .Always
  | Segment inc out =>
    simp only [hb, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨access, -, bus, -, image, -, opening, -, inc', -, closing, -, out', -, rfl⟩ := h
    obtain ⟨l, hl⟩ := push_asserts m first last trans s bus .Pull access .Always
    obtain ⟨l₁, hl₁⟩ := push_asserts m first last trans
      ((rowBuilder m first last trans).push_bus_interaction s bus .Pull access .Always) inc' .Pull
      image (.Boolean ((rowBuilder m first last trans).sub ((rowBuilder m first last trans).const 1)
        opening))
    obtain ⟨l₂, hl₂⟩ := push_asserts m first last trans _ out' .Push image (.Boolean closing)
    exact ⟨l ++ l₁ ++ l₂, by rw [hl₂, hl₁, hl]; simp⟩

/-- **The constraints of a self-contained proof on one row.**

Suppose the row's evaluation succeeds with every asserted value zero.

Then the booleanity and order groups vanish. -/
theorem row_holds {st : RamStatement} (hsp : st.boundary = .SingleProof) (hv : st.validate = .ok ())
    {cur nxt : List F} (hc : cur.length = (stdLayout st).width)
    (hn : nxt.length = (stdLayout st).width) {first last trans : F} {s : Collect F}
    (h : (RamAir.mk st (stdLayout st)).eval (rowBuilder ⟨cur, nxt⟩ first last trans) ⟨[], []⟩ = some s)
    (hs : s.Holds) :
    (∀ x ∈ boolAsserts (stdLayout st) cur, x = 0) ∧
      (∀ x ∈ orderAsserts (stdLayout st) first trans cur nxt, x = 0) := by
  unfold RamAir.eval at h
  rw [booleanity_eq (st := st) (isCollect_row ⟨cur, nxt⟩ first last trans) _ (cur := cur) rfl hc,
    obind_some,
    order_eq hsp hv first last trans _ hc hn, obind_some] at h
  unfold RamAir.eval_run_marker at h
  simp only [hsp, RamBoundary.is_segment, Bool.not_false, ite_true] at h
  obtain ⟨l, hl⟩ := declare_asserts _ first last trans h
  have hall : ∀ x ∈ s.asserts, x = 0 := hs
  rw [hl] at hall
  simp only [Collect.app, List.nil_append, one_mul, List.map_id', List.mem_append] at hall
  exact ⟨fun x hx => hall x (Or.inl (Or.inl (by simpa using hx))),
    fun x hx => hall x (Or.inl (Or.inr hx))⟩

end Plonky3Lean.Proofs.Bus
