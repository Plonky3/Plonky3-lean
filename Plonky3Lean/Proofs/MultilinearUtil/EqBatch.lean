module

public import Plonky3Lean.Proofs.MultilinearUtil.Point
public import P3MultilinearUtil.Mirror.EqBatch

@[expose] public section

/-!
# Batched equality tables: the recursive path

The batched table of points z_i with weights g_i is W(x) = sum_i g_i eq(x, z_i).

Fixing the first variable splits each weight into g_i (1 - z_i) and g_i z_i, one per half of the table.
-/

namespace Plonky3Lean.Proofs.MultilinearUtil

open Plonky3Lean.Spec.MultilinearUtil p3_multilinear_util.mirror p3_multilinear_util.eq_batch.mirror
open Finset

variable {IF EF : Type _} [Field IF] [Field EF] [Algebra IF EF]

/-- Point i: coordinate i of every row. -/
def col (rows : List (List IF)) (i : ℕ) : List IF := rows.map (·.getD i 0)

/-- The batched table, built by splitting the weights on the first variable. -/
def bt : List (List IF) → List EF → List EF
  | [], g => [g.sum]
  | r :: rows, g => bt rows (splitScalars r g).1 ++ bt rows (splitScalars r g).2

@[simp] theorem length_bt (rows : List (List IF)) (g : List EF) :
    (bt rows g).length = 2 ^ rows.length := by
  induction rows generalizing g with
  | nil => simp [bt]
  | cons r rows ih => simp [bt, ih, pow_succ, mul_two]

theorem length_splitScalars {r : List IF} {g : List EF} (h : g.length ≤ r.length) :
    (splitScalars r g).1.length = g.length ∧ (splitScalars r g).2.length = g.length := by
  simp [splitScalars]; omega

theorem getD_splitScalars {r : List IF} {g : List EF} (h : g.length ≤ r.length) (i : ℕ) :
    (splitScalars r g).1.getD i 0 = g.getD i 0 * (1 - algebraMap IF EF (r.getD i 0)) ∧
    (splitScalars r g).2.getD i 0 = g.getD i 0 * algebraMap IF EF (r.getD i 0) := by
  simp only [splitScalars, List.getD_eq_getElem?_getD, List.getElem?_zipWith]
  by_cases hi : i < g.length
  · simp [List.getElem?_eq_getElem hi, List.getElem?_eq_getElem (show i < r.length by omega)]
    ring
  · simp [List.getElem?_eq_none (show g.length ≤ i by omega)]

theorem eqTable_map {K L : Type _} [CommRing K] [CommRing L] (φ : K →+* L) (r : List K) :
    eqTable (r.map φ) = (eqTable r).map φ := by
  induction r with
  | nil => simp
  | cons c r ih => simp [eqTable_cons, ih, Function.comp_def]

theorem sum_eq_sum_getD {K : Type _} [AddCommMonoid K] (g : List K) :
    g.sum = ∑ i ∈ range g.length, g.getD i 0 := by
  induction g with
  | nil => simp
  | cons a g ih => simp [sum_range_succ', ih, add_comm]

theorem getD_append_lt {K : Type _} (l l' : List K) (d : K) {x : ℕ} (h : x < l.length) :
    (l ++ l').getD x d = l.getD x d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_append_ge {K : Type _} (l l' : List K) (d : K) {x : ℕ} (h : l.length ≤ x) :
    (l ++ l').getD x d = l'.getD (x - l.length) d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_right h]

/-- The batched table, entry by entry: sum_i g_i eq(x, z_i). -/
theorem getD_bt (rows : List (List IF)) (g : List EF) (hg : ∀ r ∈ rows, g.length ≤ r.length)
    (x : ℕ) : (bt rows g).getD x 0 = ∑ i ∈ range g.length,
      g.getD i 0 * (eqTable ((col rows i).map (algebraMap IF EF))).getD x 0 := by
  induction rows generalizing g x with
  | nil =>
    rcases Nat.eq_zero_or_pos x with rfl | hx
    · simp [bt, col, sum_eq_sum_getD]
    · simp [bt, col, List.getD_eq_getElem?_getD, List.getElem?_eq_none (show [g.sum].length ≤ x by
        simp; omega), List.getElem?_eq_none (show [(1 : EF)].length ≤ x by simp; omega)]
  | cons r rows ih =>
    have hr := hg r (by simp)
    obtain ⟨h1, h2⟩ := length_splitScalars hr
    have hg' : ∀ g' : List EF, g'.length = g.length → ∀ r ∈ rows, g'.length ≤ r.length :=
      fun g' hg' r' hr' => hg' ▸ hg r' (by simp [hr'])
    have hcol : ∀ i, (col (r :: rows) i).map (algebraMap IF EF) =
        algebraMap IF EF (r.getD i 0) :: (col rows i).map (algebraMap IF EF) := fun i => by
      simp [col]
    have hT : ∀ i, (eqTable ((col rows i).map (algebraMap IF EF))).length = 2 ^ rows.length :=
      fun i => by simp [col]
    simp only [bt, hcol, eqTable_cons]
    by_cases hx : x < 2 ^ rows.length
    · rw [getD_append_lt _ _ _ (by simpa using hx), ih _ (hg' _ h1), h1]
      refine sum_congr rfl fun i _ => ?_
      rw [getD_append_lt _ _ _ (by simpa [hT] using hx), (getD_splitScalars hr i).1,
        getD_map_mul_right]
      ring
    · rw [getD_append_ge _ _ _ (by simpa using hx), ih _ (hg' _ h2), h2, length_bt]
      refine sum_congr rfl fun i _ => ?_
      rw [getD_append_ge _ _ _ (by simp [hT]; omega), (getD_splitScalars hr i).2,
        getD_map_mul_right]
      simp only [List.length_map, hT]
      ring

/-! ## The unrolled cases and the recursion -/

theorem sum_zipWith_sub {K : Type _} [AddCommGroup K] {a b : List K} (h : a.length = b.length) :
    (List.zipWith (· - ·) a b).sum = a.sum - b.sum := by
  induction a generalizing b with
  | nil => simp [List.eq_nil_of_length_eq_zero h.symm]
  | cons x a ih =>
    obtain ⟨y, b, rfl⟩ := List.exists_cons_of_length_eq_add_one h.symm
    simp [ih (by simpa using h)]; abel

theorem eval_eq_1_batch_eq (r : List IF) (g : List EF) (h : g.length ≤ r.length) :
    [(eval_eq_1_batch r g).1, (eval_eq_1_batch r g).2] = bt [r] g := by
  simp only [eval_eq_1_batch, bt, splitScalars, List.singleton_append, List.cons.injEq, and_true]
  rw [sum_zipWith_sub (by simp; omega)]

theorem eval_eq_2_batch_eq (r0 r1 : List IF) (g : List EF) {m ws : ℕ} (hws : 2 * m ≤ ws)
    (h0 : g.length ≤ r0.length) (h1 : g.length ≤ r1.length) :
    eval_eq_2_batch [r0, r1] g m ws = some (bt [r0, r1] g) := by
  obtain ⟨l0, l1⟩ := length_splitScalars h0
  simp only [eval_eq_2_batch, show ¬ ws < 2 * m by omega, ↓reduceIte, List.getD_cons_zero,
    List.getD_cons_succ, Option.some.injEq]
  rw [bt, ← eval_eq_1_batch_eq _ _ (by omega), ← eval_eq_1_batch_eq _ _ (by omega)]
  rfl

theorem eval_eq_3_batch_eq (r0 r1 r2 : List IF) (g : List EF) {m ws : ℕ} (hws : 6 * m ≤ ws)
    (h0 : g.length ≤ r0.length) (h1 : g.length ≤ r1.length) (h2 : g.length ≤ r2.length) :
    eval_eq_3_batch [r0, r1, r2] g m ws = some (bt [r0, r1, r2] g) := by
  obtain ⟨l0, l1⟩ := length_splitScalars h0
  simp only [eval_eq_3_batch, show ¬ ws < 2 * m by omega, show ¬ ws - 2 * m < 2 * m by omega,
    show ¬ ws - 2 * m - 2 * m < 2 * m by omega, ↓reduceIte, List.getD_cons_zero, List.tail_cons]
  rw [eval_eq_2_batch_eq _ _ _ le_rfl (by omega) (by omega),
    eval_eq_2_batch_eq _ _ _ le_rfl (by omega) (by omega)]
  rfl

/-- The result of a batched fill: the table, added to the output or written over it. -/
def addOrSet (initialized : Bool) (out t : List EF) : List EF :=
  if initialized then List.zipWith (· + ·) out t else t

theorem add_or_set_eq (initialized : Bool) {out t : List EF} (h : out.length = t.length) :
    add_or_set initialized out t = some (addOrSet initialized out t) := by
  cases initialized <;> simp [add_or_set, addOrSet, h]

theorem addOrSet_append (initialized : Bool) {o1 o2 t1 t2 : List EF} (h : o1.length = t1.length) :
    addOrSet initialized o1 t1 ++ addOrSet initialized o2 t2 =
      addOrSet initialized (o1 ++ o2) (t1 ++ t2) := by
  cases initialized <;> simp [addOrSet, List.zipWith_append h]

/-- The recursive path is the batched table, for every workspace of at least 2 m n entries. -/
theorem eval_eq_batch_basic_eq (initialized : Bool) (m : ℕ) : ∀ (rows : List (List IF))
    (g out : List EF) (ws : ℕ), (∀ r ∈ rows, g.length ≤ r.length) → g.length = m →
    out.length = 2 ^ rows.length → 2 * m * rows.length ≤ ws →
    eval_eq_batch_basic initialized m rows g out ws = some (addOrSet initialized out (bt rows g))
  | [], g, out, ws, _, _, hout, _ => by
    obtain ⟨o, rfl⟩ : ∃ o, out = [o] := List.length_eq_one_iff.mp (by simpa using hout)
    cases initialized <;> simp [eval_eq_batch_basic, addOrSet, bt]
  | [r0], g, out, ws, hr, _, hout, _ => by
    simp only [eval_eq_batch_basic, hout, ne_eq, not_true_eq_false, ↓reduceIte]
    rw [add_or_set_eq _ (by simpa using hout), ← eval_eq_1_batch_eq r0 g (hr r0 (by simp))]
  | [r0, r1], g, out, ws, hr, hm, hout, hws => by
    simp only [eval_eq_batch_basic, hout, ne_eq, not_true_eq_false, ↓reduceIte]
    rw [eval_eq_2_batch_eq _ _ _ (by simp at hws; omega) (hr _ (by simp)) (hr _ (by simp)),
      Option.bind_eq_bind, Option.bind_some, add_or_set_eq _ (by simpa using hout)]
  | [r0, r1, r2], g, out, ws, hr, hm, hout, hws => by
    simp only [eval_eq_batch_basic, hout, ne_eq, not_true_eq_false, ↓reduceIte]
    rw [eval_eq_3_batch_eq _ _ _ _ (by simp at hws; omega) (hr _ (by simp)) (hr _ (by simp))
      (hr _ (by simp)), Option.bind_eq_bind, Option.bind_some, add_or_set_eq _ (by simpa using hout)]
  | r0 :: r1 :: r2 :: r3 :: rest, g, out, ws, hr, hm, hout, hws => by
    have hr0 := hr r0 (by simp)
    obtain ⟨l0, l1⟩ := length_splitScalars hr0
    have hr' : ∀ g' : List EF, g'.length = g.length → ∀ r ∈ r1 :: r2 :: r3 :: rest,
        g'.length ≤ r.length := fun g' hg' r hr'' => hg' ▸ hr r (List.mem_cons_of_mem _ hr'')
    have hlen : out.length = 2 * 2 ^ (rest.length + 3) := by
      rw [hout]; simp only [List.length_cons]
      rw [show rest.length + 1 + 1 + 1 + 1 = rest.length + 3 + 1 by omega, pow_succ]; ring
    have h3 : (r1 :: r2 :: r3 :: rest).length = rest.length + 3 := by simp
    have hhalf : (out.take (out.length / 2)).length = 2 ^ (r1 :: r2 :: r3 :: rest).length := by
      rw [List.length_take, h3, hlen]; omega
    have hhalf' : (out.drop (out.length / 2)).length = 2 ^ (r1 :: r2 :: r3 :: rest).length := by
      rw [List.length_drop, h3, hlen]; omega
    have e1 : 2 * m * (rest.length + 4) = 2 * m * rest.length + 8 * m := by ring
    have e2 : 2 * m * (rest.length + 3) = 2 * m * rest.length + 6 * m := by ring
    simp only [List.length_cons, show rest.length + 1 + 1 + 1 + 1 = rest.length + 4 by omega] at hws
    have hws' : 2 * m * (r1 :: r2 :: r3 :: rest).length ≤ ws - 2 * m := by rw [h3]; omega
    have hc : ¬ (out.length ≠ 2 ^ (r0 :: r1 :: r2 :: r3 :: rest).length) := not_not.mpr hout
    simp only [eval_eq_batch_basic, hc, ↓reduceIte, show ¬ ws < 2 * m by omega]
    rw [eval_eq_batch_basic_eq initialized m _ _ _ _ (hr' _ l0) (l0.trans hm) hhalf hws',
      eval_eq_batch_basic_eq initialized m _ _ _ _ (hr' _ l1) (l1.trans hm) hhalf' hws']
    simp only [Option.bind_eq_bind, Option.bind_some, Option.pure_def, Option.some.injEq]
    rw [addOrSet_append _ (by rw [hhalf, length_bt]), List.take_append_drop]
    rfl

end Plonky3Lean.Proofs.MultilinearUtil
