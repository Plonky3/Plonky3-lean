module

public import Plonky3Lean.Proofs.MultilinearUtil.Tab

@[expose] public section

/-!
# Batched equality tables: the packed path

The last log_2 W variables fill the lanes: lane l of the packed seed of point i is s_i eq(l, z_i).

The leading variables pick a thread, and the middle ones a block of W outputs.
-/

namespace Plonky3Lean.Proofs.MultilinearUtil

open Plonky3Lean.Spec.MultilinearUtil p3_multilinear_util.mirror p3_multilinear_util.eq_batch.mirror
open Finset

/-! ## The packed seeds -/

/-- packed_eq_poly_batch: lane l of point i is s_i eq(l, z_i). -/
theorem packed_eq_poly_batch_eq {K : Type _} [Field K] {W m : ℕ} (rows : List (List K))
    (s : List K) (hW : W = 2 ^ rows.length) (hs : s.length = m) (hrows : ∀ r ∈ rows, m ≤ r.length) :
    packed_eq_poly_batch W m rows s =
      some ((List.range m).map fun i (l : Fin W) => (tab rows s l).getD i 0) := by
  subst hW
  simp only [packed_eq_poly_batch, ne_eq, not_true_eq_false, ↓reduceIte,
    fill_buffer_batch_eq rows s hs hrows, Option.bind_eq_bind, Option.bind_some]
  refine mapM_some _ _ _ fun i _ => ?_
  simp only [from_ext_slice, List.length_map, List.length_range, ↓reduceIte, Option.some.injEq]
  funext l
  rw [getD_map_range _ _ l.isLt, getD_map_range _ _ l.isLt]

/-! ## The packed recursion -/

section Packed

variable {IF EF P : Type _} [Field IF] [Field EF] [Algebra IF EF] [CommRing P] [Algebra IF P]

/-- Block y of W consecutive outputs. -/
def chunkAt {α : Type _} (W : ℕ) (out : List α) (y : ℕ) : List α := (out.drop (y * W)).take W

theorem length_splitPacked {r : List IF} {v : List P} (h : v.length ≤ r.length) :
    (splitPacked r v).1.length = v.length ∧ (splitPacked r v).2.length = v.length := by
  simp [splitPacked]; omega

theorem tab_single (r : List IF) (s : List P) (h : s.length ≤ r.length) :
    tab [r] s 0 = (splitPacked r s).1 ∧ tab [r] s 1 = (splitPacked r s).2 := by
  constructor
  · simpa using tab_cons r [] s h (x := 0) (by norm_num)
  · simpa using tab_cons r [] s h (x := 1) (by norm_num)

theorem flatMap_range_add {α : Type _} (a b : ℕ) (f : ℕ → List α) :
    (List.range (a + b)).flatMap f = (List.range a).flatMap f ++ (List.range b).flatMap (f <| a + ·) := by
  simp [List.range_add, List.flatMap_append, List.flatMap_map]

theorem chunkAt_take {α : Type _} {W k : ℕ} (out : List α) {y : ℕ} (hy : y < k) :
    chunkAt W (out.take (k * W)) y = chunkAt W out y := by
  simp only [chunkAt, List.drop_take, List.take_take]
  congr 1
  have : W ≤ k * W - y * W := by
    rw [← Nat.sub_mul]; exact Nat.le_mul_of_pos_left _ (by omega)
  omega

theorem chunkAt_drop {α : Type _} (W k : ℕ) (out : List α) (y : ℕ) :
    chunkAt W (out.drop (k * W)) y = chunkAt W out (k + y) := by
  simp [chunkAt, List.drop_drop, Nat.add_mul]

omit [Field EF] [Algebra IF EF] in
/-- The packed recursion: block y of the output accumulates the packed tables at y. -/
theorem eval_eq_packed_batch_eq (E : Evaluator IF EF P) (W : ℕ) (initialized : Bool) (m : ℕ)
    (scalars : List EF) (acc : List EF → List P → List EF)
    (hacc : ∀ o l, o.length = W → l.length = m →
      E.accumulate_packed_batch initialized o l scalars = some (acc o l)) :
    ∀ (rows : List (List IF)) (out : List EF) (e : List P) (ws : ℕ), (∀ r ∈ rows, m ≤ r.length) →
    e.length = m → out.length = W * 2 ^ rows.length → 2 * m * (rows.length + 1) ≤ ws →
    eval_eq_packed_batch E W initialized m rows out e scalars ws =
      some ((List.range (2 ^ rows.length)).flatMap fun y => acc (chunkAt W out y) (tab rows e y))
  | [], out, e, ws, _, he, hout, _ => by
    simp only [List.length_nil, pow_zero, mul_one] at hout
    simp [eval_eq_packed_batch, hout, hacc out e hout he, chunkAt,
      List.take_of_length_le (le_of_eq hout)]
  | [r0], out, e, ws, hr, he, hout, hws => by
    have h0 := hr r0 (by simp)
    obtain ⟨l0, l1⟩ := length_splitPacked (r := r0) (v := e) (by omega)
    obtain ⟨t0, t1⟩ := tab_single r0 e (by omega)
    simp only [List.length_cons, List.length_nil, Nat.zero_add, pow_one] at hout hws
    have hc : ¬ (out.length ≠ W * 2 ^ [r0].length) := by simp [hout]
    simp only [eval_eq_packed_batch, hc, ↓reduceIte, show ¬ ws < 2 * m by omega]
    rw [show out.length / 2 = W by omega, hacc _ _ (by simp; omega) (by omega),
      hacc _ _ (by simp; omega) (by omega)]
    simp only [List.length_cons, List.length_nil, Nat.zero_add, pow_one, Option.bind_eq_bind,
      Option.bind_some, Option.pure_def, Option.some.injEq]
    rw [show (2 : ℕ) = 1 + 1 from rfl, flatMap_range_add]
    simp [chunkAt, t0, t1, List.take_of_length_le (show (out.drop W).length ≤ W by simp; omega)]
  | [r0, r1], out, e, ws, hr, he, hout, hws => by
    have h0 := hr r0 (by simp)
    have h1 := hr r1 (by simp)
    obtain ⟨l0, l1⟩ := length_splitPacked (r := r0) (v := e) (by omega)
    obtain ⟨l00, l01⟩ := length_splitPacked (r := r1) (v := (splitPacked r0 e).1) (by omega)
    obtain ⟨l10, l11⟩ := length_splitPacked (r := r1) (v := (splitPacked r0 e).2) (by omega)
    obtain ⟨t00, t01⟩ := tab_single r1 (splitPacked r0 e).1 (by omega)
    obtain ⟨t10, t11⟩ := tab_single r1 (splitPacked r0 e).2 (by omega)
    have tc := fun y (hy : y < 4) => tab_cons r0 [r1] e (by omega) (x := y) (by simpa using hy)
    simp only [List.length_cons, List.length_nil] at hout hws
    have hc : ¬ (out.length ≠ W * 2 ^ [r0, r1].length) := by simp [hout]
    simp only [eval_eq_packed_batch, hc, ↓reduceIte, show ¬ ws < 4 * m by omega]
    rw [show out.length / 4 = W by omega, hacc _ _ (by simp; omega) (by omega),
      hacc _ _ (by simp; omega) (by omega), hacc _ _ (by simp; omega) (by omega),
      hacc _ _ (by simp; omega) (by omega)]
    simp only [Option.bind_eq_bind, Option.bind_some, Option.pure_def, Option.some.injEq,
      List.length_cons, List.length_nil]
    rw [show 2 ^ (0 + 1 + 1) = 4 from rfl, show List.range 4 = [0, 1, 2, 3] from rfl]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.append_assoc, chunkAt,
      tc 0 (by norm_num), tc 1 (by norm_num), tc 2 (by norm_num), tc 3 (by norm_num)]
    simp [t00, t01, t10, t11, List.take_of_length_le (show (out.drop (3 * W)).length ≤ W by
      simp; omega), Nat.two_mul]
  | [r0, r1, r2], out, e, ws, hr, he, hout, hws => by
    have h0 := hr r0 (by simp)
    have h1 := hr r1 (by simp)
    have h2 := hr r2 (by simp)
    obtain ⟨l0, l1⟩ := length_splitPacked (r := r0) (v := e) (by omega)
    obtain ⟨l00, l01⟩ := length_splitPacked (r := r1) (v := (splitPacked r0 e).1) (by omega)
    obtain ⟨l10, l11⟩ := length_splitPacked (r := r1) (v := (splitPacked r0 e).2) (by omega)
    have tc := fun y (hy : y < 8) => tab_cons r0 [r1, r2] e (by omega) (x := y) (by simpa using hy)
    have tc0 := fun y (hy : y < 4) => tab_cons r1 [r2] (splitPacked r0 e).1 (by omega) (x := y)
      (by simpa using hy)
    have tc1 := fun y (hy : y < 4) => tab_cons r1 [r2] (splitPacked r0 e).2 (by omega) (x := y)
      (by simpa using hy)
    obtain ⟨u0, u1⟩ := tab_single r2 (splitPacked r1 (splitPacked r0 e).1).1 (by omega)
    obtain ⟨u2, u3⟩ := tab_single r2 (splitPacked r1 (splitPacked r0 e).1).2 (by omega)
    obtain ⟨u4, u5⟩ := tab_single r2 (splitPacked r1 (splitPacked r0 e).2).1 (by omega)
    obtain ⟨u6, u7⟩ := tab_single r2 (splitPacked r1 (splitPacked r0 e).2).2 (by omega)
    simp only [List.length_cons, List.length_nil] at hout hws
    have hc : ¬ (out.length ≠ W * 2 ^ [r0, r1, r2].length) := by simp [hout]
    simp only [eval_eq_packed_batch, hc, ↓reduceIte, show ¬ ws < 8 * m by omega]
    rw [show out.length / 8 = W by omega]
    have key : ∀ k < 8, ([splitPacked r2 (splitPacked r1 (splitPacked r0 e).1).1,
        splitPacked r2 (splitPacked r1 (splitPacked r0 e).1).2,
        splitPacked r2 (splitPacked r1 (splitPacked r0 e).2).1,
        splitPacked r2 (splitPacked r1 (splitPacked r0 e).2).2].flatMap
          fun pr => [pr.1, pr.2]).getD k [] = tab [r0, r1, r2] e k := by
      intro k hk
      rw [tc k hk]
      obtain rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨
          k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 := by omega
      all_goals simp [tc0, tc1, u0, u1, u2, u3, u4, u5, u6, u7]
    simp only [Nat.zero_add] at hout
    rw [mapM_some _ _ (fun j => acc (chunkAt W out j) (tab [r0, r1, r2] e j)) fun j hj => by
      simp only [List.mem_range] at hj
      rw [key j hj, hacc _ _ ?_ (by simp [he])]
      · split_ifs with h7
        · subst h7
          simp [chunkAt, List.take_of_length_le (show (out.drop (7 * W)).length ≤ W by
            simp [hout]; omega)]
        · rfl
      · have := Nat.mul_le_mul_right W (show j ≤ 7 by omega)
        split_ifs <;> simp [hout] <;> omega]
    simp only [Option.bind_eq_bind, Option.bind_some, Option.pure_def, Option.some.injEq,
      List.length_cons, List.length_nil, ← List.flatMap_def]
    rfl
  | r0 :: r1 :: r2 :: r3 :: rest, out, e, ws, hr, he, hout, hws => by
    have h0 := hr r0 (by simp)
    obtain ⟨l0, l1⟩ := length_splitPacked (r := r0) (v := e) (by omega)
    have hr' : ∀ r ∈ r1 :: r2 :: r3 :: rest, m ≤ r.length := fun r h => hr r (List.mem_cons_of_mem _ h)
    have hRl : (r1 :: r2 :: r3 :: rest).length = rest.length + 3 := by simp
    have hn : (r0 :: r1 :: r2 :: r3 :: rest).length = rest.length + 3 + 1 := by simp
    rw [hn] at hout hws
    have hp : 2 ^ (rest.length + 3 + 1) = 2 ^ (rest.length + 3) + 2 ^ (rest.length + 3) := by
      rw [pow_succ]; omega
    rw [hp] at hout
    have hX : ∀ y, y * W ≤ (y + y) * W := fun y => by nlinarith
    have hc : ¬ (out.length ≠ W * 2 ^ (r0 :: r1 :: r2 :: r3 :: rest).length) := by
      rw [hn, hp]; simp [hout]
    have hws2 : 2 * m * ((r1 :: r2 :: r3 :: rest).length + 1) ≤ ws - 2 * m := by
      rw [hRl]
      have : 2 * m * (rest.length + 3 + 1 + 1) = 2 * m * (rest.length + 3 + 1) + 2 * m := by ring
      omega
    generalize hXd : 2 ^ (rest.length + 3) = X at hout hp
    have hhalf : out.length / 2 = X * W := by rw [hout, Nat.mul_add, Nat.mul_comm W X]; omega
    simp only [eval_eq_packed_batch, hc, ↓reduceIte, show ¬ ws < 2 * m by
      have : 2 * m * (rest.length + 3 + 1 + 1) = 2 * m * (rest.length + 3 + 1) + 2 * m := by ring
      omega]
    rw [hhalf, eval_eq_packed_batch_eq E W initialized m scalars acc hacc _ _ _ _ hr' (l0.trans he)
        (by rw [List.length_take, hout, hRl, hXd, Nat.mul_add, Nat.mul_comm X W]; omega) hws2,
      eval_eq_packed_batch_eq E W initialized m scalars acc hacc _ _ _ _ hr' (l1.trans he)
        (by rw [List.length_drop, hout, hRl, hXd, Nat.mul_add, Nat.mul_comm X W]; omega) hws2]
    simp only [Option.bind_eq_bind, Option.bind_some, Option.pure_def, Option.some.injEq]
    rw [hn, hp, hRl, hXd, flatMap_range_add]
    congr 1
    · refine List.flatMap_congr fun y hy => ?_
      simp only [List.mem_range] at hy
      rw [chunkAt_take _ hy, tab_cons r0 _ e (by omega) (by rw [pow_succ, hRl, hXd]; omega), hRl, hXd]
      simp only [hy, ↓reduceIte]
    · refine List.flatMap_congr fun y hy => ?_
      simp only [List.mem_range] at hy
      rw [chunkAt_drop, tab_cons r0 _ e (by omega) (by rw [pow_succ, hRl, hXd]; omega), hRl, hXd]
      simp

end Packed

/-! ## The two accumulations -/

section Accumulate

variable {F EF : Type _} [Field F] [Field EF] [Algebra F EF]

/-- The extension accumulation writes or adds the lanes of the sum of the packed tables. -/
theorem ext_accumulate_eq (W m : ℕ) (initialized : Bool) (o : List EF) (l : List (Fin W → EF))
    (scalars : List EF) (ho : o.length = W) :
    (extEvaluator W m).accumulate_packed_batch initialized o l scalars =
      some (addOrSet initialized o (List.ofFn l.sum)) := by
  cases l with
  | nil =>
    cases initialized
    · simp only [extEvaluator, List.isEmpty_nil, ↓reduceIte, Bool.false_eq_true, addOrSet,
        List.sum_nil, Option.some.injEq]
      exact List.ext_getElem (by simp [ho]) fun i _ _ => by simp
    · simp only [extEvaluator, List.isEmpty_nil, ↓reduceIte, addOrSet, List.sum_nil,
        Option.some.injEq]
      exact List.ext_getElem (by simp [ho]) fun i _ _ => by simp
  | cons a l =>
    cases initialized <;>
      simp [extEvaluator, addOrSet, ho, List.take_of_length_le, List.drop_eq_nil_of_le]

/-- The base accumulation: lane k gets sum_i scalars_i table_i[k]. -/
theorem base_accumulate_eq (W m : ℕ) (initialized : Bool) (o : List EF) (l : List (Fin W → F))
    (scalars : List EF) (ho : o.length = W) (hl : l.length = scalars.length) :
    (baseEvaluator (EF := EF) W m).accumulate_packed_batch initialized o l scalars =
      some (addOrSet initialized o ((List.range W).map fun k =>
        (List.zipWith (fun s (v : Fin W → F) =>
          s * algebraMap F EF (if h : k < W then v ⟨k, h⟩ else 0)) scalars l).sum)) := by
  rcases scalars with _ | ⟨s0, scalars⟩
  · obtain rfl : l = [] := List.eq_nil_of_length_eq_zero hl
    cases initialized
    · simp only [baseEvaluator, ho, hl, ne_eq, not_true_eq_false, or_self, ↓reduceIte,
        List.isEmpty_nil, Bool.false_eq_true, addOrSet, List.zipWith_nil_left, List.sum_nil,
        Option.some.injEq]
      exact List.ext_getElem (by simp [ho]) fun i _ _ => by simp
    · simp only [baseEvaluator, ho, hl, ne_eq, not_true_eq_false, or_self, ↓reduceIte,
        List.isEmpty_nil, addOrSet, List.zipWith_nil_left, List.sum_nil, Option.some.injEq]
      exact List.ext_getElem (by simp [ho]) fun i _ _ => by simp
  · cases initialized
    · simp only [baseEvaluator, ho, hl, ne_eq, not_true_eq_false, or_self, ↓reduceIte,
        List.isEmpty_cons, Bool.false_eq_true, addOrSet]
    · simp only [baseEvaluator, ho, hl, ne_eq, not_true_eq_false, or_self, ↓reduceIte,
        List.isEmpty_cons, Bool.false_eq_true, addOrSet, Option.some.injEq]
      exact List.ext_getElem (by simp [ho]) fun i h1 h2 => by
        simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show i < o.length by
          simp at h1; omega)]

end Accumulate

/-! ## Reindexing the output -/

theorem map_range_mul {α : Type _} (a b : ℕ) (f : ℕ → α) :
    (List.range (a * b)).map f = (List.range a).flatMap fun t => (List.range b).map fun z => f (t * b + z) := by
  induction a with
  | zero => simp
  | succ a ih =>
    rw [Nat.succ_mul, List.range_add, List.map_append, ih, List.range_succ, List.flatMap_append]
    simp [List.map_map, Function.comp_def]

theorem chunkAt_chunkAt {α : Type _} (c d : ℕ) (out : List α) (t : ℕ) {y : ℕ} (hy : y < d) :
    chunkAt c (chunkAt (d * c) out t) y = chunkAt c out (t * d + y) := by
  simp only [chunkAt, List.drop_take, List.take_take, List.drop_drop]
  have : c ≤ d * c - y * c := by rw [← Nat.sub_mul]; exact Nat.le_mul_of_pos_left _ (by omega)
  rw [show t * (d * c) + y * c = (t * d + y) * c by ring]
  congr 1; omega

theorem chunks_eq {α : Type _} {c k : ℕ} (hc : 0 < c) {out : List α} (h : out.length = k * c) :
    chunks c out = (List.range k).map (chunkAt c out) := by
  have hl := length_chunks hc h
  simp only [chunks, List.length_map, List.length_range] at hl ⊢
  rw [hl]; rfl

theorem length_chunkAt {α : Type _} {c k : ℕ} {out : List α} (h : out.length = k * c) {t : ℕ}
    (ht : t < k) : (chunkAt c out t).length = c := by
  have : (t + 1) * c ≤ k * c := Nat.mul_le_mul_right c ht
  simp only [chunkAt, List.length_take, List.length_drop, h]
  rw [Nat.succ_mul] at this; omega

section AddOrSet

variable {EF : Type _} [Field EF]

theorem addOrSet_flatMap (initialized : Bool) {c : ℕ} (Tf : ℕ → List EF)
    (hT : ∀ j, (Tf j).length = c) : ∀ (k : ℕ) (out : List EF), out.length = k * c →
    addOrSet initialized out ((List.range k).flatMap Tf) =
      (List.range k).flatMap fun j => addOrSet initialized (chunkAt c out j) (Tf j)
  | 0, out, h => by
    obtain rfl : out = [] := List.eq_nil_of_length_eq_zero (by simpa using h)
    cases initialized <;> simp [addOrSet]
  | k + 1, out, h => by
    have hk : (out.take (k * c)).length = k * c := by
      simp only [List.length_take, h]; exact min_eq_left (Nat.mul_le_mul_right c (by omega))
    have hlast : (out.drop (k * c)).length = c := by simp [h, Nat.succ_mul]
    conv_lhs => rw [← List.take_append_drop (k * c) out]
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton,
      ← addOrSet_append _ (by rw [hk]; simp [List.length_flatMap, hT]),
      addOrSet_flatMap initialized Tf hT k _ hk, List.flatMap_append, List.flatMap_singleton]
    congr 1
    · exact List.flatMap_congr fun j hj => by
        simp only [List.mem_range] at hj
        rw [chunkAt_take _ hj]
    · simp [chunkAt, List.take_of_length_le (le_of_eq hlast)]

end AddOrSet

theorem getD_map_ringHom {K L : Type _} [CommRing K] [CommRing L] (φ : K →+* L) (l : List K)
    (x : ℕ) : (l.map φ).getD x 0 = φ (l.getD x 0) := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases l[x]? <;> simp

/-- The batched table is the sum of the weighted table, entry by entry. -/
theorem bt_eq_map_tab {IF EF : Type _} [Field IF] [Field EF] [Algebra IF EF]
    (rows : List (List IF)) (g : List EF) (hg : ∀ r ∈ rows, g.length ≤ r.length) :
    bt rows g = (List.range (2 ^ rows.length)).map fun e => (tab rows g e).sum := by
  refine ext_getD 0 (by simp) fun e he => ?_
  rw [getD_bt rows g hg, getD_map_range _ _ (by simpa using he), sum_eq_sum_getD]
  simp only [length_tab]
  refine sum_congr rfl fun i _ => ?_
  rw [tab, getD_scaleFn, eqTable_map, getD_map_ringHom]

end Plonky3Lean.Proofs.MultilinearUtil
