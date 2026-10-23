module

public import Plonky3Lean.Proofs.MultilinearUtil.EqBatch

@[expose] public section

/-!
# Weighted tables of many points

Entry x of the weighted table of points z_i with weights s_i is the vector of the s_i eq(x, z_i).

Splitting the variables of the points composes the tables: the table of A ++ B at (a, b) is the table of B, at b, weighted by the table of A at a.
-/

namespace Plonky3Lean.Proofs.MultilinearUtil

open Plonky3Lean.Spec.MultilinearUtil p3_multilinear_util.mirror p3_multilinear_util.eq_batch.mirror
open Finset

variable {IF : Type _} [Field IF]

/-- Entry a b' + b of a flattened list of pieces of length k is entry b of piece a. -/
theorem getD_flatMap_const {α β : Type _} (L : List α) (f : α → List β) {k : ℕ}
    (hk : ∀ a ∈ L, (f a).length = k) (d : β) {a b : ℕ} (ha : a < L.length) (hb : b < k) :
    (L.flatMap f).getD (a * k + b) d = (f L[a]).getD b d := by
  induction L generalizing a with
  | nil => simp at ha
  | cons x L ih =>
    rw [List.flatMap_cons]
    rcases a with _ | a
    · rw [getD_append_lt _ _ _ (by rw [hk x (by simp)]; omega)]; simp
    · rw [getD_append_ge _ _ _ (by rw [hk x (by simp)]; nlinarith), hk x (by simp),
        show (a + 1) * k + b - k = a * k + b by rw [Nat.succ_mul]; omega,
        ih (fun y hy => hk y (by simp [hy])) (by simpa using ha)]
      simp

theorem getD_eqTable_append {K : Type _} [CommRing K] (r s : List K) {a b : ℕ}
    (ha : a < 2 ^ r.length) (hb : b < 2 ^ s.length) :
    (eqTable (r ++ s)).getD (a * 2 ^ s.length + b) 0 =
      (eqTable r).getD a 0 * (eqTable s).getD b 0 := by
  rw [eqTable_append, getD_flatMap_const _ _ (fun _ _ => by simp) _ (by simpa using ha) hb]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem (show a <
    (eqTable r).length by simpa using ha)]
  rcases h : (eqTable s)[b]? <;> simp

section Algebra

variable {A : Type _} [CommRing A] [Algebra IF A]

/-- Scale entry i of v by c(i). -/
def scaleFn (c : ℕ → IF) (v : List A) : List A := v.mapIdx fun i vi => vi * algebraMap IF A (c i)

@[simp] theorem length_scaleFn (c : ℕ → IF) (v : List A) : (scaleFn c v).length = v.length := by
  simp [scaleFn]

theorem scaleFn_scaleFn (c d : ℕ → IF) (v : List A) :
    scaleFn c (scaleFn d v) = scaleFn (fun i => d i * c i) v := by
  simp only [scaleFn, List.mapIdx_mapIdx, map_mul]
  congr 1; funext i a; simp [Function.comp, mul_assoc]

theorem getD_scaleFn (c : ℕ → IF) (v : List A) (i : ℕ) :
    (scaleFn c v).getD i 0 = v.getD i 0 * algebraMap IF A (c i) := by
  simp only [scaleFn, List.getD_eq_getElem?_getD, List.getElem?_mapIdx]
  cases v[i]? <;> simp

/-- The weighted table of the points at x: entry i is s_i eq(x, z_i). -/
def tab (rows : List (List IF)) (s : List A) (x : ℕ) : List A :=
  scaleFn (fun i => (eqTable (col rows i)).getD x 0) s

@[simp] theorem length_tab (rows : List (List IF)) (s : List A) (x : ℕ) :
    (tab rows s x).length = s.length := by simp [tab]

@[simp] theorem tab_nil (s : List A) : tab ([] : List (List IF)) s 0 = s := by
  simp only [tab, col, List.map_nil, eqTable_nil, List.getD_cons_zero]
  exact List.ext_getElem (by simp) fun i _ _ => by simp [scaleFn]

/-- One split of the weights: entry i times 1 - r_i, and entry i times r_i. -/
theorem splitPacked_eq (r : List IF) (v : List A) (h : v.length ≤ r.length) :
    splitPacked r v = (scaleFn (fun i => 1 - r.getD i 0) v, scaleFn (fun i => r.getD i 0) v) := by
  simp only [splitPacked, scaleFn, Prod.mk.injEq]
  constructor
  · refine List.ext_getElem (by simp; omega) fun i h1 h2 => ?_
    simp only [List.length_zipWith] at h1
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show i < r.length by omega),
      mul_sub]
  · refine List.ext_getElem (by simp; omega) fun i h1 h2 => ?_
    simp only [List.length_zipWith] at h1
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show i < r.length by omega)]

/-- Splitting the variables composes the tables. -/
theorem tab_append (R S : List (List IF)) (s : List A) {a b : ℕ} (ha : a < 2 ^ R.length)
    (hb : b < 2 ^ S.length) : tab (R ++ S) s (a * 2 ^ S.length + b) = tab S (tab R s a) b := by
  simp only [tab, scaleFn_scaleFn]
  congr 1; funext i
  rw [show col (R ++ S) i = col R i ++ col S i by simp [col],
    show S.length = (col S i).length by simp [col],
    getD_eqTable_append _ _ (by simpa [col] using ha) (by simpa [col] using hb)]

/-- The table of (r, S): the low half splits on 1 - r, the high half on r. -/
theorem tab_cons (r : List IF) (S : List (List IF)) (s : List A) (h : s.length ≤ r.length) {x : ℕ}
    (hx : x < 2 ^ (S.length + 1)) :
    tab (r :: S) s x = if x < 2 ^ S.length then tab S (splitPacked r s).1 x
      else tab S (splitPacked r s).2 (x - 2 ^ S.length) := by
  have key : ∀ a < 2, tab ([r] ++ S) s (a * 2 ^ S.length + x % 2 ^ S.length) =
      tab S (tab [r] s a) (x % 2 ^ S.length) := fun a ha =>
    tab_append [r] S s (by simpa using ha) (Nat.mod_lt _ (by positivity))
  have h1 : tab [r] s 0 = (splitPacked r s).1 := by
    rw [splitPacked_eq r s h]; simp [tab, col, eqTable_cons]
  have h2 : tab [r] s 1 = (splitPacked r s).2 := by
    rw [splitPacked_eq r s h]; simp [tab, col, eqTable_cons]
  split
  · rename_i hlt
    have := key 0 (by omega)
    rw [zero_mul, zero_add, Nat.mod_eq_of_lt hlt, h1] at this
    simpa using this
  · rename_i hge
    have := key 1 (by omega)
    rw [one_mul, h2, show x % 2 ^ S.length = x - 2 ^ S.length by
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by rw [pow_succ] at hx; omega)],
      show 2 ^ S.length + (x - 2 ^ S.length) = x by omega] at this
    simpa using this

/-! ## The buffer fill -/

/-- The bit-0 share one doubling keeps. -/
def keptOf (m : ℕ) (row : List IF) (v : List A) : List A :=
  let vals := v.zip (row.take m)
  let scaled := vals.map fun vz => vz.1 * algebraMap IF A vz.2
  (vals.zip scaled).map fun vs => vs.1.1 - vs.2

/-- The bit-1 share one doubling writes. -/
def scaledOf (m : ℕ) (row : List IF) (v : List A) : List A :=
  (v.zip (row.take m)).map fun vz => vz.1 * algebraMap IF A vz.2

theorem fillStep_eq (m : ℕ) (row : List IF) (stride : ℕ) :
    fillStep (A := A) m row stride = fun b idx =>
      (b.set idx (keptOf m row (b.getD idx []))).set (idx + stride) (scaledOf m row (b.getD idx [])) :=
  rfl

theorem keptOf_eq {m : ℕ} {row : List IF} {v : List A} (hv : v.length ≤ m) (hm : m ≤ row.length) :
    keptOf m row v = scaleFn (fun i => 1 - row.getD i 0) v := by
  refine List.ext_getElem (by simp [keptOf]; omega) fun i h1 h2 => ?_
  simp only [keptOf, List.length_map, List.length_zip, List.length_take] at h1
  simp [keptOf, scaleFn, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem (show i < row.length by omega), mul_sub]

theorem scaledOf_eq {m : ℕ} {row : List IF} {v : List A} (hv : v.length ≤ m) (hm : m ≤ row.length) :
    scaledOf m row v = scaleFn (fun i => row.getD i 0) v := by
  refine List.ext_getElem (by simp [scaledOf]; omega) fun i h1 h2 => ?_
  simp only [scaledOf, List.length_map, List.length_zip, List.length_take] at h1
  simp [scaledOf, scaleFn, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem (show i < row.length by omega)]

theorem ext_getD {α : Type _} (d : α) {l l' : List α} (h : l.length = l'.length)
    (h' : ∀ x < l.length, l.getD x d = l'.getD x d) : l = l' :=
  List.ext_getElem h fun x h1 h2 => by
    have := h' x h1
    simpa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1,
      List.getElem?_eq_getElem h2] using this

theorem scaleFn_comm (c d : ℕ → IF) (v : List A) : scaleFn c (scaleFn d v) = scaleFn d (scaleFn c v) := by
  simp only [scaleFn_scaleFn, mul_comm]

theorem keptOf_tab {m : ℕ} {a : List IF} (S : List (List IF)) {s : List A} (hs : s.length ≤ m)
    (ha : m ≤ a.length) (x : ℕ) : keptOf m a (tab S s x) = tab S (splitPacked a s).1 x := by
  rw [keptOf_eq (by simpa using hs) ha, splitPacked_eq a s (by omega), tab, tab, scaleFn_comm]

theorem scaledOf_tab {m : ℕ} {a : List IF} (S : List (List IF)) {s : List A} (hs : s.length ≤ m)
    (ha : m ≤ a.length) (x : ℕ) : scaledOf m a (tab S s x) = tab S (splitPacked a s).2 x := by
  rw [scaledOf_eq (by simpa using hs) ha, splitPacked_eq a s (by omega), tab, tab, scaleFn_comm]

theorem getD_map_range {α : Type _} (f : ℕ → α) (d : α) {k x : ℕ} (hx : x < k) :
    ((List.range k).map f).getD x d = f x := by
  simp [List.getD_eq_getElem?_getD, hx]

/-- One doubling pass enters a row of coordinates on the top bit of every table. -/
theorem fill_pass {m : ℕ} {s : List A} (hs : s.length ≤ m) {a : List IF} (ha : m ≤ a.length)
    (S : List (List IF)) (junk : List (List A)) (hj : 2 ^ S.length ≤ junk.length) :
    (List.range (2 ^ S.length)).foldl (fillStep m a (2 ^ S.length))
      ((List.range (2 ^ S.length)).map (tab S s) ++ junk) =
      (List.range (2 ^ (S.length + 1))).map (tab (a :: S) s) ++ junk.drop (2 ^ S.length) := by
  have hp : 2 ^ (S.length + 1) = 2 ^ S.length + 2 ^ S.length := by rw [pow_succ]; omega
  have hlen : ((List.range (2 ^ S.length)).map (tab S s)).length = 2 ^ S.length := by simp
  have hB : 2 * 2 ^ S.length ≤ ((List.range (2 ^ S.length)).map (tab S s) ++ junk).length := by
    simp; omega
  have hR : ∀ y < 2 ^ S.length,
      ((List.range (2 ^ S.length)).map (tab S s) ++ junk).getD y [] = tab S s y := fun y hy => by
    rw [getD_append_lt _ _ _ (by rwa [hlen]), getD_map_range _ _ hy]
  have hT : ∀ y < 2 ^ (S.length + 1),
      ((List.range (2 ^ (S.length + 1))).map (tab (a :: S) s) ++ junk.drop (2 ^ S.length)).getD y [] =
        tab (a :: S) s y := fun y hy => by
    rw [getD_append_lt _ _ _ (by simpa using hy), getD_map_range _ _ hy]
  obtain ⟨hl, hx⟩ := pairLoop_getElem (keptOf m a) (scaledOf m a) [] (2 ^ S.length) _ hB le_rfl
  rw [fillStep_eq]
  refine ext_getD [] (by rw [hl]; simp; omega) fun x hxl => ?_
  rw [hl] at hxl
  rw [hx x hxl]
  by_cases h1 : x < 2 ^ S.length
  · simp only [h1, ↓reduceIte]
    rw [hR x h1, hT x (by omega), keptOf_tab S hs ha, tab_cons a S s (by omega) (by omega)]
    simp [h1]
  · by_cases h2 : 2 ^ S.length ≤ x ∧ x < 2 ^ S.length + 2 ^ S.length
    · simp only [h1, h2, ↓reduceIte, and_self]
      rw [hR _ (by omega), hT x (by omega), scaledOf_tab S hs ha,
        tab_cons a S s (by omega) (by omega)]
      simp [h1]
    · simp only [h1, h2, ↓reduceIte]
      rw [getD_append_ge _ _ _ (by rw [hlen]; omega), getD_append_ge _ _ _ (by simp; omega)]
      simp only [hlen, List.length_map, List.length_range, List.getD_eq_getElem?_getD,
        List.getElem?_drop]
      congr 2; omega

theorem fill_loop {m : ℕ} {s : List A} (hs : s.length ≤ m) : ∀ (L S : List (List IF))
    (junk : List (List A)), (∀ r ∈ L, m ≤ r.length) →
    2 ^ (S.length + L.length) ≤ 2 ^ S.length + junk.length →
    (L.zipIdx S.length).foldl (fun buf ri => (List.range (2 ^ ri.2)).foldl
      (fillStep m ri.1 (2 ^ ri.2)) buf) ((List.range (2 ^ S.length)).map (tab S s) ++ junk) =
      (List.range (2 ^ (S.length + L.length))).map (tab (L.reverse ++ S) s) ++
        junk.drop (2 ^ (S.length + L.length) - 2 ^ S.length)
  | [], S, junk, _, _ => by simp
  | a :: L, S, junk, hL, hj => by
    have hmono : 2 ^ (S.length + 1) ≤ 2 ^ (S.length + (L.length + 1)) :=
      Nat.pow_le_pow_right two_pos (by omega)
    have hp : 2 ^ (S.length + 1) = 2 ^ S.length + 2 ^ S.length := by rw [pow_succ]; omega
    simp only [List.length_cons] at hj
    rw [List.zipIdx_cons, List.foldl_cons, fill_pass hs (hL a (by simp)) S junk (by omega)]
    have := fill_loop hs L (a :: S) (junk.drop (2 ^ S.length)) (fun r hr => hL r (by simp [hr]))
      (by simp only [List.length_cons, List.length_drop]
          rw [show S.length + 1 + L.length = S.length + (L.length + 1) by omega]; omega)
    simp only [List.length_cons] at this
    rw [this, List.drop_drop, List.reverse_cons, List.append_assoc, List.singleton_append,
      show S.length + 1 + L.length = S.length + (L.length + 1) by omega, List.length_cons]
    congr 2
    generalize 2 ^ (S.length + (L.length + 1)) = X at hmono ⊢
    generalize 2 ^ (S.length + 1) = Y at hmono hp ⊢
    omega

/-- fill_buffer_batch: started from the weights in row 0, row x holds the weighted table at x. -/
theorem fill_buffer_batch_eq {m : ℕ} (evals : List (List IF)) (s : List A) (hs : s.length = m)
    (hrows : ∀ r ∈ evals, m ≤ r.length) :
    fill_buffer_batch m m evals (s :: List.replicate (2 ^ evals.length - 1) (List.replicate m 0)) =
      some ((List.range (2 ^ evals.length)).map (tab evals s)) := by
  have h := fill_loop (le_of_eq hs) evals.reverse [] (List.replicate (2 ^ evals.length - 1)
    (List.replicate m 0)) (fun r hr => hrows r (by simpa using hr))
    (by simp; have := Nat.one_le_two_pow (n := evals.length); omega)
  simp only [List.length_nil, pow_zero, List.range_one, List.map_cons, List.map_nil, tab_nil,
    List.singleton_append, List.length_reverse, Nat.zero_add, List.reverse_reverse,
    List.append_nil] at h
  simp only [fill_buffer_batch, ne_eq, not_true_eq_false, ↓reduceIte, h, Option.some.injEq,
    List.append_right_eq_self, List.drop_eq_nil_iff, List.length_replicate]
  omega

end Algebra

end Plonky3Lean.Proofs.MultilinearUtil
