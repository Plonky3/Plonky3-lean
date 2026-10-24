module

public import Plonky3Lean.Proofs.MultilinearUtil.EqBatchPacked

@[expose] public section

/-!
# Batched equality tables: both paths are the batched table

The batched equality evaluation writes, or adds, sum_i g_i eq(x, z_i) at every x.

This holds for every packing width 2^w and every thread count.

The variables split into the thread bits, the middle bits and the lane bits, from the top:

```text
    x = | t (log_2 T bits) | y (middle bits) | l (w bits) |
```
-/

namespace Plonky3Lean.Proofs.MultilinearUtil

open Plonky3Lean.Spec.MultilinearUtil p3_multilinear_util.mirror p3_multilinear_util.eq_batch.mirror
open Finset

variable {IF EF : Type _} [Field IF] [Field EF] [Algebra IF EF]

theorem tab_tab {A : Type _} [CommRing A] [Algebra IF A] (R S : List (List IF)) (s : List A)
    (a b : ℕ) :
    tab S (tab R s a) b = scaleFn (fun i => (eqTable (col R i)).getD a 0 *
      (eqTable (col S i)).getD b 0) s := by
  simp [tab, scaleFn_scaleFn]

/-- One lane of the packed tables is the weighted table of all the variables. -/
theorem lane_sum {W m : ℕ} (packed R S : List (List EF)) (g : List EF) (hg : g.length = m)
    (t y : ℕ) :
    List.ofFn (tab S (tab R ((List.range m).map fun i (l : Fin W) => (tab packed g l).getD i 0) t) y).sum =
      (List.range W).map fun l => (tab packed (tab S (tab R g t) y) l).sum := by
  refine List.ext_getElem (by simp) fun l h1 h2 => ?_
  simp only [tab_tab, List.getElem_ofFn, List.getElem_map, List.getElem_range]
  simp only [sum_eq_sum_getD, Finset.sum_apply, length_scaleFn, List.length_map, List.length_range,
    length_tab, hg]
  refine sum_congr rfl fun i hi => ?_
  rw [getD_scaleFn, getD_map_range _ _ (by simpa using hi)]
  simp only [Pi.mul_apply, Pi.algebraMap_apply, tab, getD_scaleFn, Algebra.algebraMap_self,
    RingHom.id_apply]
  ring

omit [Field IF] [Algebra IF EF] in
/-- The batched evaluation gives the batched table of the points, written or added.

This holds for every width and thread count. -/
theorem eval_eq_batch_eq (w T : ℕ) (initialized : Bool) {m : ℕ} (hm : 0 < m)
    (rows : List (List EF)) (out g : List EF) (hg : g.length = m)
    (hrows : ∀ r ∈ rows, m ≤ r.length) (hout : out.length = 2 ^ rows.length) :
    eval_eq_batch w T initialized m rows out g = some (addOrSet initialized out (bt rows g)) := by
  have hc1 : ¬ (m = 0) := by omega
  have hc2 : ¬ (m ≠ g.length) := by omega
  have hc3 : ¬ (out.length ≠ 2 ^ rows.length) := not_not.mpr hout
  simp only [eval_eq_batch, eval_eq_batch_common, hc1, hc2, hc3, ↓reduceIte]
  split
  · exact eval_eq_batch_basic_eq initialized m rows g out _ (fun r hr => hg ▸ hrows r hr) hg hout
      (le_max_left _ _)
  · rename_i hlarge
    -- The three groups of variables: thread, middle and lane.
    set n := rows.length with hn
    set lt := Nat.clog 2 T with hlt
    set packed := rows.drop (n - w) with hpacked
    set lead := (rows.take (n - w)).take lt with hlead
    set mid := (rows.take (n - w)).drop lt with hmid
    have hpl : packed.length = w := by simp [hpacked]; omega
    have hll : lead.length = lt := by simp [hlead]; omega
    have hsplit : rows = lead ++ (mid ++ packed) := by
      rw [hlead, hmid, hpacked, ← List.append_assoc, List.take_append_drop, List.take_append_drop]
    have hn' : n = lt + (mid.length + w) := by
      have := congrArg List.length hsplit; simp only [List.length_append] at this; omega
    have mem : ∀ l : List (List EF), (∀ r ∈ l, r ∈ rows) → ∀ r ∈ l, m ≤ r.length :=
      fun l hl r hr => hrows r (hl r hr)
    have hpr := mem packed (fun r hr => by rw [hsplit]; simp [hr])
    have hlr := mem lead (fun r hr => by rw [hsplit]; simp [hr])
    have hmr := mem mid (fun r hr => by rw [hsplit]; simp [hr])
    -- The packed seeds, then the thread seeds.
    set init := (List.range m).map fun i (l : Fin (2 ^ w)) => (tab packed g l).getD i 0 with hinit
    have hinitl : init.length = m := by simp [hinit]
    rw [show (extEvaluator (2 ^ w) m).init_packed_batch packed g = some init from
      packed_eq_poly_batch_eq packed g (by rw [hpl]) hg hpr]
    simp only [Option.bind_eq_bind, Option.bind_some, hinitl, ne_eq, not_true_eq_false, ↓reduceIte]
    have hbuf := fill_buffer_batch_eq (A := Fin (2 ^ w) → EF) lead init hinitl hlr
    rw [hll] at hbuf
    rw [hbuf, Option.bind_some]
    -- One packed recursion per thread.
    have hS : out.length / 2 ^ lt = 2 ^ mid.length * 2 ^ w := by
      rw [hout, hn', pow_add, pow_add, Nat.mul_div_cancel_left _ (by positivity)]
    have hout' : out.length = 2 ^ lt * (2 ^ mid.length * 2 ^ w) := by
      rw [hout, hn', pow_add, pow_add]
    rw [hS, chunks_eq (by positivity) hout', List.zip_map']
    rw [mapM_some _ _ (fun cb : List EF × List (Fin (2 ^ w) → EF) =>
        (List.range (2 ^ mid.length)).flatMap fun y =>
          addOrSet initialized (chunkAt (2 ^ w) cb.1 y) (List.ofFn (tab mid cb.2 y).sum)) fun cb hcb => by
      obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hcb
      simp only [List.mem_range] at ht
      exact eval_eq_packed_batch_eq _ _ _ _ _ (fun o l => addOrSet initialized o (List.ofFn l.sum))
        (fun o l ho _ => ext_accumulate_eq _ _ _ o l g ho) mid _ _ _ hmr (by simp [hinitl])
        (by rw [length_chunkAt hout' ht, Nat.mul_comm]) (le_of_eq_of_le (by ring) (le_max_left _ _))]
    simp only [List.map_map, Function.comp_def]
    simp only [Option.pure_def, Option.bind_some, ← List.flatMap_def]
    -- The batched table, reindexed by thread, block and lane.
    rw [bt_eq_map_tab rows g (fun r hr => hg ▸ hrows r hr), ← hn, hn', pow_add, pow_add,
      map_range_mul]
    simp only [map_range_mul (2 ^ mid.length) (2 ^ w)]
    rw [addOrSet_flatMap _ _ (fun t => by simp [List.length_flatMap]) _ _ hout', Option.some.injEq]
    refine List.flatMap_congr fun t ht => ?_
    simp only [List.mem_range] at ht
    rw [addOrSet_flatMap _ _ (fun y => by simp) _ _ (length_chunkAt hout' ht)]
    refine List.flatMap_congr fun y hy => ?_
    simp only [List.mem_range] at hy
    congr 1
    rw [lane_sum packed lead mid g hg t y]
    refine List.map_congr_left fun l hl => ?_
    simp only [List.mem_range] at hl
    congr 1
    rw [show t * (2 ^ mid.length * 2 ^ w) + (y * 2 ^ w + l) =
      t * 2 ^ (mid ++ packed).length + (y * 2 ^ packed.length + l) by
        simp [hpl, pow_add]]
    symm
    conv_lhs => rw [hsplit]
    rw [tab_append lead (mid ++ packed) g (by rw [hll]; exact ht) (by
      simp only [List.length_append, hpl, pow_add]; nlinarith),
      tab_append mid packed _ hy (by rw [hpl]; exact hl)]

theorem sum_zipWith_getD {α β γ : Type _} [Zero α] [Zero β] [AddCommMonoid γ] (f : α → β → γ)
    {a : List α} {b : List β} (h : a.length = b.length) :
    (List.zipWith f a b).sum = ∑ i ∈ range a.length, f (a.getD i 0) (b.getD i 0) := by
  induction a generalizing b with
  | nil => simp
  | cons x a ih =>
    obtain ⟨y, b, rfl⟩ := List.exists_cons_of_length_eq_add_one h.symm
    simp [ih (by simpa using h), sum_range_succ', add_comm]

/-- One lane of the base accumulation is the weighted table of all the variables. -/
theorem lane_sum_base {F : Type _} [Field F] [Algebra F EF] {W m : ℕ}
    (packed R S : List (List F)) (g : List EF) (hg : g.length = m) (t y : ℕ) :
    (List.range W).map (fun k => (List.zipWith (fun s (v : Fin W → F) =>
      s * algebraMap F EF (if h : k < W then v ⟨k, h⟩ else 0)) g
      (tab S (tab R ((List.range m).map fun i (l : Fin W) =>
        (tab packed (List.replicate m (1 : F)) l).getD i 0) t) y)).sum) =
      (List.range W).map fun l => (tab packed (tab S (tab R g t) y) l).sum := by
  refine List.map_congr_left fun k hk => ?_
  simp only [List.mem_range] at hk
  rw [sum_zipWith_getD _ (by simp [hg]), sum_eq_sum_getD]
  simp only [length_tab, hg, tab_tab, hk, ↓reduceDIte, length_scaleFn]
  refine sum_congr rfl fun i hi => ?_
  simp only [mem_range] at hi
  simp only [getD_scaleFn, getD_map_range _ _ hi, tab, Pi.mul_apply, Pi.algebraMap_apply,
    Algebra.algebraMap_self, RingHom.id_apply, map_mul]
  rw [show (List.replicate m (1 : F)).getD i 0 = 1 by
    rw [List.getD_eq_getElem?_getD, List.getElem?_replicate_of_lt hi, Option.getD_some]]
  simp only [map_one]
  ring

omit [Field IF] [Algebra IF EF] in
/-- The same holds for points in the base field and weights in the extension. -/
theorem eval_eq_base_batch_eq {F : Type _} [Field F] [Algebra F EF] (w T : ℕ) (initialized : Bool)
    {m : ℕ} (hm : 0 < m) (rows : List (List F)) (out g : List EF) (hg : g.length = m)
    (hrows : ∀ r ∈ rows, m ≤ r.length) (hout : out.length = 2 ^ rows.length) :
    eval_eq_base_batch w T initialized m rows out g =
      some (addOrSet initialized out (bt rows g)) := by
  have hc1 : ¬ (m = 0) := by omega
  have hc2 : ¬ (m ≠ g.length) := by omega
  have hc3 : ¬ (out.length ≠ 2 ^ rows.length) := not_not.mpr hout
  simp only [eval_eq_base_batch, eval_eq_batch_common, hc1, hc2, hc3, ↓reduceIte]
  split
  · exact eval_eq_batch_basic_eq initialized m rows g out _ (fun r hr => hg ▸ hrows r hr) hg hout
      (le_max_left _ _)
  · rename_i hlarge
    -- The three groups of variables: thread, middle and lane.
    set n := rows.length with hn
    set lt := Nat.clog 2 T with hlt
    set packed := rows.drop (n - w) with hpacked
    set lead := (rows.take (n - w)).take lt with hlead
    set mid := (rows.take (n - w)).drop lt with hmid
    have hpl : packed.length = w := by simp [hpacked]; omega
    have hll : lead.length = lt := by simp [hlead]; omega
    have hsplit : rows = lead ++ (mid ++ packed) := by
      rw [hlead, hmid, hpacked, ← List.append_assoc, List.take_append_drop, List.take_append_drop]
    have hn' : n = lt + (mid.length + w) := by
      have := congrArg List.length hsplit; simp only [List.length_append] at this; omega
    have mem : ∀ l : List (List F), (∀ r ∈ l, r ∈ rows) → ∀ r ∈ l, m ≤ r.length :=
      fun l hl r hr => hrows r (hl r hr)
    have hpr := mem packed (fun r hr => by rw [hsplit]; simp [hr])
    have hlr := mem lead (fun r hr => by rw [hsplit]; simp [hr])
    have hmr := mem mid (fun r hr => by rw [hsplit]; simp [hr])
    -- The packed seeds, then the thread seeds.
    set init := (List.range m).map fun i (l : Fin (2 ^ w)) =>
      (tab packed (List.replicate m (1 : F)) l).getD i 0 with hinit
    have hinitl : init.length = m := by simp [hinit]
    rw [show (baseEvaluator (EF := EF) (2 ^ w) m).init_packed_batch packed g = some init from
      packed_eq_poly_batch_eq packed _ (by rw [hpl]) (by simp) hpr]
    simp only [Option.bind_eq_bind, Option.bind_some, hinitl, ne_eq, not_true_eq_false, ↓reduceIte]
    have hbuf := fill_buffer_batch_eq (A := Fin (2 ^ w) → F) lead init hinitl hlr
    rw [hll] at hbuf
    rw [hbuf, Option.bind_some]
    -- One packed recursion per thread.
    have hS : out.length / 2 ^ lt = 2 ^ mid.length * 2 ^ w := by
      rw [hout, hn', pow_add, pow_add, Nat.mul_div_cancel_left _ (by positivity)]
    have hout' : out.length = 2 ^ lt * (2 ^ mid.length * 2 ^ w) := by
      rw [hout, hn', pow_add, pow_add]
    rw [hS, chunks_eq (by positivity) hout', List.zip_map']
    set acc : List EF → List (Fin (2 ^ w) → F) → List EF := fun o l => addOrSet initialized o
      ((List.range (2 ^ w)).map fun k => (List.zipWith (fun s (v : Fin (2 ^ w) → F) =>
        s * algebraMap F EF (if h : k < 2 ^ w then v ⟨k, h⟩ else 0)) g l).sum) with hacc
    rw [mapM_some _ _ (fun cb : List EF × List (Fin (2 ^ w) → F) =>
        (List.range (2 ^ mid.length)).flatMap fun y =>
          acc (chunkAt (2 ^ w) cb.1 y) (tab mid cb.2 y)) fun cb hcb => by
      obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hcb
      simp only [List.mem_range] at ht
      exact eval_eq_packed_batch_eq _ _ _ _ _ acc
        (fun o l ho hl => base_accumulate_eq _ _ _ o l g ho (by rw [hl, hg])) mid _ _ _ hmr
        (by simp [hinitl])
        (by rw [length_chunkAt hout' ht, Nat.mul_comm]) (le_of_eq_of_le (by ring) (le_max_left _ _))]
    simp only [List.map_map, Function.comp_def]
    simp only [Option.pure_def, Option.bind_some, ← List.flatMap_def]
    -- The batched table, reindexed by thread, block and lane.
    rw [bt_eq_map_tab rows g (fun r hr => hg ▸ hrows r hr), ← hn, hn', pow_add, pow_add,
      map_range_mul]
    simp only [map_range_mul (2 ^ mid.length) (2 ^ w)]
    rw [addOrSet_flatMap _ _ (fun t => by simp [List.length_flatMap]) _ _ hout', Option.some.injEq]
    refine List.flatMap_congr fun t ht => ?_
    simp only [List.mem_range] at ht
    rw [addOrSet_flatMap _ _ (fun y => by simp) _ _ (length_chunkAt hout' ht)]
    refine List.flatMap_congr fun y hy => ?_
    simp only [List.mem_range] at hy
    simp only [hacc]
    congr 1
    rw [lane_sum_base packed lead mid g hg t y]
    refine List.map_congr_left fun l hl => ?_
    simp only [List.mem_range] at hl
    congr 1
    rw [show t * (2 ^ mid.length * 2 ^ w) + (y * 2 ^ w + l) =
      t * 2 ^ (mid ++ packed).length + (y * 2 ^ packed.length + l) by
        simp [hpl, pow_add]]
    symm
    conv_lhs => rw [hsplit]
    rw [tab_append lead (mid ++ packed) g (by rw [hll]; exact ht) (by
      simp only [List.length_append, hpl, pow_add]; nlinarith),
      tab_append mid packed _ hy (by rw [hpl]; exact hl)]

end Plonky3Lean.Proofs.MultilinearUtil
