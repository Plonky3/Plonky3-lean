module

public import Plonky3Lean.Proofs.Commit.Periodic

@[expose] public section

/-!
# p3-commit: several periodic columns at once

The batched evaluation groups the columns by length.

Each group of k columns of length p is laid out as one matrix of width k:

```text
    values[r k + q] = column q of the group, row r        r < p, q < k
```

One interpolation then evaluates every column of the group.

The result agrees with evaluating the columns one at a time, panics included.
-/

open Polynomial Finset
open p3_commit.domain.mirror p3_field.coset.mirror p3_dft.mirror
open Plonky3Lean.Spec.Commit Plonky3Lean.Proofs.Dft

namespace Plonky3Lean.Proofs.Commit

set_option linter.unusedSectionVars false

variable {K : Type _} [Field K] [DecidableEq K] (G : Gen K)

/-! ## Writes into a buffer -/

section writes

variable {β : Type _} (pos : β → ℕ) (val : β → K)

/-- One write: position pos b takes value val b. -/
def write (V : ℕ → K) (b : β) : ℕ → K := fun j => if j = pos b then val b else V j

theorem foldl_write_other (L : List β) (V : ℕ → K) (j : ℕ) (hj : ∀ b ∈ L, pos b ≠ j) :
    L.foldl (write pos val) V j = V j := by
  induction L generalizing V with
  | nil => rfl
  | cons b L ih =>
    rw [List.foldl_cons, ih _ fun b' hb' => hj b' (by simp [hb'])]
    simp [write, Ne.symm (hj b (by simp))]

theorem foldl_write_mem (L : List β) (hL : L.Pairwise fun a b => pos a ≠ pos b) (V : ℕ → K) :
    ∀ b ∈ L, L.foldl (write pos val) V (pos b) = val b := by
  induction L generalizing V with
  | nil => simp
  | cons b L ih =>
    rw [List.pairwise_cons] at hL
    intro b' hb'
    rcases List.mem_cons.mp hb' with rfl | hb'
    · rw [List.foldl_cons, foldl_write_other _ _ _ _ _ fun b'' hb'' => (hL.1 b'' hb'').symm]
      simp [write]
    · exact ih hL.2 _ b' hb'

/-- Writes whose values follow a function g of the position leave g on every written position. -/
theorem foldl_write_eq (L : List β) (g : ℕ → K) (hv : ∀ b ∈ L, val b = g (pos b)) (V : ℕ → K) :
    L.foldl (write pos val) V = fun j => if j ∈ L.map pos then g j else V j := by
  induction L generalizing V with
  | nil => simp
  | cons b L ih =>
    rw [List.foldl_cons, ih fun b' hb' => hv b' (by simp [hb'])]
    funext j
    by_cases h1 : j ∈ L.map pos
    · simp [h1]
    · by_cases h2 : j = pos b
      · subst h2; simp [write, hv b (by simp)]
      · simp [h1, h2, write]

end writes

theorem pairwise_zipIdx {α : Type _} (l : List α) : l.zipIdx.Pairwise fun a b => a.2 < b.2 :=
  List.pairwise_iff_getElem.mpr fun i j _ _ hij => by simpa [List.getElem_zipIdx]

theorem mod_eq_of_add_mul {a b q q' k : ℕ} (hq : q < k) (hq' : q' < k) (h : a * k + q = b * k + q') :
    q = q' := by
  have := congrArg (· % k) h
  simpa [Nat.add_mod, Nat.mod_eq_of_lt hq, Nat.mod_eq_of_lt hq'] using this

/-! ## One group -/

/-- The value of column j at the point: its periodic polynomial. -/
noncomputable def pv (c : Coset G) (cols : List (List K)) (x : K) (j : ℕ) : K :=
  (periodicPoly c.shift c.subgroup_generator c.log_size (cols.getD j [])).eval x

theorem periodStep_none (c : Coset G) (cols : List (List K)) (x : K) (e : ℕ × List ℕ) :
    Coset.periodStep G c cols x none e = none := rfl

/-- A group whose length is not a power of two at most n panics, whatever came before. -/
theorem periodStep_bad (c : Coset G) (cols : List (List K)) (x : K) (acc : Option (ℕ → K))
    (e : ℕ × List ℕ) (he : ∀ l, e.1 = 2 ^ l → c.log_size < l) :
    Coset.periodStep G c cols x acc e = none := by
  cases acc with
  | none => rfl
  | some r =>
    simp only [Coset.periodStep, Option.bind_eq_bind, Option.bind_some]
    cases hl : log2Strict e.1 with
    | none => simp
    | some l => simp [not_le.mpr (he l (log2Strict_eq_some hl))]

/-- The interleaving buffer of a group, as a run of writes: row r of member q goes to r k + q. -/
def buf (cols : List (List K)) (idxs : List ℕ) : List (K × ℕ) :=
  idxs.zipIdx.flatMap fun q => (cols.getD q.1 []).zipIdx.map fun rv => (rv.1, rv.2 * idxs.length + q.2)

theorem buf_pairwise (cols : List (List K)) (idxs : List ℕ) :
    (buf cols idxs).Pairwise fun a b => a.2 ≠ b.2 := by
  rw [buf, List.pairwise_flatMap]
  refine ⟨fun q hq => ?_, ?_⟩
  · have hk : 0 < idxs.length := by have := (List.mem_zipIdx hq).2.1; omega
    rw [List.pairwise_map]
    exact (pairwise_zipIdx _).imp fun h h' =>
      h.ne (Nat.eq_of_mul_eq_mul_right hk (by simpa using h'))
  · refine (pairwise_zipIdx _).imp_of_mem fun {q q'} hq hq' hlt => ?_
    simp only [List.mem_map]
    rintro _ ⟨rv, -, rfl⟩ _ ⟨rv', -, rfl⟩ heq
    have h1 := (List.mem_zipIdx hq).2.1
    have h2 := (List.mem_zipIdx hq').2.1
    exact absurd (mod_eq_of_add_mul (by simpa using h1) (by simpa using h2) heq) (by omega)

/-- The buffer holds row r of member q at r k + q. -/
theorem buf_get (cols : List (List K)) (idxs : List ℕ) {p : ℕ}
    (hlen : ∀ j ∈ idxs, (cols.getD j []).length = p) (r q : ℕ) (hr : r < p) (hq : q < idxs.length) :
    (buf cols idxs).foldl (write Prod.snd Prod.fst) (fun _ => 0) (r * idxs.length + q) =
      (cols.getD idxs[q] []).getD r 0 := by
  have hl := hlen _ (List.getElem_mem hq)
  have hrv : ((cols.getD idxs[q] []).getD r 0, r) ∈ (cols.getD idxs[q] []).zipIdx :=
    List.mem_zipIdx_iff_getElem?.mpr (by
      rw [List.getD_eq_getElem (l := cols.getD idxs[q] []) _ (by rw [hl]; exact hr)]; exact List.getElem?_eq_getElem _)
  refine foldl_write_mem Prod.snd Prod.fst _ (buf_pairwise cols idxs) _ _
    (List.mem_flatMap.mpr ⟨(idxs[q], q), ?_, List.mem_map.mpr ⟨_, hrv, rfl⟩⟩)
  exact List.mem_zipIdx_iff_getElem?.mpr (by simp [hq])

/-- A group of columns of length 2^l <= n writes each member's value at the point. -/
theorem periodStep_good (hV : GenValid G) (hN : GenNested G) (h2 : (2 : K) ≠ 0) (c : Coset G)
    (cols : List (List K)) (x : K) (r : ℕ → K) (p : ℕ) (idxs : List ℕ) {l : ℕ} (hp : p = 2 ^ l)
    (hl : l ≤ c.log_size) (hlen : ∀ j ∈ idxs, (cols.getD j []).length = p) :
    Coset.periodStep G c cols x (some r) (p, idxs) =
      some fun j => if j ∈ idxs then pv G c cols x j else r j := by
  subst hp
  have hla : l ≤ G.adicity := hl.trans c.log_size_le
  have hW : idxs.zipIdx.foldl (fun (values : ℕ → K) q =>
      ((cols.getD q.1 []).zipIdx.foldl (fun (values : ℕ → K) rv =>
        fun j => if j = rv.2 * idxs.length + q.2 then rv.1 else values j) values)) (fun _ => 0) =
      (buf cols idxs).foldl (write Prod.snd Prod.fst) fun _ => 0 := by
    rw [buf, List.foldl_flatMap]
    simp only [List.foldl_map]
    rfl
  have hcol : ∀ q (hq : q < idxs.length),
      eval (x ^ 2 ^ (c.log_size - l)) (Lagrange.interpolate univ
        (Plonky3Lean.Proofs.Matrix.Interp.cosetPt (G.gen l) (c.shift ^ 2 ^ (c.log_size - l)) l)
        fun rr => (buf cols idxs).foldl (write Prod.snd Prod.fst) (fun _ => 0)
          (rr.val * idxs.length + q)) =
      pv G c cols x idxs[q] := by
    intro q hq
    simp only [buf_get cols idxs hlen _ q (Fin.isLt _) hq, pv,
      TwoAdicMultiplicativeCoset.subgroup_generator]
    rw [← comp_eq_periodicPoly G hV hN c.shift_ne_zero c.log_size_le hl (cols.getD idxs[q] [])
      (hlen _ (List.getElem_mem hq)), eval_comp]
    simp [interpolant, cosetPoints_eq_cosetPt]
  simp only [Coset.periodStep, Option.bind_eq_bind, Option.bind_some, log2Strict_pow, hl, ite_true,
    gen_get_of_le G hla,
    Plonky3Lean.Proofs.Matrix.Interp.interpolate_coset_eq (hV l hla) h2,
    pow_ne_zero _ c.shift_ne_zero, ite_false, Option.pure_def, Option.some.injEq]
  rw [hW, List.foldl_ext _ (write (fun q => q.1) fun q =>
      if h : q.2 < idxs.length then pv G c cols x idxs[q.2] else 0) _ fun acc q hq => ?_]
  · rw [foldl_write_eq _ _ _ (pv G c cols x) fun q hq => ?_]
    · funext j
      congr 1
      simp [List.mem_iff_getElem?]
    · obtain ⟨-, hq2, hq1⟩ := List.mem_zipIdx hq
      simp only [zero_add, Nat.sub_zero] at hq2 hq1
      simp [hq2, hq1]
  · obtain ⟨-, hq2, -⟩ := List.mem_zipIdx hq
    simp only [zero_add] at hq2
    funext j
    simp only [write, hq2, and_true]
    split_ifs with hj
    · exact hcol q.2 hq2
    · rfl

/-! ## Grouping by length -/

theorem mapInsert_mem (k v : ℕ) (L : List (ℕ × List ℕ)) :
    ∀ e ∈ Coset.mapInsert k v L, ∀ j ∈ e.2, (j = v ∧ e.1 = k) ∨ ∃ e' ∈ L, e'.1 = e.1 ∧ j ∈ e'.2 := by
  induction L with
  | nil =>
    intro e he j hj
    simp only [Coset.mapInsert, List.mem_singleton] at he
    subst he
    exact Or.inl ⟨by simpa using hj, rfl⟩
  | cons e0 L ih =>
    obtain ⟨k', vs⟩ := e0
    intro e he j hj
    simp only [Coset.mapInsert] at he
    split_ifs at he with h1 h2
    · rcases List.mem_cons.mp he with rfl | he
      · simp only [List.mem_append, List.mem_singleton] at hj
        rcases hj with hj | rfl
        · exact Or.inr ⟨_, List.mem_cons_self, rfl, hj⟩
        · exact Or.inl ⟨rfl, h1.symm⟩
      · exact Or.inr ⟨e, List.mem_cons_of_mem _ he, rfl, hj⟩
    · rcases List.mem_cons.mp he with rfl | he
      · exact Or.inl ⟨by simpa using hj, rfl⟩
      · rcases List.mem_cons.mp he with rfl | he
        · exact Or.inr ⟨_, List.mem_cons_self, rfl, hj⟩
        · exact Or.inr ⟨e, List.mem_cons_of_mem _ he, rfl, hj⟩
    · rcases List.mem_cons.mp he with rfl | he
      · exact Or.inr ⟨_, List.mem_cons_self, rfl, hj⟩
      · rcases ih e he j hj with h | ⟨e', he', h1', h2'⟩
        · exact Or.inl h
        · exact Or.inr ⟨e', List.mem_cons_of_mem _ he', h1', h2'⟩

theorem mapInsert_cover (k v : ℕ) (L : List (ℕ × List ℕ)) :
    (∃ e ∈ Coset.mapInsert k v L, e.1 = k ∧ v ∈ e.2) ∧
      ∀ e' ∈ L, ∀ j ∈ e'.2, ∃ e ∈ Coset.mapInsert k v L, e.1 = e'.1 ∧ j ∈ e.2 := by
  induction L with
  | nil => simp [Coset.mapInsert]
  | cons e0 L ih =>
    obtain ⟨k', vs⟩ := e0
    simp only [Coset.mapInsert]
    split_ifs with h1 h2
    · subst h1
      refine ⟨⟨_, List.mem_cons_self, rfl, by simp⟩, ?_⟩
      simp only [List.mem_cons, forall_eq_or_imp]
      exact ⟨fun j hj => ⟨_, Or.inl rfl, rfl, by simp [hj]⟩,
        fun e he j hj => ⟨e, Or.inr he, rfl, hj⟩⟩
    · refine ⟨⟨_, List.mem_cons_self, rfl, by simp⟩, ?_⟩
      simp only [List.mem_cons, forall_eq_or_imp]
      exact ⟨fun j hj => ⟨_, Or.inr (Or.inl rfl), rfl, hj⟩,
        fun e he j hj => ⟨e, Or.inr (Or.inr he), rfl, hj⟩⟩
    · obtain ⟨⟨e, he, h1', h2'⟩, ih2⟩ := ih
      refine ⟨⟨e, List.mem_cons_of_mem _ he, h1', h2'⟩, ?_⟩
      simp only [List.mem_cons, forall_eq_or_imp]
      refine ⟨fun j hj => ⟨_, Or.inl rfl, rfl, hj⟩, fun e' he' j hj => ?_⟩
      obtain ⟨e'', he'', h1'', h2''⟩ := ih2 e' he' j hj
      exact ⟨e'', Or.inr he'', h1'', h2''⟩

theorem mapInsert_ne_nil (k v : ℕ) (L : List (ℕ × List ℕ)) (hL : ∀ e ∈ L, e.2 ≠ []) :
    ∀ e ∈ Coset.mapInsert k v L, e.2 ≠ [] := by
  induction L with
  | nil => simp [Coset.mapInsert]
  | cons e0 L ih =>
    obtain ⟨k', vs⟩ := e0
    simp only [List.mem_cons, forall_eq_or_imp] at hL
    have ih := ih hL.2
    simp only [Coset.mapInsert]
    split_ifs
    · intro e he
      rcases List.mem_cons.mp he with rfl | he
      · simp
      · exact hL.2 e he
    · intro e he
      rcases List.mem_cons.mp he with rfl | he
      · simp
      · rcases List.mem_cons.mp he with rfl | he
        · exact hL.1
        · exact hL.2 e he
    · intro e he
      rcases List.mem_cons.mp he with rfl | he
      · exact hL.1
      · exact ih e he

/-- The grouping invariant: every group is nonempty, its members are known indices of its length, and every known index has a group. -/
def GroupInv (cols : List (List K)) (M : List (ℕ × List ℕ)) (S : ℕ → Prop) : Prop :=
  (∀ e ∈ M, e.2 ≠ [] ∧ ∀ j ∈ e.2, S j ∧ (cols.getD j []).length = e.1) ∧
    ∀ j, S j → ∃ e ∈ M, j ∈ e.2

theorem groupInv_foldl (cols : List (List K)) (Z : List (List K × ℕ))
    (hZ : ∀ z ∈ Z, cols.getD z.2 [] = z.1) (M : List (ℕ × List ℕ)) (S : ℕ → Prop)
    (hM : GroupInv cols M S) :
    GroupInv cols (Z.foldl (fun m p => Coset.mapInsert p.1.length p.2 m) M)
      fun j => S j ∨ j ∈ Z.map Prod.snd := by
  induction Z generalizing M S with
  | nil => simpa using hM
  | cons z Z ih =>
    rw [List.foldl_cons]
    have hz := hZ z List.mem_cons_self
    have h := ih (fun z' hz' => hZ z' (List.mem_cons_of_mem _ hz')) (Coset.mapInsert z.1.length z.2 M)
      (fun j => S j ∨ j = z.2) ?_
    · refine ⟨fun e he => ?_, fun j hj => h.2 j ?_⟩
      · refine ⟨(h.1 e he).1, fun j hj => ⟨?_, ((h.1 e he).2 j hj).2⟩⟩
        rcases ((h.1 e he).2 j hj).1 with (h' | h') | h'
        · exact Or.inl h'
        · exact Or.inr (by simp [h'])
        · exact Or.inr (by simp at h' ⊢; exact Or.inr h')
      · simp only [List.map_cons, List.mem_cons] at hj
        tauto
    · refine ⟨fun e he => ⟨mapInsert_ne_nil _ _ _ (fun e he => (hM.1 e he).1) e he,
        fun j hj => ?_⟩, fun j hj => ?_⟩
      · rcases mapInsert_mem _ _ _ e he j hj with ⟨rfl, h1⟩ | ⟨e', he', h1, h2⟩
        · exact ⟨Or.inr rfl, by rw [h1, hz]⟩
        · exact ⟨Or.inl ((hM.1 e' he').2 j h2).1, h1 ▸ ((hM.1 e' he').2 j h2).2⟩
      · rcases hj with hj | rfl
        · obtain ⟨e', he', hj'⟩ := hM.2 j hj
          obtain ⟨e, he, -, h2⟩ := (mapInsert_cover z.1.length z.2 M).2 e' he' j hj'
          exact ⟨e, he, h2⟩
        · obtain ⟨e, he, -, h2⟩ := (mapInsert_cover z.1.length z.2 M).1
          exact ⟨e, he, h2⟩

/-- The groups cover exactly the column indices, each with the length of its group. -/
theorem groupInv_colsByPeriod (cols : List (List K)) :
    GroupInv cols (Coset.colsByPeriod cols) fun j => j < cols.length := by
  have h := groupInv_foldl cols cols.zipIdx (fun z hz => ?_) [] (fun _ => False)
    ⟨by simp, by simp⟩
  · refine ⟨fun e he => ⟨(h.1 e he).1, fun j hj => ⟨?_, ((h.1 e he).2 j hj).2⟩⟩, fun j hj => h.2 j ?_⟩
    · rcases ((h.1 e he).2 j hj).1 with h' | h'
      · exact h'.elim
      · simp only [List.mem_map] at h'
        obtain ⟨z, hz, rfl⟩ := h'
        have := (List.mem_zipIdx hz).2.1
        simpa using this
    · refine Or.inr (List.mem_map.mpr ⟨(cols[j], j), ?_, rfl⟩)
      exact List.mem_zipIdx_iff_getElem?.mpr (by simp [hj])
  · obtain ⟨-, h1, h2⟩ := List.mem_zipIdx hz
    simp only [zero_add, Nat.sub_zero] at h1 h2
    simp [h2, List.getD_eq_getElem?_getD, h1]

/-! ## Agreement -/

theorem foldl_periodStep_none (c : Coset G) (cols : List (List K)) (x : K) (Es : List (ℕ × List ℕ)) :
    Es.foldl (Coset.periodStep G c cols x) none = none := by
  induction Es with
  | nil => rfl
  | cons e Es ih => exact ih

/-- One bad group anywhere makes the whole fold panic. -/
theorem foldl_periodStep_bad (c : Coset G) (cols : List (List K)) (x : K) (Es : List (ℕ × List ℕ))
    (e : ℕ × List ℕ) (he : e ∈ Es) (hbad : ∀ l, e.1 = 2 ^ l → c.log_size < l)
    (acc : Option (ℕ → K)) : Es.foldl (Coset.periodStep G c cols x) acc = none := by
  induction Es generalizing acc with
  | nil => simp at he
  | cons e' Es ih =>
    rw [List.foldl_cons]
    rcases List.mem_cons.mp he with rfl | he
    · rw [periodStep_bad G c cols x acc _ hbad, foldl_periodStep_none]
    · exact ih he _

/-- Good groups write every member's value. -/
theorem foldl_periodStep_good (hV : GenValid G) (hN : GenNested G) (h2 : (2 : K) ≠ 0) (c : Coset G)
    (cols : List (List K)) (x : K) (Es : List (ℕ × List ℕ))
    (hEs : ∀ e ∈ Es, (∃ l, e.1 = 2 ^ l ∧ l ≤ c.log_size) ∧ ∀ j ∈ e.2, (cols.getD j []).length = e.1)
    (r : ℕ → K) :
    Es.foldl (Coset.periodStep G c cols x) (some r) =
      some fun j => if j ∈ Es.flatMap Prod.snd then pv G c cols x j else r j := by
  induction Es generalizing r with
  | nil => simp
  | cons e Es ih =>
    obtain ⟨⟨l, hl, hlk⟩, hlen⟩ := hEs e List.mem_cons_self
    rw [List.foldl_cons, show e = (e.1, e.2) from rfl, periodStep_good G hV hN h2 c cols x r e.1 e.2 hl hlk hlen,
      ih fun e' he' => hEs e' (List.mem_cons_of_mem _ he')]
    congr 1
    funext j
    by_cases h1 : j ∈ Es.flatMap Prod.snd <;> by_cases h2 : j ∈ e.2 <;> simp [h1, h2]

theorem mapM_some {α β : Type _} (f : α → Option β) (g : α → β) (l : List α)
    (h : ∀ a ∈ l, f a = some (g a)) : l.mapM f = some (l.map g) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp [List.mapM_cons, h a List.mem_cons_self, ih fun a' ha' => h a' (List.mem_cons_of_mem _ ha')]

theorem mapM_none {α β : Type _} (f : α → Option β) (l : List α) (a : α) (ha : a ∈ l)
    (h : f a = none) : l.mapM f = none := by
  induction l with
  | nil => simp at ha
  | cons a' l ih =>
    rcases List.mem_cons.mp ha with rfl | ha
    · simp [List.mapM_cons, h]
    · simp only [List.mapM_cons, Option.bind_eq_bind]
      cases f a' <;> simp [ih ha]

/-- The batched evaluation agrees with evaluating the columns one at a time, panics included. -/
theorem evaluate_periodic_columns_at_eq_default (hV : GenValid G) (hN : GenNested G)
    (h2 : (2 : K) ≠ 0) (c : Coset G) (cols : List (List K)) (height : ℕ) (x : K) :
    Coset.evaluate_periodic_columns_at G c cols height x =
      Coset.default_evaluate_periodic_columns_at G c cols height x := by
  unfold Coset.evaluate_periodic_columns_at Coset.default_evaluate_periodic_columns_at
  split_ifs with hh
  · rfl
  have hinv := groupInv_colsByPeriod cols
  by_cases hg : ∀ col ∈ cols, ∃ l, col.length = 2 ^ l ∧ l ≤ c.log_size
  · have hEs : ∀ e ∈ Coset.colsByPeriod cols, (∃ l, e.1 = 2 ^ l ∧ l ≤ c.log_size) ∧
        ∀ j ∈ e.2, (cols.getD j []).length = e.1 := fun e he => by
      obtain ⟨hne, hmem⟩ := hinv.1 e he
      obtain ⟨j, hj⟩ := List.exists_mem_of_ne_nil _ hne
      obtain ⟨hjl, hlen⟩ := hmem j hj
      obtain ⟨l, hl, hlk⟩ := hg (cols.getD j []) (by rw [List.getD_eq_getElem _ _ hjl]; exact List.getElem_mem hjl)
      exact ⟨⟨l, hlen ▸ hl, hlk⟩, fun j hj => (hmem j hj).2⟩
    rw [foldl_periodStep_good G hV hN h2 c cols x _ hEs, mapM_some _
      (fun col => (periodicPoly c.shift c.subgroup_generator c.log_size col).eval x) _ fun col hcol => by
        obtain ⟨l, hl, hlk⟩ := hg col hcol
        exact evaluate_periodic_column_at_eq G hV hN h2 c col hl hlk x]
    simp only [Option.bind_eq_bind, Option.bind_some, Option.pure_def, Option.some.injEq]
    apply List.ext_getElem
    · simp
    · intro j h1 _
      have hj : j < cols.length := by simpa using h1
      obtain ⟨e, he, hje⟩ := hinv.2 j hj
      have : j ∈ (Coset.colsByPeriod cols).flatMap Prod.snd := List.mem_flatMap.mpr ⟨e, he, hje⟩
      simp [this, pv, List.getD_eq_getElem?_getD, hj]
  · push Not at hg
    obtain ⟨col, hcol, hbad⟩ := hg
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hcol
    have hnone : Coset.evaluate_periodic_column_at G c cols[j] x = none := by
      by_cases hp : ∃ l, cols[j].length = 2 ^ l
      · obtain ⟨l, hl⟩ := hp
        exact evaluate_periodic_column_at_long G c _ hl (hbad l hl) x
      · push Not at hp
        exact evaluate_periodic_column_at_not_pow G c _ hp x
    obtain ⟨e, he, hje⟩ := hinv.2 j hj
    have hkey : e.1 = cols[j].length := by
      have := ((hinv.1 e he).2 j hje).2
      simpa [List.getD_eq_getElem?_getD, hj] using this.symm
    rw [foldl_periodStep_bad G c cols x _ e he (fun l hl => hbad l (hkey ▸ hl)),
      mapM_none _ _ _ hcol hnone]
    rfl

end Plonky3Lean.Proofs.Commit
