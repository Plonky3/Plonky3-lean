module

public import Plonky3Lean.Proofs.Lookup.Constraints

@[expose] public section

/-!
# Periodic columns in the prover

The prover's row context keeps the default periodic values, which are empty.

A lookup reading a periodic column therefore stops the permutation-trace generator on every nonempty trace.

The symbolic builder records such a lookup, and the constraint folders evaluate it.
-/

namespace Plonky3Lean.Proofs.Lookup

open p3_lookup.mirror p3_air.symbolic.mirror p3_air.builder.mirror p3_air.air.mirror

set_option linter.unusedSectionVars false

variable {F : Type} [Field F] [DecidableEq F] {K : Type} [Field K] [Algebra F K] [DecidableEq K]

theorem mapM_eq_none {α β : Type _} {f : α → Option β} {l : List α} {x : α} (hx : x ∈ l)
    (hf : f x = none) : l.mapM f = none := by
  induction l with
  | nil => simp at hx
  | cons a l ih =>
    rcases List.mem_cons.1 hx with rfl | hx
    · simp [List.mapM_cons, hf]
    · simp only [List.mapM_cons, Option.bind_eq_bind]
      cases f a <;> simp [ih hx]

/-- A periodic leaf does not resolve in the prover's row context. -/
theorem resolve_periodic (main : Mat F) (preprocessed : Option (Mat F)) (pv : List F) (i j : ℕ) :
    resolve (rowContext main preprocessed pv i) ()
      (.Leaf (.Variable ⟨.Periodic, j⟩) : SymbolicExpression F) = none := by
  simp [resolve, rowContext, LookupTraceBuilder]

/-- An additive lookup whose first count is a periodic leaf fails on every row. -/
theorem lookup_row_terms_periodic (ctx_main : Mat F) (preprocessed : Option (Mat F)) (pv : List F)
    (i : ℕ) (lookup : Lookup F) (hflags : lookup.flags = none) (he : lookup.elements ≠ [])
    {j : ℕ} (hm : lookup.multiplicities[0]? = some (.Leaf (.Variable ⟨.Periodic, j⟩)))
    (alpha : K) (powers : List K) :
    lookup_row_terms (rowContext ctx_main preprocessed pv i) lookup alpha powers = none := by
  obtain ⟨e, es, hes⟩ := List.exists_cons_of_ne_nil he
  unfold lookup_row_terms
  rw [hflags]
  refine mapM_eq_none (x := (e, 0)) (by simp [hes]) ?_
  simp [hm, resolve_periodic]

theorem chunks_ne_nil {α : Type _} {n : ℕ} (hn : 0 < n) {l : List α} (hl : l ≠ []) :
    ∃ c cs, chunks n l = some (c :: cs) ∧ c ≠ [] := by
  obtain ⟨a, l', rfl⟩ := List.exists_cons_of_ne_nil hl
  refine ⟨(a :: l').take n, chunks.go n l'.length ((a :: l').drop n), ?_, by simp; omega⟩
  simp [chunks, Nat.pos_iff_ne_zero.1 hn, chunks.go]

/-- **A periodic count stops the prover.** On every trace with a row, the permutation-trace generator fails for a lookup list holding an additive lookup whose first count reads a periodic column. -/
theorem generate_permutation_periodic (main : Mat F) (preprocessed : Option (Mat F)) (pv : List F)
    (lookups : List (Lookup F)) (challenges : List K) (num_threads min_task_len : ℕ)
    (hh : 0 < main.height) {lookup : Lookup F} (hl : lookup ∈ lookups) (hflags : lookup.flags = none)
    (he : lookup.elements ≠ [])
    {j : ℕ} (hm : lookup.multiplicities[0]? = some (.Leaf (.Variable ⟨.Periodic, j⟩))) :
    generate_permutation main preprocessed pv lookups challenges num_threads min_task_len = none := by
  obtain ⟨c, cs, hch, hc⟩ := chunks_ne_nil (α := ℕ) (n := 1024) (by norm_num)
    (l := List.range main.height) (by simp; omega)
  obtain ⟨r, rs, rfl⟩ := List.exists_cons_of_ne_nil hc
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hl
  have hrow : ∀ (lc : List (K × K)) (bp : List (List K)), lc.length = lookups.length →
      bp.length = lookups.length →
      process_chunk (r :: rs) main preprocessed pv lookups lc bp = none := by
    intro lc bp hlc hbp
    unfold process_chunk
    have hmem : ((lookups[k], lc[k]'(by omega)), bp[k]'(by omega)) ∈ (lookups.zip lc).zip bp := by
      have := List.getElem_mem (l := (lookups.zip lc).zip bp) (n := k) (by simp; omega)
      simpa using this
    rw [mapM_eq_none (x := r) List.mem_cons_self (mapM_eq_none hmem
      (lookup_row_terms_periodic main preprocessed pv r _ hflags he hm _ _))]
    rfl
  have hne : lookups.isEmpty = false := by
    cases lookups with
    | nil => simp at hk
    | cons => rfl
  unfold generate_permutation
  simp only [hne, Bool.false_eq_true, ite_false]
  split
  · rfl
  · cases hlc : lookups.mapM fun (l : Lookup F) => do
        let a ← challenges[2 * l.column]?
        let b ← challenges[2 * l.column + 1]?
        pure (a, b) with
    | none => simp
    | some lc =>
      have hl' := length_of_mapM_some hlc
      simp only [Option.bind_eq_bind, Option.bind_some, hch]
      rw [mapM_eq_none (f := fun rows => process_chunk rows main preprocessed pv lookups lc
        (lc.map fun x => (List.range (((lookups.flatMap (·.elements)).map List.length).foldr max
          0)).map fun j => x.2 ^ j)) List.mem_cons_self (hrow lc _ hl' (by simp [hl']))]
      rfl

end Plonky3Lean.Proofs.Lookup
