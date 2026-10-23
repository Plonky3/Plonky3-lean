module

public import Plonky3Lean.Proofs.BatchStark.Replay
public import Plonky3Lean.Proofs.Lookup.Api

@[expose] public section

/-!
# What the batch verifier guarantees

* It never panics on a proof, once every AIR binds its public values by constraints and the keygen-cached lookups pass the layout's width checks.
* Its permutation round lists exactly the instances with lookups, in order, which is the prover's commit order.
* When it accepts: the shape checks and the height bound pass, the transcript is the pattern, every instance passes its check at the shared zeta with the shared alpha, the opening argument passes, and the terminals sum to zero.
-/

set_option linter.unusedSectionVars false

namespace Plonky3Lean.Proofs.BatchStark

open p3_batch_stark.verifier.mirror p3_batch_stark.transcript.mirror p3_lookup.mirror

variable {C F K : Type}

theorem mapM_ne_none {α β : Type} (f : α → Option β) (l : List α) (h : ∀ x ∈ l, f x ≠ none) :
    l.mapM f ≠ none := by
  induction l with
  | nil => simp
  | cons a l ih =>
    obtain ⟨b, hb⟩ := Option.ne_none_iff_exists'.1 (h a (by simp))
    obtain ⟨bs, hbs⟩ := Option.ne_none_iff_exists'.1 (ih fun x hx => h x (by simp [hx]))
    simp [List.mapM_cons, hb, hbs]

/-- Under an accepted shape, the reads Rust unwraps in the opening argument are all present. -/
theorem opening_reads_ne_none {cfg : Config} {airs : List AirInfo} {proof : BatchProof C F K}
    {pvs : List (List F)} {common : CommonData C F} {checked : Checked}
    (hS : Shaped cfg airs proof pvs common checked) : opening_reads airs proof ≠ none := by
  obtain ⟨ho, -, -, -, -, -⟩ := hS.counts
  have hn : ∀ i ∈ List.range airs.length, (fun i => if (airs.getD i default).reads_main_next then
      (proof.opened.getD i default).trace_next.map some else some none) i ≠ none := by
    intro i hi
    have := (hS.instances i (List.mem_range.1 hi)).2.2.1
    dsimp only
    split_ifs at this ⊢ with hr
    · obtain ⟨v, hv, -⟩ := this; rw [hv]; exact Option.some_ne_none _
    · exact Option.some_ne_none _
  obtain ⟨nexts, hnexts⟩ := Option.ne_none_iff_exists'.1 (mapM_ne_none _ _ hn)
  unfold opening_reads
  rw [hnexts]
  split_ifs with hrand
  · have hr : (List.range airs.length).mapM (fun i => (proof.opened.getD i default).random) ≠ none := by
      refine mapM_ne_none _ _ fun i hi => ?_
      have hi' : i < proof.opened.length := by rw [ho]; exact List.mem_range.1 hi
      have hmem : proof.opened.getD i default ∈ proof.opened := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi', Option.getD_some]
        exact List.getElem_mem hi'
      have := hS.random_opened _ hmem
      rw [hS.random_com] at hrand
      rw [hrand] at this
      exact Option.isSome_iff_ne_none.1 this
    obtain ⟨rs, hrs⟩ := Option.ne_none_iff_exists'.1 hr
    rw [hrs]; simp
  · simp

/-- **The permutation round.** With an extension of degree at least 1, the instances with a nonempty permutation opening are exactly those with lookups, in order: the prover's commit order. -/
theorem permutation_round {cfg : Config} {airs : List AirInfo} {proof : BatchProof C F K}
    {pvs : List (List F)} {common : CommonData C F} {checked : Checked}
    (hS : Shaped cfg airs proof pvs common checked) (hD : 1 ≤ cfg.dimension) :
    (List.range airs.length).filter (fun i => !(proof.opened.getD i default).permutation_local.isEmpty) =
      (List.range airs.length).filter (fun i => !(common.lookups.getD i []).isEmpty) := by
  refine List.filter_congr fun i hi => ?_
  have h := (hS.instances i (List.mem_range.1 hi)).2.2.2.2.2.2.2.1
  rcases hl : (common.lookups.getD i []).isEmpty <;> simp only [hl, Bool.false_eq_true, ↓reduceIte] at h
  · have : (proof.opened.getD i default).permutation_local ≠ [] := by
      intro he
      rw [he, List.length_nil] at h
      exact absurd h.symm (Nat.mul_pos (Nat.succ_pos _) hD).ne'
    simpa using this
  · simpa using List.length_eq_zero_iff.1 h

section Verify

variable [Zero F] [DecidableEq F] [Field K] [DecidableEq K]

/-- **The verifier never panics on a proof.** When every AIR binds its public values by constraints and the keygen-cached lookups pass the layout's width checks, verification returns an acceptance or an error on every proof. -/
theorem verify_batch_ne_none (cfg : Config) (airs : List AirInfo) (proof : BatchProof C F K)
    (pvs : List (List F)) (common : CommonData C F) (H : List (Msg C F K) → K)
    (powOk : List (Msg C F K) → ℕ → F → Bool) (pcsOk : List (Msg C F K) → K → Bool)
    (checkAt : ℕ → List K → K → K → Except BatchError Unit)
    (hb : airs.all (·.boundary_io_empty)) (hW : WidthsOk common.lookups.flatten) :
    verify_batch cfg airs proof pvs common H powOk pcsOk checkAt ≠ none := by
  unfold verify_batch
  simp only [hb, not_true_eq_false, ↓reduceIte]
  rcases hc : check_shape cfg airs proof pvs common with e | checked
  · simp
  · obtain ⟨st, r, hr, -, -⟩ := replay_played (check_shape_ok hc) hW H powOk
    obtain ⟨o, ho⟩ := Option.ne_none_iff_exists'.1 (opening_reads_ne_none (check_shape_ok hc))
    simp only [hr, Option.bind_eq_bind, Option.bind_some]
    rcases r with e | ⟨ch, α, ζ⟩
    · simp
    · simp only [ho, Option.bind_some]
      split_ifs <;> (try split) <;> simp_all

/-- **What acceptance means.** When verification accepts:

* the shape checks accept, so the height bound passes and every guarantee of an accepted shape holds;
* the replay accepts with the steps of the pattern, and yields the lookup challenges, alpha and zeta;
* the opening argument accepts at zeta;
* every instance passes its check at the shared zeta, with the shared alpha and its own challenges;
* the present terminals sum to zero. -/
theorem verify_batch_accepts {cfg : Config} {airs : List AirInfo} {proof : BatchProof C F K}
    {pvs : List (List F)} {common : CommonData C F} {H : List (Msg C F K) → K}
    {powOk : List (Msg C F K) → ℕ → F → Bool} {pcsOk : List (Msg C F K) → K → Bool}
    {checkAt : ℕ → List K → K → K → Except BatchError Unit}
    (h : verify_batch cfg airs proof pvs common H powOk pcsOk checkAt = some (.ok ())) :
    ∃ checked st ch α ζ, Shaped cfg airs proof pvs common checked ∧
      replay cfg airs proof pvs common checked H powOk = some (st, .ok (ch, α, ζ)) ∧
      pcsOk st.msgs ζ ∧ (∀ i < airs.length, checkAt i (ch.getD i []) α ζ = .ok ()) ∧
      (proof.lookup_terminals.filterMap id).sum = 0 := by
  unfold verify_batch at h
  by_cases hb : (airs.all fun x => x.boundary_io_empty) = true
  swap
  · simp [hb] at h
  simp only [hb, not_true_eq_false, ↓reduceIte] at h
  rcases hc : check_shape cfg airs proof pvs common with e | checked
  · simp [hc] at h
  · simp only [hc, Option.bind_eq_bind] at h
    rcases hr : replay cfg airs proof pvs common checked H powOk with _ | ⟨st, r⟩
    · simp [hr] at h
    · rw [hr] at h
      rcases r with e | ⟨ch, α, ζ⟩
      · simp at h
      · simp only [Option.bind_some] at h
        rcases ho : opening_reads airs proof with _ | o
        · simp [ho] at h
        · simp only [ho, Option.bind_some] at h
          refine ⟨checked, st, ch, α, ζ, check_shape_ok hc, hr, ?_⟩
          by_cases hp : pcsOk st.msgs ζ
          · simp only [hp, not_true_eq_false, ↓reduceIte] at h
            rcases hf : (List.range airs.length).forM fun i => checkAt i (ch.getD i []) α ζ with e | u
            · rw [hf] at h; simp at h
            · rw [hf] at h
              refine ⟨hp, fun i hi => (forM_ok_iff _ _).1 hf i (List.mem_range.2 hi), ?_⟩
              by_cases ht : verify_terminal_sum proof.lookup_terminals
              · exact (Plonky3Lean.Proofs.Lookup.verify_terminal_sum_iff _).1 ht
              · simp [ht] at h
          · simp [hp] at h

end Verify

end Plonky3Lean.Proofs.BatchStark
