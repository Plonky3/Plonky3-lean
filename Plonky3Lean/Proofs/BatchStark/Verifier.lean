module

public import P3BatchStark.Assumptions.Mirror.Verifier
public import Plonky3Lean.Proofs.BatchStark.Transcript
public import Plonky3Lean.Proofs.BatchStark.Layout

@[expose] public section

/-!
# The batch verifier's shape checks

* One instance's checks accept exactly the documented shapes.
* A count mismatch is rejected first, as such, and a randomization mismatch next.
* An accepted shape fixes every count the transcript reads: one degree bit and one public-value list per instance, a terminal exactly for each instance with lookups, a permutation commitment exactly when some instance has lookups, and a randomization opening exactly when the scheme hides.
-/

set_option linter.unusedSectionVars false

namespace Plonky3Lean.Proofs.BatchStark

open p3_batch_stark.verifier.mirror p3_batch_stark.transcript.mirror p3_lookup.mirror

variable {C F K : Type}

/-! ## Except lemmas -/

theorem ensure_ok {c : Prop} [Decidable c] {e : BatchError} : ensure c e = .ok () ↔ c := by
  unfold ensure; split_ifs <;> simp_all [pure, Except.pure]

theorem ensure_ok_unit {c : Prop} [Decidable c] {e : BatchError} {a : Unit} : ensure c e = .ok a ↔ c :=
  ensure_ok

theorem ensure_error {c : Prop} [Decidable c] {e e' : BatchError} : ensure c e = .error e' ↔ ¬ c ∧ e = e' := by
  unfold ensure; split_ifs <;> simp_all [pure, Except.pure, throw, throwThe, MonadExceptOf.throw]

theorem ensure_bind {α : Type} {c : Prop} [Decidable c] {e : BatchError} {f : Unit → Except BatchError α}
    {x : α} : (ensure c e >>= f) = .ok x ↔ c ∧ f () = .ok x := by
  unfold ensure; split_ifs <;> simp_all [pure, Except.pure, throw, bind, Except.bind]

theorem bind_ok {α β : Type} {x : Except BatchError α} {f : α → Except BatchError β} {y : β} :
    (x >>= f) = .ok y ↔ ∃ a, x = .ok a ∧ f a = .ok y := by
  rcases x with e | a <;> simp [bind, Except.bind]

theorem mapM_ok_iff {α β : Type} (f : α → Except BatchError β) (l : List α) (ys : List β) :
    l.mapM f = .ok ys ↔ List.Forall₂ (fun a b => f a = .ok b) l ys := by
  induction l generalizing ys with
  | nil => cases ys <;> simp [pure, Except.pure]
  | cons a l ih =>
    rw [List.mapM_cons]
    rcases hfa : f a with e | b <;> rcases hm : l.mapM f with e' | bs <;> cases ys <;>
      simp [hfa, hm, bind, Except.bind, pure, Except.pure, ← ih]

theorem forM_ok_iff {α : Type} (f : α → Except BatchError Unit) (l : List α) :
    l.forM f = .ok () ↔ ∀ x ∈ l, f x = .ok () := by
  induction l with
  | nil => simp [pure, Except.pure]
  | cons a l ih =>
    show (f a >>= fun _ => l.forM f) = _ ↔ _
    rcases hfa : f a with e | u
    · simp [hfa, bind, Except.bind]
    · simpa [hfa, bind, Except.bind] using ih

/-! ## One instance -/

/-- The documented shape of one instance's openings. -/
def InstanceOk (cfg : Config) (common : CommonData C F) (air : AirInfo) (i : ℕ) (pv : List F)
    (ov : Opened K) (terminal : Option K) (n_chunks : ℕ) : Prop :=
  pv.length = air.num_public_values ∧ ov.trace_local.length = air.width ∧
  (if air.reads_main_next then ∃ v, ov.trace_next = some v ∧ v.length = air.width else ov.trace_next = none) ∧
  ov.quotient_chunks.length = n_chunks ∧ (∀ q ∈ ov.quotient_chunks, q.length = cfg.dimension) ∧
  (∀ r ∈ ov.random, r.length = cfg.dimension) ∧
  (match ov.preprocessed with
    | some (loc, next) => preprocessedWidth common i ≠ 0 ∧ loc.length = preprocessedWidth common i ∧
        (next.map List.length).getD 0 = (if air.reads_preprocessed_next then preprocessedWidth common i else 0) ∧
        (air.reads_preprocessed_next ∨ next = none)
    | none => preprocessedWidth common i = 0) ∧
  (let lookups := common.lookups.getD i []
   let e := if lookups.isEmpty then 0 else (lookups.length + 1) * cfg.dimension
   ov.permutation_local.length = e ∧ ov.permutation_next.length = e ∧ terminal.isSome = !lookups.isEmpty)

/-- One instance's checks accept exactly the documented shape. -/
theorem check_instance_ok_iff (cfg : Config) (common : CommonData C F) (air : AirInfo) (i : ℕ)
    (pv : List F) (ov : Opened K) (terminal : Option K) (n_chunks : ℕ) :
    check_instance cfg common air i pv ov terminal n_chunks = .ok () ↔
      InstanceOk cfg common air i pv ov terminal n_chunks := by
  unfold InstanceOk
  rcases hr : air.reads_main_next <;> rcases hp : ov.preprocessed with _ | ⟨loc, next⟩ <;>
    rcases ht : ov.trace_next with _ | v <;>
    simp [check_instance, hr, hp, ht, ensure_bind, ensure_ok, and_assoc]

/-! ## The whole shape -/

/-- The instance counts the verifier checks first. -/
def CountsOk (airs : List AirInfo) (proof : BatchProof C F K) (pvs : List (List F))
    (common : CommonData C F) : Prop :=
  proof.opened.length = airs.length ∧ pvs.length = airs.length ∧ proof.degree_bits.length = airs.length ∧
    proof.lookup_terminals.length = airs.length ∧ common.lookups.length = airs.length ∧
    ∀ g ∈ common.preprocessed, g.2.length = airs.length

/-- **Wrong table count.** The verifier rejects with the count error exactly when a per-instance list has another length than the AIRs. -/
theorem check_shape_count (cfg : Config) (airs : List AirInfo) (proof : BatchProof C F K)
    (pvs : List (List F)) (common : CommonData C F) (h : ¬ CountsOk airs proof pvs common) :
    check_shape cfg airs proof pvs common = .error .InstanceCountMismatch := by
  unfold CountsOk at h
  simp only [check_shape, ensure, h, ↓reduceIte]
  rfl

/-- **Randomization.** With the right counts, the verifier rejects with the randomization error exactly when a randomization opening or commitment disagrees with the hiding flag. -/
theorem check_shape_random (cfg : Config) (airs : List AirInfo) (proof : BatchProof C F K)
    (pvs : List (List F)) (common : CommonData C F) (hc : CountsOk airs proof pvs common)
    (h : ¬ ((∀ ov ∈ proof.opened, ov.random.isSome = cfg.zk) ∧ proof.random.isSome = cfg.zk)) :
    check_shape cfg airs proof pvs common = .error .RandomizationError := by
  unfold CountsOk at hc
  simp only [check_shape, ensure]
  rw [ite_eq_left_of_eq_true _ _ (eq_true hc), ite_eq_right_of_eq_false _ _ (eq_false h)]
  rfl

/-- What an accepted shape guarantees. -/
structure Shaped (cfg : Config) (airs : List AirInfo) (proof : BatchProof C F K) (pvs : List (List F))
    (common : CommonData C F) (checked : Checked) : Prop where
  counts : CountsOk airs proof pvs common
  random_opened : ∀ ov ∈ proof.opened, ov.random.isSome = cfg.zk
  random_com : proof.random.isSome = cfg.zk
  base_len : checked.base_degree_bits.length = airs.length
  degree : ∀ i < airs.length, validate_degree_bits cfg i (proof.degree_bits.getD i 0) =
    .ok (checked.base_degree_bits.getD i 0, 2 ^ proof.degree_bits.getD i 0)
  height : ∀ s, check_multiplicity_height_bound cfg.characteristic common.lookups
    (checked.base_degree_bits.map (2 ^ ·)) ≠ some (.error s)
  instances : ∀ i < airs.length, InstanceOk cfg common (airs.getD i default) i (pvs.getD i [])
    (proof.opened.getD i default) (proof.lookup_terminals.getD i none) (checked.num_quotient_chunks.getD i 0)
  num_lookups : checked.num_lookup_instances = (common.lookups.filter (!·.isEmpty)).length
  perm : proof.permutation.isSome = decide (checked.num_lookup_instances > 0)
  prep_widths : checked.preprocessed_widths = (List.range airs.length).map (preprocessedWidth common)

theorem validate_ok {cfg : Config} {i db b s : ℕ} (h : validate_degree_bits cfg i db = .ok (b, s)) :
    b = db - cfg.is_zk ∧ s = 2 ^ db := by
  unfold validate_degree_bits at h
  split_ifs at h
  simp_all

/-- **An accepted shape.** When the shape checks accept, every guarantee above holds. -/
theorem check_shape_ok {cfg : Config} {airs : List AirInfo} {proof : BatchProof C F K}
    {pvs : List (List F)} {common : CommonData C F} {checked : Checked}
    (h : check_shape cfg airs proof pvs common = .ok checked) : Shaped cfg airs proof pvs common checked := by
  simp only [check_shape, bind_ok, ensure_ok_unit, heightResult] at h
  obtain ⟨-, hc, -, ⟨hr1, hr2⟩, sizes, hm, h⟩ := h
  obtain ⟨_, hh, _, hf, _, hp, he⟩ := h
  simp only [pure, Except.pure, Except.ok.injEq] at he
  subst he
  rw [mapM_ok_iff] at hm
  have hlen : sizes.length = airs.length := by simpa using hm.length_eq.symm
  -- Entry i of the sizes is the validated degree of instance i.
  have hsize : ∀ i < airs.length, validate_degree_bits cfg i (proof.degree_bits.getD i 0) =
      .ok ((sizes.getD i (0, 0, 0)).1, 2 ^ proof.degree_bits.getD i 0) := by
    intro i hi
    have := (List.forall₂_iff_get.1 hm).2 i (by simpa using hi) (by omega)
    simp only [List.get_eq_getElem, List.getElem_range, bind_ok, pure, Except.pure,
      Except.ok.injEq] at this
    obtain ⟨⟨b, s⟩, hv, -, -, hb⟩ := this
    obtain ⟨-, rfl⟩ := validate_ok hv
    have hg : sizes.getD i (0, 0, 0) = sizes[i] := by
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show i < sizes.length by omega)]
    rw [hg, ← hb]
    exact hv
  refine ⟨hc, hr1, hr2, by simp [hlen], fun i hi => ?_, fun s hs => ?_, fun i hi => ?_, rfl, ?_, rfl⟩
  · rw [hsize i hi]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_getElem (show i < sizes.length by omega), Option.getD_some, Option.map_some]
  · rw [hs] at hh
    exact absurd hh (by simp [throw, throwThe, MonadExceptOf.throw])
  · rw [forM_ok_iff] at hf
    exact (check_instance_ok_iff ..).1 (hf i (List.mem_range.2 hi))
  · simpa using hp

end Plonky3Lean.Proofs.BatchStark
