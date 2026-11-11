module

public import Plonky3Lean.Proofs.BatchStark.EndToEnd

@[expose] public section

/-!
# When the full batch verifier panics

- The verifier never panics on any proof, under conditions on the configuration, the AIRs and the common data.
- At the pin, each grind panics exactly when it is reached at a difficulty the field cannot sample.
- So a batch proof that reaches either grind at such a difficulty panics the verifier.
-/

set_option linter.unusedSectionVars false

universe u

namespace Plonky3Lean.Proofs.BatchStark.EndToEnd

open p3_air.air.mirror p3_lookup.mirror p3_air.builder.mirror
open p3_uni_stark.verify.mirror (validate_degree_bits checked_log_size_sum WORD_BITS natural_domain_for_degree
  PreprocessedOpening)
open p3_uni_stark.verifier.mirror (recompose_quotient_from_chunks from_ext_basis_coefficients)
open p3_batch_stark.transcript.mirror p3_batch_stark.constraints.mirror p3_batch_stark.verify.mirror
open p3_commit.domain.mirror p3_commit.periodic.mirror p3_field.coset.mirror p3_dft.mirror
open p3_commit.pcs.univariate.mirror
open Plonky3Lean.Proofs.UniStark Plonky3Lean.Proofs.Commit Plonky3Lean.Proofs.Dft Plonky3Lean.Proofs.Air
open Plonky3Lean.Spec.Commit Plonky3Lean.Spec.Air Plonky3Lean.Spec.UniStark

variable {F K C Com S P PE : Type} [Field F] [DecidableEq F] [Inhabited F] [Field K] [DecidableEq K]
  [Algebra F K]

/-! ## Not panicking, step by step -/

theorem bind_ne_none {α β : Type} {m : M α} {k : α → M β} (hm : m.run ≠ none)
    (hk : ∀ a, m = pure a → (k a).run ≠ none) : (m >>= k).run ≠ none := by
  change Option (Except Error α) at m
  rcases m with _ | (e | a)
  · exact absurd rfl hm
  · intro h; cases h
  · exact hk a rfl

theorem throw_ne_none {α : Type} (e : Error) : (throw e : M α).run ≠ none := by
  intro h; cases h

theorem pure_ne_none {α : Type} (a : α) : (pure a : M α).run ≠ none := by
  intro h; cases h

theorem mk_ne_none {α : Type} (e : Except Error α) : (ExceptT.mk (some e) : M α).run ≠ none := by
  intro h; cases h

theorem mapM_ne_none {α : Type u} {β : Type} (f : α → M β) :
    ∀ l : List α, (∀ x ∈ l, (f x).run ≠ none) → (l.mapM f).run ≠ none
  | [], _ => pure_ne_none _
  | x :: l, h => by
    rw [List.mapM_cons]
    exact bind_ne_none (h x List.mem_cons_self) fun _ _ =>
      bind_ne_none (mapM_ne_none f l fun y hy => h y (List.mem_cons_of_mem _ hy)) fun _ _ => pure_ne_none _

theorem forM_ne_none {α : Type u} (f : α → M PUnit) :
    ∀ l : List α, (∀ x ∈ l, (f x).run ≠ none) → (l.forM f).run ≠ none
  | [], _ => pure_ne_none _
  | x :: l, h => by
    show (f x >>= fun _ => l.forM f).run ≠ none
    exact bind_ne_none (h x List.mem_cons_self) fun _ _ =>
      forM_ne_none f l fun y hy => h y (List.mem_cons_of_mem _ hy)

theorem pure_inj {α : Type} {a b : α} (h : (pure a : M α) = pure b) : a = b :=
  Except.ok.inj (Option.some.inj h)

theorem panicOf_ne_none {α : Type} {o : Option α} (h : o ≠ none) : (panicOf o).run ≠ none := by
  obtain ⟨a, rfl⟩ := Option.ne_none_iff_exists'.1 h
  exact pure_ne_none a

theorem getElem?_ne_none {α : Type} {l : List α} {i : ℕ} (h : i < l.length) : l[i]? ≠ none := by
  simp [h]

/-! ## The shape checks -/

section shape

variable (G : Gen K) (cfg : Config) (common : CommonData C F) (sizing : ℕ → AirLayout → ℕ → Option ℕ)

/-- The subgroup of order 2^b, when b lies within the generator table. -/
theorem natural_domain_ne_none {b : ℕ} (hb : b ≤ G.adicity) : natural_domain_for_degree G (2 ^ b) ≠ none := by
  rw [natural_domain_pow G ⟨1, b, one_ne_zero, hb⟩ rfl rfl]; simp

/-- The shape checks never panic, when the largest height lies within the generator table and the sizing returns. -/
theorem check_shape_ne_none (hmax : cfg.log_max_trace_height ≤ G.adicity)
    (hsizing : ∀ i l n, ∃ r, sizing i l n = some r) (airs : List (BatchAir F)) (proof : BatchProof C P F K)
    (pvs : List (List F)) :
    (check_shape G cfg airs sizing proof pvs common).run ≠ none := by
  unfold check_shape
  refine bind_ne_none (mk_ne_none _) fun _ h1 => ?_
  obtain ⟨c1, c2, c3, c4, c5, c6⟩ := ensure_eq_ok.1 (mk_eq_pure.1 h1)
  refine bind_ne_none (mk_ne_none _) fun _ _ => ?_
  refine bind_ne_none (mapM_ne_none _ _ fun ⟨ba, i⟩ hx => ?_) fun sizes hsz => ?_
  · have hi : i < airs.length := (List.getElem?_eq_some_iff.1 (List.mem_zipIdx_iff_getElem?.1 hx)).1
    unfold instance_sizes
    refine bind_ne_none (panicOf_ne_none (getElem?_ne_none (c3 ▸ hi))) fun db _ => ?_
    refine bind_ne_none (mk_ne_none _) fun ⟨b, e⟩ hv => ?_
    obtain ⟨rfl, -, -, hhi, -⟩ := validate_at_ok (mk_eq_pure.1 hv)
    refine bind_ne_none ?_ fun w _ => ?_
    · unfold preprocessed_width
      rcases hg : common.preprocessed with _ | gl
      · exact pure_ne_none _
      · exact bind_ne_none (panicOf_ne_none (getElem?_ne_none (by rw [c6 gl hg]; exact hi)))
          fun _ _ => pure_ne_none _
    refine bind_ne_none (panicOf_ne_none (natural_domain_ne_none G (by omega))) fun bd _ => ?_
    obtain ⟨r, hr⟩ := hsizing i (layoutOf ba w) (Coset.size G bd)
    refine bind_ne_none (panicOf_ne_none (by simp only [layoutOf] at hr; rw [hr]; simp)) fun lq _ => ?_
    rcases checked_log_size_sum lq cfg.zk.toNat with _ | ⟨_, _⟩
    · exact throw_ne_none _
    · exact pure_ne_none _
  have hsl : sizes.length = airs.length := by simpa using ((mapM_eq_pure _ _ _).1 hsz).length_eq.symm
  refine bind_ne_none (panicOf_ne_none (by simp [check_multiplicity_height_bound, c5, hsl])) fun r _ => ?_
  rcases r with e | ⟨⟩
  · exact bind_ne_none (throw_ne_none _) fun _ h => absurd h throw_ne_pure
  refine bind_ne_none (forM_ne_none _ _ fun ⟨ba, i⟩ hx => ?_) fun _ _ =>
    bind_ne_none (mk_ne_none _) fun _ _ => pure_ne_none _
  have hi : i < airs.length := (List.getElem?_eq_some_iff.1 (List.mem_zipIdx_iff_getElem?.1 hx)).1
  exact bind_ne_none (panicOf_ne_none (getElem?_ne_none (c2 ▸ hi))) fun _ _ =>
    bind_ne_none (panicOf_ne_none (getElem?_ne_none (c1 ▸ hi))) fun _ _ =>
    bind_ne_none (panicOf_ne_none (getElem?_ne_none (hsl ▸ hi))) fun _ _ =>
    bind_ne_none (panicOf_ne_none (getElem?_ne_none (c5 ▸ hi))) fun _ _ =>
    bind_ne_none (panicOf_ne_none (getElem?_ne_none (c4 ▸ hi))) fun _ _ => mk_ne_none _

/-- The base trace subgroup of instance i, of order 2^(b - z), clamped to the generator table. -/
def tdOf (dbs : List ℕ) (i : ℕ) : Coset G :=
  ⟨1, min (dbs.getD i 0 - cfg.zk.toNat) G.adicity, one_ne_zero, min_le_right _ _⟩

/-- The extended trace subgroup of instance i, of order 2^b, clamped to the generator table. -/
def edOf (dbs : List ℕ) (i : ℕ) : Coset G :=
  ⟨1, min (dbs.getD i 0) G.adicity, one_ne_zero, min_le_right _ _⟩

end shape

section claims

variable {G : Gen K} (hV : GenValid G) (g : K) {cfg : Config} {common : CommonData C F}
  {sizing : ℕ → AirLayout → ℕ → Option ℕ} {airs : List (BatchAir F)} {proof : BatchProof C P F K}
  {pvs : List (List F)} {sizes : List Sizes} {k : ℕ}

theorem tdOf_ok (hmax : cfg.log_max_trace_height ≤ G.adicity) (hs : ShapeOk G cfg common sizing airs proof pvs sizes k)
    {i : ℕ} (hi : i < proof.degree_bits.length) :
    (tdOf G cfg proof.degree_bits i).shift = 1 ∧
      (tdOf G cfg proof.degree_bits i).log_size = proof.degree_bits.getD i 0 - cfg.zk.toNat := by
  have := (hs.sizes_getD hi).2.hi
  exact ⟨rfl, by simp only [tdOf]; omega⟩

theorem edOf_ok (hmax : cfg.log_max_trace_height ≤ G.adicity) (hs : ShapeOk G cfg common sizing airs proof pvs sizes k)
    {i : ℕ} (hi : i < proof.degree_bits.length) :
    (edOf G proof.degree_bits i).shift = 1 ∧ (edOf G proof.degree_bits i).log_size = proof.degree_bits.getD i 0 := by
  have := (hs.sizes_getD hi).2.hi
  exact ⟨rfl, by simp only [edOf]; omega⟩

/-- The quotient domains never panic, and each instance's are the chunks of a quotient coset of order 2^(b + L). -/
theorem quotient_domains_spec (hs : ShapeOk G cfg common sizing airs proof pvs sizes k) :
    let doms := (List.range proof.degree_bits.length).map fun i =>
      (tdOf G cfg proof.degree_bits i, edOf G proof.degree_bits i)
    (quotient_domains G g cfg proof.degree_bits sizes doms).run ≠ none ∧
      ∀ q, quotient_domains G g cfg proof.degree_bits sizes doms = pure q →
        q.length = proof.degree_bits.length ∧ ∀ i < proof.degree_bits.length, ∃ qdc : Coset G,
          qdc.log_size = proof.degree_bits.getD i 0 + (sizes.getD i default).log_num_quotient_chunks ∧
          q.getD i [] = (List.range (2 ^ ((sizes.getD i default).log_num_quotient_chunks + cfg.zk.toNat))).map
            (chunk G hV qdc ((sizes.getD i default).log_num_quotient_chunks + cfg.zk.toNat)) := by
  intro doms
  have get : ∀ i < proof.degree_bits.length, proof.degree_bits[i]? = some (proof.degree_bits.getD i 0) ∧
      sizes[i]? = some (sizes.getD i default) ∧ doms[i]?.map (·.2) = some (edOf G proof.degree_bits i) :=
    fun i hi => ⟨by simp [hi], (hs.sizes_getD hi).1, by simp [doms, hi]⟩
  have split : ∀ i < proof.degree_bits.length, ∀ qdc : Coset G,
      Coset.try_create_disjoint_domain G (edOf G proof.degree_bits i) g
        (2 ^ (proof.degree_bits.getD i 0 + (sizes.getD i default).log_num_quotient_chunks)) = some qdc →
      qdc.log_size = proof.degree_bits.getD i 0 + (sizes.getD i default).log_num_quotient_chunks ∧
      Coset.split_domains G qdc (2 ^ ((sizes.getD i default).log_num_quotient_chunks + cfg.zk.toNat)) =
        some ((List.range (2 ^ ((sizes.getD i default).log_num_quotient_chunks + cfg.zk.toNat))).map
          (chunk G hV qdc ((sizes.getD i default).log_num_quotient_chunks + cfg.zk.toNat))) := fun i hi qdc h => by
    obtain ⟨-, h2, -⟩ := try_create_disjoint_domain_some G h
    rw [log2Ceil_pow] at h2
    have := (hs.sizes_getD hi).2.lo
    exact ⟨h2, split_domains_eq G hV qdc (by omega)⟩
  unfold quotient_domains
  refine ⟨mapM_ne_none _ _ fun i hi => ?_, fun q hq => ?_⟩
  · have hi := List.mem_range.1 hi
    obtain ⟨g1, g2, g3⟩ := get i hi
    have hw := (hs.sizes_getD hi).2.chunks_word
    simp only [g1, g2, g3, panicOf_some, pure_bind, checked_eq hw]
    rcases hc : checked_log_size_sum (proof.degree_bits.getD i 0) (sizes.getD i default).log_num_quotient_chunks
      with _ | ⟨x, n⟩
    · exact bind_ne_none (throw_ne_none _) fun _ h => absurd h throw_ne_pure
    obtain ⟨-, rfl, -⟩ := checked_some hc
    dsimp only
    rcases ht : Coset.try_create_disjoint_domain G (edOf G proof.degree_bits i) g
      (2 ^ (proof.degree_bits.getD i 0 + (sizes.getD i default).log_num_quotient_chunks)) with _ | qdc
    · exact bind_ne_none (throw_ne_none _) fun _ h => absurd h throw_ne_pure
    rw [orReject_some, pure_bind, (split i hi qdc ht).2, panicOf_some]
    exact pure_ne_none _
  · have hF := (mapM_eq_pure _ _ _).1 hq
    have hlen : q.length = proof.degree_bits.length := by simpa using hF.length_eq.symm
    refine ⟨hlen, fun i hi => ?_⟩
    have hqi : i < q.length := hlen ▸ hi
    have hfi := (List.forall₂_iff_get.1 hF).2 i (by simpa using hi) hqi
    simp only [List.get_eq_getElem, List.getElem_range] at hfi
    obtain ⟨g1, g2, g3⟩ := get i hi
    have hw := (hs.sizes_getD hi).2.chunks_word
    simp only [g1, g2, g3, panicOf_some, pure_bind, checked_eq hw] at hfi
    rcases hc : checked_log_size_sum (proof.degree_bits.getD i 0) (sizes.getD i default).log_num_quotient_chunks
      with _ | ⟨x, n⟩ <;> rw [hc] at hfi
    · obtain ⟨_, h, -⟩ := bind_eq_pure.1 hfi; exact absurd h throw_ne_pure
    obtain ⟨-, rfl, -⟩ := checked_some hc
    dsimp only at hfi
    rcases ht : Coset.try_create_disjoint_domain G (edOf G proof.degree_bits i) g
      (2 ^ (proof.degree_bits.getD i 0 + (sizes.getD i default).log_num_quotient_chunks)) with _ | qdc <;>
      rw [ht] at hfi
    · obtain ⟨_, h, -⟩ := bind_eq_pure.1 hfi; exact absurd h throw_ne_pure
    obtain ⟨hl, hsplit⟩ := split i hi qdc ht
    rw [orReject_some, pure_bind, hsplit, panicOf_eq_pure] at hfi
    refine ⟨qdc, hl, ?_⟩
    rw [List.getD_eq_getElem _ _ hqi, ← Option.some.inj hfi]

omit [Inhabited F] in
theorem permutation_round_ne_none (ζ : K) (proof : BatchProof C P F K) (doms : List (Coset G × Coset G)) (pc : C) :
    (permutation_round G ζ proof doms pc).run ≠ none := by
  unfold permutation_round
  refine bind_ne_none (mapM_ne_none _ _ fun ⟨⟨d, ov⟩, i⟩ _ => ?_) fun _ _ => pure_ne_none _
  dsimp only
  rw [show Coset.next_point G d.1 ζ = some (ζ * d.1.subgroup_generator) from rfl, orReject_some, pure_bind]
  split_ifs <;> first
    | exact bind_ne_none (throw_ne_none _) fun _ h => absurd h throw_ne_pure
    | exact pure_ne_none _

theorem preprocessed_round_ne_none (hmax : cfg.log_max_trace_height ≤ G.adicity)
    (hs : ShapeOk G cfg common sizing airs proof pvs sizes k) (ζ : K) {gl : GlobalPreprocessed C}
    (hgl : gl ∈ common.preprocessed) (hmti : ∀ inst ∈ gl.matrix_to_instance, inst < airs.length) :
    (preprocessed_round G airs ζ proof sizes ((List.range proof.degree_bits.length).map fun i =>
      (tdOf G cfg proof.degree_bits i, edOf G proof.degree_bits i)) gl).run ≠ none := by
  unfold preprocessed_round
  refine bind_ne_none (mapM_ne_none _ _ fun ⟨inst, mi⟩ hx => ?_) fun _ _ => pure_ne_none _
  have hinst : inst < airs.length :=
    hmti _ (List.mem_of_getElem? (List.mem_zipIdx_iff_getElem?.1 hx))
  have hi : inst < proof.degree_bits.length := hs.dbs_len ▸ hinst
  obtain ⟨hszi, hsz⟩ := hs.sizes_getD hi
  dsimp only
  rw [hszi, panicOf_some, pure_bind]
  split_ifs with h0
  · exact bind_ne_none (throw_ne_none _) fun _ h => absurd h throw_ne_pure
  rw [show proof.opened[inst]? = some (proof.opened.getD inst default) by simp [hs.opened_len ▸ hinst],
    panicOf_some, pure_bind]
  rcases hp : (proof.opened.getD inst default).preprocessed with _ | p
  · exact bind_ne_none (throw_ne_none _) fun _ h => absurd h throw_ne_pure
  rw [orReject_some, pure_bind, show proof.degree_bits[inst]? = some (proof.degree_bits.getD inst 0) by simp [hi],
    panicOf_some, pure_bind, show gl.instances[inst]? = some (gl.instances.getD inst none) by
      simp [hs.instances_len gl hgl ▸ hinst], panicOf_some, pure_bind]
  rcases hm : gl.instances.getD inst none with _ | pm
  · exact bind_ne_none (throw_ne_none _) fun _ h => absurd h throw_ne_pure
  rw [orReject_some, pure_bind]
  split_ifs with h1
  · exact bind_ne_none (throw_ne_none _) fun _ h => absurd h throw_ne_pure
  simp only [not_or, ne_eq, not_not] at h1
  have := hsz.hi
  rw [h1.2] at *
  refine bind_ne_none (panicOf_ne_none (natural_domain_ne_none G (by omega))) fun _ _ => ?_
  rw [List.getElem?_eq_getElem hinst, Option.map_some, panicOf_some, pure_bind]
  split_ifs
  · rcases p.next with _ | v
    · exact bind_ne_none (throw_ne_none _) fun _ h => absurd h throw_ne_pure
    · simp [Coset.next_point, hi]
  · exact pure_ne_none _

include hV in
/-- The claims at zeta never panic, once the shape checks accept.

This needs the largest height within the generator table, and each preprocessed matrix to name an instance. -/
theorem commitments_ne_none (hmax : cfg.log_max_trace_height ≤ G.adicity)
    (hs : ShapeOk G cfg common sizing airs proof pvs sizes k)
    (hmti : ∀ gl ∈ common.preprocessed, ∀ inst ∈ gl.matrix_to_instance, inst < airs.length) (ζ : K) :
    (commitments_with_opening_points G g cfg airs ζ proof common sizes).run ≠ none := by
  have hn : proof.opened.length = proof.degree_bits.length := by rw [hs.opened_len, hs.dbs_len]
  obtain ⟨hqn, hqs⟩ := quotient_domains_spec hV g hs
  unfold commitments_with_opening_points
  rw [trace_domains_eq hs (fun i hi => tdOf_ok hmax hs hi) (fun i hi => edOf_ok hmax hs hi), pure_bind,
    zip_range _ _ _ hn, zipIdx_range]
  have hrand : ∀ x ∈ (List.range proof.degree_bits.length).map (fun i =>
      ((tdOf G cfg proof.degree_bits i, edOf G proof.degree_bits i), proof.opened.getD i default)),
      cfg.zk = true → x.2.random.isSome := fun x hx hz => by
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hx
    rw [hs.random_open _ (getD_mem_of_lt (hn ▸ List.mem_range.1 hi)), hz]
  rcases hr : proof.random with _ | rc <;> dsimp only <;> try simp only [pure_bind]
  on_goal 2 =>
    have hz : cfg.zk = true := by simpa [hr] using hs.random.symm
    refine bind_ne_none (mapM_ne_none _ _ fun ⟨d, ov⟩ hx => ?_) fun _ _ => ?_
    · obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 (hrand _ hx hz)
      simp only at hv ⊢
      rw [hv, panicOf_some, pure_bind]; exact pure_ne_none _
  all_goals
    refine bind_ne_none (mapM_ne_none _ _ fun x hx => ?_) fun _ _ => ?_
    · obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hx
      have hi := List.mem_range.1 hi
      have hI := hs.inst_getD hi
      simp only
      rw [List.getElem?_eq_getElem (hs.dbs_len ▸ hi), Option.map_some, panicOf_some, pure_bind]
      split_ifs with hm
      · obtain ⟨v, hv, -⟩ : ∃ v, (proof.opened.getD i default).trace_next = some v ∧ _ := by
          simpa [hm] using hI.next
        simp only [Coset.next_point, orReject_some, pure_bind, hv, panicOf_some]
        exact pure_ne_none _
      · exact pure_ne_none _
    refine bind_ne_none hqn fun q hq => ?_
    obtain ⟨hql, hqi⟩ := hqs q hq
    refine bind_ne_none (mapM_ne_none _ _ fun doms hd => ?_) fun rz hrz => ?_
    · obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hd
      have hi' : i < proof.degree_bits.length := hql ▸ hi
      obtain ⟨qdc, hqdc, hqd⟩ := hqi i hi'
      rw [← List.getD_eq_getElem _ [] hi, hqd]
      refine mapM_ne_none _ _ fun d hd => panicOf_ne_none ?_
      obtain ⟨j, -, rfl⟩ := List.mem_map.1 hd
      have := (hs.sizes_getD hi').2.hi
      have := (hs.sizes_getD hi').2.lo
      rw [size_eq, ← pow_add]
      exact natural_domain_ne_none G (by simp only [chunk]; omega)
    have hrl : rz.length = proof.degree_bits.length := by
      rw [← hql]; simpa using ((mapM_eq_pure _ _ _).1 hrz).length_eq.symm
    refine bind_ne_none (mapM_ne_none _ _ fun ⟨doms, i⟩ hx => ?_) fun _ _ => ?_
    · have hi : i < proof.degree_bits.length :=
        hrl ▸ (List.getElem?_eq_some_iff.1 (List.mem_zipIdx_iff_getElem?.1 hx)).1
      simp only
      rw [show proof.opened[i]? = some (proof.opened.getD i default) by simp [hn ▸ hi], panicOf_some, pure_bind]
      split_ifs
      · exact bind_ne_none (throw_ne_none _) fun _ h => absurd h throw_ne_pure
      · exact pure_ne_none _
    rcases hc : common.preprocessed with _ | gl <;> rcases hp : proof.permutation with _ | pc
    all_goals first
      | exact pure_ne_none _
      | exact bind_ne_none (permutation_round_ne_none ζ proof _ pc) fun _ _ => pure_ne_none _
      | refine bind_ne_none (preprocessed_round_ne_none hmax hs ζ (by rw [hc]; rfl) (hmti gl (by rw [hc]; rfl)))
          fun _ _ => ?_
        first
          | exact pure_ne_none _
          | exact bind_ne_none (permutation_round_ne_none ζ proof _ pc) fun _ _ => pure_ne_none _

theorem commitments_qdoms (hmax : cfg.log_max_trace_height ≤ G.adicity)
    (hs : ShapeOk G cfg common sizing airs proof pvs sizes k) (ζ : K)
    {claims : List (p3_fri.verifier.mirror.Claim G C)} {qdoms : List (List (Coset G))} {idx : Option ℕ}
    (h : commitments_with_opening_points G g cfg airs ζ proof common sizes = pure (claims, qdoms, idx)) :
    quotient_domains G g cfg proof.degree_bits sizes ((List.range proof.degree_bits.length).map fun i =>
      (tdOf G cfg proof.degree_bits i, edOf G proof.degree_bits i)) = pure qdoms := by
  unfold commitments_with_opening_points at h
  rw [trace_domains_eq hs (fun i hi => tdOf_ok hmax hs hi) (fun i hi => edOf_ok hmax hs hi), pure_bind] at h
  rcases hr : proof.random with _ | rc <;> simp only [hr, pure_bind] at h
  on_goal 2 => obtain ⟨_, -, h⟩ := bind_eq_pure.1 h
  all_goals
    obtain ⟨_, -, h⟩ := bind_eq_pure.1 h
    obtain ⟨q, hq, h⟩ := bind_eq_pure.1 h
    obtain ⟨_, -, h⟩ := bind_eq_pure.1 h
    obtain ⟨_, -, h⟩ := bind_eq_pure.1 h
    rcases hc : common.preprocessed with _ | gl <;> rcases hp : proof.permutation with _ | pc <;>
      simp only [hc, hp] at h
    all_goals
      try obtain ⟨_, -, h⟩ := bind_eq_pure.1 h
      try obtain ⟨_, -, h⟩ := bind_eq_pure.1 h
      rw [hq, (Prod.mk.inj (Prod.mk.inj (pure_inj h)).2).1]

end claims

/-! ## The two grinds -/

section grinds

open Plonky3Lean.Proofs.Fri

theorem run_lift_bind_eq_none {ε α β : Type} {o : Option α} {k : α → ExceptT ε Option β} :
    (ExceptT.lift o >>= k).run = none ↔ o = none ∨ ∃ a, o = some a ∧ (k a).run = none := by
  rcases o with _ | a <;> simp [ExceptT.lift, ExceptT.run, bind, ExceptT.bind, ExceptT.mk, ExceptT.bindCont]

theorem run_throw_ne_none {ε α : Type} (e : ε) : (throw e : ExceptT ε Option α).run ≠ none := by
  intro h; cases h

theorem run_throw_bind_ne_none {ε α β : Type} (e : ε) (k : α → ExceptT ε Option β) :
    (throw e >>= k : ExceptT ε Option β).run ≠ none := by
  intro h; cases h

variable {sp : BatchSponge F K C Com S}

/-- The out-of-domain grind panics exactly at a difficulty the field cannot sample.

The difficulty b is unsafe when b > 0 and either b >= 64 or 2^b >= p. -/
theorem ood_phase_run_eq_none (shape : BatchShape) (s : S) (w : F) :
    (p3_batch_stark.verify.mirror.ood_phase sp shape s w).run = none ↔
      ¬ PowSafe sp.sponge.order shape.ood_pow_bits := by
  unfold p3_batch_stark.verify.mirror.ood_phase
  dsimp only
  by_cases h0 : shape.ood_pow_bits = 0 ∧ w ≠ 0
  · simp only [h0, ne_eq, not_false_eq_true, and_self, ↓reduceIte]
    exact iff_of_false (run_throw_bind_ne_none _ _) (by simp_all [PowSafe])
  simp only [h0, ↓reduceIte]
  show (ExceptT.lift _ >>= _).run = none ↔ _
  rw [run_lift_bind_eq_none, ← check_witness_eq_none sp.sponge s _ ((algebraMap F K) w)]
  refine or_iff_left_of_imp fun ⟨⟨ok, s'⟩, _, h⟩ => ?_
  cases ok <;> simp at h

/-- The lookup grind panics exactly when it is reached at a difficulty the field cannot sample.

It is reached when the batch has lookups and the proof carries a witness.

This holds when the lookups pass the challenge layout's width checks. -/
theorem lookup_phase_run_eq_none (shape : BatchShape) (s : S) {all : List (List (Lookup F))}
    (hlay : ∀ α β : K, lay_out_lookup_challenges 2 all α β ≠ none) (w : Option F) :
    (p3_batch_stark.verify.mirror.lookup_phase sp shape s all w).run = none ↔
      shape.has_lookups = true ∧ w.isSome ∧ ¬ PowSafe sp.sponge.order shape.lookup_pow_bits := by
  unfold p3_batch_stark.verify.mirror.lookup_phase
  dsimp only
  by_cases hl : shape.has_lookups = true
  · simp only [hl, not_true_eq_false, ↓reduceIte, true_and]
    rcases w with _ | w
    · exact iff_of_false (run_throw_ne_none _) (by simp)
    simp only [Option.isSome_some, true_and]
    by_cases h0 : shape.lookup_pow_bits = 0 ∧ w ≠ 0
    · simp only [h0, ne_eq, not_false_eq_true, and_self, ↓reduceIte]
      exact iff_of_false (run_throw_bind_ne_none _ _) (by simp_all [PowSafe])
    simp only [h0, ↓reduceIte]
    rw [run_lift_bind_eq_none, ← check_witness_eq_none sp.sponge s _ ((algebraMap F K) w)]
    refine or_iff_left_of_imp fun ⟨⟨ok, s'⟩, _, h⟩ => ?_
    cases ok
    · simp at h
    · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
      rw [run_lift_bind_eq_none] at h
      rcases h with h | ⟨_, -, h⟩
      · exact absurd h (hlay _ _)
      · cases h
  · simp only [hl, Bool.false_eq_true, not_false_eq_true, ↓reduceIte, false_and, iff_false]
    rcases w with _ | w
    · intro h; cases h
    · exact run_throw_ne_none _

theorem getD_map_nil {α β : Type} (f : List α → List β) (hf : f [] = []) (l : List (List α)) (i : ℕ) :
    (l.map f).getD i [] = f (l.getD i []) := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  rcases l[i]? with _ | x <;> simp [hf]

/-- The lookup phase gives every instance two challenges per lookup.

This holds when a batch without lookups declares none. -/
theorem lookup_phase_challenges (shape : BatchShape) {s s' : S} {all : List (List (Lookup F))} {w : Option F}
    {ch : List (List K)} (h : (p3_batch_stark.verify.mirror.lookup_phase sp shape s all w).run = some (.ok (ch, s')))
    (hk : shape.has_lookups = false → ∀ l ∈ all, l = []) (i : ℕ) :
    2 * (all.getD i []).length ≤ (ch.getD i []).length := by
  have h' : p3_batch_stark.verify.mirror.lookup_phase sp shape s all w = pure (ch, s') := h
  clear h
  unfold p3_batch_stark.verify.mirror.lookup_phase at h'
  have tne : ∀ {α : Type} (e : BatchTranscriptFailure) (a : α),
      (throw e : ExceptT BatchTranscriptFailure Option α) ≠ pure a := fun _ _ h => by cases h
  by_cases hl : shape.has_lookups = true
  · simp only [hl, not_true_eq_false, ↓reduceIte] at h'
    rcases w with _ | w
    · exact absurd h' (tne _ _)
    simp only at h'
    split_ifs at h' with h0
    · obtain ⟨_, h, -⟩ := Plonky3Lean.Proofs.Fri.exceptT_bind_eq_pure _ _ _ |>.1 h'
      exact absurd h (tne _ _)
    obtain ⟨⟨ok, s2⟩, -, h'⟩ := Plonky3Lean.Proofs.Fri.exceptT_bind_eq_pure _ _ _ |>.1 h'
    simp only at h'
    split_ifs at h'
    · obtain ⟨_, h, -⟩ := Plonky3Lean.Proofs.Fri.exceptT_bind_eq_pure _ _ _ |>.1 h'
      exact absurd h (tne _ _)
    obtain ⟨c, hc, h'⟩ := Plonky3Lean.Proofs.Fri.exceptT_bind_eq_pure _ _ _ |>.1 h'
    cases h'
    rcases hlay : lay_out_lookup_challenges 2 all (sp.sponge.sample s2).1
      (sp.sponge.sample (sp.sponge.sample s2).2).1 with _ | c' <;> rw [hlay] at hc <;> cases hc
    rcases hb : busIds all with _ | ⟨ids, st⟩
    · simp [lay_out_lookup_challenges, hb] at hlay
    rw [lay_out_eq hb, Option.some.injEq] at hlay
    subst hlay
    have hlen := (busIds_spec hb).1
    rw [getD_map_nil _ rfl, List.length_flatMap]
    have : (ids.getD i []).length = (all.getD i []).length := by
      have := congrArg (fun l : List ℕ => l.getD i 0) hlen
      simp only [List.getD_eq_getElem?_getD, List.getElem?_map] at this ⊢
      rcases hi : ids[i]? with _ | x <;> rcases ha : all[i]? with _ | y <;> simp_all
    simp only [List.getD_eq_getElem?_getD] at this
    simp [this, mul_comm]
  · simp only [hl, Bool.false_eq_true, not_false_eq_true, ↓reduceIte] at h'
    rcases w with _ | w
    · cases h'
      have := hk (by simpa using hl)
      rcases hi : all[i]? with _ | x
      · simp [List.getD_eq_getElem?_getD, hi]
      · simp [List.getD_eq_getElem?_getD, hi, this x (List.mem_of_getElem? hi)]
    · exact absurd h' (tne _ _)

theorem adapt_ne_none {ε ε' α : Type} {x : ExceptT ε Option α} (f : ε → ε') (h : x.run ≠ none) :
    (x.adapt f : ExceptT ε' Option α).run ≠ none := by
  change Option (Except ε α) at x
  rcases x with _ | (e | a)
  · exact absurd rfl h
  all_goals intro h'; cases h'

theorem adapt_eq_pure {ε ε' α : Type} {x : ExceptT ε Option α} {f : ε → ε'} {a : α}
    (h : (x.adapt f : ExceptT ε' Option α) = pure a) : x.run = some (.ok a) := by
  change Option (Except ε α) at x
  rcases x with _ | (e | b)
  all_goals cases h
  rfl

/-- The transcript never panics when both difficulties are safe and the lookups pass the layout's checks. -/
theorem replay_ne_none (shape : BatchShape) (proof : BatchProof C P F K) (pvs : List (List F))
    (common : CommonData C F) (hlay : ∀ α β : K, lay_out_lookup_challenges 2 common.lookups α β ≠ none)
    (hpowL : PowSafe sp.sponge.order shape.lookup_pow_bits) (hpowO : PowSafe sp.sponge.order shape.ood_pow_bits) :
    (replay sp shape proof pvs common).run ≠ none := by
  unfold replay
  dsimp only
  refine bind_ne_none (adapt_ne_none _ fun h => ?_) fun _ _ => ?_
  · exact ((lookup_phase_run_eq_none shape _ hlay _).1 h).2.2 hpowL
  exact bind_ne_none (adapt_ne_none _ fun h => (ood_phase_run_eq_none shape _ _).1 h hpowO)
    fun _ _ => pure_ne_none _

/-- An accepted transcript drew its lookup challenges in the lookup phase. -/
theorem replay_lookup {shape : BatchShape} {proof : BatchProof C P F K} {pvs : List (List F)}
    {common : CommonData C F} {ch : List (List K)} {α ζ : K} {s : S}
    (h : replay sp shape proof pvs common = pure (ch, α, ζ, s)) :
    ∃ s1, (p3_batch_stark.verify.mirror.lookup_phase sp shape (preLookupState sp shape proof pvs common)
      common.lookups proof.lookup_pow_witness).run = some (.ok (ch, s1)) := by
  unfold replay at h
  dsimp only at h
  obtain ⟨⟨ch', s1⟩, h1, h⟩ := bind_eq_pure.1 h
  obtain ⟨_, -, h⟩ := bind_eq_pure.1 h
  obtain rfl : ch' = ch := (Prod.mk.inj (pure_inj h)).1
  exact ⟨s1, adapt_eq_pure h1⟩

end grinds

/-! ## One instance at zeta -/

section zeta

variable (G : Gen K)

/-- The check at zeta never panics on openings of the AIR's widths, with lookups laid out. -/
theorem verify_constraints_with_lookups_ne_none (hV : GenValid G) (h2 : (2 : K) ≠ 0) {air : Air F}
    (hb : air.public_boundary_io = []) {ch : List K} {lookups : List (Lookup F)} (hL : LaidOut air ch lookups)
    (tl tn pl pn ml mn per : List K) (pv : List F) (T : K) (c : Coset G) (ζ α q : K)
    (hs : WindowShapes air ⟨tl, tn⟩ ⟨pl, pn⟩ (pv.map (algebraMap F K)) per)
    (hperm : lookups ≠ [] → lookups.length < ml.length ∧ 0 < mn.length) :
    verify_constraints_with_lookups G air tl tn pl pn ml mn ch (if lookups = [] then [] else [T]) per lookups pv
      c ζ α q ≠ none := by
  unfold verify_constraints_with_lookups
  simp only [hb, ne_eq, not_true_eq_false, ↓reduceIte, Option.pure_def, Option.bind_eq_bind]
  by_cases hz : Coset.vanishing_poly_at_point G c ζ = 0
  · simp [hz]
  have hζ : ¬ InCoset c.shift c.subgroup_generator c.log_size ζ :=
    fun h => hz ((vanishing_poly_at_point_eq_zero G hV c ζ).2 h)
  obtain ⟨sels, hsel⟩ : ∃ sels, Coset.selectors_at_point G c ζ = some sels :=
    ⟨_, selectors_at_point_some G hV h2 c ζ hζ⟩
  have hfold := eval_air_and_lookups_verifier (holds_windowEnv hs sels.is_first_row sels.is_last_row
    sels.is_transition) α hL ⟨ml, mn⟩ hperm T
  simp only [hz, ↓reduceIte, hsel, Option.bind_some]
  rw [hfold, Option.bind_some]
  split_ifs <;> simp

theorem recompose_permutation_some {D : ℕ} (B : Module.Basis (Fin D) F K) (hD : 0 < D) (aux : ℕ)
    (flat : List K) : ∃ v, recompose_permutation B aux flat = some v ∧
      v.length = if aux = 0 then 0 else flat.length / D := by
  unfold recompose_permutation
  split_ifs with h
  · exact ⟨[], rfl, rfl⟩
  refine ⟨((List.range (flat.length / D)).map fun j => (flat.drop (j * D)).take D).map
    (fun (ch : List K) => ∑ d : Fin D, ch.getD d 0 * B d), ?_, by simp⟩
  simp only [chunks_exact, hD.ne', ↓reduceIte, Option.bind_eq_bind, Option.bind_some]
  refine mapM_some_of _ _ (fun (ch : List K) => ∑ d : Fin D, ch.getD d 0 * B d) fun ch hch => ?_
  obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hch
  have hj' : (j + 1) * D ≤ flat.length := (Nat.le_div_iff_mul_le hD).1 (List.mem_range.1 hj)
  have hlen : ((flat.drop (j * D)).take D).length = D := by
    simp only [List.length_take, List.length_drop]; rw [Nat.add_mul, one_mul] at hj'; omega
  simp [from_ext_basis_coefficients, hlen]

/-- Instance i's check at zeta never panics, under these conditions:

- the AIR binds its public values by constraints, and its lookups are laid out
- the openings passed the shape checks, and the common data's preprocessed width is the AIR's
- the chunk domains are the chunks of a quotient coset, one per opened chunk
- the AIR declares as many periodic columns as it lists
- the configured extension degree is the basis's. -/
theorem check_at_zeta_ne_none {D : ℕ} (hV : GenValid G) (hN : GenNested G) (h2 : (2 : K) ≠ 0)
    (B : Module.Basis (Fin D) F K) {cfg : Config} (hD : cfg.D = D) (hD0 : 0 < D) {ba : BatchAir F}
    (hb : ba.air.public_boundary_io = []) (i : ℕ) {ov : Opened K} {sz : Sizes} {lookups : List (Lookup F)}
    {t : Option K} {ch : List K} {pv : List F} (hI : InstOk cfg ba pv ov sz lookups t)
    (hL : LaidOut ba.air ch lookups) (hw : sz.preprocessed_width = ba.air.preprocessed_width)
    (hnpc : ba.air.num_periodic_columns = ba.air.periodic_columns.length) (c : Coset G)
    (qd : Coset G) {l : ℕ} (hl : l ≤ qd.log_size) (hql : ov.quotient_chunks.length = 2 ^ l) (ζ α : K) :
    (check_at_zeta G B ba i ov sz.preprocessed_width lookups t ch pv c
      ((List.range (2 ^ l)).map (chunk G hV qd l)) ζ α).run ≠ none := by
  unfold check_at_zeta
  rw [recompose_eq hV qd l B hl ov.quotient_chunks hql
    (fun j => ∑ d : Fin D, (ov.quotient_chunks.getD j []).getD d 0 * B d) (fun j hj => by
      have := hI.chunks_dim _ (List.getElem_mem (hql ▸ hj))
      simp only [from_ext_basis_coefficients, this, hD, ↓reduceIte, List.getD_eq_getElem _ _ (hql ▸ hj)]) ζ,
    panicOf_some, pure_bind]
  obtain ⟨ml, hml, hmll⟩ := recompose_permutation_some B hD0
    (if lookups.isEmpty then 0 else lookups.length + 1) ov.permutation_local
  obtain ⟨mn, hmn, hmnl⟩ := recompose_permutation_some B hD0
    (if lookups.isEmpty then 0 else lookups.length + 1) ov.permutation_next
  dsimp only
  rw [hml, panicOf_some, pure_bind, hmn, panicOf_some, pure_bind]
  simp only [size_eq]
  rcases hp : PeriodicColumns.new (ba.air.periodic_columns.map (·.map (algebraMap F K))) (2 ^ c.log_size)
    with e | pc
  · exact bind_ne_none (throw_ne_none _) fun _ h => absurd h throw_ne_pure
  obtain ⟨rfl, hok⟩ := new_ok_eq hp
  simp only [pure_bind]
  rw [periodic_at G hV hN h2 c _ hok ζ, panicOf_some, pure_bind]
  refine bind_ne_none ?_ fun r _ => ?_
  · obtain ⟨T, hT⟩ : ∃ T, t.toList = if lookups = [] then [] else [T] := by
      have := hI.terminal
      rcases t with _ | T
      · exact ⟨0, by simp_all⟩
      · exact ⟨T, by simp_all⟩
    rw [hT]
    have hne := verify_constraints_with_lookups_ne_none G hV h2 hb hL ov.trace_local
      (ov.trace_next.getD (List.replicate ba.air.width 0)) ((ov.preprocessed.map (·.current)).getD [])
      ((ov.preprocessed.bind (·.next)).getD (List.replicate sz.preprocessed_width 0)) ml mn
      ((ba.air.periodic_columns.map (·.map (algebraMap F K))).map fun col =>
        (periodicPoly c.shift c.subgroup_generator c.log_size col).eval ζ) pv T c ζ α
      (∑ j ∈ Finset.range (2 ^ l), (chunkL hV qd l j).eval ζ *
        ∑ d : Fin D, (ov.quotient_chunks.getD j []).getD d 0 * B d) ?shapes ?perm
    · obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.1 hne
      rw [hv]; exact pure_ne_none _
    case shapes =>
      have hn := hI.next
      have hpre := hI.pre
      refine ⟨hI.local_len, ?_, ?_, ?_, by simp [hI.pv_len], by simp [hnpc]⟩
      · rcases hm : ba.opens_main_next <;> simp only [hm, Bool.false_eq_true, ↓reduceIte] at hn
        · simp [hn]
        · obtain ⟨v, hv, hvl⟩ := hn; simp [hv, hvl]
      · rcases hp' : ov.preprocessed with _ | p <;> simp only [hp'] at hpre ⊢
        · simp [← hw, hpre]
        · simp [← hw, hpre.2.1]
      · rcases hp' : ov.preprocessed with _ | p <;> simp only [hp'] at hpre ⊢
        · simp [← hw]
        · obtain ⟨-, -, h3, h4⟩ := hpre
          rcases hnx : p.next with _ | v <;> rcases ho : ba.opens_preprocessed_next <;> simp_all
    case perm =>
      intro hne
      have h1 : lookups.isEmpty = false := by simpa using hne
      simp only [h1, Bool.false_eq_true, ↓reduceIte, Nat.add_one_ne_zero] at hmll hmnl
      rw [hmll, hmnl, hI.perm_local, hI.perm_next]
      simp only [h1, Bool.false_eq_true, ↓reduceIte, hD, Nat.mul_div_cancel _ hD0]
      omega
  · rcases r with e | ⟨⟩
    · exact throw_ne_none _
    · exact pure_ne_none _

end zeta

/-! ## Every instance at zeta -/

/-- The common data's lookups as the check at zeta reads them.

Lookup j of each instance owns slot j, and every lookup fits its instance's AIR. -/
def LookupsFit (airs : List (BatchAir F)) (common : CommonData C F) : Prop :=
  ∀ i (hi : i < airs.length), (∀ j (h : j < (common.lookups.getD i []).length),
    ((common.lookups.getD i [])[j]).column = j) ∧ ∀ l ∈ common.lookups.getD i [], Fits airs[i].air l

section all

variable {G : Gen K} (hV : GenValid G) {cfg : Config} {common : CommonData C F}
  {sizing : ℕ → AirLayout → ℕ → Option ℕ} {airs : List (BatchAir F)} {proof : BatchProof C P F K}
  {pvs : List (List F)} {sizes : List Sizes} {k : ℕ}

theorem check_all_ne_none {D : ℕ} (hN : GenNested G) (h2 : (2 : K) ≠ 0) (B : Module.Basis (Fin D) F K)
    (hD : cfg.D = D) (hmax : cfg.log_max_trace_height ≤ G.adicity)
    (hs : ShapeOk G cfg common sizing airs proof pvs sizes k)
    (hb : ∀ ba ∈ airs, ba.air.public_boundary_io = [])
    (hnpc : ∀ ba ∈ airs, ba.air.num_periodic_columns = ba.air.periodic_columns.length)
    (hcw : ∀ i (hi : i < airs.length) w, preprocessed_width common i = pure w → w = airs[i].air.preprocessed_width)
    (hfit : LookupsFit airs common) {ch : List (List K)} (hch : ch.length = airs.length)
    (hchl : ∀ i, 2 * (common.lookups.getD i []).length ≤ (ch.getD i []).length)
    {qdoms : List (List (Coset G))} (hql : qdoms.length = airs.length)
    (hqi : ∀ i < proof.degree_bits.length, ∃ qdc : Coset G,
      qdc.log_size = proof.degree_bits.getD i 0 + (sizes.getD i default).log_num_quotient_chunks ∧
      qdoms.getD i [] = (List.range (2 ^ ((sizes.getD i default).log_num_quotient_chunks + cfg.zk.toNat))).map
        (chunk G hV qdc ((sizes.getD i default).log_num_quotient_chunks + cfg.zk.toNat))) (ζ α : K) :
    (check_all_at_zeta G B cfg airs proof pvs common sizes ch qdoms ζ α).run ≠ none := by
  have hsl := hs.sizes_length
  have hD0 : 0 < D := by
    rcases Nat.eq_zero_or_pos D with h | h
    · subst h; exact absurd (B.index_nonempty) (by simp)
    · exact h
  unfold check_all_at_zeta
  refine bind_ne_none (mapM_ne_none _ _ fun sz hsz => ?_) fun tds htds => ?_
  · obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hsz
    have hi' : i < proof.degree_bits.length := by rw [hs.dbs_len, ← hsl]; exact hi
    obtain ⟨-, hS⟩ := hs.sizes_getD hi'
    rw [getElem_eq_getD hi, hS.ext, Nat.pow_div (by have := hS.lo; omega) (by norm_num)]
    exact panicOf_ne_none (natural_domain_ne_none G (by have := hS.hi; omega))
  have htl : tds.length = airs.length := by
    rw [← hsl]; simpa using ((mapM_eq_pure _ _ _).1 htds).length_eq.symm
  refine forM_ne_none _ _ fun ⟨ba, i⟩ hx => ?_
  obtain ⟨hi, rfl⟩ : ∃ hi : i < airs.length, airs[i] = ba :=
    List.getElem?_eq_some_iff.1 (List.mem_zipIdx_iff_getElem?.1 hx)
  have hi' : i < proof.degree_bits.length := hs.dbs_len ▸ hi
  have get : ∀ {α : Type} [Inhabited α] (l : List α), l.length = airs.length →
      l[i]? = some (l.getD i default) := fun l hl => by simp [hl ▸ hi]
  simp only [get _ hs.opened_len, get _ hsl, panicOf_some, pure_bind,
    show common.lookups[i]? = some (common.lookups.getD i []) by simp [hs.lookups_len ▸ hi],
    show proof.lookup_terminals[i]? = some (proof.lookup_terminals.getD i none) by
      simp [hs.terminals_len ▸ hi],
    show ch[i]? = some (ch.getD i []) by simp [hch ▸ hi], show pvs[i]? = some (pvs.getD i []) by
      simp [hs.pvs_len ▸ hi], show qdoms[i]? = some (qdoms.getD i []) by simp [hql ▸ hi],
    List.getElem?_eq_getElem (htl ▸ hi : i < tds.length)]
  obtain ⟨qdc, hqdc, hqd⟩ := hqi i hi'
  obtain ⟨-, hS⟩ := hs.sizes_getD hi'
  have hI := hs.inst_getD hi'
  have := hS.lo
  rw [hqd]
  refine check_at_zeta_ne_none G hV hN h2 B hD hD0 (hb _ (List.getElem_mem hi)) i hI
    ⟨(hfit i hi).1, (hfit i hi).2, hchl i⟩ (hcw i hi _ hS.width) (hnpc _ (List.getElem_mem hi)) _ qdc
    (by omega) (by rw [hI.chunks_len, hS.chunks]) ζ α

end all

/-! ## The whole verifier -/

open Plonky3Lean.Proofs.Fri in
/-- The batch verifier never panics, on any proof, under these conditions:

- every AIR binds its public values by constraints, and declares as many periodic columns as it lists
- the largest trace height lies within the generator table
- the quotient sizing returns
- the common data matches the AIRs: preprocessed widths, lookup slots and widths, matrix instances
- the lookups pass the challenge layout's width checks
- both grinding difficulties are zero, or b < 64 with 2^b < p
- the opening argument never panics
- the configured extension degree is the basis's. -/
theorem verify_ne_none {D : ℕ} (G : Gen K) (hV : GenValid G) (hN : GenNested G) (h2 : (2 : K) ≠ 0) (g : K)
    (B : Module.Basis (Fin D) F K) (cfg : Config) (airs : List (BatchAir F))
    (sizing : ℕ → AirLayout → ℕ → Option ℕ) (sp : BatchSponge F K C Com S)
    (pcs : List (p3_fri.verifier.mirror.Claim G C) → Option ℕ → S → Option (Except PE Unit))
    (proof : BatchProof C P F K) (pvs : List (List F)) (common : CommonData C F)
    (hb : ∀ ba ∈ airs, ba.air.public_boundary_io = [])
    (hnpc : ∀ ba ∈ airs, ba.air.num_periodic_columns = ba.air.periodic_columns.length)
    (hmax : cfg.log_max_trace_height ≤ G.adicity) (hsizing : ∀ i l n, ∃ r, sizing i l n = some r)
    (hcw : ∀ i (hi : i < airs.length) w, preprocessed_width common i = pure w → w = airs[i].air.preprocessed_width)
    (hfit : LookupsFit airs common) (hlay : ∀ α β : K, lay_out_lookup_challenges 2 common.lookups α β ≠ none)
    (hmti : ∀ gl ∈ common.preprocessed, ∀ inst ∈ gl.matrix_to_instance, inst < airs.length)
    (hpowL : PowSafe sp.sponge.order cfg.lookup_pow_bits) (hpowO : PowSafe sp.sponge.order cfg.ood_pow_bits)
    (hpcs : ∀ cl idx st, pcs cl idx st ≠ none) (hD : cfg.D = D) :
    verify_batch G g B cfg airs sizing sp pcs proof pvs common ≠ none := by
  have hany : airs.any (fun ba => !ba.air.public_boundary_io.isEmpty) = false := by
    simpa using fun ba h => hb ba h
  unfold verify_batch
  simp only [hany, Bool.false_eq_true, ↓reduceIte]
  refine bind_ne_none (check_shape_ne_none G cfg common sizing hmax hsizing airs proof pvs)
    fun ⟨sizes, k⟩ hsh => ?_
  have hs := check_shape_pure G cfg common sizing hsh
  refine bind_ne_none (replay_ne_none _ proof pvs common hlay hpowL hpowO) fun ⟨ch, α, ζ, s⟩ hrep => ?_
  obtain ⟨s1, hlk⟩ := replay_lookup hrep
  refine bind_ne_none (commitments_ne_none hV g hmax hs hmti ζ) fun ⟨claims, qdoms, idx⟩ hcl => ?_
  obtain ⟨hql, hqi⟩ := (quotient_domains_spec hV g hs).2 qdoms (commitments_qdoms g hmax hs ζ hcl)
  refine bind_ne_none (panicOf_ne_none (hpcs _ _ _)) fun r _ => ?_
  rcases r with e | ⟨⟩
  · exact bind_ne_none (throw_ne_none _) fun _ h => absurd h throw_ne_pure
  refine bind_ne_none (check_all_ne_none hV hN h2 B hD hmax hs hb hnpc hcw hfit
    (by rw [lookup_phase_length hlk, hs.lookups_len]) (lookup_phase_challenges _ hlk fun hk l hl => ?_ ) 
    (by rw [hql, hs.dbs_len]) (fun i hi => hqi i hi) ζ α) fun _ _ => ?_
  · have hk0 : k = 0 := by simpa [shapeOf, BatchShape.has_lookups] using hk
    rw [hs.count] at hk0
    have := List.length_eq_zero_iff.1 hk0
    simpa using List.filter_eq_nil_iff.1 this l hl
  split_ifs
  · exact throw_ne_none _
  · exact pure_ne_none _

/-! ## Panic witnesses at the pin -/

theorem adapt_none_bind {ε α β : Type} {x : ExceptT ε Option α} (f : ε → Error) (k : α → M β)
    (h : x.run = none) : ((x.adapt f : M α) >>= k).run = none := by
  change Option (Except ε α) at x
  subst h
  rfl

/-- An AIR with boundary cells panics the verifier on every proof. -/
theorem verify_boundary_none {D : ℕ} (G : Gen K) (g : K) (B : Module.Basis (Fin D) F K) (cfg : Config)
    (airs : List (BatchAir F)) (sizing : ℕ → AirLayout → ℕ → Option ℕ) (sp : BatchSponge F K C Com S)
    (pcs : List (p3_fri.verifier.mirror.Claim G C) → Option ℕ → S → Option (Except PE Unit))
    (proof : BatchProof C P F K) (pvs : List (List F)) (common : CommonData C F)
    (hb : ∃ ba ∈ airs, ba.air.public_boundary_io ≠ []) :
    verify_batch G g B cfg airs sizing sp pcs proof pvs common = none := by
  have hany : airs.any (fun ba => !ba.air.public_boundary_io.isEmpty) = true := by
    obtain ⟨ba, h1, h2⟩ := hb
    exact List.any_eq_true.2 ⟨ba, h1, by simpa using h2⟩
  unfold verify_batch
  simp only [hany, ↓reduceIte]
  rfl

open Plonky3Lean.Proofs.Fri in
/-- At the pin, a proof that reaches the out-of-domain grind at an unsafe difficulty panics the verifier.

It reaches the grind once the shape checks and the lookup phase accept.

The difficulty b is unsafe when b > 0 and either b >= 64 or 2^b >= p. -/
theorem verify_ood_none {D : ℕ} (G : Gen K) (g : K) (B : Module.Basis (Fin D) F K) (cfg : Config)
    (airs : List (BatchAir F)) (sizing : ℕ → AirLayout → ℕ → Option ℕ) (sp : BatchSponge F K C Com S)
    (pcs : List (p3_fri.verifier.mirror.Claim G C) → Option ℕ → S → Option (Except PE Unit))
    (proof : BatchProof C P F K) (pvs : List (List F)) (common : CommonData C F)
    (hb : ∀ ba ∈ airs, ba.air.public_boundary_io = []) {sizes : List Sizes} {k : ℕ}
    (hshape : check_shape G cfg airs sizing proof pvs common = pure (sizes, k)) {ch : List (List K)} {s1 : S}
    (hlk : (p3_batch_stark.verify.mirror.lookup_phase sp (shapeOf cfg airs common sizes k)
      (preLookupState sp (shapeOf cfg airs common sizes k) proof pvs common) common.lookups
      proof.lookup_pow_witness).run = some (.ok (ch, s1)))
    (hpow : ¬ PowSafe sp.sponge.order cfg.ood_pow_bits) :
    verify_batch G g B cfg airs sizing sp pcs proof pvs common = none := by
  have hany : airs.any (fun ba => !ba.air.public_boundary_io.isEmpty) = false := by
    simpa using fun ba h => hb ba h
  unfold verify_batch
  simp only [hany, Bool.false_eq_true, ↓reduceIte, hshape, pure_bind]
  unfold preLookupState at hlk
  unfold replay
  dsimp only
  rw [adapt_ok _ hlk, pure_bind]
  dsimp only
  simp only [bind_assoc]
  exact adapt_none_bind _ _ ((ood_phase_run_eq_none _ _ _).2 hpow)

open Plonky3Lean.Proofs.Fri in
/-- At the pin, a proof that reaches the lookup grind at an unsafe difficulty panics the verifier.

It reaches the grind once the shape checks accept.

That needs an instance with lookups, and a witness in the proof. -/
theorem verify_lookup_none {D : ℕ} (G : Gen K) (g : K) (B : Module.Basis (Fin D) F K) (cfg : Config)
    (airs : List (BatchAir F)) (sizing : ℕ → AirLayout → ℕ → Option ℕ) (sp : BatchSponge F K C Com S)
    (pcs : List (p3_fri.verifier.mirror.Claim G C) → Option ℕ → S → Option (Except PE Unit))
    (proof : BatchProof C P F K) (pvs : List (List F)) (common : CommonData C F)
    (hb : ∀ ba ∈ airs, ba.air.public_boundary_io = []) {sizes : List Sizes} {k : ℕ}
    (hshape : check_shape G cfg airs sizing proof pvs common = pure (sizes, k))
    (hlay : ∀ α β : K, lay_out_lookup_challenges 2 common.lookups α β ≠ none) (hk : 0 < k)
    (hw : proof.lookup_pow_witness.isSome) (hpow : ¬ PowSafe sp.sponge.order cfg.lookup_pow_bits) :
    verify_batch G g B cfg airs sizing sp pcs proof pvs common = none := by
  have hany : airs.any (fun ba => !ba.air.public_boundary_io.isEmpty) = false := by
    simpa using fun ba h => hb ba h
  unfold verify_batch
  simp only [hany, Bool.false_eq_true, ↓reduceIte, hshape, pure_bind]
  unfold replay
  dsimp only
  simp only [bind_assoc]
  refine adapt_none_bind _ _ ((lookup_phase_run_eq_none _ _ hlay _).2 ⟨?_, hw, hpow⟩)
  simpa [shapeOf, BatchShape.has_lookups] using hk

end Plonky3Lean.Proofs.BatchStark.EndToEnd
