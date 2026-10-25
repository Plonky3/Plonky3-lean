module

public import Plonky3Lean.Proofs.UniStark.ZkCompleteness
public import Plonky3Lean.Proofs.UniStark.Verifier
public import Plonky3Lean.Proofs.Fri.MerklePcs
public import Plonky3Lean.Proofs.Fri.HidingPcs
public import Plonky3Lean.Proofs.Commit.PeriodicBatch
public import Plonky3Lean.Proofs.Commit.PeriodicTable

@[expose] public section

/-!
# The full verifier

The verifier runs its checks in Rust's order, then the opening argument, then the check at zeta.

- When every step accepts, the verifier accepts.
- The domains it builds are the trace subgroup, the quotient coset and its chunks.
- Every randomized chunk domain is the trace subgroup itself.
-/

set_option linter.unusedSectionVars false

namespace Plonky3Lean.Proofs.UniStark

open Polynomial
open p3_air.air.mirror p3_uni_stark.verifier.mirror p3_uni_stark.prover.mirror
open p3_uni_stark.verify.mirror p3_uni_stark.transcript.mirror
open p3_commit.domain.mirror p3_commit.periodic.mirror p3_field.coset.mirror p3_dft.mirror
open Plonky3Lean.Proofs.Commit Plonky3Lean.Proofs.Dft

variable {F K : Type} [Field F] [DecidableEq F] [Field K] [DecidableEq K] [Algebra F K]

/-! ## Domains -/

theorem coset_ext {G : Gen K} {c d : Coset G} (h1 : c.shift = d.shift) (h2 : c.log_size = d.log_size) :
    c = d := by
  cases c; cases d; cases h1; cases h2; rfl

/-- The scheme's domain of order 2^k is the subgroup of that order. -/
theorem natural_domain_pow (G : Gen K) (c : Coset G) (hs : c.shift = 1) {k : ℕ} (hk : c.log_size = k) :
    natural_domain_for_degree G (2 ^ k) = some c := by
  subst hk
  simp only [natural_domain_for_degree, log2Strict_pow, Option.bind_eq_bind, Option.bind_some,
    TwoAdicMultiplicativeCoset.new, ne_eq, one_ne_zero, not_false_eq_true, c.log_size_le, and_self,
    dite_true, Option.some.injEq]
  exact coset_ext hs.symm rfl

theorem log2Ceil_pow (n : ℕ) : log2Ceil (2 ^ n) = n :=
  le_antisymm ((log2Ceil_le_iff _ _).2 le_rfl)
    ((Nat.pow_le_pow_iff_right (by norm_num)).1 (le_pow_log2Ceil _))

/-- The quotient coset: the trace's shift times g, of the requested order. -/
theorem try_create_disjoint_domain_pow (G : Gen K) (td qd : Coset G) (g : K) (hs : qd.shift = td.shift * g)
    {n : ℕ} (hn : qd.log_size = n) : Coset.try_create_disjoint_domain G td g (2 ^ n) = some qd := by
  subst hn
  simp only [Coset.try_create_disjoint_domain, TwoAdicMultiplicativeCoset.new, log2Ceil_pow, ← hs,
    qd.shift_ne_zero, ne_eq, not_false_eq_true, qd.log_size_le, and_self, dite_true]

/-- Each randomized chunk domain is the trace subgroup, when the chunks number 2^(l + z) and z <= b. -/
theorem randomized_domains (G : Gen K) (hV : GenValid G) (td qd : Coset G) (hs : td.shift = 1)
    {b l z : ℕ} (htd : td.log_size = b) (hqd : qd.log_size = b + l) (hz : z ≤ b) :
    ((List.range (2 ^ (l + z))).map (chunk G hV qd (l + z))).mapM
      (fun d => natural_domain_for_degree G (2 ^ d.log_size * 2 ^ z)) =
      some (List.replicate (2 ^ (l + z)) td) := by
  rw [mapM_some_of _ _ (fun _ => td) fun d hd => ?_, List.map_const', List.length_map, List.length_range]
  obtain ⟨i, -, rfl⟩ := List.mem_map.1 hd
  rw [← pow_add]
  exact natural_domain_pow G td hs (by simp only [chunk, hqd]; omega)

/-! ## Acceptance -/

variable {C Com S P PE : Type}

/-- The claims step accepts once its checks pass, with the periodic values and the claims at zeta. -/
theorem prepare_opening_claims_ok (G : Gen K) (air : Air F) (omn : Bool) (proof : Proof C P F K)
    (pre : Option (C × PreprocessedOpening K)) (td c : Coset G) (rqd : List (Coset G)) {ζ : K}
    (hood : check_ood_point G c ζ = .ok ())
    (hper : PeriodicColumns.new (air.periodic_columns.map (·.map (algebraMap F K))) (2 ^ c.log_size) =
      .ok ⟨air.periodic_columns.map (·.map (algebraMap F K)), 2 ^ c.log_size⟩)
    {periodic : List K}
    (hpv : Coset.evaluate_periodic_columns_at G c (air.periodic_columns.map (·.map (algebraMap F K)))
      (2 ^ c.log_size) ζ = some periodic)
    (hrand : proof.random_commitment.isSome → proof.random.isSome)
    {tn : List K} (htn : (if omn then proof.trace_next else some []) = some tn)
    (hlen : rqd.length = proof.quotient_chunks.length) :
    prepare_opening_claims G air omn proof pre td c rqd ζ =
      some (.ok (periodic, opening_claims G omn proof proof.random tn pre td rqd ζ
        (ζ * c.subgroup_generator))) := by
  have hr : ¬ (proof.random_commitment.isSome = true ∧ proof.random.isNone = true) := by
    rintro ⟨h1, h2⟩; simp_all
  unfold prepare_opening_claims
  simp only [hood, size_eq, hper, hpv, Coset.next_point, hr, ↓reduceIte, hlen, ne_eq,
    not_true_eq_false, Option.pure_def, Option.bind_eq_bind, Option.bind_some]
  rcases omn <;> simp_all

/-- The verifier accepts when every step accepts.

Write b for the proof's degree bits, z for the zero-knowledge bit and L for the quotient sizing.

- The trace domain is the subgroup of order 2^b, and the base domain the subgroup of order 2^(b - z).
- The quotient coset has shift g and order 2^(b + L), split into 2^(L + z) chunks.
- The height, the preprocessed trace, the key's height and the shape checks accept.
- Both transcript phases accept and draw alpha and zeta.
- Zeta lies off the base domain, and the periodic columns screen and evaluate.
- The opening argument accepts the claims, with every chunk on the trace subgroup.
- The chunks recombine to a value the check at zeta accepts. -/
theorem verify_accepts {D : ℕ} (G : Gen K) (hV : GenValid G) (g : K) (B : Module.Basis (Fin D) F K)
    (cfg : Config) (air : Air F) (omn opn : Bool) (sp : StarkSponge F K C Com S)
    (pcs : List (p3_fri.verifier.mirror.Claim G C) → Option ℕ → S → Option (Except PE Unit))
    (proof : Proof C P F K) (pv : List F) (vk : Option (PreprocessedVerifierKey C)) (s0 : S)
    (hb : air.public_boundary_io = []) {lq : ℕ} (td c qd : Coset G)
    (htd : td.shift = 1 ∧ td.log_size = proof.degree_bits)
    (hc : c.shift = 1 ∧ c.log_size = proof.degree_bits - cfg.zk.toNat)
    (hqd : qd.shift = g ∧ qd.log_size = proof.degree_bits + lq)
    (hlo : cfg.zk.toNat + cfg.log_min_trace_height ≤ proof.degree_bits)
    (hhi : proof.degree_bits ≤ cfg.log_max_trace_height) (hW : proof.degree_bits + lq < WORD_BITS)
    {pw : ℕ} {pre : Option (C × PreprocessedOpening K)}
    (hpp : process_preprocessed_trace air.preprocessed_width opn proof.preprocessed vk = .ok (pw, pre))
    (hkey : ∀ key ∈ vk, 0 < pw → key.degree_bits = proof.degree_bits)
    (hlq : get_log_num_quotient_chunks_for_domain air
      { preprocessed_width := pw, main_width := air.width, num_public_values := air.num_public_values,
        num_periodic_columns := air.num_periodic_columns } (2 ^ c.log_size) cfg.zk.toNat = .ok lq)
    (hshape : check_shape air omn cfg.zk cfg.D (2 ^ (lq + cfg.zk.toNat)) cfg.ood_pow_bits pv
      proof.trace_local proof.trace_next proof.quotient_chunks proof.random
      proof.random_commitment.isSome proof.ood_pow_witness = .ok ())
    {α ζ : K} {s1 s2 : S}
    (hα : constraint_phase sp pw s0 proof.trace_commitment (pre.map (·.1)) pv = .ok (α, s1))
    (hζ : (ood_phase sp cfg.zk cfg.ood_pow_bits s1 proof.quotient_commitment proof.random_commitment
      proof.ood_pow_witness).run = some (.ok (ζ, s2)))
    (hood : check_ood_point G c ζ = .ok ())
    {periodic : List K}
    (hper : PeriodicColumns.new (air.periodic_columns.map (·.map (algebraMap F K))) (2 ^ c.log_size) =
      .ok ⟨air.periodic_columns.map (·.map (algebraMap F K)), 2 ^ c.log_size⟩)
    (hpv : Coset.evaluate_periodic_columns_at G c (air.periodic_columns.map (·.map (algebraMap F K)))
      (2 ^ c.log_size) ζ = some periodic)
    {tn : List K} (htn : (if omn then proof.trace_next else some []) = some tn)
    (hpcs : pcs (opening_claims G omn proof proof.random tn pre td
      (List.replicate (2 ^ (lq + cfg.zk.toNat)) td) ζ (ζ * c.subgroup_generator))
      (pre.map fun _ => cfg.zk.toNat + 2) s2 = some (.ok ()))
    {q : K}
    (hrec : recompose_quotient_from_chunks G B
      ((List.range (2 ^ (lq + cfg.zk.toNat))).map (chunk G hV qd (lq + cfg.zk.toNat)))
      proof.quotient_chunks ζ = some q)
    (hvc : verify_constraints G air proof.trace_local (proof.trace_next.getD (List.replicate air.width 0))
      (proof.preprocessed.map (·.current))
      (match proof.preprocessed.bind (·.next) with
        | some v => some v
        | none => if pw > 0 then some (List.replicate pw 0) else none)
      periodic pv c ζ α q = some (.ok ())) :
    verify_with_preprocessed G g B cfg air omn opn sp pcs proof pv vk s0 = some (.ok ()) := by
  obtain ⟨htd1, htd2⟩ := htd
  obtain ⟨hc1, hc2⟩ := hc
  obtain ⟨hq1, hq2⟩ := hqd
  have hz : cfg.zk.toNat ≤ proof.degree_bits := by omega
  have hval : validate_degree_bits proof.degree_bits cfg.zk.toNat cfg.log_min_trace_height
      cfg.log_max_trace_height = .ok (proof.degree_bits - cfg.zk.toNat, 2 ^ proof.degree_bits) := by
    simp only [validate_degree_bits]; split_ifs <;> first | omega | rfl
  have hkey' : (vk.map fun key => decide (pw > 0 ∧ key.degree_bits ≠ proof.degree_bits)).getD false =
      false := by
    rcases vk with _ | key
    · rfl
    · simpa using hkey key rfl
  have hl : lq + cfg.zk.toNat ≤ qd.log_size := by omega
  have hs1 : checked_log_size_sum lq cfg.zk.toNat = some (lq + cfg.zk.toNat, 2 ^ (lq + cfg.zk.toNat)) := by
    simp only [checked_log_size_sum]; split_ifs <;> first | omega | rfl
  have hs2 : checked_log_size_sum proof.degree_bits lq =
      some (proof.degree_bits + lq, 2 ^ (proof.degree_bits + lq)) := by
    simp only [checked_log_size_sum]; split_ifs <;> first | omega | rfl
  have hdiv : 2 ^ proof.degree_bits / 2 ^ cfg.zk.toNat = 2 ^ (proof.degree_bits - cfg.zk.toNat) :=
    Nat.pow_div hz (by norm_num)
  unfold verify_with_preprocessed
  simp only [hb, ne_eq, not_true_eq_false, ↓reduceIte, hval, natural_domain_pow G td htd1 htd2, hpp,
    Option.pure_def, Option.bind_eq_bind, Option.bind_some, hkey', Bool.false_eq_true,
    hdiv, ← hc2, natural_domain_pow G c hc1 rfl, size_eq]
  simp only [hlq, Except.toOption, Option.bind_some, hs1, hs2,
    try_create_disjoint_domain_pow G td qd g (by rw [htd1, hq1, one_mul]) hq2,
    split_domains_eq G hV qd hl, randomized_domains G hV td qd htd1 htd2 hq2 hz, hshape, hα, hζ]
  obtain ⟨hr1, hr2, -, -, -, hql, -⟩ := (check_shape_ok_iff _ _ _ _ _ _ _ _ _ _ _ _ _).1 hshape
  rw [prepare_opening_claims_ok G air omn proof pre td c _ hood hper hpv (by simp_all) htn
    (by rw [List.length_replicate, hql])]
  simp only [Option.bind_some, hpcs, hrec]
  exact hvc

/-! ## Completeness -/

/-- Screened periodic columns evaluate at a point to their periodic polynomials. -/
theorem periodic_at (G : Gen K) (hV : GenValid G) (hN : GenNested G) (h2 : (2 : K) ≠ 0) (c : Coset G)
    (cols : List (List K)) (hok : ∀ col ∈ cols, ColumnOk (2 ^ c.log_size) col) (x : K) :
    Coset.evaluate_periodic_columns_at G c cols (2 ^ c.log_size) x =
      some (cols.map fun col => (periodicPoly c.shift c.subgroup_generator c.log_size col).eval x) := by
  rw [evaluate_periodic_columns_at_eq_default G hV hN h2]
  simp only [Coset.default_evaluate_periodic_columns_at, size_eq, ne_eq, not_true_eq_false, ↓reduceIte]
  refine mapM_some_of _ _ _ fun col hcol => ?_
  obtain ⟨hp, hd⟩ := hok col hcol
  simp only [isPowerOfTwo, decide_eq_true_eq] at hp
  have hl : Nat.log 2 col.length ≤ c.log_size := by
    have := Nat.dvd_of_mod_eq_zero hd
    rw [← hp.2] at this
    exact (Nat.pow_dvd_pow_iff_le_right (by norm_num)).1 this
  exact evaluate_periodic_column_at_eq G hV hN h2 c col hp.2.symm hl x

open p3_air.builder.mirror Plonky3Lean.Spec.Air Plonky3Lean.Spec.Commit Plonky3Lean.Spec.UniStark
  Plonky3Lean.Proofs.Air in
/-- Completeness of the verifier, given the chunks' recombination.

Take a trace that satisfies the STARK's relation on the base subgroup of order n = 2^(b - z).

The AIR reads the next row of both traces, and its periodic columns have their periodic polynomials.

Open the trace and the preprocessed trace honestly at the drawn zeta, off the base subgroup.

Assume the steps before the claims accept.

Assume the opening argument accepts the claims, and the chunks recombine to the quotient at zeta.

Then the verifier accepts. -/
theorem verify_complete {D : ℕ} (G : Gen K) (hV : GenValid G) (hN : GenNested G) (h2 : (2 : K) ≠ 0)
    (g : K) (B : Module.Basis (Fin D) F K) (cfg : Config) (air : Air F) (opn : Bool)
    (sp : StarkSponge F K C Com S)
    (pcs : List (p3_fri.verifier.mirror.Claim G C) → Option ℕ → S → Option (Except PE Unit))
    (proof : Proof C P F K) (pv : List F) (vk : Option (PreprocessedVerifierKey C)) (s0 : S)
    (hb : air.public_boundary_io = []) {lq : ℕ} (td c qd : Coset G)
    (htd : td.shift = 1 ∧ td.log_size = proof.degree_bits)
    (hc : c.shift = 1 ∧ c.log_size = proof.degree_bits - cfg.zk.toNat)
    (hqd : qd.shift = g ∧ qd.log_size = proof.degree_bits + lq)
    (hlo : cfg.zk.toNat + cfg.log_min_trace_height ≤ proof.degree_bits)
    (hhi : proof.degree_bits ≤ cfg.log_max_trace_height) (hW : proof.degree_bits + lq < WORD_BITS)
    {pw : ℕ} {pre : Option (C × PreprocessedOpening K)}
    (hpp : process_preprocessed_trace air.preprocessed_width opn proof.preprocessed vk = .ok (pw, pre))
    (hkey : ∀ key ∈ vk, 0 < pw → key.degree_bits = proof.degree_bits)
    (hlq : get_log_num_quotient_chunks_for_domain air
      { preprocessed_width := pw, main_width := air.width, num_public_values := air.num_public_values,
        num_periodic_columns := air.num_periodic_columns } (2 ^ c.log_size) cfg.zk.toNat = .ok lq)
    (hshape : check_shape air true cfg.zk cfg.D (2 ^ (lq + cfg.zk.toNat)) cfg.ood_pow_bits pv
      proof.trace_local proof.trace_next proof.quotient_chunks proof.random
      proof.random_commitment.isSome proof.ood_pow_witness = .ok ())
    {α ζ : K} {s1 s2 : S}
    (hα : constraint_phase sp pw s0 proof.trace_commitment (pre.map (·.1)) pv = .ok (α, s1))
    (hζ : (ood_phase sp cfg.zk cfg.ood_pow_bits s1 proof.quotient_commitment proof.random_commitment
      proof.ood_pow_witness).run = some (.ok (ζ, s2)))
    (hζc : ¬ InCoset c.shift c.subgroup_generator c.log_size ζ)
    {s ω : F} (hcs : c.shift = algebraMap F K s) (hcg : c.subgroup_generator = algebraMap F K ω)
    (hω : IsPrimitiveRoot ω (2 ^ c.log_size)) (hs : s ≠ 0)
    {T : Instance F} (hT : T.height = 2 ^ c.log_size) {main prep periodic : ℕ → F[X]}
    (hmain : ∀ i < 2 ^ c.log_size, ∀ j, (main j).eval (s * ω ^ i) = T.main i j)
    (hprep : ∀ i < 2 ^ c.log_size, ∀ j, (prep j).eval (s * ω ^ i) = T.prep i j)
    (hpub : ∀ j, pv.getD j 0 = T.pub j)
    (hper : ∀ i < 2 ^ c.log_size, ∀ j, (periodic j).eval (s * ω ^ i) = T.periodic j i)
    (hpvl : pv.length = air.num_public_values) (hsat : SatisfiesStark (constraints air) T ω)
    (hnpc : air.num_periodic_columns = air.periodic_columns.length)
    (hscreen : ∀ col ∈ air.periodic_columns.map (·.map (algebraMap F K)), ColumnOk (2 ^ c.log_size) col)
    (hperK : ∀ j < air.num_periodic_columns, (periodic j).map (algebraMap F K) =
      periodicPoly c.shift c.subgroup_generator c.log_size
        ((air.periodic_columns.getD j []).map (algebraMap F K)))
    (htl : proof.trace_local =
      openRow (starkAssignK s ω c.log_size main prep (pv.getD · 0) periodic) (.main 0) air.width ζ)
    (htn : proof.trace_next = some
      (openRow (starkAssignK s ω c.log_size main prep (pv.getD · 0) periodic) (.main 1) air.width ζ))
    (hpre : (proof.preprocessed = some ⟨
        openRow (starkAssignK s ω c.log_size main prep (pv.getD · 0) periodic) (.prep 0)
          air.preprocessed_width ζ,
        some (openRow (starkAssignK s ω c.log_size main prep (pv.getD · 0) periodic) (.prep 1)
          air.preprocessed_width ζ)⟩) ∨
      (proof.preprocessed = none ∧ air.preprocessed_width = 0 ∧ pw = 0))
    (hpcs : pcs (opening_claims G true proof proof.random
      (openRow (starkAssignK s ω c.log_size main prep (pv.getD · 0) periodic) (.main 1) air.width ζ)
      pre td (List.replicate (2 ^ (lq + cfg.zk.toNat)) td) ζ (ζ * c.subgroup_generator))
      (pre.map fun _ => cfg.zk.toNat + 2) s2 = some (.ok ()))
    (hrec : recompose_quotient_from_chunks G B
      ((List.range (2 ^ (lq + cfg.zk.toNat))).map (chunk G hV qd (lq + cfg.zk.toNat)))
      proof.quotient_chunks ζ = some ((quotientPoly c.shift c.subgroup_generator c.log_size
        (combinedPoly α (starkAssignK s ω c.log_size main prep (pv.getD · 0) periodic)
          (constraints air))).eval ζ)) :
    verify_with_preprocessed G g B cfg air true opn sp pcs proof pv vk s0 = some (.ok ()) := by
  set σ := starkAssignK (K := K) s ω c.log_size main prep (pv.getD · 0) periodic with hσ
  have hood : check_ood_point G c ζ = .ok () := by
    simp [check_ood_point, (vanishing_poly_at_point_eq_zero G hV c ζ).not.2 hζc, pure, Except.pure]
  -- The periodic values are the periodic polynomials at zeta.
  have hpv : Coset.evaluate_periodic_columns_at G c (air.periodic_columns.map (·.map (algebraMap F K)))
      (2 ^ c.log_size) ζ = some (openRow σ .periodic air.num_periodic_columns ζ) := by
    rw [periodic_at G hV hN h2 c _ hscreen ζ]
    refine congrArg some (List.ext_getElem (by simp [openRow, hnpc]) fun j h1 h2' => ?_)
    have hj : j < air.num_periodic_columns := by simpa [openRow] using h2'
    simp only [List.getElem_map, openRow, List.getElem_range, hσ, starkAssignK, starkAssign]
    rw [hperK j hj, List.getD_eq_getElem _ _ (by omega)]
  -- The preprocessed rows the check reads are the honest ones.
  have hpre' : ((proof.preprocessed.map (·.current)) = some (openRow σ (.prep 0) air.preprocessed_width ζ) ∧
      (match proof.preprocessed.bind (·.next) with
        | some v => some v
        | none => if pw > 0 then some (List.replicate pw 0) else none) =
        some (openRow σ (.prep 1) air.preprocessed_width ζ)) ∨
      (proof.preprocessed.map (·.current) = none ∧
        (match proof.preprocessed.bind (·.next) with
          | some v => some v
          | none => if pw > 0 then some (List.replicate pw 0) else none) = none ∧
        air.preprocessed_width = 0) := by
    rcases hpre with h | ⟨h, h0, hp0⟩
    · left; simp [h]
    · right; simp [h, h0, hp0]
  refine verify_accepts G hV g B cfg air true opn sp pcs proof pv vk s0 hb td c qd htd hc hqd hlo hhi
    hW hpp hkey hlq hshape hα hζ hood ((new_ok_iff _ _).2 hscreen) hpv
    (by simp [htn]) hpcs hrec ?_
  rw [htl, htn, Option.getD_some]
  exact verify_constraints_complete G hV h2 hb c hcs hcg hω hs hT hmain hprep hpub hper hpvl hsat hζc α
    hpre'

/-! ## The FRI scheme over Merkle commitments -/

section merkle

open Plonky3Lean.Proofs.Fri Plonky3Lean.Proofs.MerkleTree Plonky3Lean.Spec.Fri p3_fri.mirror
  p3_fri.config.mirror p3_fri.transcript.mirror p3_fri.verifier.mirror p3_commit.pcs.univariate.mirror
open p3_air.builder.mirror Plonky3Lean.Spec.Air Plonky3Lean.Spec.Commit Plonky3Lean.Spec.UniStark
  Plonky3Lean.Proofs.Air

variable {DI DF : Type}

/-- An honest FRI prover over Merkle commitments, for the given claims.

It bundles the hypotheses of the PCS completeness over Merkle trees:

- the claims are the evaluations of columns below their domain's size
- every batch commits and opens the low-degree extensions of its columns
- every round commits and opens its codeword, and folds the DEEP words
- the final polynomial interpolates the final word
- the caps lie low enough. -/
def MerkleHonest (G : Gen K) (g : K) {C S : Type} (hashI : List (List K) → DI) (cmpI : List DI → DI)
    (zI : DI) (capI : ℕ) (hashF : List (List K) → DF) (cmpF : List DF → DF) (zF : DF) (capF : ℕ)
    (sp : Sponge K (merkleOps hashF cmpF zF capF).Commitment S) (params : FriParameters)
    (claims : List (Claim G C))
    (proof : FriProof K (merkleOps hashF cmpF zF capF).Commitment (merkleOps hashF cmpF zF capF).MultiProof
      (merkleOps hashI cmpI zI capI).MultiProof) (s : S)
    (commit_of : C → (merkleOps hashI cmpI zI capI).Commitment) : Prop :=
  G.adicity < 64 ∧ ∃ (L : List ℕ) (cols : MatrixOpening K (p3_commit.domain.mirror.Coset G) → List K[X]) (α : K) (s2 : S)
    (betas : List K) (s3 s4 : S) (indices : List ℕ),
    FriPre G params claims proof L ∧
    (∀ c ∈ claims, ∀ m ∈ c.matrices, ∀ p ∈ m.points, p.values = (cols m).map (·.eval p.point)) ∧
    (∀ c ∈ claims, ∀ m ∈ c.matrices, ∀ f ∈ cols m, f.degree < ↑(2 ^ m.domain.log_size)) ∧
    (∀ c ∈ claims, ∀ m ∈ c.matrices, params.log_final_poly_len ≤ m.domain.log_size) ∧
    (∀ c ∈ claims, ∀ m ∈ c.matrices, m.points ≠ []) ∧
    (∀ c ∈ claims, ∀ m ∈ c.matrices, ∀ p ∈ m.points,
      ∀ r < 2 ^ (inputLogHeights params.log_blowup claims).headD 0,
        p.point ≠ rowPoint G g ((inputLogHeights params.log_blowup claims).headD 0) r) ∧
    (∀ c ∈ claims, ∃ m ∈ c.matrices, capI ≤ m.domain.log_size + params.log_blowup) ∧
    capF ≤ params.log_blowup + params.log_final_poly_len ∧
    (∀ c ∈ claims, commit_of c.commitment =
      merkleCap hashI cmpI zI capI (batchMats G g params.log_blowup cols c)) ∧
    batch_phase sp (PcsShape.from_claims params claims) (claimedState sp claims s)
      (some proof.batch_pow_witness) = pure (α, s2) ∧
    commit_rounds sp (FriShape.with_schedule params L ((inputLogHeights params.log_blowup claims).headD 0))
      s2 proof.commit_phase_commits proof.commit_pow_witnesses = pure (betas, s3) ∧
    query_phase sp (FriShape.with_schedule params L ((inputLogHeights params.log_blowup claims).headD 0))
      s3 proof.final_poly (some proof.query_pow_witness) = pure (indices, s4) ∧
    proof.input_openings = claims.map (honestBatch G g params.log_blowup
      ((inputLogHeights params.log_blowup claims).headD 0) cols hashI cmpI zI capI indices) ∧
    (∀ q i, indices[q]? = some i →
      HonestSiblings G (deepInput g α params.log_blowup cols claims) q
        ((inputLogHeights params.log_blowup claims).headD 0) i
        (deepOn g α params.log_blowup cols claims ((inputLogHeights params.log_blowup claims).headD 0))
        (proofRounds proof betas L)) ∧
    (∀ i < 2 ^ params.log_final_poly_len, proof.final_poly.getD i 0 =
      Plonky3Lean.Spec.Dft.idft (G.gen params.log_final_poly_len) (2 ^ params.log_final_poly_len)
        (fun j => (revIndex (2 ^ params.log_final_poly_len)
          ((word G (proofFinal G g α params cols claims proof betas L)
            (params.log_final_poly_len + params.log_blowup)).take (2 ^ params.log_final_poly_len))).getD j 0) i) ∧
    (∀ k (hk : k < (proofRds G g α params cols claims proof betas L).length),
      proof.commit_phase_commits[k]? = some (merkleCap hashF cmpF zF capF
        [roundMat (proofRds G g α params cols claims proof betas L)[k].w
          (proofRds G g α params cols claims proof betas L)[k].a
          ((inputLogHeights params.log_blowup claims).headD 0 -
            (((proofRds G g α params cols claims proof betas L).take (k + 1)).map Rd.a).sum)]) ∧
      ∀ o, proof.commit_phase_openings[k]? = some o → o.opening_proof =
        (roundGroups (proofRds G g α params cols claims proof betas L) indices k).map
          (merklePath hashF cmpF zF capF
            [roundMat (proofRds G g α params cols claims proof betas L)[k].w
              (proofRds G g α params cols claims proof betas L)[k].a
              ((inputLogHeights params.log_blowup claims).headD 0 -
                (((proofRds G g α params cols claims proof betas L).take (k + 1)).map Rd.a).sum)]))

/-- The FRI verifier over Merkle commitments accepts an honest prover's proof. -/
theorem merkle_accepts (G : Gen K) (hV : GenValid G) (hN : GenNested G) (h2 : (2 : K) ≠ 0) (g : K)
    {C S : Type} (hashI : List (List K) → DI) (cmpI : List DI → DI) (zI : DI) (capI : ℕ)
    (hashF : List (List K) → DF) (cmpF : List DF → DF) (zF : DF) (capF : ℕ)
    (sp : Sponge K (merkleOps hashF cmpF zF capF).Commitment S) (params : FriParameters)
    (claims : List (Claim G C))
    (proof : FriProof K (merkleOps hashF cmpF zF capF).Commitment (merkleOps hashF cmpF zF capF).MultiProof
      (merkleOps hashI cmpI zI capI).MultiProof) (s : S)
    (commit_of : C → (merkleOps hashI cmpI zI capI).Commitment)
    (h : MerkleHonest G g hashI cmpI zI capI hashF cmpF zF capF sp params claims proof s commit_of) :
    (p3_fri.two_adic_pcs.mirror.verify G g (merkleOps hashF cmpF zF capF) (merkleOps hashI cmpI zI capI)
      sp params claims proof s commit_of).run = some (.ok ()) := by
  obtain ⟨hG, L, cols, α, s2, betas, s3, s4, indices, hpre, hval, hdeg, hF, hpts, hout, hcapI, hcapF,
    hcom, hb, hc, hq, hopen, hsib, hfin, hround⟩ := h
  rw [pcs_verify_complete_merkle G hV hN h2 g hashI cmpI zI capI hashF cmpF zF capF sp params claims
    proof s commit_of hG hpre cols hval hdeg hF hpts hout hcapI hcapF hcom hb hc hq hopen hsib hfin hround]
  rfl

theorem verify_complete_merkle {D : ℕ} (G : Gen K) (hV : GenValid G) (hN : GenNested G) (h2 : (2 : K) ≠ 0)
    (g : K) (B : Module.Basis (Fin D) F K) (cfg : Config) (air : Air F) (opn : Bool)
    (hashI : List (List K) → DI) (cmpI : List DI → DI) (zI : DI) (capI : ℕ)
    (hashF : List (List K) → DF) (cmpF : List DF → DF) (zF : DF) (capF : ℕ) (params : FriParameters)
    (commit_of : C → (merkleOps hashI cmpI zI capI).Commitment)
    (sp : StarkSponge F K C (merkleOps hashF cmpF zF capF).Commitment S)
    (proof : Proof C (FriProof K (merkleOps hashF cmpF zF capF).Commitment (merkleOps hashF cmpF zF capF).MultiProof
      (merkleOps hashI cmpI zI capI).MultiProof) F K) (pv : List F) (vk : Option (PreprocessedVerifierKey C)) (s0 : S)
    (hb : air.public_boundary_io = []) {lq : ℕ} (td c qd : p3_commit.domain.mirror.Coset G)
    (htd : td.shift = 1 ∧ td.log_size = proof.degree_bits)
    (hc : c.shift = 1 ∧ c.log_size = proof.degree_bits - cfg.zk.toNat)
    (hqd : qd.shift = g ∧ qd.log_size = proof.degree_bits + lq)
    (hlo : cfg.zk.toNat + cfg.log_min_trace_height ≤ proof.degree_bits)
    (hhi : proof.degree_bits ≤ cfg.log_max_trace_height) (hW : proof.degree_bits + lq < WORD_BITS)
    {pw : ℕ} {pre : Option (C × PreprocessedOpening K)}
    (hpp : process_preprocessed_trace air.preprocessed_width opn proof.preprocessed vk = .ok (pw, pre))
    (hkey : ∀ key ∈ vk, 0 < pw → key.degree_bits = proof.degree_bits)
    (hlq : get_log_num_quotient_chunks_for_domain air
      { preprocessed_width := pw, main_width := air.width, num_public_values := air.num_public_values,
        num_periodic_columns := air.num_periodic_columns } (2 ^ c.log_size) cfg.zk.toNat = .ok lq)
    (hshape : check_shape air true cfg.zk cfg.D (2 ^ (lq + cfg.zk.toNat)) cfg.ood_pow_bits pv
      proof.trace_local proof.trace_next proof.quotient_chunks proof.random
      proof.random_commitment.isSome proof.ood_pow_witness = .ok ())
    {α ζ : K} {s1 s2 : S}
    (hα : constraint_phase sp pw s0 proof.trace_commitment (pre.map (·.1)) pv = .ok (α, s1))
    (hζ : (ood_phase sp cfg.zk cfg.ood_pow_bits s1 proof.quotient_commitment proof.random_commitment
      proof.ood_pow_witness).run = some (.ok (ζ, s2)))
    (hζc : ¬ InCoset c.shift c.subgroup_generator c.log_size ζ)
    {s ω : F} (hcs : c.shift = algebraMap F K s) (hcg : c.subgroup_generator = algebraMap F K ω)
    (hω : IsPrimitiveRoot ω (2 ^ c.log_size)) (hs : s ≠ 0)
    {T : Instance F} (hT : T.height = 2 ^ c.log_size) {main prep periodic : ℕ → F[X]}
    (hmain : ∀ i < 2 ^ c.log_size, ∀ j, (main j).eval (s * ω ^ i) = T.main i j)
    (hprep : ∀ i < 2 ^ c.log_size, ∀ j, (prep j).eval (s * ω ^ i) = T.prep i j)
    (hpub : ∀ j, pv.getD j 0 = T.pub j)
    (hper : ∀ i < 2 ^ c.log_size, ∀ j, (periodic j).eval (s * ω ^ i) = T.periodic j i)
    (hpvl : pv.length = air.num_public_values) (hsat : SatisfiesStark (constraints air) T ω)
    (hnpc : air.num_periodic_columns = air.periodic_columns.length)
    (hscreen : ∀ col ∈ air.periodic_columns.map (·.map (algebraMap F K)), ColumnOk (2 ^ c.log_size) col)
    (hperK : ∀ j < air.num_periodic_columns, (periodic j).map (algebraMap F K) =
      periodicPoly c.shift c.subgroup_generator c.log_size
        ((air.periodic_columns.getD j []).map (algebraMap F K)))
    (htl : proof.trace_local =
      openRow (starkAssignK s ω c.log_size main prep (pv.getD · 0) periodic) (.main 0) air.width ζ)
    (htn : proof.trace_next = some
      (openRow (starkAssignK s ω c.log_size main prep (pv.getD · 0) periodic) (.main 1) air.width ζ))
    (hpre : (proof.preprocessed = some ⟨
        openRow (starkAssignK s ω c.log_size main prep (pv.getD · 0) periodic) (.prep 0)
          air.preprocessed_width ζ,
        some (openRow (starkAssignK s ω c.log_size main prep (pv.getD · 0) periodic) (.prep 1)
          air.preprocessed_width ζ)⟩) ∨
      (proof.preprocessed = none ∧ air.preprocessed_width = 0 ∧ pw = 0))
    (hfit : ∀ e ∈ constraints air, FitsChunks (2 ^ c.log_size) (2 ^ (lq + cfg.zk.toNat))
      (constraintPoly (starkAssign s ω c.log_size main prep (pv.getD · 0) periodic) e))
    (hlen : proof.quotient_chunks.length = 2 ^ (lq + cfg.zk.toNat))
    (hv : ∀ i (hi : i < 2 ^ (lq + cfg.zk.toNat)),
      from_ext_basis_coefficients B (proof.quotient_chunks[i]'(hlen ▸ hi)) =
        some ((chunkInterp hV qd (lq + cfg.zk.toNat) (quotientPoly c.shift c.subgroup_generator c.log_size
          (combinedPoly α (starkAssignK s ω c.log_size main prep (pv.getD · 0) periodic) (constraints air))) i).eval ζ))
    (hM : MerkleHonest G g hashI cmpI zI capI hashF cmpF zF capF sp.sponge params
      (opening_claims G true proof proof.random
        (openRow (starkAssignK s ω c.log_size main prep (pv.getD · 0) periodic) (.main 1) air.width ζ)
        pre td (List.replicate (2 ^ (lq + cfg.zk.toNat)) td) ζ (ζ * c.subgroup_generator))
      proof.opening_proof s2 commit_of) :
    verify_with_preprocessed G g B cfg air true opn sp
      (fun cl _ st => (p3_fri.two_adic_pcs.mirror.verify G g (merkleOps hashF cmpF zF capF)
      (merkleOps hashI cmpI zI capI) sp.sponge params cl proof.opening_proof st commit_of).run)
      proof pv vk s0 = some (.ok ()) := by
  have hdeg := degree_quotient_lt (K := K) Nat.one_le_two_pow hfit α
  rw [← hcs, ← hcg, ← pow_add, show lq + cfg.zk.toNat + c.log_size = qd.log_size by omega] at hdeg
  exact verify_complete G hV hN h2 g B cfg air opn sp _ proof pv vk s0 hb td c qd htd hc hqd hlo hhi hW
    hpp hkey hlq hshape hα hζ hζc hcs hcg hω hs hT hmain hprep hpub hper hpvl hsat hnpc hscreen hperK htl
    htn hpre (merkle_accepts G hV hN h2 g hashI cmpI zI capI hashF cmpF zF capF sp.sponge params _
      proof.opening_proof s2 commit_of hM)
    (recompose_quotient hV qd _ B hN (by omega) _ hdeg _ hlen hv)

theorem verify_complete_hiding {D : ℕ} (G : Gen K) (hV : GenValid G) (hN : GenNested G) (h2 : (2 : K) ≠ 0)
    (g : K) (B : Module.Basis (Fin D) F K) (cfg : Config) (air : Air F) (opn : Bool)
    (hashI : List (List K) → DI) (cmpI : List DI → DI) (zI : DI) (capI : ℕ)
    (hashF : List (List K) → DF) (cmpF : List DF → DF) (zF : DF) (capF : ℕ) (params : FriParameters)
    (commit_of : C → (merkleOps hashI cmpI zI capI).Commitment)
    (r : ℕ)
    (sp : StarkSponge F K C (merkleOps hashF cmpF zF capF).Commitment S)
    (proof : Proof C (List (List (List (List K))) × FriProof K (merkleOps hashF cmpF zF capF).Commitment (merkleOps hashF cmpF zF capF).MultiProof
      (merkleOps hashI cmpI zI capI).MultiProof) F K) (pv : List F) (vk : Option (PreprocessedVerifierKey C)) (s0 : S)
    (hb : air.public_boundary_io = []) {lq : ℕ} (td c qd : p3_commit.domain.mirror.Coset G)
    (htd : td.shift = 1 ∧ td.log_size = proof.degree_bits)
    (hc : c.shift = 1 ∧ c.log_size = proof.degree_bits - cfg.zk.toNat)
    (hqd : qd.shift = g ∧ qd.log_size = proof.degree_bits + lq)
    (hlo : cfg.zk.toNat + cfg.log_min_trace_height ≤ proof.degree_bits)
    (hhi : proof.degree_bits ≤ cfg.log_max_trace_height) (hW : proof.degree_bits + lq < WORD_BITS)
    {pw : ℕ} {pre : Option (C × PreprocessedOpening K)}
    (hpp : process_preprocessed_trace air.preprocessed_width opn proof.preprocessed vk = .ok (pw, pre))
    (hkey : ∀ key ∈ vk, 0 < pw → key.degree_bits = proof.degree_bits)
    (hlq : get_log_num_quotient_chunks_for_domain air
      { preprocessed_width := pw, main_width := air.width, num_public_values := air.num_public_values,
        num_periodic_columns := air.num_periodic_columns } (2 ^ c.log_size) cfg.zk.toNat = .ok lq)
    (hshape : check_shape air true cfg.zk cfg.D (2 ^ (lq + cfg.zk.toNat)) cfg.ood_pow_bits pv
      proof.trace_local proof.trace_next proof.quotient_chunks proof.random
      proof.random_commitment.isSome proof.ood_pow_witness = .ok ())
    {α ζ : K} {s1 s2 : S}
    (hα : constraint_phase sp pw s0 proof.trace_commitment (pre.map (·.1)) pv = .ok (α, s1))
    (hζ : (ood_phase sp cfg.zk cfg.ood_pow_bits s1 proof.quotient_commitment proof.random_commitment
      proof.ood_pow_witness).run = some (.ok (ζ, s2)))
    (hζc : ¬ InCoset c.shift c.subgroup_generator c.log_size ζ)
    {s ω : F} (hcs : c.shift = algebraMap F K s) (hcg : c.subgroup_generator = algebraMap F K ω)
    (hω : IsPrimitiveRoot ω (2 ^ c.log_size)) (hs : s ≠ 0)
    {T : Instance F} (hT : T.height = 2 ^ c.log_size) {main prep periodic : ℕ → F[X]}
    (hmain : ∀ i < 2 ^ c.log_size, ∀ j, (main j).eval (s * ω ^ i) = T.main i j)
    (hprep : ∀ i < 2 ^ c.log_size, ∀ j, (prep j).eval (s * ω ^ i) = T.prep i j)
    (hpub : ∀ j, pv.getD j 0 = T.pub j)
    (hper : ∀ i < 2 ^ c.log_size, ∀ j, (periodic j).eval (s * ω ^ i) = T.periodic j i)
    (hpvl : pv.length = air.num_public_values) (hsat : SatisfiesStark (constraints air) T ω)
    (hnpc : air.num_periodic_columns = air.periodic_columns.length)
    (hscreen : ∀ col ∈ air.periodic_columns.map (·.map (algebraMap F K)), ColumnOk (2 ^ c.log_size) col)
    (hperK : ∀ j < air.num_periodic_columns, (periodic j).map (algebraMap F K) =
      periodicPoly c.shift c.subgroup_generator c.log_size
        ((air.periodic_columns.getD j []).map (algebraMap F K)))
    (htl : proof.trace_local =
      openRow (starkAssignK s ω c.log_size main prep (pv.getD · 0) periodic) (.main 0) air.width ζ)
    (htn : proof.trace_next = some
      (openRow (starkAssignK s ω c.log_size main prep (pv.getD · 0) periodic) (.main 1) air.width ζ))
    (hpre : (proof.preprocessed = some ⟨
        openRow (starkAssignK s ω c.log_size main prep (pv.getD · 0) periodic) (.prep 0)
          air.preprocessed_width ζ,
        some (openRow (starkAssignK s ω c.log_size main prep (pv.getD · 0) periodic) (.prep 1)
          air.preprocessed_width ζ)⟩) ∨
      (proof.preprocessed = none ∧ air.preprocessed_width = 0 ∧ pw = 0))
    (hfit : ∀ e ∈ constraints air, FitsChunks (2 ^ c.log_size) (2 ^ (lq + cfg.zk.toNat))
      (constraintPoly (starkAssign s ω c.log_size main prep (pv.getD · 0) periodic) e))
    (hlen : proof.quotient_chunks.length = 2 ^ (lq + cfg.zk.toNat))
    (t : ℕ → K[X])
    (hv : ∀ i (hi : i < 2 ^ (lq + cfg.zk.toNat)),
      from_ext_basis_coefficients B (proof.quotient_chunks[i]'(hlen ▸ hi)) =
        some ((chunkInterp hV qd (lq + cfg.zk.toNat) (quotientPoly c.shift c.subgroup_generator c.log_size
          (combinedPoly α (starkAssignK s ω c.log_size main prep (pv.getD · 0) periodic) (constraints air))) i +
          chunkZ hV qd (lq + cfg.zk.toNat) i * mask hV qd (lq + cfg.zk.toNat) t i).eval ζ))
    (full : List (p3_fri.verifier.mirror.Claim G C))
    (hcl : (opening_claims G true proof proof.random
        (openRow (starkAssignK s ω c.log_size main prep (pv.getD · 0) periodic) (.main 1) air.width ζ)
        pre td (List.replicate (2 ^ (lq + cfg.zk.toNat)) td) ζ (ζ * c.subgroup_generator)) =
      (hideClaims r (pre.map fun _ => cfg.zk.toNat + 2) full).1)
    (hrand : proof.opening_proof.1 = (hideClaims r (pre.map fun _ => cfg.zk.toNat + 2) full).2)
    (hidx : ∀ i, pre.map (fun _ => cfg.zk.toNat + 2) = some i → i < full.length) (hDr : cfg.D ≤ r)
    (hbud : ∀ cl ∈ full, ∀ m ∈ cl.matrices, ∃ req,
      p3_fri.hiding_pcs.mirror.hiding_budget params.num_queries cfg.D m.points.length = some req ∧
        req ≤ m.domain.size / 2)
    (hhid : ∀ e ∈ full.zipIdx, ∀ m ∈ e.1.matrices, ∀ p ∈ m.points,
      hiddenCount r (pre.map fun _ => cfg.zk.toNat + 2) e.2 ≤ p.values.length)
    (hM : MerkleHonest G g hashI cmpI zI capI hashF cmpF zF capF sp.sponge params full
      proof.opening_proof.2 s2 commit_of) :
    verify_with_preprocessed G g B cfg air true opn sp
      (fun cl idx st => (p3_fri.hiding_pcs.mirror.verify_hiding G g (merkleOps hashF cmpF zF capF)
      (merkleOps hashI cmpI zI capI) sp.sponge params cfg.D r idx cl proof.opening_proof.1
      proof.opening_proof.2 st commit_of).run)
      proof pv vk s0 = some (.ok ()) := by
  have hdeg := degree_quotient_lt (K := K) Nat.one_le_two_pow hfit α
  rw [← hcs, ← hcg, ← pow_add, show lq + cfg.zk.toNat + c.log_size = qd.log_size by omega] at hdeg
  have hacc := verify_hiding_complete G g _ _ sp.sponge params cfg.D r _ full proof.opening_proof.2 s2
    commit_of hidx hDr hbud hhid (by
      have := merkle_accepts G hV hN h2 g hashI cmpI zI capI hashF cmpF zF capF sp.sponge params full
        proof.opening_proof.2 s2 commit_of hM
      exact ExceptT.ext (by rw [this]; rfl))
  refine verify_complete G hV hN h2 g B cfg air opn sp _ proof pv vk s0 hb td c qd htd hc hqd hlo hhi hW
    hpp hkey hlq hshape hα hζ hζc hcs hcg hω hs hT hmain hprep hpub hper hpvl hsat hnpc hscreen hperK htl
    htn hpre ?_ (recompose_quotient_masked hV qd _ B hN (by omega) _ hdeg t ζ _ hlen hv)
  simp only [hcl, hrand, hacc]
  rfl

end merkle

/-! ## When the verifier panics -/

theorem validate_degree_bits_ok {db z lo hi a b : ℕ} (h : validate_degree_bits db z lo hi = .ok (a, b)) :
    a = db - z ∧ b = 2 ^ db ∧ z + lo ≤ db ∧ db ≤ hi := by
  simp only [validate_degree_bits] at h
  split_ifs at h with h1 h2 h3
  cases h
  exact ⟨rfl, rfl, by omega, by omega⟩

theorem checked_log_size_sum_some {a b x n : ℕ} (h : checked_log_size_sum a b = some (x, n)) :
    x = a + b ∧ n = 2 ^ (a + b) := by
  simp only [checked_log_size_sum] at h
  split_ifs at h; cases h; exact ⟨rfl, rfl⟩

/-- The second phase panics exactly at the grind, when the commitment steps pass and the difficulty is unsafe. -/
theorem ood_phase_run_eq_none {C Com S : Type} (sp : StarkSponge F K C Com S) (zk : Bool) (bits : ℕ) (s : S)
    (quotient : C) (random : Option C) (w : F) :
    (p3_uni_stark.verify.mirror.ood_phase sp zk bits s quotient random w).run = none ↔
      random.isSome = zk ∧ 0 < bits ∧ ¬ Plonky3Lean.Proofs.Fri.PowSafe sp.sponge.order bits := by
  unfold p3_uni_stark.verify.mirror.ood_phase
  rcases zk <;> rcases random with _ | r <;> by_cases hb : 0 < bits <;>
    simp [hb, ExceptT.run_bind, ExceptT.lift, ExceptT.mk, throw, throwThe, MonadExceptOf.throw]
  any_goals (simp [ExceptT.run]; done)
  · rw [← Plonky3Lean.Proofs.Fri.check_witness_eq_none sp.sponge (sp.observe_commitment s quotient) bits]
    rcases p3_fri.transcript.mirror.check_witness sp.sponge (sp.observe_commitment s quotient) bits
      ((algebraMap F K) w) with _ | ⟨_ | _, s'⟩ <;> simp [ExceptT.run, pure, ExceptT.pure, ExceptT.mk, Functor.map, ExceptT.map]
  · rw [← Plonky3Lean.Proofs.Fri.check_witness_eq_none sp.sponge
      (sp.observe_commitment (sp.observe_commitment s quotient) r) bits]
    rcases p3_fri.transcript.mirror.check_witness sp.sponge
      (sp.observe_commitment (sp.observe_commitment s quotient) r) bits
      ((algebraMap F K) w) with _ | ⟨_ | _, s'⟩ <;> simp [ExceptT.run, pure, ExceptT.pure, ExceptT.mk, Functor.map, ExceptT.map]

theorem new_ok_eq {cols : List (List K)} {height : ℕ} {pc : PeriodicColumns K}
    (h : PeriodicColumns.new cols height = .ok pc) :
    pc = ⟨cols, height⟩ ∧ ∀ col ∈ cols, ColumnOk height col := by
  have h' := h
  rw [new_eq] at h'
  split at h'
  · cases h'
    exact ⟨rfl, (new_ok_iff cols height).1 h⟩
  · cases h'

variable {C P : Type} in
/-- The claims step never panics once the shape checks pass:

- zeta off the base domain, or its rejection, comes first
- screened periodic columns evaluate
- the next row of the trace is present when the AIR reads it. -/
theorem prepare_opening_claims_ne_none (G : Gen K) (hV : GenValid G) (hN : GenNested G) (h2 : (2 : K) ≠ 0)
    (air : Air F) (omn : Bool) (proof : Proof C P F K) (pre : Option (C × PreprocessedOpening K))
    (td c : Coset G) (rqd : List (Coset G)) (ζ : K) (htn : omn = true → proof.trace_next.isSome) :
    prepare_opening_claims G air omn proof pre td c rqd ζ ≠ none := by
  unfold prepare_opening_claims
  rcases check_ood_point G c ζ with e | ⟨⟩
  · simp
  simp only [size_eq]
  rcases hp : PeriodicColumns.new (air.periodic_columns.map (·.map (algebraMap F K))) (2 ^ c.log_size)
    with e | pc
  · simp
  obtain ⟨rfl, hok⟩ := new_ok_eq hp
  simp only [periodic_at G hV hN h2 c _ hok, Coset.next_point, Option.pure_def, Option.bind_eq_bind,
    Option.bind_some]
  split_ifs with _ hm
  all_goals first
    | simp; done
    | obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 (htn hm); simp [hv]

variable {C P : Type} in
/-- A claims step that returns claims has checked that zeta lies off the base domain. -/
theorem prepare_opening_claims_ood (G : Gen K) (air : Air F) (omn : Bool) (proof : Proof C P F K)
    (pre : Option (C × PreprocessedOpening K)) (td c : Coset G) (rqd : List (Coset G)) (ζ : K)
    {r : List K × List (p3_fri.verifier.mirror.Claim G C)}
    (h : prepare_opening_claims G air omn proof pre td c rqd ζ = some (.ok r)) :
    check_ood_point G c ζ = .ok () := by
  unfold prepare_opening_claims at h
  rcases hc : check_ood_point G c ζ with e | ⟨⟩
  · simp [hc] at h
  · rfl

variable {C Com S P PE : Type} in
/-- The verifier never panics, on any proof, when:

- the AIR binds its public values by constraints
- the largest trace height lies within the generator table
- the quotient sizing returns at every preprocessed width and height
- the grinding difficulty before zeta is zero, or b < 64 with 2^b < p
- the opening argument never panics
- the configured extension degree is the basis's. -/
theorem verify_ne_none {D : ℕ} (G : Gen K) (hV : GenValid G) (hN : GenNested G) (h2 : (2 : K) ≠ 0)
    (g : K) (B : Module.Basis (Fin D) F K) (cfg : Config) (air : Air F) (omn opn : Bool)
    (sp : StarkSponge F K C Com S)
    (pcs : List (p3_fri.verifier.mirror.Claim G C) → Option ℕ → S → Option (Except PE Unit))
    (proof : Proof C P F K) (pv : List F) (vk : Option (PreprocessedVerifierKey C)) (s0 : S)
    (hb : air.public_boundary_io = []) (hmax : cfg.log_max_trace_height ≤ G.adicity)
    (hsizing : ∀ w n, ∃ l, get_log_num_quotient_chunks_for_domain air
      { preprocessed_width := w, main_width := air.width, num_public_values := air.num_public_values,
        num_periodic_columns := air.num_periodic_columns } n cfg.zk.toNat = .ok l)
    (hpow : Plonky3Lean.Proofs.Fri.PowSafe sp.sponge.order cfg.ood_pow_bits)
    (hpcs : ∀ cl idx st, pcs cl idx st ≠ none) (hD : cfg.D = D) :
    verify_with_preprocessed G g B cfg air omn opn sp pcs proof pv vk s0 ≠ none := by
  unfold verify_with_preprocessed
  simp only [hb, ne_eq, not_true_eq_false, ↓reduceIte, Option.pure_def, Option.bind_eq_bind]
  rcases hval : validate_degree_bits proof.degree_bits cfg.zk.toNat cfg.log_min_trace_height
    cfg.log_max_trace_height with e | ⟨bb, deg⟩
  · simp
  obtain ⟨rfl, rfl, hlo, hhi⟩ := validate_degree_bits_ok hval
  have hz : cfg.zk.toNat ≤ proof.degree_bits := by omega
  obtain ⟨td, htd1, htd2⟩ : ∃ td : Coset G, td.shift = 1 ∧ td.log_size = proof.degree_bits :=
    ⟨⟨1, proof.degree_bits, one_ne_zero, hhi.trans hmax⟩, rfl, rfl⟩
  obtain ⟨c, hc1, hc2⟩ : ∃ c : Coset G, c.shift = 1 ∧ c.log_size = proof.degree_bits - cfg.zk.toNat :=
    ⟨⟨1, proof.degree_bits - cfg.zk.toNat, one_ne_zero, by have := hhi.trans hmax; omega⟩, rfl, rfl⟩
  have hdiv : 2 ^ proof.degree_bits / 2 ^ cfg.zk.toNat = 2 ^ (proof.degree_bits - cfg.zk.toNat) :=
    Nat.pow_div hz (by norm_num)
  simp only [natural_domain_pow G td htd1 htd2, Option.bind_some]
  rcases hpp : process_preprocessed_trace air.preprocessed_width opn proof.preprocessed vk with e | ⟨pw, pre⟩
  · simp
  dsimp only
  by_cases hk : (vk.map fun key => decide (pw > 0 ∧ ¬key.degree_bits = proof.degree_bits)).getD false = true
  · simp only [hk, ↓reduceIte]; exact Option.some_ne_none _
  simp only [hk, Bool.false_eq_true, ↓reduceIte]
  obtain ⟨lq, hlq⟩ := hsizing pw (2 ^ c.log_size)
  simp only [← hc2, natural_domain_pow G c hc1 rfl, Option.bind_some, size_eq, hlq, Except.toOption]
  rcases hs1 : checked_log_size_sum lq cfg.zk.toNat with _ | ⟨x1, n1⟩
  · simp
  obtain ⟨-, rfl⟩ := checked_log_size_sum_some hs1
  simp only [hdiv, ← hc2, natural_domain_pow G c hc1 rfl, Option.bind_some]
  rcases hs2 : checked_log_size_sum proof.degree_bits lq with _ | ⟨x2, n2⟩
  · simp
  obtain ⟨-, rfl⟩ := checked_log_size_sum_some hs2
  dsimp only
  rcases hq : Coset.try_create_disjoint_domain G td g (2 ^ (proof.degree_bits + lq)) with _ | qd
  · simp
  obtain ⟨-, hq2, -⟩ := try_create_disjoint_domain_some G hq
  rw [log2Ceil_pow] at hq2
  have hl : lq + cfg.zk.toNat ≤ qd.log_size := by omega
  simp only [split_domains_eq G hV qd hl, Option.bind_some,
    randomized_domains G hV td qd htd1 htd2 hq2 hz]
  rcases hsh : check_shape air omn cfg.zk cfg.D (2 ^ (lq + cfg.zk.toNat)) cfg.ood_pow_bits pv
    proof.trace_local proof.trace_next proof.quotient_chunks proof.random proof.random_commitment.isSome
    proof.ood_pow_witness with e | ⟨⟩
  · simp
  obtain ⟨-, -, -, htn, -, hql, hqD, -⟩ := (check_shape_ok_iff _ _ _ _ _ _ _ _ _ _ _ _ _).1 hsh
  dsimp only
  rcases hα : p3_uni_stark.verify.mirror.constraint_phase sp pw s0 proof.trace_commitment
    (pre.map (·.1)) pv with f | ⟨α, s1⟩
  · simp [hα]
  simp only [hα]
  rcases hζ : (p3_uni_stark.verify.mirror.ood_phase sp cfg.zk cfg.ood_pow_bits s1 proof.quotient_commitment
    proof.random_commitment proof.ood_pow_witness).run with _ | (f | ⟨ζ, s2⟩)
  · exact absurd hpow ((ood_phase_run_eq_none sp _ _ _ _ _ _).1 hζ).2.2
  · simp
  simp only [Option.bind_some]
  rcases hpr : prepare_opening_claims G air omn proof pre td c
    (List.replicate (2 ^ (lq + cfg.zk.toNat)) td) ζ with _ | (e | ⟨per, cl⟩)
  · exact absurd hpr (prepare_opening_claims_ne_none G hV hN h2 air omn proof pre td c _ ζ fun hm => by
      simp only [hm, ↓reduceIte] at htn; obtain ⟨v, hv, -⟩ := htn; simp [hv])
  · simp
  have hood := prepare_opening_claims_ood G air omn proof pre td c _ ζ hpr
  simp only [Option.bind_some]
  rcases hp : pcs cl (pre.map fun _ => cfg.zk.toNat + 2) s2 with _ | (e | ⟨⟩)
  · exact absurd hp (hpcs _ _ _)
  · simp
  simp only [Option.bind_some]
  rw [recompose_eq hV qd _ B hl proof.quotient_chunks hql
    (fun i => ∑ d : Fin D, (proof.quotient_chunks.getD i []).getD d 0 * B d) (fun i hi => by
      have := hqD _ (List.getElem_mem (hql ▸ hi))
      simp only [from_ext_basis_coefficients, this, hD, ↓reduceIte, List.getD_eq_getElem _ _ (hql ▸ hi)])]
  simp only [Option.bind_some]
  intro h0
  rw [verify_constraints_none_iff G hV air hb, ← vanishing_poly_at_point_eq_zero G hV c ζ] at h0
  simp [check_ood_point, h0, throw, throwThe, MonadExceptOf.throw] at hood

variable {C Com S P PE : Type} in
/-- The boundary assertion panics on every proof of an AIR with boundary cells. -/
theorem verify_boundary_none {D : ℕ} (G : Gen K) (g : K) (B : Module.Basis (Fin D) F K) (cfg : Config)
    (air : Air F) (omn opn : Bool) (sp : StarkSponge F K C Com S)
    (pcs : List (p3_fri.verifier.mirror.Claim G C) → Option ℕ → S → Option (Except PE Unit))
    (proof : Proof C P F K) (pv : List F) (vk : Option (PreprocessedVerifierKey C)) (s0 : S)
    (hb : air.public_boundary_io ≠ []) :
    verify_with_preprocessed G g B cfg air omn opn sp pcs proof pv vk s0 = none := by
  simp [verify_with_preprocessed, hb]

variable {C : Type} in
/-- The preprocessed checks never compare a supplied key with the AIR.

A key of positive width w, with an opening of width w, passes whatever width the AIR declares. -/
theorem process_preprocessed_trace_any_key (air_width : ℕ) (used : Bool) (key : PreprocessedVerifierKey C)
    (p : PreprocessedOpening K) (hw : 0 < key.width) (hcur : p.current.length = key.width)
    (hnext : p.next = if used then some (List.replicate key.width 0) else none) :
    process_preprocessed_trace air_width used (some p) (some key) =
      .ok (key.width, some (key.commitment, p)) := by
  obtain ⟨w, d, cm⟩ := key
  rcases used <;> simp_all [process_preprocessed_trace, bind, Except.bind, pure, Except.pure] <;> omega

end Plonky3Lean.Proofs.UniStark
