module

public import Plonky3Lean.Proofs.BatchStark.Zeta
public import Plonky3Lean.Proofs.BatchStark.Layout
public import Plonky3Lean.Proofs.UniStark.EndToEnd

@[expose] public section

/-!
# The full batch verifier

The verifier runs its shape checks, the transcript, the opening argument, then each instance's check at zeta.

- When every step accepts, the verifier accepts.
- Accepted shape checks fix every count, size and opening shape.
- The claims at zeta then have a closed form, round by round.
- An honest instance passes its check at zeta.
- Completeness holds for any opening argument that accepts the claims.
- It also holds over Merkle commitments with two-adic FRI, and over the hiding scheme.
-/

set_option linter.unusedSectionVars false

universe u

namespace Plonky3Lean.Proofs.BatchStark.EndToEnd

open p3_air.air.mirror p3_lookup.mirror
open p3_uni_stark.verify.mirror (validate_degree_bits checked_log_size_sum WORD_BITS natural_domain_for_degree
  PreprocessedOpening)
open p3_uni_stark.verifier.mirror (recompose_quotient_from_chunks from_ext_basis_coefficients)
open p3_batch_stark.transcript.mirror p3_batch_stark.constraints.mirror p3_batch_stark.verify.mirror
open p3_commit.domain.mirror p3_commit.periodic.mirror p3_field.coset.mirror p3_dft.mirror
open p3_commit.pcs.univariate.mirror
open Plonky3Lean.Proofs.UniStark Plonky3Lean.Proofs.Commit Plonky3Lean.Proofs.Dft

variable {F K C Com S P PE : Type} [Field F] [DecidableEq F] [Inhabited F] [Field K] [DecidableEq K]
  [Algebra F K]

/-! ## The verifier's monad -/

@[simp] theorem panicOf_some {α : Type} (a : α) : panicOf (some a) = pure a := rfl

@[simp] theorem panicOf_none {α β : Type} (k : α → M β) : (panicOf none >>= k) = panicOf none := rfl

@[simp] theorem mk_ok {α : Type} (a : α) : (ExceptT.mk (some (.ok a)) : M α) = pure a := rfl

theorem bind_eq_pure {α β : Type} {m : M α} {k : α → M β} {b : β} :
    m >>= k = pure b ↔ ∃ a, m = pure a ∧ k a = pure b :=
  Plonky3Lean.Proofs.Fri.exceptT_bind_eq_pure m k b

theorem panicOf_eq_pure {α : Type} {o : Option α} {a : α} : panicOf o = pure a ↔ o = some a := by
  rcases o with _ | o
  · exact ⟨fun h => (by cases h), fun h => (by cases h)⟩
  · exact ⟨fun h => (by cases h; rfl), fun h => (by cases h; rfl)⟩

theorem mk_eq_pure {α : Type} {e : Except Error α} {a : α} : (ExceptT.mk (some e) : M α) = pure a ↔ e = .ok a :=
  ⟨fun h => by cases h; rfl, fun h => by subst h; rfl⟩

theorem throw_ne_pure {α : Type} {e : Error} {a : α} : (throw e : M α) ≠ pure a := by
  intro h; cases h

theorem ensure_eq_ok {c : Prop} [Decidable c] {e : Error} {u : Unit} : ensure c e = .ok u ↔ c := by
  unfold ensure; split_ifs with h <;> simp [h, pure, Except.pure]

theorem mapM_eq_pure {α : Type u} {β : Type} (f : α → M β) :
    ∀ (l : List α) (ys : List β), l.mapM f = pure ys ↔ List.Forall₂ (fun x y => f x = pure y) l ys
  | [], ys => by
    rcases ys with _ | _ <;> simp [List.mapM_nil]
    intro h; cases h
  | x :: l, ys => by
    rw [List.mapM_cons, bind_eq_pure]
    rcases ys with _ | ⟨y, ys⟩
    · simp only [List.forall₂_nil_right_iff, reduceCtorEq, iff_false, not_exists, not_and]
      intro a _ h
      obtain ⟨_, -, h⟩ := bind_eq_pure.1 h
      cases h
    · simp only [List.forall₂_cons, ← mapM_eq_pure f l ys]
      constructor
      · rintro ⟨a, ha, h⟩
        obtain ⟨b, hb, h⟩ := bind_eq_pure.1 h
        cases h
        exact ⟨ha, hb⟩
      · rintro ⟨ha, hb⟩
        exact ⟨y, ha, by rw [hb]; rfl⟩

theorem forM_eq_pure {α : Type u} (f : α → M PUnit) :
    ∀ (l : List α), l.forM f = pure () ↔ ∀ x ∈ l, f x = pure ()
  | [] => by simp
  | x :: l => by
    show f x >>= (fun _ => l.forM f) = pure () ↔ _
    rw [bind_eq_pure, List.forall_mem_cons, ← forM_eq_pure f l]
    exact ⟨fun ⟨⟨⟩, h1, h2⟩ => ⟨h1, h2⟩, fun ⟨h1, h2⟩ => ⟨(), h1, h2⟩⟩

/-! ## The shape checks -/

theorem validate_at_ok {cfg : Config} {i db a b : ℕ} (h : validate_degree_bits_at cfg i db = .ok (a, b)) :
    a = db - cfg.zk.toNat ∧ b = 2 ^ db ∧ cfg.zk.toNat + cfg.log_min_trace_height ≤ db ∧
      db ≤ cfg.log_max_trace_height ∧ db < 64 := by
  unfold validate_degree_bits_at validate_degree_bits at h
  split_ifs at h with h1 h2 h3
  cases h
  exact ⟨rfl, rfl, by omega, by omega, by simp only [WORD_BITS] at h3; omega⟩

theorem validate_at_eq {cfg : Config} {i db : ℕ} (h1 : cfg.zk.toNat + cfg.log_min_trace_height ≤ db)
    (h2 : db ≤ cfg.log_max_trace_height) (h3 : db < 64) :
    validate_degree_bits_at cfg i db = .ok (db - cfg.zk.toNat, 2 ^ db) := by
  unfold validate_degree_bits_at validate_degree_bits
  simp only [WORD_BITS]
  split_ifs <;> first | omega | rfl

theorem checked_some {a b x n : ℕ} (h : checked_log_size_sum a b = some (x, n)) :
    x = a + b ∧ n = 2 ^ (a + b) ∧ a + b < 64 := by
  simp only [checked_log_size_sum] at h
  split_ifs at h with h1; cases h; exact ⟨rfl, rfl, by simp only [WORD_BITS] at h1; omega⟩

theorem checked_eq {a b : ℕ} (h : a + b < 64) : checked_log_size_sum a b = some (a + b, 2 ^ (a + b)) := by
  simp only [checked_log_size_sum, WORD_BITS]; split_ifs <;> first | omega | rfl

section sizes

variable (G : Gen K) (cfg : Config) (common : CommonData C F) (sizing : ℕ → AirLayout → ℕ → Option ℕ)

/-- The layout instance i's sizing receives. -/
def layoutOf (ba : BatchAir F) (w : ℕ) : AirLayout :=
  { preprocessed_width := w, main_width := ba.air.width, num_public_values := ba.air.num_public_values,
    num_periodic_columns := ba.air.num_periodic_columns }

/-- What an accepted first loop computes for instance i of degree bits b:

- the base degree bits b - z and the extended size 2^b, with b within the bounds and below 64
- the common data's preprocessed width
- the sizing L on the base domain, and the chunk count 2^(L + z), with L + z below 64. -/
structure SizesOk (db : ℕ) (ba : BatchAir F) (i : ℕ) (sz : Sizes) : Prop where
  base : sz.base_degree_bits = db - cfg.zk.toNat
  ext : sz.ext_size = 2 ^ db
  lo : cfg.zk.toNat + cfg.log_min_trace_height ≤ db
  hi : db ≤ cfg.log_max_trace_height
  word : db < 64
  width : preprocessed_width common i = pure sz.preprocessed_width
  domain : ∃ bd, natural_domain_for_degree G (2 ^ (db - cfg.zk.toNat)) = some bd ∧
    sizing i (layoutOf ba sz.preprocessed_width) (Coset.size G bd) = some sz.log_num_quotient_chunks
  chunks : sz.num_quotient_chunks = 2 ^ (sz.log_num_quotient_chunks + cfg.zk.toNat)
  chunks_word : sz.log_num_quotient_chunks + cfg.zk.toNat < 64

theorem instance_sizes_pure {dbs : List ℕ} {ba : BatchAir F} {i : ℕ} {sz : Sizes}
    (h : instance_sizes G cfg common sizing dbs ba i = pure sz) :
    ∃ db, dbs[i]? = some db ∧ SizesOk G cfg common sizing db ba i sz := by
  unfold instance_sizes at h
  obtain ⟨db, hdb, h⟩ := bind_eq_pure.1 h
  obtain ⟨⟨b, e⟩, hv, h⟩ := bind_eq_pure.1 h
  obtain ⟨w, hw, h⟩ := bind_eq_pure.1 h
  obtain ⟨bd, hbd, h⟩ := bind_eq_pure.1 h
  obtain ⟨lq, hlq, h⟩ := bind_eq_pure.1 h
  obtain ⟨rfl, rfl, h1, h2, h3⟩ := validate_at_ok (mk_eq_pure.1 hv)
  rcases hc : checked_log_size_sum lq cfg.zk.toNat with _ | ⟨x, n⟩ <;> rw [hc] at h
  · exact absurd h throw_ne_pure
  obtain ⟨-, rfl, hw'⟩ := checked_some hc
  cases h
  exact ⟨db, panicOf_eq_pure.1 hdb, rfl, rfl, h1, h2, h3, hw, ⟨bd, panicOf_eq_pure.1 hbd,
    panicOf_eq_pure.1 hlq⟩, rfl, hw'⟩

/-- What accepted shape checks guarantee, with n instances:

- every count is n, and the randomization matches the scheme
- each instance's first loop accepted, with its sizes
- the multiplicity height bound holds
- each instance's openings pass their checks
- k counts the instances with lookups, and a permutation commitment is present exactly when k > 0. -/
structure ShapeOk (airs : List (BatchAir F)) (proof : BatchProof C P F K) (pvs : List (List F))
    (sizes : List Sizes) (k : ℕ) : Prop where
  opened_len : proof.opened.length = airs.length
  pvs_len : pvs.length = airs.length
  dbs_len : proof.degree_bits.length = airs.length
  terminals_len : proof.lookup_terminals.length = airs.length
  lookups_len : common.lookups.length = airs.length
  instances_len : ∀ g ∈ common.preprocessed, g.instances.length = airs.length
  random_open : ∀ ov ∈ proof.opened, ov.random.isSome = cfg.zk
  random : proof.random.isSome = cfg.zk
  first_loop : List.Forall₂ (fun (x : BatchAir F × ℕ) sz =>
    ∃ db, proof.degree_bits[x.2]? = some db ∧ SizesOk G cfg common sizing db x.1 x.2 sz) airs.zipIdx sizes
  height : check_multiplicity_height_bound cfg.characteristic common.lookups
    (sizes.map fun sz => 2 ^ sz.base_degree_bits) = some (.ok ())
  inst : ∀ x ∈ airs.zipIdx, ∃ pv ov sz lk t, pvs[x.2]? = some pv ∧ proof.opened[x.2]? = some ov ∧
    sizes[x.2]? = some sz ∧ common.lookups[x.2]? = some lk ∧ proof.lookup_terminals[x.2]? = some t ∧
    check_instance cfg x.1 x.2 pv ov sz lk t = .ok ()
  count : k = (common.lookups.filter (!·.isEmpty)).length
  perm : proof.permutation.isSome = decide (k > 0)

theorem check_shape_pure {airs : List (BatchAir F)} {proof : BatchProof C P F K} {pvs : List (List F)}
    {sizes : List Sizes} {k : ℕ} (h : check_shape G cfg airs sizing proof pvs common = pure (sizes, k)) :
    ShapeOk G cfg common sizing airs proof pvs sizes k := by
  unfold check_shape at h
  obtain ⟨⟨⟩, h1, h⟩ := bind_eq_pure.1 h
  obtain ⟨⟨⟩, h2, h⟩ := bind_eq_pure.1 h
  obtain ⟨sz, h3, h⟩ := bind_eq_pure.1 h
  obtain ⟨r, h4, h⟩ := bind_eq_pure.1 h
  rcases r with e | ⟨⟩
  · obtain ⟨_, h, -⟩ := bind_eq_pure.1 h
    exact absurd h throw_ne_pure
  obtain ⟨⟨⟩, h5, h⟩ := bind_eq_pure.1 h
  obtain ⟨⟨⟩, h6, h⟩ := bind_eq_pure.1 h
  cases h
  obtain ⟨c1, c2, c3, c4, c5, c6⟩ := ensure_eq_ok.1 (mk_eq_pure.1 h1)
  obtain ⟨r1, r2⟩ := ensure_eq_ok.1 (mk_eq_pure.1 h2)
  refine ⟨c1, c2, c3, c4, c5, c6, r1, r2, ?_, panicOf_eq_pure.1 h4, fun x hx => ?_, rfl,
    ensure_eq_ok.1 (mk_eq_pure.1 h6)⟩
  · refine ((mapM_eq_pure _ _ _).1 h3).imp fun x sz hx => ?_
    exact instance_sizes_pure G cfg common sizing hx
  · obtain ⟨ba, i⟩ := x
    have h := (forM_eq_pure _ _).1 h5 _ hx
    obtain ⟨pv, e1, h⟩ := bind_eq_pure.1 h
    obtain ⟨ov, e2, h⟩ := bind_eq_pure.1 h
    obtain ⟨sz, e3, h⟩ := bind_eq_pure.1 h
    obtain ⟨lk, e4, h⟩ := bind_eq_pure.1 h
    obtain ⟨t, e5, h⟩ := bind_eq_pure.1 h
    exact ⟨pv, ov, sz, lk, t, panicOf_eq_pure.1 e1, panicOf_eq_pure.1 e2, panicOf_eq_pure.1 e3,
      panicOf_eq_pure.1 e4, panicOf_eq_pure.1 e5, mk_eq_pure.1 h⟩

theorem ShapeOk.sizes_length {airs : List (BatchAir F)} {proof : BatchProof C P F K} {pvs : List (List F)}
    {sizes : List Sizes} {k : ℕ} (hs : ShapeOk G cfg common sizing airs proof pvs sizes k) :
    sizes.length = airs.length := by
  simpa using hs.first_loop.length_eq.symm

theorem ShapeOk.sizes_at {airs : List (BatchAir F)} {proof : BatchProof C P F K} {pvs : List (List F)}
    {sizes : List Sizes} {k : ℕ} (hs : ShapeOk G cfg common sizing airs proof pvs sizes k) {i : ℕ}
    (hi : i < airs.length) :
    ∃ db, proof.degree_bits[i]? = some db ∧ SizesOk G cfg common sizing db airs[i] i
      (sizes[i]'(by rw [hs.sizes_length]; exact hi)) := by
  have := (List.forall₂_iff_get.1 hs.first_loop).2 i (by simpa using hi) (by rw [hs.sizes_length]; exact hi)
  simpa using this

end sizes

/-- What accepted checks on one instance's openings guarantee. -/
structure InstOk (cfg : Config) (ba : BatchAir F) (pv : List F) (ov : Opened K) (sz : Sizes)
    (lk : List (Lookup F)) (t : Option K) : Prop where
  pv_len : pv.length = ba.air.num_public_values
  local_len : ov.trace_local.length = ba.air.width
  next : if ba.opens_main_next then ∃ v, ov.trace_next = some v ∧ v.length = ba.air.width
    else ov.trace_next = none
  chunks_len : ov.quotient_chunks.length = sz.num_quotient_chunks
  chunks_dim : ∀ q ∈ ov.quotient_chunks, q.length = cfg.D
  random_dim : ∀ r ∈ ov.random, r.length = cfg.D
  pre : match ov.preprocessed with
    | some p => sz.preprocessed_width ≠ 0 ∧ p.current.length = sz.preprocessed_width ∧
      (p.next.map List.length).getD 0 = (if ba.opens_preprocessed_next then sz.preprocessed_width else 0) ∧
      (ba.opens_preprocessed_next = true ∨ p.next = none)
    | none => sz.preprocessed_width = 0
  perm_local : ov.permutation_local.length = if lk.isEmpty then 0 else (lk.length + 1) * cfg.D
  perm_next : ov.permutation_next.length = if lk.isEmpty then 0 else (lk.length + 1) * cfg.D
  terminal : t.isSome = !lk.isEmpty

theorem except_bind_ok {α β : Type} {x : Except Error α} {f : α → Except Error β} {b : β} :
    x >>= f = .ok b ↔ ∃ a, x = .ok a ∧ f a = .ok b := by
  rcases x with e | a <;> simp [bind, Except.bind]

theorem getD_map_decide {o : Option (List K)} {w : ℕ} :
    (o.map fun v => decide (v.length = w)).getD false = true ↔ ∃ v, o = some v ∧ v.length = w := by
  cases o <;> simp

theorem check_instance_ok {cfg : Config} {ba : BatchAir F} {i : ℕ} {pv : List F} {ov : Opened K} {sz : Sizes}
    {lk : List (Lookup F)} {t : Option K} (h : check_instance cfg ba i pv ov sz lk t = .ok ()) :
    InstOk cfg ba pv ov sz lk t := by
  unfold check_instance ensure at h
  rcases hm : ba.opens_main_next <;> rcases hp : ov.preprocessed with _ | p <;>
    simp [hm, hp, bind, Except.bind, pure, Except.pure] at h
  all_goals
    simp only [throw, throwThe, MonadExceptOf.throw] at h
    split_ifs at h <;> simp only at h <;>
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp_all [getD_map_decide]

/-! ## The claims at zeta -/

instance instInhabitedOpened : Inhabited (Opened K) := ⟨⟨[], none, none, [], none, [], []⟩⟩

instance instInhabitedSizes : Inhabited Sizes := ⟨⟨0, 0, 0, 0, 0⟩⟩

theorem mapM_zipIdx {α : Type u} {β : Type} (l : List α) (f : α × ℕ → M β) (g : ℕ → β)
    (h : ∀ i (hi : i < l.length), f (l[i], i) = pure (g i)) :
    l.zipIdx.mapM f = pure ((List.range l.length).map g) := by
  rw [mapM_eq_pure, List.forall₂_iff_get]
  refine ⟨by simp, fun i h1 h2 => ?_⟩
  simp only [List.length_zipIdx] at h1
  simpa using h i h1

theorem mapM_range {β : Type} (n : ℕ) (f : ℕ → M β) (g : ℕ → β) (h : ∀ i < n, f i = pure (g i)) :
    (List.range n).mapM f = pure ((List.range n).map g) :=
  Plonky3Lean.Proofs.Fri.mapM_eq_pure_map' _ fun i hi => h i (List.mem_range.1 hi)

theorem mapM_panicOf {α β : Type} (f : α → Option β) :
    ∀ l : List α, l.mapM (fun x => panicOf (f x)) = panicOf (l.mapM f)
  | [] => rfl
  | x :: l => by
    rw [List.mapM_cons, List.mapM_cons, mapM_panicOf f l]
    rcases f x with _ | y
    · rfl
    · rcases l.mapM f with _ | ys <;> rfl

theorem getElem_eq_getD {α : Type} [Inhabited α] {l : List α} {i : ℕ} (h : i < l.length) :
    l[i] = l.getD i default := by
  rw [List.getD_eq_getElem _ _ h]

section claims

variable (G : Gen K) (hV : GenValid G) (g : K) (cfg : Config)

/-- The domains of n instances an accepted shape fixes, with b the degree bits and L the sizing:

- the base trace domain is the subgroup of order 2^(b - z)
- the extended trace domain is the subgroup of order 2^b
- the quotient coset has shift g and order 2^(b + L), with b + L < 64. -/
structure DomainsOk (proof : BatchProof C P F K) (sizes : List Sizes) (td ed qd : ℕ → Coset G) : Prop where
  base : ∀ i < proof.degree_bits.length,
    (td i).shift = 1 ∧ (td i).log_size = proof.degree_bits.getD i 0 - cfg.zk.toNat
  ext : ∀ i < proof.degree_bits.length, (ed i).shift = 1 ∧ (ed i).log_size = proof.degree_bits.getD i 0
  quot : ∀ i < proof.degree_bits.length, (qd i).shift = g ∧
    (qd i).log_size = proof.degree_bits.getD i 0 + (sizes.getD i default).log_num_quotient_chunks
  word : ∀ i < proof.degree_bits.length,
    proof.degree_bits.getD i 0 + (sizes.getD i default).log_num_quotient_chunks < 64

/-- The trace matrix of one instance: the current row at zeta, and the next row at zeta h when read. -/
def traceMat (omn : Bool) (td ed : Coset G) (ζ : K) (ov : Opened K) : MatrixOpening K (Coset G) :=
  if omn then ⟨ed, [⟨ζ, ov.trace_local⟩, ⟨ζ * td.subgroup_generator, ov.trace_next.getD []⟩]⟩
  else ⟨ed, [⟨ζ, ov.trace_local⟩]⟩

/-- The preprocessed matrix of one instance, on its extended trace domain. -/
def preMat (opn : Bool) (td ed : Coset G) (ζ : K) (p : PreprocessedOpening K) : MatrixOpening K (Coset G) :=
  if opn then ⟨ed, [⟨ζ, p.current⟩, ⟨ζ * td.subgroup_generator, p.next.getD []⟩]⟩
  else ⟨ed, [⟨ζ, p.current⟩]⟩

/-- The permutation matrix of one instance, absent when its permutation opening is empty. -/
def permMat (td ed : Coset G) (ζ : K) (ov : Opened K) : Option (MatrixOpening K (Coset G)) :=
  if ov.permutation_local.isEmpty then none
  else some ⟨ed, [⟨ζ, ov.permutation_local⟩, ⟨ζ * td.subgroup_generator, ov.permutation_next⟩]⟩

/-- The claims at zeta, in round order, for n instances with base domains td and extended domains ed.

- the randomization round, when hiding
- the trace round
- one matrix per quotient chunk, each on its instance's extended trace domain
- the preprocessed round, in matrix order
- the permutation round, over the instances with a permutation opening. -/
def batchClaims (airs : List (BatchAir F)) (proof : BatchProof C P F K) (common : CommonData C F)
    (td ed : ℕ → Coset G) (ζ : K) : List (p3_fri.verifier.mirror.Claim G C) :=
  let n := proof.degree_bits.length
  let ov := fun i => proof.opened.getD i default
  (match proof.random with
    | some rc => [⟨rc, (List.range n).map fun i => ⟨ed i, [⟨ζ, (ov i).random.getD []⟩]⟩⟩]
    | none => []) ++
  [⟨proof.main, (List.range n).map fun i =>
      traceMat G ((airs[i]?.map (·.opens_main_next)).getD false) (td i) (ed i) ζ (ov i)⟩,
    ⟨proof.quotient_chunks, ((List.range n).map fun i =>
      (ov i).quotient_chunks.map fun v => (⟨ed i, [⟨ζ, v⟩]⟩ : MatrixOpening K (Coset G))).flatten⟩] ++
  (match common.preprocessed with
    | some gl => [⟨gl.commitment, gl.matrix_to_instance.map fun inst =>
        preMat G ((airs[inst]?.map (·.opens_preprocessed_next)).getD false) (td inst) (ed inst) ζ
          ((ov inst).preprocessed.getD ⟨[], none⟩)⟩]
    | none => []) ++
  (match proof.permutation with
    | some pc => [⟨pc, ((List.range n).map fun i => permMat G (td i) (ed i) ζ (ov i)).filterMap id⟩]
    | none => [])

/-- Each instance's quotient chunk domains: the 2^(L + z) chunks of its quotient coset. -/
noncomputable def batchChunks (proof : BatchProof C P F K) (sizes : List Sizes) (qd : ℕ → Coset G) :
    List (List (Coset G)) :=
  (List.range proof.degree_bits.length).map fun i =>
    (List.range (2 ^ ((sizes.getD i default).log_num_quotient_chunks + cfg.zk.toNat))).map
      (chunk G hV (qd i) ((sizes.getD i default).log_num_quotient_chunks + cfg.zk.toNat))

/-- What the preprocessed round needs of the global commitment.

Each matrix names an instance with a positive width, an opening, and metadata at that matrix and degree.

Its next row is present when the AIR reads it. -/
def PreOk (airs : List (BatchAir F)) (proof : BatchProof C P F K) (sizes : List Sizes)
    (global : GlobalPreprocessed C) : Prop :=
  ∀ x ∈ global.matrix_to_instance.zipIdx, ∃ ba pm p, airs[x.1]? = some ba ∧
    (sizes.getD x.1 default).preprocessed_width ≠ 0 ∧ (proof.opened.getD x.1 default).preprocessed = some p ∧
    global.instances[x.1]? = some (some pm) ∧ pm.matrix_index = x.2 ∧
    pm.degree_bits = proof.degree_bits.getD x.1 0 ∧ (ba.opens_preprocessed_next = true → p.next.isSome)

variable {G cfg} {sizing : ℕ → AirLayout → ℕ → Option ℕ} {common : CommonData C F}

theorem trace_domains_eq {airs : List (BatchAir F)} {proof : BatchProof C P F K} {pvs : List (List F)}
    {sizes : List Sizes} {k : ℕ} (hs : ShapeOk G cfg common sizing airs proof pvs sizes k)
    {td ed : ℕ → Coset G}
    (hbase : ∀ i < proof.degree_bits.length,
      (td i).shift = 1 ∧ (td i).log_size = proof.degree_bits.getD i 0 - cfg.zk.toNat)
    (hext : ∀ i < proof.degree_bits.length, (ed i).shift = 1 ∧ (ed i).log_size = proof.degree_bits.getD i 0) :
    trace_domains G cfg proof.degree_bits =
      pure ((List.range proof.degree_bits.length).map fun i => (td i, ed i)) := by
  unfold trace_domains
  refine mapM_zipIdx _ _ _ fun i hi => ?_
  obtain ⟨db, hdb, hsz⟩ := hs.sizes_at G cfg common sizing (hs.dbs_len ▸ hi)
  have hget : proof.degree_bits[i] = db := by simpa [hi] using hdb
  have hgetD : proof.degree_bits.getD i 0 = db := by rw [List.getD_eq_getElem _ _ hi, hget]
  obtain ⟨h1, h2⟩ := hbase i hi
  obtain ⟨e1, e2⟩ := hext i hi
  have hz : cfg.zk.toNat ≤ db := by have := hsz.lo; omega
  simp only [hget, validate_at_eq hsz.lo hsz.hi hsz.word, mk_ok, pure_bind,
    Nat.pow_div hz (by norm_num : 0 < 2), natural_domain_pow G (td i) h1 (k := db - cfg.zk.toNat) (by omega),
    natural_domain_pow G (ed i) e1 (k := db) (by omega), panicOf_some]

@[simp] theorem orReject_some {α : Type} (a : α) (e : Error) : orReject (some a) e = pure a := rfl

section inst

variable {airs : List (BatchAir F)} {proof : BatchProof C P F K} {pvs : List (List F)}
  {sizes : List Sizes} {k : ℕ} (hs : ShapeOk G cfg common sizing airs proof pvs sizes k)
include hs

theorem ShapeOk.sizes_getD {i : ℕ} (hi : i < proof.degree_bits.length) :
    sizes[i]? = some (sizes.getD i default) ∧
      SizesOk G cfg common sizing (proof.degree_bits.getD i 0) (airs[i]'(hs.dbs_len ▸ hi)) i
        (sizes.getD i default) := by
  obtain ⟨db, hdb, hsz⟩ := hs.sizes_at G cfg common sizing (hs.dbs_len ▸ hi)
  have hsl : i < sizes.length := by rw [hs.sizes_length, ← hs.dbs_len]; exact hi
  have hget : proof.degree_bits[i] = db := by simpa [hi] using hdb
  refine ⟨by simp [hsl], ?_⟩
  rw [List.getD_eq_getElem _ _ hi, hget, List.getD_eq_getElem _ _ hsl]
  exact hsz

theorem ShapeOk.inst_getD {i : ℕ} (hi : i < proof.degree_bits.length) :
    InstOk cfg (airs[i]'(hs.dbs_len ▸ hi)) (pvs.getD i []) (proof.opened.getD i default)
      (sizes.getD i default) (common.lookups.getD i []) (proof.lookup_terminals.getD i none) := by
  have hi' : i < airs.length := hs.dbs_len ▸ hi
  obtain ⟨pv, ov, sz, lk, t, e1, e2, e3, e4, e5, h⟩ :=
    hs.inst (airs[i], i) (List.mem_zipIdx_iff_getElem?.2 (by simp [hi']))
  simp only [List.getD_eq_getElem?_getD, e1, e2, e3, e4, e5, Option.getD_some]
  exact check_instance_ok h

end inst

variable {airs : List (BatchAir F)} {proof : BatchProof C P F K} {pvs : List (List F)}
  {sizes : List Sizes} {k : ℕ} {td ed qd : ℕ → Coset G}

theorem quotient_domains_eq (hs : ShapeOk G cfg common sizing airs proof pvs sizes k)
    (hd : DomainsOk G g cfg proof sizes td ed qd) :
    quotient_domains G g cfg proof.degree_bits sizes
      ((List.range proof.degree_bits.length).map fun i => (td i, ed i)) =
      pure (batchChunks G hV cfg proof sizes qd) := by
  unfold quotient_domains batchChunks
  refine mapM_range _ _ _ fun i hi => ?_
  obtain ⟨hszi, hsz⟩ := hs.sizes_getD hi
  obtain ⟨q1, q2⟩ := hd.quot i hi
  obtain ⟨e1, e2⟩ := hd.ext i hi
  have hz : cfg.zk.toNat ≤ proof.degree_bits.getD i 0 := by have := hsz.lo; omega
  have hdb : proof.degree_bits[i]? = some (proof.degree_bits.getD i 0) := by
    simp [hi]
  simp only [hdb, hszi, panicOf_some, pure_bind, checked_eq hsz.chunks_word, checked_eq (hd.word i hi),
    List.getElem?_map, List.getElem?_range hi, Option.map_some,
    try_create_disjoint_domain_pow G (ed i) (qd i) g (by rw [e1, q1, one_mul])
      (n := proof.degree_bits.getD i 0 + (sizes.getD i default).log_num_quotient_chunks) q2,
    orReject_some]
  rw [split_domains_eq G hV (qd i) (by omega), panicOf_some]

theorem randomized_eq (hs : ShapeOk G cfg common sizing airs proof pvs sizes k)
    (hd : DomainsOk G g cfg proof sizes td ed qd) :
    (batchChunks G hV cfg proof sizes qd).mapM (fun doms => doms.mapM fun d =>
      panicOf (natural_domain_for_degree G (Coset.size G d * 2 ^ cfg.zk.toNat))) =
      pure ((List.range proof.degree_bits.length).map fun i =>
        List.replicate (2 ^ ((sizes.getD i default).log_num_quotient_chunks + cfg.zk.toNat)) (ed i)) := by
  unfold batchChunks
  refine Plonky3Lean.Proofs.Fri.mapM_map_eq_pure _ fun i hi => ?_
  have hi := List.mem_range.1 hi
  obtain ⟨-, hsz⟩ := hs.sizes_getD hi
  obtain ⟨q1, q2⟩ := hd.quot i hi
  obtain ⟨e1, e2⟩ := hd.ext i hi
  have hz : cfg.zk.toNat ≤ proof.degree_bits.getD i 0 := by have := hsz.lo; omega
  simp only [size_eq]
  rw [mapM_panicOf, randomized_domains G hV (ed i) (qd i) e1 e2 q2 hz, panicOf_some]

theorem zip_range {α β : Type} [Inhabited β] (n : ℕ) (f : ℕ → α) (l : List β) (hl : l.length = n) :
    ((List.range n).map f).zip l = (List.range n).map fun i => (f i, l.getD i default) := by
  refine List.ext_getElem (by simp [hl]) fun i h1 h2 => ?_
  simp only [List.length_zip, List.length_map, List.length_range, hl, min_self] at h1
  simp [List.getElem?_eq_getElem (hl ▸ h1)]

theorem zipIdx_range {α : Type} (n : ℕ) (f : ℕ → α) :
    ((List.range n).map f).zipIdx = (List.range n).map fun i => (f i, i) :=
  List.ext_getElem (by simp) fun i h1 h2 => by simp

theorem zip_replicate_left {α β : Type} (a : α) : ∀ l : List β, (List.replicate l.length a).zip l = l.map (a, ·)
  | [] => rfl
  | b :: l => by simp [List.replicate_succ, zip_replicate_left a l]

theorem getD_mem_of_lt {α : Type} [Inhabited α] {l : List α} {i : ℕ} (h : i < l.length) : l.getD i default ∈ l := by
  rw [List.getD_eq_getElem _ _ h]; exact List.getElem_mem h

theorem preprocessed_round_eq (hs : ShapeOk G cfg common sizing airs proof pvs sizes k)
    (hd : DomainsOk G g cfg proof sizes td ed qd) {gl : GlobalPreprocessed C}
    (hp : PreOk airs proof sizes gl) (ζ : K) :
    preprocessed_round G airs ζ proof sizes ((List.range proof.degree_bits.length).map fun i => (td i, ed i)) gl =
      pure ⟨gl.commitment, gl.matrix_to_instance.map fun inst =>
        preMat G ((airs[inst]?.map (·.opens_preprocessed_next)).getD false) (td inst) (ed inst) ζ
          ((proof.opened.getD inst default).preprocessed.getD ⟨[], none⟩)⟩ := by
  unfold preprocessed_round
  rw [Plonky3Lean.Proofs.Fri.mapM_eq_pure_map' (g := fun x => preMat G
    ((airs[x.1]?.map (·.opens_preprocessed_next)).getD false) (td x.1) (ed x.1) ζ
      ((proof.opened.getD x.1 default).preprocessed.getD ⟨[], none⟩)) _ fun x hx => ?_, pure_bind]
  · conv_rhs => rw [← List.zipIdx_map_fst 0 gl.matrix_to_instance, List.map_map]
    rfl
  obtain ⟨inst, mi⟩ := x
  obtain ⟨ba, pm, p, hba, hw, hpo, hpm, hmi, hdb, hnext⟩ := hp _ hx
  have hai : inst < airs.length := (List.getElem?_eq_some_iff.1 hba).1
  have hi : inst < proof.degree_bits.length := hs.dbs_len ▸ hai
  have hsl : inst < sizes.length := by rw [hs.sizes_length]; exact hai
  have hol : inst < proof.opened.length := by rw [hs.opened_len]; exact hai
  obtain ⟨e1, e2⟩ := hd.ext inst hi
  obtain ⟨t1, t2⟩ := hd.base inst hi
  simp only at hmi hdb hnext ⊢
  simp only [show sizes[inst]? = some (sizes.getD inst default) by simp [hsl], panicOf_some, pure_bind,
    hw, ↓reduceIte, show proof.opened[inst]? = some (proof.opened.getD inst default) by simp [hol], hpo,
    orReject_some, show proof.degree_bits[inst]? = some (proof.degree_bits.getD inst 0) by simp [hi], hpm,
    hmi, hdb, ne_eq, not_true_eq_false, or_self, natural_domain_pow G (ed inst) e1 e2,
    hba, Option.map_some, Option.getD_some, List.getElem?_map, List.getElem?_range hi, Coset.next_point,
    preMat]
  split_ifs with hn
  · obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 (hnext hn)
    simp [hv]
  · rfl

theorem permutation_round_eq (hs : ShapeOk G cfg common sizing airs proof pvs sizes k) (ζ : K) (pc : C) :
    permutation_round G ζ proof ((List.range proof.degree_bits.length).map fun i => (td i, ed i)) pc =
      pure ⟨pc, ((List.range proof.degree_bits.length).map fun i =>
        permMat G (td i) (ed i) ζ (proof.opened.getD i default)).filterMap id⟩ := by
  have hn : proof.opened.length = proof.degree_bits.length := by rw [hs.opened_len, hs.dbs_len]
  unfold permutation_round
  rw [zip_range _ _ _ hn, zipIdx_range, Plonky3Lean.Proofs.Fri.mapM_map_eq_pure
    (g := fun i => permMat G (td i) (ed i) ζ (proof.opened.getD i default)) _ fun i hi => ?_, pure_bind]
  have hI := hs.inst_getD (List.mem_range.1 hi)
  simp only [hI.perm_local, hI.perm_next, ne_eq, not_true_eq_false, ↓reduceIte, permMat, Coset.next_point,
    orReject_some, pure_bind]
  split_ifs <;> rfl

theorem commitments_eq (hs : ShapeOk G cfg common sizing airs proof pvs sizes k)
    (hd : DomainsOk G g cfg proof sizes td ed qd)
    (hpre : ∀ gl ∈ common.preprocessed, PreOk airs proof sizes gl) (ζ : K) :
    commitments_with_opening_points G g cfg airs ζ proof common sizes =
      pure (batchClaims G airs proof common td ed ζ, batchChunks G hV cfg proof sizes qd,
        common.preprocessed.map fun _ => cfg.zk.toNat + 2) := by
  have hn : proof.opened.length = proof.degree_bits.length := by rw [hs.opened_len, hs.dbs_len]
  unfold commitments_with_opening_points
  rw [trace_domains_eq hs hd.base hd.ext, pure_bind, zip_range _ _ _ hn, zipIdx_range]
  rw [Plonky3Lean.Proofs.Fri.mapM_map_eq_pure
    (F := fun i => (((td i, ed i), proof.opened.getD i default), i))
    (g := fun i => traceMat G ((airs[i]?.map (·.opens_main_next)).getD false) (td i) (ed i) ζ
      (proof.opened.getD i default)) _ ?htr]
  rw [quotient_domains_eq hV g hs hd]
  simp only [pure_bind, randomized_eq hV g hs hd, zipIdx_range]
  rw [Plonky3Lean.Proofs.Fri.mapM_map_eq_pure
    (F := fun i => (List.replicate (2 ^ ((sizes.getD i default).log_num_quotient_chunks + cfg.zk.toNat)) (ed i), i))
    (g := fun i => (proof.opened.getD i default).quotient_chunks.map fun v =>
      (⟨ed i, [⟨ζ, v⟩]⟩ : MatrixOpening K (Coset G))) _ ?hqc]
  case hqc =>
    intro i hi
    have hi := List.mem_range.1 hi
    have hI := hs.inst_getD hi
    obtain ⟨-, hsz⟩ := hs.sizes_getD hi
    have hol : i < proof.opened.length := by rw [hn]; exact hi
    have hlen : (proof.opened.getD i default).quotient_chunks.length =
        2 ^ ((sizes.getD i default).log_num_quotient_chunks + cfg.zk.toNat) := by
      rw [hI.chunks_len, hsz.chunks]
    simp only [show proof.opened[i]? = some (proof.opened.getD i default) by simp [hol], panicOf_some,
      pure_bind, List.length_replicate, hlen, ne_eq, not_true_eq_false, ↓reduceIte]
    rw [← hlen, zip_replicate_left, List.map_map]
    rfl
  case htr =>
    intro i hi
    have hi := List.mem_range.1 hi
    have hai : i < airs.length := hs.dbs_len ▸ hi
    have hI := hs.inst_getD hi
    simp only [List.getElem?_eq_getElem hai, Option.map_some, panicOf_some, pure_bind, Option.getD_some,
      traceMat, Coset.next_point, orReject_some]
    split_ifs with hm
    · obtain ⟨v, hv, -⟩ : ∃ v, (proof.opened.getD i default).trace_next = some v ∧ v.length = airs[i].air.width := by
        simpa [hm] using hI.next
      simp only [hv, panicOf_some, pure_bind, Option.getD_some]
    · rfl
  have hpre' : ∀ gl, common.preprocessed = some gl → PreOk airs proof sizes gl := fun gl h => hpre gl h
  rcases hr : proof.random with _ | rc
  · have hz : cfg.zk = false := by simpa [hr] using hs.random.symm
    rcases hc : common.preprocessed with _ | gl <;> rcases hp : proof.permutation with _ | pc
    all_goals try simp only [preprocessed_round_eq g hs hd (hpre' _ hc), pure_bind]
    all_goals try simp only [permutation_round_eq hs, pure_bind]
    all_goals simp [batchClaims, hr, hc, hp, hz]
  · have hz : cfg.zk = true := by simpa [hr] using hs.random.symm
    simp only
    rw [Plonky3Lean.Proofs.Fri.mapM_map_eq_pure (g := fun i => (⟨ed i, [⟨ζ,
      (proof.opened.getD i default).random.getD []⟩]⟩ : MatrixOpening K (Coset G))) _ fun i hi => ?_, pure_bind]
    · rcases hc : common.preprocessed with _ | gl <;> rcases hp : proof.permutation with _ | pc
      all_goals try simp only [preprocessed_round_eq g hs hd (hpre' _ hc), pure_bind]
      all_goals try simp only [permutation_round_eq hs, pure_bind]
      all_goals simp [batchClaims, hr, hc, hp, hz]
    · have hol : i < proof.opened.length := by rw [hn]; exact List.mem_range.1 hi
      have := hs.random_open _ (getD_mem_of_lt hol)
      rw [hz] at this
      obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 this
      simp only [hv, panicOf_some, pure_bind, Option.getD_some]

end claims

/-! ## Edge cases of the claims -/

section edges

variable {G : Gen K}

/-- With no instance and no preprocessed commitment, no claim names a matrix.

The two-adic opening argument then rejects the claims as vacuous. -/
theorem batchClaims_no_instances (airs : List (BatchAir F)) (proof : BatchProof C P F K)
    (common : CommonData C F) (td ed : ℕ → Coset G) (ζ : K) (h0 : proof.degree_bits = [])
    (hpre : common.preprocessed = none) :
    ∀ c ∈ batchClaims G airs proof common td ed ζ, c.matrices = [] := by
  intro c hc
  rcases hr : proof.random with _ | rc <;> rcases hp : proof.permutation with _ | pc <;>
    simp only [batchClaims, hr, hp, hpre, h0, List.length_nil, List.range_zero, List.map_nil, List.flatten_nil,
      List.filterMap_nil, List.nil_append, List.append_nil, List.cons_append, List.mem_cons, List.not_mem_nil,
      or_false] at hc <;> rcases hc with rfl | rfl | rfl | rfl <;> rfl

/-- An instance's permutation matrix is claimed exactly when it declares a lookup.

This holds once its openings pass the shape checks, with a positive extension degree. -/
theorem permMat_isSome_iff {cfg : Config} (hD : 0 < cfg.D) {ba : BatchAir F} {pv : List F} {ov : Opened K}
    {sz : Sizes} {lk : List (Lookup F)} {t : Option K} (hI : InstOk cfg ba pv ov sz lk t) (td ed : Coset G)
    (ζ : K) : (permMat G td ed ζ ov).isSome ↔ lk ≠ [] := by
  have h := hI.perm_local
  unfold permMat
  rcases lk with _ | ⟨l, lk⟩
  · simp_all
  · have : ov.permutation_local ≠ [] := fun he => by simp [he] at h; nlinarith
    simp [List.isEmpty_iff, this]

end edges

/-! ## One instance at zeta -/

section zeta

open Polynomial Plonky3Lean.Spec.Air Plonky3Lean.Spec.Commit Plonky3Lean.Spec.UniStark

variable (G : Gen K)

/-- An honest instance's check at zeta accepts.

Take a trace coset off which zeta lies, trace polynomials and permutation columns.

Assume the openings are their values at zeta, and the AIR reads the next row of both traces.

Assume the vanishing polynomial divides the instance's constraint polynomial C.

Assume the chunks recombine to the quotient s^n C / Z at zeta.

Then the check accepts. -/
theorem check_at_zeta_complete {D : ℕ} (hV : GenValid G) (hN : GenNested G) (h2 : (2 : K) ≠ 0)
    (B : Module.Basis (Fin D) F K) (ba : BatchAir F) (hb : ba.air.public_boundary_io = []) (i : ℕ)
    (ov : Opened K) {lookups : List (Lookup F)} {ch : List K} (hL : LaidOut ba.air ch lookups)
    {pv : List F} (hpv : pv.length = ba.air.num_public_values) (c : Coset G)
    (main prep periodic P : ℕ → K[X]) (T α : K) {ζ : K}
    (hζ : ¬ InCoset c.shift c.subgroup_generator c.log_size ζ) (qdoms : List (Coset G))
    (htl : ov.trace_local = openRow (instAssign G c main prep periodic pv) (.main 0) ba.air.width ζ)
    (htn : ov.trace_next = some (openRow (instAssign G c main prep periodic pv) (.main 1) ba.air.width ζ))
    (hpre : ov.preprocessed = some ⟨openRow (instAssign G c main prep periodic pv) (.prep 0)
        ba.air.preprocessed_width ζ, some (openRow (instAssign G c main prep periodic pv) (.prep 1)
        ba.air.preprocessed_width ζ)⟩ ∨ (ov.preprocessed = none ∧ ba.air.preprocessed_width = 0))
    (hpl : recompose_permutation B (if lookups.isEmpty then 0 else lookups.length + 1) ov.permutation_local =
      some (permOpening c.subgroup_generator ζ P lookups).current)
    (hpn : recompose_permutation B (if lookups.isEmpty then 0 else lookups.length + 1) ov.permutation_next =
      some (permOpening c.subgroup_generator ζ P lookups).next)
    (hnpc : ba.air.num_periodic_columns = ba.air.periodic_columns.length)
    (hscreen : ∀ col ∈ ba.air.periodic_columns.map (·.map (algebraMap F K)), ColumnOk (2 ^ c.log_size) col)
    (hperK : ∀ j < ba.air.num_periodic_columns, periodic j =
      periodicPoly c.shift c.subgroup_generator c.log_size ((ba.air.periodic_columns.getD j []).map (algebraMap F K)))
    (hrec : recompose_quotient_from_chunks G B qdoms ov.quotient_chunks ζ =
      some ((quotientPoly c.shift c.subgroup_generator c.log_size
        (instancePoly G ba.air c main prep periodic pv P ch T α lookups)).eval ζ))
    (hdvd : vanishing c.shift c.subgroup_generator c.log_size ∣
      instancePoly G ba.air c main prep periodic pv P ch T α lookups) :
    check_at_zeta G B ba i ov ba.air.preprocessed_width lookups (if lookups = [] then none else some T) ch pv c
      qdoms ζ α = pure () := by
  set σ := instAssign G c main prep periodic pv with hσ
  have hpv' : Coset.evaluate_periodic_columns_at G c (ba.air.periodic_columns.map (·.map (algebraMap F K)))
      (2 ^ c.log_size) ζ = some (openRow σ .periodic ba.air.num_periodic_columns ζ) := by
    rw [periodic_at G hV hN h2 c _ hscreen ζ]
    refine congrArg some (List.ext_getElem (by simp [openRow, hnpc]) fun j h1 h2' => ?_)
    have hj : j < ba.air.num_periodic_columns := by simpa [openRow] using h2'
    simp only [List.getElem_map, openRow, List.getElem_range, hσ, instAssign, starkAssign]
    rw [hperK j hj, List.getD_eq_getElem _ _ (by omega)]
  have hpre' : (ov.preprocessed.map (·.current)).getD [] = openRow σ (.prep 0) ba.air.preprocessed_width ζ ∧
      (ov.preprocessed.bind (·.next)).getD (List.replicate ba.air.preprocessed_width 0) =
        openRow σ (.prep 1) ba.air.preprocessed_width ζ := by
    rcases hpre with h | ⟨h, h0⟩
    · simp [h]
    · simp [h, h0, openRow]
  have hperm : (if lookups = [] then none else some T).toList = if lookups = [] then [] else [T] := by
    split_ifs <;> rfl
  have hcomp := verify_constraints_with_lookups_complete G hV h2 hb c main prep periodic hpv P hL T α hζ hdvd
  simp only [List.isEmpty_iff] at hpl hpn
  unfold check_at_zeta
  simp only [hrec, panicOf_some, pure_bind, List.isEmpty_iff, hpl, hpn, htn, Option.getD_some, size_eq,
    (new_ok_iff _ _).2 hscreen, hpv', hpre'.1, hpre'.2, hperm, htl]
  rw [hcomp, panicOf_some, pure_bind]

/-- An honest instance at zeta, with base trace coset c, trace polynomials and permutation columns P.

- The AIR binds its public values by constraints, and its lookups are laid out.
- Zeta lies off c, and the AIR reads the next row of both traces.
- The openings are the polynomials' values at zeta, the permutation rows flattened over the basis.
- The periodic columns screen, with their periodic polynomials.
- The chunks recombine to the quotient s^n C / Z at zeta, and Z divides the constraint polynomial C.
- A terminal T is present exactly when the instance has lookups. -/
structure Honest {D : ℕ} (B : Module.Basis (Fin D) F K) (ba : BatchAir F) (ov : Opened K)
    (lookups : List (Lookup F)) (t : Option K) (ch : List K) (pv : List F) (c : Coset G)
    (qdoms : List (Coset G)) (ζ α : K) (main prep periodic P : ℕ → K[X]) (T : K) : Prop where
  boundary : ba.air.public_boundary_io = []
  laid : LaidOut ba.air ch lookups
  pv_len : pv.length = ba.air.num_public_values
  off : ¬ InCoset c.shift c.subgroup_generator c.log_size ζ
  trace_local : ov.trace_local = openRow (instAssign G c main prep periodic pv) (.main 0) ba.air.width ζ
  trace_next : ov.trace_next = some (openRow (instAssign G c main prep periodic pv) (.main 1) ba.air.width ζ)
  pre : ov.preprocessed = some ⟨openRow (instAssign G c main prep periodic pv) (.prep 0)
      ba.air.preprocessed_width ζ, some (openRow (instAssign G c main prep periodic pv) (.prep 1)
      ba.air.preprocessed_width ζ)⟩ ∨ (ov.preprocessed = none ∧ ba.air.preprocessed_width = 0)
  perm_local : recompose_permutation B (if lookups.isEmpty then 0 else lookups.length + 1) ov.permutation_local =
    some (permOpening c.subgroup_generator ζ P lookups).current
  perm_next : recompose_permutation B (if lookups.isEmpty then 0 else lookups.length + 1) ov.permutation_next =
    some (permOpening c.subgroup_generator ζ P lookups).next
  npc : ba.air.num_periodic_columns = ba.air.periodic_columns.length
  screen : ∀ col ∈ ba.air.periodic_columns.map (·.map (algebraMap F K)), ColumnOk (2 ^ c.log_size) col
  periodic_eq : ∀ j < ba.air.num_periodic_columns, periodic j =
    periodicPoly c.shift c.subgroup_generator c.log_size ((ba.air.periodic_columns.getD j []).map (algebraMap F K))
  recombine : recompose_quotient_from_chunks G B qdoms ov.quotient_chunks ζ =
    some ((quotientPoly c.shift c.subgroup_generator c.log_size
      (instancePoly G ba.air c main prep periodic pv P ch T α lookups)).eval ζ)
  dvd : vanishing c.shift c.subgroup_generator c.log_size ∣
    instancePoly G ba.air c main prep periodic pv P ch T α lookups
  terminal : t = if lookups = [] then none else some T

theorem Honest.check {D : ℕ} (hV : GenValid G) (hN : GenNested G) (h2 : (2 : K) ≠ 0)
    {B : Module.Basis (Fin D) F K} {ba : BatchAir F} {ov : Opened K} {lookups : List (Lookup F)} {t : Option K}
    {ch : List K} {pv : List F} {c : Coset G} {qdoms : List (Coset G)} {ζ α : K} {main prep periodic P : ℕ → K[X]}
    {T : K} (h : Honest G B ba ov lookups t ch pv c qdoms ζ α main prep periodic P T) (i : ℕ) :
    check_at_zeta G B ba i ov ba.air.preprocessed_width lookups t ch pv c qdoms ζ α = pure () := by
  rw [h.terminal]
  exact check_at_zeta_complete G hV hN h2 B ba h.boundary i ov h.laid h.pv_len c main prep periodic P T α h.off
    qdoms h.trace_local h.trace_next h.pre h.perm_local h.perm_next h.npc h.screen h.periodic_eq h.recombine h.dvd

end zeta

section all

variable {G : Gen K} {g : K} {cfg : Config} {sizing : ℕ → AirLayout → ℕ → Option ℕ} {common : CommonData C F}
  {airs : List (BatchAir F)} {proof : BatchProof C P F K} {pvs : List (List F)} {sizes : List Sizes} {k : ℕ}
  {td ed qd : ℕ → Coset G}

/-- Every instance's check at zeta accepts when each one does, on its base trace domain. -/
theorem check_all_eq {D : ℕ} (B : Module.Basis (Fin D) F K) (hs : ShapeOk G cfg common sizing airs proof pvs sizes k)
    (hd : DomainsOk G g cfg proof sizes td ed qd) {ch : List (List K)} (hch : ch.length = airs.length)
    {qdoms : List (List (Coset G))} (hq : qdoms.length = airs.length) (ζ α : K)
    (h : ∀ i (hi : i < airs.length), check_at_zeta G B airs[i] i (proof.opened.getD i default)
      (sizes.getD i default).preprocessed_width (common.lookups.getD i []) (proof.lookup_terminals.getD i none)
      (ch.getD i []) (pvs.getD i []) (td i) (qdoms.getD i []) ζ α = pure ()) :
    check_all_at_zeta G B cfg airs proof pvs common sizes ch qdoms ζ α = pure () := by
  have hsl := hs.sizes_length
  have htds : sizes.mapM (fun sz => panicOf (natural_domain_for_degree G (sz.ext_size / 2 ^ cfg.zk.toNat))) =
      pure ((List.range airs.length).map td) := by
    rw [mapM_eq_pure, List.forall₂_iff_get]
    refine ⟨by simp [hsl], fun i h1 h2 => ?_⟩
    have hi : i < proof.degree_bits.length := by rw [hs.dbs_len, ← hsl]; exact h1
    obtain ⟨-, hsz⟩ := hs.sizes_getD hi
    obtain ⟨t1, t2⟩ := hd.base i hi
    have hz : cfg.zk.toNat ≤ proof.degree_bits.getD i 0 := by have := hsz.lo; omega
    simp only [List.get_eq_getElem, List.getElem_map, List.getElem_range, ← getElem_eq_getD h1] at hsz ⊢
    rw [hsz.ext, Nat.pow_div hz (by norm_num), natural_domain_pow G (td i) t1 t2, panicOf_some]
  unfold check_all_at_zeta
  rw [htds, pure_bind, forM_eq_pure]
  rintro ⟨ba, i⟩ hx
  obtain ⟨hi, rfl⟩ : ∃ hi : i < airs.length, airs[i] = ba := by
    exact List.getElem?_eq_some_iff.1 (List.mem_zipIdx_iff_getElem?.1 hx)
  have get : ∀ {α : Type} [Inhabited α] (l : List α), l.length = airs.length →
      l[i]? = some (l.getD i default) := fun l hl => by simp [hl ▸ hi]
  simp only [get _ (hs.opened_len), get _ (by rw [hsl]), panicOf_some, pure_bind]
  simp only [show common.lookups[i]? = some (common.lookups.getD i []) by simp [hs.lookups_len ▸ hi],
    show proof.lookup_terminals[i]? = some (proof.lookup_terminals.getD i none) by simp [hs.terminals_len ▸ hi],
    show ch[i]? = some (ch.getD i []) by simp [hch ▸ hi], show pvs[i]? = some (pvs.getD i []) by simp [hs.pvs_len ▸ hi],
    show qdoms[i]? = some (qdoms.getD i []) by simp [hq ▸ hi], List.getElem?_map, List.getElem?_range hi,
    Option.map_some, panicOf_some, pure_bind]
  exact h i hi

end all

/-! ## The transcript -/

theorem adapt_ok {ε ε' α : Type} {x : ExceptT ε Option α} {a : α} (f : ε → ε') (h : x.run = some (.ok a)) :
    (x.adapt f : ExceptT ε' Option α) = pure a := by
  obtain rfl : x = ExceptT.mk (some (.ok a)) := h
  rfl

section transcript

variable {sp : BatchSponge F K C Com S} {shape : BatchShape} {proof : BatchProof C P F K}
  {pvs : List (List F)} {common : CommonData C F}

/-- The state the lookup phase starts from: the seed, then the degree bits, the main commitment,
the public values and the preprocessed commitment. -/
def preLookupState (sp : BatchSponge F K C Com S) (shape : BatchShape) (proof : BatchProof C P F K)
    (pvs : List (List F)) (common : CommonData C F) : S :=
  preprocessed_phase sp (main_phase sp (instance_bindings sp (sp.seed shape) proof.degree_bits) proof.main pvs)
    (common.preprocessed.map (·.commitment))

/-- The state the out-of-domain phase starts from, after the lookup phase reached s. -/
def preOodState (sp : BatchSponge F K C Com S) (proof : BatchProof C P F K) (s : S) : S :=
  quotient_phase sp (permutation_phase sp s proof.permutation (proof.lookup_terminals.filterMap id)).2
    proof.quotient_chunks proof.random

/-- The transcript accepts when both grinds accept, with alpha drawn after the terminals. -/
theorem replay_eq {ch : List (List K)} {s1 : S}
    (hlk : (lookup_phase sp shape (preLookupState sp shape proof pvs common) common.lookups
      proof.lookup_pow_witness).run = some (.ok (ch, s1)))
    {ζ : K} {s : S} (hood : (ood_phase sp shape (preOodState sp proof s1) proof.ood_pow_witness).run =
      some (.ok (ζ, s))) :
    replay sp shape proof pvs common =
      pure (ch, (permutation_phase sp s1 proof.permutation (proof.lookup_terminals.filterMap id)).1, ζ, s) := by
  unfold preLookupState at hlk
  unfold preOodState at hood
  unfold replay
  dsimp only
  rw [adapt_ok _ hlk, pure_bind]
  dsimp only
  rw [adapt_ok _ hood, pure_bind]

theorem lay_out_length {all : List (List (Lookup F))} {α β : K} {ch : List (List K)}
    (h : lay_out_lookup_challenges 2 all α β = some ch) : ch.length = all.length := by
  rcases hb : busIds all with _ | ⟨ids, st⟩
  · simp [lay_out_lookup_challenges, hb] at h
  rw [lay_out_eq hb] at h
  cases h
  have := congrArg List.length (busIds_spec hb).1
  simpa using this

/-- The lookup phase returns one challenge list per instance. -/
theorem lookup_phase_length {s s' : S} {all : List (List (Lookup F))} {w : Option F} {ch : List (List K)}
    (h : (p3_batch_stark.verify.mirror.lookup_phase sp shape s all w).run = some (.ok (ch, s'))) :
    ch.length = all.length := by
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
    exact lay_out_length hlay
  · simp only [hl, Bool.false_eq_true, not_false_eq_true, ↓reduceIte] at h'
    rcases w with _ | w
    · cases h'; simp
    · exact absurd h' (tne _ _)

end transcript

/-! ## Acceptance -/

/-- The verifier accepts when every step accepts. -/
theorem verify_accepts {D : ℕ} (G : Gen K) (g : K) (B : Module.Basis (Fin D) F K) (cfg : Config)
    (airs : List (BatchAir F)) (sizing : ℕ → AirLayout → ℕ → Option ℕ) (sp : BatchSponge F K C Com S)
    (pcs : List (p3_fri.verifier.mirror.Claim G C) → Option ℕ → S → Option (Except PE Unit))
    (proof : BatchProof C P F K) (pvs : List (List F)) (common : CommonData C F)
    (hb : ∀ ba ∈ airs, ba.air.public_boundary_io = []) {sizes : List Sizes} {k : ℕ}
    (hshape : check_shape G cfg airs sizing proof pvs common = pure (sizes, k))
    {ch : List (List K)} {α ζ : K} {s : S}
    (hrep : replay sp (shapeOf cfg airs common sizes k) proof pvs common = pure (ch, α, ζ, s))
    {claims : List (p3_fri.verifier.mirror.Claim G C)} {qdoms : List (List (Coset G))} {idx : Option ℕ}
    (hcl : commitments_with_opening_points G g cfg airs ζ proof common sizes = pure (claims, qdoms, idx))
    (hpcs : pcs claims idx s = some (.ok ()))
    (hz : check_all_at_zeta G B cfg airs proof pvs common sizes ch qdoms ζ α = pure ())
    (hsum : verify_terminal_sum proof.lookup_terminals = true) :
    verify_batch G g B cfg airs sizing sp pcs proof pvs common = some (.ok ()) := by
  have hany : airs.any (fun ba => !ba.air.public_boundary_io.isEmpty) = false := by
    simpa using fun ba h => hb ba h
  unfold verify_batch
  simp only [hany, Bool.false_eq_true, ↓reduceIte, pure_bind, hshape, hrep, hcl, hpcs, panicOf_some,
    hz, hsum, Bool.not_true]
  rfl

/-! ## Recombining the chunks -/

section chunks

open Polynomial

variable {G : Gen K} (hV : GenValid G) {g : K} {cfg : Config} {sizing : ℕ → AirLayout → ℕ → Option ℕ}
  {common : CommonData C F} {airs : List (BatchAir F)} {proof : BatchProof C P F K} {pvs : List (List F)}
  {sizes : List Sizes} {k : ℕ} {td ed qd : ℕ → Coset G}

theorem batchChunks_getD {i : ℕ} (hi : i < proof.degree_bits.length) :
    (batchChunks G hV cfg proof sizes qd).getD i [] =
      (List.range (2 ^ ((sizes.getD i default).log_num_quotient_chunks + cfg.zk.toNat))).map
        (chunk G hV (qd i) ((sizes.getD i default).log_num_quotient_chunks + cfg.zk.toNat)) := by
  simp [batchChunks, List.getD_eq_getElem?_getD, hi]

/-- Instance i's chunks, opened at their interpolants of Q, recombine to Q at zeta.

Here Q has degree below the quotient coset's order. -/
theorem recombine_chunks {D : ℕ} (B : Module.Basis (Fin D) F K) (hN : GenNested G)
    (hs : ShapeOk G cfg common sizing airs proof pvs sizes k) (hd : DomainsOk G g cfg proof sizes td ed qd)
    {i : ℕ} (hi : i < proof.degree_bits.length) (Q : K[X]) (hQ : Q.degree < (2 ^ (qd i).log_size : ℕ))
    (ζ : K) (chunks : List (List K))
    (hlen : chunks.length = 2 ^ ((sizes.getD i default).log_num_quotient_chunks + cfg.zk.toNat))
    (hv : ∀ j (hj : j < 2 ^ ((sizes.getD i default).log_num_quotient_chunks + cfg.zk.toNat)),
      from_ext_basis_coefficients B (chunks[j]'(hlen ▸ hj)) =
        some ((chunkInterp hV (qd i) ((sizes.getD i default).log_num_quotient_chunks + cfg.zk.toNat) Q j).eval ζ)) :
    recompose_quotient_from_chunks G B ((batchChunks G hV cfg proof sizes qd).getD i []) chunks ζ =
      some (Q.eval ζ) := by
  obtain ⟨-, hsz⟩ := hs.sizes_getD hi
  have := hsz.lo
  rw [batchChunks_getD hV hi]
  exact recompose_quotient hV (qd i) _ B hN (by rw [(hd.quot i hi).2]; omega) Q hQ chunks hlen hv

/-- Instance i's masked chunks recombine to Q at zeta, as the unmasked ones do.

Chunk j opens to its interpolant plus Z_j times its mask, the last mask balancing the others. -/
theorem recombine_chunks_masked {D : ℕ} (B : Module.Basis (Fin D) F K) (hN : GenNested G)
    (hs : ShapeOk G cfg common sizing airs proof pvs sizes k) (hd : DomainsOk G g cfg proof sizes td ed qd)
    {i : ℕ} (hi : i < proof.degree_bits.length) (Q : K[X]) (hQ : Q.degree < (2 ^ (qd i).log_size : ℕ))
    (t : ℕ → K[X]) (ζ : K) (chunks : List (List K))
    (hlen : chunks.length = 2 ^ ((sizes.getD i default).log_num_quotient_chunks + cfg.zk.toNat))
    (hv : ∀ j (hj : j < 2 ^ ((sizes.getD i default).log_num_quotient_chunks + cfg.zk.toNat)),
      from_ext_basis_coefficients B (chunks[j]'(hlen ▸ hj)) =
        some ((chunkInterp hV (qd i) ((sizes.getD i default).log_num_quotient_chunks + cfg.zk.toNat) Q j +
          chunkZ hV (qd i) ((sizes.getD i default).log_num_quotient_chunks + cfg.zk.toNat) j *
            mask hV (qd i) ((sizes.getD i default).log_num_quotient_chunks + cfg.zk.toNat) t j).eval ζ)) :
    recompose_quotient_from_chunks G B ((batchChunks G hV cfg proof sizes qd).getD i []) chunks ζ =
      some (Q.eval ζ) := by
  obtain ⟨-, hsz⟩ := hs.sizes_getD hi
  have := hsz.lo
  rw [batchChunks_getD hV hi]
  exact recompose_quotient_masked hV (qd i) _ B hN (by rw [(hd.quot i hi).2]; omega) Q hQ t ζ chunks hlen hv

end chunks

/-! ## Completeness -/

open Polynomial

/-- Completeness of the batch verifier, given each instance's chunk recombination.

Take n instances, each with its base trace coset, extended trace domain and quotient coset.

Assume the shape checks accept, and the common data's preprocessed widths are the AIRs'.

Assume both grinds accept, drawing the lookup challenges, alpha and zeta.

Assume each instance is honest at zeta, and the terminals sum to zero.

Assume the opening argument accepts the claims at zeta.

Then the verifier accepts. -/
theorem verify_complete {D : ℕ} (G : Gen K) (hV : GenValid G) (hN : GenNested G) (h2 : (2 : K) ≠ 0) (g : K)
    (B : Module.Basis (Fin D) F K) (cfg : Config) (airs : List (BatchAir F))
    (sizing : ℕ → AirLayout → ℕ → Option ℕ) (sp : BatchSponge F K C Com S)
    (pcs : List (p3_fri.verifier.mirror.Claim G C) → Option ℕ → S → Option (Except PE Unit))
    (proof : BatchProof C P F K) (pvs : List (List F)) (common : CommonData C F) {sizes : List Sizes} {k : ℕ}
    (hshape : check_shape G cfg airs sizing proof pvs common = pure (sizes, k))
    {td ed qd : ℕ → Coset G} (hd : DomainsOk G g cfg proof sizes td ed qd)
    (hpre : ∀ gl ∈ common.preprocessed, PreOk airs proof sizes gl)
    (hcw : ∀ i (hi : i < airs.length), (sizes.getD i default).preprocessed_width = airs[i].air.preprocessed_width)
    {ch : List (List K)} {s1 : S}
    (hlk : (p3_batch_stark.verify.mirror.lookup_phase sp (shapeOf cfg airs common sizes k)
      (preLookupState sp (shapeOf cfg airs common sizes k) proof pvs common) common.lookups
      proof.lookup_pow_witness).run = some (.ok (ch, s1)))
    {ζ : K} {s : S}
    (hood : (p3_batch_stark.verify.mirror.ood_phase sp (shapeOf cfg airs common sizes k) (preOodState sp proof s1)
      proof.ood_pow_witness).run = some (.ok (ζ, s)))
    (main prep periodic Pc : ℕ → ℕ → K[X]) (T : ℕ → K)
    (hhon : ∀ i (hi : i < airs.length), Honest G B airs[i] (proof.opened.getD i default) (common.lookups.getD i [])
      (proof.lookup_terminals.getD i none) (ch.getD i []) (pvs.getD i []) (td i)
      ((batchChunks G hV cfg proof sizes qd).getD i []) ζ
      (permutation_phase sp s1 proof.permutation (proof.lookup_terminals.filterMap id)).1
      (main i) (prep i) (periodic i) (Pc i) (T i))
    (hsum : verify_terminal_sum proof.lookup_terminals = true)
    (hpcs : pcs (batchClaims G airs proof common td ed ζ) (common.preprocessed.map fun _ => cfg.zk.toNat + 2) s =
      some (.ok ())) :
    verify_batch G g B cfg airs sizing sp pcs proof pvs common = some (.ok ()) := by
  have hs := check_shape_pure G cfg common sizing hshape
  have hb : ∀ ba ∈ airs, ba.air.public_boundary_io = [] := fun ba hba => by
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hba
    exact (hhon i hi).boundary
  refine verify_accepts G g B cfg airs sizing sp pcs proof pvs common hb hshape (replay_eq hlk hood)
    (commitments_eq hV g hs hd hpre ζ) hpcs ?_ hsum
  refine check_all_eq B hs hd ?_ ?_ ζ _ fun i hi => ?_
  · rw [lookup_phase_length hlk, hs.lookups_len]
  · simp [batchChunks, hs.dbs_len]
  · rw [hcw i hi]
    exact (hhon i hi).check G hV hN h2 i

section merkle

open Plonky3Lean.Proofs.Fri Plonky3Lean.Proofs.MerkleTree Plonky3Lean.Spec.Fri p3_fri.mirror
  p3_fri.config.mirror p3_fri.transcript.mirror p3_fri.verifier.mirror p3_commit.pcs.univariate.mirror

variable {DI DF : Type}

/-- Completeness over Merkle commitments and two-adic FRI.

The FRI prover is honest on the verifier's claims at zeta. -/
theorem verify_complete_merkle {D : ℕ} (G : Gen K) (hV : GenValid G) (hN : GenNested G) (h2 : (2 : K) ≠ 0) (g : K)
    (B : Module.Basis (Fin D) F K) (cfg : Config) (airs : List (BatchAir F))
    (sizing : ℕ → AirLayout → ℕ → Option ℕ)
    (hashI : List (List K) → DI) (cmpI : List DI → DI) (zI : DI) (capI : ℕ)
    (hashF : List (List K) → DF) (cmpF : List DF → DF) (zF : DF) (capF : ℕ) (params : FriParameters)
    (commit_of : C → (merkleOps hashI cmpI zI capI).Commitment)
    (sp : BatchSponge F K C (merkleOps hashF cmpF zF capF).Commitment S)
    (proof : BatchProof C (FriProof K (merkleOps hashF cmpF zF capF).Commitment (merkleOps hashF cmpF zF capF).MultiProof
      (merkleOps hashI cmpI zI capI).MultiProof) F K) (pvs : List (List F)) (common : CommonData C F) {sizes : List Sizes} {k : ℕ}
    (hshape : check_shape G cfg airs sizing proof pvs common = pure (sizes, k))
    {td ed qd : ℕ → p3_commit.domain.mirror.Coset G} (hd : DomainsOk G g cfg proof sizes td ed qd)
    (hpre : ∀ gl ∈ common.preprocessed, PreOk airs proof sizes gl)
    (hcw : ∀ i (hi : i < airs.length), (sizes.getD i default).preprocessed_width = airs[i].air.preprocessed_width)
    {ch : List (List K)} {s1 : S}
    (hlk : (p3_batch_stark.verify.mirror.lookup_phase sp (shapeOf cfg airs common sizes k)
      (preLookupState sp (shapeOf cfg airs common sizes k) proof pvs common) common.lookups
      proof.lookup_pow_witness).run = some (.ok (ch, s1)))
    {ζ : K} {s : S}
    (hood : (p3_batch_stark.verify.mirror.ood_phase sp (shapeOf cfg airs common sizes k) (preOodState sp proof s1)
      proof.ood_pow_witness).run = some (.ok (ζ, s)))
    (main prep periodic Pc : ℕ → ℕ → K[X]) (T : ℕ → K)
    (hhon : ∀ i (hi : i < airs.length), Honest G B airs[i] (proof.opened.getD i default) (common.lookups.getD i [])
      (proof.lookup_terminals.getD i none) (ch.getD i []) (pvs.getD i []) (td i)
      ((batchChunks G hV cfg proof sizes qd).getD i []) ζ
      (permutation_phase sp s1 proof.permutation (proof.lookup_terminals.filterMap id)).1
      (main i) (prep i) (periodic i) (Pc i) (T i))
    (hsum : verify_terminal_sum proof.lookup_terminals = true)
    (hM : MerkleHonest G g hashI cmpI zI capI hashF cmpF zF capF sp.sponge params
      (batchClaims G airs proof common td ed ζ) proof.opening_proof s commit_of) :
    verify_batch G g B cfg airs sizing sp
      (fun cl _ st => (p3_fri.two_adic_pcs.mirror.verify G g (merkleOps hashF cmpF zF capF)
        (merkleOps hashI cmpI zI capI) sp.sponge params cl proof.opening_proof st commit_of).run)
      proof pvs common = some (.ok ()) :=
  verify_complete G hV hN h2 g B cfg airs sizing sp _ proof pvs common hshape hd hpre hcw hlk hood main prep periodic Pc T hhon hsum
    (merkle_accepts G hV hN h2 g hashI cmpI zI capI hashF cmpF zF capF sp.sponge params _ proof.opening_proof s
      commit_of hM)

/-- Completeness of the zero-knowledge path, over the hiding FRI scheme and Merkle commitments.

- The verifier's claims are the public part of a randomized batch.
- The proof's hidden values are the rest of it.
- The FRI prover is honest on the randomized batch. -/
theorem verify_complete_hiding {D : ℕ} (G : Gen K) (hV : GenValid G) (hN : GenNested G) (h2 : (2 : K) ≠ 0) (g : K)
    (B : Module.Basis (Fin D) F K) (cfg : Config) (airs : List (BatchAir F))
    (sizing : ℕ → AirLayout → ℕ → Option ℕ)
    (hashI : List (List K) → DI) (cmpI : List DI → DI) (zI : DI) (capI : ℕ)
    (hashF : List (List K) → DF) (cmpF : List DF → DF) (zF : DF) (capF : ℕ) (params : FriParameters)
    (commit_of : C → (merkleOps hashI cmpI zI capI).Commitment) (r : ℕ)
    (sp : BatchSponge F K C (merkleOps hashF cmpF zF capF).Commitment S)
    (proof : BatchProof C (List (List (List (List K))) × FriProof K (merkleOps hashF cmpF zF capF).Commitment (merkleOps hashF cmpF zF capF).MultiProof
      (merkleOps hashI cmpI zI capI).MultiProof) F K) (pvs : List (List F)) (common : CommonData C F) {sizes : List Sizes} {k : ℕ}
    (hshape : check_shape G cfg airs sizing proof pvs common = pure (sizes, k))
    {td ed qd : ℕ → p3_commit.domain.mirror.Coset G} (hd : DomainsOk G g cfg proof sizes td ed qd)
    (hpre : ∀ gl ∈ common.preprocessed, PreOk airs proof sizes gl)
    (hcw : ∀ i (hi : i < airs.length), (sizes.getD i default).preprocessed_width = airs[i].air.preprocessed_width)
    {ch : List (List K)} {s1 : S}
    (hlk : (p3_batch_stark.verify.mirror.lookup_phase sp (shapeOf cfg airs common sizes k)
      (preLookupState sp (shapeOf cfg airs common sizes k) proof pvs common) common.lookups
      proof.lookup_pow_witness).run = some (.ok (ch, s1)))
    {ζ : K} {s : S}
    (hood : (p3_batch_stark.verify.mirror.ood_phase sp (shapeOf cfg airs common sizes k) (preOodState sp proof s1)
      proof.ood_pow_witness).run = some (.ok (ζ, s)))
    (main prep periodic Pc : ℕ → ℕ → K[X]) (T : ℕ → K)
    (hhon : ∀ i (hi : i < airs.length), Honest G B airs[i] (proof.opened.getD i default) (common.lookups.getD i [])
      (proof.lookup_terminals.getD i none) (ch.getD i []) (pvs.getD i []) (td i)
      ((batchChunks G hV cfg proof sizes qd).getD i []) ζ
      (permutation_phase sp s1 proof.permutation (proof.lookup_terminals.filterMap id)).1
      (main i) (prep i) (periodic i) (Pc i) (T i))
    (hsum : verify_terminal_sum proof.lookup_terminals = true)
    (full : List (p3_fri.verifier.mirror.Claim G C))
    (hcl : batchClaims G airs proof common td ed ζ =
      (hideClaims r (common.preprocessed.map fun _ => cfg.zk.toNat + 2) full).1)
    (hrand : proof.opening_proof.1 = (hideClaims r (common.preprocessed.map fun _ => cfg.zk.toNat + 2) full).2)
    (hidx : ∀ i, common.preprocessed.map (fun _ => cfg.zk.toNat + 2) = some i → i < full.length)
    (hDr : cfg.D ≤ r)
    (hbud : ∀ cl ∈ full, ∀ m ∈ cl.matrices, ∃ req,
      p3_fri.hiding_pcs.mirror.hiding_budget params.num_queries cfg.D m.points.length = some req ∧
        req ≤ m.domain.size / 2)
    (hhid : ∀ e ∈ full.zipIdx, ∀ m ∈ e.1.matrices, ∀ p ∈ m.points,
      hiddenCount r (common.preprocessed.map fun _ => cfg.zk.toNat + 2) e.2 ≤ p.values.length)
    (hM : MerkleHonest G g hashI cmpI zI capI hashF cmpF zF capF sp.sponge params full
      proof.opening_proof.2 s commit_of) :
    verify_batch G g B cfg airs sizing sp
      (fun cl idx st => (p3_fri.hiding_pcs.mirror.verify_hiding G g (merkleOps hashF cmpF zF capF)
        (merkleOps hashI cmpI zI capI) sp.sponge params cfg.D r idx cl proof.opening_proof.1
        proof.opening_proof.2 st commit_of).run)
      proof pvs common = some (.ok ()) := by
  have hacc := verify_hiding_complete G g _ _ sp.sponge params cfg.D r _ full proof.opening_proof.2 s
    commit_of hidx hDr hbud hhid (by
      have := merkle_accepts G hV hN h2 g hashI cmpI zI capI hashF cmpF zF capF sp.sponge params full
        proof.opening_proof.2 s commit_of hM
      exact ExceptT.ext (by rw [this]; rfl))
  refine verify_complete G hV hN h2 g B cfg airs sizing sp _ proof pvs common hshape hd hpre hcw hlk hood main prep periodic Pc T hhon hsum ?_
  simp only [hcl, hrand, hacc]
  rfl

end merkle

end Plonky3Lean.Proofs.BatchStark.EndToEnd
