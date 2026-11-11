module

public import Plonky3Lean.Proofs.BinaryPcs.Complete
public import Plonky3Lean.Proofs.BinaryPcs.Walk
public import Plonky3Lean.Proofs.BinaryPcs.Extracted

@[expose] public section

/-!
# p3-binary-pcs: claims

Five items are extracted:

- the fold of a pair
- the schedule's constructor
- its change of folding factor
- its batch count
- the transcript shape

Their claims assume a 64-bit word, and that the field instances compute the operations they name.

Each one returns what its transcription computes, so the transcription's claims cover the shipped code.

The query count comes from a floating-point bound of p3-security, and is assumed.

The coset fold and the verifier's query phase are transcribed over fields of characteristic 2.

The specification is the folding of FRI-Binius (Diamond and Posen, eprint 2024/504, section 4).

It runs over the additive NTT of Lin, Chung and Han:

```text
    codeword of d over S_l:   ntt(d)_i = sum_k X_k(point(i)) d_k
    fold at beta:             (lo, hi) -> f_0 + beta (f_0 + f_1)
                              f_1 = lo + hi,  f_0 = lo + point(2 j) f_1
    bound coefficients:       d'_k = (1 - beta) d_(2k) + beta d_(2k+1)
```

The security model is that of p3-security (eprint 2024/1553, Appendix A, Theorem 8):

- each fold over words of N symbols costs (N + 1) / |K|
- each sumcheck round costs 2 / |K|

The sponge is modelled by its history.

The Merkle schemes and the query draw are functions of what they read.

A panic is modelled as a missing result.
-/

open Finset Plonky3Lean.Spec.BinaryDft Plonky3Lean.Proofs.BinaryDft Plonky3Lean.Proofs.BinaryPcs
open p3_sumcheck.mirror p3_binary_dft.mirror p3_binary_pcs.mirror p3_binary_pcs.params.mirror
open p3_binary_pcs.transcript.mirror p3_binary_pcs.fold.mirror p3_binary_pcs.verifier.mirror

set_option linter.unusedSectionVars false

namespace Plonky3Lean.Claims.BinaryPcs

/-! ## The schedule -/

/-- The constructor accepts a schedule exactly when its invariants hold:

- the arity and the rate are nonzero
- the factor lies between 1 and the arity
- the codeword fits in a word and in the alphabet's domain
- the challenge width is priced
- grinding stays below the witness capacity and the target
- the field leaves room for the target. -/
theorem try_new_with_folding.ok (Q : ℕ → ℕ → ℕ → ℕ) (fBits efBits n : ℕ) (params : BinaryPcsParams)
    (lff : ℕ) (c : BinaryPcsConfig) :
    try_new_with_folding Q fBits efBits n params lff = some (.ok c) ↔
      c = ⟨params, fBits, efBits, n, Q params.security_level params.log_inv_rate params.pow_bits, lff⟩ ∧
        Inv c :=
  try_new_with_folding_ok Q fBits efBits n params lff c

/-- The constructor panics only when the alphabet is narrower than a byte.

No encodable level is that narrow. -/
theorem try_new_with_folding.panics (Q : ℕ → ℕ → ℕ → ℕ) (fBits efBits n : ℕ)
    (params : BinaryPcsParams) (lff : ℕ) :
    try_new_with_folding Q fBits efBits n params lff = none ↔
      n + params.log_inv_rate < 64 ∧ n ≠ 0 ∧ 0 < lff ∧ lff ≤ n ∧ n + params.log_inv_rate ≤ fBits ∧
        fBits < 8 :=
  try_new_with_folding_none Q fBits efBits n params lff

/-- Changing the folding factor of an accepted schedule never panics.

It accepts exactly the factors that keep the invariants. -/
theorem try_with_folding {c : BinaryPcsConfig} (h : Inv c) (lff : ℕ) :
    (∃ r, c.try_with_folding lff = some r) ∧
      ∀ c', c.try_with_folding lff = some (.ok c') ↔ c' = { c with log_folding_factor := lff } ∧ Inv c' :=
  h.try_with_folding lff

/-- On an accepted schedule, the security model exists. -/
theorem security_regime {c : BinaryPcsConfig} (h : Inv c) : c.security_regime = some (regimeOf c) :=
  h.security_regime

/-- The transcript shape of an accepted schedule never panics.

It has n + r - lff index bits and min(q, 2^(n+r-lff)) distinct pairs. -/
theorem shape {c : BinaryPcsConfig} (h : Inv c) :
    BinaryPcsShape.new c = some ⟨c.num_variables, c.log_folding_factor,
      (c.num_variables + c.log_folding_factor - 1) / c.log_folding_factor - 1,
      2 ^ c.params.log_inv_rate, c.params.pow_bits,
      c.num_variables + c.params.log_inv_rate - c.log_folding_factor,
      min c.num_queries (2 ^ (c.num_variables + c.params.log_inv_rate - c.log_folding_factor))⟩ :=
  h.shape

/-- For b below ceil(n / lff), batch b starts at variable b lff and folds min(lff, n - b lff) variables. -/
theorem fold_batches {c : BinaryPcsConfig} (h : Inv c) :
    c.fold_batches = some ((List.range ((c.num_variables + c.log_folding_factor - 1) / c.log_folding_factor)).map
      fun b => (b * c.log_folding_factor, min c.log_folding_factor (c.num_variables - b * c.log_folding_factor))) :=
  h.fold_batches

/-- The fold and sumcheck errors fit the target.

The bound is sum_j (2^(r+j+1) + 1 + 2) 2^(lambda + reserve) <= 2^K.

One bit is reserved unless every coset is queried. -/
theorem field_error {c : BinaryPcsConfig} (h : Inv c) :
    (∑ j ∈ range c.num_variables, (2 ^ (c.params.log_inv_rate + j + 1) + 1 + 2)) *
        2 ^ (c.params.security_level + if (regimeOf c).queries_are_exhaustive then 0 else 1) ≤
      2 ^ c.challenge_field_bits :=
  h.field_error

/-! ## The fold -/

section Fold

variable {F EF : Type} [Field F] [CharP F 2] [Field EF] [Algebra F EF]

/-- The FRI-Binius folding lemma.

Take the codeword of d over S_(l+1) and fold its pair above point(j).

The result is the codeword over S_l of the bound coefficients. -/
theorem fold_pair.ntt {L : Level F} (hL : Cantor L) {l : ℕ} (hl : l + 1 ≤ 2 ^ L.logBits) (hw : l < 64)
    (d : ℕ → F) {j : ℕ} (hj : j < 2 ^ l) (beta : EF) :
    fold_pair L j beta (ntt L.cantor (l + 1) 0 d (2 * j)) (ntt L.cantor (l + 1) 0 d (2 * j + 1)) =
      some (ntt (algebraMap F EF ∘ L.cantor) l 0
        (fun k => (1 - beta) * algebraMap F EF (d (2 * k)) + beta * algebraMap F EF (d (2 * k + 1))) j) :=
  fold_pair_ntt hL hl hw d hj beta

/-- Folding a pair panics exactly when the doubled index, wrapped at the word, leaves the alphabet's domain. -/
theorem fold_pair.panics (L : Level F) (index : ℕ) (beta : EF) (lo hi : F) :
    fold_pair L index beta lo hi = none ↔ ¬ 2 * index % 2 ^ 64 < 2 ^ 2 ^ L.logBits := by
  rw [fold_pair_eq]; split_ifs <;> simp_all

/-- Folding an honest coset of 2^a symbols gives a codeword over S_l.

It is the codeword of d with its a lowest variables bound. -/
theorem fold_coset.ntt [CharP EF 2] {LF : Level F} {LE : Level EF} (hF : Cantor LF) (hE : Cantor LE)
    (hpre : ∀ r < 2 ^ LF.logBits, LE.cantor r = algebraMap F EF (LF.cantor r)) {l a : ℕ} (ha : 0 < a)
    (hla : l + a ≤ 2 ^ LF.logBits) (hlaE : l + a ≤ 2 ^ LE.logBits) (hw : l + a ≤ 64) (d : ℕ → F)
    (bs : List EF) (hbs : bs.length = a) {c : ℕ} (hc : c < 2 ^ l) :
    fold_coset LF LE c ((List.range (2 ^ a)).map fun i => ntt LF.cantor (l + a) 0 d (c * 2 ^ a + i)) bs =
      some (ntt LE.cantor l 0 (bindAll bs (algebraMap F EF ∘ d)) c) :=
  fold_coset_ntt hF hE hpre ha hla hlaE hw d bs hbs hc

/-- One round of the tower-basis fold, with its walk over the domain, is the plain fold of every pair. -/
theorem fold_round.eq (L : Level F) (codeword : List F) (beta : EF) {m : ℕ}
    (hlen : codeword.length ≤ 2 ^ m) (hm : m ≤ 2 ^ L.logBits) (hw : m ≤ 64) :
    fold_round L codeword beta = (List.range (codeword.length / 2)).mapM fun j =>
      fold_pair L j beta (codeword.getD (2 * j) 0) (codeword.getD (2 * j + 1) 0) :=
  fold_round_eq L codeword beta hlen hm hw

end Fold

/-- After binding every variable, the coefficients leave the multilinear extension of d at the challenges. -/
theorem bindAll.mle {EF : Type} [Field EF] (bs : List EF) (e : ℕ → EF) :
    bindAll bs e 0 = ∑ k ∈ range (2 ^ bs.length), eqWeight bs k * e k :=
  bindAll_zero bs e

/-- After every fold, the honest final codeword over S_r is uniform.

Each symbol is the multilinear extension at the challenges. -/
theorem final.uniform {EF : Type} [Field EF] {β : ℕ → EF} (r : ℕ) (bs : List EF) (e : ℕ → EF)
    (he : ∀ k, 2 ^ bs.length ≤ k → e k = 0) (i : ℕ) :
    ntt β r 0 (bindAll bs e) i = ∑ k ∈ range (2 ^ bs.length), eqWeight bs k * e k :=
  ntt_bindAll r bs e he i

/-! ## The query phase -/

section Verifier

variable {F EF ComT ComX MPT MPX E : Type} [Field F] [Field EF] [Algebra F EF] [DecidableEq F]
  [DecidableEq EF] (V : Env F EF ComT ComX MPT MPX E)

/-- On an accepted schedule, the query phase never panics.

It answers every proof with an acceptance or a typed rejection. -/
theorem verify_query_paths.no_panic {c : BinaryPcsConfig} (hc : Inv c)
    (hLF : c.committed_field_bits ≤ 2 ^ V.LF.logBits) (hLE : c.committed_field_bits ≤ 2 ^ V.LE.logBits)
    {s : BinaryPcsShape} (hs : BinaryPcsShape.new c = some s) (base_commitment : ComT) (betas : List EF)
    (hb : betas.length = c.num_variables) (proof : BinaryPcsProof F EF ComX MPT MPX)
    (h : List (Step F EF)) : verify_query_paths V c base_commitment betas proof s h ≠ none :=
  verify_query_paths_ne_none V hc hLF hLE hs base_commitment betas hb proof h

/-- On an accepted schedule, the query phase accepts an honest proof.

This needs the Merkle schemes to accept its openings. -/
theorem verify_query_paths.complete [CharP F 2] [CharP EF 2] {c : BinaryPcsConfig} (hc : Inv c)
    (hLF : Cantor V.LF) (hLE : Cantor V.LE)
    (hpre : ∀ t < 2 ^ V.LF.logBits, V.LE.cantor t = algebraMap F EF (V.LF.cantor t))
    (hbF : c.committed_field_bits ≤ 2 ^ V.LF.logBits) (hbE : c.committed_field_bits ≤ 2 ^ V.LE.logBits)
    {s : BinaryPcsShape} (hs : BinaryPcsShape.new c = some s) (base_commitment : ComT)
    (d : ℕ → F) (betas : List EF) (hb : betas.length = c.num_variables)
    (proof : BinaryPcsProof F EF ComX MPT MPX) (h h2 : List (Step F EF))
    (hcanon : check_canonical_pow_witness (E := E) c proof = .ok ())
    (hfin : proof.final_codeword = (List.range (2 ^ c.params.log_inv_rate)).map
      (honestWord V d betas (c.num_variables + c.params.log_inv_rate) c.num_variables))
    (hpow : query_pow V.S s proof.pow_witness (h ++ [.message proof.final_codeword]) = .ok h2)
    (hbase : proof.base_opened_values = honestRows (ntt V.LF.cantor (c.num_variables + c.params.log_inv_rate) 0 d)
      (((query_pairs V.S s h2).1).map (· <<< (c.log_folding_factor - 1))) 0
      (min c.log_folding_factor c.num_variables))
    (hrl : proof.rounds.length = (c.num_variables + c.log_folding_factor - 1) / c.log_folding_factor - 1)
    (hround : ∀ i (hi : i < proof.rounds.length), proof.rounds[i].opened_values =
      honestRows (honestWord V d betas (c.num_variables + c.params.log_inv_rate) ((i + 1) * c.log_folding_factor))
        (((query_pairs V.S s h2).1).map (· <<< (c.log_folding_factor - 1))) ((i + 1) * c.log_folding_factor)
        (min c.log_folding_factor (c.num_variables - (i + 1) * c.log_folding_factor)))
    (hmb : V.mmcs.verifyBase base_commitment (1, 2 ^ (c.num_variables + c.params.log_inv_rate))
      (flat_coset_indices (((query_pairs V.S s h2).1).map (· <<< (c.log_folding_factor - 1))) 0
        (min c.log_folding_factor c.num_variables)) proof.base_opened_values proof.base_multi_proof = .ok ())
    (hmr : ∀ i (hi : i < proof.rounds.length), V.mmcs.verifyRound proof.rounds[i].commitment
      (1, 2 ^ (c.num_variables + c.params.log_inv_rate) >>> ((i + 1) * c.log_folding_factor))
      (flat_coset_indices (((query_pairs V.S s h2).1).map (· <<< (c.log_folding_factor - 1)))
        ((i + 1) * c.log_folding_factor) (min c.log_folding_factor (c.num_variables - (i + 1) * c.log_folding_factor)))
      proof.rounds[i].opened_values proof.rounds[i].multi_proof = .ok ()) :
    verify_query_paths V c base_commitment betas proof s h = some (.ok (query_pairs V.S s h2).2) :=
  verify_query_paths_complete V hc hLF hLE hpre hbF hbE hs base_commitment d betas hb proof h h2 hcanon hfin
    hpow hbase hrl hround hmb hmr

end Verifier

/-! ## The shipped code -/

section Shipped

variable {F EF R : Type} [Field F] [Field EF] [Algebra F EF]

/-- The shipped fold of a pair computes the transcription's fold. -/
theorem extracted.fold_pair (h64 : System.Platform.numBits = 64)
    {inst : p3_binary_field.tower.TowerLevel F R} {einst : p3_field.field.ExtensionField EF F}
    {L : Level F} (h : FoldComputes inst einst L) (index : Aeneas.Std.Usize) (beta : EF) (lo hi : F) :
    p3_binary_pcs.fold.fold_pair inst einst index beta lo hi =
      Proofs.BinaryDft.ofOption (fold_pair L index.val beta lo hi) :=
  fold_pair_eq_mirror h64 h index beta lo hi

/-- The FRI-Binius folding lemma, for the shipped fold.

Folding the pair above point(j) of an honest codeword gives the codeword of the bound coefficients. -/
theorem extracted.fold_pair.ntt [CharP F 2] (h64 : System.Platform.numBits = 64)
    {inst : p3_binary_field.tower.TowerLevel F R} {einst : p3_field.field.ExtensionField EF F}
    {L : Level F} (h : FoldComputes inst einst L) (hL : Cantor L) {l : ℕ}
    (hl : l + 1 ≤ 2 ^ L.logBits) (hw : l < 64) (d : ℕ → F) {j : Aeneas.Std.Usize} (hj : j.val < 2 ^ l)
    (beta : EF) :
    p3_binary_pcs.fold.fold_pair inst einst j beta (ntt L.cantor (l + 1) 0 d (2 * j.val))
        (ntt L.cantor (l + 1) 0 d (2 * j.val + 1)) =
      .ok (ntt (algebraMap F EF ∘ L.cantor) l 0
        (fun k => (1 - beta) * algebraMap F EF (d (2 * k)) + beta * algebraMap F EF (d (2 * k + 1))) j.val) := by
  rw [fold_pair_eq_mirror h64 h, fold_pair_ntt hL hl hw d hj beta]
  rfl

/-- The shipped constructor computes the transcription's, with p3-security's query count.

It reads the two levels' bit widths from their instances. -/
theorem extracted.try_new_with_folding (h64 : System.Platform.numBits = 64) {Enc R0 R1 : Type}
    (encInst : p3_binary_dft.encoder.EncodableLevel F Enc R0)
    (tInst : p3_binary_field.tower.TowerLevel EF R1) (fb eb : Aeneas.Std.Usize)
    (hfb : encInst.p3_binary_fieldtowerTowerLevelInst.p3_fieldfieldFieldInst.bits = .ok fb)
    (heb : tInst.p3_fieldfieldFieldInst.bits = .ok eb)
    (n : Aeneas.Std.Usize) (params : p3_binary_pcs.params.BinaryPcsParams) (lff : Aeneas.Std.Usize) :
    liftR (resM configM)
        (p3_binary_pcs.params.BinaryPcsConfig.try_new_with_folding encInst tInst n params lff) =
      Proofs.BinaryDft.ofOption (try_new_with_folding queriesNat fb.val eb.val n.val (paramsM params) lff.val) :=
  try_new_with_folding_eq h64 encInst tInst fb eb hfb heb n params lff

/-- The shipped change of folding factor computes the transcription's. -/
theorem extracted.try_with_folding.eq (h64 : System.Platform.numBits = 64)
    (c : p3_binary_pcs.params.BinaryPcsConfig) (lff : Aeneas.Std.Usize) :
    liftR (resM configM) (p3_binary_pcs.params.BinaryPcsConfig.try_with_folding c lff) =
      Proofs.BinaryDft.ofOption ((configM c).try_with_folding lff.val) :=
  try_with_folding_eq h64 c lff

/-- On an accepted schedule, the shipped change of folding factor never panics.

It accepts exactly the factors that keep the invariants. -/
theorem extracted.try_with_folding (h64 : System.Platform.numBits = 64)
    {c : p3_binary_pcs.params.BinaryPcsConfig} (h : Inv (configM c)) (lff : Aeneas.Std.Usize) :
    ∃ r, p3_binary_pcs.params.BinaryPcsConfig.try_with_folding c lff = .ok r ∧
      ∀ c', resM configM r = .ok c' ↔
        c' = { configM c with log_folding_factor := lff.val } ∧ Inv c' := by
  obtain ⟨⟨x, hx⟩, hiff⟩ := h.try_with_folding lff.val
  have e := try_with_folding_eq h64 c lff
  rw [hx] at e
  obtain ⟨r, hr, hrx⟩ := liftR_ok e
  exact ⟨r, hr, fun c' => by rw [hrx, ← hiff c', hx, Option.some.injEq]⟩

/-- The shipped batch count is ceil(n / lff), and panics at a zero factor. -/
theorem extracted.num_fold_batches (c : p3_binary_pcs.params.BinaryPcsConfig) :
    liftR Aeneas.Std.UScalar.val (p3_binary_pcs.params.BinaryPcsConfig.num_fold_batches c) =
      Proofs.BinaryDft.ofOption (configM c).num_fold_batches :=
  num_fold_batches_eq c

/-- On an accepted schedule, the shipped transcript shape never panics.

It has n + r - lff index bits and min(q, 2^(n+r-lff)) distinct pairs. -/
theorem extracted.shape (h64 : System.Platform.numBits = 64) {c : p3_binary_pcs.params.BinaryPcsConfig}
    (h : Inv (configM c)) :
    ∃ s, p3_binary_pcs.transcript.BinaryPcsShape.new c = .ok s ∧
      shapeM s = ⟨c.num_variables.val, c.log_folding_factor.val,
        (c.num_variables.val + c.log_folding_factor.val - 1) / c.log_folding_factor.val - 1,
        2 ^ c.params.log_inv_rate.val, c.params.pow_bits.val,
        c.num_variables.val + c.params.log_inv_rate.val - c.log_folding_factor.val,
        min c.num_queries.val (2 ^ (c.num_variables.val + c.params.log_inv_rate.val -
          c.log_folding_factor.val))⟩ := by
  obtain ⟨s, hs, hv⟩ := Lib.spec_imp_exists (shape_new_spec h64 c h)
  rw [h.shape] at hv
  exact ⟨s, hs, Option.some.inj hv⟩

end Shipped

/-! ## The tower levels -/

/-- Over GF(2^128), the FRI-Binius folding lemma holds for every codeword that fits in a word.

The codeword dimension may go up to the field's 128 dimensions. -/
theorem towerLevel.fold_pair {l : ℕ} (hw : l < 64) (b : ℕ)
    (d : ℕ → ConcreteBinaryTower.ConcreteBTField 7) {j : ℕ} (hj : j < 2 ^ l)
    (beta : ConcreteBinaryTower.ConcreteBTField 7) :
    fold_pair (towerLevel 7 b) j beta (ntt (towerLevel 7 b).cantor (l + 1) 0 d (2 * j))
        (ntt (towerLevel 7 b).cantor (l + 1) 0 d (2 * j + 1)) =
      some (ntt (towerLevel 7 b).cantor l 0 (fun k => (1 - beta) * d (2 * k) + beta * d (2 * k + 1)) j) := by
  have := fold_pair_ntt (EF := ConcreteBinaryTower.ConcreteBTField 7) (towerLevel_cantor le_rfl b)
    (l := l) (by simp [towerLevel]; omega) hw d hj beta
  simpa using this

end Plonky3Lean.Claims.BinaryPcs
