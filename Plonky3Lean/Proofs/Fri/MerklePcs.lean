module

public import Plonky3Lean.Proofs.Fri.Merkle

@[expose] public section

/-!
# Completeness of the PCS verifier over Merkle commitments

Both commitment schemes are the Merkle tree scheme.

An honest prover commits every input batch as the low-degree extensions of its columns.

It commits every round's codeword with one row per group of folded values.

It opens both at the indices the verifier derives.

The verifier then accepts.

No hypothesis says that a scheme accepts: the Merkle tree's completeness proves it.
-/

namespace Plonky3Lean.Proofs.Fri

open Polynomial Finset Plonky3Lean.Spec.Fri p3_fri.two_adic_pcs.mirror p3_dft.mirror
open p3_fri.verifier.mirror p3_fri.mirror p3_fri.config.mirror Plonky3Lean.Proofs.Dft
open p3_commit.pcs.univariate.mirror p3_fri.transcript.mirror Plonky3Lean.Proofs.MerkleTree

variable {K : Type} [Field K] [DecidableEq K]

/-! ## The honest matrices -/

/-- The low-degree extension of one claimed matrix.

Row r holds every column at point r of the bit-reversed coset of order 2^(k + b). -/
noncomputable def ldeMat (G : Gen K) (g : K) (b : ℕ) (cols : MatrixOpening K (Coset G) → List K[X])
    (m : MatrixOpening K (Coset G)) : Mat K :=
  ⟨2 ^ (m.domain.log_size + b), (cols m).length,
    fun r j => ((cols m).get j).eval (rowPoint G g (m.domain.log_size + b) r)⟩

/-- The matrices one batch commits. -/
noncomputable def batchMats (G : Gen K) (g : K) (b : ℕ) (cols : MatrixOpening K (Coset G) → List K[X])
    {C : Type} (c : Claim G C) : List (Mat K) :=
  c.matrices.map (ldeMat G g b cols)

/-- One round's codeword of log height lh: row t holds the 2^a values of group t. -/
def roundMat (w : List K) (a lh : ℕ) : Mat K := ⟨2 ^ lh, 2 ^ a, fun t j => w.getD (t * 2 ^ a + j.val) 0⟩

omit [DecidableEq K] in
theorem matRow_ldeMat (G : Gen K) (g : K) (b : ℕ) (cols : MatrixOpening K (Coset G) → List K[X])
    (m : MatrixOpening K (Coset G)) (r : ℕ) :
    matRow (ldeMat G g b cols m) r = (cols m).map (·.eval (rowPoint G g (m.domain.log_size + b) r)) := by
  rw [← List.ofFn_getElem_eq_map, matRow, ← List.ofFn_eq_map]
  rfl

omit [DecidableEq K] in
theorem matRow_roundMat (w : List K) (a lh t : ℕ) : matRow (roundMat w a lh) t = rowList w a t := by
  rw [matRow, ← List.ofFn_eq_map]
  rfl

theorem topLog_singleton (x : ℕ) : topLog [x] = x := by simp [topLog]

theorem topLog_le {l : List ℕ} {B : ℕ} (hl : ∀ x ∈ l, x ≤ B) : topLog l ≤ B := foldl_max_le l 0 B hl (Nat.zero_le _)

theorem foldl_max_pow : ∀ (l : List ℕ) (a : ℕ), (l.map (2 ^ ·)).foldl max (2 ^ a) = 2 ^ l.foldl max a
  | [], _ => rfl
  | y :: l, a => by
    rw [List.map_cons, List.foldl_cons, List.foldl_cons,
      ← (pow_right_monotone (by norm_num : 1 ≤ 2) : Monotone (2 ^ · : ℕ → ℕ)).map_max]
    exact foldl_max_pow l _

theorem max?_map_pow {l : List ℕ} (hl : l ≠ []) : (l.map (2 ^ ·)).max? = some (2 ^ topLog l) := by
  obtain ⟨y, t, rfl⟩ := List.exists_cons_of_ne_nil hl
  rw [List.map_cons, List.max?_cons', foldl_max_pow, topLog, List.foldl_cons, Nat.zero_max]

omit [DecidableEq K] in
theorem batchLogs_batchMats (G : Gen K) (g : K) (b : ℕ) (cols : MatrixOpening K (Coset G) → List K[X])
    {C : Type} (c : Claim G C) :
    batchLogs (batchMats G g b cols c) = c.matrices.map fun m => m.domain.log_size + b := by
  simp [batchLogs, batchMats, ldeMat, Nat.log_pow]

omit [DecidableEq K] in
/-- On a batch with a matrix, the check's indices are the query indices shifted to the batch's tallest height. -/
theorem batchReduced_eq (G : Gen K) (g : K) (b H : ℕ) (cols : MatrixOpening K (Coset G) → List K[X])
    {C : Type} (indices : List ℕ) (c : Claim G C) (hne : c.matrices ≠ []) :
    batchReduced b H indices c = indices.map (· / 2 ^ (H - topLog (batchLogs (batchMats G g b cols c)))) := by
  have hh : (c.matrices.map fun m => 2 ^ m.domain.log_size * 2 ^ b) =
      (c.matrices.map fun m => m.domain.log_size + b).map (2 ^ ·) := by simp [pow_add]
  rw [batchReduced, hh, max?_map_pow (by simpa using hne), batchLogs_batchMats]
  simp [Nat.log_pow]

omit [DecidableEq K] in
/-- On honest claims, the check's dimensions are the committed matrices' widths and heights. -/
theorem batchDims_eq (G : Gen K) (g : K) (b : ℕ) (cols : MatrixOpening K (Coset G) → List K[X])
    {C : Type} (c : Claim G C) (hpts : ∀ m ∈ c.matrices, m.points ≠ [])
    (hval : ∀ m ∈ c.matrices, ∀ p ∈ m.points, p.values = (cols m).map (·.eval p.point)) :
    batchDims b c = (batchMats G g b cols c).map fun M => (M.width, M.height) := by
  simp only [batchDims, batchMats, List.map_map]
  refine List.map_congr_left fun m hm => ?_
  obtain ⟨p, t, hp⟩ := List.exists_cons_of_ne_nil (hpts m hm)
  simp [ldeMat, hp, hval m hm p (by simp [hp]), pow_add]

theorem mem_zip_map_self {α β : Type _} (f : α → β) :
    ∀ (l : List α), ∀ bc ∈ (l.map f).zip l, bc = (f bc.2, bc.2) ∧ bc.2 ∈ l
  | [], _, h => by simp at h
  | x :: l, bc, h => by
    rcases List.mem_cons.1 h with rfl | h
    · simp
    · obtain ⟨e, hm⟩ := mem_zip_map_self f l bc h
      exact ⟨e, List.mem_cons_of_mem _ hm⟩

/-- The honest opening of one input batch at the verifier's indices. -/
noncomputable def honestBatch (G : Gen K) (g : K) (b H : ℕ) (cols : MatrixOpening K (Coset G) → List K[X])
    {C D : Type} (h : List (List K) → D) (c : List D → D) (z : D) (capH : ℕ) (indices : List ℕ)
    (cl : Claim G C) : BatchMultiOpening K (merkleOps h c z capH).MultiProof :=
  ⟨(batchReduced b H indices cl).map (merkleRows (batchMats G g b cols cl)),
    (batchReduced b H indices cl).map (merklePath h c z capH (batchMats G g b cols cl))⟩

theorem proofRds_arities (G : Gen K) (g α : K) {C Com MP IMP : Type} (params : FriParameters)
    (cols : MatrixOpening K (Coset G) → List K[X]) (claims : List (Claim G C))
    (proof : FriProof K Com MP IMP) (betas : List K) {L : List ℕ} (hpre : FriPre G params claims proof L)
    (hβ : betas.length = L.length) :
    (proofRds G g α params cols claims proof betas L).map Rd.a = L := by
  have hsvl : (proof.commit_phase_openings.map (·.sibling_values)).length = L.length := by
    rw [List.length_map, hpre.openings]
  obtain ⟨-, hrsa, -⟩ := honestRds_map G (deepInput g α params.log_blowup cols claims)
    ((inputLogHeights params.log_blowup claims).headD 0)
    (deepOn g α params.log_blowup cols claims ((inputLogHeights params.log_blowup claims).headD 0))
    (proofRounds proof betas L)
  rw [proofRds, hrsa, proofRounds, show (fun x : K × ℕ × List (List K) => x.2.1) = Prod.fst ∘ Prod.snd from rfl,
    ← List.map_map, List.map_snd_zip (by rw [List.length_zip, hsvl, hβ, min_self]),
    List.map_fst_zip (by rw [hsvl])]

/-! ## Completeness -/

/-- Completeness of the PCS verifier over Merkle commitments.

The claims are honest, as in the completeness from honest commitments.

Both schemes are Merkle trees, with any hashers, compressions and padding digests.

The prover is honest:

- every batch commits the low-degree extensions of its columns
- every batch opens at the verifier's indices
- every round commits its codeword, one row per group, and opens it at the round's groups
- the rounds fold the DEEP word of the tallest height, and roll in the DEEP words below
- the final polynomial is the inverse transform of the final word.

The caps lie low enough:

- every batch has a matrix at least as tall as the input cap
- the final codeword is at least as tall as the round cap.

Then the verifier accepts. -/
theorem pcs_verify_complete_merkle (G : Gen K) (hV : GenValid G) (hN : GenNested G) (h2 : (2 : K) ≠ 0)
    (g : K) {C S DI DF : Type} (hashI : List (List K) → DI) (cmpI : List DI → DI) (zI : DI) (capI : ℕ)
    (hashF : List (List K) → DF) (cmpF : List DF → DF) (zF : DF) (capF : ℕ)
    (sp : Sponge K (merkleOps hashF cmpF zF capF).Commitment S) (params : FriParameters)
    (claims : List (Claim G C))
    (proof : FriProof K (merkleOps hashF cmpF zF capF).Commitment (merkleOps hashF cmpF zF capF).MultiProof
      (merkleOps hashI cmpI zI capI).MultiProof) (s : S)
    (commit_of : C → (merkleOps hashI cmpI zI capI).Commitment) (hG : G.adicity < 64)
    {L : List ℕ} (hpre : FriPre G params claims proof L) (cols : MatrixOpening K (Coset G) → List K[X])
    (hval : ∀ c ∈ claims, ∀ m ∈ c.matrices, ∀ p ∈ m.points, p.values = (cols m).map (·.eval p.point))
    (hdeg : ∀ c ∈ claims, ∀ m ∈ c.matrices, ∀ f ∈ cols m, f.degree < ↑(2 ^ m.domain.log_size))
    (hF : ∀ c ∈ claims, ∀ m ∈ c.matrices, params.log_final_poly_len ≤ m.domain.log_size)
    (hpts : ∀ c ∈ claims, ∀ m ∈ c.matrices, m.points ≠ [])
    (hout : ∀ c ∈ claims, ∀ m ∈ c.matrices, ∀ p ∈ m.points,
      ∀ r < 2 ^ (inputLogHeights params.log_blowup claims).headD 0,
        p.point ≠ rowPoint G g ((inputLogHeights params.log_blowup claims).headD 0) r)
    (hcapI : ∀ c ∈ claims, ∃ m ∈ c.matrices, capI ≤ m.domain.log_size + params.log_blowup)
    (hcapF : capF ≤ params.log_blowup + params.log_final_poly_len)
    (hcom : ∀ c ∈ claims, commit_of c.commitment =
      merkleCap hashI cmpI zI capI (batchMats G g params.log_blowup cols c))
    {α : K} {s2 : S}
    (hb : batch_phase sp (PcsShape.from_claims params claims) (claimedState sp claims s)
      (some proof.batch_pow_witness) = pure (α, s2))
    {betas : List K} {s3 s4 : S} {indices : List ℕ}
    (hc : commit_rounds sp (FriShape.with_schedule params L ((inputLogHeights params.log_blowup claims).headD 0))
      s2 proof.commit_phase_commits proof.commit_pow_witnesses = pure (betas, s3))
    (hq : query_phase sp (FriShape.with_schedule params L ((inputLogHeights params.log_blowup claims).headD 0))
      s3 proof.final_poly (some proof.query_pow_witness) = pure (indices, s4))
    (hopen : proof.input_openings = claims.map (honestBatch G g params.log_blowup
      ((inputLogHeights params.log_blowup claims).headD 0) cols hashI cmpI zI capI indices))
    (hsib : ∀ q i, indices[q]? = some i →
      HonestSiblings G (deepInput g α params.log_blowup cols claims) q
        ((inputLogHeights params.log_blowup claims).headD 0) i
        (deepOn g α params.log_blowup cols claims ((inputLogHeights params.log_blowup claims).headD 0))
        (proofRounds proof betas L))
    (hfin : ∀ i < 2 ^ params.log_final_poly_len, proof.final_poly.getD i 0 =
      Plonky3Lean.Spec.Dft.idft (G.gen params.log_final_poly_len) (2 ^ params.log_final_poly_len)
        (fun j => (revIndex (2 ^ params.log_final_poly_len)
          ((word G (proofFinal G g α params cols claims proof betas L)
            (params.log_final_poly_len + params.log_blowup)).take (2 ^ params.log_final_poly_len))).getD j 0) i)
    (hround : ∀ k (hk : k < (proofRds G g α params cols claims proof betas L).length),
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
                (((proofRds G g α params cols claims proof betas L).take (k + 1)).map Rd.a).sum)])) :
    verify G g (merkleOps hashF cmpF zF capF) (merkleOps hashI cmpI zI capI) sp params claims proof s commit_of =
      pure () := by
  set b := params.log_blowup
  set H := (inputLogHeights b claims).headD 0 with hHdef
  have hidx := query_phase_indices_lt sp _ _ _ _ hq
  have hβ : betas.length = L.length := commit_rounds_length sp _ _ _ _ hc
  have hle := le_inputLogHeights_head b claims
  have hHa : H ≤ G.adicity := hpre.height
  obtain ⟨hS, hFall, -, hsum⟩ := schedule_facts G params claims proof hpre hF
  have hFH : b + params.log_final_poly_len ≤ H := hFall _ (by
    rcases hSc : inputLogHeights b claims with _ | ⟨x, T⟩
    · exact absurd hSc hS
    · rw [hHdef, hSc]; simp)
  -- Facts about one batch: a matrix, its tallest height below H, and the honest row of each matrix.
  have hne : ∀ c ∈ claims, c.matrices ≠ [] := fun c hc => by
    obtain ⟨m, hm, -⟩ := hcapI c hc; exact List.ne_nil_of_mem hm
  have htopH : ∀ c ∈ claims, topLog (batchLogs (batchMats G g b cols c)) ≤ H := fun c hc => by
    rw [batchLogs_batchMats]
    exact topLog_le fun x hx => by
      obtain ⟨m, hm, rfl⟩ := List.mem_map.1 hx; exact hle c hc m hm
  have hrow : ∀ c ∈ claims, ∀ i, (merkleRows (batchMats G g b cols c)
      (i / 2 ^ (H - topLog (batchLogs (batchMats G g b cols c))))) =
      c.matrices.map fun m => (cols m).map (·.eval (xOfQuery G g H i (m.domain.log_size + b))) := by
    intro c hc i
    set T := topLog (batchLogs (batchMats G g b cols c)) with hTdef
    have hT : T ≤ H := htopH c hc
    rw [merkleRows, ← hTdef]
    conv_lhs => rw [batchMats, List.map_map]
    refine List.map_congr_left fun m hm => ?_
    have hlm : m.domain.log_size + b ≤ T := by
      rw [hTdef, batchLogs_batchMats]; exact le_topLog (List.mem_map_of_mem hm)
    have hlog : Nat.log 2 (ldeMat G g b cols m).height = m.domain.log_size + b := Nat.log_pow (by norm_num) _
    show matRow (ldeMat G g b cols m) _ = _
    rw [matRow_ldeMat, hlog, xOfQuery_eq G g ((hle c hc m hm).trans hHa), Nat.div_div_eq_div_mul, ← pow_add,
      show H - T + (T - (m.domain.log_size + b)) = H - (m.domain.log_size + b) by omega]

  -- The honest openings are the columns at each query point.
  have hon : HonestOpenings G g b H cols claims indices proof.input_openings := by
    refine ⟨by rw [hopen, List.length_map], fun bo hbo => ?_, fun q hq => ?_⟩
    · rw [hopen] at hbo
      obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hbo
      simp [honestBatch, batchReduced_eq G g b H cols indices c (hne c hc)]
    · rw [hopen, List.forall₂_map_right_iff, List.forall₂_same]
      intro c hc
      simp only [honestBatch, batchReduced_eq G g b H cols indices c (hne c hc), List.getD_eq_getElem?_getD,
        List.getElem?_map, List.getElem?_eq_getElem hq, Option.map_some, Option.getD_some]
      rw [hrow c hc, List.forall₂_map_right_iff, List.forall₂_same]
      exact fun m _ => rfl
  refine pcs_verify_complete_honest G hV hN h2 g _ _ sp params claims proof s commit_of hG hpre cols hval hdeg hF
    hpts hout hb hc hq hon (fun bc hbc => ?_) hsib hfin (fun k hk c o hck hok => ?_)
  · -- Every input batch verifies: the Merkle tree's completeness.
    rw [hopen] at hbc
    obtain ⟨hbc', hc⟩ := mem_zip_map_self _ _ bc hbc
    rw [hbc']
    simp only [honestBatch]
    rw [hcom _ hc, batchDims_eq G g b cols _ (hpts _ hc) (hval _ hc), batchReduced_eq G g b H cols indices _ (hne _ hc)]
    obtain ⟨m, hm, hcm⟩ := hcapI _ hc
    refine merkle_verify_honest hashI cmpI zI capI _ _ _ rfl (by simpa [batchMats] using hne _ hc) ?_ ?_ ?_
    · intro M hM
      obtain ⟨m, -, rfl⟩ := List.mem_map.1 hM
      simp [ldeMat, Nat.log_pow]
    · rw [batchLogs_batchMats]; exact hcm.trans (le_topLog (List.mem_map_of_mem hm))
    · intro I hI
      obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hI
      have hT := htopH _ hc
      rw [Nat.div_lt_iff_lt_mul (by positivity), ← pow_add, show topLog (batchLogs (batchMats G g b cols bc.2)) +
        (H - topLog (batchLogs (batchMats G g b cols bc.2))) = H by omega]
      exact hidx i hi
  · -- Every round verifies: the Merkle tree's completeness on the round's codeword.
    set rs := proofRds G g α params cols claims proof betas L
    obtain ⟨hcom', hprf⟩ := hround k hk
    rw [hcom'] at hck
    cases Option.some.inj hck
    rw [hprf o hok]
    have hSk : ((rs.take (k + 1)).map Rd.a).sum ≤ H - (b + params.log_final_poly_len) := by
      rw [List.map_take, proofRds_arities G g α params cols claims proof betas hpre hβ, ← hsum]
      have := List.sum_take_add_sum_drop L (k + 1)
      omega
    have hrows : (roundGroups rs indices k).map (fun t => [rowList rs[k].w rs[k].a t]) =
        (roundGroups rs indices k).map (merkleRows [roundMat rs[k].w rs[k].a
          (H - ((rs.take (k + 1)).map Rd.a).sum)]) := by
      refine List.map_congr_left fun t _ => ?_
      simp only [merkleRows, batchLogs, List.map_cons, List.map_nil, topLog_singleton, Nat.sub_self, pow_zero,
        Nat.div_one, matRow_roundMat]
    rw [hrows]
    refine merkle_verify_honest hashF cmpF zF capF _ _ _ rfl (by simp) (by simp [roundMat, Nat.log_pow])
      (by simp only [batchLogs, roundMat, List.map_cons, List.map_nil, Nat.log_pow (by norm_num : 1 < 2),
        topLog_singleton]; omega) ?_
    intro t ht
    simp only [batchLogs, roundMat, List.map_cons, List.map_nil, Nat.log_pow (by norm_num : 1 < 2), topLog_singleton]
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 ht
    rw [Nat.div_lt_iff_lt_mul (by positivity), ← pow_add, show H - ((rs.take (k + 1)).map Rd.a).sum +
      ((rs.take (k + 1)).map Rd.a).sum = H by omega]
    exact hidx i hi

end Plonky3Lean.Proofs.Fri
