module

public import Plonky3Lean.Proofs.BinaryPcs.Verifier

@[expose] public section

/-!
# An honest proof passes the query phase

The honest prover commits to the codeword of the message over S_(n+r).

After the first s folds, the word is a codeword over S_(n+r-s).

Its message is the original one with its s lowest variables bound.

At every drawn index, the prover opens the whole coset of every batch.

It sends the last word in full.

Every fold check then compares a folded coset with the same value of the next word.

So the query phase accepts.
-/

namespace Plonky3Lean.Proofs.BinaryPcs

open Plonky3Lean.Spec.BinaryDft Plonky3Lean.Proofs.BinaryDft
open p3_sumcheck.mirror p3_binary_dft.mirror p3_binary_pcs.mirror p3_binary_pcs.params.mirror
open p3_binary_pcs.transcript.mirror p3_binary_pcs.fold.mirror p3_binary_pcs.verifier.mirror

/-- The rows an honest prover opens for one batch: every symbol of each queried coset of the word. -/
def honestRows {A : Type _} (W : ℕ → A) (indices : List ℕ) (start a : ℕ) : List (List A) :=
  indices.flatMap fun index => (List.range (2 ^ a)).map fun j => [W ((index >>> start) >>> a <<< a + j)]

theorem flatMap_getElem? {α β : Type _} (g : α → List β) (s : ℕ) (hg : ∀ x, (g x).length = s) :
    ∀ (l : List α) {q j : ℕ} (_hq : q < l.length) (_hj : j < s),
      (l.flatMap g)[q * s + j]? = (g l[q])[j]?
  | [], _, _, hq, _ => by simp at hq
  | x :: l, q, j, hq, hj => by
    cases q with
    | zero =>
      simp only [List.flatMap_cons, zero_mul, zero_add, List.getElem_cons_zero]
      exact List.getElem?_append_left (by rw [hg]; exact hj)
    | succ q =>
      rw [List.flatMap_cons, List.getElem?_append_right (by rw [hg]; nlinarith), hg,
        show (q + 1) * s + j - s = q * s + j by rw [add_mul, one_mul]; omega]
      exact flatMap_getElem? g s hg l (by simpa using hq) hj

theorem honestRows_length {A : Type _} (W : ℕ → A) (indices : List ℕ) (start a : ℕ) :
    (honestRows W indices start a).length = indices.length * 2 ^ a := by
  simp [honestRows, List.length_flatMap, List.map_const', List.sum_replicate]

theorem honestRows_width {A : Type _} (W : ℕ → A) (indices : List ℕ) (start a : ℕ) :
    ∀ x ∈ honestRows W indices start a, x.length = 1 := by
  intro x hx
  simp only [honestRows, List.mem_flatMap, List.mem_map] at hx
  obtain ⟨_, _, _, _, rfl⟩ := hx
  rfl

theorem honestRows_get {A : Type _} (W : ℕ → A) (indices : List ℕ) (start a : ℕ) {q j : ℕ}
    (hq : q < indices.length) (hj : j < 2 ^ a) :
    (honestRows W indices start a)[q * 2 ^ a + j]? =
      some [W (indices[q] >>> start >>> a * 2 ^ a + j)] := by
  rw [honestRows, flatMap_getElem? _ (2 ^ a) (fun _ => by simp) _ hq hj]
  simp [List.getElem?_range hj, Nat.shiftLeft_eq]

/-! ## Each fold check of an honest proof passes -/

variable {F EF ComT ComX MPT MPX E : Type} [Field F] [CharP F 2] [Field EF] [CharP EF 2] [Algebra F EF]
  [DecidableEq F] [DecidableEq EF] (V : Env F EF ComT ComX MPT MPX E)

/-- The honest word after the first s folds, over S_(n+r-s), in the challenge field. -/
def honestWord (d : ℕ → F) (betas : List EF) (m s : ℕ) (i : ℕ) : EF :=
  ntt V.LE.cantor (m - s) 0 (bindAll (betas.take s) (algebraMap F EF ∘ d)) i

omit [DecidableEq F] in
/-- One fold check of an honest proof passes.

The words of the proof are honest:

- the base word is the codeword of d over S_(n+r)
- every later word is the honest word of its first variable
- the final word is the honest word after every fold. -/
theorem foldCheck_honest {n r lff : ℕ} (hk : 0 < lff) (hLF : Cantor V.LF) (hLE : Cantor V.LE)
    (hpre : ∀ t < 2 ^ V.LF.logBits, V.LE.cantor t = algebraMap F EF (V.LF.cantor t))
    (hbF : n + r ≤ 2 ^ V.LF.logBits) (hbE : n + r ≤ 2 ^ V.LE.logBits) (hw : n + r ≤ 64)
    (d : ℕ → F) (betas : List EF) (hb : betas.length = n) (indices : List ℕ)
    (proof : BinaryPcsProof F EF ComX MPT MPX)
    (hbase : proof.base_opened_values = honestRows (ntt V.LF.cantor (n + r) 0 d) indices 0 (min lff n))
    (hrl : proof.rounds.length = (n + lff - 1) / lff - 1)
    (hround : ∀ i (hi : i < proof.rounds.length), proof.rounds[i].opened_values =
      honestRows (honestWord V d betas (n + r) ((i + 1) * lff)) indices ((i + 1) * lff)
        (min lff (n - (i + 1) * lff)))
    (hfin : proof.final_codeword = (List.range (2 ^ r)).map (honestWord V d betas (n + r) n))
    {q batch : ℕ} (hq : q < indices.length) (hidx : indices[q] < 2 ^ (n + r))
    (hbatch : batch < (n + lff - 1) / lff) :
    foldCheck V betas proof ((List.range ((n + lff - 1) / lff)).map
      fun b => (b * lff, min lff (n - b * lff))) q indices[q] batch = some (.ok ()) := by
  obtain ⟨hs, ha, hsa, hmid, hlast⟩ := batch_facts hk hbatch
  simp only [foldCheck, List.getElem?_map, List.getElem?_range hbatch, Option.map_some,
    Option.bind_eq_bind, Option.bind_some]
  simp only [show ¬ betas.length < batch * lff + min lff (n - batch * lff) by omega, ite_false]
  have hrow : ∀ {A : Type} (W : ℕ → A) (st a j : ℕ), j < 2 ^ a →
      (honestRows W indices st a)[q * 2 ^ a + j]? = some [W ((indices[q] >>> (st + a)) * 2 ^ a + j)] :=
    fun W st a j hj => by rw [honestRows_get W indices st a hq hj, Nat.shiftRight_add]
  have hnext : batch + 1 < (n + lff - 1) / lff →
      (batch + 1) * lff = batch * lff + min lff (n - batch * lff) := fun h1 => by
    rw [add_mul, one_mul, hmid h1]
  generalize hst : batch * lff = st at *
  generalize ha' : min lff (n - st) = a at *
  generalize hnp : indices[q] >>> (st + a) = np at *
  have hbs : ((betas.drop st).take a).length = a := by simp [hb]; omega
  have hnpl : np < 2 ^ (n + r - st - a) := by
    rw [← hnp, Nat.shiftRight_eq_div_pow, Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), ← pow_add]
    exact lt_of_lt_of_le hidx (Nat.pow_le_pow_right (by norm_num) (by omega))
  have htake : betas.take st ++ (betas.drop st).take a = betas.take (st + a) := (List.take_add ..).symm
  -- The folded coset is the honest word after st + a folds, at np.
  have hfold0 : batch = 0 → fold_query_coset V V.LF proof.base_opened_values q np ((betas.drop st).take a) =
      some (honestWord V d betas (n + r) (st + a) np) := fun h0 => by
    have hst0 : st = 0 := by rw [← hst, h0, zero_mul]
    subst hst0
    rw [hbase, show min lff n = a by rw [← ha', Nat.sub_zero]]
    rw [fold_query_coset_honest V hLF hLE hpre (l := n + r - 0 - a) (a := a) (by omega) (by omega)
      (by omega) d _ hbs (by omega) hnpl _ q (fun j hj => by
        rw [hrow _ 0 a j hj, hnp, show n + r - 0 - a + a = n + r by omega])]
    simp only [honestWord, List.drop_zero, zero_add, Nat.sub_zero]
  have hfold1 : ∀ (h0 : batch ≠ 0), fold_query_coset V V.LE
      (proof.rounds[batch - 1]'(by omega)).opened_values q np ((betas.drop st).take a) =
      some (honestWord V d betas (n + r) (st + a) np) := fun h0 => by
    have hi : batch - 1 < proof.rounds.length := by omega
    have hsti : (batch - 1 + 1) * lff = st := by rw [← hst]; congr 1; omega
    rw [hround _ hi, hsti, ha']
    rw [fold_query_coset_honest V (A := EF) hLE hLE (fun t _ => by simp) (l := n + r - st - a) (a := a)
      (by omega) (by omega) (by omega) (bindAll (betas.take st) (algebraMap F EF ∘ d)) _ hbs (by omega)
      hnpl _ q (fun j hj => by
        rw [hrow _ st a j hj, hnp]
        simp only [honestWord]
        rw [show n + r - st - a + a = n + r - st by omega])]
    have hid : (⇑(algebraMap EF EF) ∘ bindAll (betas.take st) (⇑(algebraMap F EF) ∘ d)) =
        bindAll (betas.take st) (⇑(algebraMap F EF) ∘ d) := by funext; simp
    simp only [honestWord]
    rw [hid, bindAll_append, htake, show n + r - st - a = n + r - (st + a) by omega]
  by_cases h1 : batch + 1 < (n + lff - 1) / lff
  · have hr : batch < proof.rounds.length := by omega
    have hmod : np % 2 ^ min lff (n - (st + a)) < 2 ^ min lff (n - (st + a)) :=
      Nat.mod_lt _ (Nat.two_pow_pos _)
    have hget := hrow (honestWord V d betas (n + r) (st + a)) (st + a) (min lff (n - (st + a))) _ hmod
    rw [Nat.shiftRight_add, hnp, Nat.shiftRight_eq_div_pow, Nat.div_add_mod'] at hget
    rw [List.getElem?_range h1, Option.map_some]
    dsimp only
    simp only [List.getElem?_eq_getElem hr, Option.bind_some, hround batch hr, hnext h1, hget,
      List.getElem?_cons_zero]
    split_ifs with h0
    · rw [hfold0 h0]; simp [pure]
    · simp only [List.getElem?_eq_getElem (show batch - 1 < proof.rounds.length by omega),
        Option.bind_some]
      rw [hfold1 h0]; simp [pure]
  · have hnone : (List.range ((n + lff - 1) / lff))[batch + 1]? = none :=
      List.getElem?_eq_none (by simp; omega)
    have hlastv : st + a = n := hlast h1
    have hnpr : np < 2 ^ r := by rw [show r = n + r - st - a by omega]; exact hnpl
    rw [hnone, Option.map_none]
    simp only [hfin, List.getElem?_map, List.getElem?_range hnpr, Option.map_some, Option.bind_some]
    split_ifs with h0
    · rw [hfold0 h0, hlastv]; simp [pure]
    · simp only [List.getElem?_eq_getElem (show batch - 1 < proof.rounds.length by omega),
        Option.bind_some]
      rw [hfold1 h0, hlastv]; simp [pure]

/-! ## The query phase accepts an honest proof -/

theorem firstError_all_ok {α ε : Type _} (xs : List α) (f : α → Option (Except ε Unit))
    (h : ∀ x ∈ xs, f x = some (.ok ())) : firstError xs f = some (.ok ()) := by
  unfold firstError
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rw [List.foldlM_cons, h x (by simp)]
    exact ih fun y hy => h y (by simp [hy])

omit [Field F] [DecidableEq F] in
theorem check_round_shape_of {A : Type _} (round : ℕ) (rows : List (List A)) (e : ℕ)
    (hl : rows.length = e) (hw : ∀ x ∈ rows, x.length = 1) :
    check_round_shape (F := F) (E := E) round rows e = .ok () := by
  unfold check_round_shape
  simp only [hl, ne_eq, not_true_eq_false, ite_false]
  rw [List.find?_eq_none.2 fun q hq => by
    have hq' : q < rows.length := hl ▸ List.mem_range.1 hq
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hq', hw _ (List.getElem_mem hq')]]

/-- On an accepted schedule, the query phase accepts an honest proof.

The honest prover:

- commits to the codeword of d
- folds with the sumcheck challenges
- sends the last word
- opens every coset of every batch at the drawn indices.

The two Merkle schemes accept honest openings, and the grinding witness passes. -/
theorem verify_query_paths_complete {c : BinaryPcsConfig} (hc : Inv c) (hLF : Cantor V.LF)
    (hLE : Cantor V.LE) (hpre : ∀ t < 2 ^ V.LF.logBits, V.LE.cantor t = algebraMap F EF (V.LF.cantor t))
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
    verify_query_paths V c base_commitment betas proof s h = some (.ok (query_pairs V.S s h2).2) := by
  have hd := hc.domain
  have hw := hc.word
  have hk := hc.lff_pos
  have hsv := hs
  rw [hc.shape] at hsv
  obtain ⟨hlenI, hltI⟩ := indices_facts V.S hc hs h2
  set idx := ((query_pairs V.S s h2).1).map (· <<< (c.log_folding_factor - 1)) with hidx
  have hF : proof.final_codeword.length = 2 ^ c.params.log_inv_rate := by simp [hfin]
  unfold verify_query_paths
  simp only [BinaryPcsConfig.num_fold_rounds, hb, ne_eq, not_true_eq_false, ite_false,
    check_round_and_final_lengths_eq hc, hc.domain_size, hc.fold_batches, Option.bind_eq_bind,
    Option.bind_some, hrl, hF, hcanon]
  set nb := (c.num_variables + c.log_folding_factor - 1) / c.log_folding_factor with hnb
  set B := (List.range nb).map fun b =>
    (b * c.log_folding_factor, min c.log_folding_factor (c.num_variables - b * c.log_folding_factor)) with hB
  have hnb0 : 0 < nb := hc.batches_pos
  have hBl : B.length = nb := by simp [hB]
  have hBi : ∀ i (hi : i < nb), B[i]? =
      some (i * c.log_folding_factor, min c.log_folding_factor (c.num_variables - i * c.log_folding_factor)) :=
    fun i hi => by simp [hB, List.getElem?_range hi]
  have hT : min c.num_queries (2 ^ (c.num_variables + c.params.log_inv_rate) >>> c.log_folding_factor) =
      idx.length := by
    rw [hlenI, Nat.shiftRight_eq_div_pow, Nat.pow_div (by have := hc.lff_le; omega) (by norm_num)]
  have hround_get : ∀ i (hi : i < nb - 1), proof.rounds[i]? = some (proof.rounds[i]'(by omega)) :=
    fun i hi => List.getElem?_eq_getElem _
  simp only [hBl, hBi 0 hnb0, Option.bind_some, zero_mul, Nat.sub_zero, hT]
  rw [check_round_shape_of 0 _ _ (by rw [hbase, honestRows_length, Nat.shiftLeft_eq])
    (by rw [hbase]; exact honestRows_width _ _ _ _)]
  rw [firstError_all_ok _ _ fun i hi => by
    have hi := List.mem_range.1 hi
    rw [hBi (i + 1) (by omega), hround_get i hi]
    simp only [Option.bind_some, pure]
    rw [check_round_shape_of _ _ _ (by rw [hround i (by omega), honestRows_length, Nat.shiftLeft_eq])
      (by rw [hround i (by omega)]; exact honestRows_width _ _ _ _)]]
  have hfc : final_codeword (F := F) s proof.final_codeword h = .ok (h ++ [.message proof.final_codeword]) := by
    cases hsv
    simp [final_codeword, hF]
  simp only [Option.bind_some, hfc, hpow, hk.ne', ite_false, ← hidx, hmb]
  rw [firstError_all_ok _ _ fun i hi => by
    have hi := List.mem_range.1 hi
    rw [hBi (i + 1) (by omega), hround_get i hi]
    simp only [Option.bind_some, pure, hmr i (by omega)]]
  rw [firstError_all_ok _ _ fun q hq => by
    have hq := List.mem_range.1 hq
    rw [List.getElem?_eq_getElem hq, Option.bind_some]
    exact firstError_all_ok _ _ fun batch hbatch => foldCheck_honest V hk hLF hLE hpre (by omega)
      (by omega) (by omega) d betas hb idx proof hbase hrl hround hfin hq (hltI _ (List.getElem_mem _))
      (by simpa [hBl] using List.mem_range.1 hbatch)]
  rfl

end Plonky3Lean.Proofs.BinaryPcs
