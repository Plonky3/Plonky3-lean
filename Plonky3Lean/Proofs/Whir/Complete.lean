module

public import Plonky3Lean.Proofs.Whir.Honest
public import Plonky3Lean.Proofs.MultilinearUtil.SplitEq

@[expose] public section

/-!
# Completeness of the WHIR verifier

The verifier accepts the honest prover's proof.
-/

namespace Plonky3Lean.Proofs.Whir

open Finset Plonky3Lean.Spec.MultilinearUtil Plonky3Lean.Spec.Whir Plonky3Lean.Proofs.MultilinearUtil
open p3_sumcheck.mirror p3_sumcheck.constraints.mirror p3_whir.mirror p3_whir.transcript.mirror
open p3_multilinear_util.point.mirror

set_option linter.unusedSectionVars false

variable {F EF Com MP D : Type _} [Field F] [Field EF] [Algebra F EF] [DecidableEq F] [DecidableEq EF]

/-! ## The out-of-domain phase -/

theorem oodProve_succ (S : WSponge F EF) (P : List EF) (nv : ℕ) (h : List (Step F EF)) (k : ℕ) :
    oodProve S P nv h (k + 1) =
      let o := oodProve S P nv h k
      let point := Point.expand_from_univariate (S.sample o.2.2) nv
      (o.1 ++ [point], o.2.1 ++ [mle P point], o.2.2 ++ [.challenge, .message [mle P point]]) := by
  simp [oodProve, List.range_succ]

theorem oodProve_length (S : WSponge F EF) (P : List EF) (nv : ℕ) (h : List (Step F EF)) :
    ∀ k, (oodProve S P nv h k).2.1.length = k
  | 0 => rfl
  | k + 1 => by rw [oodProve_succ]; simp [oodProve_length S P nv h k]

theorem oodProve_prefix (S : WSponge F EF) (P : List EF) (nv : ℕ) (h : List (Step F EF)) (k : ℕ) :
    ∀ j, ∃ ys, (oodProve S P nv h (k + j)).2.1 = (oodProve S P nv h k).2.1 ++ ys
  | 0 => ⟨[], by simp⟩
  | j + 1 => by
    obtain ⟨ys, hy⟩ := oodProve_prefix S P nv h k j
    rw [← add_assoc, oodProve_succ]
    exact ⟨ys ++ _, by simp only [hy, List.append_assoc]; rfl⟩

/-- The verifier's out-of-domain loop on the honest answers draws the prover's points.

It ends at the prover's history. -/
theorem ood_loop (S : WSponge F EF) (P : List EF) (nv : ℕ) (h : List (Step F EF)) {s : ℕ} :
    ∀ k ≤ s, (List.range k).foldl (fun (acc : List (List EF) × List (Step F EF)) i =>
        let z := S.sample acc.2
        (acc.1 ++ [Point.expand_from_univariate z nv],
          acc.2 ++ [.challenge, .message [(oodProve S P nv h s).2.1.getD i 0]])) ([], h) =
      ((oodProve S P nv h k).1, (oodProve S P nv h k).2.2)
  | 0, _ => rfl
  | k + 1, hk => by
    rw [List.range_succ, List.foldl_append, ood_loop S P nv h k (by omega), oodProve_succ]
    obtain ⟨ys, hy⟩ := oodProve_prefix S P nv h (k + 1) (s - (k + 1))
    rw [show k + 1 + (s - (k + 1)) = s by omega, oodProve_succ] at hy
    simp [hy, List.getD_eq_getElem?_getD, oodProve_length]

/-! ## Folding the opened rows -/

@[simp] theorem length_row (P : List EF) (n k : ℕ) (ω : EF) (i : ℕ) : (row P n k ω i).length = 2 ^ k := by
  simp [row]

omit [DecidableEq F] [DecidableEq EF] in
theorem uni_map (c : List F) (y : F) : algebraMap F EF (uni c y) = uni (c.map (algebraMap F EF)) (algebraMap F EF y) := by
  simp only [uni, map_sum, map_mul, map_pow, List.length_map]
  refine sum_congr rfl fun b _ => ?_
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases c[b]? <;> simp

omit [DecidableEq F] [DecidableEq EF] in
/-- A base-field row, lifted, is the row of the lifted table at the lifted generator. -/
theorem row_map (P : List F) (n k : ℕ) (ω : F) (i : ℕ) :
    (row P n k ω i).map (algebraMap F EF) = row (P.map (algebraMap F EF)) n k (algebraMap F EF ω) i := by
  simp only [row, List.map_map]
  refine List.map_congr_left fun j _ => ?_
  simp only [Function.comp, uni_map, block, List.map_take, List.map_drop, map_pow]

/-- The verifier's fold of an honest row is the folded table's polynomial at the row's domain point. -/
theorem folds_honest (thr w T : ℕ) (P : List EF) {nv : ℕ} (hP : P.length = 2 ^ nv) (r : List EF)
    (hr : r.length ≤ nv) (hr64 : r.length < 64) (ω : EF) (idx : List ℕ) :
    (idx.map (row P nv r.length ω)).mapM (fun a => (p3_multilinear_util.poly.mirror.Poly.new a).bind
      fun p => p3_multilinear_util.split_eq.mirror.Poly.eval_ext thr w T p r) =
      some (idx.map fun i => uni (foldTable P nv r) (ω ^ i)) := by
  induction idx with
  | nil => rfl
  | cons i idx ih =>
    simp only [List.map_cons, List.mapM_cons, Poly_new_pow _ (length_row P nv r.length ω i),
      poly_eval_ext_eq thr w T _ r hr64 (length_row P nv r.length ω i), mle_row P hP r hr,
      Option.bind_eq_bind, Option.bind_some, Option.pure_def, ih]

/-! ## Honest claims -/

/-- The claimed values of a group are the table's: P~ at each equality point, P^ at each scalar point. -/
def _root_.p3_sumcheck.constraints.mirror.Statements.Honest (P : List EF) : Statements F EF → Prop
  | .Eq s => s.evaluations = s.points.map (mle P)
  | .Select s => s.evaluations = s.vars.map fun v => uni P (algebraMap F EF v)

theorem sum_dot (N : ℕ) (P : ℕ → EF) (x : ℕ → List EF) :
    ∀ (gs : List (List EF → EF)) (pw : List EF),
      ∑ b ∈ range N, P b * dot (gs.map (· (x b))) pw = dot (gs.map fun g => ∑ b ∈ range N, P b * g (x b)) pw
  | [], _ => by simp [dot]
  | _ :: _, [] => by simp [dot]
  | g :: gs, p :: pw => by
    have ih := sum_dot N P x gs pw
    simp only [List.map_cons, dot, List.zipWith_cons_cons, List.sum_cons] at ih ⊢
    rw [← ih, sum_mul, ← sum_add_distrib]
    exact sum_congr rfl fun b _ => by ring

theorem weightAt_eq_fns (con : Constraint F EF) (y : List EF) :
    weightAt con y = dot ((con.statements.flatMap Statements.fns).map (· y))
      (powers con.challenge con.initial_power (con.statements.flatMap Statements.evals).length) := by
  simp only [weightAt, List.map_flatMap]
  congr 2
  funext s
  exact Statements.weights_eq s y

theorem fns_honest {s : Statements F EF} {P : List EF} {n : ℕ} (hP : P.length = 2 ^ n)
    (h : s.Dim n ∧ s.Honest P) :
    s.fns.map (fun g => ∑ b ∈ range (2 ^ n), P.getD b 0 * g (vertex n b)) = s.evals := by
  cases s with
  | Eq s =>
    have h2 : s.evaluations = s.points.map (mle P) := h.2
    have h1 : ∀ p ∈ s.points, p.length = n := h.1
    simp only [Statements.fns, Statements.evals, List.map_map, h2]
    refine List.map_congr_left fun p hp => ?_
    simp only [Function.comp, mle, h1 p hp]
    exact sum_congr rfl fun b _ => by rw [eq_comm', mul_comm]
  | Select s =>
    have h2 : s.evaluations = s.vars.map fun v => uni P (algebraMap F EF v) := h.2
    simp only [Statements.fns, Statements.evals, List.map_map, h2]
    exact List.map_congr_left fun v _ => cubeDot_sel P hP _

/-- With honest claims, a constraint's claim is the sum of the table against its weight table. -/
theorem combine_evals_honest (con : Constraint F EF) (P : List EF) {n : ℕ} (hP : P.length = 2 ^ n) (σ : EF)
    (h : ∀ s ∈ con.statements, s.WF ∧ s.Dim n ∧ s.Honest P) :
    con.combine_evals σ = σ + ∑ b ∈ range (2 ^ n), P.getD b 0 * (cubeTable (weightAt con) n).getD b 0 := by
  rw [Constraint.combine_evals_eq con σ fun s hs => (h s hs).1]
  congr 1
  rw [sum_congr rfl fun b hb => by rw [getD_cubeTable _ (mem_range.mp hb), weightAt_eq_fns],
    sum_dot (2 ^ n) (fun b => P.getD b 0) (vertex n), List.map_flatMap]
  congr 1
  exact (List.flatMap_congr fun s hs => fns_honest hP ⟨(h s hs).2.1, (h s hs).2.2⟩).symm

/-! ## Query indices -/

theorem query_summand_depths_le : ∀ m, ∀ d ∈ query_summand_depths m, 2 ^ d ≤ m := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro d hd
    unfold query_summand_depths at hd
    split at hd
    · simp at hd
    · rcases List.mem_cons.mp hd with rfl | hd
      · exact Nat.pow_log_le_self 2 (by omega)
      · have := ih _ (Nat.sub_lt (by omega) (Nat.two_pow_pos _)) d hd
        have := Nat.two_pow_pos (Nat.log 2 m)
        omega

theorem query_draws_cases (f q : ℕ) : query_draws f q = 0 ∨ query_draws f q < f := by
  unfold query_draws; split_ifs <;> omega

theorem querySite_spec {D k q p : ℕ} {s : QuerySite} (h : querySite D k q p = some s) :
    s.pow_bits = p ∧ 2 ^ s.index_bits = D >>> k ∧ s.draws = query_draws (D >>> k) q ∧
      s.depths = query_summand_depths s.draws := by
  simp only [querySite] at h
  split at h
  · next hc => cases h; exact ⟨rfl, hc.2, rfl, rfl⟩
  · cases h

/-- Every index the query phase plays lies in the folded domain, when each draw does. -/
theorem play_query_indices_lt (S : WSponge F EF) (hidx : ∀ h bits count, ∀ i ∈ S.indices h bits count, i < 2 ^ bits)
    (hlen : ∀ h bits count, (S.indices h bits count).length = count) (h : List (Step F EF)) {width draws : ℕ}
    (hd : draws = 0 ∨ draws < 2 ^ width) (stratified : Bool) :
    ∀ i ∈ (play_query_indices S h width draws stratified (query_summand_depths draws)).1, i < 2 ^ width := by
  unfold play_query_indices
  split_ifs with h0 h1
  · simp
  · exact hidx _ _ _
  · have hdep : ∀ d ∈ query_summand_depths draws, d < width := fun d hd' => by
      have := query_summand_depths_le draws d hd'
      have : 2 ^ d < 2 ^ width := by omega
      exact (Nat.pow_lt_pow_iff_right (by norm_num)).mp this
    suffices ∀ (ds : List ℕ), (∀ d ∈ ds, d < width) → ∀ acc : List ℕ × List (Step F EF), (∀ i ∈ acc.1, i < 2 ^ width) →
        ∀ i ∈ (ds.foldl (fun (acc : List ℕ × List (Step F EF)) depth =>
          ((acc.1 ++ (List.range (draw S acc.2 (width - depth) (2 ^ depth)).1.length).map fun s =>
            stratified_index width depth s ((draw S acc.2 (width - depth) (2 ^ depth)).1.getD s 0)),
            (draw S acc.2 (width - depth) (2 ^ depth)).2)) acc).1, i < 2 ^ width from
      this _ hdep ([], h) (by simp)
    intro ds
    induction ds with
    | nil => exact fun _ acc hacc => hacc
    | cons d ds ih =>
      intro hds acc hacc
      refine ih (fun t ht => hds t (by simp [ht])) _ fun i hi => ?_
      rcases List.mem_append.mp hi with hi | hi
      · exact hacc i hi
      · obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hi
        have hdw := hds d (by simp)
        have hs' : s < 2 ^ d := by simpa [draw, hlen] using hs
        have hlow : (draw S acc.2 (width - d) (2 ^ d)).1.getD s 0 < 2 ^ (width - d) := by
          simp only [draw, List.getD_eq_getElem?_getD]
          rw [List.getElem?_eq_getElem (by rw [hlen]; exact hs')]
          exact hidx _ _ _ _ (List.getElem_mem _)
        unfold stratified_index
        rw [Nat.shiftLeft_eq]
        refine Nat.or_lt_two_pow ?_ (lt_of_lt_of_le hlow (Nat.pow_le_pow_right (by norm_num) (by omega)))
        calc s * 2 ^ (width - d) < 2 ^ d * 2 ^ (width - d) := by
              exact Nat.mul_lt_mul_of_pos_right hs' (Nat.two_pow_pos _)
          _ = 2 ^ width := by rw [← pow_add]; congr 1; omega

/-! ## The assumptions of completeness -/

/-- The configuration is consistent, as the Rust derivation makes it.

Every folded domain fits the two-adicity. -/
structure Valid (c : WhirConfig) (n adicity : ℕ) : Prop where
  schedule : c.n_rounds < c.folding_schedule.length
  folding : ∀ t ≤ c.n_rounds, (queried c t).folding_factor = c.folding_schedule.getD t 0
  small : ∀ t ≤ c.n_rounds, c.folding_schedule.getD t 0 < 64
  vars0 : n = (queried c 0).num_variables + c.folding_schedule.getD 0 0
  vars : ∀ t < c.n_rounds, (queried c t).num_variables = (queried c (t + 1)).num_variables + c.folding_schedule.getD (t + 1) 0
  final : c.final_round_config.num_variables = c.final_sumcheck_rounds ∧ c.final_sumcheck_rounds < 64
  sites : ∀ t ≤ c.n_rounds, (c.site t).isSome
  final_pow : c.final_round_config.pow_bits = c.terminal_pow_bits
  adicity : ∀ t ≤ c.n_rounds, (queried c t).log_folded_domain_size ≤ adicity

variable (E : Env F EF Com MP) (PE : ProverEnv F EF Com MP D) (c : WhirConfig)

/-- What completeness assumes of the sponge, the Merkle scheme and the layout. -/
structure Honesty (P0 : List F) (n : ℕ) (commitment : Com) : Prop where
  table : P0.length = 2 ^ n
  solve : ∀ h b, 0 < b → E.S.grind h b (PE.solve h b) = true
  indices : ∀ h bits count, ∀ i ∈ E.S.indices h bits count, i < 2 ^ bits
  count : ∀ h bits count, (E.S.indices h bits count).length = count
  base : ∀ idx : List ℕ, (∀ i ∈ idx, i < (queried c 0).domain_size >>> (queried c 0).folding_factor) →
    E.mmcs.verifyBase commitment ((queried c 0).domain_size >>> (queried c 0).folding_factor,
      2 ^ (queried c 0).folding_factor) idx
      (idx.map (row P0 n (queried c 0).folding_factor (E.gen (queried c 0).log_folded_domain_size)))
      (PE.openBase idx) = true
  ext : ∀ (M : List (List EF)) (idx : List ℕ) (H W : ℕ), M.length = H → (∀ r ∈ M, r.length = W) →
    (∀ i ∈ idx, i < H) →
    E.mmcs.verifyExt (PE.commit M).1 (H, W) idx (idx.map (M.getD · [])) (PE.openExt (PE.commit M).2 idx) = true
  layout : ∀ α, (E.initial α).num_variables = n ∧
    ∀ s ∈ (E.initial α).statements, s.WF ∧ s.Dim n ∧ s.Honest (P0.map (algebraMap F EF))

/-! ## The invariant between rounds -/

/-- The variable count of the table queried in round t. -/
def nvAt (t : ℕ) : ℕ := (queried c t).num_variables

/-- The number of variables folded before the queries of round t. -/
def kAt (t : ℕ) : ℕ := c.folding_schedule.getD t 0

/-- The honest state after t rounds. -/
structure Inv (P0 : List F) (n : ℕ) (commitment : Com) (t : ℕ) (st : PState F EF Com MP D) : Prop where
  lenP : st.P.length = 2 ^ nvAt c t
  lenW : st.Wt.length = 2 ^ nvAt c t
  claimSum : st.claim = ∑ b ∈ range (2 ^ nvAt c t), st.P.getD b 0 * st.Wt.getD b 0
  weight : ∀ y : List EF, y.length = nvAt c t → mle st.Wt y =
    (st.cons.map fun con => weightAt con
      ((st.rand.flatten ++ y).drop ((st.rand.flatten ++ y).length - con.num_variables))).sum
  cons : ∀ con ∈ st.cons, con.num_variables ≤ st.rand.flatten.length + nvAt c t ∧
    ∀ s ∈ con.statements, s.WF ∧ s.Dim con.num_variables
  last : ∃ r, st.rand.getLast? = some r ∧ r.length = kAt c t ∧ st.P = foldTable st.prevP st.prevNv r
  prevLen : st.prevP.length = 2 ^ st.prevNv
  prevNv : st.prevNv = nvAt c t + kAt c t
  code0 : t = 0 → st.prevData = none ∧ st.prevP = P0.map (algebraMap F EF) ∧ st.prevRoot = commitment
  codeS : t ≠ 0 → st.prevData = some (PE.commit (codeRows E c st.prevP st.prevNv t)).2 ∧
    st.prevRoot = (PE.commit (codeRows E c st.prevP st.prevNv t)).1
  rounds : st.rounds.length = t

/-- The honest sumcheck on two tables of 2^nv entries, for k <= nv rounds.

It gives the lengths, the folds and the replayed claim. -/
theorem honestSumcheck_spec (S : Sponge F EF) (solve : List (Step F EF) → ℕ → F) (pow : ℕ) (f w : List EF)
    (h : List (Step F EF)) {nv k : ℕ} (hf : f.length = 2 ^ nv) (hw : w.length = 2 ^ nv) (hk : k ≤ nv) :
    let H := honestSumcheck S solve pow f w h k
    H.rs.length = k ∧ H.f.length = 2 ^ (nv - k) ∧ H.w.length = 2 ^ (nv - k) ∧ H.f = foldTable f nv H.rs ∧
      H.w = foldTable w nv H.rs ∧
      Plonky3Lean.Proofs.Sumcheck.replay .Evaluation (∑ b ∈ range (2 ^ nv), f.getD b 0 * w.getD b 0) H.ms H.rs =
        ∑ i ∈ range (2 ^ (nv - k)), H.f.getD i 0 * H.w.getD i 0 := by
  intro H
  obtain ⟨-, -, hl⟩ := proverRun_ms S solve pow
    ⟨[], [], [], f, w, if 0 < k then h ++ [SumcheckShape.seed k pow .Evaluation] else h⟩ k
  exact ⟨by simpa [H, honestSumcheck] using hl, proverRun_tables S solve pow f w _ hf hw k hk⟩

/-- The weight table after a sumcheck on it.

Its extension at y is the extension before, at the challenges then y. -/
theorem mle_fold_weight (w rs y : List EF) {nv : ℕ} (h : rs.length + y.length = nv) :
    mle (foldTable w nv rs) y = mle w (rs ++ y) := by
  rw [← h, mle_foldTable]

/-! ## The initial fold -/

theorem inv_init {P0 : List F} {n adicity : ℕ} {commitment : Com} (hv : Valid c n adicity)
    (hh : Honesty E PE c P0 n commitment) (h : List (Step F EF)) :
    Inv E PE c P0 n commitment 0 (honestInit E PE c P0 n commitment h).1 := by
  set con := E.initial (E.S.sample (h ++ [E.layoutSeed]))
  obtain ⟨hcn, hcs⟩ := hh.layout (E.S.sample (h ++ [E.layoutSeed]))
  have hP : (P0.map (algebraMap F EF)).length = 2 ^ n := by simp [hh.table]
  have hk : c.folding_schedule.getD 0 0 ≤ n := by rw [hv.vars0]; omega
  have hnv : n - c.folding_schedule.getD 0 0 = nvAt c 0 := by unfold nvAt; rw [hv.vars0]; omega
  obtain ⟨hrs, hlf, hlw, hff, hfw, hrep⟩ := honestSumcheck_spec E.S.toSponge PE.solve c.starting_folding_pow_bits
    (P0.map (algebraMap F EF)) (cubeTable (weightAt con) n) (h ++ [E.layoutSeed, .challenge]) hP
    (length_cubeTable _ _) hk
  rw [hnv] at hlf hlw hrep
  refine ⟨hlf, hlw, ?_, ?_, ?_, ⟨_, rfl, hrs, hff⟩, hP, ?_, fun _ => ⟨rfl, rfl, rfl⟩, fun h0 => absurd rfl h0, rfl⟩
  · simp only [honestInit]
    rw [combine_evals_honest con _ hP 0 hcs, zero_add, hrep]
  · intro y hy
    simp only [honestInit, List.flatten_cons, List.flatten_nil, List.append_nil, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, add_zero]
    rw [hfw, mle_fold_weight _ _ _ (by rw [hrs, hy, ← hnv]; omega), List.length_append, hrs, hy, hcn,
      show c.folding_schedule.getD 0 0 + nvAt c 0 - n = 0 by rw [← hnv]; omega, List.drop_zero,
      isML_weightAt con (fun s hs => (hcs s hs).2.1) _ (by rw [List.length_append, hrs, hy, ← hnv]; omega)]
  · intro con' hc'
    simp only [honestInit, List.mem_singleton] at hc'
    subst hc'
    refine ⟨?_, fun s hs => ⟨(hcs s hs).1, hcn ▸ (hcs s hs).2.1⟩⟩
    simp only [honestInit, List.flatten_cons, List.flatten_nil, List.append_nil]
    rw [hrs, hcn, ← hnv]
    omega
  · simp only [honestInit, kAt]
    rw [← hnv]; omega

/-! ## One round -/

theorem oodProve_honest (S : WSponge F EF) (P : List EF) (nv : ℕ) (h : List (Step F EF)) :
    ∀ k, (oodProve S P nv h k).2.1 = (oodProve S P nv h k).1.map (mle P) ∧
      ∀ p ∈ (oodProve S P nv h k).1, p.length = nv
  | 0 => ⟨rfl, by simp [oodProve]⟩
  | k + 1 => by
    obtain ⟨h1, h2⟩ := oodProve_honest S P nv h k
    rw [oodProve_succ]
    refine ⟨by simp [h1], fun p hp => ?_⟩
    rcases List.mem_append.mp hp with hp | hp
    · exact h2 p hp
    · simp only [List.mem_singleton] at hp
      simp [hp, expand_from_univariate_eq]

theorem getD_zipWith_add {a b : List EF} (hab : a.length = b.length) (i : ℕ) :
    (List.zipWith (· + ·) a b).getD i 0 = a.getD i 0 + b.getD i 0 := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_zipWith]
  by_cases hi : i < a.length
  · simp [List.getElem?_eq_getElem hi, List.getElem?_eq_getElem (hab ▸ hi)]
  · simp [List.getElem?_eq_none (Nat.le_of_not_lt hi), List.getElem?_eq_none (hab ▸ Nat.le_of_not_lt hi)]

theorem getD_codeRows (P : List EF) (nv t : ℕ) {i : ℕ}
    (hi : i < (queried c t).domain_size >>> (queried c t).folding_factor) :
    (codeRows E c P nv t).getD i [] =
      row P nv (queried c t).folding_factor (algebraMap F EF (E.gen (queried c t).log_folded_domain_size)) i := by
  simp [codeRows, List.getD_eq_getElem?_getD, hi]

theorem site_queried {t : ℕ} {s : QuerySite} (hs : c.site t = some s) :
    s.pow_bits = (if t < c.n_rounds then (queried c t).pow_bits else c.terminal_pow_bits) ∧
      ∃ k, (t < c.n_rounds → c.round_folding_factor t = some k) ∧ (¬ t < c.n_rounds → k = (queried c t).folding_factor) ∧
        2 ^ s.index_bits = (queried c t).domain_size >>> k ∧
        s.draws = query_draws ((queried c t).domain_size >>> k) (if t < c.n_rounds then (queried c t).num_queries else c.terminal_num_queries) ∧
        s.depths = query_summand_depths s.draws := by
  unfold WhirConfig.site at hs
  by_cases ht : t < c.n_rounds
  · simp only [ht, ↓reduceIte] at hs ⊢
    obtain ⟨p, hp, hs⟩ := Option.bind_eq_some_iff.mp hs
    obtain ⟨k, hk, hs⟩ := Option.bind_eq_some_iff.mp hs
    have hq : queried c t = p := by
      simp only [queried, ht, ↓reduceIte, List.getD_eq_getElem?_getD, hp, Option.getD_some]
    obtain ⟨h1, h2, h3, h4⟩ := querySite_spec hs
    exact ⟨by rw [hq, h1], k, fun _ => hk, fun h => absurd trivial h, by rw [hq, h2], by rw [hq, h3], h4⟩
  · simp only [ht, ↓reduceIte] at hs ⊢
    have hq : queried c t = c.final_round_config := by simp [queried, ht]
    obtain ⟨h1, h2, h3, h4⟩ := querySite_spec hs
    exact ⟨h1, _, fun h => h.elim, fun _ => by rw [hq], by rw [hq, h2], by rw [hq, h3], h4⟩

theorem query_pow_honest (S : WSponge F EF) (solve : List (Step F EF) → ℕ → F)
    (hsolve : ∀ h b, 0 < b → S.grind h b (solve h b) = true) (E' : Env F EF Com MP) (hS : E'.S = S)
    (round bits : ℕ) (h : List (Step F EF)) :
    query_pow E' round bits (if bits = 0 then 0 else solve h bits) h =
      .ok (if bits = 0 then h else h ++ [.pow bits (solve h bits)]) := by
  unfold query_pow
  by_cases hb : bits = 0
  · simp [hb]; rfl
  · simp [hb, hS, hsolve h bits (Nat.pos_of_ne_zero hb)]; rfl

/-- The STIR phase on the honest openings.

It gives the selector statement of the folded table at the queried points. -/
theorem stir_honest {P0 : List F} {n : ℕ} {commitment : Com} (hv : Valid c n E.adicity)
    (hh : Honesty E PE c P0 n commitment) {t : ℕ} (ht : t ≤ c.n_rounds) {st : PState F EF Com MP D}
    (hinv : Inv E PE c P0 n commitment t st) {r : List EF} (hr : st.rand.getLast? = some r)
    {s : QuerySite} (hs : c.site t = some s) (h0 : List (Step F EF)) :
    let h1 := if s.pow_bits = 0 then h0 else h0 ++ [.pow s.pow_bits (PE.solve h0 s.pow_bits)]
    let qi := play_query_indices E.S h1 s.index_bits s.draws c.stratified_queries s.depths
    let g := E.gen (queried c t).log_folded_domain_size
    verify_stir_challenges E c (openPrev E PE c P0 n st t qi.1)
      (if s.pow_bits = 0 then 0 else PE.solve h0 s.pow_bits) (queried c t) st.prevRoot r t h0 =
      some (.ok (⟨(queried c t).num_variables, qi.1.map (g ^ ·),
        qi.1.map fun i => uni st.P (algebraMap F EF (g ^ i))⟩, qi.2)) := by
  intro h1 qi g
  obtain ⟨-, k, hk1, hk2, hbits, hdraws, hdepths⟩ := site_queried c hs
  have hk : k = (queried c t).folding_factor := by
    by_cases htn : t < c.n_rounds
    · have := hk1 htn
      simp only [WhirConfig.round_folding_factor] at this
      rw [hv.folding t ht, List.getD_eq_getElem?_getD, this, Option.getD_some]
    · exact hk2 htn
  obtain ⟨r', hr', hrlen, hrP⟩ := hinv.last
  rw [hr] at hr'
  cases hr'
  have hidx : ∀ i ∈ qi.1, i < (queried c t).domain_size >>> (queried c t).folding_factor := by
    intro i hi
    rw [← hk, ← hbits]
    refine play_query_indices_lt E.S hh.indices hh.count h1 (width := s.index_bits) (draws := s.draws) ?_
      c.stratified_queries i ?_
    · rw [hdraws, hbits]; exact query_draws_cases _ _
    · rw [← hdepths]; exact hi
  have hqk : (queried c t).folding_factor = r.length := by rw [hrlen, kAt, hv.folding t ht]
  have hrows : verify_merkle_proof E (openPrev E PE c P0 n st t qi.1) st.prevRoot qi.1
      ((queried c t).domain_size >>> (queried c t).folding_factor, 2 ^ (queried c t).folding_factor) t =
      .ok (qi.1.map (row st.prevP st.prevNv r.length (algebraMap F EF g))) := by
    rw [← hqk]
    by_cases ht0 : t = 0
    · obtain ⟨hd, hpp, hroot⟩ := hinv.code0 ht0
      subst ht0
      have hnv : st.prevNv = n := by rw [hinv.prevNv, hv.vars0]; rfl
      simp only [openPrev, hd, verify_merkle_proof, beq_self_eq_true, List.length_map, ne_eq,
        not_true_eq_false, ↓reduceIte, hroot, hh.base qi.1 hidx, List.map_map]
      congr 1
      refine List.map_congr_left fun i _ => ?_
      rw [Function.comp_apply, row_map, hpp, hnv]
    · obtain ⟨hd, hroot⟩ := hinv.codeS ht0
      have hM := hh.ext (codeRows E c st.prevP st.prevNv t) qi.1 _ (2 ^ (queried c t).folding_factor)
        (by simp [codeRows]) (fun row hrow => by
          obtain ⟨i, -, rfl⟩ := List.mem_map.mp hrow
          exact length_row _ _ _ _ _) hidx
      simp only [openPrev, hd, verify_merkle_proof, List.length_map, ne_eq, not_true_eq_false, ↓reduceIte,
        hroot, hM, show (t == 0) = false from by simpa using ht0]
      congr 1
      exact List.map_congr_left fun i hi => getD_codeRows E c _ _ t (hidx i hi)
  simp only [verify_stir_challenges, hs, Option.bind_eq_bind, Option.bind_some, bind_pure_comp]
  rw [query_pow_honest E.S PE.solve hh.solve E rfl]
  simp only
  erw [hrows]
  simp only
  rw [hqk] at hidx
  rw [folds_honest E.thr E.w E.T st.prevP hinv.prevLen r (by rw [hinv.prevNv, hrlen]; omega)
    (by rw [hrlen, kAt]; exact hv.small t ht)]
  simp [two_adic_generator, hv.adicity t ht, g, hrP, map_pow]
  exact ⟨rfl, rfl⟩

/-- The verifier parses the honest round.

It reads the root, then the prover's out-of-domain points and answers. -/
theorem parse_honest (root : Com) (P : List EF) (nv s t : ℕ) (h : List (Step F EF)) (pw : F)
    (op : QueryOpenings F EF MP) (sc : SumcheckData F EF) :
    let o := oodProve E.S P nv (h ++ [.message (E.enc root)]) s
    parse_with_round E ⟨some root, o.2.1, pw, op, sc⟩ nv s t h = .ok (root, ⟨nv, o.1, o.2.1⟩, o.2.2) := by
  intro o
  have := ood_loop E.S P nv (h ++ [.message (E.enc root)]) s le_rfl
  simp only [parse_with_round, oodProve_length, ne_eq, not_true_eq_false, ↓reduceIte, o] at this ⊢
  rw [this]
  rfl

theorem new_with_existing_claim_eq (γ : EF) (nv : ℕ) (L : List (Statements F EF))
    (h : ∀ s ∈ L, s.num_variables = nv) : Constraint.new_with_existing_claim γ nv L = some ⟨nv, L, γ, 1⟩ := by
  simp only [Constraint.new_with_existing_claim, Constraint.new, List.all_eq_true, beq_iff_eq]
  split_ifs with hc
  · rfl
  · exact absurd h hc

theorem queried_lt {t : ℕ} (ht : t < c.n_rounds) : c.round_parameters[t]? = some (queried c t) := by
  simp only [queried, ht, ↓reduceIte, List.getD_eq_getElem?_getD]
  rw [List.getElem?_eq_getElem ht, Option.getD_some]

/-- The verifier's round accepts one honest round, and the invariant moves to the next round. -/
theorem round_honest {P0 : List F} {n : ℕ} {commitment : Com} (hv : Valid c n E.adicity)
    (hh : Honesty E PE c P0 n commitment) {t : ℕ} (ht : t < c.n_rounds) {st : PState F EF Com MP D}
    (hinv : Inv E PE c P0 n commitment t st) (proof : WhirProof F EF Com MP)
    (hp : proof.rounds[t]? = (honestRound E PE c P0 n st t).rounds[t]?) :
    let st' := honestRound E PE c P0 n st t
    roundStep E c proof ⟨st.cons, st.rand, st.prevRoot, st.claim, st.h⟩ t =
      some (.ok ⟨st'.cons, st'.rand, st'.prevRoot, st'.claim, st'.h⟩) ∧ Inv E PE c P0 n commitment (t + 1) st' := by
  intro st'
  obtain ⟨s, hs⟩ := Option.isSome_iff_exists.mp (hv.sites t ht.le)
  obtain ⟨hspow, -⟩ := site_queried c hs
  simp only [ht, ↓reduceIte] at hspow
  obtain ⟨r, hr, hrlen, hrP⟩ := hinv.last
  have hq : c.round_parameters.getD t default = queried c t := by simp [queried, ht]
  set nv := (queried c t).num_variables
  set rd := PE.commit (codeRows E c st.P nv (t + 1))
  set o := oodProve E.S st.P nv (st.h ++ [.message (E.enc rd.1)]) (queried c t).ood_samples
  set h1 := if s.pow_bits = 0 then o.2.2 else o.2.2 ++ [.pow s.pow_bits (PE.solve o.2.2 s.pow_bits)]
  set qi := play_query_indices E.S h1 s.index_bits s.draws c.stratified_queries s.depths
  set g := E.gen (queried c t).log_folded_domain_size
  set con : Constraint F EF := ⟨nv, [.Eq ⟨nv, o.1, o.2.1⟩,
    .Select ⟨nv, qi.1.map (g ^ ·), qi.1.map fun i => uni st.P (algebraMap F EF (g ^ i))⟩], E.S.sample qi.2, 1⟩
  set Wt' := List.zipWith (· + ·) st.Wt (cubeTable (weightAt con) nv)
  set H := honestSumcheck E.S.toSponge PE.solve (queried c t).folding_pow_bits st.P Wt' (qi.2 ++ [.challenge])
    (c.folding_schedule.getD (t + 1) 0)
  have hst' : st' =
      { P := H.f, Wt := H.w,
        claim := Plonky3Lean.Proofs.Sumcheck.replay .Evaluation (con.combine_evals st.claim) H.ms H.rs,
        cons := st.cons ++ [con], rand := st.rand ++ [H.rs], h := H.h, prevP := st.P, prevNv := nv,
        prevData := some rd.2, prevRoot := rd.1,
        rounds := st.rounds ++ [⟨some rd.1, o.2.1, if s.pow_bits = 0 then 0 else PE.solve o.2.2 s.pow_bits,
          openPrev E PE c P0 n st t qi.1, (H.ms, H.ws)⟩] } := by
    simp only [st', honestRound, hq, hs, Option.getD_some, ← hspow]
    rfl
  have hrec : proof.rounds[t]? = some ⟨some rd.1, o.2.1, if s.pow_bits = 0 then 0 else PE.solve o.2.2 s.pow_bits,
      openPrev E PE c P0 n st t qi.1, (H.ms, H.ws)⟩ := by
    rw [hp]
    show st'.rounds[t]? = _
    rw [hst']
    simp [hinv.rounds]
  have hk1 : c.round_folding_factor (t + 1) = some (c.folding_schedule.getD (t + 1) 0) := by
    simp only [WhirConfig.round_folding_factor, List.getD_eq_getElem?_getD]
    rw [List.getElem?_eq_getElem (by have := hv.schedule; omega),
      Option.getD_some]
  constructor
  · rw [hst']
    simp only [roundStep, queried_lt c ht, hrec, Option.bind_eq_bind, Option.bind_some]
    rw [parse_honest]
    simp only [hr, Option.bind_some]
    rw [stir_honest E PE c hv hh ht.le hinv hr hs]
    simp only [Option.bind_some]
    rw [new_with_existing_claim_eq _ _ _ (by
      simp only [List.mem_cons, List.mem_nil_iff, or_false]; rintro _ (rfl | rfl) <;> rfl)]
    simp only [Option.bind_some, hk1, sumcheck, H, Wt']
    rw [verify_rounds_honest E.S.toSponge PE.solve hh.solve]
    rfl
  · rw [hst']
    have hvars : nv = nvAt c (t + 1) + c.folding_schedule.getD (t + 1) 0 := hv.vars t ht
    have hP : st.P.length = 2 ^ nv := hinv.lenP
    have hWt : st.Wt.length = 2 ^ nv := hinv.lenW
    have hW : Wt'.length = 2 ^ nv := by
      simp only [Wt', List.length_zipWith, length_cubeTable, hWt, min_self]
    obtain ⟨hrs, hlf, hlw, hff, hfw, hrep⟩ := honestSumcheck_spec E.S.toSponge PE.solve
      (queried c t).folding_pow_bits st.P Wt' (qi.2 ++ [.challenge]) hP hW
      (k := c.folding_schedule.getD (t + 1) 0) (by omega)
    have hnv' : nv - c.folding_schedule.getD (t + 1) 0 = nvAt c (t + 1) := by omega
    rw [hnv'] at hlf hlw hrep
    have hrs' : H.rs.length = c.folding_schedule.getD (t + 1) 0 := hrs
    have hnvt : nvAt c t = nv := rfl
    obtain ⟨hooh, hood⟩ := oodProve_honest E.S st.P nv (st.h ++ [.message (E.enc rd.1)]) (queried c t).ood_samples
    have hcon : ∀ s ∈ con.statements, s.WF ∧ s.Dim nv ∧ s.Honest st.P := by
      simp only [con, List.mem_cons, List.mem_nil_iff, or_false]
      rintro _ (rfl | rfl)
      · exact ⟨((congrArg List.length hooh).trans (List.length_map _)).symm, hood, hooh⟩
      · exact ⟨by simp [Statements.WF], trivial, by simp [Statements.Honest, Function.comp]⟩
    refine ⟨hlf, hlw, ?_, ?_, ?_, ⟨H.rs, by simp, hrs, hff⟩, hP, hvars, fun h => absurd h (by omega),
      fun _ => ⟨rfl, rfl⟩, by simp [hinv.rounds]⟩
    · rw [← hrep, combine_evals_honest con st.P hP st.claim hcon, hinv.claimSum]
      show Plonky3Lean.Proofs.Sumcheck.replay .Evaluation (∑ b ∈ range (2 ^ nv), st.P.getD b 0 * st.Wt.getD b 0 +
        ∑ b ∈ range (2 ^ nv), st.P.getD b 0 * (cubeTable (weightAt con) nv).getD b 0) H.ms H.rs = _
      rw [← sum_add_distrib]
      congr 1
      exact sum_congr rfl fun b _ => by rw [getD_zipWith_add (by simp [hWt]), mul_add]
    · intro y hy
      rw [hfw, mle_fold_weight _ _ _ (by rw [hrs, hy]; omega), mle_add_tables (by simp [hWt]),
        hinv.weight _ (by rw [List.length_append, hrs, hy]; omega),
        isML_weightAt con (fun s hs => (hcon s hs).2.1) _ (by rw [List.length_append, hrs, hy]; omega)]
      simp only [List.flatten_append, List.flatten_cons, List.flatten_nil, List.append_nil, List.map_append,
        List.map_cons, List.map_nil, List.sum_append, List.sum_cons, List.sum_nil, add_zero, List.append_assoc]
      congr 1
      rw [List.length_append, List.length_append, hrs, hy, show con.num_variables = nv from rfl,
        show st.rand.flatten.length + (c.folding_schedule.getD (t + 1) 0 + nvAt c (t + 1)) - nv =
          st.rand.flatten.length by omega,
        List.drop_left]
    · intro c' hc'
      rcases List.mem_append.mp hc' with hc' | hc'
      · obtain ⟨h1, h2⟩ := hinv.cons c' hc'
        refine ⟨?_, h2⟩
        simp only [List.flatten_append, List.flatten_cons, List.flatten_nil, List.append_nil, List.length_append]
        omega
      · simp only [List.mem_singleton] at hc'
        subst hc'
        refine ⟨?_, fun s hs => ⟨(hcon s hs).1, (hcon s hs).2.1⟩⟩
        simp only [List.flatten_append, List.flatten_cons, List.flatten_nil, List.append_nil, List.length_append]
        show nv ≤ _
        omega

/-! ## Every round -/

/-- The honest state after the initial fold and t rounds. -/
def stAt (P0 : List F) (n : ℕ) (commitment : Com) (h : List (Step F EF)) (t : ℕ) : PState F EF Com MP D :=
  (List.range t).foldl (honestRound E PE c P0 n) (honestInit E PE c P0 n commitment h).1

theorem stAt_succ (P0 : List F) (n : ℕ) (commitment : Com) (h : List (Step F EF)) (t : ℕ) :
    stAt E PE c P0 n commitment h (t + 1) = honestRound E PE c P0 n (stAt E PE c P0 n commitment h t) t := by
  simp [stAt, List.range_succ]

theorem honestRound_rounds (P0 : List F) (n : ℕ) (st : PState F EF Com MP D) (t : ℕ) :
    ∃ rec, (honestRound E PE c P0 n st t).rounds = st.rounds ++ [rec] := ⟨_, rfl⟩

theorem stAt_rounds_prefix (P0 : List F) (n : ℕ) (commitment : Com) (h : List (Step F EF)) (t : ℕ) :
    ∀ j, ∃ l, (stAt E PE c P0 n commitment h (t + j)).rounds = (stAt E PE c P0 n commitment h t).rounds ++ l
  | 0 => ⟨[], by simp⟩
  | j + 1 => by
    obtain ⟨l, hl⟩ := stAt_rounds_prefix P0 n commitment h t j
    obtain ⟨rec, hrec⟩ := honestRound_rounds E PE c P0 n (stAt E PE c P0 n commitment h (t + j)) (t + j)
    exact ⟨l ++ [rec], by rw [← add_assoc, stAt_succ, hrec, hl, List.append_assoc]⟩

/-- The view the verifier's loop keeps of a prover state. -/
def view (st : PState F EF Com MP D) : LoopState F EF Com := ⟨st.cons, st.rand, st.prevRoot, st.claim, st.h⟩

/-- The verifier's loop over every round runs the honest rounds, and the invariant holds at the end. -/
theorem loop_honest {P0 : List F} {n : ℕ} {commitment : Com} (hv : Valid c n E.adicity)
    (hh : Honesty E PE c P0 n commitment) (h : List (Step F EF)) (proof : WhirProof F EF Com MP)
    (hp : proof.rounds = (stAt E PE c P0 n commitment h c.n_rounds).rounds) :
    ∀ t ≤ c.n_rounds, (List.range t).foldlM (loopStep E c proof) (.ok (view (stAt E PE c P0 n commitment h 0))) =
      some (.ok (view (stAt E PE c P0 n commitment h t))) ∧ Inv E PE c P0 n commitment t (stAt E PE c P0 n commitment h t)
  | 0, _ => ⟨rfl, inv_init E PE c hv hh h⟩
  | t + 1, ht => by
    obtain ⟨ih, hinv⟩ := loop_honest hv hh h proof hp t (by omega)
    have hpt : proof.rounds[t]? = (honestRound E PE c P0 n (stAt E PE c P0 n commitment h t) t).rounds[t]? := by
      obtain ⟨l, hl⟩ := stAt_rounds_prefix E PE c P0 n commitment h (t + 1) (c.n_rounds - (t + 1))
      rw [show t + 1 + (c.n_rounds - (t + 1)) = c.n_rounds by omega] at hl
      obtain ⟨rec, hrec⟩ := honestRound_rounds E PE c P0 n (stAt E PE c P0 n commitment h t) t
      rw [hp, hl, stAt_succ, hrec]
      simp [hinv.rounds]
    obtain ⟨hstep, hinv'⟩ := round_honest E PE c hv hh (show t < c.n_rounds by omega) hinv proof hpt
    refine ⟨?_, by rw [stAt_succ]; exact hinv'⟩
    rw [List.range_succ, List.foldlM_append, ih]
    simp only [List.foldlM_cons, List.foldlM_nil, Option.bind_eq_bind, Option.bind_some, loopStep]
    rw [show roundStep E c proof (view (stAt E PE c P0 n commitment h t)) t = _ from hstep, stAt_succ]
    rfl

/-! ## The final phase -/

theorem horner_eq_uni : ∀ (c : List EF) (x : EF), horner c x = uni c x
  | [], _ => by simp [horner, uni]
  | a :: c, x => by
    rw [horner, List.foldr_cons, ← horner, horner_eq_uni c x, uni, uni, List.length_cons, sum_range_succ', mul_sum]
    simp only [List.getD_cons_succ, List.getD_cons_zero, pow_zero, mul_one, pow_succ]
    rw [add_comm]
    congr 1
    exact sum_congr rfl fun b _ => by ring

/-- The honest round records carry a zero witness wherever the difficulty is zero. -/
theorem stAt_canonical {P0 : List F} {n : ℕ} {commitment : Com} (hv : Valid c n E.adicity)
    (h : List (Step F EF)) :
    ∀ t ≤ c.n_rounds, ∀ i r, (stAt E PE c P0 n commitment h t).rounds[i]? = some r →
      (queried c i).pow_bits = 0 → r.pow_witness = 0
  | 0, _, i, r, hr, _ => by simp [stAt, honestInit] at hr
  | t + 1, ht, i, r, hr, hz => by
    have hlen : ∀ t, (stAt E PE c P0 n commitment h t).rounds.length = t := by
      intro t
      induction t with
      | zero => simp [stAt, honestInit]
      | succ t ih =>
        obtain ⟨rec, hrec⟩ := honestRound_rounds E PE c P0 n (stAt E PE c P0 n commitment h t) t
        rw [stAt_succ, hrec, List.length_append, ih, List.length_singleton]
    rw [stAt_succ] at hr
    by_cases hi : i < t
    · have : (honestRound E PE c P0 n (stAt E PE c P0 n commitment h t) t).rounds[i]? =
          (stAt E PE c P0 n commitment h t).rounds[i]? := by
        obtain ⟨rec, hrec⟩ := honestRound_rounds E PE c P0 n (stAt E PE c P0 n commitment h t) t
        rw [hrec, List.getElem?_append_left (by rw [hlen]; exact hi)]
      exact stAt_canonical hv h t (by omega) i r (this ▸ hr) hz
    · have hit : i = t := by
        by_contra hne
        have := hlen (t + 1)
        rw [stAt_succ] at this
        rw [List.getElem?_eq_none (by omega)] at hr
        cases hr
      subst hit
      have hq : c.round_parameters.getD i default = queried c i := by
        simp [queried, show i < c.n_rounds by omega]
      simp only [honestRound, hq, List.getElem?_append_right (by rw [hlen]), hlen, Nat.sub_self,
        List.getElem?_cons_zero, Option.some.injEq] at hr
      rw [← hr]
      simp [hz]

/-! ## Completeness -/

/-- The final check on the honest final table passes.

Each queried value is the table's polynomial at its point. -/
theorem select_verify_honest (P : List EF) (nv : ℕ) (g : F) (idx : List ℕ) :
    SelectStatement.verify ⟨nv, idx.map (g ^ ·), idx.map fun i => uni P (algebraMap F EF (g ^ i))⟩ P = true := by
  simp only [SelectStatement.verify, List.all_eq_true]
  intro ve hve
  obtain ⟨i, -, rfl⟩ : ∃ i ∈ idx, ve = (g ^ i, uni P (algebraMap F EF (g ^ i))) := by
    rw [List.zip_map', List.mem_map] at hve
    obtain ⟨i, hi, rfl⟩ := hve
    exact ⟨i, hi, rfl⟩
  simp [horner_eq_uni]

/-- The extension of a table at r is the only entry of its fold at r. -/
theorem getD_foldTable_full (P r : List EF) {m : ℕ} (hm : r.length = m) :
    (foldTable P m r).getD 0 0 = mle P r := by
  subst hm
  have := mle_foldTable P r []
  simpa using this

/-- The fields of the honest proof. -/
theorem honestProof_eq {P0 : List F} {n : ℕ} {commitment : Com} {s : QuerySite} (hs : c.site c.n_rounds = some s)
    (h : List (Step F EF)) :
    let st := stAt E PE c P0 n commitment h c.n_rounds
    let h1 := st.h ++ [.message st.P]
    let qi := play_query_indices E.S (if s.pow_bits = 0 then h1 else h1 ++ [.pow s.pow_bits (PE.solve h1 s.pow_bits)])
      s.index_bits s.draws c.stratified_queries s.depths
    let HF := honestSumcheck E.S.toSponge PE.solve c.final_folding_pow_bits st.P st.Wt qi.2 c.final_sumcheck_rounds
    honestProof E PE c P0 n commitment h =
      ⟨(honestInit E PE c P0 n commitment h).2, st.rounds, some st.P,
        if s.pow_bits = 0 then 0 else PE.solve h1 s.pow_bits, openPrev E PE c P0 n st c.n_rounds qi.1,
        if 0 < c.final_sumcheck_rounds then some (HF.ms, HF.ws) else none⟩ := by
  simp only [honestProof, hs, Option.getD_some]
  rfl

/-- The replay accepts the honest proof. -/
theorem replay_complete {P0 : List F} {n : ℕ} {commitment : Com} (hv : Valid c n E.adicity)
    (hh : Honesty E PE c P0 n commitment) (h : List (Step F EF)) :
    ∃ out, replay E c (honestProof E PE c P0 n commitment h) commitment h = some (.ok out) := by
  obtain ⟨sN, hsN⟩ := Option.isSome_iff_exists.mp (hv.sites c.n_rounds le_rfl)
  obtain ⟨hloop, hinv⟩ := loop_honest E PE c hv hh h (honestProof E PE c P0 n commitment h) rfl c.n_rounds le_rfl
  have hpe := honestProof_eq E PE c (P0 := P0) (n := n) (commitment := commitment) hsN h
  generalize honestProof E PE c P0 n commitment h = proof at hloop hpe ⊢
  have hf0 : proof.initial_sumcheck = (honestInit E PE c P0 n commitment h).2 := by rw [hpe]
  have hf1 : proof.final_poly = some (stAt E PE c P0 n commitment h c.n_rounds).P := by rw [hpe]
  have hf2 := congrArg WhirProof.final_pow_witness hpe
  have hf3 := congrArg WhirProof.final_openings hpe
  have hf4 := congrArg WhirProof.final_sumcheck hpe
  simp only at hf2 hf3 hf4
  clear hpe
  have hk0 : c.round_folding_factor 0 = some (c.folding_schedule.getD 0 0) := by
    simp only [WhirConfig.round_folding_factor, List.getD_eq_getElem?_getD]
    rw [List.getElem?_eq_getElem (by have := hv.schedule; omega), Option.getD_some]
  set H0 := honestSumcheck E.S.toSponge PE.solve c.starting_folding_pow_bits (P0.map (algebraMap F EF))
    (cubeTable (weightAt (E.initial (E.S.sample (h ++ [E.layoutSeed])))) n) (h ++ [E.layoutSeed, .challenge])
    (c.folding_schedule.getD 0 0)
  have hv0 : view (stAt E PE c P0 n commitment h 0) = ⟨[E.initial (E.S.sample (h ++ [E.layoutSeed]))], [H0.rs],
      commitment, Plonky3Lean.Proofs.Sumcheck.replay .Evaluation
        ((E.initial (E.S.sample (h ++ [E.layoutSeed]))).combine_evals 0) H0.ms H0.rs, H0.h⟩ := rfl
  rw [hv0] at hloop
  simp only [replay, hk0, Option.bind_eq_bind, Option.bind_some, sumcheck, hf0, honestInit,
    show h ++ [E.layoutSeed] ++ [Step.challenge] = h ++ [E.layoutSeed, .challenge] by simp]
  rw [verify_rounds_honest E.S.toSponge PE.solve hh.solve]
  simp only [Except.mapError]
  simp only [H0] at hloop
  rw [hloop]
  set st := stAt E PE c P0 n commitment h c.n_rounds
  have hqN : queried c c.n_rounds = c.final_round_config := by simp [queried]
  have hnvN : nvAt c c.n_rounds = c.final_sumcheck_rounds := by rw [nvAt, hqN, hv.final.1]
  have hlenP : st.P.length = 2 ^ c.final_round_config.num_variables := by rw [hinv.lenP, nvAt, hqN]
  obtain ⟨r, hr, -, -⟩ := hinv.last
  simp only [Option.bind_some, view, hf1, hlenP, ne_eq, not_true_eq_false, ↓reduceIte, hr]
  rw [← hqN, hf2, hf3, stir_honest E PE c hv hh le_rfl hinv hr hsN]
  simp only [Option.bind_some, select_verify_honest, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  generalize (play_query_indices E.S (if sN.pow_bits = 0 then st.h ++ [Step.message st.P]
      else st.h ++ [Step.message st.P] ++ [Step.pow sN.pow_bits (PE.solve (st.h ++ [Step.message st.P]) sN.pow_bits)])
      sN.index_bits sN.draws c.stratified_queries sN.depths).2 = qh at hf4 ⊢
  -- The weight and the table at the closing challenges rf.
  have hfinal : ∀ rf : List EF, rf.length = nvAt c c.n_rounds →
      VariableOrder.Prefix.eval_constraints_poly st.cons (st.rand ++ [rf]).flatten = some (mle st.Wt rf) ∧
      p3_multilinear_util.split_eq.mirror.Poly.eval_ext E.thr E.w E.T st.P rf = some (mle st.P rf) := by
    intro rf hrf
    have hflat : (st.rand ++ [rf]).flatten = st.rand.flatten ++ rf := by simp
    refine ⟨?_, poly_eval_ext_eq _ _ _ _ _ (by rw [hrf, hnvN]; exact hv.final.2) (by rw [hinv.lenP, hrf])⟩
    rw [hflat, eval_constraints_poly_prefix _ _ fun con hcon => ?_, hinv.weight rf hrf]
    obtain ⟨hn, hs⟩ := hinv.cons con hcon
    refine ⟨by rw [List.length_append, hrf]; omega, fun s hs' => ⟨(hs s hs').1, ?_⟩⟩
    have hd := (hs s hs').2
    cases s with
    | Eq s => exact fun p hp => by rw [hd p hp, List.length_drop, List.length_append, hrf]; omega
    | Select s => trivial
  have hlenW : st.Wt.length = 2 ^ nvAt c c.n_rounds := hinv.lenW
  by_cases hR : 0 < c.final_sumcheck_rounds
  · set HF := honestSumcheck E.S.toSponge PE.solve c.final_folding_pow_bits st.P st.Wt qh c.final_sumcheck_rounds
    have hR0 : c.final_sumcheck_rounds ≠ 0 := by omega
    obtain ⟨hrs, -, -, hff, hfw, hrep⟩ := honestSumcheck_spec E.S.toSponge PE.solve c.final_folding_pow_bits st.P
      st.Wt qh hinv.lenP hlenW (k := c.final_sumcheck_rounds) (by rw [hnvN])
    obtain ⟨hw, hp⟩ := hfinal HF.rs (by rw [hrs, hnvN])
    have hclaim : Plonky3Lean.Proofs.Sumcheck.replay .Evaluation st.claim HF.ms HF.rs =
        mle st.Wt HF.rs * mle st.P HF.rs := by
      rw [hinv.claimSum, hrep, hnvN, Nat.sub_self, pow_zero, sum_range_one, hff, hfw,
        getD_foldTable_full _ _ (by rw [hrs, hnvN]), getD_foldTable_full _ _ (by rw [hrs, hnvN]), mul_comm]
    simp only [HF] at hw hp hclaim
    simp only [hR, ↓reduceIte, hf4, verify_final_sumcheck_rounds, hR0]
    rw [verify_rounds_honest E.S.toSponge PE.solve hh.solve]
    simp only [hw, hp, Option.bind_some, hclaim, not_true_eq_false, ↓reduceIte]
    exact ⟨_, rfl⟩
  · have hR0 : c.final_sumcheck_rounds = 0 := by omega
    obtain ⟨hw, hp⟩ := hfinal [] (by rw [hnvN, hR0]; rfl)
    have hclaim : st.claim = mle st.Wt [] * mle st.P [] := by
      rw [hinv.claimSum, hnvN, hR0, pow_zero, sum_range_one, mle_nil, mle_nil, mul_comm]
    simp only [hR, ↓reduceIte, hw, hp, Option.bind_some, pure, Except.pure, hclaim, not_true_eq_false]
    exact ⟨_, rfl⟩

/-- Completeness: the verifier accepts the honest proof.

It returns the concatenated folding challenges. -/
theorem verify_complete {P0 : List F} {n : ℕ} {commitment : Com} (hv : Valid c n E.adicity)
    (hh : Honesty E PE c P0 n commitment) (seed : Step F EF) (h : List (Step F EF)) :
    ∃ out, verify E c seed (honestProof E PE c P0 n commitment (h ++ [seed])) commitment h = some (.ok out) := by
  obtain ⟨sN, hsN⟩ := Option.isSome_iff_exists.mp (hv.sites c.n_rounds le_rfl)
  obtain ⟨hpowN, -⟩ := site_queried c hsN
  simp only [lt_irrefl, ↓reduceIte] at hpowN
  obtain ⟨-, hinv⟩ := loop_honest E PE c hv hh (h ++ [seed]) (honestProof E PE c P0 n commitment (h ++ [seed])) rfl
    c.n_rounds le_rfl
  have hp := honestProof_eq E PE c (P0 := P0) (n := n) (commitment := commitment) hsN (h ++ [seed])
  have hrounds : (honestProof E PE c P0 n commitment (h ++ [seed])).rounds.length = c.n_rounds := hinv.rounds
  have hfind : ((c.round_parameters.zip (honestProof E PE c P0 n commitment (h ++ [seed])).rounds).zipIdx).find?
      (fun e => e.1.1.pow_bits == 0 && e.1.2.pow_witness != 0) = none := by
    refine List.find?_eq_none.mpr fun e he => ?_
    obtain ⟨⟨p, r⟩, i⟩ := e
    rw [List.mk_mem_zipIdx_iff_getElem?, List.getElem?_zip_eq_some] at he
    obtain ⟨hp', hr⟩ := he
    have hi : i < c.n_rounds := (List.getElem?_eq_some_iff.mp hp').1
    rw [queried_lt c hi, Option.some.injEq] at hp'
    subst hp'
    by_cases hz : (queried c i).pow_bits = 0
    · simp [hz, stAt_canonical E PE c hv (h ++ [seed]) c.n_rounds le_rfl i r hr hz]
    · simp [hz]
  have hfinpow : ¬ (c.final_round_config.pow_bits = 0 ∧
      (honestProof E PE c P0 n commitment (h ++ [seed])).final_pow_witness ≠ 0) := by
    rintro ⟨hz, hne⟩
    apply hne
    rw [hp]
    simp only
    rw [hpowN, ← hv.final_pow, hz]
    rfl
  have hfinsc : ¬ (c.final_sumcheck_rounds = 0 ∧
      (honestProof E PE c P0 n commitment (h ++ [seed])).final_sumcheck.isSome) := by
    rintro ⟨hz, hs⟩
    rw [hp] at hs
    simp [hz] at hs
  simp only [verify, hrounds, ne_eq, not_true_eq_false, ↓reduceIte, hfind, hfinpow, hfinsc]
  exact replay_complete E PE c hv hh (h ++ [seed])

end Plonky3Lean.Proofs.Whir
