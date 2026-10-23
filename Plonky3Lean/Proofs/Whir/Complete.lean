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

/-- The verifier's out-of-domain loop on the honest answers draws the prover's points and ends at its history. -/
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

/-- The verifier's folds of honest rows: each is the folded table's polynomial at the row's domain point. -/
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

/-- With honest claims, a constraint's claim is the sum of the table against the constraint's weight table. -/
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

/-- The configuration is consistent, as the Rust derivation makes it, and every folded domain fits the two-adicity. -/
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
  claim : st.σ = ∑ b ∈ range (2 ^ nvAt c t), st.P.getD b 0 * st.Wt.getD b 0
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

/-- The honest sumcheck on two tables of 2^nv entries, k <= nv rounds: lengths, folds and the replayed claim. -/
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

/-- The weight table after a sumcheck on it: its extension at y is the extension before, at the challenges then y. -/
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

/-- The STIR phase on the honest openings: the selector statement of the folded table at the queried points. -/
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

end Plonky3Lean.Proofs.Whir
