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
    (idx.map (row P nv r.length ω)).mapM (fun a => do
      let p ← p3_multilinear_util.poly.mirror.Poly.new a
      p3_multilinear_util.split_eq.mirror.Poly.eval_ext thr w T p r) =
      some (idx.map fun i => uni (foldTable P nv r) (ω ^ i)) := by
  induction idx with
  | nil => rfl
  | cons i idx ih =>
    simp only [Option.bind_eq_bind] at ih
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

end Plonky3Lean.Proofs.Whir
