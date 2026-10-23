module

public import Plonky3Lean.Proofs.Sumcheck.Verifier
public import Plonky3Lean.Proofs.Matrix.Interpolation

@[expose] public section

/-!
# The generic-degree round: d values on the wire

A round of degree d sends h(x_0), h(x_2), ..., h(x_d), where x_i is the interpolation node i.

The verifier rebuilds h(x_1) = c - h(x_0) from the running claim c, and interpolates h through the d + 1 nodes.

With x_0 = 0, x_1 = 1 and distinct nodes, every polynomial of degree at most d with h(0) + h(1) = c has exactly one message, so this is the verifier of Section 4.1.
-/

namespace Plonky3Lean.Proofs.Sumcheck

open Polynomial Finset Lagrange p3_sumcheck p3_sumcheck.mirror p3_sumcheck.generic_degree.mirror
  p3_matrix.interpolation.mirror

variable {F EF : Type _} [Field EF] [DecidableEq EF]

/-- The values at the d + 1 nodes: the first value sent, the claim minus it, then the rest. -/
def fullValues (c : EF) : List EF → List EF
  | [] => []
  | e0 :: rest => e0 :: (c - e0) :: rest

/-- The polynomial the values sent stand for under the claim c: the interpolant through the nodes. -/
noncomputable def decGen (node : ℕ → EF) (d : ℕ) (c : EF) (m : Fin d → EF) : EF[X] :=
  interpolate univ (fun i : Fin (d + 1) => node i) fun i => (fullValues c (List.ofFn m)).getD i 0

/-- RoundPolyInterpolator::eval is the interpolant through the nodes, evaluated at r, when the weights are those of the nodes. -/
theorem RoundPolyInterpolator.eval_eq (node : ℕ → EF) {d : ℕ} (hd : 0 < d)
    {wt : Fin (d + 1) → EF} (hwt : RoundPolyInterpolator.new node d = some wt) (m : Fin d → EF)
    (c r : EF) :
    RoundPolyInterpolator.eval node d wt (List.ofFn m) c r = some ((decGen node d c m).eval r) := by
  have hinj : Function.Injective fun i : Fin (d + 1) => node i := by
    by_contra h
    simp [RoundPolyInterpolator.new, Proofs.Matrix.Interp.barycentric_weights_eq, h] at hwt
  have key := Proofs.Matrix.Interp.interpolate_arbitrary_point_eq
    (fun i (_ : Fin 1) => (fullValues c (List.ofFn m)).getD i 0) (fun i : Fin (d + 1) => node i) r
  simp only [hinj, ite_true, interpolate_arbitrary_point, RoundPolyInterpolator.new] at key hwt
  rw [hwt, Option.bind_some] at key
  obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
  simp only [RoundPolyInterpolator.eval, List.length_cons, List.length_ofFn, ne_eq, not_true_eq_false,
    ↓reduceIte, List.ofFn_succ, fullValues, sub_eq_zero] at key ⊢
  split at key <;> rename_i hfind
  · rw [hfind]; simpa [decGen, List.ofFn_succ, fullValues] using congrFun (Option.some.inj key) 0
  · rw [hfind]
    simpa [decGen, List.ofFn_succ, fullValues] using congrArg (Option.map (· 0)) key

section Nodes

omit [DecidableEq EF]

variable (node : ℕ → EF) {d : ℕ} (hinj : Function.Injective fun i : Fin (d + 1) => node i)
include hinj

theorem natDegree_decGen (c : EF) (m : Fin d → EF) : (decGen node d c m).natDegree ≤ d := by
  have := degree_interpolate_lt (s := univ) (fun i : Fin (d + 1) => (fullValues c (List.ofFn m)).getD i 0)
    hinj.injOn
  rw [card_univ, Fintype.card_fin] at this
  exact natDegree_le_iff_degree_le.mpr (Order.le_of_lt_succ (by exact_mod_cast this))

/-- The value of the interpolant at node i is entry i of the values. -/
theorem eval_decGen_node (c : EF) (m : Fin d → EF) (i : Fin (d + 1)) :
    (decGen node d c m).eval (node i) = (fullValues c (List.ofFn m)).getD i 0 :=
  eval_interpolate_at_node _ hinj.injOn (mem_univ i)

theorem decGen_sum (hd : 0 < d) (h0 : node 0 = 0) (h1 : node 1 = 1) (c : EF) (m : Fin d → EF) :
    (decGen node d c m).eval 0 + (decGen node d c m).eval 1 = c := by
  obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
  have e0 := eval_decGen_node node hinj c m 0
  have e1 := eval_decGen_node node hinj c m 1
  simp only [Fin.val_zero, Fin.val_one, h0, h1, List.ofFn_succ, fullValues] at e0 e1
  simp [e0, e1]

/-- The message of a polynomial: its values at the nodes 0, 2, ..., d. -/
def encGen (p : EF[X]) (k : Fin d) : EF := p.eval (node (if k.val = 0 then 0 else k.val + 1))

theorem decGen_encGen (hd : 0 < d) (h0 : node 0 = 0) (h1 : node 1 = 1) {c : EF} {p : EF[X]}
    (hp : p.natDegree ≤ d) (hc : p.eval 0 + p.eval 1 = c) : decGen node d c (encGen node p) = p := by
  refine (eq_interpolate_of_eval_eq _ hinj.injOn ?_ fun i _ => ?_).symm
  · rw [card_univ, Fintype.card_fin]
    exact (degree_le_of_natDegree_le hp).trans_lt (WithBot.coe_lt_coe.mpr d.lt_succ_self)
  · rcases d with _ | d'
    · exact absurd hd (lt_irrefl 0)
    obtain ⟨_ | _ | k, hi⟩ := i
    · simp [List.ofFn_succ, fullValues, encGen, h0]
    · simp [List.ofFn_succ, fullValues, encGen, h0, h1, ← hc]
    · simp [List.ofFn_succ, fullValues, encGen, List.getD_eq_getElem?_getD, show k < d' by omega]

end Nodes

/-! ## The verifier -/

/-- The steps of round i up to its challenge: the values, then the witness when grinding. -/
def genSteps (polys : List (List EF)) (wits : List F) (pow_bits i : ℕ) : List (Step F EF) :=
  .message (polys.getD i []) :: if 0 < pow_bits then (wits[i]?.map (Step.pow pow_bits)).toList else []

/-- The history at the start of round i. -/
def genBefore (h : List (Step F EF)) (polys : List (List EF)) (wits : List F) (pow_bits : ℕ) :
    ℕ → List (Step F EF)
  | 0 => h
  | i + 1 => genBefore h polys wits pow_bits i ++ genSteps polys wits pow_bits i ++ [.challenge]

/-- The rejection round i raises, if any: a wrong count of values first, then a failing witness. -/
def genErr (S : Sponge F EF) (h : List (Step F EF)) (polys : List (List EF)) (wits : List F)
    (d pow_bits i : ℕ) : Option GenericDegreeError :=
  if (polys.getD i []).length ≠ d then some (.PolyEvalCountMismatch i d (polys.getD i []).length)
  else if 0 < pow_bits then
    match wits[i]? with
    | some w => if S.grind (genBefore h polys wits pow_bits i ++ [.message (polys.getD i [])]) pow_bits w
        then none else some (.InvalidPowWitness i)
    | none => some (.MissingPowWitness i)
  else none

/-- The challenge of round i. -/
def genChallengeAt (S : Sponge F EF) (h : List (Step F EF)) (polys : List (List EF)) (wits : List F)
    (pow_bits i : ℕ) : EF :=
  S.sample (genBefore h polys wits pow_bits i ++ genSteps polys wits pow_bits i)

/-- The values of a round as a message of length d. -/
def toMsg (d : ℕ) (l : List EF) (k : Fin d) : EF := l.getD k 0

omit [DecidableEq EF] in
theorem ofFn_toMsg {d : ℕ} {l : List EF} (hl : l.length = d) : List.ofFn (toMsg d l) = l :=
  List.ext_getElem (by simp [hl]) fun i _ h2 => by
    simp [toMsg, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2]

theorem foldlM_genRound (S : Sponge F EF) (node : ℕ → EF) {d : ℕ} (hd : 0 < d) (pow_bits : ℕ)
    {wt : Fin (d + 1) → EF} (hwt : RoundPolyInterpolator.new node d = some wt) (polys : List (List EF))
    (wits : List F) (h : List (Step F EF)) (c : EF) {N : ℕ} (hp : polys.length = N)
    (hw : wits.length = if 0 < pow_bits then N else 0) :
    ∀ k ≤ N, (List.range k).foldlM (p3_sumcheck.generic_degree.mirror.verifyRound S node d pow_bits wt polys wits) (.ok ([], c, h)) =
      some (match (List.range k).findSome? (genErr S h polys wits d pow_bits) with
      | some e => .error e
      | none =>
        let rs := (List.range k).map (genChallengeAt S h polys wits pow_bits)
        .ok (rs, finalClaim (decGen node d) c ((polys.map (toMsg d)).take k) rs,
          genBefore h polys wits pow_bits k))
  | 0, _ => rfl
  | k + 1, hk => by
    rw [List.range_succ, List.foldlM_append, foldlM_genRound S node hd pow_bits hwt polys wits h c hp hw k
      (by omega), List.findSome?_append]
    rcases hf : (List.range k).findSome? (genErr S h polys wits d pow_bits) with _ | e
    swap
    · simp [p3_sumcheck.generic_degree.mirror.verifyRound]
    have hkN : k < polys.length := by omega
    obtain ⟨l, hl⟩ : ∃ l, polys[k]? = some l := ⟨_, List.getElem?_eq_getElem hkN⟩
    have hgd : polys.getD k [] = l := by simp [List.getD_eq_getElem?_getD, hl]
    have hrs : ((List.range k).map (genChallengeAt S h polys wits pow_bits)).length =
        ((polys.map (toMsg d)).take k).length := by simp; omega
    have htake : (polys.map (toMsg d)).take (k + 1) = (polys.map (toMsg d)).take k ++ [toMsg d l] := by
      rw [List.take_add_one, List.getElem?_map, hl]; rfl
    simp only [Option.none_or, List.findSome?_singleton, List.foldlM_cons, List.foldlM_nil,
      Option.bind_eq_bind]
    by_cases hlen : l.length = d
    swap
    · simp [generic_degree.mirror.verifyRound,
        generic_degree.mirror.VerifierTranscript.round, genErr, hl, hlen, bind, Except.bind, throw, throwThe, MonadExceptOf.throw]
    have hev := RoundPolyInterpolator.eval_eq node hd hwt (toMsg d l)
    rw [ofFn_toMsg hlen] at hev
    by_cases hpb : 0 < pow_bits
    · obtain ⟨w, hw'⟩ : ∃ w, wits[k]? = some w :=
        ⟨_, List.getElem?_eq_getElem (by simp [hpb] at hw; omega)⟩
      by_cases hg : S.grind (genBefore h polys wits pow_bits k ++ [.message l]) pow_bits w
      · simp [generic_degree.mirror.verifyRound,
        generic_degree.mirror.VerifierTranscript.round, genErr, hl, hlen, hpb, hw', hg, bind, Except.bind, pure,
          Except.pure, hev, htake, genChallengeAt, genBefore, genSteps]
        rw [finalClaim_snoc _ _ _ _ hrs.symm]
      · simp [generic_degree.mirror.verifyRound,
        generic_degree.mirror.VerifierTranscript.round, genErr, hl, hlen, hpb, hw', hg, bind, Except.bind,
          throw, throwThe, MonadExceptOf.throw]
    · simp [generic_degree.mirror.verifyRound,
        generic_degree.mirror.VerifierTranscript.round, genErr, hl, hlen, hpb, bind, Except.bind, pure,
        Except.pure, hev, htake, genChallengeAt, genBefore, genSteps]
      rw [finalClaim_snoc _ _ _ _ hrs.symm]

/-- GenericDegreeProof::verify: the configuration checks, a panic on equal nodes, then the first rejected round, else the challenges and the replayed claim.

The claimed sum is absorbed right after the seed, before the first challenge. -/
theorem verify_eq (S : Sponge F EF) (node : ℕ → EF) (c : EF) (polys : List (List EF)) (wits : List F)
    (h : List (Step F EF)) (N d pow_bits : ℕ) :
    verify S node c polys wits h N d pow_bits =
      if d = 0 then some (.error (.InvalidDegree d))
      else if polys.length ≠ N then some (.error (.RoundCountMismatch N polys.length))
      else if wits.length ≠ (if 0 < pow_bits then N else 0) then
        some (.error (.PowWitnessCountMismatch (if 0 < pow_bits then N else 0) wits.length))
      else if ¬ Function.Injective (fun i : Fin (d + 1) => node i) then none
      else
        let h' := h ++ [GenericDegreeShape.seed N d pow_bits, .message [c]]
        some (match (List.range N).findSome? (genErr S h' polys wits d pow_bits) with
        | some e => .error e
        | none =>
          let rs := (List.range N).map (genChallengeAt S h' polys wits pow_bits)
          .ok (rs, finalClaim (decGen node d) c (polys.map (toMsg d)) rs,
            genBefore h' polys wits pow_bits N)) := by
  unfold verify
  by_cases hd : d = 0
  · simp [hd]
  by_cases hp : polys.length = N
  swap
  · simp [hd, hp]
  by_cases hw : wits.length = if 0 < pow_bits then N else 0
  swap
  · simp only [hd, hp, hw, ne_eq, not_true_eq_false, not_false_eq_true, ↓reduceIte]
  have hnew := Proofs.Matrix.Interp.barycentric_weights_eq (fun i : Fin (d + 1) => node i)
  by_cases hinj : Function.Injective fun i : Fin (d + 1) => node i
  · simp only [hd, hp, hw, hinj, ne_eq, not_true_eq_false, ↓reduceIte] at hnew ⊢
    rw [RoundPolyInterpolator.new, hnew, Option.bind_some, foldlM_genRound S node (Nat.pos_of_ne_zero hd)
      pow_bits (by rw [RoundPolyInterpolator.new, hnew]) polys wits _ c hp hw N le_rfl, ← hp,
      List.take_of_length_le (by simp)]
  · simp only [hd, hp, hw, hinj, ne_eq, not_true_eq_false, not_false_eq_true, ↓reduceIte] at hnew ⊢
    rw [RoundPolyInterpolator.new, hnew, Option.bind_none]

end Plonky3Lean.Proofs.Sumcheck
