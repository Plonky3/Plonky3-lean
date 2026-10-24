module

public import Plonky3Lean.Proofs.Bus.Gkr
public import Plonky3Lean.Proofs.Sumcheck.GenericDegree

@[expose] public section

/-!
# The product-tree verifier never panics

The verifier checks every proof length against the statement before it replays the transcript.

Take a statement its constructor accepts and a field with six distinct interpolation nodes.

The verifier then returns an answer for every proof: the output, or an error.

The layers are checked in kind and length.

Each layer's sumcheck has exactly as many rounds as the point it inherits has coordinates.
-/

namespace Plonky3Lean.Proofs.Bus

open p3_bus.product.mirror p3_sumcheck.generic_degree.mirror p3_multilinear_util.point.mirror

set_option linter.unusedSectionVars false

variable {F S : Type _} [Field F] [DecidableEq F]

theorem forM_ok_iff {α ε : Type _} (l : List α) (c : α → Bool) (e : α → ε) :
    l.forM (fun x => if c x then (throw (e x) : Except ε Unit) else pure ()) = .ok () ↔
      ∀ x ∈ l, c x = false := by
  induction l with
  | nil => simp [List.forM_nil, pure, Except.pure]
  | cons x l ih =>
    unfold List.forM
    cases hc : c x
    · simp only [Bool.false_eq_true, ite_false]
      change (l.forM _ = _) ↔ _
      rw [ih]; simp [hc]
    · simp only [ite_true]
      change ((Except.error (e x) : Except ε Unit) = Except.ok ()) ↔ _
      simp [hc]

/-- What an accepted shape check gives: the root count, the layer count, and each layer's kind and lengths. -/
theorem validate_shape_ok {p : ProductGkrProof F} {shape : ProductGkrShape}
    (h : p.validate_shape shape = .ok ()) :
    p.roots.length = shape.root_message_len ∧ p.layers.length = shape.layers.length ∧
      ∀ j (hj : j < shape.layers.length), ∃ hj' : j < p.layers.length,
        match shape.layers[j], p.layers[j] with
        | (2, _), .Binary children => children.length = shape.num_trees
        | (4, rounds), .RadixFour round_polys children =>
          round_polys.length = rounds ∧ children.length = shape.num_trees
        | _, _ => False := by
  unfold ProductGkrProof.validate_shape at h
  by_cases h1 : p.roots.length = shape.root_message_len
  swap
  · simp [h1, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at h
  by_cases h2 : p.layers.length = shape.layers.length
  swap
  · simp [h1, h2, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at h
  simp only [h1, h2, ne_eq, not_true_eq_false, ite_false, pure, Except.pure, bind,
    Except.bind] at h
  refine ⟨h1, h2, fun j hj => ⟨by omega, ?_⟩⟩
  have hall := (forM_ok_iff _ _ _).1 h j (List.mem_range.2 hj)
  rw [List.getElem?_eq_getElem hj, List.getElem?_eq_getElem (by omega)] at hall
  revert hall
  rcases shape.layers[j] with ⟨a, r⟩
  rcases p.layers[j] with c | ⟨rp, c⟩ <;>
    rcases a with _ | _ | _ | _ | _ | a <;> simp

/-- A validated layer of arity four is a radix-four proof with one round polynomial per round. -/
theorem kind_radix {p : ProductGkrProof F} {shape : ProductGkrShape} {j r : ℕ}
    (hj : j < shape.layers.length) (hj' : j < p.layers.length)
    (hm : match shape.layers[j], p.layers[j] with
        | (2, _), .Binary children => children.length = shape.num_trees
        | (4, rounds), .RadixFour round_polys children =>
          round_polys.length = rounds ∧ children.length = shape.num_trees
        | _, _ => False)
    (e : shape.layers[j] = (4, r)) : ∃ rp c, p.layers[j] = .RadixFour rp c ∧ rp.length = r := by
  rw [e] at hm
  revert hm
  cases p.layers[j] with
  | Binary c => simp
  | RadixFour rp c => intro hm; exact ⟨rp, c, rfl, hm.1⟩

/-- A validated layer of arity two is a binary proof. -/
theorem kind_binary {p : ProductGkrProof F} {shape : ProductGkrShape} {j r : ℕ}
    (hj : j < shape.layers.length) (hj' : j < p.layers.length)
    (hm : match shape.layers[j], p.layers[j] with
        | (2, _), .Binary children => children.length = shape.num_trees
        | (4, rounds), .RadixFour round_polys children =>
          round_polys.length = rounds ∧ children.length = shape.num_trees
        | _, _ => False)
    (e : shape.layers[j] = (2, r)) : ∃ c, p.layers[j] = .Binary c := by
  rw [e] at hm
  revert hm
  cases p.layers[j] with
  | Binary c => intro; exact ⟨c, rfl⟩
  | RadixFour rp c => simp

section Layer

variable (node : ℕ → F) (T : VerifierTranscript F S) {weights : Fin 6 → F}
  (hw : RoundPolyInterpolator.new node 5 = some weights)
include hw

/-- The round loop of a layer never panics, and collects one challenge per round polynomial. -/
theorem rounds_some : ∀ (rp : List (Fin 5 → F)) (acc : F × List F × S),
    ∃ out : F × List F × S, rp.foldlM (fun (acc : F × List F × S) round_poly => do
      let (challenge, t) := T.round acc.2.2 (List.ofFn round_poly)
      let running_sum ← RoundPolyInterpolator.eval node 5 weights (List.ofFn round_poly) acc.1
        challenge
      pure (running_sum, acc.2.1 ++ [challenge], t)) acc = some out ∧
      out.2.1.length = acc.2.1.length + rp.length
  | [], acc => ⟨acc, by simp⟩
  | q :: rp, acc => by
    obtain ⟨out, h, hl⟩ := rounds_some rp ((RoundPolyInterpolator.eval node 5 weights (List.ofFn q)
      acc.1 (T.round acc.2.2 (List.ofFn q)).1).get (by
        rw [Plonky3Lean.Proofs.Sumcheck.RoundPolyInterpolator.eval_eq node (by norm_num) hw]; rfl),
      acc.2.1 ++ [(T.round acc.2.2 (List.ofFn q)).1], (T.round acc.2.2 (List.ofFn q)).2)
    refine ⟨out, ?_, by rw [hl]; simp; omega⟩
    rw [List.foldlM_cons]
    simp only [Plonky3Lean.Proofs.Sumcheck.RoundPolyInterpolator.eval_eq node (by norm_num : 0 < 5) hw] at h ⊢
    exact h

/-- A radix-four layer whose rounds match the inherited point never panics.

It leaves a point two coordinates longer. -/
theorem verify_layer_radix_some (st : VerifyState F S) (li : ℕ) (rp : List (Fin 5 → F))
    (c : List (F × F × F × F)) (hlen : rp.length = st.point.length) :
    ∃ st', verify_layer node T weights st li (.RadixFour rp c) = some st' ∧
      st'.point.length = st.point.length + 2 := by
  obtain ⟨out, h, hl⟩ := rounds_some node T hw rp
    (combine st.values (T.begin_layer st.transcript).1, [], (T.begin_layer st.transcript).2)
  simp only [List.length_nil, zero_add] at hl
  unfold verify_layer
  simp only [Option.bind_eq_bind] at h ⊢
  rw [h, Option.bind_some]
  simp only [Point.eval_eq, hl, hlen, ne_eq, not_true_eq_false, ite_false, Option.bind_some]
  refine ⟨_, rfl, ?_⟩
  simp [hl, hlen]

/-- A binary layer never panics, and leaves a one-coordinate point. -/
theorem verify_layer_binary_some (st : VerifyState F S) (li : ℕ) (c : List (F × F)) :
    ∃ st', verify_layer node T weights st li (.Binary c) = some st' ∧ st'.point.length = 1 := by
  unfold verify_layer
  exact ⟨_, rfl, rfl⟩

/-- The radix-four layers of a schedule never panic, given matching round counts. -/
theorem fold_radix_some : ∀ (k start : ℕ) (P : List (ProductGkrLayerProof F)) (hP : P.length = k),
    (∀ j (hj : j < k), ∃ rp c, P[j]'(by omega) = .RadixFour rp c ∧ rp.length = start + 2 * j) →
    ∀ (st : VerifyState F S), st.point.length = start → ∀ idx : ℕ,
    ∃ st', ((((List.range k).map fun j => (4, start + 2 * j)).zip P).zipIdx idx).foldlM
      (fun st (lp : ((ℕ × ℕ) × ProductGkrLayerProof F) × ℕ) =>
        verify_layer node T weights st lp.2 lp.1.2) st = some st'
  | 0, _, P, _, _, st, _, _ => ⟨st, by simp⟩
  | k + 1, start, q :: P, hP, hv, st, hst, idx => by
    obtain ⟨rp, c, hq, hrp⟩ := hv 0 (by omega)
    simp only [List.getElem_cons_zero, mul_zero, add_zero] at hq hrp
    subst hq
    obtain ⟨st', h1, h2⟩ := verify_layer_radix_some node T hw st idx rp c (hrp.trans hst.symm)
    obtain ⟨st'', h⟩ := fold_radix_some k (start + 2) P (by simpa using hP)
      (fun j hj => by
        obtain ⟨rp', c', h', hl'⟩ := hv (j + 1) (by omega)
        exact ⟨rp', c', by simpa using h', by rw [hl']; ring⟩) st' (by omega) (idx + 1)
    refine ⟨st'', ?_⟩
    rw [List.range_succ_eq_map, List.map_cons, List.map_map]
    simp only [List.zip_cons_cons, List.zipIdx_cons, List.foldlM_cons, h1, Option.bind_eq_bind,
      Option.bind_some, mul_zero, add_zero]
    convert h using 4
    simp [Function.comp_def]; intros; ring

end Layer

/-- **The verifier never panics.**

Take a statement its constructor accepts and a field with six distinct interpolation nodes.

The verifier returns the output or an error for every proof. -/
theorem verify_isSome (node : ℕ → F) (T : VerifierTranscript F S) (bits : ℕ)
    (p : ProductGkrProof F) {shape : ProductGkrShape}
    (hshape : shape.root_shape = .FirstTwoShared → 2 ≤ shape.num_trees)
    (hnodes : has_distinct_round_nodes bits node = true) :
    (p.verify node T bits shape).isSome := by
  -- Six distinct nodes build the interpolator.
  have hinj : Function.Injective fun i : Fin (5 + 1) => node i := by
    intro i j hij
    unfold has_distinct_round_nodes at hnodes
    split at hnodes
    · cases hnodes
    simp only [List.all_eq_true, List.mem_range, Bool.or_eq_true, decide_eq_true_eq,
      bne_iff_ne, ne_eq] at hnodes
    by_contra hne
    rcases Nat.lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with h | h
    · exact (hnodes i i.2 j j.2).resolve_left (by omega) hij
    · exact (hnodes j j.2 i i.2).resolve_left (by omega) hij.symm
  obtain ⟨w, hw⟩ : ∃ w, RoundPolyInterpolator.new node 5 = some w := by
    rw [RoundPolyInterpolator.new, Plonky3Lean.Proofs.Matrix.Interp.barycentric_weights_eq,
      ite_eq_left hinj]
    exact ⟨_, rfl⟩
  unfold ProductGkrProof.verify
  simp only [hnodes, Bool.not_true, Bool.false_eq_true, ite_false]
  cases hv : p.validate_shape shape with
  | error e => simp
  | ok u =>
    obtain ⟨hroots, hlen, hlayers⟩ := validate_shape_ok hv
    obtain ⟨roots, hr⟩ : ∃ r, shape.root_shape.decode p.roots = some r := by
      unfold ProductGkrRootShape.decode
      cases hs : shape.root_shape
      · exact ⟨_, rfl⟩
      · have := hshape hs
        have hl : p.roots.length = shape.num_trees - 1 := by
          rw [hroots, ProductGkrShape.root_message_len, hs]
        obtain ⟨e0, rest, he⟩ : ∃ e0 rest, p.roots = e0 :: rest :=
          List.exists_cons_of_length_pos (by omega)
        exact ⟨e0 :: e0 :: rest, by simp [he]⟩
    obtain ⟨st, hst⟩ : ∃ st', ((shape.layers.zip p.layers).zipIdx).foldlM
        (fun st (lp : ((ℕ × ℕ) × ProductGkrLayerProof F) × ℕ) =>
          verify_layer node T w st lp.2 lp.1.2) ⟨roots, [], none, T.init p.roots⟩ = some st' := by
      have hL := layers_eq shape
      split at hL
      · have hk : p.layers.length = shape.log_height / 2 := by rw [hlen, hL]; simp
        have := fold_radix_some node T hw (shape.log_height / 2) 0 p.layers hk
          (fun j hj => by
            obtain ⟨hj', hm⟩ := hlayers j (by rw [hL]; simpa using hj)
            exact kind_radix _ hj' hm (by simp [hL]))
          ⟨roots, [], none, T.init p.roots⟩ rfl 0
        simpa [hL] using this
      · obtain ⟨q, P, hqP⟩ : ∃ q P, p.layers = q :: P :=
          List.exists_cons_of_length_pos (by rw [hlen, hL]; simp)
        obtain ⟨hj0, hm0⟩ := hlayers 0 (by rw [hL]; simp)
        obtain ⟨c, hc⟩ := kind_binary _ hj0 hm0 (r := 0) (by simp [hL])
        simp only [hqP, List.getElem_cons_zero] at hc
        subst hc
        obtain ⟨st1, h1, h1l⟩ := verify_layer_binary_some node T hw
          ⟨roots, [], none, T.init p.roots⟩ 0 c
        have hk : P.length = shape.log_height / 2 := by
          have := hlen; rw [hqP, hL] at this; simpa using this
        have := fold_radix_some node T hw (shape.log_height / 2) 1 P hk
          (fun j hj => by
            obtain ⟨hj', hm⟩ := hlayers (j + 1) (by rw [hL]; simpa using hj)
            obtain ⟨rp, c', h', hl'⟩ := kind_radix _ hj' hm (r := 1 + 2 * j) (by simp [hL])
            exact ⟨rp, c', by simpa [hqP] using h', hl'⟩)
          st1 h1l 1
        obtain ⟨st', h'⟩ := this
        refine ⟨st', ?_⟩
        rw [hL, hqP]
        simp only [List.zip_cons_cons, List.zipIdx_cons, List.foldlM_cons, Option.bind_eq_bind]
        rw [h1, Option.bind_some]
        exact h'
    cases u
    simp only [hr, hw, Option.bind_eq_bind, Option.bind_some, hst]
    split <;> rfl

end Plonky3Lean.Proofs.Bus
