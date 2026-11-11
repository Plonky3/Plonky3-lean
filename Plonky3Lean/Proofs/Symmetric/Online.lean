module

public import Plonky3Lean.Spec.Sponge
public import Mathlib.Data.Nat.Init

@[expose] public section

/-!
# The sponges, one item at a time

The code absorbs one item per loop iteration and keeps the rate position in a counter.

This file proves that running it item by item gives the block-wise specification.
-/

namespace Plonky3Lean.Proofs.Symmetric

open Plonky3Lean.Spec.Sponge

variable {T : Type}

/-- One iteration of the padding-free loop: write the item, and permute when the block is full. -/
def pfStep (f : List T → List T) (r : ℕ) (p : List T × ℕ) (x : T) : List T × ℕ :=
  if p.2 + 1 = r then (f (p.1.set p.2 x), 0) else (p.1.set p.2 x, p.2 + 1)

/-- After the loop: a partial block is permuted, a finished one is not. -/
def pfFinish (f : List T → List T) (p : List T × ℕ) : List T :=
  if p.2 ≠ 0 then f p.1 else p.1

theorem set_eq {l : List T} {i : ℕ} {a : T} (h : i < l.length) :
    l.set i a = l.take i ++ a :: l.drop (i + 1) := by
  rw [List.set_eq_take_append_cons_drop, ite_eq_left_of_eq_true _ _ (eq_true h)]

theorem blocks_nil (r : ℕ) : blocks r ([] : List T) = [] := by
  rw [blocks]

theorem blocks_cons (r : ℕ) (l : List T) (hr : 0 < r) (hl : l ≠ []) :
    blocks r l = l.take r :: blocks r (l.drop r) := by
  obtain ⟨x, xs, rfl⟩ := List.exists_cons_of_ne_nil hl
  rw [blocks, ite_eq_right_of_eq_false _ _ (eq_false (by omega)), show max r 1 = r by omega]

theorem blocks_of_lt (r : ℕ) (l : List T) (hr : l.length ≤ r) (hl : l ≠ []) :
    blocks r l = [l] := by
  have hr0 : 0 < r := by
    have : l.length ≠ 0 := by simpa using hl
    omega
  rw [blocks_cons r l hr0 hl, List.take_of_length_le hr, List.drop_of_length_le hr, blocks_nil]

theorem flatten_blocks (r : ℕ) (hr : 0 < r) :
    ∀ l : List T, (blocks r l).flatten = l := by
  intro l
  induction h : l.length using Nat.strong_induction_on generalizing l with
  | _ n ih =>
    rcases l with _ | ⟨x, xs⟩
    · simp [blocks_nil]
    · rw [blocks_cons r _ hr (by simp), List.flatten_cons,
        ih _ (by simp [← h]; omega) _ rfl, List.take_append_drop]

/-- Writing items one at a time from position `i`, short of the end of the block. -/
theorem foldl_pfStep_lt (f : List T → List T) (r : ℕ) :
    ∀ (b s : List T) (i : ℕ), i + b.length < r → i + b.length ≤ s.length →
      b.foldl (pfStep f r) (s, i) = (s.take i ++ b ++ s.drop (i + b.length), i + b.length) := by
  intro b
  induction b with
  | nil => intro s i _ _; simp
  | cons x b ih =>
    intro s i h1 h2
    simp only [List.length_cons] at h1 h2
    rw [List.foldl_cons, pfStep, ite_eq_right_of_eq_false _ _ (eq_false (by omega))]
    dsimp only
    rw [ih _ _ (by omega) (by simp; omega)]
    refine Prod.ext ?_ (by simp; omega)
    apply List.ext_getElem (by simp; omega)
    intro n h3 h4
    simp only [List.getElem_append, List.getElem_take, List.getElem_drop, List.getElem_set,
      List.getElem_cons, List.length_take, List.length_append, List.length_cons, List.length_set]
    split_ifs <;> first | rfl | omega | (congr 1; omega)

/-- A whole block, written from position zero, ends in one permutation. -/
theorem foldl_pfStep_full (f : List T → List T) (r : ℕ) (b s : List T) (hb : b.length = r)
    (hs : r ≤ s.length) (hr : 0 < r) :
    b.foldl (pfStep f r) (s, 0) = (absorb f s b, 0) := by
  obtain ⟨b', x, rfl⟩ : ∃ b' x, b = b' ++ [x] := by
    rcases b.eq_nil_or_concat' with rfl | h
    · simp at hb; omega
    · exact h
  simp only [List.length_append, List.length_singleton] at hb
  rw [List.foldl_append, foldl_pfStep_lt f r b' s 0 (by omega) (by omega)]
  simp only [List.foldl_cons, List.foldl_nil, pfStep, Nat.zero_add, ite_eq_left_of_eq_true _ _ (eq_true (show b'.length + 1 = r by omega))]
  congr 1
  rw [absorb, overwrite]
  congr 1
  rw [List.set_append_right _ _ (by simp)]
  simp only [List.take_zero, List.nil_append, List.length_append, List.length_singleton]
  rw [set_eq (by simp; omega)]
  simp only [List.take_zero, List.nil_append, Nat.sub_self, List.drop_drop,
    List.append_assoc, List.singleton_append]

theorem length_foldl_absorb (f : List T → List T) (w : ℕ) (hf : ∀ s, s.length = w → (f s).length = w)
    (r : ℕ) (hr : r ≤ w) :
    ∀ (bs : List (List T)) (s : List T), s.length = w → (∀ b ∈ bs, b.length ≤ r) →
      (bs.foldl (absorb f) s).length = w := by
  intro bs
  induction bs with
  | nil => intro s hs _; simpa using hs
  | cons b bs ih =>
    intro s hs hb
    rw [List.foldl_cons]
    apply ih _ _ (fun b' hb' => hb b' (by simp [hb']))
    apply hf
    have := hb b (by simp)
    simp [overwrite]
    omega

theorem blocks_length_le (r : ℕ) (hr : 0 < r) :
    ∀ l : List T, ∀ b ∈ blocks r l, b.length ≤ r := by
  intro l
  induction h : l.length using Nat.strong_induction_on generalizing l with
  | _ n ih =>
    rcases l with _ | ⟨x, xs⟩
    · simp [blocks_nil]
    · rw [blocks_cons r _ hr (by simp)]
      intro b hb
      rcases List.mem_cons.1 hb with rfl | hb
      · simp only [List.length_take]; omega
      · exact ih _ (by simp [← h]; omega) _ rfl b hb

/-- Item by item, the padding-free loop computes the block-wise absorption. -/
theorem pfFinish_foldl (f : List T → List T) (w r : ℕ) (hr : 0 < r) (hrw : r ≤ w)
    (hf : ∀ s, s.length = w → (f s).length = w) :
    ∀ (m s : List T), s.length = w →
      pfFinish f (m.foldl (pfStep f r) (s, 0)) = (blocks r m).foldl (absorb f) s := by
  intro m
  induction h : m.length using Nat.strong_induction_on generalizing m with
  | _ n ih =>
    intro s hs
    rcases Nat.lt_or_ge m.length r with hlt | hge
    · rcases m with _ | ⟨x, xs⟩
      · simp [pfFinish, blocks_nil]
      · rw [foldl_pfStep_lt f r _ s 0 (by simpa using hlt) (by simp at hlt ⊢; omega),
          blocks_of_lt r _ (Nat.le_of_lt hlt) (by simp)]
        simp [pfFinish, absorb, overwrite]
    · have hne : m ≠ [] := by rintro rfl; simp at hge; omega
      rw [← List.take_append_drop r m, List.foldl_append,
        foldl_pfStep_full f r _ s (by simp; omega) (by omega) hr, List.take_append_drop,
        blocks_cons r m hr hne, List.foldl_cons]
      apply ih _ (by simp; omega) _ rfl
      apply hf
      simp [overwrite]
      omega

/-! ## The 10-padded sponge -/

/-- The state the next item lands in: a waiting full block is permuted first. -/
def p10Pre (f : List T → List T) (full : Bool) (s : List T) : List T := bif full then f s else s

/-- One iteration of the 10-padded loop.

A full block waits in the rate, flagged, until the next item arrives; only then is it permuted.
-/
def p10Step (f : List T → List T) (r : ℕ) (p : List T × ℕ × Bool) (x : T) : List T × ℕ × Bool :=
  let s := p10Pre f p.2.2 p.1
  if p.2.1 + 1 = r then (s.set p.2.1 x, 0, true) else (s.set p.2.1 x, p.2.1 + 1, false)

/-- After the loop: the capacity separator on a waiting full block, or the sentinel and zeros after a partial one; then the permutation. -/
def p10Finish (f : List T → List T) (d : T → T) (zero : T) (r : ℕ) (p : List T × ℕ × Bool) : List T :=
  if p.2.2 then f (p.1.set r (d (p.1.getD r zero)))
  else f (p.1.take p.2.1 ++ d zero :: List.replicate (r - p.2.1 - 1) zero ++ p.1.drop r)

theorem foldl_p10Step_false (f : List T → List T) (r : ℕ) :
    ∀ (b s : List T) (i : ℕ), i + b.length < r → i + b.length ≤ s.length →
      b.foldl (p10Step f r) (s, i, false) =
        (s.take i ++ b ++ s.drop (i + b.length), i + b.length, false) := by
  intro b
  induction b with
  | nil => intro s i _ _; simp
  | cons x b ih =>
    intro s i h1 h2
    simp only [List.length_cons] at h1 h2
    rw [List.foldl_cons, p10Step]
    dsimp only [p10Pre, Bool.cond_false]
    rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega))]
    rw [ih _ _ (by omega) (by simp; omega)]
    refine Prod.ext ?_ (Prod.ext (by simp; omega) rfl)
    apply List.ext_getElem (by simp; omega)
    intro n h3 h4
    simp only [List.getElem_append, List.getElem_take, List.getElem_drop, List.getElem_set,
      List.getElem_cons, List.length_take, List.length_append, List.length_cons, List.length_set]
    split_ifs <;> first | rfl | omega | (congr 1; omega)

/-- A partial block, from a block boundary. -/
theorem foldl_p10Step_partial (f : List T → List T) (r : ℕ) (b s : List T) (full : Bool)
    (hb0 : b ≠ []) (hb : b.length < r) (hs : r ≤ (p10Pre f full s).length) :
    b.foldl (p10Step f r) (s, 0, full) = (overwrite (p10Pre f full s) b, b.length, false) := by
  obtain ⟨x, b', rfl⟩ := List.exists_cons_of_ne_nil hb0
  simp only [List.length_cons] at hb ⊢
  rw [List.foldl_cons, p10Step]
  dsimp only
  rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega))]
  generalize p10Pre f full s = t at hs ⊢
  rw [foldl_p10Step_false f r b' _ (0 + 1) (by omega) (by simp; omega)]
  refine Prod.ext ?_ (Prod.ext (by simp; omega) rfl)
  apply List.ext_getElem (by simp [overwrite]; omega)
  intro n h3 h4
  simp only [overwrite, List.getElem_append, List.getElem_take, List.getElem_drop, List.getElem_set,
    List.getElem_cons, List.length_take, List.length_append, List.length_cons, List.length_set]
  split_ifs <;> first | rfl | omega | (congr 1; omega)

/-- A whole block, from a block boundary, waits in the rate, flagged. -/
theorem foldl_p10Step_full (f : List T → List T) (r : ℕ) (b s : List T) (full : Bool)
    (hb : b.length = r) (hr : 0 < r) (hs : r ≤ (p10Pre f full s).length) :
    b.foldl (p10Step f r) (s, 0, full) = (overwrite (p10Pre f full s) b, 0, true) := by
  obtain ⟨b', x, rfl⟩ : ∃ b' x, b = b' ++ [x] := by
    rcases b.eq_nil_or_concat' with rfl | h
    · simp at hb; omega
    · exact h
  simp only [List.length_append, List.length_singleton] at hb
  rcases b' with _ | ⟨y, b''⟩
  · simp only [List.nil_append, List.foldl_cons, List.foldl_nil, p10Step, Nat.zero_add]
    simp only [List.length_nil, Nat.zero_add] at hb
    rw [ite_eq_left_of_eq_true _ _ (eq_true hb)]
    generalize p10Pre f full s = t at hs ⊢
    congr 1
    apply List.ext_getElem (by simp [overwrite]; omega)
    intro n h3 h4
    simp only [overwrite, List.getElem_append, List.getElem_drop, List.getElem_set,
      List.getElem_cons, List.length_cons, List.length_nil]
    split_ifs <;> first | rfl | omega | (congr 1; omega)
  · simp only [List.length_cons] at hb
    rw [List.foldl_append, foldl_p10Step_partial f r _ s full (by simp) (by simp; omega) hs]
    simp only [List.foldl_cons, List.foldl_nil, p10Step, List.length_cons]
    generalize p10Pre f full s = t at hs ⊢
    simp only [p10Pre, Bool.cond_false]
    rw [ite_eq_left_of_eq_true _ _ (eq_true (by omega))]
    congr 1
    simp only [overwrite]
    rw [List.set_append_right _ _ (by simp)]
    simp only [List.length_cons, Nat.sub_self]
    simp
    rw [List.drop_eq_getElem_cons (show b''.length + 1 < t.length by omega), List.set_cons_zero]

/-- Whole blocks, from a block boundary: the last one waits in the rate, flagged, and the others are absorbed. -/
theorem foldl_p10Step_blocks (f : List T → List T) (w r : ℕ) (hr : 0 < r) (hrw : r ≤ w)
    (hf : ∀ s, s.length = w → (f s).length = w) :
    ∀ (k : ℕ) (m s : List T) (full : Bool), m.length = r * (k + 1) →
      (p10Pre f full s).length = w →
      m.foldl (p10Step f r) (s, 0, full) =
        (overwrite (((blocks r m).dropLast).foldl (absorb f) (p10Pre f full s))
          ((blocks r m).getLastD []), 0, true) := by
  intro k
  induction k with
  | zero =>
    intro m s full hm hs
    have hne : m ≠ [] := by rintro rfl; simp at hm; omega
    rw [foldl_p10Step_full f r m s full (by simpa using hm) hr (by omega),
      blocks_of_lt r m (by simp at hm; omega) hne]
    rfl
  | succ k ih =>
    intro m s full hm hs
    have hne : m ≠ [] := by rintro rfl; simp at hm; rw [Nat.mul_succ] at hm; omega
    have hdrop : (m.drop r).length = r * (k + 1) := by
      simp only [List.length_drop, hm, Nat.mul_succ]; omega
    have hne' : blocks r (m.drop r) ≠ [] := by
      have hne2 : m.drop r ≠ [] := by
        intro h; rw [h] at hdrop; simp at hdrop; rw [Nat.mul_succ] at hdrop; omega
      rw [blocks_cons r _ hr hne2]; simp
    rw [← List.take_append_drop r m, List.foldl_append,
      foldl_p10Step_full f r _ s full (by simp; rw [hm, Nat.mul_succ]; omega) hr (by omega),
      List.take_append_drop]
    rw [ih (m.drop r) _ true hdrop (by
      rw [show p10Pre f true _ = f _ from rfl]
      apply hf
      simp only [overwrite, List.length_append, List.length_take, List.length_drop]
      have : r ≤ m.length := by rw [hm, Nat.mul_succ]; omega
      omega)]
    rw [blocks_cons r m hr hne, List.dropLast_cons_of_ne_nil hne', List.foldl_cons]
    obtain ⟨b, bs', hbs⟩ := List.exists_cons_of_ne_nil hne'
    rw [hbs]
    simp only [List.getLastD_cons]
    rfl

/-- The sentinel and zeros after a partial block are the 10-padding of that block. -/
theorem finish_partial (S R : List T) (d0 zero : T) (r : ℕ) (hR : R.length < r) :
    (overwrite S R).take R.length ++ d0 :: List.replicate (r - R.length - 1) zero ++
        (overwrite S R).drop r =
      overwrite S (R ++ d0 :: List.replicate (r - R.length - 1) zero) := by
  simp only [overwrite, List.take_left', List.length_append, List.length_cons,
    List.length_replicate, List.drop_append, List.drop_eq_nil_of_le (Nat.le_of_lt hR),
    List.nil_append, List.drop_drop, List.append_assoc, List.cons_append]
  congr 4
  omega

/-- The 10-padded sponge from any initial state, before squeezing. -/
def p10Core (f : List T → List T) (d : T → T) (zero : T) (r : ℕ) (s m : List T) : List T :=
  let p := pad10Blocks zero (d zero) r m
  let s0 := p.1.dropLast.foldl (absorb f) s
  let s' := overwrite s0 (p.1.getLastD [])
  let s'' := if p.2 then s'.set r (d (s'.getD r zero)) else s'
  f s''

theorem pad10_eq_p10Core (f : List T → List T) (d : T → T) (zero : T) (w r out : ℕ) (m : List T) :
    pad10 f d zero w r out m = (p10Core f d zero r (List.replicate w zero) m).take out := rfl

/-- Item by item, the 10-padded loop computes the padded block-wise absorption. -/
theorem p10Finish_foldl (f : List T → List T) (d : T → T) (zero : T) (w r : ℕ) (hr : 0 < r)
    (hrw : r ≤ w) (hf : ∀ s, s.length = w → (f s).length = w) (m s : List T) (hs : s.length = w) :
    p10Finish f d zero r (m.foldl (p10Step f r) (s, 0, false)) = p10Core f d zero r s m := by
  by_cases hA : m ≠ [] ∧ m.length % r = 0
  · obtain ⟨k, hk⟩ : ∃ k, m.length = r * (k + 1) := by
      have h1 : m.length ≠ 0 := by simpa using hA.1
      refine ⟨m.length / r - 1, ?_⟩
      have := Nat.div_add_mod m.length r
      have h2 : 0 < m.length / r := Nat.div_pos (by
        rcases Nat.lt_or_ge m.length r with h | h
        · rw [Nat.mod_eq_of_lt h] at hA; omega
        · exact h) hr
      rw [Nat.sub_add_cancel h2]
      omega
    rw [foldl_p10Step_blocks f w r hr hrw hf k m s false hk hs]
    have hp : pad10Blocks zero (d zero) r m = (blocks r m, true) := by
      unfold pad10Blocks; exact ite_eq_left_of_eq_true _ _ (eq_true hA)
    simp only [p10Finish, p10Core, hp, p10Pre, Bool.cond_false, ite_true]
  · have hmod := Nat.div_add_mod m.length r
    have hlt := Nat.mod_lt m.length hr
    have hkm : m.length / r * r = m.length - m.length % r := by rw [Nat.mul_comm]; omega
    have hp : pad10Blocks zero (d zero) r m =
        (blocks r (m.take (m.length / r * r)) ++ [m.drop (m.length / r * r) ++ d zero ::
          List.replicate (r - (m.length - m.length / r * r) - 1) zero], false) := by
      unfold pad10Blocks; exact ite_eq_right_of_eq_false _ _ (eq_false hA)
    simp only [p10Core, hp, Bool.false_eq_true, ite_false]
    rcases Nat.eq_zero_or_pos (m.length / r) with hk0 | hk0
    · have hm : m.length < r := by rw [hk0] at hmod; omega
      have hk : m.length / r * r = 0 := by rw [hk0]; simp
      rw [hk]
      rcases m with _ | ⟨x, xs⟩
      · simp [p10Finish, blocks_nil, overwrite, Nat.sub_add_cancel hr]
      · rw [foldl_p10Step_partial f r _ s false (by simp) hm (by simp [p10Pre]; omega)]
        simp only [p10Finish, p10Pre, Bool.cond_false, Bool.false_eq_true, ite_false,
          List.take_zero, List.drop_zero, blocks_nil, List.nil_append, Nat.sub_zero]
        simp only [List.dropLast_singleton, List.foldl_nil, List.getLastD_eq_getLast?,
          List.getLast?_singleton, Option.getD_some]
        rw [finish_partial s (x :: xs) (d zero) zero r hm]
    · have hm0 : m ≠ [] := by rintro rfl; simp at hk0
      have hmr : m.length % r ≠ 0 := fun h => hA ⟨hm0, h⟩
      generalize hK : m.length / r * r = K at hkm ⊢
      obtain ⟨j, hj⟩ : ∃ j, K = r * (j + 1) :=
        ⟨m.length / r - 1, by rw [← hK, Nat.mul_comm, Nat.sub_add_cancel hk0]⟩
      have hKm : K < m.length := by omega
      have hR : (m.drop K).length < r := by rw [List.length_drop]; omega
      have hRne : m.drop K ≠ [] := by
        intro h; have := congrArg List.length h; simp at this; omega
      have htk : (m.take K).length = r * (j + 1) := by simp; omega
      have hbne : blocks r (m.take K) ≠ [] := by
        rw [blocks_cons r _ hr (by
          intro h
          rw [h, List.length_nil] at htk
          exact absurd htk.symm (Nat.ne_of_gt (Nat.mul_pos hr (Nat.succ_pos j))))]
        simp
      conv_lhs => rw [← List.take_append_drop K m, List.foldl_append,
        foldl_p10Step_blocks f w r hr hrw hf j (m.take K) s false htk (by simpa [p10Pre] using hs)]
      have hlen : ((blocks r (m.take K)).foldl (absorb f) s).length = w :=
        length_foldl_absorb f w hf r hrw _ s hs (blocks_length_le r hr _)
      have hfold : p10Pre f true (overwrite ((blocks r (m.take K)).dropLast.foldl (absorb f)
          (p10Pre f false s)) ((blocks r (m.take K)).getLastD [])) =
          (blocks r (m.take K)).foldl (absorb f) s := by
        conv_rhs => rw [← List.dropLast_append_getLast hbne]
        rw [List.foldl_append]
        simp [p10Pre, absorb, List.getLastD_eq_getLast?, List.getLast?_eq_some_getLast hbne]
      rw [foldl_p10Step_partial f r (m.drop K) _ true hRne hR (by rw [hfold, hlen]; exact hrw),
        hfold]
      simp only [p10Finish, Bool.false_eq_true, ite_false, List.dropLast_concat,
        List.getLastD_concat]
      rw [show r - (m.length - K) - 1 = r - (m.drop K).length - 1 by simp,
        finish_partial _ (m.drop K) (d zero) zero r hR]

end Plonky3Lean.Proofs.Symmetric
