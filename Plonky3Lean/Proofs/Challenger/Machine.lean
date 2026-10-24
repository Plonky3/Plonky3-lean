module

public import Plonky3Lean.Spec.Duplex
public import Plonky3Lean.Proofs.Symmetric.Collisions
public import Mathlib.Algebra.CharP.Basic

@[expose] public section

/-!
# The duplex challenger as a machine over lists

The state of the duplex challenger holds the sponge, the input buffer and the output buffer as lists.

Observing, sampling and the duplexing step are written exactly as the Rust code runs them.

A sibling file proves that the extracted code computes these functions.

Here the machine is related to the duplex construction of the specification:

- every transcript of observations and samples returns the samples the construction gives
- the sample after an observation reads the permutation of a block that ends with that observation
- one duplexing step is injective in its block when the characteristic exceeds the rate
- in characteristic q <= r the length tag repeats, and a block collides with its zero extension.
-/

namespace Plonky3Lean.Proofs.Challenger

open Plonky3Lean.Spec.Sponge Plonky3Lean.Spec.Duplex Plonky3Lean.Proofs.Symmetric

/-- The challenger's state: the sponge, the inputs not yet absorbed, and the outputs not yet read. -/
structure St (F : Type) where
  s : List F
  inb : List F
  outb : List F

section Machine

variable {F : Type} [AddMonoidWithOne F] (f : List F → List F) (r : ℕ)

/-- Absorb the input buffer, permute, and refill the output buffer with the new rate. -/
def St.duplexing (st : St F) : St F :=
  ⟨f (pad r st.s st.inb), [], (f (pad r st.s st.inb)).take r⟩

/-- Clear the outputs, buffer the value, and duplex when the buffer reaches the rate. -/
def St.observe (st : St F) (x : F) : St F :=
  let st₁ : St F := ⟨st.s, st.inb ++ [x], []⟩
  if st₁.inb.length = r then st₁.duplexing f r else st₁

/-- Duplex if inputs are pending or no output is left, then pop the last output. -/
def St.sample (st : St F) : F × St F :=
  let st₁ := if st.inb ≠ [] ∨ st.outb = [] then st.duplexing f r else st
  (st₁.outb.getLastD 0, ⟨st₁.s, st₁.inb, st₁.outb.dropLast⟩)

/-- Observe each value in order. -/
def St.observeAll (st : St F) (xs : List F) : St F := xs.foldl (St.observe f r) st

/-- Draw k samples in order. -/
def St.sampleN : St F → ℕ → List F × St F
  | st, 0 => ([], st)
  | st, k + 1 =>
    let p := st.sample f r
    let q := p.2.sampleN k
    (p.1 :: q.1, q.2)

/-- One phase: observe xs, then draw k samples. -/
def St.phase (st : St F) (xs : List F) (k : ℕ) : List F × St F :=
  (st.observeAll f r xs).sampleN f r k

/-- A transcript, phase by phase. -/
def St.transcript : St F → List (List F × ℕ) → List F
  | _, [] => []
  | st, (xs, k) :: ps => (st.phase f r xs k).1 ++ (st.phase f r xs k).2.transcript ps

end Machine

section Lists

variable {T : Type}

theorem getLastD_take (l : List T) (n : ℕ) (d : T) (h0 : 0 < n) (hn : n ≤ l.length) :
    (l.take n).getLastD d = l.getD (n - 1) d := by
  rw [List.getLastD_eq_getLast?, List.getLast?_eq_getElem?, List.getD_eq_getElem?_getD]
  simp [Nat.min_eq_left hn, show n - 1 < n by omega, show n - 1 < l.length by omega]

end Lists

section Lengths

variable {F : Type} [AddMonoidWithOne F]

theorem pad_length (r : ℕ) (s sigma : List F) (hr : r < s.length) (hs : sigma.length ≤ r) :
    (pad r s sigma).length = s.length := by
  unfold pad
  split_ifs
  · rfl
  · simp only [List.length_append, List.length_replicate, List.length_cons, List.length_drop]
    omega

omit [AddMonoidWithOne F] in
theorem blank_length (f : List F → List F) (w : ℕ) (hf : ∀ s, s.length = w → (f s).length = w) :
    ∀ (n : ℕ) (s : List F), s.length = w → (blank f n s).length = w := by
  intro n
  induction n with
  | zero => intro s hs; exact hs
  | succ n ih => intro s hs; exact ih _ (hf s hs)

theorem foldl_duplex_length (f : List F → List F) (r w : ℕ) (hrw : r < w)
    (hf : ∀ s, s.length = w → (f s).length = w) :
    ∀ (bs : List (List F)) (s : List F), (∀ b ∈ bs, b.length ≤ r) → s.length = w →
      (bs.foldl (duplex f r) s).length = w
  | [], _, _, hs => hs
  | b :: bs, s, hb, hs =>
    foldl_duplex_length f r w hrw hf bs _ (fun b' hb' => hb b' (List.mem_cons_of_mem _ hb'))
      (hf _ (by rw [pad_length r s b (by omega) (hb b List.mem_cons_self), hs]))

theorem absorbRun_length (f : List F → List F) (r w : ℕ) (hr : 0 < r) (hrw : r < w)
    (hf : ∀ s, s.length = w → (f s).length = w) (xs s : List F) (hs : s.length = w) :
    (absorbRun f r s xs).length = w :=
  foldl_duplex_length f r w hrw hf _ s (blocks_length_le r hr xs) hs

end Lengths

section Phases

variable {F : Type} [AddMonoidWithOne F] (f : List F → List F) (r w : ℕ)

/-- Take j samples drawn from a fresh rate of a state.

The challenger then holds the last state whose rate it read, and the rest of that rate. -/
def afterSamples (s₁ : List F) : ℕ → St F
  | 0 => ⟨s₁, [], s₁.take r⟩
  | j + 1 => ⟨blank f (j / r) s₁, [], (blank f (j / r) s₁).take (r - (j % r + 1))⟩

omit [AddMonoidWithOne F] in
theorem blank_succ' (n : ℕ) (s : List F) : blank f (n + 1) s = f (blank f n s) := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih => rw [blank, ih, blank]

variable {f r w}

/-- With no input pending and outputs left, a sample pops the last output. -/
theorem sample_buffered (s : List F) (n : ℕ) (hn : 0 < n) (hl : n ≤ s.length) :
    (St.mk s [] (s.take n)).sample f r = (s.getD (n - 1) 0, ⟨s, [], s.take (n - 1)⟩) := by
  have hne : s.take n ≠ [] := List.ne_nil_of_length_pos (by simp; omega)
  simp only [St.sample, ne_eq, not_true_eq_false, hne, or_self, ite_false]
  rw [getLastD_take _ _ _ hn hl, List.dropLast_take hl]

/-- With no input pending and no output left, a sample makes a blank call.

It pops the last rate cell of that call. -/
theorem sample_empty (s : List F) (hr : 0 < r) (hl : r ≤ (f s).length) :
    (St.mk s [] []).sample f r = ((f s).getD (r - 1) 0, ⟨f s, [], (f s).take (r - 1)⟩) := by
  have hne : (f s).take r ≠ [] := List.ne_nil_of_length_pos (by simp; omega)
  simp only [St.sample, ne_eq, not_true_eq_false, or_true, ite_true, St.duplexing, pad]
  rw [getLastD_take _ _ _ hr hl, List.dropLast_take hl]

theorem sample_afterSamples (hr : 0 < r) (hrw : r < w)
    (hf : ∀ s, s.length = w → (f s).length = w) (s₁ : List F) (hs : s₁.length = w) (j : ℕ) :
    (afterSamples f r s₁ j).sample f r = (phaseSample f r s₁ j, afterSamples f r s₁ (j + 1)) := by
  have hbl := blank_length f w hf
  have hmod := Nat.mod_lt j hr
  rcases j with _ | j
  · rw [afterSamples, sample_buffered s₁ r hr (by omega)]
    simp [phaseSample, afterSamples, blank]
  · have hlen := hbl (j / r) s₁ hs
    by_cases hm : j % r + 1 = r
    · -- The rate is used up: a blank call refills it.
      have h2 : (j + 1) % r = 0 := by rw [← Nat.mod_add_mod, hm, Nat.mod_self]
      have h1 : (j + 1) / r = j / r + 1 := by
        rw [Nat.succ_div]
        simp [Nat.dvd_of_mod_eq_zero h2]
      rw [afterSamples, hm, Nat.sub_self, List.take_zero,
        sample_empty (blank f (j / r) s₁) hr (by rw [hf _ hlen]; omega)]
      simp [phaseSample, afterSamples, h1, h2, blank_succ']
    · -- The next output is still buffered.
      have hmod' := Nat.mod_lt j hr
      have h2 : (j + 1) % r = j % r + 1 := by
        rw [← Nat.mod_add_mod, Nat.mod_eq_of_lt (by omega)]
      have h1 : (j + 1) / r = j / r := by
        rw [Nat.succ_div]
        simp only [Nat.add_eq_left, ite_eq_right_iff, one_ne_zero, imp_false]
        intro hd
        have := Nat.mod_eq_zero_of_dvd hd
        omega
      rw [afterSamples, sample_buffered _ (r - (j % r + 1)) (by omega) (by omega)]
      simp only [phaseSample, afterSamples, h1, h2, Prod.mk.injEq, St.mk.injEq, true_and]
      rw [show r - (j % r + 1) - 1 = r - 1 - (j % r + 1) by omega,
        show r - (j % r + 1 + 1) = r - 1 - (j % r + 1) by omega]
      exact ⟨rfl, rfl⟩

theorem sampleN_afterSamples (hr : 0 < r) (hrw : r < w)
    (hf : ∀ s, s.length = w → (f s).length = w) (s₁ : List F) (hs : s₁.length = w) :
    ∀ (k j : ℕ), (afterSamples f r s₁ j).sampleN f r k =
      ((List.range' j k).map (phaseSample f r s₁), afterSamples f r s₁ (j + k)) := by
  intro k
  induction k with
  | zero => intro j; rfl
  | succ k ih =>
    intro j
    rw [St.sampleN, sample_afterSamples hr hrw hf s₁ hs j, ih (j + 1), List.range'_succ,
      List.map_cons, show j + 1 + k = j + (k + 1) by omega]

omit [AddMonoidWithOne F] in
theorem blocks_split (hr : 0 < r) (xs : List F) (hk : xs.length % r ≠ 0) :
    blocks r xs = blocks r (xs.take (xs.length / r * r)) ++ [xs.drop (xs.length / r * r)] := by
  have hdm := Nat.div_add_mod xs.length r
  have hlt := Nat.mod_lt xs.length hr
  rw [Nat.mul_comm] at hdm
  conv_lhs => rw [← List.take_append_drop (xs.length / r * r) xs]
  rw [blocks_append r hr (xs.length / r) _ _ (by
      rw [List.length_take, Nat.min_eq_left (by omega), Nat.mul_comm]),
    blocks_of_lt r (xs.drop (xs.length / r * r)) (by rw [List.length_drop]; omega)
      (by rw [ne_eq, List.drop_eq_nil_iff]; omega)]

omit [AddMonoidWithOne F] in
theorem getLastD_cons_of_ne {T : Type} (a d : T) (l : List T) (hl : l ≠ []) :
    (a :: l).getLastD d = l.getLastD d := by
  obtain ⟨b, l, rfl⟩ := List.exists_cons_of_ne_nil hl
  simp

omit [AddMonoidWithOne F] in
theorem blocks_ne_nil (hr : 0 < r) (xs : List F) (hxs : xs ≠ []) : blocks r xs ≠ [] := by
  intro hb
  have := flatten_blocks r hr xs
  rw [hb, List.flatten_nil] at this
  exact hxs this.symm

theorem observeAll_short (st : St F) (ys : List F) (hy : ys ≠ [])
    (h : st.inb.length + ys.length < r) : st.observeAll f r ys = ⟨st.s, st.inb ++ ys, []⟩ := by
  induction ys generalizing st with
  | nil => exact absurd rfl hy
  | cons y ys ih =>
    simp only [List.length_cons] at h
    have hob : st.observe f r y = ⟨st.s, st.inb ++ [y], []⟩ := by
      simp only [St.observe, List.length_append, List.length_singleton]
      split_ifs with hc
      · omega
      · rfl
    rw [St.observeAll, List.foldl_cons, hob]
    rcases eq_or_ne ys [] with rfl | hys
    · rfl
    · rw [← St.observeAll, ih _ hys (by simp; omega)]
      simp

theorem observeAll_append (st : St F) (a b : List F) :
    st.observeAll f r (a ++ b) = (st.observeAll f r a).observeAll f r b := by
  simp [St.observeAll, List.foldl_append]

theorem observeAll_block (st : St F) (ys : List F) (hy : ys ≠ [])
    (h : st.inb.length + ys.length = r) :
    st.observeAll f r ys = (St.mk st.s (st.inb ++ ys) []).duplexing f r := by
  obtain ⟨init, y, rfl⟩ := List.eq_nil_or_concat ys |>.resolve_left hy
  rw [List.concat_eq_append] at h ⊢
  simp only [List.length_append, List.length_singleton] at h
  have hmid : st.observeAll f r init = ⟨st.s, st.inb ++ init, if init = [] then st.outb else []⟩ := by
    rcases eq_or_ne init [] with rfl | hi
    · simp [St.observeAll]
    · rw [observeAll_short st init hi (by omega)]
      simp [hi]
  rw [observeAll_append, hmid]
  simp only [St.observeAll, List.foldl_cons, List.foldl_nil, St.observe, List.append_assoc,
    List.length_append, List.length_singleton]
  split_ifs
  rfl

/-- Observing a run of values from an empty input buffer absorbs every whole block.

If the run ends on a block boundary, the last observation absorbed the last block.

Its rate is then fresh.

Otherwise the last block waits in the input buffer and the outputs are cleared. -/
theorem observeAll_eq (hr : 0 < r) (xs : List F) (st : St F) (hinb : st.inb = []) (hxs : xs ≠ []) :
    st.observeAll f r xs =
      if ((blocks r xs).getLastD []).length = r then
        ⟨absorbRun f r st.s xs, [], (absorbRun f r st.s xs).take r⟩
      else ⟨(blocks r xs).dropLast.foldl (duplex f r) st.s, (blocks r xs).getLastD [], []⟩ := by
  obtain ⟨s, inb, o⟩ := st
  simp only at hinb
  subst hinb
  by_cases hle : xs.length ≤ r
  · rw [blocks_of_lt r xs hle hxs]
    simp only [List.getLastD_cons, List.getLastD_nil, List.dropLast_singleton, List.foldl_nil]
    split_ifs with hl
    · rw [observeAll_block _ xs hxs (by simpa using hl)]
      simp [absorbRun, blocks_of_lt r xs hle hxs, St.duplexing, duplex]
    · rw [observeAll_short _ xs hxs (by simp; omega)]
      simp
  · have hd : xs.drop r ≠ [] := by rw [ne_eq, List.drop_eq_nil_iff]; omega
    have hbd := blocks_ne_nil hr _ hd
    have htake : (xs.take r).length = r := List.length_take_of_le (by omega)
    have hsplit := observeAll_append (f := f) (r := r) (St.mk s [] o) (xs.take r) (xs.drop r)
    rw [List.take_append_drop] at hsplit
    rw [hsplit, observeAll_block (St.mk s [] o) (xs.take r) (List.ne_nil_of_length_pos (by omega))
      (by simpa using htake),
      observeAll_eq hr (xs.drop r) _ rfl hd, blocks_cons r xs hr hxs,
      getLastD_cons_of_ne _ _ _ hbd, List.dropLast_cons_of_ne_nil hbd]
    simp only [St.duplexing, List.nil_append, List.foldl_cons, absorbRun, duplex,
      blocks_cons r xs hr hxs]
termination_by xs.length
decreasing_by simp; omega

omit [AddMonoidWithOne F] in
theorem blocks_mem_ne_nil (hr : 0 < r) : ∀ (xs : List F), ∀ b ∈ blocks r xs, b ≠ [] := by
  intro xs
  induction h : xs.length using Nat.strong_induction_on generalizing xs with
  | _ n ih =>
    rcases xs with _ | ⟨x, xs⟩
    · simp [blocks_nil]
    · rw [blocks_cons r _ hr (by simp)]
      intro b hb
      rcases List.mem_cons.1 hb with rfl | hb
      · simp [List.take_eq_nil_iff]; omega
      · exact ih _ (by simp [← h]; omega) _ rfl b hb

omit [AddMonoidWithOne F] in
theorem blocks_last_ne_nil (hr : 0 < r) (xs : List F) (hxs : xs ≠ []) :
    (blocks r xs).getLastD [] ≠ [] := by
  have hbn := blocks_ne_nil hr xs hxs
  rw [List.getLastD_eq_getLast?, List.getLast?_eq_some_getLast hbn, Option.getD_some]
  exact blocks_mem_ne_nil hr xs _ (List.getLast_mem hbn)

theorem absorbRun_split (hr : 0 < r) (s xs : List F) (hxs : xs ≠ []) :
    absorbRun f r s xs = duplex f r ((blocks r xs).dropLast.foldl (duplex f r) s) ((blocks r xs).getLastD []) := by
  have hbn := blocks_ne_nil hr xs hxs
  rw [absorbRun]
  conv_lhs => rw [← List.dropLast_append_getLast hbn]
  rw [List.foldl_append, List.getLastD_eq_getLast?, List.getLast?_eq_some_getLast hbn]
  rfl

/-- When the next sample duplexes anyway, it samples the duplexed state. -/
theorem sample_of_duplexing (st : St F) (h : st.inb ≠ [] ∨ st.outb = [])
    (hne : (st.duplexing f r).outb ≠ []) :
    st.sample f r = (st.duplexing f r).sample f r := by
  have h' : (st.duplexing f r).inb = [] := rfl
  simp only [St.sample, ne_eq, h, ite_true, h', not_true_eq_false, hne, or_self, ite_false]

theorem sampleN_of_duplexing (st : St F) (h : st.inb ≠ [] ∨ st.outb = [])
    (hne : (st.duplexing f r).outb ≠ []) (k : ℕ) (hk : 0 < k) :
    st.sampleN f r k = (st.duplexing f r).sampleN f r k := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt hk
  simp only [Nat.zero_add, St.sampleN, sample_of_duplexing st h hne]

theorem take_ne_nil {T : Type} (l : List T) (r : ℕ) (hr : 0 < r) (hl : r ≤ l.length) : l.take r ≠ [] :=
  List.ne_nil_of_length_pos (by simp; omega)

/-- A phase from a clean input buffer returns the construction's samples and ends in its state.

The phase must observe a value, or start with no buffered output. -/
theorem phase_eq (hr : 0 < r) (hrw : r < w) (hf : ∀ s, s.length = w → (f s).length = w)
    (st : St F) (hs : st.s.length = w) (hinb : st.inb = []) (xs : List F) (k : ℕ)
    (hfresh : xs ≠ [] ∨ st.outb = []) (hk : 0 < k) :
    st.phase f r xs k = (phase f r st.s xs k, afterSamples f r (phaseFirst f r st.s xs) k) := by
  have key : st.phase f r xs k = (afterSamples f r (phaseFirst f r st.s xs) 0).sampleN f r k := by
    rw [St.phase]
    rcases eq_or_ne xs [] with rfl | hxs
    · obtain ⟨s, inb, o⟩ := st
      simp only at hinb hfresh hs
      subst hinb
      simp only [ne_eq, not_true_eq_false, false_or] at hfresh
      subst hfresh
      rw [St.observeAll, List.foldl_nil, sampleN_of_duplexing _ (Or.inr rfl)
        (take_ne_nil _ r hr (by simp [pad, hf s hs]; omega)) k hk]
      simp [St.duplexing, afterSamples, phaseFirst, pad]
    · rw [observeAll_eq hr xs st hinb hxs]
      split_ifs with hl
      · simp [afterSamples, phaseFirst, hxs]
      · have hP := foldl_duplex_length f r w hrw hf (blocks r xs).dropLast st.s
          (fun b hb => blocks_length_le r hr xs b (List.dropLast_subset _ hb)) hs
        have hL : ((blocks r xs).getLastD []).length ≤ r := by
          have hbn := blocks_ne_nil hr xs hxs
          rw [List.getLastD_eq_getLast?, List.getLast?_eq_some_getLast hbn, Option.getD_some]
          exact blocks_length_le r hr xs _ (List.getLast_mem hbn)
        rw [sampleN_of_duplexing _ (Or.inl (blocks_last_ne_nil hr xs hxs)) (take_ne_nil _ r hr (by
          rw [hf _ (by rw [pad_length r _ _ (by dsimp only; omega) hL, hP])]; omega)) k hk]
        simp only [afterSamples, phaseFirst, hxs, ite_false]
        rw [absorbRun_split hr st.s xs hxs]
        rfl
  have hlen : (phaseFirst f r st.s xs).length = w := by
    unfold phaseFirst
    split_ifs
    · exact hf _ hs
    · exact absorbRun_length f r w hr hrw hf xs _ hs
  rw [key, sampleN_afterSamples hr hrw hf _ hlen k 0, Nat.zero_add, phase, List.range_eq_range']

omit [AddMonoidWithOne F] in
theorem afterSamples_s (s₁ : List F) (k : ℕ) (hk : 0 < k) :
    (afterSamples f r s₁ k).s = blank f ((k - 1) / r) s₁ := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt hk
  rfl

theorem transcript_eq_aux (hr : 0 < r) (hrw : r < w) (hf : ∀ s, s.length = w → (f s).length = w) :
    ∀ (ps : List (List F × ℕ)) (st : St F), (∀ p ∈ ps, 0 < p.2) → (∀ p ∈ ps.drop 1, p.1 ≠ []) →
      st.s.length = w → st.inb = [] → (∀ p ∈ ps.head?, p.1 ≠ [] ∨ st.outb = []) →
      st.transcript f r ps = transcript f r st.s ps := by
  intro ps
  induction ps with
  | nil => intro st _ _ _ _ _; rfl
  | cons p ps ih =>
    intro st hk hne hs hinb hfresh
    obtain ⟨xs, k⟩ := p
    have hk0 : 0 < k := hk _ List.mem_cons_self
    have hlen : (phaseFirst f r st.s xs).length = w := by
      unfold phaseFirst
      split_ifs
      · exact hf _ hs
      · exact absorbRun_length f r w hr hrw hf xs _ hs
    have hst := afterSamples_s (f := f) (r := r) (phaseFirst f r st.s xs) k hk0
    rw [St.transcript, transcript, phase_eq hr hrw hf st hs hinb xs k (hfresh _ rfl) hk0]
    congr 1
    rw [ih _ (fun q hq => hk q (List.mem_cons_of_mem _ hq))
      (fun q hq => hne q (by rcases ps with _ | ⟨a, ps⟩ <;> simp_all))
      (by rw [hst]; exact blank_length f w hf _ _ hlen)
      (by obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt hk0; rfl)
      (fun q hq => Or.inl (hne q (by rcases ps with _ | ⟨a, ps⟩ <;> simp_all))), hst]
    rfl

/-- Run every well-formed transcript from a challenger with empty buffers.

It returns the samples of the duplex construction. -/
theorem transcript_eq (hr : 0 < r) (hrw : r < w) (hf : ∀ s, s.length = w → (f s).length = w)
    (ps : List (List F × ℕ)) (st : St F) (hwf : WellFormed ps) (hs : st.s.length = w)
    (hinb : st.inb = []) (hout : st.outb = []) : st.transcript f r ps = transcript f r st.s ps :=
  transcript_eq_aux hr hrw hf ps st hwf.1 hwf.2 hs hinb (fun _ _ => Or.inr hout)

end Phases

section Binding

variable {F : Type} [AddMonoidWithOne F] {f : List F → List F} {r w : ℕ}

/-- The sample after an observation reads the permutation of a block that ends with that observation.

No output buffered before the observation is ever returned after it. -/
theorem sample_observe (hr : 0 < r) (hrw : r < w) (hf : ∀ s, s.length = w → (f s).length = w)
    (st : St F) (hs : st.s.length = w) (hinb : st.inb.length < r) (x : F) :
    ((st.observe f r x).sample f r).1 = (f (pad r st.s (st.inb ++ [x]))).getD (r - 1) 0 := by
  have hlen : (f (pad r st.s (st.inb ++ [x]))).length = w :=
    hf _ (by rw [pad_length r _ _ (by omega) (by simp; omega), hs])
  simp only [St.observe, List.length_append, List.length_singleton]
  split_ifs with h
  · simp only [St.sample, St.duplexing, ne_eq, not_true_eq_false, false_or,
      take_ne_nil (f (pad r st.s (st.inb ++ [x]))) r hr (by omega)]
    exact getLastD_take _ _ _ hr (by omega)
  · simp only [St.sample, ne_eq, List.append_eq_nil_iff, List.cons_ne_self, and_false,
      not_false_eq_true, true_or, ite_true, St.duplexing]
    exact getLastD_take _ _ _ hr (by omega)

end Binding

section Injectivity

variable {F : Type} [AddGroupWithOne F]

/-- Suppose no two lengths up to r have the same image in the field.

With a fixed state, the padded state then determines the block.

A blank call and an absorbing call never meet either.

The length tag of a nonempty block is not zero. -/
theorem pad_injective (r : ℕ) (s : List F)
    (hchar : ∀ a b : ℕ, a ≤ r → b ≤ r → (a : F) = b → a = b)
    (σ τ : List F) (hσ : σ.length ≤ r) (hτ : τ.length ≤ r) (h : pad r s σ = pad r s τ) : σ = τ := by
  -- Cell r carries s_r plus the length.
  -- The first cells carry the block.
  have cell : ∀ ρ : List F, ρ.length ≤ r → (pad r s ρ).getD r 0 = s.getD r 0 + (ρ.length : F) := by
    intro ρ hρ
    unfold pad
    split_ifs with h0
    · simp [h0]
    · rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp; omega)]
      simp only [List.length_append, List.length_replicate]
      rw [show r - (ρ.length + (r - ρ.length)) = 0 by omega]
      simp
  have hl : σ.length = τ.length :=
    hchar _ _ hσ hτ (add_left_cancel (by rw [← cell σ hσ, ← cell τ hτ, h]))
  have pre : ∀ ρ : List F, ρ.length ≤ r → (pad r s ρ).take ρ.length = ρ := by
    intro ρ hρ
    unfold pad
    split_ifs with h0
    · simp [h0]
    · simp
  rw [← pre σ hσ, ← pre τ hτ, h, hl]

/-- The no-collision hypothesis holds whenever the characteristic exceeds the rate. -/
theorem cast_inj_of_charP (q r : ℕ) [CharP F q] (hq : r < q) :
    ∀ a b : ℕ, a ≤ r → b ≤ r → (a : F) = b → a = b := by
  intro a b ha hb h
  rw [CharP.natCast_eq_natCast F q, Nat.ModEq, Nat.mod_eq_of_lt (by omega),
    Nat.mod_eq_of_lt (by omega)] at h
  exact h

/-- In characteristic q, a block collides with its extension by q zeros, as long as both fit the rate.

The overwrite pads with zeros.

The length tags n and n + q are equal in the field.

```text
    q = 2, r = 4:   pad [a]        = [a, 0, 0, 0 | s_4 + 1, ...]
                    pad [a, 0, 0]  = [a, 0, 0, 0 | s_4 + 3, ...]     and 3 = 1 in F_2
```
-/
theorem pad_collision (q r : ℕ) [CharP F q] (s σ : List F) (hσ : σ ≠ [])
    (hq : σ.length + q ≤ r) : pad r s σ = pad r s (σ ++ List.replicate q 0) := by
  have hne : σ ++ List.replicate q (0 : F) ≠ [] := by simp [hσ]
  unfold pad
  simp only [hσ, hne, ↓reduceIte]
  simp only [List.length_append, List.length_replicate, Nat.cast_add, CharP.cast_eq_zero, add_zero,
    List.append_assoc, List.replicate_append_replicate]
  rw [show q + (r - (σ.length + q)) = r - σ.length by omega]

end Injectivity

end Plonky3Lean.Proofs.Challenger
