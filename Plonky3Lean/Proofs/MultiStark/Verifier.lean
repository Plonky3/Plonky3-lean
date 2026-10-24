module

public import P3MultiStark.Zerocheck
public import Plonky3Lean.Proofs.MultiStark.Selectors
public import Plonky3Lean.Proofs.MultilinearUtil.PointForms

@[expose] public section

/-!
# The zerocheck verifier: its claim check and its closing check

The claim check accepts exactly the claim the earlier reductions fix:

```text
    claim = eta * lookup + lambda * bus        zero with neither
```

The closing check recomputes the batched constraints from the openings at the bound point r:

```text
    final_sum = eq(tau, r) * sum_i (beta^i c_i + eta l_i) + lambda * bus(r)
```

Instance i is evaluated at the suffix of r of its own arity, with the selectors in closed form there.

The checks never panic on any openings, given the caller's well-formed statement.

A wrong count is rejected with the error naming it.
-/

namespace Plonky3Lean.Proofs.MultiStark

open p3_multi_stark.zerocheck.mirror p3_multi_stark.opening.mirror p3_multi_stark.selectors.mirror
  p3_multilinear_util.point.mirror

variable {K : Type _}

/-! ## The next row -/

theorem foldl_scatterStep_some [Field K] (l : List (ℕ × K)) (row : List K)
    (h : ∀ cv ∈ l, cv.1 < row.length) :
    ∃ row', l.foldl scatterStep (some row) = some row' ∧ row'.length = row.length := by
  induction l generalizing row with
  | nil => exact ⟨row, rfl, rfl⟩
  | cons cv l ih =>
    have hcv := h cv List.mem_cons_self
    obtain ⟨row', h1, h2⟩ := ih (row.set cv.1 cv.2) fun cv' hm => by
      simpa using h cv' (List.mem_cons_of_mem _ hm)
    exact ⟨row', by simpa [scatterStep, hcv] using h1, by simpa using h2⟩

/-- The next row never panics on declared columns inside the width. -/
theorem next_row_isSome [Field K] {cols : List ℕ} {vals : List K} {width : ℕ}
    (hlen : cols.length = vals.length) (hcols : ∀ c ∈ cols, c < width) :
    (next_row cols vals width).isSome := by
  obtain ⟨row, h, -⟩ := foldl_scatterStep_some (cols.zip vals) (List.replicate width 0)
    fun cv hm => by simpa using hcols _ (List.of_mem_zip hm).1
  simp [next_row, hlen, h]

theorem eval_eq_self [Field K] {τ r : List K} (h : τ.length = r.length) :
    Point.eval_eq τ r = some (Plonky3Lean.Spec.MultilinearUtil.eq τ r) := by
  rw [Plonky3Lean.Proofs.MultilinearUtil.eval_eq_eq h]; simp

variable [Field K]

/-! ## One instance -/

/-- What the caller guarantees about one instance:

- a nonzero width
- the public-value count its AIR reads
- an arity at most the cube's
- successor columns inside the widths. -/
structure AirOk (red : ZerocheckReduction K) (e : Entry K) : Prop where
  width : e.1.main_width ≠ 0
  public_values : e.2.1 = e.1.num_public_values
  arity : e.2.2.1 ≤ red.tau.length
  main_columns : ∀ c ∈ e.2.2.2.1.next_columns, c < e.1.main_width
  preprocessed_columns : ∀ c ∈ e.2.2.2.2.next_columns, c < e.1.preprocessed_width

/-- The suffix of the bound point an instance of arity h is evaluated at. -/
def suffix (red : ZerocheckReduction K) (h : ℕ) : List K := red.point.drop (red.tau.length - h)

/-- The instance's term, given its two next rows and its periodic values.

It is beta^i times its batched constraints, plus eta times its lookup link when it has one. -/
def term (red : ZerocheckReduction K) (e : Entry K) (bp : K) (next prep_next periodic : List K) : K :=
  let ci := e.1.eval (BoundaryEvals.at (suffix red e.2.2.1)) e.2.2.2.1.local_values next
    e.2.2.2.2.local_values prep_next periodic
  if e.1.linked then bp * ci.1 + red.eta * ci.2 else bp * ci.1

/-- The step of one well-formed instance.

It runs its four width checks, then its next rows, its periodic values and its term. -/
theorem checkAir_eq {red : ZerocheckReduction K} {e : Entry K} (he : AirOk red e)
    (hpt : red.point.length = red.tau.length) (bp : K) :
    checkAir red e.1 e.2.1 e.2.2.1 e.2.2.2.1 e.2.2.2.2 bp =
      if e.2.2.2.1.local_values.length ≠ e.1.main_width then
        some (.error (.OpeningCountMismatch e.1.main_width e.2.2.2.1.local_values.length))
      else if e.2.2.2.1.next_values.length ≠ e.2.2.2.1.next_columns.length then
        some (.error (.NextOpeningCountMismatch e.2.2.2.1.next_columns.length
          e.2.2.2.1.next_values.length))
      else if e.2.2.2.2.local_values.length ≠ e.1.preprocessed_width then
        some (.error (.PreprocessedOpeningCountMismatch e.1.preprocessed_width
          e.2.2.2.2.local_values.length))
      else if e.2.2.2.2.next_values.length ≠ e.2.2.2.2.next_columns.length then
        some (.error (.PreprocessedNextOpeningCountMismatch e.2.2.2.2.next_columns.length
          e.2.2.2.2.next_values.length))
      else
        match next_row e.2.2.2.1.next_columns e.2.2.2.1.next_values e.1.main_width,
          next_row e.2.2.2.2.next_columns e.2.2.2.2.next_values e.1.preprocessed_width with
        | some next, some prep_next =>
          match e.1.periodic (suffix red e.2.2.1) with
          | none => some (.error .Periodic)
          | some periodic => some (.ok (term red e bp next prep_next periodic, periodic))
        | _, _ => none := by
  obtain ⟨air, pv, h, main, prep⟩ := e
  have ha := he.arity
  have h1 : (air.main_width = 0) = False := eq_false he.width
  have h2 : (pv = air.num_public_values) = True := eq_true he.public_values
  have h3 : (red.tau.length < h) = False := eq_false (by simp only at ha; omega)
  have h4 : (red.point.length < red.tau.length - h) = False := eq_false (by omega)
  unfold checkAir term suffix
  simp only [h1, h2, h3, h4, ne_eq, not_true_eq_false, ↓reduceIte]
  split_ifs <;> try rfl

theorem checkAir_ne_none {red : ZerocheckReduction K} {e : Entry K} (he : AirOk red e)
    (hpt : red.point.length = red.tau.length) (bp : K) :
    checkAir red e.1 e.2.1 e.2.2.1 e.2.2.2.1 e.2.2.2.2 bp ≠ none := by
  rw [checkAir_eq he hpt]
  split_ifs with w1 w2 w3 w4 <;> try simp
  obtain ⟨n, hn⟩ := Option.isSome_iff_exists.mp (next_row_isSome (not_not.mp w2).symm he.main_columns)
  obtain ⟨q, hq⟩ := Option.isSome_iff_exists.mp
    (next_row_isSome (not_not.mp w4).symm he.preprocessed_columns)
  rw [hn, hq]
  rcases e.1.periodic (suffix red e.2.2.1) with _ | p <;> simp

/-- The instance's openings have the widths its AIR declares. -/
def WidthsMatch (e : Entry K) : Prop :=
  e.2.2.2.1.local_values.length = e.1.main_width ∧
  e.2.2.2.1.next_values.length = e.2.2.2.1.next_columns.length ∧
  e.2.2.2.2.local_values.length = e.1.preprocessed_width ∧
  e.2.2.2.2.next_values.length = e.2.2.2.2.next_columns.length

/-- **One instance accepted.**

An instance's step returns a term exactly when:

- its widths match
- its two next rows exist
- its periodic values fit.

The term is its folder value at the suffix of the point. -/
theorem checkAir_ok {red : ZerocheckReduction K} {e : Entry K} (he : AirOk red e)
    (hpt : red.point.length = red.tau.length) {bp t : K} {per : List K} :
    checkAir red e.1 e.2.1 e.2.2.1 e.2.2.2.1 e.2.2.2.2 bp = some (.ok (t, per)) ↔
      WidthsMatch e ∧ ∃ next prep_next,
        next_row e.2.2.2.1.next_columns e.2.2.2.1.next_values e.1.main_width = some next ∧
        next_row e.2.2.2.2.next_columns e.2.2.2.2.next_values e.1.preprocessed_width =
          some prep_next ∧
        e.1.periodic (suffix red e.2.2.1) = some per ∧ t = term red e bp next prep_next per := by
  rw [checkAir_eq he hpt, WidthsMatch]
  by_cases w1 : e.2.2.2.1.local_values.length = e.1.main_width
  swap; · simp [w1]
  by_cases w2 : e.2.2.2.1.next_values.length = e.2.2.2.1.next_columns.length
  swap; · simp [w1, w2]
  by_cases w3 : e.2.2.2.2.local_values.length = e.1.preprocessed_width
  swap; · simp [w1, w2, w3]
  by_cases w4 : e.2.2.2.2.next_values.length = e.2.2.2.2.next_columns.length
  swap; · simp [w1, w2, w3, w4]
  simp only [w1, w2, w3, w4, ne_eq, not_true_eq_false, ↓reduceIte, true_and]
  obtain ⟨n, hn⟩ := Option.isSome_iff_exists.mp (next_row_isSome w2.symm he.main_columns)
  obtain ⟨q, hq⟩ := Option.isSome_iff_exists.mp (next_row_isSome w4.symm he.preprocessed_columns)
  rw [hn, hq]
  rcases hp : e.1.periodic (suffix red e.2.2.1) with _ | p
  · simp
  · simp only [Option.some.injEq, Except.ok.injEq, Prod.mk.injEq]
    constructor
    · rintro ⟨rfl, rfl⟩; exact ⟨n, q, rfl, rfl, rfl, rfl⟩
    · rintro ⟨n', q', rfl, rfl, rfl, rfl⟩; exact ⟨rfl, rfl⟩

/-- **One instance rejected for its width.**

An instance whose current row has the wrong width is rejected with that width and that count. -/
theorem checkAir_width {red : ZerocheckReduction K} {e : Entry K} (he : AirOk red e)
    (hpt : red.point.length = red.tau.length) (bp : K)
    (hw : e.2.2.2.1.local_values.length ≠ e.1.main_width) :
    checkAir red e.1 e.2.1 e.2.2.1 e.2.2.2.1 e.2.2.2.2 bp =
      some (.error (.OpeningCountMismatch e.1.main_width e.2.2.2.1.local_values.length)) := by
  rw [checkAir_eq he hpt]; simp [hw]

theorem accumulate_ne_none {red : ZerocheckReduction K} (hpt : red.point.length = red.tau.length) :
    ∀ (l : List (Entry K)) (g bp : K), (∀ e ∈ l, AirOk red e) → accumulate red l g bp ≠ none
  | [], _, _, _ => by simp [accumulate]
  | e :: l, g, bp, hl => by
    obtain ⟨air, pv, h, main, prep⟩ := e
    have hc := checkAir_ne_none (hl _ List.mem_cons_self) hpt bp
    have ih := accumulate_ne_none hpt l
    simp only [accumulate]
    rcases hc' : checkAir red air pv h main prep bp with _ | e | ⟨t, per⟩
    · exact absurd hc' hc
    · simp
    · have := ih (g + t) (bp * red.beta) fun e he => hl e (List.mem_cons_of_mem _ he)
      simp only
      rcases hr : accumulate red l (g + t) (bp * red.beta) with _ | _ | _
      · exact absurd hr this
      · simp
      · simp

/-- **The loop accumulates.**

An accepted loop sums one term per instance.

Instance k's step is taken at beta^k times the starting power. -/
theorem accumulate_ok {red : ZerocheckReduction K} :
    ∀ (l : List (Entry K)) (g bp g' : K) (ps : List (List K)),
      accumulate red l g bp = some (.ok (g', ps)) →
      ∃ ts : List (K × List K), ts.length = l.length ∧ g' = g + (ts.map Prod.fst).sum ∧
        ps = ts.map Prod.snd ∧ ∀ k (hk : k < l.length) (hk' : k < ts.length),
          checkAir red l[k].1 l[k].2.1 l[k].2.2.1 l[k].2.2.2.1 l[k].2.2.2.2 (bp * red.beta ^ k) =
            some (.ok ts[k])
  | [], g, bp, g', ps, h => by
    simp only [accumulate, Option.some.injEq, Except.ok.injEq, Prod.mk.injEq] at h
    exact ⟨[], rfl, by simp [h.1], by simp [h.2], fun k hk => absurd hk (by simp)⟩
  | (air, pv, h, main, prep) :: l, g, bp, g', ps, hacc => by
    simp only [accumulate] at hacc
    rcases hc : checkAir red air pv h main prep bp with _ | e | ⟨t, per⟩ <;> rw [hc] at hacc
    · simp at hacc
    · simp at hacc
    · simp only at hacc
      rcases hr : accumulate red l (g + t) (bp * red.beta) with _ | e | ⟨g'', ps'⟩ <;>
        rw [hr] at hacc
      · simp at hacc
      · simp at hacc
      · simp only [Option.some.injEq, Except.ok.injEq, Prod.mk.injEq] at hacc
        obtain ⟨ts, hlen, hg, hps, hk⟩ := accumulate_ok l _ _ _ _ hr
        refine ⟨(t, per) :: ts, by simp [hlen], by simp [← hacc.1, hg]; ring,
          by simp [← hacc.2, hps], fun k hk1 hk2 => ?_⟩
        rcases k with _ | k
        · simpa using hc
        · have := hk k (by simpa using hk1) (by simpa using hk2)
          simpa [pow_succ, mul_assoc, mul_comm red.beta] using this

/-! ## The whole closing check -/

variable [DecidableEq K]

/-- What the caller guarantees:

- a nonempty batch
- one public-value count and one arity per AIR
- positive arities
- a bound point as long as tau
- every instance well formed. -/
structure StatementOk (airs : List (AirView K)) (pvs log_heights : List ℕ)
    (main prep : List (TableOpening K)) (red : ZerocheckReduction K) : Prop where
  nonempty : airs ≠ []
  pvs_length : airs.length = pvs.length
  heights_length : airs.length = log_heights.length
  positive : ∀ h ∈ log_heights, 0 < h
  point : red.point.length = red.tau.length
  instances : ∀ e ∈ entries airs pvs log_heights main prep, AirOk red e

/-- The closing check of a well-formed statement.

It checks the two opening counts, runs the loop, then compares. -/
theorem check_constraint_eq {airs : List (AirView K)} {pvs log_heights : List ℕ}
    {main prep : List (TableOpening K)} {red : ZerocheckReduction K}
    (hs : StatementOk airs pvs log_heights main prep red) (bus : Option (BusTerm K)) :
    check_constraint airs pvs log_heights main prep red bus =
      if main.length ≠ airs.length then some (.error (.OpeningCountMismatch airs.length main.length))
      else if prep.length ≠ airs.length then
        some (.error (.PreprocessedOpeningCountMismatch airs.length prep.length))
      else
        match accumulate red (entries airs pvs log_heights main prep) 0 1 with
        | none => none
        | some (.error e) => some (.error e)
        | some (.ok (g, periodics)) => closing red main prep bus g periodics := by
  have h1 : (airs = []) = False := eq_false hs.nonempty
  have h2 : (airs.length = pvs.length) = True := eq_true hs.pvs_length
  have h3 : (airs.length = log_heights.length) = True := eq_true hs.heights_length
  have h4 : (log_heights.all (0 < ·)) = true := List.all_eq_true.mpr fun h hh => by
    simpa using hs.positive h hh
  have h5 : (red.point.length = red.tau.length) = True := eq_true hs.point
  unfold check_constraint
  simp only [h1, h2, h3, h4, h5, ne_eq, not_true_eq_false, ↓reduceIte]
  rfl

/-- The comparison, once the bus value is known. -/
theorem closing_eq {red : ZerocheckReduction K} (hpt : red.point.length = red.tau.length)
    (main prep : List (TableOpening K)) (bus : Option (BusTerm K)) (g : K) (ps : List (List K)) :
    closing red main prep bus g ps =
      match bus with
      | none => if red.final_sum = Plonky3Lean.Spec.MultilinearUtil.eq red.tau red.point * g then
          some (.ok ()) else some (.error .FinalSumMismatch)
      | some f =>
        match f (main.map (·.local_values)) (prep.map (·.local_values)) ps with
        | .error _ => some (.error .BusBinding)
        | .ok b =>
          if red.final_sum = Plonky3Lean.Spec.MultilinearUtil.eq red.tau red.point * g +
            red.lambda * b then some (.ok ()) else some (.error .FinalSumMismatch) := by
  unfold closing
  simp only [eval_eq_self hpt.symm]
  rcases bus with _ | f
  · simp only [mul_zero, add_zero, ne_eq, ite_not]
  · simp only [ne_eq, ite_not]
    cases f (main.map (·.local_values)) (prep.map (·.local_values)) ps <;> rfl

/-- **The verifier never panics on openings.**

Given a well-formed statement, the closing check returns a verdict.

This holds for any openings, any bus family and any reduced sum. -/
theorem check_constraint_ne_none {airs : List (AirView K)} {pvs log_heights : List ℕ}
    {main prep : List (TableOpening K)} {red : ZerocheckReduction K}
    (hs : StatementOk airs pvs log_heights main prep red) (bus : Option (BusTerm K)) :
    check_constraint airs pvs log_heights main prep red bus ≠ none := by
  rw [check_constraint_eq hs]
  split_ifs <;> try simp
  have := accumulate_ne_none hs.point (entries airs pvs log_heights main prep) 0 1 hs.instances
  rcases hacc : accumulate red (entries airs pvs log_heights main prep) 0 1 with _ | _ | ⟨g, ps⟩
  · exact absurd hacc this
  · simp
  · simp only [closing_eq hs.point]
    rcases bus with _ | f
    · split_ifs <;> simp
    · simp only
      split
      · simp
      · split_ifs <;> simp

/-- **A wrong opening count is named.**

With more or fewer main openings than AIRs, the verdict is that count mismatch. -/
theorem check_constraint_main_count {airs : List (AirView K)} {pvs log_heights : List ℕ}
    {main prep : List (TableOpening K)} {red : ZerocheckReduction K}
    (hs : StatementOk airs pvs log_heights main prep red) (bus : Option (BusTerm K))
    (hm : main.length ≠ airs.length) :
    check_constraint airs pvs log_heights main prep red bus =
      some (.error (.OpeningCountMismatch airs.length main.length)) := by
  rw [check_constraint_eq hs]; simp [hm]

/-- **Acceptance implies the closing equation.**

An accepted closing check has:

- an accepted loop with value g
- a bus value b, zero without a bus
- a reduced sum equal to eq(tau, r) g + lambda b. -/
theorem check_constraint_accepts {airs : List (AirView K)} {pvs log_heights : List ℕ}
    {main prep : List (TableOpening K)} {red : ZerocheckReduction K}
    (hs : StatementOk airs pvs log_heights main prep red) {bus : Option (BusTerm K)}
    (h : check_constraint airs pvs log_heights main prep red bus = some (.ok ())) :
    ∃ g ps b, accumulate red (entries airs pvs log_heights main prep) 0 1 = some (.ok (g, ps)) ∧
      ((bus = none ∧ b = 0) ∨
        ∃ f, bus = some f ∧ f (main.map (·.local_values)) (prep.map (·.local_values)) ps = .ok b) ∧
      red.final_sum = Plonky3Lean.Spec.MultilinearUtil.eq red.tau red.point * g + red.lambda * b := by
  rw [check_constraint_eq hs] at h
  split_ifs at h with c1 c2
  · simp at h
  · simp at h
  rcases hacc : accumulate red (entries airs pvs log_heights main prep) 0 1 with _ | _ | ⟨g, ps⟩ <;>
    rw [hacc] at h
  · simp at h
  · simp at h
  · simp only [closing_eq hs.point] at h
    refine ⟨g, ps, ?_⟩
    rcases bus with _ | f
    · simp only at h
      split_ifs at h with hf
      · exact ⟨0, rfl, Or.inl ⟨rfl, rfl⟩, by simpa using hf⟩
      · simp at h
    · simp only at h
      rcases hf : f (main.map (·.local_values)) (prep.map (·.local_values)) ps with _ | b <;>
        rw [hf] at h
      · simp at h
      · simp only at h
        split_ifs at h with hfs
        · exact ⟨b, rfl, Or.inr ⟨f, rfl, hf⟩, hfs⟩
        · simp at h

/-- **Completeness of the closing check.**

The check accepts when it has:

- matching counts
- an accepted loop with value g
- a bus value b
- a reduced sum equal to eq(tau, r) g + lambda b. -/
theorem check_constraint_complete {airs : List (AirView K)} {pvs log_heights : List ℕ}
    {main prep : List (TableOpening K)} {red : ZerocheckReduction K}
    (hs : StatementOk airs pvs log_heights main prep red) {bus : Option (BusTerm K)}
    (hmain : main.length = airs.length) (hprep : prep.length = airs.length) {g b : K}
    {ps : List (List K)} (hacc : accumulate red (entries airs pvs log_heights main prep) 0 1 =
      some (.ok (g, ps)))
    (hbus : (bus = none ∧ b = 0) ∨
      ∃ f, bus = some f ∧ f (main.map (·.local_values)) (prep.map (·.local_values)) ps = .ok b)
    (hsum : red.final_sum =
      Plonky3Lean.Spec.MultilinearUtil.eq red.tau red.point * g + red.lambda * b) :
    check_constraint airs pvs log_heights main prep red bus = some (.ok ()) := by
  rw [check_constraint_eq hs]
  simp only [hmain, hprep, ne_eq, not_true_eq_false, ↓reduceIte, hacc, closing_eq hs.point]
  rcases hbus with ⟨rfl, rfl⟩ | ⟨f, rfl, hf⟩
  · simp [hsum]
  · simp [hf, hsum]

/-! ## The claim check -/

/-- **The claim check.**

The claim is accepted exactly when both hold:

- the bus output is not malformed
- the claim is eta times the lookup claim plus lambda times the bus claim.

With neither a lookup nor a bus, it is accepted exactly when it is zero. -/
theorem check_claimed_sum_ok {claimed : K} {lookup : Option K} {bus : Option (Except Unit K)}
    {eta lambda : K} :
    check_claimed_sum claimed lookup bus eta lambda = .ok () ↔
      (∀ e, bus ≠ some (.error e)) ∧
        claimed = (match lookup with | none => 0 | some l => eta * l) +
          lambda * (match bus with | some (.ok c) => c | _ => 0) := by
  unfold check_claimed_sum
  rcases lookup with _ | l <;> rcases bus with _ | (e | c) <;> by_cases hc : claimed = 0 <;>
    simp [hc] <;> tauto

end Plonky3Lean.Proofs.MultiStark
