module

public import P3MultiStark.Mirror.Transcript

@[expose] public section

/-!
# The statement transcript: what is bound before the first challenge

The statement's pattern splits in two:

```text
    preprocessed commitment?  main commitment  public values ...   |   delegations ...
```

Every challenge is drawn inside a delegation, so all three are absorbed before any of them.

The pattern and the instance label together determine the shape:

```text
    pattern  ->  the public-value counts, the bus, the indexed reduction, the preprocessed presence
    label    ->  the instance count, the difficulty, every arity, width and successor column
```

Take two statements that seed the sponge alike, up to a collision of the pattern's fingerprint.

They are the same statement.

The zerocheck's label alone determines its shape.
-/

namespace Plonky3Lean.Proofs.MultiStark

open p3_multi_stark.transcript.mirror

/-! ## The statement pattern -/

/-- The steps that bind the statement:

- the preprocessed commitment
- the main commitment's bracket
- one public-value step per instance. -/
def statementSteps (s : MultiStarkShape) : List Step :=
  (if s.has_preprocessed then [.PreprocessedCommitment] else []) ++ delegation .MainCommitment ++
    s.instances.map (fun i => .PublicValues i.num_public_values)

/-- The delegations, in the order the run performs them. -/
def delegationSteps (s : MultiStarkShape) : List Step :=
  (if s.has_bus then delegation .BusArgument else []) ++ delegation .LookupArgument ++
    delegation .Zerocheck ++ (if s.has_indexed then delegation .IndexedLookup else []) ++
    delegation .MainOpening ++ (if s.has_preprocessed then delegation .PreprocessedOpening else [])

theorem pattern_eq (s : MultiStarkShape) : s.pattern = statementSteps s ++ delegationSteps s := by
  simp [MultiStarkShape.pattern, statementSteps, delegationSteps, List.append_assoc]

/-- A marker of a delegation other than the main commitment, where challenges are drawn. -/
def isDelegationMarker : Step → Bool
  | .Begin d => d != .MainCommitment
  | .End d => d != .MainCommitment
  | _ => false

/-- A step that binds the statement: a commitment, the main commitment's bracket, or public values. -/
def isStatementStep : Step → Bool
  | .PreprocessedCommitment => true
  | .Begin .MainCommitment => true
  | .End .MainCommitment => true
  | .PublicValues _ => true
  | _ => false

/-- **Everything is bound before the first challenge.**

After the statement's commitments and public values, the pattern holds only delegation markers.

These mark delegations other than the main commitment.

Every challenge is drawn inside one of them. -/
theorem delegation_only (s : MultiStarkShape) : (delegationSteps s).all isDelegationMarker := by
  unfold delegationSteps
  split_ifs <;> decide

/-- The statement's own steps bind the statement and draw nothing. -/
theorem statement_steps (s : MultiStarkShape) : (statementSteps s).all isStatementStep := by
  unfold statementSteps
  split_ifs <;> simp [delegation, isStatementStep]

/-! ## The pattern and the label determine the shape -/

theorem columnWords_append_inj {c d : List ℕ} {r r' : List ℕ}
    (h : columnWords c ++ r = columnWords d ++ r') : c = d ∧ r = r' := by
  simp only [columnWords, List.cons_append, List.cons.injEq] at h
  exact List.append_inj h.2 h.1

theorem instanceWords_append_inj {a b : MultiStarkInstanceShape} {r r' : List ℕ}
    (h : instanceWords a ++ r = instanceWords b ++ r') :
    a.num_variables = b.num_variables ∧ a.main_width = b.main_width ∧
      a.preprocessed_width = b.preprocessed_width ∧
      a.main_next_row_columns = b.main_next_row_columns ∧
      a.preprocessed_next_row_columns = b.preprocessed_next_row_columns ∧ r = r' := by
  simp only [instanceWords, List.append_assoc, List.cons_append, List.nil_append,
    List.cons.injEq] at h
  obtain ⟨h1, h2, h3, h⟩ := h
  obtain ⟨h4, h⟩ := columnWords_append_inj h
  obtain ⟨h5, h⟩ := columnWords_append_inj h
  exact ⟨h1, h2, h3, h4, h5, h⟩

/-- Instances with the same words and the same public-value counts are the same instances. -/
theorem flatMap_instanceWords_inj : ∀ {as bs : List MultiStarkInstanceShape},
    as.length = bs.length → as.flatMap instanceWords = bs.flatMap instanceWords →
    as.map (·.num_public_values) = bs.map (·.num_public_values) → as = bs
  | [], [], _, _, _ => rfl
  | a :: as, b :: bs, hl, hw, hp => by
    simp only [List.flatMap_cons, List.map_cons, List.cons.injEq, List.length_cons,
      Nat.add_right_cancel_iff] at hl hw hp
    obtain ⟨h1, h2, h3, h4, h5, hr⟩ := instanceWords_append_inj hw
    have : a = b := by cases a; cases b; simp_all
    rw [this, flatMap_instanceWords_inj hl hr hp.2]

theorem has_bus_iff (s : MultiStarkShape) :
    s.has_bus = true ↔ Step.Begin .BusArgument ∈ s.pattern := by
  unfold MultiStarkShape.pattern
  generalize s.has_preprocessed = p
  generalize s.has_indexed = x
  generalize s.has_bus = b
  cases p <;> cases x <;> cases b <;> simp [delegation]

theorem has_indexed_iff (s : MultiStarkShape) :
    s.has_indexed = true ↔ Step.Begin .IndexedLookup ∈ s.pattern := by
  unfold MultiStarkShape.pattern
  generalize s.has_preprocessed = p
  generalize s.has_indexed = x
  generalize s.has_bus = b
  cases p <;> cases x <;> cases b <;> simp [delegation]

/-- The public-value counts, read back off the pattern. -/
def publicCounts (p : List Step) : List ℕ :=
  p.filterMap fun st => match st with | .PublicValues c => some c | _ => none

theorem publicCounts_pattern (s : MultiStarkShape) :
    publicCounts s.pattern = s.instances.map (·.num_public_values) := by
  simp only [publicCounts, MultiStarkShape.pattern, delegation, List.filterMap_append]
  split_ifs <;> simp [List.filterMap_map]

/-- **The statement seed binds the shape.**

Two shapes with the same pattern and the same instance label are equal. -/
theorem shape_injective {s t : MultiStarkShape} (hp : s.pattern = t.pattern) (hl : s.label = t.label) :
    s = t := by
  simp only [MultiStarkShape.label, List.cons_append, List.nil_append, List.cons.injEq] at hl
  obtain ⟨hn, hpow, hw⟩ := hl
  have hi := flatMap_instanceWords_inj hn hw (by rw [← publicCounts_pattern, hp, publicCounts_pattern])
  have hb : s.has_bus = t.has_bus := Bool.eq_iff_iff.mpr (by rw [has_bus_iff, has_bus_iff, hp])
  have hx : s.has_indexed = t.has_indexed :=
    Bool.eq_iff_iff.mpr (by rw [has_indexed_iff, has_indexed_iff, hp])
  cases s; cases t; simp_all

/-! ## The zerocheck pattern -/

/-- **The zerocheck draws everything before its sumcheck.**

Alpha, beta, eta, lambda and the free coordinates come first.

The sumcheck's bracket comes last. -/
theorem zerocheck_pattern_eq (s : ZerocheckShape) :
    ∃ challenges, s.pattern = challenges ++ [.BeginSumcheck, .EndSumcheck] ∧
      .BeginSumcheck ∉ challenges ∧ .EndSumcheck ∉ challenges := by
  refine ⟨[.Alpha, .Beta] ++ (if s.lookup_point_len > 0 then [.Eta] else []) ++
    (if s.bus_degree.isSome then [.BusBatching] else []) ++
    (if s.free_coordinates > 0 then [.Tau s.free_coordinates] else []), rfl, ?_, ?_⟩ <;>
    split_ifs <;> simp

theorem flatMap_degrees_inj : ∀ {as bs : List AirDegrees} {r r' : List ℕ}, as.length = bs.length →
    as.flatMap (fun d => [d.constraints, d.interactions]) ++ r =
      bs.flatMap (fun d => [d.constraints, d.interactions]) ++ r' → as = bs ∧ r = r'
  | [], [], _, _, _, h => ⟨rfl, by simpa using h⟩
  | a :: as, b :: bs, _, _, hl, h => by
    simp only [List.flatMap_cons, List.cons_append, List.nil_append,
      List.cons.injEq, List.length_cons, Nat.add_right_cancel_iff] at hl h
    obtain ⟨h1, h2, h⟩ := h
    obtain ⟨h3, h4⟩ := flatMap_degrees_inj hl h
    exact ⟨by cases a; cases b; simp_all, h4⟩

/-- **The zerocheck seed binds its shape.**

Two zerocheck shapes with the same instance label are equal. -/
theorem zerocheck_shape_injective {s t : ZerocheckShape} (hl : s.label = t.label) : s = t := by
  simp only [ZerocheckShape.label, List.cons_append, List.nil_append, List.cons.injEq] at hl
  obtain ⟨h1, h2, h3, h4, h⟩ := hl
  obtain ⟨hd, hb⟩ := flatMap_degrees_inj h4 h
  have : s.bus_degree = t.bus_degree := by
    cases hs : s.bus_degree <;> cases ht : t.bus_degree <;> simp_all
  cases s; cases t; simp_all

/-- The free coordinates are the cube's variables the lookup tail leaves. -/
theorem free_add_tail (s : ZerocheckShape) (h : s.lookup_point_len ≤ s.log_height) :
    s.free_coordinates + s.lookup_point_len = s.log_height := by
  simp only [ZerocheckShape.free_coordinates]; omega

end Plonky3Lean.Proofs.MultiStark
