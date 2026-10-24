module

public import Plonky3Lean.Proofs.Lookup.Periodic

@[expose] public section

/-!
# Challenges, counts, buses, weights and the height bound

The challenge table, the signed counts and the typed buses do what their names say.

The weights of a lookup are summed exactly, and an overflow panics.

The height bound accepts exactly when the weighted height sum is below the characteristic.
-/

namespace Plonky3Lean.Proofs.Lookup

open p3_lookup.mirror Finset

set_option linter.unusedSectionVars false

/-! ## The terminal check -/

/-- The cross-AIR check accepts exactly when the present terminals sum to zero. -/
theorem verify_terminal_sum_iff {K : Type} [Field K] [DecidableEq K] (t : List (Option K)) :
    verify_terminal_sum t = true ↔ (t.filterMap id).sum = 0 := by
  simp [verify_terminal_sum]

/-! ## Challenges -/

theorem foldl_prefix {K : Type _} [Field K] (α γ : K) (n : ℕ) :
    (List.range n).foldl (fun (st : K × List K) _ => (st.1 + γ, st.2 ++ [st.1 + γ])) (α, []) =
      (α + n * γ, (List.range n).map fun i : ℕ => α + ((i : K) + 1) * γ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.foldl_append, ih]
    simp; ring

/-- **The challenge table.**

A width of 0 panics.

Otherwise bus i gets alpha + (i + 1) beta^W. -/
theorem challenges_new {K : Type _} [Field K] (α β : K) (W n : ℕ) :
    Challenges.new α β W n =
      if W = 0 then none else
        some (α, β, (List.range n).map fun i : ℕ => α + ((i : K) + 1) * β ^ W) := by
  unfold Challenges.new
  by_cases hW : W = 0
  · simp [hW]
  · simp only [hW, ite_false, show W > 0 by omega, not_true_eq_false, foldl_prefix]; rfl

/-! ## Counts and buses -/

variable {E : Type _}

/-- A constant count is bounded by its absolute value. -/
theorem count_from_weight {F : Type _} [Ring F] (c : ℤ) : (Count.from_i32 (F := F) c).2 = c.natAbs :=
  rfl

/-- Swapping send and receive keeps the bound. -/
theorem count_neg_weight (neg : E → E) (c : E × ℕ) : (Count.neg neg c).2 = c.2 := rfl

/-- A provided table entry has weight 0 and the negated count. -/
theorem table_entry_records (neg : E → E) (bus : String) (r : Recorded E) (key : List E)
    (n : E) : (LookupBus.table_entry neg bus r key n).global = r.global ++ [(bus, key, (neg n, 0))] :=
  rfl

/-- A receive records the negated count with the same weight. -/
theorem receive_records (neg : E → E) (bus : String) (r : Recorded E) (fields : List E)
    (c : E × ℕ) :
    (PermutationCheckBus.receive neg bus r fields c).global = r.global ++ [(bus, fields, (neg c.1, c.2))] :=
  rfl

/-- Each exclusive branch is a unit query of weight 1. -/
theorem lookup_key_exclusive_records (one : E) (bus : String) (r : Recorded E)
    (branches : List (E × List E)) :
    (LookupBus.lookup_key_exclusive one bus r branches).exclusive =
      r.exclusive ++ [(bus, branches.map fun b => (b.1, (one, 1), b.2))] := rfl

/-! ## Weights -/

theorem foldlM_checked_add (ws : List ℕ) (a : ℕ) (ha : a ≤ U32_MAX) :
    ws.foldlM (fun acc w => checked_add_u32 acc w) a =
      if a + ws.sum ≤ U32_MAX then some (a + ws.sum) else none := by
  induction ws generalizing a with
  | nil => simp [ha]
  | cons w ws ih =>
    rw [List.foldlM_cons, List.sum_cons]
    by_cases h1 : a + w ≤ U32_MAX
    · rw [show checked_add_u32 a w = some (a + w) by simp [checked_add_u32, h1]]
      simp only [Option.bind_eq_bind, Option.bind_some]
      rw [ih _ h1, add_assoc]
    · rw [show checked_add_u32 a w = none by simp [checked_add_u32, h1]]
      simp only [Option.bind_eq_bind, Option.bind_none]
      rw [ite_eq_right_iff.2 (fun h => absurd h (by omega))]

/-- **The local weight is summed exactly.**

A local lookup's weight is the sum of its tuples' weights.

A sum above 2^32 - 1 panics rather than clamps. -/
theorem local_weight {F : Type} (i : SymbolicLocalInteraction F) :
    i.tuples.foldlM (fun acc t => checked_add_u32 acc t.2.2) 0 =
      if (i.tuples.map (·.2.2)).sum ≤ U32_MAX then some (i.tuples.map (·.2.2)).sum else none := by
  have := foldlM_checked_add (i.tuples.map (·.2.2)) 0 (Nat.zero_le _)
  simp only [List.foldlM_map, zero_add] at this
  exact this

/-! ## The height bound -/

/-- **The height bound.**

Unequal lengths panic.

Otherwise it accepts exactly when sum_i w_i h_i < p. -/
theorem check_multiplicity_height_bound_iff {F : Type} (p : ℕ) (lookups : List (List (Lookup F)))
    (heights : List ℕ) (h : lookups.length = heights.length) :
    check_multiplicity_height_bound p lookups heights = some (.ok ()) ↔
      ((lookups.zip heights).map fun x => total_count_weight x.1 * x.2).sum < p := by
  unfold check_multiplicity_height_bound
  simp only [h, ne_eq, not_true_eq_false, ite_false, Option.bind_eq_bind, Option.pure_def]
  split_ifs with hp <;> simp [hp]
  omega

/-- Unequal lengths panic. -/
theorem check_multiplicity_height_bound_panics {F : Type} (p : ℕ) (lookups : List (List (Lookup F)))
    (heights : List ℕ) : check_multiplicity_height_bound p lookups heights = none ↔
      lookups.length ≠ heights.length := by
  unfold check_multiplicity_height_bound
  split_ifs with h <;> simp [h]

end Plonky3Lean.Proofs.Lookup
