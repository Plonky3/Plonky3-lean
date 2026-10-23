module

public import P3Bus
public import Mathlib.Data.Nat.Size
public import Mathlib.Data.Nat.Log
public import Mathlib.Algebra.Field.Basic
public import Plonky3Lean.Proofs.Bus.Product

@[expose] public section

/-!
# The tuple layout of a plan

A plan pads every tuple to one width:

```text
    [ payload 0 .. w )  [ zero w .. p )  [ identity bits p .. p + d )  [ zero .. 2^m )
```

The identity of the i-th bus in name order is i + 1, and d = ceil(log_2(n + 1)) bits hold every identity.

So two declarations produce the same padded tuple only when they name the same bus and carry the same payload.
-/

namespace Plonky3Lean.Proofs.Bus

open p3_bus.plan.mirror p3_bus.mirror p3_bus.product.mirror

set_option linter.unusedSectionVars false

/-- What the planner guarantees about a plan's tuple layout. -/
structure LayoutWF (p : BusPlan) : Prop where
  identity : ∀ i (h : i < p.domains.length), p.domains[i].identity = i + 1
  bits : p.domains.length < 2 ^ p.domain_slots
  slots : p.domain_slots ≤ 64
  width : ∀ d ∈ p.domains, d.payload_width ≤ p.payload_slots
  logical : p.logical_tuple_width = p.payload_slots + p.domain_slots
  fingerprint : p.logical_tuple_width ≤ p.fingerprint_width
  pow : p.fingerprint_width = 2 ^ p.geometry.tuple_variables

/-- The value of one slot: a payload entry, an identity bit, or zero. -/
def slotValue {F : Type _} [Zero F] [One F] (payload : List F) : Option BusTupleSlot → F
  | some (.Payload i) => payload.getD i 0
  | some (.DomainBit bit) => if bit then 1 else 0
  | _ => 0

/-- The padded tuple of a declaration on bus b with this payload, as the fingerprint reads it. -/
def tupleOf {F : Type _} [Zero F] [One F] (p : BusPlan) (b : ℕ) (payload : List F) : List F :=
  (List.range p.fingerprint_width).map fun slot => slotValue payload (p.tuple_slot b slot)

theorem tuple_slot_payload {p : BusPlan} {b slot : ℕ} (hb : b < p.domains.length)
    (hw : p.domains[b].payload_width ≤ p.fingerprint_width) (hs : slot < p.domains[b].payload_width) :
    p.tuple_slot b slot = some (.Payload slot) := by
  unfold BusPlan.tuple_slot
  simp [List.getElem?_eq_getElem hb, hs, show ¬ p.fingerprint_width ≤ slot by omega]

theorem tuple_slot_bit {p : BusPlan} (hp : LayoutWF p) {b k : ℕ} (hb : b < p.domains.length)
    (hk : k < p.domain_slots) :
    p.tuple_slot b (p.payload_slots + k) = some (.DomainBit (p.domains[b].identity_bit k)) := by
  have hw := hp.width _ (List.getElem_mem hb)
  have hl := hp.logical
  have hf := hp.fingerprint
  unfold BusPlan.tuple_slot
  simp [List.getElem?_eq_getElem hb, show ¬ p.fingerprint_width ≤ p.payload_slots + k by omega,
    show ¬ p.payload_slots + k < p.domains[b].payload_width by omega,
    show p.payload_slots + k < p.logical_tuple_width by omega]

/-- **The layout is injective.** On a valid plan, a padded tuple determines its bus and, given the bus's width, its payload. -/
theorem tupleOf_injective {F : Type _} [Field F] {p : BusPlan} (hp : LayoutWF p) {b b' : ℕ}
    (hb : b < p.domains.length) (hb' : b' < p.domains.length) {x y : List F}
    (hx : x.length = p.domains[b].payload_width) (hy : y.length = p.domains[b'].payload_width)
    (h : tupleOf p b x = tupleOf p b' y) : b = b' ∧ x = y := by
  have hentry : ∀ slot, slot < p.fingerprint_width →
      slotValue x (p.tuple_slot b slot) = slotValue y (p.tuple_slot b' slot) := fun slot hs => by
    have := congrArg (fun l : List F => l.getD slot 0) h
    simpa [tupleOf, List.getD_eq_getElem?_getD, hs] using this
  -- Distinct buses differ in an identity bit below the reserved width.
  have hbus : b = b' := by
    by_contra hne
    have hid : p.domains[b].identity ≠ p.domains[b'].identity := by
      rw [hp.identity b hb, hp.identity b' hb']; omega
    obtain ⟨k, hk, hbit⟩ : ∃ k < p.domain_slots,
        p.domains[b].identity_bit k ≠ p.domains[b'].identity_bit k := by
      by_contra hall
      simp only [not_exists, not_and, not_not] at hall
      apply hid
      have h1 : p.domains[b].identity < 2 ^ p.domain_slots := by
        rw [hp.identity b hb]; have := hp.bits; omega
      have h2 : p.domains[b'].identity < 2 ^ p.domain_slots := by
        rw [hp.identity b' hb']; have := hp.bits; omega
      refine Nat.eq_of_testBit_eq fun j => ?_
      by_cases hj : j < p.domain_slots
      · have := hall j hj
        simp only [BusDomain.identity_bit, show j < 64 by have := hp.slots; omega, decide_true,
          Bool.true_and] at this
        rw [Nat.testBit, Nat.testBit]
        simp only [Nat.shiftRight_eq_div_pow, Nat.one_and_eq_mod_two] at this ⊢
        rcases Nat.mod_two_eq_zero_or_one (p.domains[b].identity / 2 ^ j) with e | e <;>
        rcases Nat.mod_two_eq_zero_or_one (p.domains[b'].identity / 2 ^ j) with e' | e' <;>
          simp_all
      · rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le h1 (Nat.pow_le_pow_right two_pos (by omega))),
          Nat.testBit_lt_two_pow (lt_of_lt_of_le h2 (Nat.pow_le_pow_right two_pos (by omega)))]
    have := hentry (p.payload_slots + k) (by have := hp.logical; have := hp.fingerprint; omega)
    rw [tuple_slot_bit hp hb hk, tuple_slot_bit hp hb' hk] at this
    revert this hbit
    cases p.domains[b].identity_bit k <;> cases p.domains[b'].identity_bit k <;> simp [slotValue]
  subst hbus
  refine ⟨rfl, List.ext_getElem (by rw [hx, hy]) fun i hi _ => ?_⟩
  have hw := hp.width _ (List.getElem_mem hb)
  have := hentry i (by have := hp.logical; have := hp.fingerprint; omega)
  rw [tuple_slot_payload hb (by have := hp.logical; have := hp.fingerprint; omega) (by omega)] at this
  simpa [slotValue, List.getD_eq_getElem?_getD, hi, show i < y.length by omega] using this

theorem except_bind_ok {ε α β : Type _} {x : Except ε α} {f : α → Except ε β} {v : β}
    (h : (x >>= f) = .ok v) : ∃ a, x = .ok a ∧ f a = .ok v := by
  cases x with
  | error e => cases h
  | ok a => exact ⟨a, rfl, h⟩

/-- **The planner's layout.** A plan the planner returns satisfies the layout invariants. -/
theorem build_wf {F : Type _} {inputs : List (BusPlanInput F)} {p : BusPlan}
    (h : BusPlan.build inputs = .ok (some p)) : LayoutWF p := by
  unfold BusPlan.build at h
  split at h
  case h_2 => cases h
  split_ifs at h with h0
  · cases h
  obtain ⟨widths, -, h⟩ := except_bind_ok h
  dsimp only at h
  split at h
  case h_2 => cases h
  rename_i identity_limit hil
  split at h
  case h_2 => cases h
  rename_i logical hlog
  split at h
  case h_2 => cases h
  rename_i fingerprint hfp
  obtain ⟨⟨pushes, pulls, pc, qc⟩, -, h⟩ := except_bind_ok h
  dsimp only at h
  split at h
  case h_2 => cases h
  split at h
  case h_2 => cases h
  injection h with h
  injection h with h
  subst h
  set sorted := widths.mergeSort fun a b => decide (a.1 ≤ b.1)
  have hil' : identity_limit = sorted.length + 1 := by
    unfold checked_add at hil; split_ifs at hil; exact (Option.some.inj hil).symm
  have hlog' : logical = (sorted.map (·.2)).foldl max 0 + log2_ceil_usize identity_limit := by
    unfold checked_add at hlog; split_ifs at hlog; exact (Option.some.inj hlog).symm
  have hlt : identity_limit < 2 ^ 64 := by
    unfold checked_add at hil; split_ifs at hil with hh; rw [hil']; exact hh
  have hfp' : logical ≤ fingerprint := by
    unfold checked_next_power_of_two at hfp; split_ifs at hfp
    rw [← Option.some.inj hfp]; exact Nat.le_pow_clog one_lt_two _
  have hpow : fingerprint = 2 ^ fingerprint.log2 := by
    unfold checked_next_power_of_two at hfp; split_ifs at hfp
    rw [← Option.some.inj hfp, Nat.log2_two_pow]
  have hge : ∀ (l : List ℕ) (a : ℕ), a ≤ l.foldl max a := by
    intro l; induction l with
    | nil => simp
    | cons y l ih => intro a; exact le_trans (le_max_left a y) (ih _)
  have hmax : ∀ (l : List ℕ) (a : ℕ), ∀ x ∈ l, x ≤ l.foldl max a := by
    intro l; induction l with
    | nil => simp
    | cons y l ih =>
      intro a x hx
      rcases List.mem_cons.1 hx with rfl | hx
      · exact le_trans (le_max_right a x) (hge l _)
      · exact ih _ x hx
  refine ⟨fun i hi => by simp, ?_, ?_, fun d hd => ?_, hlog', hfp', hpow⟩
  · simp only [List.length_map, List.length_zipIdx, log2_ceil_usize, hil', Nat.add_sub_cancel]
    exact Nat.lt_size_self _
  · simp only [log2_ceil_usize, hil', Nat.add_sub_cancel]
    exact Nat.size_le.2 (by omega)
  · simp only [List.mem_map, List.mem_zipIdx_iff_getElem?] at hd
    obtain ⟨⟨⟨nm, w⟩, i⟩, hmem, rfl⟩ := hd
    exact hmax _ 0 _ (List.mem_map.2 ⟨(nm, w), List.mem_of_getElem? hmem, rfl⟩)

/-- Lists whose images permute under a map injective on their entries permute themselves. -/
theorem perm_of_map_perm {α β : Type _} [DecidableEq α] [DecidableEq β] {f : α → β}
    {l₁ l₂ : List α} (hinj : ∀ a ∈ l₁ ++ l₂, ∀ b ∈ l₁ ++ l₂, f a = f b → a = b)
    (h : (l₁.map f).Perm (l₂.map f)) : l₁.Perm l₂ := by
  rw [List.perm_iff_count] at h ⊢
  intro a
  by_cases ha : a ∈ l₁ ++ l₂
  · have hc : ∀ l : List α, (∀ x ∈ l, x ∈ l₁ ++ l₂) → l.count a = (l.map f).count (f a) := by
      intro l hl
      rw [List.count, List.count, List.countP_map]
      exact List.countP_congr fun x hx => by
        simp only [Function.comp, beq_iff_eq]
        exact ⟨fun h => h ▸ rfl, fun h => hinj x (hl x hx) a ha h⟩
    rw [hc l₁ (fun x hx => List.mem_append_left _ hx), hc l₂ (fun x hx => List.mem_append_right _ hx),
      h]
  · rw [List.count_eq_zero_of_not_mem (fun h => ha (List.mem_append_left _ h)),
      List.count_eq_zero_of_not_mem (fun h => ha (List.mem_append_right _ h))]

theorem length_tupleOf {F : Type _} [Zero F] [One F] (p : BusPlan) (b : ℕ) (x : List F) :
    (tupleOf p b x).length = p.fingerprint_width := by simp [tupleOf]

/-- A declaration a plan accepts: a bus of the plan, and a payload of that bus's width. -/
def Fits {F : Type _} (p : BusPlan) (d : ℕ × List F) : Prop :=
  ∃ h : d.1 < p.domains.length, d.2.length = (p.domains[d.1]'h).payload_width

/-- **Soundness of the bus.** On a plan the planner returns, if the pushed declarations are not a permutation of the pulled ones, their grand products over the padded tuples agree on at most max(1, m) N |K|^m of the |K|^(m + 1) pairs of an offset and a point.

Here m is the number of tuple variables and N bounds both sides. -/
theorem bus_soundness {K : Type _} [Field K] [Fintype K] [DecidableEq K] {p : BusPlan}
    (hp : LayoutWF p) {push pull : List (ℕ × List K)} (hpush : ∀ d ∈ push, Fits p d)
    (hpull : ∀ d ∈ pull, Fits p d) (hperm : ¬ push.Perm pull) {N : ℕ} (hN : push.length ≤ N)
    (hN' : pull.length ≤ N) :
    Finset.card {x : K × (Fin p.geometry.tuple_variables → K) |
      Plonky3Lean.Spec.Bus.grandProduct x.1 (List.ofFn x.2) (push.map fun d => tupleOf p d.1 d.2) =
        Plonky3Lean.Spec.Bus.grandProduct x.1 (List.ofFn x.2) (pull.map fun d => tupleOf p d.1 d.2)}
      ≤ max 1 p.geometry.tuple_variables * N * Fintype.card K ^ p.geometry.tuple_variables := by
  refine card_bad_challenges_le (fun t ht => ?_) (fun t ht => ?_) (fun h => hperm ?_)
    (by simpa using hN) (by simpa using hN')
  · obtain ⟨d, -, rfl⟩ := List.mem_map.1 ht; rw [length_tupleOf, hp.pow]
  · obtain ⟨d, -, rfl⟩ := List.mem_map.1 ht; rw [length_tupleOf, hp.pow]
  -- On fitting declarations the layout is injective, so tuples permute exactly when declarations do.
  have hinj : ∀ d ∈ push ++ pull, ∀ d' ∈ push ++ pull,
      tupleOf p d.1 d.2 = tupleOf p d'.1 d'.2 → d = d' := fun d hd d' hd' he => by
    obtain ⟨hb, hx⟩ : Fits p d := by
      rcases List.mem_append.1 hd with h | h; exacts [hpush d h, hpull d h]
    obtain ⟨hb', hy⟩ : Fits p d' := by
      rcases List.mem_append.1 hd' with h | h; exacts [hpush d' h, hpull d' h]
    obtain ⟨h1, h2⟩ := tupleOf_injective hp hb hb' hx hy he
    exact Prod.ext h1 h2
  exact perm_of_map_perm hinj (by simpa using h)

end Plonky3Lean.Proofs.Bus
