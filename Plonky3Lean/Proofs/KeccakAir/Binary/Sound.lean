module

public import Plonky3Lean.Proofs.KeccakAir.Binary.Row
public import Plonky3Lean.Proofs.KeccakAir.Sound

@[expose] public section

/-!
# Soundness of the characteristic-2 Keccak-f AIR

Let a trace of n rows satisfy the AIR over a field of characteristic 2, with every state cell a bit.

The AIR states the booleanity, or leaves it to the commitment.

* Every row is one-hot: a round r < 24, or an output row.
* A round-r row is followed by round r + 1, for r < 23.
* Round 23 and an output row are followed by round 0 or an output row.
* The next row's state is Rnd(A, r) of a round-r row's state A.

So from a round-0 row, the state 24 rows later, with indices modulo n, is Keccak-f[1600] of its state.
-/

set_option linter.unusedSectionVars false

namespace Plonky3Lean.Proofs.KeccakAir.Binary

open p3_air.builder.mirror p3_air.air.mirror p3_keccak_air.mirror p3_keccak_air.mirror.binary
open Plonky3Lean.Spec.Air Plonky3Lean.Spec.Keccak Plonky3Lean.Proofs.Air Plonky3Lean.Proofs.KeccakAir

variable {F : Type} [Field F] [DecidableEq F]

/-! ## Bits in characteristic 2 -/

section char2

variable (h2 : (2 : F) = 0)
include h2

theorem add_eq_zero_iff_eq {a b : F} : a + b = 0 ↔ a = b := by
  have : b + b = 0 := by rw [← two_mul, h2, zero_mul]
  constructor
  · intro h; linear_combination h - this
  · intro h; subst h; exact this

theorem char2_solve {a n r : F} (h : a + n + r = 0) : n = a + r := by
  linear_combination h - (a + r) * h2

theorem bitF_add (a b : Bool) : (bitF a : F) + bitF b = bitF (a ^^ b) := by
  cases a <;> cases b <;> simp [bitF, one_add_one_eq_two, h2]

theorem one_add_bitF_mul (a b : Bool) : (1 + bitF a : F) * bitF b = bitF (!a && b) := by
  cases a <;> cases b <;> simp [bitF, one_add_one_eq_two, h2]

end char2

/-! ## The trace -/

section trace

variable {cb : Bool} {T : Instance F}

/-- Row i of a trace, as the row builder reads it for the characteristic-2 AIR. -/
def curB (cb : Bool) (T : Instance F) (i : ℕ) : ℕ → F :=
  rowOf (rowEnv T i) (AirLayout.from_air (binaryAir (F := F) cb)) 0

theorem rowOf_next_mod (i : ℕ) :
    rowOf (rowEnv T i) (AirLayout.from_air (binaryAir (F := F) cb)) 1 = curB cb T ((i + 1) % T.height) := by
  funext c; rfl

theorem rowSpecB_of_satisfies (hT : Satisfies (constraints (binaryAir cb)) T) {i : ℕ}
    (hi : i < T.height) :
    RowSpecB cb (curB cb T i) (curB cb T ((i + 1) % T.height)) (if i = 0 then 1 else 0) := by
  rw [← rowOf_next_mod]
  exact (eval_iff cb _ _).mp ((satisfies_iff_rows (binaryAir cb) T).mp hT i hi)

/-- The flags of a row are one-hot at k. -/
def OneHot (f : ℕ → F) (k : ℕ) : Prop := ∀ r < 25, f (col.round_flags r) = if r = k then 1 else 0

/-- One-hot flags at k are followed by k + 1 for k < 23, and by 0 or 24 for k = 23 or 24. -/
theorem onehot_next (h2 : (2 : F) = 0) {loc nxt nxt' : ℕ → F} {first first' : F} {k : ℕ}
    (hR : RowSpecB cb loc nxt first) (hR' : RowSpecB cb nxt nxt' first') (hk : k < 25)
    (hf : OneHot loc k) :
    (k < 23 → OneHot nxt (k + 1)) ∧ (23 ≤ k → OneHot nxt 0 ∨ OneHot nxt 24) := by
  have hmid : ∀ r < 23, nxt (col.round_flags (r + 1)) = if r = k then 1 else 0 := fun r hr => by
    rw [← hf r (by omega)]
    exact (add_eq_zero_iff_eq h2).mp (hR.step r hr)
  have hw := hR.wrap
  rw [hf 23 (by omega), hf 24 (by omega)] at hw
  have hx := hR'.excl
  refine ⟨fun hk23 => ?_, fun hk23 => ?_⟩
  · have h0 : nxt (col.round_flags 0) = nxt (col.round_flags 24) := by
      rw [ite_eq_right (by omega), ite_eq_right (by omega), add_zero, add_zero] at hw
      exact (add_eq_zero_iff_eq h2).mp hw
    rw [h0, mul_self_eq_zero] at hx
    intro r hr
    rcases r with _ | r
    · rw [h0, hx]; simp
    · by_cases hr' : r < 23
      · rw [hmid r hr']; simp
      · obtain rfl : r = 23 := by omega
        rw [hx]; simp; omega
  · have hs : nxt (col.round_flags 0) + nxt (col.round_flags 24) = 1 := by
      have h1 : ((if 23 = k then (1 : F) else 0) + if 24 = k then 1 else 0) = 1 := by
        rcases (by omega : k = 23 ∨ k = 24) with rfl | rfl <;> simp
      rw [add_assoc _ (if 23 = k then (1 : F) else 0), h1] at hw
      exact (add_eq_zero_iff_eq h2).mp hw
    have h24 : nxt (col.round_flags 24) = 1 - nxt (col.round_flags 0) := by linear_combination hs
    rw [h24] at hx
    have hmid' : ∀ r < 23, nxt (col.round_flags (r + 1)) = 0 := fun r hr => by
      rw [hmid r hr, ite_eq_right (by omega)]
    rcases mul_eq_zero.mp hx with h0 | h0
    · right
      intro r hr
      rcases r with _ | r
      · rw [h0]; simp
      · by_cases hr' : r < 23
        · rw [hmid' r hr']; simp; omega
        · obtain rfl : r = 23 := by omega
          rw [h24, h0]; simp
    · left
      have h1 : nxt (col.round_flags 0) = 1 := by linear_combination -h0
      intro r hr
      rcases r with _ | r
      · rw [h1]; simp
      · by_cases hr' : r < 23
        · rw [hmid' r hr']; simp
        · obtain rfl : r = 23 := by omega
          rw [h24, h1]; simp

end trace

/-! ## One row computes one round -/

/-- The state a row holds. -/
def stateOf (loc : ℕ → F) : State := fun x y z => bv (loc (binary.col.a y.val x.val z.val))

section round

variable (h2 : (2 : F) = 0) {loc nxt : ℕ → F}
  (hb : ∀ y < 5, ∀ x < 5, ∀ z < 64, loc (binary.col.a y x z) * (loc (binary.col.a y x z) - 1) = 0)
include h2 hb

theorem loc_a (x y : Fin 5) (z : Fin 64) :
    loc (binary.col.a y.val x.val z.val) = bitF (stateOf loc x y z) :=
  eq_bitF (hb _ y.isLt _ x.isLt _ z.isLt)

theorem loc_a' {x y z : ℕ} (hx : x < 5) (hy : y < 5) (hz : z < 64) :
    loc (binary.col.a y x z) = bitF (stateOf loc ⟨x, hx⟩ ⟨y, hy⟩ ⟨z, hz⟩) :=
  eq_bitF (hb _ hy _ hx _ hz)

theorem colC_eq (x : Fin 5) (z : Fin 64) :
    colC loc x.val z.val = bitF (stateOf loc x 0 z ^^ stateOf loc x 1 z ^^ stateOf loc x 2 z ^^
      stateOf loc x 3 z ^^ stateOf loc x 4 z) := by
  simp only [colC, sum_eq, List.range_succ, List.range_zero, List.nil_append, List.map_append,
    List.map_cons, List.map_nil, List.sum_append, List.sum_cons, List.sum_nil, add_zero]
  rw [loc_a' h2 hb x.isLt (by omega : 0 < 5) z.isLt, loc_a' h2 hb x.isLt (by omega : 1 < 5) z.isLt,
    loc_a' h2 hb x.isLt (by omega : 2 < 5) z.isLt, loc_a' h2 hb x.isLt (by omega : 3 < 5) z.isLt,
    loc_a' h2 hb x.isLt (by omega : 4 < 5) z.isLt, bitF_add h2, bitF_add h2, bitF_add h2,
    bitF_add h2]
  rfl

theorem colA'_eq (x y : Fin 5) (z : Fin 64) :
    colA' loc y.val x.val z.val = bitF (theta (stateOf loc) x y z) := by
  have h4 := colC_eq h2 hb (x - 1) z
  have h1 := colC_eq h2 hb (x + 1) (z - 1)
  rw [fin5_sub_one] at h4
  rw [fin5_add, fin64_sub_one, Fin.val_one] at h1
  rw [colA', h4, h1, loc_a h2 hb, bitF_add h2, bitF_add h2, theta]
  simp only
  cases stateOf loc x y z <;> simp

theorem colB_eq (x y : Fin 5) (z : Fin 64) :
    colB loc x.val y.val z.val = bitF (pi (rho (theta (stateOf loc))) x y z) := by
  rw [pi_rho_apply, ← colA'_eq h2 hb]
  rfl

/-- A round-k row maps its state to the next row's state by Rnd(., k). -/
theorem next_eq {first : F} {k : ℕ} (hR : RowSpecB cb loc nxt first) (hk : k < 24)
    (hf : OneHot loc k) (x y : Fin 5) (z : Fin 64) :
    nxt (binary.col.a y.val x.val z.val) = bitF (rnd (stateOf loc) k x y z) := by
  have h := hR.round y y.isLt x x.isLt z z.isLt
  have hB1 := colB_eq h2 hb (x + 1) y z
  have hB2 := colB_eq h2 hb (x + 2) y z
  rw [fin5_add, Fin.val_one] at hB1
  rw [fin5_add, Fin.val_two] at hB2
  simp only [roundExpr] at h
  rw [hf 24 (by omega), ite_eq_right (show ¬ (24 = k) by omega), add_zero, one_mul, colB_eq h2 hb, hB1, hB2,
    one_add_bitF_mul h2, bitF_add h2] at h
  simp only [rnd, iota, chi, Bool.xor_true, Fin.ext_iff, Fin.val_zero]
  split_ifs at h ⊢ with h0
  · have hsum : sum fieldOps (((List.range 24).filter fun r => rcBit r z.val ≠ 0).map fun r =>
        loc (col.round_flags r)) = bitF (decide (rcBit k z.val ≠ 0)) := by
      rw [sum_eq, List.map_congr_left (g := fun r => if r = k then (1 : F) else 0)
        (fun r hr => hf r (by simp at hr; omega)), sum_onehot _ ((List.nodup_range).filter _)]
      by_cases hrc : rcBit k z.val ≠ 0 <;> simp [hrc, hk, bitF]
    rw [hsum] at h
    rw [char2_solve h2 h, bitF_add h2,
      show decide (rcBit k z.val ≠ 0) = roundConstant k z by
        simp only [rcBit_eq hk z.isLt, Fin.ofNat_val_eq_self, Bool.decide_eq_true]]
  · exact ((add_eq_zero_iff_eq h2).mp h).symm

end round


/-! ## Permutations -/

section perm

variable (h2 : (2 : F) = 0) {cb : Bool} {T : Instance F} (hT : Satisfies (constraints (binaryAir cb)) T)
include h2 hT

/-- Every row is one-hot. -/
theorem onehot_all : ∀ i < T.height, ∃ k < 25, OneHot (curB cb T i) k := by
  intro i
  induction i with
  | zero =>
    intro hi
    have h := rowSpecB_of_satisfies hT hi
    refine ⟨0, by omega, fun r hr => ?_⟩
    rcases r with _ | r
    · simpa [sub_eq_zero] using h.first_flag
    · simpa using h.first_zero r (by omega)
  | succ i ih =>
    intro hi
    obtain ⟨k, hk, hf⟩ := ih (by omega)
    have h := rowSpecB_of_satisfies hT (by omega : i < T.height)
    have h' := rowSpecB_of_satisfies hT hi
    rw [Nat.mod_eq_of_lt hi] at h
    obtain ⟨hlt, hge⟩ := onehot_next h2 h h' hk hf
    by_cases hk23 : k < 23
    · exact ⟨k + 1, by omega, hlt hk23⟩
    · rcases hge (by omega) with h0 | h24
      · exact ⟨0, by omega, h0⟩
      · exact ⟨24, by omega, h24⟩

variable (hbits : ∀ i < T.height, ∀ y < 5, ∀ x < 5, ∀ z < 64,
  curB cb T i (binary.col.a y x z) * (curB cb T i (binary.col.a y x z) - 1) = 0)
include hbits

/-- A round-k row's successor, modulo the height, holds Rnd(A, k) of its state A. -/
theorem state_next {i k : ℕ} (hi : i < T.height) (hk : k < 24) (hf : OneHot (curB cb T i) k) :
    stateOf (curB cb T ((i + 1) % T.height)) = rnd (stateOf (curB cb T i)) k := by
  funext x y z
  have := next_eq h2 (hbits i hi) (rowSpecB_of_satisfies hT hi) hk hf x y z
  simp only [stateOf] at this ⊢
  rw [this, bv_bitF]

/-- From a round-0 row, the next 23 rows are rounds 1 to 23, and the row after holds Keccak-f[1600] of its state. -/
theorem perm_sound {i : ℕ} (hi : i < T.height) (hf : OneHot (curB cb T i) 0) :
    (∀ k < 24, OneHot (curB cb T ((i + k) % T.height)) k) ∧
      stateOf (curB cb T ((i + 24) % T.height)) = keccakP 24 (stateOf (curB cb T i)) := by
  have hn : 0 < T.height := by omega
  have hstep : ∀ k < 24, OneHot (curB cb T ((i + k) % T.height)) k ∧
      stateOf (curB cb T ((i + k) % T.height)) =
        (List.range k).foldl (fun A r => rnd A r) (stateOf (curB cb T i)) := by
    intro k
    induction k with
    | zero => intro _; simpa [Nat.mod_eq_of_lt hi] using hf
    | succ k ih =>
      intro hk
      obtain ⟨hf', hs⟩ := ih (by omega)
      have hj : (i + k) % T.height < T.height := Nat.mod_lt _ hn
      have hmod : (i + (k + 1)) % T.height = ((i + k) % T.height + 1) % T.height := by
        rw [Nat.mod_add_mod, Nat.add_assoc]
      have h := rowSpecB_of_satisfies hT hj
      have h' := rowSpecB_of_satisfies hT (Nat.mod_lt ((i + k) % T.height + 1) hn)
      refine ⟨?_, ?_⟩
      · rw [hmod]; exact (onehot_next h2 h h' (by omega) hf').1 (by omega)
      · rw [hmod, state_next h2 hT hbits hj (by omega) hf', hs, List.range_succ, List.foldl_append]
        rfl
  refine ⟨fun k hk => (hstep k hk).1, ?_⟩
  obtain ⟨hf23, hs23⟩ := hstep 23 (by omega)
  have hj : (i + 23) % T.height < T.height := Nat.mod_lt _ hn
  have hmod : (i + 24) % T.height = ((i + 23) % T.height + 1) % T.height := by
    rw [Nat.mod_add_mod]
  rw [hmod, state_next h2 hT hbits hj (by omega) hf23, hs23, keccakP]
  simp [List.range_succ]

end perm

end Plonky3Lean.Proofs.KeccakAir.Binary
