module

public import Plonky3Lean.Proofs.Blake2sAir.Row
public import Plonky3Lean.Proofs.Blake2sAir.Spec
public import Plonky3Lean.Proofs.Sha256Air.Binary.Add
public import Plonky3Lean.Proofs.Sha256Air.Words
public import Plonky3Lean.Proofs.Sha256Air.GenSat

@[expose] public section

/-!
# One row of the BLAKE2s AIR computes the compression function

Let a row meet its constraints in characteristic 2, with its input cells bits.

Then every witness cell is a bit, and the working state the AIR tracks holds the RFC 7693 working vector:

- before the rounds, it holds the chaining value, the IV, the counter and the flag
- after each G step, it holds the vector G leaves.

The additions are ripple-carry adders on bits, so no characteristic bound beyond 2 is needed.
-/

set_option linter.unusedSectionVars false

namespace Plonky3Lean.Proofs.Blake2sAir

open p3_air.builder.mirror p3_air.air.mirror p3_blake2s_air.mirror Plonky3Lean.Spec.Air
open Plonky3Lean.Proofs.KeccakAir (propBuilder fieldOps rowOf bitF)
open Plonky3Lean.Proofs.Sha256Air (Holds rotr_bit)
open Plonky3Lean.Proofs.Sha256Air.Binary (step_holds final_holds add_bitF neg_eq_self eq_of_add_eq_zero)

variable {F : Type} [Field F]

theorem ite_t {α : Type} {c : Prop} [Decidable c] (h : c) (a b : α) : (if c then a else b) = a := by
  simp [h]

theorem ite_f {α : Type} {c : Prop} [Decidable c] (h : ¬ c) (a b : α) : (if c then a else b) = b := by
  simp [h]

/-! ## Words of bits -/

theorem u32_bits (w : Word) {i : ℕ} (hi : i < 32) :
    (u32_to_bits_le w i : F) = bitF (w.getLsbD i) :=
  Plonky3Lean.Proofs.Sha256Air.u32_bits_eq w hi

theorem holds_u32 (w : Word) : Holds (u32_to_bits_le (F := F) w) w := fun _ hb => u32_bits w hb

theorem rotl_bit (x : Word) {n : ℕ} (hn : n < 32) {i : ℕ} (hi : i < 32) :
    (x.rotateLeft n).getLsbD i = x.getLsbD ((i + 32 - n) % 32) := by
  rw [BitVec.getLsbD_rotateLeft, Nat.mod_eq_of_lt hn]
  split_ifs with h
  · congr 1; omega
  · simp only [hi, decide_true, Bool.true_and]; congr 1; omega

/-- Two words held by the same cells are equal. -/
theorem Holds.unique {x : ℕ → F} {X Y : Word} (hX : Holds x X) (hY : Holds x Y) : X = Y := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have := (hX i hi).symm.trans (hY i hi)
  cases hx : X.getLsbD i <;> cases hy : Y.getLsbD i <;> simp_all [bitF]

variable (h2 : (2 : F) = 0)
include h2

/-! ## The additions and the rotations -/

theorem add2_holds {x y s : ℕ → F} {X Y : Word} (hx : Holds x X) (hy : Holds y Y)
    (h : Add2Ok x y s) : Holds s (X + Y) :=
  final_holds h2 hx hy h.1 h.2

theorem add3_holds {x y z c s : ℕ → F} {X Y Z : Word} (hx : Holds x X) (hy : Holds y Y)
    (hz : Holds z Z) (h : Add3Ok x y z c s) : Holds s (X + Y + Z) :=
  add2_holds h2 (step_holds h2 hx hy h.1.1 h.1.2) hz h.2

/-- The cells rotated into `x ^ (y <<< n)` hold `(x ^ z) >>> n` when that sum holds `z`. -/
theorem xor_rotl_inv {x y : ℕ → F} {X Z : Word} {n : ℕ} (hn : n < 32) (hx : Holds x X)
    (hz : Holds (xor_rotl fieldOps x y n) Z) : Holds y ((X ^^^ Z).rotateRight n) := by
  intro j hj
  have hi : ((j + n) % 32 + 32 - n) % 32 = j := by omega
  have e := hz ((j + n) % 32) (Nat.mod_lt _ (by norm_num))
  simp only [xor_rotl, fo_add, hi, hx _ (Nat.mod_lt _ (by norm_num : 0 < 32))] at e
  have : y j = bitF (Z.getLsbD ((j + n) % 32)) + bitF (X.getLsbD ((j + n) % 32)) := by
    linear_combination e + Plonky3Lean.Proofs.Sha256Air.Binary.neg_eq_self h2
      (bitF (X.getLsbD ((j + n) % 32)) : F)
  rw [this, add_bitF h2, rotr_bit _ hn hj, BitVec.getLsbD_xor, Bool.xor_comm]

/-- The cells of `x ^ (y <<< n)` hold that word. -/
theorem xor_rotl_holds {x y : ℕ → F} {X Y : Word} {n : ℕ} (hn : n < 32) (hx : Holds x X)
    (hy : Holds y Y) : Holds (xor_rotl fieldOps x y n) (X ^^^ Y.rotateLeft n) := by
  intro i hi
  simp only [xor_rotl, fo_add, hx i hi, hy _ (Nat.mod_lt _ (by norm_num : 0 < 32)), add_bitF h2,
    BitVec.getLsbD_xor, rotl_bit Y hn hi]

omit h2 in
theorem xor_rotl_var_eq (x y : ℕ → F) (n : ℕ) :
    xor_rotl_var fieldOps x y n = xor_rotl fieldOps x y n := rfl

/-! ## One G step -/

omit h2 in
/-- The AIR's state holds a working vector of 16 words, row by row. -/
def StateHolds (st : State F) (v : List Word) : Prop :=
  v.length = 16 ∧ ∀ j < 4, Holds (st.a j) (v.getD j 0) ∧ Holds (st.b j) (v.getD (4 + j) 0) ∧
    Holds (st.c j) (v.getD (8 + j) 0) ∧ Holds (st.d j) (v.getD (12 + j) 0)

/-- A G step that meets its constraints moves the state as G moves the working vector. -/
theorem step_sound {st : State F} {v : List Word} (hs : StateHolds st v) {slots : List ℕ}
    (hsl : ∀ j < 4, slots.getD j 0 < 4) {mx my : ℕ → F} {X Y : Word} (hx : Holds mx X)
    (hy : Holds my Y) {g : Blake2sBinaryGCols F} (hok : GOk st slots mx my g) :
    StateHolds (gNext st slots g)
      (Plonky3Lean.Spec.Blake2s.G v (slots.getD 0 0) (4 + slots.getD 1 0) (8 + slots.getD 2 0)
        (12 + slots.getD 3 0) X Y) := by
  obtain ⟨hlen, hst⟩ := hs
  obtain ⟨ok1, ok2, ok3, ok4⟩ := hok
  have ha0 := hsl 0 (by norm_num)
  have hb0 := hsl 1 (by norm_num)
  have hc0 := hsl 2 (by norm_num)
  have hd0 := hsl 3 (by norm_num)
  simp only [gNext] at ok1 ok2 ok3 ok4 ⊢
  generalize slots.getD 0 0 = ia at *
  generalize slots.getD 1 0 = ib at *
  generalize slots.getD 2 0 = ic at *
  generalize slots.getD 3 0 = id at *
  have ha := (hst _ ha0).1
  have hb := (hst _ hb0).2.1
  have hc := (hst _ hc0).2.2.1
  have hd := (hst _ hd0).2.2.2
  have ea1 := add3_holds h2 ha hb hx ok1
  have ed1 := xor_rotl_inv h2 (by norm_num) hd ea1
  have ec1 := add2_holds h2 hc ed1 ok2
  rw [xor_rotl_var_eq] at ec1
  have eb1 := xor_rotl_inv h2 (by norm_num) hb ec1
  have ea2 := add3_holds h2 ea1 eb1 hy ok3
  rw [xor_rotl_var_eq] at ea2
  have ed2 := xor_rotl_inv h2 (by norm_num) ed1 ea2
  have ec2 := add2_holds h2 ec1 ed2 ok4
  rw [xor_rotl_var_eq] at ec2
  have eb2 := xor_rotl_inv h2 (by norm_num) eb1 ec2
  refine ⟨by rw [Plonky3Lean.Proofs.Blake2sAir.length_G, hlen], fun j hj => ?_⟩
  simp only [G_getD hlen ha0 hb0 hc0 hd0, xor_rotl_var_eq]
  refine ⟨?_, ?_, ?_, ?_⟩
  · by_cases e : j = ia
    · subst e; rw [Function.update_self, ite_t rfl]; exact ea2
    · rw [Function.update_of_ne e, ite_f e, ite_f (by omega), ite_f (by omega), ite_f (by omega)]
      exact (hst j hj).1
  · by_cases e : j = ib
    · subst e; rw [Function.update_self, ite_f (by omega), ite_t rfl]; exact eb2
    · rw [Function.update_of_ne e, ite_f (by omega), ite_f (by omega), ite_f (by omega),
        ite_f (by omega)]
      exact (hst j hj).2.1
  · by_cases e : j = ic
    · subst e; rw [Function.update_self, ite_f (by omega), ite_f (by omega), ite_t rfl]; exact ec2
    · rw [Function.update_of_ne e, ite_f (by omega), ite_f (by omega), ite_f (by omega),
        ite_f (by omega)]
      exact (hst j hj).2.2.1
  · by_cases e : j = id
    · subst e
      rw [Function.update_self, ite_f (by omega), ite_f (by omega), ite_f (by omega), ite_t rfl]
      exact ed2
    · rw [Function.update_of_ne e, ite_f (by omega), ite_f (by omega), ite_f (by omega),
        ite_f (by omega)]
      exact (hst j hj).2.2.2

/-- The witness words of a G step that meets its constraints are words of bits. -/
theorem step_bits {st : State F} {v : List Word} (hs : StateHolds st v) {slots : List ℕ}
    (hsl : ∀ j < 4, slots.getD j 0 < 4) {mx my : ℕ → F} {X Y : Word} (hx : Holds mx X)
    (hy : Holds my Y) {g : Blake2sBinaryGCols F} (hok : GOk st slots mx my g) :
    (∃ W, Holds g.d1 W) ∧ (∃ W, Holds g.b1 W) ∧ (∃ W, Holds g.d2 W) ∧ (∃ W, Holds g.b2 W) := by
  obtain ⟨-, hst⟩ := hs
  obtain ⟨ok1, ok2, ok3, ok4⟩ := hok
  have ea1 := add3_holds h2 (hst _ (hsl 0 (by norm_num))).1 (hst _ (hsl 1 (by norm_num))).2.1 hx ok1
  have ed1 := xor_rotl_inv h2 (by norm_num) (hst _ (hsl 3 (by norm_num))).2.2.2 ea1
  have ec1 := add2_holds h2 (hst _ (hsl 2 (by norm_num))).2.2.1 ed1 ok2
  rw [xor_rotl_var_eq] at ec1
  have eb1 := xor_rotl_inv h2 (by norm_num) (hst _ (hsl 1 (by norm_num))).2.1 ec1
  have ea2 := add3_holds h2 ea1 eb1 hy ok3
  rw [xor_rotl_var_eq] at ea2
  have ed2 := xor_rotl_inv h2 (by norm_num) ed1 ea2
  have ec2 := add2_holds h2 ec1 ed2 ok4
  rw [xor_rotl_var_eq] at ec2
  exact ⟨⟨_, ed1⟩, ⟨_, eb1⟩, ⟨_, ed2⟩, ⟨_, xor_rotl_inv h2 (by norm_num) eb1 ec2⟩⟩

/-! ## The rounds -/

omit h2 in
theorem g_schedule_lt (g : ℕ) {j : ℕ} (hj : j < 4) : (G_SCHEDULE.getD g []).getD j 0 < 4 := by
  rcases Nat.lt_or_ge g 8 with hg | hg
  · have : ∀ g < 8, ∀ j < 4, (G_SCHEDULE.getD g []).getD j 0 < 4 := by decide
    exact this g hg j hj
  · rw [List.getD_eq_default G_SCHEDULE [] (by simpa [G_SCHEDULE] using hg)]; simp

omit h2 in
theorem sigma_lt (r j : ℕ) : (SIGMA.getD r []).getD j 0 < 16 := by
  rcases Nat.lt_or_ge r 10 with hr | hr
  · rcases Nat.lt_or_ge j 16 with hj | hj
    · have : ∀ r < 10, ∀ j < 16, (SIGMA.getD r []).getD j 0 < 16 := by decide
      exact this r hr j hj
    · have : ∀ r < 10, (SIGMA.getD r []).length = 16 := by decide
      rw [List.getD_eq_default _ _ (by rw [this r hr]; exact hj)]; simp
  · rw [List.getD_eq_default SIGMA [] (by simpa [SIGMA] using hr)]; simp

/-- Rounds that meet their constraints move the state as the ten rounds of RFC 7693. -/
theorem rounds_sound {loc : ℕ → F} {M : List Word} (hm : ∀ k < 16, Holds (msg loc k) (M.getD k 0))
    {st : State F} {v : List Word} (hs : StateHolds st v)
    (hc : Chain (CRound loc) (TRound loc) (List.range NUM_ROUNDS) st) :
    StateHolds ((List.range NUM_ROUNDS).foldl (TRound loc) st)
      (Plonky3Lean.Spec.Blake2s.rounds M v 10) := by
  rw [rounds_eq]
  refine chain_inv (U := fun v r => (List.range 8).foldl (gStep M r) v) (I := StateHolds)
    (fun r st v hr hs => ?_) _ _ _ hc hs
  exact chain_inv (U := gStep M r) (I := StateHolds) (fun g st v hg hs =>
    step_sound h2 hs (fun j hj => g_schedule_lt g hj) (hm _ (sigma_lt _ _)) (hm _ (sigma_lt _ _)) hg)
    _ _ _ hr hs

/-! ## The initial state -/

omit h2 in
theorem IV_eq : p3_blake2s_air.mirror.IV = Plonky3Lean.Spec.Blake2s.IV := by decide

theorem holds_add {x y : ℕ → F} {X Y : Word} (hx : Holds x X) (hy : Holds y Y) :
    Holds (fun b => x b + y b) (X ^^^ Y) := fun b hb => by
  show x b + y b = _
  rw [hx b hb, hy b hb, add_bitF h2, BitVec.getLsbD_xor]

section init

variable [DecidableEq F] (loc : ℕ → F)

omit h2 in
/-- The chaining value a row holds. -/
def cvOf : List Word := (List.range 8).map fun i => Plonky3Lean.Proofs.Sha256Air.wordOf
  fun b => loc (col.chaining_value i b)

omit h2 in
/-- The message block a row holds. -/
def blockOf : List Word := (List.range 16).map fun i => Plonky3Lean.Proofs.Sha256Air.wordOf (msg loc i)

omit h2 in
/-- The byte counter a row holds, from its low and its high word. -/
def counterOf : ℕ :=
  (Plonky3Lean.Proofs.Sha256Air.wordOf fun b => loc (col.counter_low b)).toNat +
    2 ^ 32 * (Plonky3Lean.Proofs.Sha256Air.wordOf fun b => loc (col.counter_high b)).toNat

omit h2 in
/-- The final-block flag a row holds. -/
def flagOf : Bool := decide (loc col.last_block = 1)

end init

omit h2 in
theorem ofNat_counter_lo (lo hi : Word) : BitVec.ofNat 32 (lo.toNat + 2 ^ 32 * hi.toNat) = lo := by
  apply BitVec.eq_of_toNat_eq
  have := lo.isLt
  simp only [BitVec.toNat_ofNat]
  omega

omit h2 in
theorem ofNat_counter_hi (lo hi : Word) :
    BitVec.ofNat 32 ((lo.toNat + 2 ^ 32 * hi.toNat) / 2 ^ 32) = hi := by
  apply BitVec.eq_of_toNat_eq
  have := lo.isLt
  have := hi.isLt
  simp only [BitVec.toNat_ofNat]
  omega

/-- The state before the rounds holds the RFC's initial working vector, on a row of input bits. -/
theorem init_sound [DecidableEq F] {loc : ℕ → F} (hb : BoolOk loc) :
    StateHolds (initState loc)
      (Plonky3Lean.Spec.Blake2s.init (cvOf loc) (counterOf loc) (flagOf loc)) := by
  obtain ⟨hcv, -, hlo, hhi, hfl⟩ := hb
  have hlen : (cvOf loc).length = 8 := by simp [cvOf]
  have hcvj : ∀ i < 8, Holds (fun b => loc (col.chaining_value i b)) ((cvOf loc).getD i 0) :=
    fun i hi => by
      simpa [cvOf, hi] using Plonky3Lean.Proofs.Sha256Air.holds_wordOf (hcv i hi)
  have hivj : ∀ j < 8, ((cvOf loc) ++ Plonky3Lean.Spec.Blake2s.IV).getD (8 + j) 0 =
      Plonky3Lean.Spec.Blake2s.IV.getD j 0 := fun j _ => by
    rw [List.getD_append_right _ _ _ _ (by omega), hlen, Nat.add_sub_cancel_left]
  have hiv : ∀ i, Holds (u32_to_bits_le (F := F) (p3_blake2s_air.mirror.IV.getD i 0))
      (Plonky3Lean.Spec.Blake2s.IV.getD i 0) := fun i => by rw [IV_eq]; exact holds_u32 _
  refine ⟨by cases flagOf loc <;> simp [Plonky3Lean.Spec.Blake2s.init, hlen,
    Plonky3Lean.Spec.Blake2s.IV], fun j hj => ?_⟩
  simp only [init_getD hlen]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [ite_f (by omega), ite_f (by omega), ite_f (by omega), List.getD_append _ _ _ _ (by omega)]
    exact hcvj j (by omega)
  · rw [ite_f (by omega), ite_f (by omega), ite_f (by omega), List.getD_append _ _ _ _ (by omega)]
    exact hcvj (4 + j) (by omega)
  · rw [ite_f (by omega), ite_f (by omega), ite_f (by omega), hivj j (by omega)]
    exact hiv j
  · interval_cases j
    · rw [ite_t rfl, counterOf, ofNat_counter_lo]
      exact holds_add h2 (hiv 4) (Plonky3Lean.Proofs.Sha256Air.holds_wordOf hlo)
    · rw [ite_f (by omega), ite_t rfl, counterOf, ofNat_counter_hi]
      exact holds_add h2 (hiv 5) (Plonky3Lean.Proofs.Sha256Air.holds_wordOf hhi)
    · rw [ite_f (by omega), ite_f (by omega), ite_t rfl]
      have hf : loc col.last_block = bitF (flagOf loc) := Plonky3Lean.Proofs.KeccakAir.eq_bitF hfl
      have := holds_add h2 (hiv 6) (Y := if flagOf loc then BitVec.allOnes 32 else 0)
        (y := fun _ => loc col.last_block) (fun b hb => by
          rw [hf]
          cases flagOf loc
          · simp
          · simp only [ite_true, BitVec.getLsbD_allOnes, hb, decide_true])
      cases e : flagOf loc <;> simp only [e, Bool.false_eq_true, ite_false, ite_true,
        BitVec.xor_allOnes] at this ⊢ <;> exact this
    · rw [ite_f (by omega), ite_f (by omega), ite_f (by omega), hivj 7 (by omega)]
      exact hiv 7

omit h2 in
/-- The message cells of a row of input bits hold its block. -/
theorem msg_holds [DecidableEq F] {loc : ℕ → F} (hB : BoolOk loc) :
    ∀ k < 16, Holds (msg loc k) ((blockOf loc).getD k 0) := fun k hk => by
  rw [show (blockOf loc).getD k 0 = Plonky3Lean.Proofs.Sha256Air.wordOf (msg loc k) by
    simp [blockOf, hk]]
  exact Plonky3Lean.Proofs.Sha256Air.holds_wordOf (hB.2.1 k hk)

omit h2 in
/-- On a row of input bits, the input cells are the bits of the words a row is read as. -/
theorem inputs_hold [DecidableEq F] {loc : ℕ → F} (hb : BoolOk loc) :
    (∀ i < 8, ∀ b < 32, loc (col.chaining_value i b) = bitF (((cvOf loc).getD i 0).getLsbD b)) ∧
    (∀ k < 16, ∀ b < 32, loc (col.block k b) = bitF (((blockOf loc).getD k 0).getLsbD b)) ∧
    (∀ b < 32, loc (col.counter_low b) = bitF ((BitVec.ofNat 32 (counterOf loc)).getLsbD b)) ∧
    (∀ b < 32, loc (col.counter_high b) = bitF ((BitVec.ofNat 32 (counterOf loc / 2 ^ 32)).getLsbD b)) ∧
    loc col.last_block = bitF (flagOf loc) := by
  refine ⟨fun i hi b hb' => ?_, fun k hk b hb' => msg_holds hb k hk b hb', fun b hb' => ?_,
    fun b hb' => ?_, Plonky3Lean.Proofs.KeccakAir.eq_bitF hb.2.2.2.2⟩
  · have := Plonky3Lean.Proofs.Sha256Air.holds_wordOf (hb.1 i hi) b hb'
    simpa [cvOf, hi] using this
  · rw [counterOf, ofNat_counter_lo]
    exact Plonky3Lean.Proofs.Sha256Air.holds_wordOf hb.2.2.1 b hb'
  · rw [counterOf, ofNat_counter_hi]
    exact Plonky3Lean.Proofs.Sha256Air.holds_wordOf hb.2.2.2.1 b hb'

/-! ## One row -/

/-- The working state after the ten rounds, as the evaluation tracks it on a row. -/
def finalState (loc : ℕ → F) : State F := (List.range NUM_ROUNDS).foldl (TRound loc) (initState loc)

/-- A row that meets its constraints, with its input cells bits, computes the RFC 7693 rounds.

The input cells are bits when the booleanity is stated.

The final state holds the working vector after ten rounds.

The rounds start from the row's chaining value, block, counter and flag. -/
theorem row_sound [DecidableEq F] {cb : Bool} {env : Var → F} {L : AirLayout}
    (h : eval cb (propBuilder env L) True) (hb : cb = true ∨ BoolOk (rowOf env L 0)) :
    BoolOk (rowOf env L 0) ∧ StateHolds (finalState (rowOf env L 0))
      (Plonky3Lean.Spec.Blake2s.rounds (blockOf (rowOf env L 0))
        (Plonky3Lean.Spec.Blake2s.init (cvOf (rowOf env L 0)) (counterOf (rowOf env L 0))
          (flagOf (rowOf env L 0))) 10) := by
  obtain ⟨hbool, hchain⟩ := (eval_iff cb env L).mp h
  have hB : BoolOk (rowOf env L 0) := hb.elim hbool id
  exact ⟨hB, rounds_sound h2 (msg_holds hB) (init_sound h2 hB) hchain⟩

end Plonky3Lean.Proofs.Blake2sAir
