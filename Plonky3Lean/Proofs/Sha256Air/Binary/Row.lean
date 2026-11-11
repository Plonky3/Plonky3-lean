module

public import Plonky3Lean.Proofs.Sha256Air.Binary.AddMany

@[expose] public section

/-!
# The constraints of one row of the characteristic-2 SHA-256 AIR

The row builder's conjunction, written out loop by loop:

- the input bits are bits, when the AIR states it
- each schedule word is a chained addition
- each round's Ch and Maj bits, and its three chained additions
- each output word is a chained addition
-/

set_option linter.unusedSectionVars false

namespace Plonky3Lean.Proofs.Sha256Air.Binary

open p3_air.builder.mirror p3_air.air.mirror p3_sha256_air.mirror.binary
open p3_sha256_air.mirror (kOf u32_to_bits_le)
open Plonky3Lean.Spec.Air
open Plonky3Lean.Proofs.KeccakAir (propBuilder fieldOps rowOf foldl_and)

variable {F : Type} [Field F]

/-- A row builder whose window is never read: the field operations and the conjunction. -/
def pb0 : AirBuilder F F Prop := propBuilder (fun _ => 0) {}

theorem add_many_pb0 (env : Var → F) (L : AirLayout) (s : Prop) (ws cs : List (ℕ → F)) (sum : ℕ → F) :
    add_many (propBuilder env L) s ws cs sum = (s ∧ add_many (pb0 (F := F)) True ws cs sum) := by
  rw [add_many_factor env L]; rfl

/-- The constraints of the characteristic-2 AIR on one row. -/
structure RowSpecB (loc : ℕ → F) (cb : Bool) : Prop where
  bool : cb = true → (∀ k < 4, ∀ b < 32, loc (col.a_chain k b) * (loc (col.a_chain k b) - 1) = 0) ∧
    (∀ k < 4, ∀ b < 32, loc (col.e_chain k b) * (loc (col.e_chain k b) - 1) = 0) ∧
    (∀ t < 16, ∀ b < 32, loc (col.w t b) * (loc (col.w t b) - 1) = 0)
  sched : ∀ i < 48, add_many (pb0 (F := F)) True
    [xor3_shift fieldOps (fun b => loc (col.w (16 + i - 2) b)) 17 19 10, fun b => loc (col.w (16 + i - 7) b),
      xor3_shift fieldOps (fun b => loc (col.w (16 + i - 15) b)) 7 18 3,
      fun b => loc (col.w (16 + i - 16) b)]
    ((List.range 2).map fun j c => loc (col.sched_carries i j c)) (fun b => loc (col.w (16 + i) b))
  ch : ∀ t < 64, ∀ i < 32, loc (col.e_chain (t + 3) i) * (loc (col.e_chain (t + 2) i) +
    loc (col.e_chain (t + 1) i)) + loc (col.e_chain (t + 1) i) + loc (col.ch t i) = 0
  maj : ∀ t < 64, ∀ i < 32, maj fieldOps (loc (col.a_chain (t + 3) i)) (loc (col.a_chain (t + 2) i))
    (loc (col.a_chain (t + 1) i)) + loc (col.maj t i) = 0
  t1 : ∀ t < 64, add_many (pb0 (F := F)) True
    [fun b => loc (col.e_chain t b), xor3_rot fieldOps (fun b => loc (col.e_chain (t + 3) b)) 6 11 25,
      fun i => loc (col.ch t i), fun i => u32_to_bits_le (F := F) (BitVec.ofNat 32 (kOf t)) i,
      fun b => loc (col.w t b)]
    ((List.range 3).map fun j c => loc (col.t1_carries t j c)) (fun i => loc (col.t1 t i))
  new_e : ∀ t < 64, add_many (pb0 (F := F)) True
    [fun b => loc (col.a_chain t b), fun i => loc (col.t1 t i)] [] (fun b => loc (col.e_chain (t + 4) b))
  new_a : ∀ t < 64, add_many (pb0 (F := F)) True
    [fun i => loc (col.t1 t i), xor3_rot fieldOps (fun b => loc (col.a_chain (t + 3) b)) 2 13 22,
      fun i => loc (col.maj t i)]
    [fun c => loc (col.new_a_carries t c)] (fun b => loc (col.a_chain (t + 4) b))
  out_a : ∀ i < 4, add_many (pb0 (F := F)) True
    [fun b => loc (col.a_chain (3 - i) b), fun b => loc (col.a_chain (67 - i) b)] []
    (fun b => loc (col.h_out i b))
  out_e : ∀ i < 4, add_many (pb0 (F := F)) True
    [fun b => loc (col.e_chain (3 - i) b), fun b => loc (col.e_chain (67 - i) b)] []
    (fun b => loc (col.h_out (4 + i) b))

@[simp] theorem fo_const (a : F) : fieldOps.const a = a := rfl
@[simp] theorem fo_add (a b : F) : fieldOps.add a b = a + b := rfl
@[simp] theorem fo_mul (a b : F) : fieldOps.mul a b = a * b := rfl
@[simp] theorem fo_sub (a b : F) : fieldOps.sub a b = a - b := rfl

theorem eval_iff_B (cb : Bool) (env : Var → F) (L : AirLayout) :
    p3_sha256_air.mirror.binary.eval cb (propBuilder env L) True ↔ RowSpecB (rowOf env L 0) cb := by
  simp only [p3_sha256_air.mirror.binary.eval, add_many_pb0, AirBuilder.assert_bools,
    AirBuilder.assert_zeros, Plonky3Lean.Proofs.KeccakAir.pb_assert_zero, and_assoc, foldl_and,
    List.foldl_map, Plonky3Lean.Proofs.KeccakAir.pb_current, Plonky3Lean.Proofs.KeccakAir.propBuilder_ops,
    true_and, AirBuilder.bool_check, List.mem_range, p3_sha256_air.mirror.BLOCK_WORDS,
    p3_sha256_air.mirror.SCHEDULE_EXTENSIONS, p3_sha256_air.mirror.NUM_COMPRESSION_ROUNDS,
    p3_sha256_air.mirror.STATE_WORDS, SCHEDULE_CARRIES, T1_CARRIES, fo_const, fo_add, fo_mul, fo_sub]
  have hbool : ∀ cb : Bool, (if cb = true then ∀ a ∈
        List.map (fun k b => rowOf env L 0 (col.a_chain k b)) (List.range 4) ++
          List.map (fun k b => rowOf env L 0 (col.e_chain k b)) (List.range 4) ++
            List.map (fun t b => rowOf env L 0 (col.w t b)) (List.range 16),
        ∀ a_2 < 32, a a_2 * (a a_2 - 1) = 0 else True) ↔
      (cb = true → (∀ k < 4, ∀ b < 32, rowOf env L 0 (col.a_chain k b) *
        (rowOf env L 0 (col.a_chain k b) - 1) = 0) ∧
        (∀ k < 4, ∀ b < 32, rowOf env L 0 (col.e_chain k b) * (rowOf env L 0 (col.e_chain k b) - 1) = 0) ∧
        (∀ t < 16, ∀ b < 32, rowOf env L 0 (col.w t b) * (rowOf env L 0 (col.w t b) - 1) = 0)) := by
    intro cb
    cases cb <;> simp [List.mem_append, or_imp, forall_and]
  have hout : ∀ P : ℕ → Prop, (∀ a < 8, P a) ↔ (∀ i < 4, P i) ∧ ∀ i < 4, P (4 + i) := fun P =>
    ⟨fun h => ⟨fun i hi => h i (by omega), fun i hi => h (4 + i) (by omega)⟩,
      fun h a ha => (Nat.lt_or_ge a 4).elim (h.1 a) fun h4 => by
        have := h.2 (a - 4) (by omega); rwa [show 4 + (a - 4) = a by omega] at this⟩
  rw [hbool, hout]
  constructor
  · rintro ⟨hb, hs, hr, ha, he⟩
    refine ⟨hb, fun i hi => hs i (by omega), fun t ht => (hr t ht).1, fun t ht => (hr t ht).2.1,
      fun t ht => (hr t ht).2.2.1, fun t ht => (hr t ht).2.2.2.1, fun t ht => (hr t ht).2.2.2.2,
      fun i hi => ?_, fun i hi => ?_⟩
    · have := ha i hi
      simp only [hi, ↓reduceIte, Nat.mod_eq_of_lt hi] at this
      rwa [show 64 + 3 - i = 67 - i by omega] at this
    · have := he i hi
      simp only [show ¬ 4 + i < 4 by omega, ↓reduceIte, show (4 + i) % 4 = i by omega] at this
      rwa [show 64 + 3 - i = 67 - i by omega] at this
  · rintro ⟨hb, hs, hc, hm, ht1, hne, hna, ha, he⟩
    refine ⟨hb, fun i hi => hs i (by omega), fun t ht => ⟨hc t ht, hm t ht, ht1 t ht, hne t ht, hna t ht⟩,
      fun i hi => ?_, fun i hi => ?_⟩
    · simp only [hi, ↓reduceIte, Nat.mod_eq_of_lt hi, show 64 + 3 - i = 67 - i by omega]
      exact ha i hi
    · simp only [show ¬ 4 + i < 4 by omega, ↓reduceIte, show (4 + i) % 4 = i by omega,
        show 64 + 3 - i = 67 - i by omega]
      exact he i hi

end Plonky3Lean.Proofs.Sha256Air.Binary
