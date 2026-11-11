module

public import Plonky3Lean.Proofs.Sha256Air.Binary.Add
public import Plonky3Lean.Proofs.Sha256Air.Row

@[expose] public section

/-!
# A chained addition on the row builder

The AIR adds n words with n - 2 stored-carry additions and a last one that reads its carries off the sum.

On bits, in characteristic 2, its constraints force the sum to be the words' sum modulo `2^32`.
-/

set_option linter.unusedSectionVars false

namespace Plonky3Lean.Proofs.Sha256Air.Binary

open p3_air.builder.mirror p3_air.air.mirror p3_sha256_air.mirror p3_sha256_air.mirror.binary
open Plonky3Lean.Spec.Air
open Plonky3Lean.Proofs.KeccakAir (propBuilder fieldOps bitF foldl_and)
open Plonky3Lean.Proofs.Sha256Air (Holds)

variable {F : Type} [Field F] (env : Var → F) (L : AirLayout)

/-- The sum of a nonempty list of words, added from the left. -/
def sumW : List (BitVec 32) → BitVec 32
  | [] => 0
  | W :: Ws => Ws.foldl (· + ·) W

theorem step_fst (acc : Prop × (ℕ → F)) (wc : (ℕ → F) × (ℕ → F)) :
    (add_many_step (propBuilder env L) acc wc).1 =
      ((acc.1 ∧ acc.2 0 * wc.1 0 + wc.2 0 = 0) ∧
        ∀ i ∈ List.range' 1 30, maj fieldOps (acc.2 i) (wc.1 i) (wc.2 (i - 1)) + wc.2 i = 0) := by
  exact Plonky3Lean.Proofs.Sha256Air.foldl_eq_and _ (fun _ _ => rfl) _

theorem fold_mono (l : List ((ℕ → F) × (ℕ → F))) (acc : Prop × (ℕ → F))
    (h : (l.foldl (add_many_step (propBuilder env L)) acc).1) : acc.1 := by
  induction l generalizing acc with
  | nil => exact h
  | cons x l ih => exact ((step_fst env L acc x ▸ ih _ h).1).1

theorem fold_holds (h2 : (2 : F) = 0) (l : List ((ℕ → F) × (ℕ → F))) (Wl : List (BitVec 32))
    (hl : List.Forall₂ (fun wc W => Holds wc.1 W) l Wl) (acc : Prop × (ℕ → F)) (P : BitVec 32)
    (hp : Holds acc.2 P) (h : (l.foldl (add_many_step (propBuilder env L)) acc).1) :
    acc.1 ∧ Holds (l.foldl (add_many_step (propBuilder env L)) acc).2 (Wl.foldl (· + ·) P) := by
  induction hl generalizing acc P with
  | nil => exact ⟨h, hp⟩
  | @cons wc W l Wl hw _ ih =>
    have h1 := fold_mono env L l _ h
    rw [step_fst] at h1
    obtain ⟨⟨hs, h0⟩, hi⟩ := h1
    exact ⟨hs, (ih _ (P + W) (step_holds h2 hp hw h0 hi) h).2⟩

theorem forall₂_zip {a : List (ℕ → F)} {b : List (BitVec 32)} {cs : List (ℕ → F)}
    (ht : List.Forall₂ Holds a b) (hl : a.length = cs.length) :
    List.Forall₂ (fun wc W => Holds wc.1 W) (a.zip cs) b := by
  induction ht generalizing cs with
  | nil => exact .nil
  | cons hab _ ih =>
    cases cs with
    | nil => simp at hl
    | cons c cs => exact .cons hab (ih (by simpa using hl))

/-- A chained addition on bits: the state's proposition holds, and the sum holds the words' sum. -/
theorem add_many_holds (h2 : (2 : F) = 0) {s : Prop} {ws cs : List (ℕ → F)} {sum : ℕ → F}
    {Ws : List (BitVec 32)} (hw : List.Forall₂ Holds ws Ws) (hlen : ws.length = cs.length + 2)
    (h : add_many (propBuilder env L) s ws cs sum) : s ∧ Holds sum (sumW Ws) := by
  obtain ⟨w0, rest, W0, Wrest, hw0, hr, rfl, rfl⟩ : ∃ w0 rest W0 Wrest, Holds w0 W0 ∧
      List.Forall₂ Holds rest Wrest ∧ ws = w0 :: rest ∧ Ws = W0 :: Wrest := by
    cases hw with
    | nil => simp at hlen
    | cons h1 h2' => exact ⟨_, _, _, _, h1, h2', rfl, rfl⟩
  have hN : rest.length = cs.length + 1 := by simpa using hlen
  have hWN : Wrest.length = cs.length + 1 := by rw [← hr.length_eq, hN]
  unfold add_many at h
  simp only [List.drop_succ_cons, List.drop_zero, List.getD_cons_zero, List.getD_cons_succ] at h
  obtain ⟨⟨hF, h0⟩, hi⟩ := (Plonky3Lean.Proofs.Sha256Air.foldl_eq_and _ (fun _ _ => rfl) _).mp h
  have hz := forall₂_zip (List.forall₂_take cs.length hr) (cs := cs) (by simp [hN])
  obtain ⟨hs, hp⟩ := fold_holds env L h2 _ _ hz _ W0 hw0 hF
  have hl : Holds (rest.getD cs.length fun _ => (propBuilder env L).const 0) (Wrest.getD cs.length 0) := by
    rw [List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ (by omega)]
    exact List.forall₂_iff_get.mp hr |>.2 _ (by omega) (by omega)
  refine ⟨hs, ?_⟩
  have := final_holds h2 hp hl h0 hi
  rw [sumW, show Wrest = Wrest.take cs.length ++ [Wrest.getD cs.length 0] by
    rw [List.getD_eq_getElem _ _ (by omega)]
    conv_lhs => rw [← List.take_append_drop cs.length Wrest]
    congr 1
    rw [List.drop_eq_getElem_cons (by omega), List.drop_eq_nil_of_le (by omega)], List.foldl_append,
    List.foldl_cons, List.foldl_nil]
  exact this

theorem fold_factor (l : List ((ℕ → F) × (ℕ → F))) (s : Prop) (p : ℕ → F) :
    ((l.foldl (add_many_step (propBuilder env L)) (s, p)).1 ↔
      s ∧ (l.foldl (add_many_step (propBuilder env L)) (True, p)).1) ∧
    (l.foldl (add_many_step (propBuilder env L)) (s, p)).2 =
      (l.foldl (add_many_step (propBuilder env L)) (True, p)).2 := by
  induction l generalizing s p with
  | nil => simp
  | cons x l ih =>
    simp only [List.foldl_cons]
    obtain ⟨h1, h2⟩ := ih (add_many_step (propBuilder env L) (s, p) x).1
      (add_many_step (propBuilder env L) (s, p) x).2
    obtain ⟨h3, h4⟩ := ih (add_many_step (propBuilder env L) (True, p) x).1
      (add_many_step (propBuilder env L) (True, p) x).2
    have e2 : (add_many_step (propBuilder env L) (s, p) x).2 =
        (add_many_step (propBuilder env L) (True, p) x).2 := rfl
    refine ⟨?_, ?_⟩
    · rw [show (add_many_step (propBuilder env L) (s, p) x) =
          ((add_many_step (propBuilder env L) (s, p) x).1, (add_many_step (propBuilder env L) (s, p) x).2)
          from rfl, h1, step_fst, show (add_many_step (propBuilder env L) (True, p) x) =
          ((add_many_step (propBuilder env L) (True, p) x).1,
            (add_many_step (propBuilder env L) (True, p) x).2) from rfl, h3, step_fst, e2]
      simp only [true_and, and_assoc]
    · rw [show (add_many_step (propBuilder env L) (s, p) x) =
          ((add_many_step (propBuilder env L) (s, p) x).1, (add_many_step (propBuilder env L) (s, p) x).2)
          from rfl, h2, show (add_many_step (propBuilder env L) (True, p) x) =
          ((add_many_step (propBuilder env L) (True, p) x).1,
            (add_many_step (propBuilder env L) (True, p) x).2) from rfl, h4, e2]

/-- On the row builder, a chained addition conjoins its constraints to the state. -/
theorem add_many_factor (s : Prop) (ws cs : List (ℕ → F)) (sum : ℕ → F) :
    add_many (propBuilder env L) s ws cs sum = (s ∧ add_many (propBuilder env L) True ws cs sum) := by
  unfold add_many
  simp only []
  obtain ⟨h1, h2⟩ := fold_factor env L (((ws.drop 1).take cs.length).zip cs) s
    (ws.getD 0 fun _ => (propBuilder env L).const 0)
  rw [h2]
  apply propext
  simp only [Plonky3Lean.Proofs.KeccakAir.pb_assert_zero, foldl_and, h1, and_assoc]

end Plonky3Lean.Proofs.Sha256Air.Binary
