module

public import Plonky3Lean.Proofs.BinaryDft.Stage

@[expose] public section

/-!
# The transcribed transform is the network

The stages run one pass each, top stage first forward and bottom stage first inverse.

So the transform of 2^l rows is the forward or inverse Lin-Chung-Han network on those rows.
-/

set_option linter.unusedSectionVars false

namespace Plonky3Lean.Proofs.BinaryDft

open Finset Plonky3Lean.Spec.BinaryDft p3_binary_dft.mirror p3_binary_dft.domain.mirror
  p3_binary_dft.butterfly.mirror p3_binary_dft.lch.mirror p3_dft.mirror

variable {F : Type _} [Field F] {V : Type _} [AddCommGroup V] [Module F V]

/-! ## The networks as loops over their stages -/

theorem network_foldl (τ : ℕ → ℕ → F) (l : ℕ) (y : ℕ → V) :
    network τ l y = (List.range l).reverse.foldl (fun y j => stage (τ j) j y) y := by
  induction l generalizing y with
  | zero => rfl
  | succ l ih => rw [network, ih, List.range_succ, List.reverse_append]; rfl

theorem inetwork_foldl (τ : ℕ → ℕ → F) (l : ℕ) (y : ℕ → V) :
    inetwork τ l y = (List.range l).foldl (fun y j => istage (τ j) j y) y := by
  induction l generalizing y with
  | zero => rfl
  | succ l ih => rw [inetwork, ih, List.range_succ, List.foldl_append]; rfl

theorem range_map_rev (l : ℕ) : (List.range l).map (fun s => l - 1 - s) = (List.range l).reverse := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp only [List.getElem_map, List.getElem_range, List.getElem_reverse, List.length_range]

/-- The rows below 2^l from y, the rest from x. -/
def mask (l : ℕ) (x y : ℕ → V) : ℕ → V := fun r => if r < 2 ^ l then y r else x r

variable [DecidableEq F] [CharP F 2] {L : Level F} (hL : Cantor L) {l : ℕ}
  (hl : l ≤ 2 ^ L.logBits) (shift : F)
include hL hl

omit [DecidableEq F] [CharP F 2] hL hl in
theorem stageWith_mask (τ : ℕ → ℕ → F) (inverse : Bool) {j : ℕ} (hj : j < l) (x y : ℕ → V) :
    stageWith τ inverse l j (mask l x y) =
      mask l x (if inverse then istage (τ j) j y else stage (τ j) j y) := by
  have e : 2 ^ l = 2 ^ (l - j - 1) * 2 ^ (j + 1) := by rw [← pow_add]; congr 1; omega
  have hx : ∀ i < 2 ^ (l - j - 1) * 2 ^ (j + 1), mask l x y i = y i := fun i hi => by
    simp [mask, show i < 2 ^ l by rw [e]; exact hi]
  funext r
  by_cases hr : r < 2 ^ l
  · have hr' : r < 2 ^ (l - j - 1) * 2 ^ (j + 1) := by rw [← e]; exact hr
    simp only [stageWith, mask, hr, ↓reduceIte]
    cases inverse
    · exact stage_congr (fun _ _ => rfl) hx hr'
    · exact istage_congr (fun _ _ => rfl) hx hr'
  · simp [stageWith, mask, hr]

/-- A sequence of stage passes is the sequence of stages, on the first 2^l rows. -/
theorem foldlM_stage_pass (inverse : Bool) {width : ℕ} (hw : 0 < width) (js : List ℕ)
    (hjs : ∀ j ∈ js, j < l) (x y : ℕ → V) :
    js.foldlM (fun x j => stage_pass L (canonTw L l shift) inverse width (2 ^ l) j x) (mask l x y) =
      some (mask l x (js.foldl (fun y j => if inverse then istage (twiddle L.cantor shift j) j y
        else stage (twiddle L.cantor shift j) j y) y)) := by
  rw [foldlM_some _ (fun x j => stageWith (twiddle L.cantor shift) inverse l j x) _
    (fun a j _ => stage_pass_eq hL hl shift inverse hw (hjs j ‹_›) a)]
  congr 1
  induction js generalizing y with
  | nil => rfl
  | cons j js ih =>
    simp only [List.foldl_cons]
    rw [stageWith_mask _ inverse (hjs j List.mem_cons_self), ih (fun j hj => hjs j
      (List.mem_cons_of_mem _ hj))]

omit [DecidableEq F] [CharP F 2] hL hl in
theorem mask_self (x : ℕ → V) : mask l x x = x := by funext r; simp [mask]

theorem twiddles_new_canon : Twiddles.new L l shift = some (canonTw L l shift) :=
  Twiddles.new_eq L hl shift

/-- The network of the transform, forward or inverse, with the twiddles of the coset. -/
def lchNet (L : Level F) (shift : F) (inverse : Bool) (l : ℕ) (x : ℕ → V) : ℕ → V :=
  if inverse then inetwork (twiddle L.cantor shift) l x else network (twiddle L.cantor shift) l x

/-- The l stage passes, top first forward and bottom first inverse, are the network. -/
theorem stage_passes_eq (inverse : Bool) {width : ℕ} (hw : 0 < width) (x : ℕ → V) :
    (List.range l).foldlM (fun x step => stage_pass L (canonTw L l shift) inverse width (2 ^ l)
      (if inverse then step else l - 1 - step) x) x = some (mask l x (lchNet L shift inverse l x)) := by
  have hmap := List.foldlM_map (f := fun step => if inverse then step else l - 1 - step)
    (g := fun x j => stage_pass L (canonTw L l shift) inverse width (2 ^ l) j x)
    (l := List.range l) (init := x)
  rw [← hmap]
  conv_lhs => rw [← mask_self (l := l) x]
  rw [foldlM_stage_pass hL hl shift inverse hw _ (fun j hj => by
    simp only [List.mem_map, List.mem_range] at hj; obtain ⟨s, hs, rfl⟩ := hj; split_ifs <;> omega)]
  congr 2
  cases inverse
  · simp [lchNet, network_foldl, range_map_rev]
  · simp [lchNet, inetwork_foldl]

end Plonky3Lean.Proofs.BinaryDft
