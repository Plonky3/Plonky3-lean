module

public import Plonky3Lean.Proofs.BinaryDft.Twiddles
public import Plonky3Lean.Proofs.Dft.Glue

@[expose] public section

/-!
# One stage of the transcribed transform

A slice of whole blocks, its twiddle walked from block to block, runs the butterflies of the stage
on those blocks.

A stage pass cuts the rows into such slices and writes each one back, so it is the stage.
-/

namespace Plonky3Lean.Proofs.BinaryDft

open Finset Plonky3Lean.Spec.BinaryDft p3_binary_dft.mirror p3_binary_dft.domain.mirror
  p3_binary_dft.butterfly.mirror p3_binary_dft.lch.mirror p3_dft.mirror Plonky3Lean.Proofs.Dft

variable {F : Type _} [Field F] [DecidableEq F] {V : Type _} [AddCommGroup V] [Module F V]

/-- The butterfly of block b with twiddle tau(b), forward or inverse. -/
def kop (inverse : Bool) (τ : ℕ → F) : ℕ → ℕ → V → V → V × V :=
  fun b _ => if inverse then ibutterfly (τ b) else butterfly (τ b)

theorem pairOp_eq (inverse : Bool) (t : F) :
    (pairOp inverse t (decide (t = 0)) : V → V → V × V) =
      if inverse then ibutterfly t else butterfly t := by
  funext u v
  by_cases ht : t = 0 <;> cases inverse <;> simp [pairOp, ht, butterfly, ibutterfly, add_comm]

/-- A full block of the slice runs the butterflies of that block, offsets in order. -/
theorem blockButterfly_full (inverse : Bool) {len half i : ℕ} (h : (i + 1) * (2 * half) ≤ len)
    (t : F) (y : ℕ → V) :
    blockButterfly inverse len half i t y =
      some (pairLoop ((List.range half).map fun s => (i, s)) half
        (kop inverse (fun _ => t)) y) := by
  have hb : min (2 * half) (len - i * (2 * half)) = 2 * half := by
    rw [min_eq_left]; rw [add_mul, one_mul] at h; omega
  simp only [blockButterfly, hb, show ¬ 2 * half < half by omega, ↓reduceIte, plain_butterfly,
    show 2 * half - half = half by omega, packed_butterfly, butterfly_values, pairLoop,
    List.foldl_map, pairOp_eq, kop]
  congr 1
  refine congrArg (fun f => List.foldl f y (List.range half)) ?_
  funext acc s
  rw [show i * (2 * half) + half + s = i * (2 * half) + s + half by ring]

omit [DecidableEq F] in
/-- The butterflies of a stage on rows below nb 2^(j+1) are the stage. -/
theorem layer_kop (inverse : Bool) (τ : ℕ → F) (j nb : ℕ) (x : ℕ → V) {i : ℕ}
    (hi : i < nb * 2 ^ (j + 1)) :
    layer (kop inverse τ) (2 ^ j) nb x i =
      if inverse then istage τ j x i else stage τ j x i := by
  have e : 2 * 2 ^ j = 2 ^ (j + 1) := by rw [pow_succ]; ring
  unfold layer
  simp only [e, hi, ↓reduceIte]
  cases inverse <;> simp [kop, stage, istage]

/-! ## The canonical twiddle state of a Cantor level -/

/-- The twiddle state a Cantor level builds for 2^l rows over shift + S_l. -/
def canonTw (L : Level F) (l : ℕ) (shift : F) : Twiddles F :=
  ⟨(List.range l).map fun j => sqAddIter j shift,
    (List.range (l - 1)).map fun r => ∑ q ∈ range (r + 1), L.cantor (q + 1)⟩

section Canon

variable [CharP F 2] {L : Level F} (hL : Cantor L) {l : ℕ} (hl : l ≤ 2 ^ L.logBits) (shift : F)
include hL hl

omit [Field F] [DecidableEq F] [CharP F 2] hL in
theorem blocks_lt {j b : ℕ} (hj : j < l) (hb : b < 2 ^ (l - j - 1)) :
    b * 2 ^ (j + 1) < 2 ^ 2 ^ L.logBits :=
  calc b * 2 ^ (j + 1) < 2 ^ (l - j - 1) * 2 ^ (j + 1) :=
        Nat.mul_lt_mul_of_pos_right hb (Nat.two_pow_pos _)
    _ = 2 ^ l := by rw [← pow_add]; congr 1; omega
    _ ≤ 2 ^ 2 ^ L.logBits := Nat.pow_le_pow_right two_pos hl

omit [DecidableEq F] in
theorem canonTw_at {j b : ℕ} (hj : j < l) (hb : b < 2 ^ (l - j - 1)) :
    (canonTw L l shift).at L j b = some (twiddle L.cantor shift j b) := by
  have hlt := blocks_lt hl hj hb
  rw [Twiddles.at_eq L _ (by simpa [canonTw] using hj)
    (by rw [pow_succ] at hlt; nlinarith [Nat.two_pow_pos j]),
    twiddle_cantor hL shift (by omega) hlt]
  simp [canonTw]

omit [DecidableEq F] in
theorem canonTw_step {j c : ℕ} (hj : j < l) (hc : 0 < c) (hcl : c < 2 ^ (l - j - 1)) :
    (canonTw L l shift).step c =
      some (∑ q ∈ range (trailingZeros c + 1), L.cantor (q + 1)) ∧
    twiddle L.cantor shift j c =
      twiddle L.cantor shift j (c - 1) + ∑ q ∈ range (trailingZeros c + 1), L.cantor (q + 1) := by
  have htz : trailingZeros c < l - 1 := trailingZeros_lt hc
    (lt_of_lt_of_le hcl (Nat.pow_le_pow_right two_pos (by omega)))
  refine ⟨by simp [Twiddles.step, canonTw, htz], ?_⟩
  rw [twiddle_cantor hL shift (by omega) (blocks_lt hl hj hcl),
    twiddle_cantor hL shift (by omega) (blocks_lt hl hj (by omega)), point_step _ hc, add_assoc]

/-- A slice of cnt whole blocks, its twiddle walked from block first, runs the stage's butterflies there. -/
theorem walkBlocks_eq (inverse : Bool) {j first cnt : ℕ} (hj : j < l) (hcnt : 0 < cnt)
    (hfc : first + cnt ≤ 2 ^ (l - j - 1)) (y : ℕ → V) :
    walkBlocks L (canonTw L l shift) inverse j first (cnt * (2 * 2 ^ j)) (2 ^ j) y =
      some (layer (kop inverse fun b => twiddle L.cantor shift j (first + b)) (2 ^ j) cnt y) := by
  set τ := fun b => twiddle L.cantor shift j (first + b) with hτ
  set S := fun c => ∑ q ∈ range (trailingZeros c + 1), L.cantor (q + 1)
  have hm : 0 < 2 * 2 ^ j := by positivity
  have hcount : (cnt * (2 * 2 ^ j) + 2 * 2 ^ j - 1) / (2 * 2 ^ j) = cnt := by
    rw [show cnt * (2 * 2 ^ j) + 2 * 2 ^ j - 1 = (2 * 2 ^ j - 1) + cnt * (2 * 2 ^ j) by omega,
      Nat.add_mul_div_right _ _ hm, Nat.div_eq_of_lt (by omega), zero_add]
  let blk : F → ℕ → (ℕ → V) → ℕ → V := fun t i y =>
    pairLoop ((List.range (2 ^ j)).map fun s => (i, s)) (2 ^ j) (kop inverse fun _ => t) y
  let g : (ℕ → V) × F → ℕ → (ℕ → V) × F := fun acc i =>
    if i = 0 then (blk acc.2 i acc.1, acc.2) else (blk (acc.2 + S (first + i)) i acc.1, acc.2 + S (first + i))
  unfold walkBlocks
  rw [canonTw_at hL hl shift hj (by omega), hcount]
  simp only [Option.bind_eq_bind, Option.bind_some]
  rw [foldlM_some _ g _ (fun acc i hi => by
    have hi' := List.mem_range.mp hi
    by_cases h0 : i = 0
    · subst h0
      simp only [↓reduceIte, g, Option.pure_def, Option.bind_some]
      rw [blockButterfly_full _ (by nlinarith)]; rfl
    · simp only [h0, ↓reduceIte, g]
      rw [(canonTw_step hL hl shift hj (by omega) (by omega)).1]
      simp only [Option.pure_def, Option.bind_some]
      rw [blockButterfly_full _ (by nlinarith)]; rfl)]
  -- the walk carries the twiddle of the block it is on
  have walk : ∀ k, 1 ≤ k → k ≤ cnt →
      (List.range k).foldl g (y, τ 0) =
        ((List.range k).foldl (fun y i => blk (τ i) i y) y, τ (k - 1)) := by
    intro k hk1 hk
    induction k with
    | zero => omega
    | succ k ih =>
      rcases Nat.eq_zero_or_pos k with rfl | hk0
      · simp [g, hτ]
      rw [List.range_succ, List.foldl_append, List.foldl_append, ih hk0 (by omega)]
      simp only [List.foldl_cons, List.foldl_nil, g, show k ≠ 0 by omega, ↓reduceIte,
        Nat.add_sub_cancel]
      have := (canonTw_step hL hl shift hj (c := first + k) (by omega) (by omega)).2
      rw [show first + k - 1 = first + (k - 1) by omega] at this
      have this' : τ (k - 1) + S (first + k) = τ k := this.symm
      rw [this']
  have h0 : twiddle L.cantor shift j first = τ 0 := by simp [hτ]
  simp only [Option.pure_def, h0, Option.bind_some]
  rw [walk cnt hcnt le_rfl, ← pairLoop_blocks cnt (2 ^ j) (Nat.two_pow_pos j)]
  congr 1
  simp only [pairLoop, blocks, List.foldl_flatMap, List.foldl_map, blk, kop]

omit [DecidableEq F] [CharP F 2] hL hl in
theorem stage_slice (τ : ℕ → F) (j c : ℕ) (x : ℕ → V) (r : ℕ) :
    stage (fun b => τ (c + b)) j (slice x (c * 2 ^ (j + 1))) r = stage τ j x (r + c * 2 ^ (j + 1)) := by
  rw [stage_offset]; congr 1 <;> funext b <;> simp [slice, add_comm]

omit [DecidableEq F] [CharP F 2] hL hl in
theorem istage_slice (τ : ℕ → F) (j c : ℕ) (x : ℕ → V) (r : ℕ) :
    istage (fun b => τ (c + b)) j (slice x (c * 2 ^ (j + 1))) r =
      istage τ j x (r + c * 2 ^ (j + 1)) := by
  rw [istage_offset]; congr 1 <;> funext b <;> simp [slice, add_comm]

/-- Stage j with twiddles tau_j, forward or inverse, on the first 2^l rows. -/
def stageWith (τ : ℕ → ℕ → F) (inverse : Bool) (l j : ℕ) (x : ℕ → V) : ℕ → V :=
  fun r => if r < 2 ^ l then
    (if inverse then istage (τ j) j x r else stage (τ j) j x r) else x r

/-- The stage of the twiddles W^_j at the block points, forward or inverse, on the first 2^l rows. -/
abbrev stageAt (L : Level F) (shift : F) (inverse : Bool) (l j : ℕ) (x : ℕ → V) : ℕ → V :=
  stageWith (twiddle L.cantor shift) inverse l j x

/-- A stage pass is the stage, whatever the tasks it is cut into. -/
theorem stage_pass_eq (inverse : Bool) {width j : ℕ} (hw : 0 < width) (hj : j < l)
    (x : ℕ → V) :
    stage_pass L (canonTw L l shift) inverse width (2 ^ l) j x =
      some (stageAt L shift inverse l j x) := by
  unfold stage_pass
  dsimp only
  simp only [show 2 ^ j * width ≠ 0 by positivity, ↓reduceIte]
  set τ := twiddle L.cantor shift j
  set P := max (BUTTERFLY_GRAIN / (2 ^ j * width)) 1 with hP
  have hP1 : 1 ≤ P := le_max_right _ _
  set B := 2 * 2 ^ j with hB
  have hB0 : 0 < B := by positivity
  set nb := 2 ^ (l - j - 1)
  have hn : 2 ^ l = nb * B := by
    rw [hB, ← mul_assoc, mul_comm _ 2, ← pow_succ', ← pow_add]; congr 1; omega
  set T := P * B
  have hT0 : 0 < T := Nat.mul_pos hP1 hB0
  -- task k covers blocks k P .. k P + cnt k - 1, rows k T .. k T + cnt k B - 1
  let cnt := fun k => min P (nb - k * P)
  have hlen : ∀ k, min T (2 ^ l - k * T) = cnt k * B := fun k => by
    simp only [cnt, T, hn, show k * (P * B) = k * P * B by ring, ← Nat.sub_mul,
      Nat.mul_min_mul_right]
  have hB' : B = 2 ^ (j + 1) := by rw [hB, pow_succ]; ring
  set S : ℕ → V := fun r => if inverse then istage τ j x r else stage τ j x r
  let g : (ℕ → V) → ℕ → ℕ → V := fun acc k =>
    writeBack acc (k * T) (cnt k * B)
      (layer (kop inverse fun b => τ (k * P + b)) (2 ^ j) (cnt k) (slice acc (k * T)))
  set ntasks := (2 ^ l + T - 1) / T
  have htasks : ∀ k, k < ntasks ↔ k * T < 2 ^ l := fun k => by
    rw [← Nat.add_one_le_iff, Nat.le_div_iff_mul_le hT0, add_mul, one_mul]; omega
  have hk_lt : ∀ k < ntasks, k * P < nb := fun k hk => by
    have h := (htasks k).mp hk
    rw [hn, show k * T = k * P * B by ring] at h
    exact Nat.lt_of_mul_lt_mul_right h
  -- each step of the fold transforms one task's rows
  rw [foldlM_some _ g _ (fun acc k hk => by
    have hk' := hk_lt k (List.mem_range.mp hk)
    rw [hlen k, walkBlocks_eq hL hl shift inverse hj (by simp [cnt]; omega) (by simp [cnt]; omega)]
    rfl)]
  congr 1
  -- after k tasks, the rows below k T are those of the stage
  have inv : ∀ k ≤ ntasks, (List.range k).foldl g x =
      fun r => if r < k * T ∧ r < 2 ^ l then S r else x r := by
    intro k hk
    induction k with
    | zero => funext r; simp
    | succ k ih =>
      have hkT := (htasks k).mp (by omega)
      have hk' := hk_lt k (by omega)
      rw [List.range_succ, List.foldl_append, ih (by omega)]
      funext r
      simp only [List.foldl_cons, List.foldl_nil, g, writeBack]
      have hend : k * T + cnt k * B = min ((k + 1) * T) (2 ^ l) := by
        rw [← hlen k, add_mul, one_mul]; omega
      by_cases hr : k * T ≤ r ∧ r < k * T + cnt k * B
      · simp only [hr, and_self, ↓reduceIte]
        have hslice : slice (fun r => if r < k * T ∧ r < 2 ^ l then S r else x r) (k * T) =
            slice x (k * T) := by
          funext q; simp [slice]
        rw [hslice, layer_kop inverse _ j (cnt k) _ (by rw [← hB']; omega)]
        have hc : k * T = k * P * 2 ^ (j + 1) := by rw [← hB']; ring
        have hcond : r < (k + 1) * T ∧ r < 2 ^ l := by
          have h := hend ▸ hr.2
          exact ⟨lt_of_lt_of_le h (min_le_left _ _), lt_of_lt_of_le h (min_le_right _ _)⟩
        simp only [hcond, and_self, ↓reduceIte, S, hc]
        obtain ⟨r', rfl⟩ : ∃ r', r = r' + k * P * 2 ^ (j + 1) := ⟨r - k * P * 2 ^ (j + 1), by omega⟩
        rw [Nat.add_sub_cancel]
        cases inverse
        · simp only [Bool.false_eq_true, ↓reduceIte, stage_slice]
        · simp only [↓reduceIte, istage_slice]
      · simp only [hr, ↓reduceIte]
        congr 1
        apply propext
        constructor
        · rintro ⟨h1, h2⟩; exact ⟨by nlinarith, h2⟩
        · rintro ⟨h1, h2⟩
          refine ⟨?_, h2⟩
          by_contra h
          exact hr ⟨by omega, by rw [hend]; refine lt_min (by nlinarith) h2⟩
  rw [inv ntasks le_rfl]
  funext r
  simp only [stageAt, stageWith, S]
  by_cases hr : r < 2 ^ l
  · have : r < ntasks * T := by
      by_contra h
      have := (htasks ntasks).not.mp (lt_irrefl _)
      omega
    simp [hr, this, τ]
  · simp [hr]

end Canon

end Plonky3Lean.Proofs.BinaryDft
