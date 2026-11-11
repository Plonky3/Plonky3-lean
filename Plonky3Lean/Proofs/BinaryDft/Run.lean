module

public import Plonky3Lean.Proofs.BinaryDft.Transform

@[expose] public section

/-!
# The blocked schedule

On the serial pool the schedule stages nothing.

The stages above the tile run one plain pass each.

The bottom stages run inside each contiguous tile, as that tile's own network with renumbered blocks.

Both orders compute the network.
-/

set_option linter.unusedSectionVars false

namespace Plonky3Lean.Proofs.BinaryDft

open Finset Plonky3Lean.Spec.BinaryDft p3_binary_dft.mirror p3_binary_dft.domain.mirror
  p3_binary_dft.butterfly.mirror p3_binary_dft.lch.mirror p3_dft.mirror Plonky3Lean.Proofs.Dft

variable {F : Type _} [Field F] {V : Type _} [AddCommGroup V] [Module F V]

/-- Stages in any order, on the first 2^l rows. -/
theorem foldl_stageWith_mask (τ : ℕ → ℕ → F) (inverse : Bool) {l : ℕ} (js : List ℕ)
    (hjs : ∀ j ∈ js, j < l) (x y : ℕ → V) :
    js.foldl (fun x j => stageWith τ inverse l j x) (mask l x y) =
      mask l x (js.foldl (fun y j => if inverse then istage (τ j) j y else stage (τ j) j y) y) := by
  induction js generalizing y with
  | nil => rfl
  | cons j js ih =>
    simp only [List.foldl_cons]
    rw [stageWith_mask _ inverse (hjs j List.mem_cons_self), ih (fun j hj => hjs j
      (List.mem_cons_of_mem _ hj))]

/-- The butterflies of a stage on all 2^(t-j-1) blocks of a tile are the stage on its 2^t rows. -/
theorem layer_stageWith (τ : ℕ → ℕ → F) (inverse : Bool) {t j : ℕ} (hj : j < t) (y : ℕ → V) :
    layer (kop inverse (τ j)) (2 ^ j) (2 ^ (t - j - 1)) y = stageWith τ inverse t j y := by
  have e : 2 ^ (t - j - 1) * (2 * 2 ^ j) = 2 ^ t := by
    rw [← pow_succ', ← pow_add]; congr 1; omega
  funext r
  by_cases hr : r < 2 ^ t
  · rw [layer_kop inverse _ j _ _ (by rw [pow_succ]; linarith [e])]
    simp [stageWith, hr]
  · rw [layer_of_ge _ _ _ _ (by omega)]
    simp [stageWith, hr]

theorem network_split (τ : ℕ → ℕ → F) {t l : ℕ} (ht : t ≤ l) (y : ℕ → V) :
    network τ l y = network τ t
      (((List.range (l - t)).map (t + ·)).reverse.foldl (fun y j => stage (τ j) j y) y) := by
  rw [network_foldl, network_foldl, show l = t + (l - t) by omega, List.range_add,
    List.reverse_append, List.foldl_append, Nat.add_sub_cancel_left]

theorem inetwork_split (τ : ℕ → ℕ → F) {t l : ℕ} (ht : t ≤ l) (y : ℕ → V) :
    inetwork τ l y =
      ((List.range (l - t)).map (t + ·)).foldl (fun y j => istage (τ j) j y) (inetwork τ t y) := by
  rw [inetwork_foldl, inetwork_foldl, show l = t + (l - t) by omega, List.range_add,
    List.foldl_append, Nat.add_sub_cancel_left]

omit [AddCommGroup V] [Module F V] in
theorem mask_mask (l : ℕ) (x z w : ℕ → V) : mask l (mask l x z) w = mask l x w := by
  funext r; simp only [mask]; split_ifs <;> rfl

variable [DecidableEq F] [CharP F 2] {L : Level F} (hL : Cantor L) {l : ℕ}
  (hl : l ≤ 2 ^ L.logBits) (shift : F)
include hL hl

/-- The twiddles of tile index: block b of stage j is global block index 2^(t-j-1) + b. -/
def tileTw (L : Level F) (shift : F) (t index : ℕ) : ℕ → ℕ → F :=
  fun j b => twiddle L.cantor shift j (index * 2 ^ (t - 1 - j) + b)

/-- A tile runs its own network, forward or inverse, with the tile's twiddles. -/
theorem tile_stages_eq (inverse : Bool) {t index : ℕ} (ht : t ≤ l)
    (hidx : (index + 1) * 2 ^ t ≤ 2 ^ l) (y : ℕ → V) :
    tile_stages L (canonTw L l shift) inverse (2 ^ t) t 0 index y =
      some (mask t y (if inverse then inetwork (tileTw L shift t index) t y
        else network (tileTw L shift t index) t y)) := by
  unfold tile_stages
  have hstep : ∀ a, ∀ step ∈ List.range t,
      walkBlocks L (canonTw L l shift) inverse (0 + if inverse then step else t - 1 - step)
        (index * 2 ^ (t - 1 - if inverse then step else t - 1 - step)) (2 ^ t)
        (2 ^ if inverse then step else t - 1 - step) a =
      some (stageWith (V := V) (tileTw L shift t index) inverse t
        (if inverse then step else t - 1 - step) a) := by
    intro a step hs
    have hs' := List.mem_range.mp hs
    set jj := if inverse then step else t - 1 - step with hjj
    have hjt : jj < t := by rw [hjj]; split_ifs <;> omega
    have e : 2 ^ t = 2 ^ (t - jj - 1) * (2 * 2 ^ jj) := by
      rw [← pow_succ', ← pow_add]; congr 1; omega
    have hfc : index * 2 ^ (t - 1 - jj) + 2 ^ (t - jj - 1) ≤ 2 ^ (l - jj - 1) := by
      have h2 : 2 ^ (l - jj - 1) = 2 ^ (l - t) * 2 ^ (t - jj - 1) := by
        rw [← pow_add]; congr 1; omega
      have h3 : index + 1 ≤ 2 ^ (l - t) := by
        have : 2 ^ l = 2 ^ (l - t) * 2 ^ t := by rw [← pow_add]; congr 1; omega
        rw [this] at hidx; exact Nat.le_of_mul_le_mul_right hidx (Nat.two_pow_pos t)
      rw [h2, show t - 1 - jj = t - jj - 1 by omega]; nlinarith [Nat.two_pow_pos (t - jj - 1)]
    rw [zero_add, e, walkBlocks_eq hL hl shift inverse (by omega) (Nat.two_pow_pos _) hfc,
      ← layer_stageWith _ inverse hjt]
    rfl
  rw [foldlM_some _ _ _ hstep]
  congr 1
  have hmap := List.foldl_map (f := fun step => if inverse then step else t - 1 - step)
    (g := fun x j => stageWith (tileTw L shift t index) inverse t j x) (l := List.range t) (init := y)
  rw [← hmap]
  conv_lhs => rw [← mask_self (l := t) y]
  rw [foldl_stageWith_mask _ inverse _ (fun j hj => by
    simp only [List.mem_map, List.mem_range] at hj; obtain ⟨s, hs, rfl⟩ := hj; split_ifs <;> omega)]
  cases inverse
  · simp [network_foldl, range_map_rev]
  · simp [inetwork_foldl]

omit [DecidableEq F] [CharP F 2] hL hl in
theorem tile_offset (inverse : Bool) (t k : ℕ) (x : ℕ → V) (r : ℕ) :
    (if inverse then inetwork (tileTw L shift t k) t (slice x (k * 2 ^ t)) r
      else network (tileTw L shift t k) t (slice x (k * 2 ^ t)) r) =
    (if inverse then inetwork (twiddle L.cantor shift) t x (r + k * 2 ^ t)
      else network (twiddle L.cantor shift) t x (r + k * 2 ^ t)) := by
  have hs : slice x (k * 2 ^ t) = fun q => x (q + k * 2 ^ t) := by funext q; simp [slice, add_comm]
  have ht : tileTw L shift t k = fun j b => twiddle L.cantor shift j (b + k * 2 ^ (t - 1 - j)) := by
    funext j b; simp [tileTw, add_comm]
  cases inverse
  · simp [network_offset, hs, ht]
  · simp [inetwork_offset, hs, ht]

/-- The contiguous tiles together run the bottom t stages of the network over all 2^l rows. -/
theorem deep_tiles_eq (inverse : Bool) {t : ℕ} (ht : t ≤ l) (x : ℕ → V) :
    deep_tiles L (canonTw L l shift) inverse (2 ^ l) t x =
      some (mask l x (if inverse then inetwork (twiddle L.cantor shift) t x
        else network (twiddle L.cantor shift) t x)) := by
  set N : ℕ → V := fun r => if inverse then inetwork (twiddle L.cantor shift) t x r
    else network (twiddle L.cantor shift) t x r
  have hT := Nat.two_pow_pos t
  have hn : 2 ^ l = 2 ^ (l - t) * 2 ^ t := by rw [← pow_add]; congr 1; omega
  have hcount : (2 ^ l + 2 ^ t - 1) / 2 ^ t = 2 ^ (l - t) := by
    rw [hn, show 2 ^ (l - t) * 2 ^ t + 2 ^ t - 1 = (2 ^ t - 1) + 2 ^ (l - t) * 2 ^ t by omega,
      Nat.add_mul_div_right _ _ hT, Nat.div_eq_of_lt (by omega), zero_add]
  have hlen : ∀ k < 2 ^ (l - t), min (2 ^ t) (2 ^ l - k * 2 ^ t) = 2 ^ t := fun k hk => by
    rw [min_eq_left]; rw [hn]
    have : (k + 1) * 2 ^ t ≤ 2 ^ (l - t) * 2 ^ t := Nat.mul_le_mul_right _ hk
    rw [add_mul, one_mul] at this; omega
  let g : (ℕ → V) → ℕ → ℕ → V := fun acc k =>
    writeBack acc (k * 2 ^ t) (2 ^ t) (mask t (slice acc (k * 2 ^ t))
      (if inverse then inetwork (tileTw L shift t k) t (slice acc (k * 2 ^ t))
        else network (tileTw L shift t k) t (slice acc (k * 2 ^ t))))
  unfold deep_tiles
  rw [hcount, foldlM_some _ g _ (fun acc k hk => by
    have hk' := List.mem_range.mp hk
    simp only [hlen k hk']
    rw [tile_stages_eq hL hl shift inverse ht (by
      rw [hn]; exact Nat.mul_le_mul_right _ hk')]
    rfl)]
  congr 1
  have inv : ∀ k ≤ 2 ^ (l - t), (List.range k).foldl g x =
      fun r => if r < k * 2 ^ t then N r else x r := by
    intro k hk
    induction k with
    | zero => funext r; simp
    | succ k ih =>
      rw [List.range_succ, List.foldl_append, ih (by omega)]
      funext r
      simp only [List.foldl_cons, List.foldl_nil, g, writeBack]
      by_cases hr : k * 2 ^ t ≤ r ∧ r < k * 2 ^ t + 2 ^ t
      · have hslice : slice (fun r => if r < k * 2 ^ t then N r else x r) (k * 2 ^ t) =
            slice x (k * 2 ^ t) := by funext q; simp [slice]
        obtain ⟨r', rfl⟩ : ∃ r', r = r' + k * 2 ^ t := ⟨r - k * 2 ^ t, by omega⟩
        simp only [hr, and_self, ↓reduceIte, hslice, Nat.add_sub_cancel, mask,
          show r' < 2 ^ t by omega, show r' + k * 2 ^ t < (k + 1) * 2 ^ t by rw [add_mul]; omega]
        have := tile_offset (L := L) shift inverse t k x r'
        cases inverse <;> simpa [N] using this
      · simp only [hr, ↓reduceIte]
        congr 1
        apply propext
        rw [add_mul, one_mul]
        omega
  rw [inv _ le_rfl, ← hn]
  funext r
  cases inverse <;> simp [mask, N]

omit [DecidableEq F] [CharP F 2] hL hl in
theorem cut_serial (bytes width : ℕ) :
    (Cut.new (Schedule.new bytes width l) l).group = 1 := by
  simp [Cut.new, Schedule.new, Schedule.for_workers]

/-- On the serial pool the blocked schedule is the network. -/
theorem run_eq (inverse : Bool) {width bytes : ℕ} (hw : 0 < width) (x : ℕ → V) :
    run L (canonTw L l shift) inverse width l (Schedule.new bytes width l) x =
      some (mask l x (lchNet L shift inverse l x)) := by
  set c := Cut.new (Schedule.new bytes width l) l with hc
  have hg : c.group = 1 := cut_serial bytes width
  have htile : c.tile ≤ l := min_le_right _ _
  have hgroups : c.groups = l - c.tile := by
    simp only [hc, Cut.new] at hg ⊢; rw [hg]; simp
  have hpass : ∀ a : ℕ → V, ∀ g ∈ List.range c.groups, ∀ inv : Bool,
      group_pass L (canonTw L l shift) inv width (2 ^ l) (c.bounds g) a =
        stage_pass L (canonTw L l shift) inv width (2 ^ l) (c.tile + g) a := by
    intro a g hg' inv
    have hg'' := List.mem_range.mp hg'
    have hln : c.log_n = l := rfl
    have hb : c.bounds g = (c.tile + g, c.tile + g + 1) := by
      simp only [Cut.bounds, hg, mul_one, hln]; congr 1; rw [min_eq_left]; omega
    simp [group_pass, hb]
  have hjs : ∀ j ∈ (List.range c.groups).map (c.tile + ·), j < l := by
    intro j hj; simp only [List.mem_map, List.mem_range] at hj; omega
  have hlist : ∀ (inv : Bool) (js : List ℕ) (hjs' : ∀ g ∈ js, g ∈ List.range c.groups) (a : ℕ → V),
      js.foldlM (fun x g => group_pass L (canonTw L l shift) inv width (2 ^ l) (c.bounds g) x) a =
        (js.map (c.tile + ·)).foldlM
          (fun x j => stage_pass L (canonTw L l shift) inv width (2 ^ l) j x) a := by
    intro inv js hjs' a
    induction js generalizing a with
    | nil => rfl
    | cons g js ih =>
      simp only [List.foldlM_cons, List.map_cons]
      rw [hpass a g (hjs' g List.mem_cons_self) inv]
      cases stage_pass L (canonTw L l shift) inv width (2 ^ l) (c.tile + g) a with
      | none => rfl
      | some b => exact ih (fun g hg => hjs' g (List.mem_cons_of_mem _ hg)) b
  have e : 2 ^ (l - c.tile) * 2 ^ c.tile = 2 ^ l := by rw [← pow_add]; congr 1; omega
  unfold run
  simp only [← hc]
  have hfold := fun (inv : Bool) (js : List ℕ) (h : ∀ j ∈ js, j < l) =>
    (mask_self (l := l) x) ▸ foldlM_stage_pass hL hl shift inv hw js h x x
  cases inverse
  · simp only [Bool.false_eq_true, ↓reduceIte, forward_below, Option.bind_eq_bind]
    rw [hlist false _ (fun g hg => by simpa using hg), hfold false _ (fun j hj => hjs j (by
        simpa [List.map_reverse] using hj)), Option.bind_some]
    have hz : ((List.range c.groups).reverse.map (c.tile + ·)).foldl
        (fun y j => if false = true then istage (twiddle L.cantor shift j) j y
          else stage (twiddle L.cantor shift j) j y) x =
        ((List.range (l - c.tile)).map (c.tile + ·)).reverse.foldl
          (fun y j => stage (twiddle L.cantor shift j) j y) x := by
      simp [hgroups, List.map_reverse]
    rw [hz]
    split_ifs with h0
    · rw [deep_tiles_eq hL hl shift false htile, mask_mask]
      congr 1
      funext r
      simp only [mask, lchNet, Bool.false_eq_true, ↓reduceIte]
      split_ifs with hr
      · rw [network_split _ htile]
        exact network_congr (c := 2 ^ (l - c.tile)) (fun _ _ _ _ => rfl)
          (fun i hi => by simp [mask, show i < 2 ^ l by omega]) (by omega)
      · rfl
    · have h0' : c.tile = 0 := by omega
      simp only [Option.pure_def, Option.some.injEq, lchNet, Bool.false_eq_true, ↓reduceIte]
      rw [network_split _ htile, h0']
      rfl
  · simp only [↓reduceIte, Option.bind_eq_bind]
    have hz : ∀ y : ℕ → V, ((List.range c.groups).map (c.tile + ·)).foldl
        (fun y j => if true = true then istage (twiddle L.cantor shift j) j y
          else stage (twiddle L.cantor shift j) j y) y =
        ((List.range (l - c.tile)).map (c.tile + ·)).foldl
          (fun y j => istage (twiddle L.cantor shift j) j y) y := by
      intro y; simp [hgroups]
    split_ifs with h0
    · rw [deep_tiles_eq hL hl shift true htile, Option.bind_some, hlist true _ (fun g hg => hg),
        foldlM_stage_pass hL hl shift true hw _ hjs, hz, lchNet, inetwork_split _ htile]
      simp
    · have h0' : c.tile = 0 := by omega
      rw [Option.pure_def, Option.bind_some, hlist true _ (fun g hg => hg), hfold true _ hjs, hz,
        lchNet, inetwork_split _ htile, h0']
      rfl

/-- The transform of 2^l rows is the network, on either branch of its size test. -/
theorem transform_eq (inverse : Bool) {width : ℕ} (hw : 0 < width) (x : ℕ → V) :
    transform L inverse width (2 ^ l) shift x = some (mask l x (lchNet L shift inverse l x)) := by
  unfold transform
  simp only [show width ≠ 0 by omega, ↓reduceIte, log2Strict_pow, Option.bind_eq_bind,
    Option.bind_some, show ¬ 2 ^ L.logBits < l by omega, twiddles_new_canon hL hl]
  by_cases hs : 2 ^ l * width * L.bytes ≤ DEEP_TILE_BYTES
  · simp only [hs, ↓reduceIte]; exact stage_passes_eq hL hl shift inverse hw x
  · simp only [hs, ↓reduceIte]; exact run_eq hL hl shift inverse hw x

end Plonky3Lean.Proofs.BinaryDft
