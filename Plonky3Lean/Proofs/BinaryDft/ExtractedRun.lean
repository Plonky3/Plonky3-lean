module

public import Plonky3Lean.Proofs.BinaryDft.ExtractedLch
public import Plonky3Lean.Lib.Scalar.Signed

@[expose] public section

/-!
# The extracted transform

The extracted schedule, tile pass and blocked run are the transcribed ones.

So the extracted forward and inverse transforms return what the transcribed transform returns.

They panic exactly when it does.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open Plonky3Lean.Lib Plonky3Lean.Spec.BinaryDft p3_binary_dft.mirror

set_option linter.unusedSectionVars false

namespace Plonky3Lean.Proofs.BinaryDft

variable {F : Type} [Field F]

/-! ## Iterating a range backwards -/

theorem range_next_back_lt (i : Std.Usize) {K : ℕ} (hK : K ≤ Usize.max) (h : i.val < K) :
    core.IteratorRange.next_back core.Usize.Insts.CoreIterRangeStep { start := i, «end» := uz K } =
      .ok (core.option.Option.Some (uz (K - 1)), { start := i, «end» := uz (K - 1) }) := by
  unfold core.IteratorRange.next_back
  have h1 : (1#usize : Std.Usize).val = 1 := rfl
  have hu : uoverflowing_sub (uz K) 1#usize = (uz (K - 1), false) := by
    have hKv := uz_val hK
    have hle : (1#usize : Std.Usize).bv ≤ (uz K).bv := by
      rw [BitVec.le_def, UScalar.bv_toNat, UScalar.bv_toNat, h1, hKv]; omega
    refine Prod.ext (UScalar.eq_of_val_eq ?_) (by simp [uoverflowing_sub, uz_val hK, h1]; omega)
    rw [uz_val (show K - 1 ≤ Usize.max by omega)]
    calc (uoverflowing_sub (uz K) 1#usize).1.val
        = (@HSub.hSub (BitVec UScalarTy.Usize.numBits) _ _ _ (uz K).bv (1#usize : Std.Usize).bv).toNat := rfl
      _ = (uz K).bv.toNat - (1#usize : Std.Usize).bv.toNat := BitVec.toNat_sub_of_le hle
      _ = K - 1 := by rw [UScalar.bv_toNat, UScalar.bv_toNat, hKv, h1]
  simp [core.Usize.Insts.CoreCmpPartialOrdUsize, core.mkUPartialOrd, uz_val hK, compare_lt_iff_lt.mpr h,
    core.Usize.Insts.CoreIterRangeStep.backward_checked,
    core.convert.TryFromUTInfallible.Blanket.try_from, core.convert.From.Blanket.from,
    core.num.Usize.checked_sub, core.num.Usize.overflowing_sub,
    rust_primitives.arithmetic.overflowing_sub_usize, hu]

/-! ## Base-two logarithms -/

theorem u32_sub_ok (x y : Std.U32) (h : y.val ≤ x.val) :
    ∃ z : Std.U32, (x - y : RustM Std.U32) = .ok z ∧ z.val = x.val - y.val := by
  obtain ⟨z, hz, hv⟩ := spec_imp_exists (UScalar.sub_bv_spec (x := x) (y := y) h)
  exact ⟨z, hz, hv.1⟩

theorem numBits_le64 : UScalarTy.Usize.numBits ≤ 64 := by
  rw [UScalarTy.Usize_numBits_eq]; rcases System.Platform.numBits_eq with e | e <;> omega

theorem log_lt_numBits (x : Std.Usize) (hx : x.val ≠ 0) : Nat.log 2 x.val < UScalarTy.Usize.numBits :=
  (Nat.log_lt_iff_lt_pow one_lt_two hx).mpr x.hBounds

theorem lz_eq (x : Std.Usize) (hx : x.val ≠ 0) :
    ∃ v : Std.U32, core.num.Usize.leading_zeros x = .ok v ∧
      v.val = UScalarTy.Usize.numBits - Nat.log 2 x.val - 1 := by
  have h0 : x.bv ≠ 0 := fun h => hx (by simp [UScalar.val, h])
  refine ⟨_, rfl, ?_⟩
  simp only [Aeneas.Std.core.num.Usize.leading_zeros, BitVec.leadingZeros, h0, ↓reduceIte]
  show (BitVec.ofNat 32 (System.Platform.numBits - Nat.log 2 x.bv.toNat - 1)).toNat = _
  have := numBits_le64
  rw [BitVec.toNat_ofNat, UScalar.bv_toNat, ← UScalarTy.Usize_numBits_eq, Nat.mod_eq_of_lt (by omega)]

theorem lz_zero (x : Std.Usize) (hx : x.val = 0) :
    ∃ v : Std.U32, core.num.Usize.leading_zeros x = .ok v ∧ v.val = UScalarTy.Usize.numBits := by
  have h0 : x.bv = 0 := by
    apply BitVec.eq_of_toNat_eq; rw [UScalar.bv_toNat, hx]; rfl
  refine ⟨_, rfl, ?_⟩
  simp only [Aeneas.Std.core.num.Usize.leading_zeros, BitVec.leadingZeros, h0, ↓reduceIte]
  show (BitVec.ofNat 32 System.Platform.numBits).toNat = _
  have := numBits_le64
  rw [BitVec.toNat_ofNat, ← UScalarTy.Usize_numBits_eq, Nat.mod_eq_of_lt (by omega)]

theorem bits_val : (core.num.Usize.BITS : Std.U32).val = UScalarTy.Usize.numBits := by
  simp [core.num.Usize.BITS]

theorem cast_u32_usize (v : Std.U32) (h : v.val ≤ 64) : (UScalar.cast .Usize v) = uz v.val :=
  UScalar.eq_of_val_eq (by
    rw [uz_val (by have := usize_max_ge (n := 64) (by norm_num); rw [UScalar.max_USize_eq] at this; omega),
      UScalar.cast_val_mod_pow_greater_numBits_eq _ _ (by
        rcases System.Platform.numBits_eq with e | e <;> simp [UScalarTy.numBits, e])])

/-- The floor of log_2, with log_2 0 taken as 0. -/
theorem log2_floor_eq (n : Std.Usize) : p3_util.log2_floor_usize n = .ok (uz (Nat.log 2 n.val)) := by
  unfold p3_util.log2_floor_usize
  by_cases h0 : n.val = 0
  · have : n = 0#usize := UScalar.eq_of_val_eq (by rw [h0]; rfl)
    subst this
    simp only [ite_true, Nat.log_zero_right, h0]
    exact congrArg RustM.ok (UScalar.eq_of_val_eq (by rw [uz_val (by scalar_tac)]; rfl))
  · rw [ite_of_neg (fun h => h0 (by rw [h]; rfl))]
    have hl := log_lt_numBits n h0
    have h64 := numBits_le64
    have h1 : (1#u32 : Std.U32).val = 1 := rfl
    obtain ⟨z, hz, hzv⟩ := u32_sub_ok core.num.Usize.BITS 1#u32 (by rw [bits_val, h1]; omega)
    obtain ⟨v, hv, hvv⟩ := lz_eq n h0
    obtain ⟨y, hy, hyv⟩ := u32_sub_ok z v (by rw [hzv, hvv, bits_val, h1]; omega)
    rw [hz, bind_ok, hv, bind_ok, hy, bind_ok, cast_u32_usize y (by rw [hyv, hzv, hvv, bits_val, h1]; omega),
      hyv, hzv, hvv, bits_val, h1]
    congr 2; omega

theorem clog_eq_log_pred {n : ℕ} (hn : 2 ≤ n) : Nat.clog 2 n = Nat.log 2 (n - 1) + 1 := by
  apply le_antisymm
  · rw [Nat.clog_le_iff_le_pow one_lt_two]
    have := Nat.lt_pow_succ_log_self one_lt_two (n - 1)
    omega
  · rw [Nat.succ_le_iff, Nat.lt_clog_iff_pow_lt one_lt_two]
    have := Nat.pow_log_le_self 2 (show n - 1 ≠ 0 by omega)
    omega

/-- The ceiling of log_2, with log_2 0 taken as 0. -/
theorem log2_ceil_eq (n : Std.Usize) : p3_util.log2_ceil_usize n = .ok (uz (Nat.clog 2 n.val)) := by
  unfold p3_util.log2_ceil_usize
  have h64 := numBits_le64
  rw [show core.num.Usize.saturating_sub_exposed n 1#usize = .ok (uz (n.val - 1)) from rfl, bind_ok]
  have hum : n.val - 1 ≤ Usize.max := by scalar_tac
  by_cases h1 : n.val ≤ 1
  · obtain ⟨v, hv, hvv⟩ := lz_zero (uz (n.val - 1)) (by rw [uz_val hum]; omega)
    obtain ⟨y, hy, hyv⟩ := u32_sub_ok core.num.Usize.BITS v (by rw [hvv, bits_val])
    rw [hv, bind_ok, hy, bind_ok, cast_u32_usize y (by rw [hyv, hvv, bits_val]; omega), hyv, hvv, bits_val,
      Nat.sub_self, Nat.clog_of_right_le_one h1]
  · have hn0 : (uz (n.val - 1)).val ≠ 0 := by rw [uz_val hum]; omega
    obtain ⟨v, hv, hvv⟩ := lz_eq (uz (n.val - 1)) hn0
    have hl := log_lt_numBits _ hn0
    rw [uz_val hum] at hvv hl
    obtain ⟨y, hy, hyv⟩ := u32_sub_ok core.num.Usize.BITS v (by rw [hvv, bits_val]; omega)
    rw [hv, bind_ok, hy, bind_ok, cast_u32_usize y (by rw [hyv, hvv, bits_val]; omega), hyv, hvv, bits_val,
      clog_eq_log_pred (by omega)]
    congr 2; omega

/-! ## Division rounding up -/

theorem uz_rem {a b : ℕ} (ha : a ≤ Usize.max) (hb : b ≤ Usize.max) (h0 : b ≠ 0) :
    (uz a % uz b : RustM Std.Usize) = .ok (uz (a % b)) := by
  obtain ⟨z, hz, hv⟩ := spec_imp_exists (UScalar.rem_spec (uz a) (y := uz b) (by rw [uz_val hb]; exact h0))
  rw [hz, eq_uz z, hv, uz_val ha, uz_val hb]

theorem ceil_div_eq (a b : ℕ) (hb : 0 < b) :
    (a + b - 1) / b = a / b + if 0 < a % b then 1 else 0 := by
  have e := Nat.div_add_mod a b
  have hr : a % b < b := Nat.mod_lt a hb
  generalize a / b = d at e ⊢
  generalize a % b = r at e hr ⊢
  rw [show a + b - 1 = (r + b - 1) + b * d by omega, Nat.add_mul_div_left _ _ hb]
  split_ifs with h
  · rw [Nat.div_eq_of_lt_le (k := 1) (by omega) (by omega)]; omega
  · rw [Nat.div_eq_of_lt (by omega)]; omega

theorem div_ceil_eq {a b : ℕ} (ha : a ≤ Usize.max) (hb : b ≤ Usize.max) (h0 : 0 < b) :
    core.num.Usize.div_ceil (uz a) (uz b) = .ok (uz ((a + b - 1) / b)) := by
  unfold core.num.Usize.div_ceil
  rw [uz_div ha hb (by omega), bind_ok, uz_rem ha hb (by omega), bind_ok, ceil_div_eq a b h0]
  have hr : (0#usize : Std.Usize) = uz 0 := UScalar.eq_of_val_eq (by rw [uz_val (by scalar_tac)]; rfl)
  rw [hr]
  split_ifs with h1 h2 h2
  · have hd : a / b + 1 ≤ a := by
      have := Nat.div_add_mod a b; have := Nat.div_le_self a b
      nlinarith [Nat.mul_le_mul_right (a / b) (show 1 ≤ b from h0)]
    exact uz_add_one (by omega)
  · exact absurd ((uz_lt (by scalar_tac) (le_trans (Nat.mod_le a b) ha)).mp h1) (by omega)
  · exact absurd ((uz_lt (by scalar_tac) (le_trans (Nat.mod_le a b) ha)).mpr h2) h1
  · rfl

/-! ## The schedule -/

theorem min_uz {a b : ℕ} (ha : a ≤ Usize.max) (hb : b ≤ Usize.max) :
    core.Usize.Insts.CoreCmpOrd.min (uz a) (uz b) = .ok (uz (min a b)) := by
  obtain ⟨z, hz, hv⟩ := spec_imp_exists (Plonky3Lean.Lib.core.Usize.Insts.CoreCmpOrd.min.spec (uz a) (uz b))
  rw [hz, eq_uz z, hv, uz_val ha, uz_val hb]

open p3_binary_dft.lch.mirror in
/-- A transcribed schedule as the extracted structure. -/
def toSched (s : Schedule) : p3_binary_dft.lch.schedule.Schedule :=
  ⟨uz s.log_tile_rows, uz s.log_staged_rows, uz s.log_slab_rows⟩

open p3_binary_dft.lch.mirror in
/-- The extracted schedule of the serial pool is the transcribed one, at the element size the layout gives. -/
theorem schedule_new_eq {b w : ℕ} (hsz : core.mem.size_of F = .ok (uz b)) (hb : 0 < b) (hw : 0 < w)
    (hbw : b * w ≤ Usize.max) (log_n : Std.Usize) (hl : log_n.val < UScalarTy.Usize.numBits) :
    p3_binary_dft.lch.schedule.Schedule.new F (uz w) log_n =
      .ok (toSched (Schedule.new b w log_n.val)) := by
  have h64 := numBits_le64
  have hbig : 2 ^ 32 - 1 ≤ Usize.max := by
    rcases Usize.bounds_eq with e | e <;> rw [e] <;> simp [U32.max_def, U64.max_def, U32.numBits, U64.numBits]
  norm_num at hbig
  have hbwpos : 0 < b * w := Nat.mul_pos hb hw
  have hdeep : p3_binary_dft.lch.schedule.DEEP_TILE_BYTES = .ok (uz 131072) := by
    unfold p3_binary_dft.lch.schedule.DEEP_TILE_BYTES
    rw [show (128#usize : Std.Usize) = uz 128 from UScalar.eq_of_val_eq (by rw [uz_val (by omega)]; rfl),
      show (1024#usize : Std.Usize) = uz 1024 from UScalar.eq_of_val_eq (by rw [uz_val (by omega)]; rfl),
      uz_mul (by omega) (by omega) (by omega)]
  have hcache : p3_binary_dft.lch.schedule.CACHE_LINE_BYTES = uz 64 := by
    unfold p3_binary_dft.lch.schedule.CACHE_LINE_BYTES
    exact UScalar.eq_of_val_eq (by rw [uz_val (by omega)]; rfl)
  have hstaged : p3_binary_dft.lch.schedule.STAGED_WORKERS = uz 16 := by
    unfold p3_binary_dft.lch.schedule.STAGED_WORKERS
    exact UScalar.eq_of_val_eq (by rw [uz_val (by omega)]; rfl)
  have hlm : log_n.val ≤ Usize.max := by omega
  have hbm : b ≤ Usize.max := le_trans (Nat.le_mul_of_pos_right b hw) hbw
  have hwm : w ≤ Usize.max := le_trans (Nat.le_mul_of_pos_left w hb) hbw
  unfold p3_binary_dft.lch.schedule.Schedule.new p3_binary_dft.lch.schedule.Schedule.for_workers
    Schedule.new Schedule.for_workers
  simp only [p3_maybe_rayon.serial.current_num_threads, bind_ok, uz_one, hsz, uz_mul hbw hbm hwm,
    hdeep, uz_div (show 131072 ≤ Usize.max by omega) hbw (by omega)]
  have hq : 131072 / (b * w) ≤ 131072 := Nat.div_le_self _ _
  set m1 := max (131072 / (b * w)) 1 with hm1
  have hm1b : m1 ≤ 131072 := by omega
  have hlog1 : Nat.log 2 m1 ≤ m1 := Nat.log_le_self 2 m1
  set m2 := (64 + b * w - 1) / (b * w) with hm2
  have hm2b : m2 ≤ 64 := by
    rw [hm2]; apply Nat.div_le_of_le_mul; omega
  have hclog2 : Nat.clog 2 m2 ≤ m2 := Nat.clog_le_of_le_pow (Nat.lt_two_pow_self).le
  rw [max_uz (by omega) (by omega), bind_ok, ← hm1, log2_floor_eq, bind_ok, uz_val (by omega),
    log2_ceil_eq, bind_ok, uz_val (show 1 ≤ Usize.max by omega), saturating_sub_exposed_eq, bind_ok,
    uz_val (show Nat.clog 2 1 ≤ Usize.max by simp), min_uz (by omega) (by omega), bind_ok, hcache,
    div_ceil_eq (by omega) hbw hbwpos, bind_ok, ← hm2, log2_ceil_eq, bind_ok, uz_val (by omega),
    min_uz (by omega) (by omega), bind_ok]
  have hshl : ∀ (x : Std.Usize) (s : ℕ), s < UScalarTy.Usize.numBits →
      (x <<< uz s : RustM Std.Usize) = .ok ⟨x.bv.shiftLeft s⟩ := by
    intro x s hs
    show UScalar.shiftLeft_UScalar x (uz s) = _
    unfold UScalar.shiftLeft_UScalar UScalar.shiftLeft
    rw [uz_val (by omega), ite_of_pos hs]
  rw [hshl _ _ (by have := Nat.min_le_right (Nat.clog 2 m2) (min (Nat.log 2 m1) (log_n.val - Nat.clog 2 1)); omega),
    bind_ok, hstaged, ite_of_neg (fun h => absurd ((uz_le (by omega) (by omega)).mp h) (by omega))]
  simp only [toSched, log2Floor, log2Ceil, DEEP_TILE_BYTES, hm1, show (16 ≤ 1) = False by decide, ite_false]
  rw [show (128 * 1024 : ℕ) = 131072 by norm_num,
    show (0#usize : Std.Usize) = uz 0 from UScalar.eq_of_val_eq (by rw [uz_val (by omega)]; rfl)]

/-! ## The cut -/

open p3_binary_dft.lch.mirror in
/-- A transcribed cut as the extracted structure. -/
def toCut (c : Cut) : p3_binary_dft.lch.schedule.Cut :=
  ⟨uz c.tile, uz c.slab, uz c.group, uz c.groups, uz c.log_n⟩

theorem ite_uz {c : Prop} [Decidable c] (a b : ℕ) :
    (if c then RustM.ok (uz a) else RustM.ok (uz b)) = RustM.ok (uz (if c then a else b)) := by
  split_ifs <;> rfl

open p3_binary_dft.lch.mirror in
/-- The extracted cut of a schedule with no staged group: one stage per group above the tile. -/
theorem cut_new_eq (s : Schedule) (h1 : s.log_tile_rows ≤ Usize.max) (h2 : s.log_staged_rows = 0)
    (h3 : s.log_slab_rows ≤ Usize.max) {log_n : ℕ} (hl : log_n ≤ Usize.max) :
    p3_binary_dft.lch.schedule.Cut.new (toSched s) (uz log_n) = .ok (toCut (Cut.new s log_n)) := by
  have hmin : (p3_binary_dft.lch.schedule.MIN_FUSED_STAGES : Std.Usize) = uz 2 := by
    unfold p3_binary_dft.lch.schedule.MIN_FUSED_STAGES
    exact UScalar.eq_of_val_eq (by rw [uz_val (by scalar_tac)]; rfl)
  have h2m : (2 : ℕ) ≤ Usize.max := by scalar_tac
  unfold p3_binary_dft.lch.schedule.Cut.new Cut.new
  simp only [toSched, hmin, h2]
  have ht : ∃ t, t = min s.log_tile_rows log_n ∧
      (if uz s.log_tile_rows < uz log_n then RustM.ok (uz s.log_tile_rows) else RustM.ok (uz log_n)) =
        RustM.ok (uz t) := by
    refine ⟨_, rfl, ?_⟩
    by_cases h : s.log_tile_rows < log_n
    · rw [ite_of_pos ((uz_lt h1 hl).mpr h), min_eq_left h.le]
    · rw [ite_of_neg (fun h' => h ((uz_lt h1 hl).mp h')), min_eq_right (by omega)]
  obtain ⟨t, htv, hte⟩ := ht
  have htm : t ≤ Usize.max := by omega
  rw [hte, bind_ok]
  have hs : (if uz s.log_slab_rows < uz t then RustM.ok (uz s.log_slab_rows) else RustM.ok (uz t)) =
      RustM.ok (uz (min s.log_slab_rows t)) := by
    by_cases h : s.log_slab_rows < t
    · rw [ite_of_pos ((uz_lt h3 htm).mpr h), min_eq_left h.le]
    · rw [ite_of_neg (fun h' => h ((uz_lt h3 htm).mp h')), min_eq_right (by omega)]
  rw [hs, bind_ok, ite_of_neg (fun h' => absurd ((uz_le h2m (by scalar_tac)).mp h') (by omega)), bind_ok,
    uz_sub (by omega) hl, bind_ok, uz_one, div_ceil_eq (by omega) (by scalar_tac) one_pos, bind_ok]
  simp only [toCut, ← htv, show ¬ (2 ≤ 0) from by omega, ite_false]

open p3_binary_dft.lch.mirror in
theorem cut_bounds_eq (c : Cut) (hg1 : c.group = 1) (g : ℕ) (h : c.tile + g + 1 ≤ Usize.max)
    (hl : c.log_n ≤ Usize.max) :
    p3_binary_dft.lch.schedule.Cut.bounds (toCut c) (uz g) = .ok (uz (c.bounds g).1, uz (c.bounds g).2) := by
  unfold p3_binary_dft.lch.schedule.Cut.bounds Cut.bounds
  simp only [toCut, hg1, mul_one]
  rw [uz_mul (by omega) (by omega) (by scalar_tac), bind_ok, mul_one, uz_add (by omega), bind_ok,
    uz_add (by omega), bind_ok]
  by_cases hc : c.tile + g + 1 < c.log_n
  · rw [ite_of_pos ((uz_lt (by omega) hl).mpr hc), min_eq_left hc.le]
  · rw [ite_of_neg (fun h' => hc ((uz_lt (by omega) hl).mp h')), min_eq_right (by omega)]

/-! ## The stages of one tile -/

open p3_binary_dft.lch.mirror in
variable [DecidableEq F] {R : Type} {L : Level F} in
/-- The extracted stages of a tile of 2^k rows are the transcribed ones. -/
theorem tile_stages_eq_mirror {inst : p3_binary_dft.butterfly.ButterflyField F R} (hb : ButterflyComputes inst L)
    (tw : Twiddles F) (hbl : tw.bases.length ≤ Usize.max) (hsl : tw.steps.length ≤ Usize.max)
    (inverse : Bool) {w k base index N : ℕ} (hw : 0 < w) (y : ℕ → ℕ → F) (s : Slice F)
    (hy : flat w (2 ^ k) y = s.val) (hN : (index + 1) * 2 ^ k ≤ N) (hNw : N * w + 1024 ≤ Usize.max)
    (hbase : base + k ≤ Usize.max) :
    p3_binary_dft.lch.schedule.hax_reshaped.tile_stages inverse inst s (uz w) (uz k) (uz base) (uz index)
        (toTw tw) =
      ofOption ((tile_stages L tw inverse (2 ^ k) k base index y).map fun y => mkSlice (flat w (2 ^ k) y)) := by
  have hNle : N ≤ N * w := Nat.le_mul_of_pos_right N hw
  have hkN : 2 ^ k ≤ N := le_trans (Nat.le_mul_of_pos_left _ (by omega)) hN
  have hkb : k < UScalarTy.Usize.numBits := by
    by_contra hc
    have : 2 ^ UScalarTy.Usize.numBits ≤ 2 ^ k := Nat.pow_le_pow_right two_pos (by omega)
    have : Usize.max = 2 ^ UScalarTy.Usize.numBits - 1 := by rw [Usize.max_def]; simp [Usize.numBits]
    omega
  have hkm : k ≤ Usize.max := by have := Nat.lt_two_pow_self (n := k); omega
  have := loop_foldlM_inv
    (fun st => p3_binary_dft.lch.schedule.hax_reshaped.tile_stages_loop.body inverse inst (uz w) (uz k) (uz base)
      (uz index) (toTw tw) st.1 st.2)
    (fun (y : ℕ → ℕ → F) step => (({ start := uz step, «end» := uz k } : core.ops.range.Range Std.Usize),
      mkSlice (flat w (2 ^ k) y)))
    (fun y => mkSlice (flat w (2 ^ k) y)) k
    (fun y step =>
      let jj := if inverse then step else k - 1 - step
      walkBlocks L tw inverse (base + jj) (index * 2 ^ (k - 1 - jj)) (2 ^ k) (2 ^ jj) y)
    (fun _ _ => True) (fun st hst c _ => ?_) (fun c _ => ?_) y trivial
  · rw [hy, mkSlice_self] at this
    exact this
  · -- One stage of the tile.
    set jj := if inverse then st else k - 1 - st with hjj
    have hjjk : jj < k := by rw [hjj]; split_ifs <;> omega
    have hjjm : jj ≤ Usize.max := by omega
    have hpow : 2 ^ k = 2 ^ (k - 1 - jj) * (2 * 2 ^ jj) := by
      rw [← pow_succ', ← pow_add]; congr 1; omega
    have hidx : index * 2 ^ (k - 1 - jj) ≤ Usize.max := by
      have : index * 2 ^ (k - 1 - jj) ≤ index * 2 ^ k := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right two_pos (by omega))
      have : index * 2 ^ k ≤ N := by rw [add_mul, one_mul] at hN; omega
      omega
    have hwalk := walk_blocks_eq hb tw hbl hsl inverse false hw (Nat.two_pow_pos jj)
      (mkSlice (flat w (2 ^ k) c)) c (by rw [mkSlice_val (by rw [length_flat]; have := Nat.mul_le_mul_right w hkN; omega), ← hpow])
      (uz (base + jj)) (uz (index * 2 ^ (k - 1 - jj)))
      (by
        rw [uz_val hidx]
        have h1 : (index * 2 ^ (k - 1 - jj) + 2 ^ (k - 1 - jj)) * 2 ≤ (index + 1) * 2 ^ k := by
          rw [show index * 2 ^ (k - 1 - jj) + 2 ^ (k - 1 - jj) = (index + 1) * 2 ^ (k - 1 - jj) by ring,
            mul_assoc]
          exact Nat.mul_le_mul_left _ (by rw [← pow_succ]; exact Nat.pow_le_pow_right two_pos (by omega))
        omega)
      (by
        have : 2 ^ jj * 2 ≤ 2 ^ k := by rw [← pow_succ]; exact Nat.pow_le_pow_right two_pos (by omega)
        have : 2 * (2 ^ jj * w) ≤ N * w := by
          rw [← mul_assoc, mul_comm 2]; exact Nat.mul_le_mul_right _ (by omega)
        omega)
    rw [← hpow, uz_val (show base + jj ≤ Usize.max by omega), uz_val hidx] at hwalk
    simp only [p3_binary_dft.lch.schedule.hax_reshaped.tile_stages_loop.body]
    rw [show core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next
        core.Usize.Insts.CoreIterRangeStep { start := uz st, «end» := uz k } = _ from range_step st (uz k)
          (by rw [uz_val hkm]; exact hst)]
    have hk1 : (uz k - 1#usize : RustM Std.Usize) = .ok (uz (k - 1)) := by
      rw [uz_one, uz_sub (by omega) hkm]
    have hjv : (if inverse = true then RustM.ok (uz st) else do
        let i ← uz k - 1#usize
        i - uz st) = RustM.ok (uz jj) := by
      rw [hjj]; cases inverse
      · rw [ite_of_neg (by simp), hk1, bind_ok, uz_sub (by omega) (by omega)]; rfl
      · rfl
    simp only [usz_eq_uz, bind_ok, Aeneas.Std.uncurry]
    have hjw : 2 ^ jj * w ≤ Usize.max := by
      have : 2 ^ jj ≤ 2 ^ k := Nat.pow_le_pow_right two_pos hjjk.le
      have := Nat.mul_le_mul_right w (le_trans this hkN); omega
    rw [hjv, bind_ok, uz_one, shl_uz (by omega) (by rw [one_mul]; have := Nat.le_mul_of_pos_right (2 ^ jj) hw; omega),
      bind_ok, one_mul, uz_mul hjw (by have := Nat.le_mul_of_pos_right (2 ^ jj) hw; omega)
        (by have := Nat.le_mul_of_pos_left w (Nat.two_pow_pos jj); omega), bind_ok,
      uz_sub (show 1 ≤ k by omega) hkm, bind_ok, uz_sub (by omega) (by omega), bind_ok, shl_uz (by omega) hidx, bind_ok,
      uz_add (by omega), bind_ok, hwalk]
    cases walkBlocks L tw inverse (base + jj) (index * 2 ^ (k - 1 - jj)) (2 ^ k) (2 ^ jj) c <;>
      simp [ofOption]
  · simp only [p3_binary_dft.lch.schedule.hax_reshaped.tile_stages_loop.body]
    rw [show core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next
        core.Usize.Insts.CoreIterRangeStep { start := uz k, «end» := uz k } = _ from range_next_none _ _ le_rfl]
    simp

end Plonky3Lean.Proofs.BinaryDft
