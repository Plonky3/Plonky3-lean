module

public import Plonky3Lean.Proofs.BinaryDft.ExtractedLch
public import Plonky3Lean.Lib.Scalar.Signed
public import Plonky3Lean.Proofs.Matrix.Log2

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

/-! ## The deep tiles -/

open p3_binary_dft.lch.mirror in
variable [DecidableEq F] {R : Type} {L : Level F} in
/-- The extracted pass over the tiles of 2^k rows is the transcribed one. -/
theorem deep_tiles_eq_mirror {inst : p3_binary_dft.butterfly.ButterflyField F R} (hb : ButterflyComputes inst L)
    (tw : Twiddles F) (hbl : tw.bases.length ≤ Usize.max) (hsl : tw.steps.length ≤ Usize.max)
    (inverse : Bool) {w n k : ℕ} (hw : 0 < w) (x : ℕ → ℕ → F) (values : Slice F)
    (hv : flat w n x = values.val) (hdiv : 2 ^ k ∣ n) (hn : 0 < n) (hbound : n * w + 1024 ≤ Usize.max) :
    p3_binary_dft.lch.schedule.deep_tiles inverse inst values (uz w) (uz k) (toTw tw) =
      ofOption ((deep_tiles L tw inverse n k x).map fun y => mkSlice (flat w n y)) := by
  obtain ⟨K, hK⟩ := hdiv
  have hkn : 2 ^ k ≤ n := Nat.le_of_dvd hn ⟨K, hK⟩
  have hKpos : 0 < K := by rcases Nat.eq_zero_or_pos K with h | h <;> simp_all
  have hnle : n ≤ n * w := Nat.le_mul_of_pos_right n hw
  have hkb : k < UScalarTy.Usize.numBits := by
    by_contra hc
    have : 2 ^ UScalarTy.Usize.numBits ≤ 2 ^ k := Nat.pow_le_pow_right two_pos (by omega)
    have : Usize.max = 2 ^ UScalarTy.Usize.numBits - 1 := by rw [Usize.max_def]; simp [Usize.numBits]
    omega
  set T := 2 ^ k with hT
  have hTpos : 0 < T := Nat.two_pow_pos k
  set TL := T * w with hTL
  have hTLm : TL ≤ Usize.max := by have := Nat.mul_le_mul_right w hkn; omega
  have hcount : (n + T - 1) / T = K := by
    rw [hK, show T * K + T - 1 = (T - 1) + K * T by rw [mul_comm]; omega, Nat.add_mul_div_right _ _ hTpos,
      Nat.div_eq_of_lt (by omega), zero_add]
  have hloop := loop_foldlM_inv
    (fun st => p3_binary_dft.lch.schedule.hax_reshaped.deep_tiles_loop.body inverse inst (uz w) (uz k) (toTw tw)
      (uz TL) (uz (n * w)) st.1 st.2.1 st.2.2)
    (fun (x : ℕ → ℕ → F) i => (mkSlice (flat w n x), uz (i * TL), uz i))
    (fun x => mkSlice (flat w n x)) K
    (fun x index => do
      let y ← tile_stages L tw inverse (min T (n - index * T)) k 0 index (slice x (index * T))
      pure (writeBack x (index * T) (min T (n - index * T)) y))
    (fun _ _ => True) (fun i hi c _ => ?_) (fun c _ => ?_) x trivial
  · simp only [zero_mul] at hloop
    rw [hv, mkSlice_self] at hloop
    have hl : p3_binary_dft.lch.schedule.hax_reshaped.deep_tiles_loop inverse inst values (uz w) (uz k) (toTw tw)
        (uz TL) (uz (n * w)) 0#usize 0#usize = _ := hloop
    unfold p3_binary_dft.lch.schedule.deep_tiles p3_binary_dft.lch.schedule.hax_reshaped.deep_tiles deep_tiles
    have hwm : w ≤ Usize.max := le_trans (Nat.le_mul_of_pos_left w hn) (by omega)
    rw [uz_one, shl_uz hkb (by rw [one_mul]; omega), bind_ok, one_mul, ← hT,
      uz_mul hTLm (by omega) hwm, bind_ok, ← hTL]
    simp only [massert, bne_uz_zero hTLm]
    rw [ite_of_pos (by simp only [ne_eq, decide_eq_true_eq]; positivity), bind_ok, slice_len_eq, bind_ok, ← hv,
      length_flat, hl, hcount]
  · -- One tile.
    have hi1 : (i + 1) * T ≤ n := by rw [hK, mul_comm T K]; exact Nat.mul_le_mul_right _ hi
    have hmin : min T (n - i * T) = T := min_eq_left (by rw [add_mul, one_mul] at hi1; omega)
    have hiTL : i * T * w + T * w ≤ n * w := by
      have h := Nat.mul_le_mul_right w hi1; rw [add_mul, one_mul, add_mul] at h; exact h
    have hTLe : ∀ m, m * TL = m * T * w := fun m => by rw [hTL]; ring
    have hgl : (flat w n c).length = n * w := length_flat _ _ _
    have hgv : (mkSlice (flat w n c)).val = flat w n c := mkSlice_val (by omega)
    have hidx := index_mut_range_eq (mkSlice (flat w n c)) (a := i * T * w) (b := i * T * w + T * w) (by omega)
      (by rw [hgv, hgl]; exact hiTL)
    rw [hgv, show i * T * w + T * w - i * T * w = T * w by omega,
      ← flat_slice c (by omega : i * T + T ≤ n)] at hidx
    have hsub : (mkSlice (flat w T (slice c (i * T)))).val = flat w T (slice c (i * T)) := mkSlice_val (by
      rw [length_flat]; have := Nat.mul_le_mul_right w hkn; omega)
    have hts := tile_stages_eq_mirror hb tw hbl hsl inverse hw (base := 0) (slice c (i * T)) _ hsub.symm hi1
      hbound (by have := Nat.lt_two_pow_self (n := k); omega)
    have hzero : (0#usize : Std.Usize) = uz 0 := UScalar.eq_of_val_eq (by rw [uz_val (by scalar_tac)]; rfl)
    simp only [p3_binary_dft.lch.schedule.hax_reshaped.deep_tiles_loop.body, hTLe]
    rw [ite_of_pos ((uz_lt (by omega) (by omega)).mpr (by
        have := Nat.mul_le_mul_right w (show i * T + 1 ≤ n by rw [add_mul, one_mul] at hi1; omega)
        rw [add_mul, one_mul] at this; omega)),
      ← hTLe, chunk_end_eq (by rw [hTLe]; omega) (by omega) hTLm, hTLe, hTL, min_eq_left hiTL, bind_ok, hidx,
      bind_ok]
    simp only [Aeneas.Std.uncurry]
    have hi1n : i + 1 ≤ n := le_trans (Nat.le_mul_of_pos_right (i + 1) hTpos) hi1
    rw [hzero, hts, uz_add_one (by omega), add_mul, add_mul, one_mul, hmin]
    cases tile_stages L tw inverse T k 0 i (slice c (i * T)) with
    | none => simp [ofOption]
    | some y =>
      simp only [ofOption, bind_ok, Option.bind_eq_bind, Option.bind_some, Option.pure_def, Option.map]
      refine ⟨trivial, ?_⟩
      rw [mkSlice_val (by rw [length_flat]; have := Nat.mul_le_mul_right w hkn; omega),
        show i * T * w = (i * T) * w from rfl, ← flat_writeBack c y (by omega : i * T + T ≤ n)]
  · simp only [p3_binary_dft.lch.schedule.hax_reshaped.deep_tiles_loop.body]
    rw [show K * TL = n * w by rw [hTL, hK]; ring, ite_of_neg (lt_irrefl _)]

/-! ## The blocked run -/

variable {R : Type} in
theorem group_pass_stage {inst : p3_binary_dft.butterfly.ButterflyField F R} (inverse : Bool) (values : Slice F)
    (w lo : ℕ) (slab : Std.Usize) (tw : p3_binary_dft.lch.twiddles.Twiddles F) (hlo : lo + 1 ≤ Usize.max) :
    p3_binary_dft.lch.schedule.group_pass inverse inst values (uz w) (uz lo, uz (lo + 1)) slab tw =
      p3_binary_dft.lch.schedule.stage_pass inverse inst values (uz w) (uz lo) tw := by
  unfold p3_binary_dft.lch.schedule.group_pass
  simp only [Aeneas.Std.uncurry]
  rw [uz_sub (by omega) hlo, bind_ok, show lo + 1 - lo = 1 by omega, uz_one, ite_of_pos rfl]

theorem foldlM_reverse {α : Type} (f : α → ℕ → Option α) (n : ℕ) (x : α) :
    (List.range n).reverse.foldlM f x = (List.range n).foldlM (fun x k => f x (n - 1 - k)) x := by
  rw [← range_map_rev, List.foldlM_map]

open p3_binary_dft.lch.mirror in
theorem cut_serial_facts {b w l : ℕ} (c : Cut) (hc : c = Cut.new (Schedule.new b w l) l) :
    c.group = 1 ∧ c.tile ≤ l ∧ c.groups = l - c.tile ∧ c.log_n = l ∧
      ∀ g < c.groups, c.bounds g = (c.tile + g, c.tile + g + 1) := by
  subst hc
  simp only [Cut.new, Schedule.new, Schedule.for_workers, show ¬ (16 ≤ 1) by omega, ite_false,
    show ¬ (2 ≤ 0) by omega, Cut.bounds, mul_one, Nat.add_sub_cancel]
  refine ⟨trivial, min_le_right _ _, Nat.div_one _, trivial, fun g hg => ?_⟩
  simp only [Nat.div_one] at hg
  simp only [Prod.mk.injEq, true_and]
  omega

open p3_binary_dft.lch.mirror in
variable [DecidableEq F] {R : Type} {L : Level F} in
/-- The extracted blocked run on the serial pool is the transcribed one. -/
theorem run_eq_mirror {inst : p3_binary_dft.butterfly.ButterflyField F R} (hb : ButterflyComputes inst L)
    (tw : Twiddles F) (hbl : tw.bases.length ≤ Usize.max) (hsl : tw.steps.length ≤ Usize.max)
    (inverse : Bool) {b w l : ℕ} (hw : 0 < w) (x : ℕ → ℕ → F) (values : Slice F)
    (hv : flat w (2 ^ l) x = values.val) (hbound : 2 ^ l * w + 1024 ≤ Usize.max) :
    p3_binary_dft.lch.schedule.run inverse inst values (uz w) (uz l) (toTw tw) (toSched (Schedule.new b w l)) =
      ofOption ((run L tw inverse w l (Schedule.new b w l) x).map fun y => mkSlice (flat w (2 ^ l) y)) := by
  set sch := Schedule.new b w l with hsch
  set c := Cut.new sch l with hc
  obtain ⟨hg1, htile, hgroups, hcl, hbounds⟩ := cut_serial_facts c hc
  have hnl : 2 ^ l ≤ 2 ^ l * w := Nat.le_mul_of_pos_right _ hw
  have hl2 : l < 2 ^ l := Nat.lt_two_pow_self
  have hlm : l ≤ Usize.max := by omega
  have hst0 : sch.log_staged_rows = 0 := by simp [hsch, Schedule.new, Schedule.for_workers]
  have hst1 : sch.log_tile_rows ≤ Usize.max := by
    simp only [hsch, Schedule.new, Schedule.for_workers]; exact le_trans (min_le_right _ _) (by omega)
  have hst3 : sch.log_slab_rows ≤ Usize.max := by
    simp only [hsch, Schedule.new, Schedule.for_workers]
    exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (by omega))
  -- One stage of a group, on any rows.
  have hstage : ∀ (g : ℕ), g < c.groups → ∀ (inv : Bool) (y : ℕ → ℕ → F) (vs : Slice F),
      flat w (2 ^ l) y = vs.val →
      p3_binary_dft.lch.schedule.group_pass inv inst vs (uz w) (uz (c.bounds g).1, uz (c.bounds g).2)
          (uz c.slab) (toTw tw) =
        ofOption ((group_pass L tw inv w (2 ^ l) (c.bounds g) y).map fun y => mkSlice (flat w (2 ^ l) y)) := by
    intro g hg inv y vs hy
    rw [hbounds g hg, group_pass_stage inv vs w _ _ _ (by omega)]
    simp only [group_pass, show c.tile + g + 1 - (c.tile + g) = 1 by omega, ite_true]
    exact stage_pass_eq_mirror hb tw hbl hsl inv hw y vs hy
      (Nat.pow_dvd_pow 2 (by omega)) (Nat.two_pow_pos l) hbound
  have hdeep : ∀ (inv : Bool) (y : ℕ → ℕ → F) (vs : Slice F), flat w (2 ^ l) y = vs.val →
      p3_binary_dft.lch.schedule.deep_tiles inv inst vs (uz w) (uz c.tile) (toTw tw) =
        ofOption ((deep_tiles L tw inv (2 ^ l) c.tile y).map fun y => mkSlice (flat w (2 ^ l) y)) :=
    fun inv y vs hy => deep_tiles_eq_mirror hb tw hbl hsl inv hw y vs hy (Nat.pow_dvd_pow 2 htile)
      (Nat.two_pow_pos l) hbound
  have hcm : c.tile + c.groups ≤ Usize.max := by omega
  have hzero : (0#usize : Std.Usize) = uz 0 := UScalar.eq_of_val_eq (by rw [uz_val (by scalar_tac)]; rfl)
  have htilepos : (uz c.tile > 0#usize) ↔ 0 < c.tile := by
    rw [hzero, gt_iff_lt, uz_lt (by scalar_tac) (by omega)]
  -- The inverse groups, bottom first.
  have hinv : ∀ (y : ℕ → ℕ → F) (vs : Slice F), flat w (2 ^ l) y = vs.val →
      p3_binary_dft.lch.schedule.run_loop inst { start := 0#usize, «end» := uz c.groups } vs (uz w) (toTw tw)
          (uz c.tile) (uz c.slab) (uz c.group) (uz c.groups) (uz c.log_n) =
        ofOption (((List.range c.groups).foldlM (fun x g => group_pass L tw true w (2 ^ l) (c.bounds g) x) y).map
          fun y => mkSlice (flat w (2 ^ l) y)) := by
    intro y vs hy
    have := loop_foldlM_inv
      (fun st => p3_binary_dft.lch.schedule.run_loop.body inst (uz w) (toTw tw) (uz c.tile) (uz c.slab)
        (uz c.group) (uz c.groups) (uz c.log_n) st.1 st.2)
      (fun (y : ℕ → ℕ → F) k => (({ start := uz k, «end» := uz c.groups } : core.ops.range.Range Std.Usize),
        mkSlice (flat w (2 ^ l) y)))
      (fun y => mkSlice (flat w (2 ^ l) y)) c.groups
      (fun x g => group_pass L tw true w (2 ^ l) (c.bounds g) x)
      (fun _ _ => True) (fun k hk c' _ => ?_) (fun c' _ => ?_) y trivial
    · rw [hy, mkSlice_self] at this
      exact this
    · simp only [p3_binary_dft.lch.schedule.run_loop.body]
      rw [show core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next
          core.Usize.Insts.CoreIterRangeStep { start := uz k, «end» := uz c.groups } = _ from range_step k _
            (by rw [uz_val (by omega)]; exact hk)]
      simp only [usz_eq_uz, bind_ok, Aeneas.Std.uncurry]
      rw [show p3_binary_dft.lch.schedule.Cut.mk (uz c.tile) (uz c.slab) (uz c.group) (uz c.groups)
          (uz c.log_n) = toCut c from rfl,
        cut_bounds_eq c hg1 k (by omega) (by omega), bind_ok,
        hstage k hk true c' (mkSlice (flat w (2 ^ l) c')) (mkSlice_val (by rw [length_flat]; omega)).symm]
      cases group_pass L tw true w (2 ^ l) (c.bounds k) c' <;> simp [ofOption]
    · simp only [p3_binary_dft.lch.schedule.run_loop.body]
      rw [show core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next
          core.Usize.Insts.CoreIterRangeStep { start := uz c.groups, «end» := uz c.groups } = _ from
        range_next_none _ _ le_rfl]
      simp
  -- The forward groups, top first.
  have hfwd : ∀ (y : ℕ → ℕ → F) (vs : Slice F), flat w (2 ^ l) y = vs.val →
      p3_binary_dft.lch.schedule.forward_below_loop inst
          ({ iter := { start := 0#usize, «end» := uz c.groups } } :
            core.iter.adapters.rev.Rev (core.ops.range.Range Std.Usize)) vs (uz w) (toCut c) (toTw tw) =
        ofOption (((List.range c.groups).foldlM
          (fun x k => group_pass L tw false w (2 ^ l) (c.bounds (c.groups - 1 - k)) x) y).map
          fun y => (mkSlice (flat w (2 ^ l) y), toCut c)) := by
    intro y vs hy
    have := loop_foldlM_inv
      (fun st => p3_binary_dft.lch.schedule.forward_below_loop.body inst (uz w) (toCut c) (toTw tw) st.1 st.2)
      (fun (y : ℕ → ℕ → F) k => (({ iter := { start := 0#usize, «end» := uz (c.groups - k) } } :
          core.iter.adapters.rev.Rev (core.ops.range.Range Std.Usize)), mkSlice (flat w (2 ^ l) y)))
      (fun y => (mkSlice (flat w (2 ^ l) y), toCut c)) c.groups
      (fun x k => group_pass L tw false w (2 ^ l) (c.bounds (c.groups - 1 - k)) x)
      (fun _ _ => True) (fun k hk c' _ => ?_) (fun c' _ => ?_) y trivial
    · rw [hy, mkSlice_self, Nat.sub_zero] at this
      exact this
    · simp only [p3_binary_dft.lch.schedule.forward_below_loop.body,
        core.iter.adapters.rev.Rev.Insts.CoreIterTraitsIteratorIterator.next,
        core.ops.range.Range.Insts.CoreIterTraitsDouble_endedDoubleEndedIterator]
      rw [range_next_back_lt _ (by omega) (by rw [show (0#usize : Std.Usize).val = 0 from rfl]; omega)]
      simp only [bind_ok, Aeneas.Std.uncurry]
      rw [show c.groups - k - 1 = c.groups - (k + 1) by omega, show c.groups - 1 - k = c.groups - (k + 1) by omega,
        cut_bounds_eq c hg1 _ (by omega) (by omega), bind_ok,
        show (toCut c).slab = uz c.slab from rfl,
        hstage _ (by omega) false c' (mkSlice (flat w (2 ^ l) c')) (mkSlice_val (by rw [length_flat]; omega)).symm]
      cases group_pass L tw false w (2 ^ l) (c.bounds (c.groups - (k + 1))) c' <;> simp [ofOption]
    · simp only [p3_binary_dft.lch.schedule.forward_below_loop.body,
        core.iter.adapters.rev.Rev.Insts.CoreIterTraitsIteratorIterator.next,
        core.ops.range.Range.Insts.CoreIterTraitsDouble_endedDoubleEndedIterator]
      rw [Nat.sub_self, ← hzero]
      unfold core.IteratorRange.next_back
      simp [core.Usize.Insts.CoreCmpPartialOrdUsize, core.mkUPartialOrd]
  have hfl : ∀ z : ℕ → ℕ → F, flat w (2 ^ l) z = (mkSlice (flat w (2 ^ l) z)).val :=
    fun z => (mkSlice_val (by rw [length_flat]; omega)).symm
  unfold p3_binary_dft.lch.schedule.run run
  rw [cut_new_eq sch hst1 hst0 hst3 hlm, bind_ok, ← hc,
    show (toCut c).tile = uz c.tile from rfl, show (toCut c).slab = uz c.slab from rfl,
    show (toCut c).group = uz c.group from rfl, show (toCut c).groups = uz c.groups from rfl,
    show (toCut c).log_n = uz c.log_n from rfl]
  cases inverse
  · -- Forward: the groups top first, then the tiles.
    simp only [Bool.false_eq_true, ite_false]
    unfold p3_binary_dft.lch.schedule.forward_below forward_below
    simp only [core.iter.traits.iterator.Iterator.rev.default, core.iter.adapters.rev.Rev.new, bind_ok]
    rw [hfwd x values hv, foldlM_reverse]
    cases (List.range c.groups).foldlM
        (fun x k => group_pass L tw false w (2 ^ l) (c.bounds (c.groups - 1 - k)) x) x with
    | none => simp [ofOption]
    | some z =>
      simp only [ofOption, Option.map_some, bind_ok, Aeneas.Std.uncurry, Option.bind_eq_bind, Option.bind_some,
        show (toCut c).tile = uz c.tile from rfl]
      by_cases h : 0 < c.tile
      · rw [ite_of_pos (htilepos.mpr h), ite_of_pos h, hdeep false z _ (hfl z)]; rfl
      · rw [ite_of_neg (fun h' => h (htilepos.mp h')), ite_of_neg h]; rfl
  · -- Inverse: the tiles, then the groups bottom first.
    simp only [ite_true]
    by_cases h : 0 < c.tile
    · rw [ite_of_pos (htilepos.mpr h), ite_of_pos h, hdeep true x values hv]
      cases deep_tiles L tw true (2 ^ l) c.tile x with
      | none => simp [ofOption]
      | some z =>
        simp only [ofOption, Option.map_some, bind_ok, Option.bind_eq_bind, Option.bind_some]
        exact hinv z _ (hfl z)
    · rw [ite_of_neg (fun h' => h (htilepos.mp h')), ite_of_neg h, bind_ok]
      exact hinv x values hv

/-! ## The transform -/

theorem div_uz_zero (x : Std.Usize) : (x / uz 0 : RustM Std.Usize) = .fail .panic := by
  show UScalar.div x (uz 0) = _
  unfold UScalar.div
  simp

open p3_binary_dft.lch.mirror p3_dft.mirror in
variable [DecidableEq F] {R : Type} {L : Level F} in
/-- The extracted transform is the transcribed one on the rows of a buffer of n rows.

It assumes that the element size is the level's, and that the buffer's bytes fit a word. -/
theorem transform_eq_mirror {inst : p3_binary_dft.butterfly.ButterflyField F R} (hb : ButterflyComputes inst L)
    (hlb : L.logBits ≤ 31) (hsz : core.mem.size_of F = .ok (uz L.bytes)) (hbytes : 0 < L.bytes)
    (inverse : Bool) {w n : ℕ} (hwm : w ≤ Usize.max) (x : ℕ → ℕ → F) (values : Slice F)
    (hv : flat w n x = values.val) (hfit : n * w * L.bytes + 1024 ≤ Usize.max) (shift : F) :
    p3_binary_dft.lch.transform inverse inst values (uz w) shift =
      ofOption ((transform L inverse w n shift x).map fun y => mkSlice (flat w n y)) := by
  have hlen : values.val.length = n * w := by rw [← hv, length_flat]
  have hnw : n * w ≤ n * w * L.bytes := Nat.le_mul_of_pos_right _ hbytes
  unfold p3_binary_dft.lch.transform transform
  rw [slice_len_eq, bind_ok, hlen]
  rcases Nat.eq_zero_or_pos w with hw0 | hw
  · subst hw0
    rw [div_uz_zero]; simp [ofOption]
  have hnn : n ≤ n * w := Nat.le_mul_of_pos_right n hw
  rw [uz_div (by omega) hwm (by omega), bind_ok, Nat.mul_div_cancel n hw, ite_of_neg (by omega)]
  by_cases hpow : ∃ l, n = 2 ^ l
  case neg =>
    push Not at hpow
    rw [Plonky3Lean.Proofs.Matrix.log2_strict_usize_panics (uz n) (by rw [uz_val (by omega)]; exact hpow)]
    have : log2Strict n = none := by
      unfold log2Strict
      rw [ite_of_neg (fun h => hpow _ h.2.symm)]
    simp [this, ofOption]
  obtain ⟨l, rfl⟩ := hpow
  have hl2 : l < 2 ^ l := Nat.lt_two_pow_self
  have hn1 : 2 ^ l ≤ 2 ^ l * w := Nat.le_mul_of_pos_right _ hw
  have hlnb : l < UScalarTy.Usize.numBits := by
    by_contra hc
    have : 2 ^ UScalarTy.Usize.numBits ≤ 2 ^ l := Nat.pow_le_pow_right two_pos (by omega)
    have : Usize.max = 2 ^ UScalarTy.Usize.numBits - 1 := by rw [Usize.max_def]; simp [Usize.numBits]
    omega
  obtain ⟨r, hr, hrv⟩ := spec_imp_exists (Plonky3Lean.Proofs.Matrix.log2_strict_usize_two_pow hlnb (uz (2 ^ l)) (uz_val (by omega)))
  rw [hr, bind_ok, eq_uz r, hrv]
  have hls : log2Strict (2 ^ l) = some l := by
    unfold log2Strict; rw [ite_of_pos ⟨by positivity, by rw [Nat.log_pow one_lt_two]⟩, Nat.log_pow one_lt_two]
  simp only [hls, Option.bind_eq_bind, Option.bind_some]
  have h32 : 32 ≤ UScalarTy.Usize.numBits := Plonky3Lean.Proofs.Matrix.numBits_ge
  have hbig : 2 ^ 32 - 1 ≤ Usize.max := by
    rcases Usize.bounds_eq with e | e <;> rw [e] <;> simp [U32.max_def, U64.max_def, U32.numBits, U64.numBits]
  have hpb : 2 ^ L.logBits ≤ 2 ^ 31 := Nat.pow_le_pow_right two_pos hlb
  rw [hb.logBits, bind_ok, uz_one, shl_uz (by omega) (by rw [one_mul]; omega), bind_ok, one_mul]
  simp only [massert]
  by_cases hlb2 : l ≤ 2 ^ L.logBits
  case neg =>
    rw [ite_of_neg (fun h => hlb2 ((uz_le (by omega) (by omega)).mp h)), ite_of_pos (by omega)]
    simp [ofOption]
  rw [ite_of_pos ((uz_le (by omega) (by omega)).mpr hlb2), ite_of_neg (by omega), bind_ok,
    twiddles_new_eq_mirror hb.tower, uz_val (by omega), Twiddles.new_eq L hlb2 shift]
  simp only [ofOption, Option.map_some, bind_ok, Option.bind_some]
  set tw : Twiddles F := ⟨(List.range l).map fun j => sqAddIter j shift,
    (List.range (l - 1)).map fun r => ∑ q ∈ Finset.range (r + 1), L.cantor (q + 1)⟩ with htw
  have hbl : tw.bases.length ≤ Usize.max := by simp [htw]; omega
  have hsl : tw.steps.length ≤ Usize.max := by simp [htw]; omega
  have hbound : 2 ^ l * w + 1024 ≤ Usize.max := by omega
  have hsv : core.mem.size_of_val values = .ok (uz (2 ^ l * w * L.bytes)) := by
    unfold core.mem.size_of_val
    have := Nat.le_mul_of_pos_left L.bytes (show 0 < 2 ^ l * w by positivity)
    rw [hsz, bind_ok, uz_val (show L.bytes ≤ Usize.max by omega)]
    show RustM.ok (uz (values.val.length * L.bytes)) = _
    rw [hlen]
  have hdeep : p3_binary_dft.lch.schedule.DEEP_TILE_BYTES = .ok (uz 131072) := by
    unfold p3_binary_dft.lch.schedule.DEEP_TILE_BYTES
    rw [show (128#usize : Std.Usize) = uz 128 from UScalar.eq_of_val_eq (by rw [uz_val (by omega)]; rfl),
      show (1024#usize : Std.Usize) = uz 1024 from UScalar.eq_of_val_eq (by rw [uz_val (by omega)]; rfl),
      uz_mul (by omega) (by omega) (by omega)]
  rw [hsv, bind_ok, hdeep, bind_ok]
  simp only [DEEP_TILE_BYTES, show (128 * 1024 : ℕ) = 131072 by norm_num]
  by_cases hsmall : 2 ^ l * w * L.bytes ≤ 131072
  · rw [ite_of_pos ((uz_le (by omega) (by omega)).mpr hsmall), ite_of_pos hsmall]
    -- The stages one pass each.
    have := loop_foldlM_inv
      (fun st => p3_binary_dft.lch.transform_loop.body inverse inst (uz w) (uz l) (toTw tw) st.1 st.2)
      (fun (y : ℕ → ℕ → F) k => (({ start := uz k, «end» := uz l } : core.ops.range.Range Std.Usize),
        mkSlice (flat w (2 ^ l) y)))
      (fun y => mkSlice (flat w (2 ^ l) y)) l
      (fun x step => stage_pass L tw inverse w (2 ^ l) (if inverse = true then step else l - 1 - step) x)
      (fun _ _ => True) (fun k hk c _ => ?_) (fun c _ => ?_) x trivial
    · rw [hv, mkSlice_self] at this
      have hl : p3_binary_dft.lch.transform_loop inverse inst { start := 0#usize, «end» := uz l } values (uz w)
          (uz l) (toTw tw) = _ := this
      rw [hl]; rfl
    · simp only [p3_binary_dft.lch.transform_loop.body]
      rw [show core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next
          core.Usize.Insts.CoreIterRangeStep { start := uz k, «end» := uz l } = _ from range_step k _
            (by rw [uz_val (by omega)]; exact hk)]
      simp only [usz_eq_uz, bind_ok, Aeneas.Std.uncurry]
      set j := if inverse = true then k else l - 1 - k with hj
      have hjl : j < l := by rw [hj]; split_ifs <;> omega
      have hjv : (if inverse = true then RustM.ok (uz k) else do
          let i ← uz l - 1#usize
          i - uz k) = RustM.ok (uz j) := by
        rw [hj]; cases inverse
        · rw [ite_of_neg (by simp), uz_one, uz_sub (by omega) (by omega), bind_ok, uz_sub (by omega) (by omega)]
          rfl
        · rfl
      rw [hjv, bind_ok, stage_pass_eq_mirror hb tw hbl hsl inverse hw c _ (mkSlice_val (by
          rw [length_flat]; omega)).symm (Nat.pow_dvd_pow 2 (by omega)) (Nat.two_pow_pos l) hbound]
      cases stage_pass L tw inverse w (2 ^ l) j c <;> simp [ofOption]
    · simp only [p3_binary_dft.lch.transform_loop.body]
      rw [show core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next
          core.Usize.Insts.CoreIterRangeStep { start := uz l, «end» := uz l } = _ from range_next_none _ _ le_rfl]
      simp
  · have hbw : L.bytes * w ≤ Usize.max := by
      have h := Nat.le_mul_of_pos_left (L.bytes * w) (Nat.two_pow_pos l)
      rw [show 2 ^ l * (L.bytes * w) = 2 ^ l * w * L.bytes by ring] at h; omega
    have hul : (uz l).val < UScalarTy.Usize.numBits := by rw [uz_val (by omega)]; exact hlnb
    rw [ite_of_neg (fun h => hsmall ((uz_le (by omega) (by omega)).mp h)), ite_of_neg hsmall,
      schedule_new_eq hsz hbytes hw hbw (uz l) hul, bind_ok, uz_val (by omega),
      run_eq_mirror hb tw hbl hsl inverse hw x values hv hbound]
    rfl

/-! ## The extracted transform computes the additive NTT -/

theorem flat_congr {w n : ℕ} {x y : ℕ → ℕ → F} (h : ∀ r < n, x r = y r) : flat w n x = flat w n y := by
  apply List.ext_getElem?; intro p
  rw [flat_getElem?, flat_getElem?]
  split_ifs with hp
  · rcases Nat.eq_zero_or_pos w with hw | hw
    · subst hw; simp at hp
    · rw [h _ (by rw [Nat.div_lt_iff_lt_mul hw]; exact hp)]
  · rfl

section Ntt

open p3_binary_dft.lch.mirror

variable [DecidableEq F] [CharP F 2] {R : Type} {L : Level F} {inst : p3_binary_dft.butterfly.ButterflyField F R}
  (hL : Cantor L) (hb : ButterflyComputes inst L) (hlb : L.logBits ≤ 31)
  (hsz : core.mem.size_of F = .ok (uz L.bytes)) (hbytes : 0 < L.bytes)
include hL hb hlb hsz hbytes

/-- The extracted forward transform of 2^l rows lists the additive NTT of the rows over the coset. -/
theorem extracted_transform_ntt {l w : ℕ} (hl : l ≤ 2 ^ L.logBits) (hw : 0 < w) (hwm : w ≤ Usize.max)
    (values : Slice F) (hlen : values.val.length = 2 ^ l * w)
    (hfit : 2 ^ l * w * L.bytes + 1024 ≤ Usize.max) (shift : F) :
    p3_binary_dft.lch.transform false inst values (uz w) shift =
      .ok (mkSlice (flat w (2 ^ l) (ntt L.cantor l shift (rowsOf w values.val)))) := by
  rw [transform_eq_mirror hb hlb hsz hbytes false hwm (rowsOf w values.val) values (flat_rowsOf _ hlen) hfit,
    transform_ntt hL hl shift hw]
  simp only [ofOption, Option.map_some]
  congr 2
  exact flat_congr fun r hr => by simp [mask, hr]

/-- The extracted inverse transform recovers the rows of coefficients whose additive NTT it is given. -/
theorem extracted_transform_intt {l w : ℕ} (hl : l ≤ 2 ^ L.logBits) (hw : 0 < w) (hwm : w ≤ Usize.max)
    (shift : F) (d : ℕ → ℕ → F) (values : Slice F) (hv : values.val = flat w (2 ^ l) (ntt L.cantor l shift d))
    (hfit : 2 ^ l * w * L.bytes + 1024 ≤ Usize.max) :
    p3_binary_dft.lch.transform true inst values (uz w) shift = .ok (mkSlice (flat w (2 ^ l) d)) := by
  rw [transform_eq_mirror hb hlb hsz hbytes true hwm (ntt L.cantor l shift d) values hv.symm hfit,
    transform_eq hL hl shift true hw]
  simp only [ofOption, Option.map_some]
  congr 2
  refine flat_congr fun r hr => ?_
  have hi := transform_intt hL hl shift hw d (ntt L.cantor l shift d) (fun _ _ => rfl) hr
  rw [transform_eq hL hl shift true hw] at hi
  simpa using hi

/-- The extracted inverse transform undoes the extracted forward transform. -/
theorem extracted_transform_round_trip {l w : ℕ} (hl : l ≤ 2 ^ L.logBits) (hw : 0 < w) (hwm : w ≤ Usize.max)
    (values : Slice F) (hlen : values.val.length = 2 ^ l * w)
    (hfit : 2 ^ l * w * L.bytes + 1024 ≤ Usize.max) (shift : F) :
    (do
      let out ← p3_binary_dft.lch.transform false inst values (uz w) shift
      p3_binary_dft.lch.transform true inst out (uz w) shift) = .ok values := by
  rw [extracted_transform_ntt hL hb hlb hsz hbytes hl hw hwm values hlen hfit shift,
    bind_tc_ok (α := Slice F), extracted_transform_intt hL hb hlb hsz hbytes hl hw hwm shift (rowsOf w values.val) _
      (mkSlice_val (by rw [length_flat]; have := Nat.le_mul_of_pos_right (2 ^ l * w) hbytes; omega)) hfit,
    flat_rowsOf _ hlen, mkSlice_self]

/-- The extracted transform panics on a height that is not a power of two, or wider than the level. -/
theorem extracted_transform_panics (inverse : Bool) {n w : ℕ} (hwm : w ≤ Usize.max) (values : Slice F)
    (hlen : values.val.length = n * w) (hfit : n * w * L.bytes + 1024 ≤ Usize.max) (shift : F)
    (h : (∀ k, n ≠ 2 ^ k) ∨ (∃ l, n = 2 ^ l ∧ 2 ^ L.logBits < l)) :
    p3_binary_dft.lch.transform inverse inst values (uz w) shift = .fail .panic := by
  rcases Nat.eq_zero_or_pos w with hw | hw
  · subst hw
    unfold p3_binary_dft.lch.transform
    rw [slice_len_eq, bind_ok, div_uz_zero]; simp
  rw [transform_eq_mirror hb hlb hsz hbytes inverse hwm (rowsOf w values.val) values (flat_rowsOf _ hlen) hfit,
    transform_panics inverse shift (h.elim Or.inl (fun h => Or.inr (Or.inl h)))]
  rfl

end Ntt

variable {R : Type} in
/-- The extracted transform panics at width zero, whatever the buffer. -/
theorem extracted_transform_panics_width {inst : p3_binary_dft.butterfly.ButterflyField F R} (inverse : Bool)
    (values : Slice F) (shift : F) :
    p3_binary_dft.lch.transform inverse inst values (uz 0) shift = .fail .panic := by
  unfold p3_binary_dft.lch.transform
  rw [slice_len_eq, bind_ok, div_uz_zero]; simp

end Plonky3Lean.Proofs.BinaryDft
