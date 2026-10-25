module

public import Plonky3Lean.Proofs.MerkleTree.Binary
public import Plonky3Lean.Proofs.MerkleTree.Panics

@[expose] public section

/-!
# The height check, read forwards
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open p3_merkle_tree

namespace Plonky3Lean.Proofs.MerkleTree

/-- The rounded-up base-2 logarithm, as the word computation returns it. -/
theorem log2_ceil_ok (x : Std.Usize) :
    ∃ r, p3_util.log2_ceil_usize x = RustM.ok r ∧
      r.val = if x.val ≤ 1 then 0 else Nat.log 2 (x.val - 1) + 1 := by
  unfold p3_util.log2_ceil_usize
  simp only [core.num.Usize.saturating_sub_exposed, bind_ok, core.num.Usize.leading_zeros,
    rust_primitives.arithmetic.leading_zeros_usize]
  have hw : UScalarTy.Usize.numBits = 32 ∨ UScalarTy.Usize.numBits = 64 := by
    rcases System.Platform.numBits_eq with h | h <;> simp [UScalarTy.numBits, h]
  set i : Std.Usize := (BitVec.ofNat UScalarTy.Usize.numBits (x.val - (1#usize).val))#uscalar
  have hi : i.val = x.val - 1 := by
    show (BitVec.ofNat _ _).toNat = _
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := x.hBounds; simp at this ⊢; omega)]
    rfl
  have hlz : (Std.core.num.Usize.leading_zeros i).val =
      if i.val = 0 then UScalarTy.Usize.numBits else UScalarTy.Usize.numBits - Nat.log 2 i.val - 1 := by
    have hbv : i.bv = 0 ↔ i.val = 0 := by rw [← BitVec.toNat_inj]; rfl
    have hw2 : System.Platform.numBits < 4294967296 := by
      rcases System.Platform.numBits_eq with h | h <;> omega
    have hu : UScalarTy.Usize.numBits = System.Platform.numBits := rfl
    simp only [Std.core.num.Usize.leading_zeros, BitVec.leadingZeros, hbv]
    split_ifs <;> (show (BitVec.ofNat 32 _).toNat = _; rw [BitVec.toNat_ofNat]; (try simp only [UScalar.bv_toNat] at *); omega)
  have hbits : (Std.core.num.Usize.BITS).val = UScalarTy.Usize.numBits := by
    simp [Std.core.num.Usize.BITS]
  obtain ⟨d, hd, hdv⟩ : ∃ d, Std.core.num.Usize.BITS - Std.core.num.Usize.leading_zeros i = RustM.ok d ∧
      d.val = (Std.core.num.Usize.BITS).val - (Std.core.num.Usize.leading_zeros i).val := by
    have : Std.core.num.Usize.BITS - Std.core.num.Usize.leading_zeros i ⦃ z =>
        z.val = (Std.core.num.Usize.BITS).val - (Std.core.num.Usize.leading_zeros i).val ⦄ := by
      step*
      rw [hbits, hlz]; split <;> omega
    exact Lib.spec_imp_exists this
  refine ⟨_, by rw [hd, bind_ok], ?_⟩
  rw [U32.cast_Usize_val_eq, hdv, hbits, hlz, hi]
  have hx : x.val < 2 ^ UScalarTy.Usize.numBits := by have := x.hBounds; simp at this ⊢; omega
  split_ifs with h0 h1 h1
  · omega
  · omega
  · omega
  · have := Nat.log_lt_of_lt_pow (b := 2) h0 (show x.val - 1 < 2 ^ UScalarTy.Usize.numBits by omega)
    omega

/-- The rounded-up base-2 logarithm, with 0 for 0 and 1. -/
def clog (x : ℕ) : ℕ := if x ≤ 1 then 0 else Nat.log 2 (x - 1) + 1

theorem clog_two_pow (e : ℕ) : clog (2 ^ e) = e := by
  rcases e with _ | e
  · simp [clog]
  have h1 : 1 < 2 ^ (e + 1) := Nat.one_lt_two_pow (by omega)
  have h2 : 2 ^ e ≤ 2 ^ (e + 1) - 1 := by rw [pow_succ]; have := Nat.one_le_two_pow (n := e); omega
  rw [clog, ite_eq_right (show ¬ 2 ^ (e + 1) ≤ 1 by omega), Nat.log_eq_of_pow_le_of_lt_pow h2 (by omega)]

theorem usize_shr_eq {x y : Std.Usize} (h : y.val < UScalarTy.Usize.numBits) :
    ∃ z, x >>> y = RustM.ok z ∧ z.val = x.val >>> y.val := by
  have : x >>> y ⦃ z => z.val = x.val >>> y.val ⦄ := by step*
  exact Lib.spec_imp_exists this

theorem numBits_pos : 0 < UScalarTy.Usize.numBits := by
  rcases System.Platform.numBits_eq with h | h <;> simp [UScalarTy.numBits, h]

/-- A word holding 2^n has n below the word size. -/
theorem lt_numBits_of_pow {x : Std.Usize} {n : ℕ} (h : x.val = 2 ^ n) : n < UScalarTy.Usize.numBits := by
  have hx : x.val < 2 ^ UScalarTy.Usize.numBits := by have := x.hBounds; simp at this ⊢; omega
  rw [h] at hx
  exact (Nat.pow_lt_pow_iff_right (by omega)).1 hx

/-- The first loop of the height check returns. -/
theorem max_loop_total (dims : Slice p3_matrix.Dimensions) :
    ∃ m, mmcs.hax_reshaped.validate_heights_loop0 dims 0#usize 0#usize = RustM.ok m := by
  unfold mmcs.hax_reshaped.validate_heights_loop0
  refine loop_total _ (fun x : Std.Usize × Std.Usize => x.2.val ≤ dims.val.length)
    (fun x => dims.val.length - x.2.val) ?_ _ (by simp)
  rintro ⟨mx, i⟩ hi
  dsimp only at hi
  unfold mmcs.hax_reshaped.validate_heights_loop0.body
  simp only [core.slice.Slice.len, rust_primitives.slice.slice_length, bind_ok]
  by_cases hlt : i.val < dims.val.length
  · rw [ite_eq_left (show i < Slice.len dims by simpa using hlt), Lib.slice_index_eq dims i hlt, bind_ok]
    have hmax : dims.val.length ≤ Usize.max := by scalar_tac
    obtain ⟨i2, hi2, hi2v⟩ := usize_add_eq (x := i) (y := 1#usize) (by simp; omega)
    have hi2v' : i2.val = i.val + 1 := by simpa using hi2v
    split <;> (rw [bind_ok, hi2, bind_ok]; exact ⟨_, rfl, by dsimp only; omega, by dsimp only; omega⟩)
  · rw [ite_eq_right (show ¬ i < Slice.len dims by simpa using hlt)]
    exact ⟨_, rfl, trivial⟩

theorem pow_sub_one_div {n k : ℕ} (hk : k ≤ n) : (2 ^ n - 1) / 2 ^ k = 2 ^ (n - k) - 1 := by
  have hn : 2 ^ n = 2 ^ (n - k) * 2 ^ k := by rw [← pow_add, Nat.sub_add_cancel hk]
  have h1 : 1 ≤ 2 ^ (n - k) := Nat.one_le_two_pow
  have h2 : 1 ≤ 2 ^ k := Nat.one_le_two_pow
  apply Nat.div_eq_of_lt_le
  · rw [Nat.sub_mul, one_mul, ← hn]; omega
  · have h3 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
    rw [Nat.sub_add_cancel h1, ← hn]; omega

theorem clog_eq (x : ℕ) : (if x ≤ 1 then 0 else Nat.log 2 (x - 1) + 1) = clog x := rfl

/-- On power-of-two heights, the height check passes and returns the tallest height. -/
theorem validate_binary {dims : Slice p3_matrix.Dimensions} (hpow : PowHeights dims)
    (hne : dims.val ≠ []) :
    ∃ val : Std.Usize, mmcs.hax_reshaped.validate_heights dims = RustM.ok (core.result.Result.Ok val) ∧
      val.val = maxHeight dims := by
  obtain ⟨m, hm⟩ := max_loop_total dims
  have hmv := max_loop_ok hm
  obtain ⟨d0, hd0⟩ := List.exists_mem_of_ne_nil _ hne
  have hpos : 0 < maxHeight dims := by
    have h1 := le_foldl_max_of (dims.val.map fun d => d.height.val) 0 d0.height.val
      (Or.inl (List.mem_map_of_mem hd0))
    have h2 : 1 ≤ d0.height.val := by rw [← hpow d0 hd0]; exact Nat.one_le_two_pow
    unfold maxHeight; omega
  obtain ⟨hmax, hlog⟩ := maxHeight_pow hpow hpos
  set n := Nat.log 2 (maxHeight dims)
  have hm2 : m.val = 2 ^ n := by rw [hmv, ← hmax]
  have hnb := lt_numBits_of_pow hm2
  unfold mmcs.hax_reshaped.validate_heights
  rw [hm, bind_ok, ite_eq_right (fun h => by rw [h] at hm2; simp at hm2)]
  obtain ⟨lg, hlg, hlgv⟩ := log2_ceil_ok m
  rw [clog_eq, hm2, clog_two_pow] at hlgv
  rw [hlg, bind_ok]
  unfold mmcs.hax_reshaped.validate_heights_loop1
  refine (fun ⟨r, hr, hrv⟩ => ⟨m, hrv ▸ hr, hmv⟩) (loop_total_post _
    (fun i : Std.Usize => i.val ≤ dims.val.length) (fun r => r = core.result.Result.Ok m)
    (fun i => dims.val.length - i.val) ?_ 0#usize (by simp))
  intro i hi
  unfold mmcs.hax_reshaped.validate_heights_loop1.body
  simp only [core.slice.Slice.len, rust_primitives.slice.slice_length, bind_ok]
  by_cases hlt : i.val < dims.val.length
  · rw [ite_eq_left (show i < Slice.len dims by simpa using hlt), Lib.slice_index_eq dims i hlt, bind_ok]
    set d := dims.val[i.val]
    have hd : d.height.val = 2 ^ Nat.log 2 d.height.val := (hpow d (List.getElem_mem hlt)).symm
    have he : Nat.log 2 d.height.val ≤ n := by
      have := hlog i.val (by rw [logsOf_length]; exact hlt)
      simpa [logsOf, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt] using this
    set e := Nat.log 2 d.height.val
    obtain ⟨c, hc, hcv⟩ := log2_ceil_ok d.height
    rw [clog_eq, hd, clog_two_pow] at hcv
    rw [hc, bind_ok]
    obtain ⟨br, hbr, hbrv⟩ := usize_sub_eq (x := lg) (y := c) (by omega)
    rw [hbr, bind_ok]
    obtain ⟨m1, hm1, hm1v⟩ := usize_sub_eq (x := m) (y := 1#usize) (by simp; have := Nat.one_le_two_pow (n := n); omega)
    rw [hm1, bind_ok]
    obtain ⟨sh, hsh, hshv⟩ := usize_shr_eq (x := m1) (y := br) (by omega)
    rw [hsh, bind_ok]
    have hshv' : sh.val = 2 ^ e - 1 := by
      rw [hshv, Nat.shiftRight_eq_div_pow, hm1v, hbrv, hlgv, hcv, hm2]
      rw [show ((1#usize : Std.Usize).val) = 1 from rfl, pow_sub_one_div (by omega),
        show n - (n - e) = e by omega]
    obtain ⟨ex, hex, hexv⟩ := usize_add_eq (x := sh) (y := 1#usize) (by
      have hb : d.height.val ≤ Usize.max := by scalar_tac
      rw [show ((1#usize : Std.Usize).val) = 1 from rfl, hshv']
      have := Nat.one_le_two_pow (n := e); omega)
    rw [hex, bind_ok]
    have hexd : ex = d.height := by
      apply UScalar.eq_of_val_eq
      rw [hexv, hshv', hd]; have := Nat.one_le_two_pow (n := e); simp
    rw [hexd]
    simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
    have hmax' : dims.val.length ≤ Usize.max := by scalar_tac
    obtain ⟨i2, hi2, hi2v⟩ := usize_add_eq (x := i) (y := 1#usize) (by simp; omega)
    have hi2v' : i2.val = i.val + 1 := by simpa using hi2v
    rw [hi2, bind_ok]
    exact ⟨_, rfl, by omega, by omega⟩
  · rw [ite_eq_right (show ¬ i < Slice.len dims by simpa using hlt)]
    exact ⟨_, rfl, rfl⟩

theorem usize_max_eq : Usize.max = 2 ^ UScalarTy.Usize.numBits - 1 := by
  rw [Usize.max_def]; simp [Usize.numBits, UScalarTy.numBits]

/-- The largest word rounds up to a full word of halvings. -/
theorem clog_max : clog Usize.max = UScalarTy.Usize.numBits := by
  have hw : 2 ≤ UScalarTy.Usize.numBits := by
    rcases System.Platform.numBits_eq with h | h <;> simp [UScalarTy.numBits, h]
  have h1 : 2 ≤ 2 ^ (UScalarTy.Usize.numBits - 1) := by
    calc 2 = 2 ^ 1 := rfl
      _ ≤ _ := Nat.pow_le_pow_right (by omega) (by omega)
  have h2 : 2 ^ UScalarTy.Usize.numBits = 2 * 2 ^ (UScalarTy.Usize.numBits - 1) := by
    rw [← pow_succ', Nat.sub_add_cancel (by omega)]
  rw [clog, usize_max_eq, ite_eq_right (by omega),
    Nat.log_eq_of_pow_le_of_lt_pow (m := UScalarTy.Usize.numBits - 1) (by omega) (by omega)]
  omega

/-- The height check panics on a tallest height of the largest word next to a height 0 or 1.

That height sits a full word of halvings below the leaves, and the shift by the word size overflows.

```text
    heights:          2^w - 1 and h <= 1, on a w-bit word
    rounded-up log:   w and 0
    shift:            (2^w - 2) >> w overflows
``` -/
theorem validate_panics_max (w0 w1 M h : Std.Usize) (hM : M.val = Usize.max) (hh : h.val ≤ 1) :
    mmcs.hax_reshaped.validate_heights (dims2 w0 M w1 h) = RustM.fail .panic := by
  obtain ⟨m, hm⟩ := max_loop_total (dims2 w0 M w1 h)
  have hmv := max_loop_ok hm
  have hmM : m = M := by
    apply UScalar.eq_of_val_eq
    have hmh : maxHeight (dims2 w0 M w1 h) = max M.val h.val := by
      simp [maxHeight, dims2]
    have hMb : h.val ≤ M.val := by
      have : 1 ≤ Usize.max := by scalar_tac
      omega
    rw [hmv, hmh]; omega
  subst hmM
  have hw : 2 ≤ UScalarTy.Usize.numBits := by
    rcases System.Platform.numBits_eq with h | h <;> simp [UScalarTy.numBits, h]
  have hmax : Usize.max = 2 ^ UScalarTy.Usize.numBits - 1 := usize_max_eq
  have hp : 4 ≤ 2 ^ UScalarTy.Usize.numBits := by
    calc 4 = 2 ^ 2 := rfl
      _ ≤ _ := Nat.pow_le_pow_right (by omega) hw
  unfold mmcs.hax_reshaped.validate_heights
  rw [hm, bind_ok, ite_eq_right (fun h0 => by rw [h0] at hM; simp at hM; omega)]
  obtain ⟨lg, hlg, hlgv⟩ := log2_ceil_ok m
  rw [clog_eq, hM, clog_max] at hlgv
  rw [hlg, bind_ok]
  have hv : (dims2 w0 m w1 h).val =
      [{ width := w0, height := m }, { width := w1, height := h }] := by simp [dims2]
  have hlen : Slice.len (dims2 w0 m w1 h) = 2#usize := by
    apply UScalar.eq_of_val_eq; simp [hv]
  have h1 : (1#usize : Std.Usize).val = 1 := rfl
  obtain ⟨m1, hm1, hm1v⟩ := usize_sub_eq (x := m) (y := 1#usize) (by rw [h1]; omega)
  unfold mmcs.hax_reshaped.validate_heights_loop1
  -- The tallest matrix passes: it sits at depth 0.
  rw [loop]
  unfold mmcs.hax_reshaped.validate_heights_loop1.body
  simp only [core.slice.Slice.len, rust_primitives.slice.slice_length, bind_ok]
  rw [hlen, ite_eq_left (by decide), Lib.slice_index_eq _ _ (by simp [hv]), bind_ok]
  simp only [hv, List.getElem_cons_zero, show (0#usize : Std.Usize).val = 0 from rfl]
  obtain ⟨b0, hb0, hb0v⟩ := usize_sub_eq (x := lg) (y := lg) le_rfl
  obtain ⟨s0, hs0, hs0v⟩ := usize_shr_eq (x := m1) (y := b0) (by rw [hb0v]; omega)
  obtain ⟨e0, he0, he0v⟩ := usize_add_eq (x := s0) (y := 1#usize) (by
    rw [hs0v, hb0v, hm1v, h1]; simp; omega)
  have he0m : e0 = m := by
    apply UScalar.eq_of_val_eq; rw [he0v, hs0v, hb0v, hm1v, h1]; simp; omega
  rw [hlg, bind_ok, hb0, bind_ok, hm1, bind_ok, hs0, bind_ok, he0, bind_ok, he0m]
  simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, bind_ok]
  obtain ⟨one, hone, honev⟩ := usize_add_eq (x := 0#usize) (y := 1#usize) (by
    rw [h1, show (0#usize : Std.Usize).val = 0 from rfl, hmax]
    omega)
  have honev' : one.val = 1 := by rw [honev, h1]; rfl
  rw [hone, bind_ok]
  -- The short matrix sits a full word of halvings down, and the shift overflows.
  rw [bind_ok]
  dsimp only
  rw [loop]
  rw [ite_eq_left (show one < 2#usize by
    show one.val < (2#usize : Std.Usize).val; rw [honev']; decide)]
  rw [Lib.slice_index_eq _ _ (by simp [hv, honev']), bind_ok]
  simp only [hv, honev', List.getElem_cons_succ, List.getElem_cons_zero]
  obtain ⟨c, hc, hcv⟩ := log2_ceil_ok h
  rw [ite_eq_left hh] at hcv
  obtain ⟨b1, hb1, hb1v⟩ := usize_sub_eq (x := lg) (y := c) (by omega)
  have hshr : m1 >>> b1 = RustM.fail .panic := by
    simp only [HShiftRight.hShiftRight, UScalar.shiftRight_UScalar, UScalar.shiftRight]
    rw [ite_eq_right (by rw [hb1v, hlgv, hcv]; omega)]
  rw [hc, bind_ok, hb1, bind_ok, hshr, bind_fail, bind_fail]

variable {P PW F W H C : Type} {N DIGEST_ELEMS : Std.Usize} in
/-- The verifier panics on those dimensions once it holds one row per matrix.

So no index, rows, siblings or cap avoid the panic. -/
theorem verify_panics_max (cl : core.clone.Clone F) (cp : core.marker.Copy W)
    (dfInst : core.default.Default W) (eqInst : core.cmp.PartialEq W W)
    (hInst : p3_symmetric.hasher.CryptographicHasher H F (Std.Array W DIGEST_ELEMS))
    (cInst : p3_symmetric.compression.PseudoCompressionFunction C (Std.Array W DIGEST_ELEMS) N)
    (mt : mmcs.MerkleTreeMmcs P PW H C N DIGEST_ELEMS)
    (commit : p3_symmetric.hash.MerkleCap F (Std.Array W DIGEST_ELEMS))
    (w0 w1 M h : Std.Usize) (hM : M.val = Usize.max) (hh : h.val ≤ 1) (index : Std.Usize)
    (opened : Slice (alloc.vec.Vec F)) (hlen : opened.val.length = 2)
    (proof : Slice (Std.Array W DIGEST_ELEMS)) :
    mmcs.hax_reshaped.verify_batch cl cp dfInst eqInst hInst cInst mt commit (dims2 w0 M w1 h) index
      opened proof = RustM.fail .panic := by
  unfold mmcs.hax_reshaped.verify_batch
  have hl : Slice.len (dims2 w0 M w1 h) = Slice.len opened := by
    apply UScalar.eq_of_val_eq; simp [dims2, hlen]
  simp only [core.slice.Slice.len, rust_primitives.slice.slice_length, bind_ok, hl,
    bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
  rw [validate_panics_max w0 w1 M h hM hh, bind_fail]

end Plonky3Lean.Proofs.MerkleTree
