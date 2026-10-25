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

/-! ## The checks on the dimensions return -/

theorem slice_insert_eq {α : Type} (v : Slice α) (j : Std.Usize) (x : α)
    (hj : j.val ≤ v.val.length) (hl : v.val.length + 1 ≤ Usize.max) :
    ∃ w, alloc.vec.Vec.insert (show alloc.vec.Vec α from v) j x = RustM.ok w := by
  have h2 : j.val < Usize.max := by omega
  have h3 : j.val + 1 + (v.val.length - j.val) ≤ Usize.max := by omega
  have hlen : (Slice.len v).val = v.val.length := by simp
  simp only [alloc.vec.Vec.insert, rust_primitives.sequence.seq_len,
    rust_primitives.sequence.seq_drain, bind_ok]
  rw [dite_eq_left_of_eq_true (eq_true ⟨by rw [hlen]; exact hj, by rw [hlen]⟩), bind_ok]
  show ∃ w, (do
      let s1 ← rust_primitives.sequence.seq_push
        (Slice.from (List.take j.val v.val ++ List.drop (Slice.len v).val v.val) (by
          simp only [List.length_append, List.length_take, List.length_drop]; omega)) x
      let (s2, _) ← rust_primitives.sequence.seq_concat s1
        (Slice.from (List.take ((Slice.len v).val - j.val) (List.drop j.val v.val)) (by
          simp only [List.length_take, List.length_drop]; omega))
      RustM.ok s2) = RustM.ok w
  simp [rust_primitives.sequence.seq_push, rust_primitives.sequence.seq_concat, hlen, h2]
  erw [bind_ok]
  rw [dite_eq_left_of_eq_true (eq_true (by simp only [Slice.from_val, List.length_append,
    List.length_take, List.length_singleton, Nat.min_eq_left hj]; omega))]
  erw [bind_ok]
  exact ⟨_, rfl⟩

theorem vec_insert_eq {α : Type} (v : alloc.vec.Vec α) (j : Std.Usize) (x : α)
    (hj : j.val ≤ v.val.length) (hl : v.val.length + 1 ≤ Usize.max) :
    ∃ w, alloc.vec.Vec.insert v j x = RustM.ok w :=
  slice_insert_eq v j x hj hl

theorem vec_new_ok (α : Type) :
    alloc.vec.Vec.new α = RustM.ok (show alloc.vec.Vec α from Slice.new α) := by
  simp [alloc.vec.Vec.new, rust_primitives.sequence.seq_empty]

theorem vec_len_eq {α : Type} (v : alloc.vec.Vec α) :
    alloc.vec.Vec.len v = RustM.ok (Slice.len v) := by
  simp [alloc.vec.Vec.len, rust_primitives.sequence.seq_len]

theorem usize_succ_eq {i : Std.Usize} (h : i.val < Usize.max) :
    ∃ i2, i + 1#usize = RustM.ok i2 ∧ i2.val = i.val + 1 := by
  obtain ⟨i2, hi2, hv⟩ := usize_add_eq (x := i) (y := 1#usize) (by simp; omega)
  exact ⟨i2, hi2, by simpa using hv⟩

/-- The insertion scan returns a position in the order. -/
theorem insert_scan_total (dims : Slice p3_matrix.Dimensions) (order : alloc.vec.Vec Std.Usize)
    (height : Std.Usize) (hord : ∀ x ∈ order.val, x.val < dims.val.length) :
    ∃ j, mmcs.hax_reshaped.tallest_first_loop0_loop0 dims order height 0#usize = RustM.ok j ∧
      j.val ≤ order.val.length := by
  unfold mmcs.hax_reshaped.tallest_first_loop0_loop0
  refine loop_total_post _ (fun j : Std.Usize => j.val ≤ order.val.length)
    (fun j : Std.Usize => j.val ≤ order.val.length) (fun j => order.val.length - j.val) ?_ _ (by simp)
  intro j hj
  unfold mmcs.hax_reshaped.tallest_first_loop0_loop0.body
  rw [vec_len_eq, bind_ok]
  by_cases hlt : j.val < order.val.length
  · rw [ite_eq_left (show j < Slice.len order by simpa using hlt), vec_index_eq order j hlt, bind_ok,
      Lib.slice_index_eq dims _ (hord _ (List.getElem_mem hlt)), bind_ok]
    split
    · have hmax : order.val.length ≤ Usize.max := by scalar_tac
      obtain ⟨j1, hj1, hj1v⟩ := usize_succ_eq (i := j) (by omega)
      rw [hj1, bind_ok]
      exact ⟨_, rfl, by omega, by omega⟩
    · exact ⟨_, rfl, hj⟩
  · rw [ite_eq_right (show ¬ j < Slice.len order by simpa using hlt)]
    exact ⟨_, rfl, hj⟩

/-- The insertion sort of the matrix indices returns. -/
theorem tallest_first_total (dims : Slice p3_matrix.Dimensions) :
    ∃ order, mmcs.hax_reshaped.tallest_first dims = RustM.ok order := by
  unfold mmcs.hax_reshaped.tallest_first
  rw [vec_new_ok, bind_ok]
  unfold mmcs.hax_reshaped.tallest_first_loop0
  have hmax : dims.val.length ≤ Usize.max := by scalar_tac
  refine loop_total _ (fun x : alloc.vec.Vec Std.Usize × Std.Usize => x.2.val ≤ dims.val.length ∧
      x.1.val.length = x.2.val ∧ ∀ y ∈ x.1.val, y.val < dims.val.length)
    (fun x => dims.val.length - x.2.val) ?_ _ ⟨by simp, by simp, by simp⟩
  rintro ⟨o, i⟩ ⟨hi, hlen, hb⟩
  dsimp only at hi hlen hb
  unfold mmcs.hax_reshaped.tallest_first_loop0.body
  simp only [core.slice.Slice.len, rust_primitives.slice.slice_length, bind_ok]
  by_cases hlt : i.val < dims.val.length
  · rw [ite_eq_left (show i < Slice.len dims by simpa using hlt), Lib.slice_index_eq dims i hlt, bind_ok]
    obtain ⟨j, hj, hjle⟩ := insert_scan_total dims o (dims.val[i.val]).height hb
    rw [hj, bind_ok]
    obtain ⟨o1, ho1⟩ := vec_insert_eq o j i hjle (by omega)
    rw [ho1, bind_ok]
    obtain ⟨i2, hi2, hi2v⟩ := usize_succ_eq (i := i) (by omega)
    rw [hi2, bind_ok]
    have ho1v := vec_insert_ok ho1
    refine ⟨_, rfl, ⟨?_, ?_, ?_⟩, ?_⟩ <;> dsimp only
    · omega
    · rw [ho1v]; simp; omega
    · intro y hy
      rw [ho1v] at hy
      simp only [List.mem_append, List.mem_cons] at hy
      rcases hy with hy | rfl | hy
      · exact hb y (List.mem_of_mem_take hy)
      · exact hlt
      · exact hb y (List.mem_of_mem_drop hy)
    · omega
  · rw [ite_eq_right (show ¬ i < Slice.len dims by simpa using hlt)]
    exact ⟨_, rfl, trivial⟩

/-- The padded width of a power-of-two layer, for arity 2. -/
theorem padded_pow_total {x : Std.Usize} {k : ℕ} (hx : x.val = 2 ^ k) :
    ∃ r, p3_merkle_tree.merkle_tree.padded_len x 2#usize = RustM.ok r ∧ r.val = 2 ^ k := by
  have hb : x.val ≤ Usize.max := by scalar_tac
  unfold p3_merkle_tree.merkle_tree.padded_len
  split
  · exact ⟨_, rfl, hx⟩
  · rename_i h1
    have h1' : ¬ x.val ≤ 1 := h1
    rw [ite_eq_left (show 2#usize ≤ x by show (2#usize : Std.Usize).val ≤ x.val; simp; omega)]
    unfold core.num.Usize.div_ceil
    obtain ⟨d, hd, hdv⟩ := usize_div_eq (x := x) (y := 2#usize) (by simp)
    obtain ⟨m, hm, hmv⟩ := usize_rem_eq (x := x) (y := 2#usize) (by simp)
    have hk : 1 ≤ k := by
      rcases k with _ | k
      · simp at hx; omega
      · omega
    have hmod : x.val % 2 = 0 := by rw [hx]; exact Nat.two_pow_mod_two_eq_zero.2 (by omega)
    rw [hd, bind_ok, hm, bind_ok, ite_eq_right (by
      show ¬ (0 : ℕ) < m.val; rw [hmv]; simp [hmod])]
    obtain ⟨p, hp, hpv⟩ := usize_mul_eq (x := d) (y := 2#usize) (by
      rw [hdv]; simp; omega)
    refine ⟨p, by rw [bind_ok]; exact hp, ?_⟩
    rw [hpv, hdv]; simp; omega

/-- The leaf scan of the schedule returns. -/
theorem sched_leaf_total (dims : Slice p3_matrix.Dimensions) (order : alloc.vec.Vec Std.Usize)
    (lnpt : Std.Usize) (hord : ∀ x ∈ order.val, x.val < dims.val.length)
    (hh : ∀ d ∈ dims.val, d.height.val ≤ 2 ^ (UScalarTy.Usize.numBits - 1)) :
    ∃ p, mmcs.hax_reshaped.arity_schedule_and_proof_levels_loop0 dims order lnpt 0#usize =
      RustM.ok p := by
  unfold mmcs.hax_reshaped.arity_schedule_and_proof_levels_loop0
  refine loop_total _ (fun p : Std.Usize => p.val ≤ order.val.length)
    (fun p => order.val.length - p.val) ?_ _ (by simp)
  intro p hp
  unfold mmcs.hax_reshaped.arity_schedule_and_proof_levels_loop0.body
  rw [vec_len_eq, bind_ok]
  by_cases hlt : p.val < order.val.length
  · have hi := hord _ (List.getElem_mem hlt)
    rw [ite_eq_left (show p < Slice.len order by simpa using hlt), vec_index_eq order p hlt, bind_ok,
      Lib.slice_index_eq dims _ hi, bind_ok]
    obtain ⟨r, hr, -⟩ := npt_eq (hh _ (List.getElem_mem hi))
    rw [hr, bind_ok]
    split
    · have hmax : order.val.length ≤ Usize.max := by scalar_tac
      obtain ⟨p1, hp1, hp1v⟩ := usize_succ_eq (i := p) (by omega)
      rw [hp1, bind_ok]
      exact ⟨_, rfl, by omega, by omega⟩
    · exact ⟨_, rfl, trivial⟩
  · rw [ite_eq_right (show ¬ p < Slice.len order by simpa using hlt)]
    exact ⟨_, rfl, trivial⟩

/-- The leaf scan of the verifier returns. -/
theorem verify_leaf_total (dims : Slice p3_matrix.Dimensions) (order : alloc.vec.Vec Std.Usize)
    (lnpt : Std.Usize) (hord : ∀ x ∈ order.val, x.val < dims.val.length)
    (hh : ∀ d ∈ dims.val, d.height.val ≤ 2 ^ (UScalarTy.Usize.numBits - 1)) :
    ∃ p, mmcs.hax_reshaped.verify_batch_loop1 dims order lnpt 0#usize = RustM.ok p := by
  unfold mmcs.hax_reshaped.verify_batch_loop1
  refine loop_total _ (fun p : Std.Usize => p.val ≤ order.val.length)
    (fun p => order.val.length - p.val) ?_ _ (by simp)
  intro p hp
  unfold mmcs.hax_reshaped.verify_batch_loop1.body
  rw [vec_len_eq, bind_ok]
  by_cases hlt : p.val < order.val.length
  · have hi := hord _ (List.getElem_mem hlt)
    rw [ite_eq_left (show p < Slice.len order by simpa using hlt), vec_index_eq order p hlt, bind_ok,
      Lib.slice_index_eq dims _ hi, bind_ok]
    obtain ⟨r, hr, -⟩ := npt_eq (hh _ (List.getElem_mem hi))
    rw [hr, bind_ok]
    split
    · have hmax : order.val.length ≤ Usize.max := by scalar_tac
      obtain ⟨p1, hp1, hp1v⟩ := usize_succ_eq (i := p) (by omega)
      rw [hp1, bind_ok]
      exact ⟨_, rfl, by omega, by omega⟩
    · exact ⟨_, rfl, trivial⟩
  · rw [ite_eq_right (show ¬ p < Slice.len order by simpa using hlt)]
    exact ⟨_, rfl, trivial⟩

/-- The scan past one injected height returns, at or after where it starts. -/
theorem sched_advance_total (dims : Slice p3_matrix.Dimensions) (order : alloc.vec.Vec Std.Usize)
    (nh : Std.Usize) (hord : ∀ x ∈ order.val, x.val < dims.val.length) (pos : Std.Usize)
    (hpos : pos.val ≤ order.val.length) :
    ∃ p1, mmcs.hax_reshaped.arity_schedule_and_proof_levels_loop1_loop0 dims order pos nh =
      RustM.ok p1 ∧ p1.val ≤ order.val.length := by
  unfold mmcs.hax_reshaped.arity_schedule_and_proof_levels_loop1_loop0
  refine loop_total_post _ (fun p : Std.Usize => p.val ≤ order.val.length)
    (fun p : Std.Usize => p.val ≤ order.val.length) (fun p => order.val.length - p.val) ?_ _ hpos
  intro p hp
  unfold mmcs.hax_reshaped.arity_schedule_and_proof_levels_loop1_loop0.body
  rw [vec_len_eq, bind_ok]
  by_cases hlt : p.val < order.val.length
  · rw [ite_eq_left (show p < Slice.len order by simpa using hlt), vec_index_eq order p hlt, bind_ok,
      Lib.slice_index_eq dims _ (hord _ (List.getElem_mem hlt)), bind_ok]
    split
    · have hmax : order.val.length ≤ Usize.max := by scalar_tac
      obtain ⟨p1, hp1, hp1v⟩ := usize_succ_eq (i := p) (by omega)
      rw [hp1, bind_ok]
      exact ⟨_, rfl, by omega, by omega⟩
    · exact ⟨_, rfl, hp⟩
  · rw [ite_eq_right (show ¬ p < Slice.len order by simpa using hlt)]
    exact ⟨_, rfl, hp⟩

theorem selectSpec_two (curr lnpt : ℕ) (height : ℕ → ℕ) (order : List ℕ) (from' : ℕ) :
    selectSpec 2 curr lnpt height order from' = 2 := by
  unfold selectSpec; split_ifs <;> rfl

/-- With arity 2, the arity choice returns. -/
theorem select_two_total (curr lnpt : Std.Usize) (dims : Slice p3_matrix.Dimensions)
    (order : Slice Std.Usize) (from' : Std.Usize) (hord : ∀ x ∈ order.val, x.val < dims.val.length)
    (hh : ∀ d ∈ dims.val, d.height.val ≤ 2 ^ (UScalarTy.Usize.numBits - 1)) :
    ∃ v, mmcs.hax_reshaped.select_arity_step 2#usize curr lnpt dims order from' = RustM.ok v := by
  unfold mmcs.hax_reshaped.select_arity_step
  split
  · exact ⟨_, rfl⟩
  obtain ⟨q, hq, hqv⟩ := usize_div_eq (x := curr) (y := 2#usize) (by simp)
  rw [hq, bind_ok]
  obtain ⟨t, ht, -⟩ := npt_eq (x := q) (by rw [hqv]; simpa using half_le_pow curr)
  rw [ht, bind_ok]
  unfold mmcs.hax_reshaped.select_arity_step_loop
  have hmax : order.val.length ≤ Usize.max := by scalar_tac
  refine loop_total _ (fun _ => True) (fun k : Std.Usize => order.val.length - k.val) ?_ _ trivial
  intro k _
  unfold mmcs.hax_reshaped.select_arity_step_loop.body
  simp only [core.slice.Slice.len, rust_primitives.slice.slice_length, bind_ok]
  by_cases hlt : k.val < order.val.length
  · have hi := hord _ (List.getElem_mem hlt)
    rw [ite_eq_left (show k < Slice.len order by simpa using hlt), Lib.slice_index_eq order k hlt,
      bind_ok, Lib.slice_index_eq dims _ hi, bind_ok]
    obtain ⟨r, hr, -⟩ := npt_eq (hh _ (List.getElem_mem hi))
    rw [hr, bind_ok]
    obtain ⟨k1, hk1, hk1v⟩ := usize_succ_eq (i := k) (by omega)
    split
    · split
      · exact ⟨_, rfl, trivial⟩
      · rw [hk1, bind_ok]; exact ⟨_, rfl, trivial, by omega⟩
    · rw [hk1, bind_ok]; exact ⟨_, rfl, trivial, by omega⟩
  · rw [ite_eq_right (show ¬ k < Slice.len order by simpa using hlt)]
    exact ⟨_, rfl, trivial⟩

theorem vec_push_total {T : Type} (v : alloc.vec.Vec T) (x : T) (h : v.val.length + 1 ≤ Usize.max) :
    ∃ v', alloc.vec.Vec.push v x = RustM.ok v' ∧ v'.val = v.val ++ [x] := by
  have h' : (v.val ++ [x]).length ≤ Usize.max := by simpa using h
  refine ⟨Slice.from (v.val ++ [x]) h', ?_, Slice.from_val _ _⟩
  simp [alloc.vec.Vec.push, rust_primitives.sequence.seq_push, show v.val.length < Usize.max by omega]

theorem numBits_lt_max : UScalarTy.Usize.numBits < Usize.max := by
  rw [usize_max_eq]
  have := Nat.lt_two_pow_self (n := UScalarTy.Usize.numBits)
  have hw : 2 ≤ UScalarTy.Usize.numBits := by
    rcases System.Platform.numBits_eq with h | h <;> simp [UScalarTy.numBits, h]
  have : UScalarTy.Usize.numBits + 1 < 2 ^ UScalarTy.Usize.numBits := by
    rcases System.Platform.numBits_eq with h | h <;> simp [UScalarTy.numBits, h]
  omega

/-- With arity 2, the schedule loop returns from a power-of-two width.

It halves the width at each level. -/
theorem sched_two_total (dims : Slice p3_matrix.Dimensions) (order : alloc.vec.Vec Std.Usize)
    (lnpt : Std.Usize) (hord : ∀ x ∈ order.val, x.val < dims.val.length)
    (hh : ∀ d ∈ dims.val, d.height.val ≤ 2 ^ (UScalarTy.Usize.numBits - 1))
    (k : ℕ) (curr pos : Std.Usize) (sched : alloc.vec.Vec Std.Usize) (hc : curr.val = 2 ^ k)
    (hp : pos.val ≤ order.val.length) (hk : k + sched.val.length < UScalarTy.Usize.numBits) :
    ∃ v, mmcs.hax_reshaped.arity_schedule_and_proof_levels_loop1 2#usize dims order curr lnpt pos
      sched = RustM.ok v := by
  unfold mmcs.hax_reshaped.arity_schedule_and_proof_levels_loop1
  have hmw := numBits_lt_max
  refine loop_total _ (fun x : Std.Usize × Std.Usize × alloc.vec.Vec Std.Usize => ∃ k,
      x.1.val = 2 ^ k ∧ x.2.1.val ≤ order.val.length ∧ k + x.2.2.val.length < UScalarTy.Usize.numBits)
    (fun x => x.1.val) ?_ _ ⟨k, hc, hp, hk⟩
  rintro ⟨c, p, sc⟩ ⟨k, hc, hp, hk⟩
  dsimp only at hc hp hk
  unfold mmcs.hax_reshaped.arity_schedule_and_proof_levels_loop1.body
  simp only
  by_cases hc1 : 1 < c.val
  · have hk1 : 1 ≤ k := by
      rcases k with _ | k
      · simp at hc; omega
      · omega
    rw [ite_eq_left (show c > 1#usize by show (1#usize : Std.Usize).val < c.val; simpa using hc1)]
    simp only [alloc.vec.Vec.Insts.CoreOpsDerefDerefSlice.deref, as_slice_eq, bind_ok]
    have hordS : ∀ x ∈ (vs order).val, x.val < dims.val.length := by rw [vs_val]; exact hord
    obtain ⟨step, hstep⟩ := select_two_total c lnpt dims (vs order) p hordS hh
    have hsv : step.val = 2 := by rw [select_ok_eq hstep]; exact selectSpec_two _ _ _ _ _
    rw [hstep, bind_ok]
    obtain ⟨sc1, hsc1, hsc1v⟩ := vec_push_total sc step (by omega)
    rw [hsc1, bind_ok]
    obtain ⟨ln, hln, hlnv⟩ := usize_div_eq (x := c) (y := step) (by omega)
    have hlnv' : ln.val = 2 ^ (k - 1) := by
      rw [hlnv, hsv, hc, show k = k - 1 + 1 by omega, pow_succ, Nat.mul_div_cancel _ (by omega)]
      simp
    rw [hln, bind_ok]
    obtain ⟨c1, hc1', hc1v⟩ := padded_pow_total hlnv'
    rw [hc1', bind_ok]
    obtain ⟨t, ht, -⟩ := npt_eq (x := ln) (by
      rw [hlnv']; exact Nat.pow_le_pow_right (by omega) (by omega))
    rw [ht, bind_ok, vec_len_eq, bind_ok]
    have hdec : c1.val < c.val := by
      rw [hc1v, hc]; exact Nat.pow_lt_pow_right (by omega) (by omega)
    have hinv : ∀ p' : Std.Usize, p'.val ≤ order.val.length →
        (∃ k', c1.val = 2 ^ k' ∧ p'.val ≤ order.val.length ∧
          k' + sc1.val.length < UScalarTy.Usize.numBits) :=
      fun p' hp' => ⟨k - 1, hc1v, hp', by rw [hsc1v, List.length_append, List.length_singleton]; omega⟩
    by_cases hlt : p.val < order.val.length
    · have hi := hord _ (List.getElem_mem hlt)
      rw [ite_eq_left (show p < Slice.len order by simpa using hlt), vec_index_eq order p hlt, bind_ok,
        Lib.slice_index_eq dims _ hi, bind_ok]
      obtain ⟨r, hr, -⟩ := npt_eq (hh _ (List.getElem_mem hi))
      rw [hr, bind_ok]
      split
      · obtain ⟨p1, hp1, hp1le⟩ := sched_advance_total dims order _ hord p hp
        rw [hp1, bind_ok]
        exact ⟨_, rfl, hinv p1 hp1le, hdec⟩
      · exact ⟨_, rfl, hinv p hp, hdec⟩
    · rw [ite_eq_right (show ¬ p < Slice.len order by simpa using hlt)]
      exact ⟨_, rfl, hinv p hp, hdec⟩
  · rw [ite_eq_right (show ¬ c > 1#usize by
      show ¬ (1#usize : Std.Usize).val < c.val; simpa using hc1)]
    exact ⟨_, rfl, trivial⟩

/-- Power-of-two heights fit in half the word range. -/
theorem pow_heights_le {dims : Slice p3_matrix.Dimensions} (hpow : PowHeights dims) :
    ∀ d ∈ dims.val, d.height.val ≤ 2 ^ (UScalarTy.Usize.numBits - 1) := by
  intro d hd
  have he := lt_numBits_of_pow (hpow d hd).symm
  rw [← hpow d hd]
  exact Nat.pow_le_pow_right (by omega) (by omega)

/-- With arity 2, the schedule returns on power-of-two heights. -/
theorem arity_two_total {cap : Std.Usize} {dims : Slice p3_matrix.Dimensions} (hpow : PowHeights dims)
    (hne : dims.val ≠ []) :
    ∃ sched pl, mmcs.hax_reshaped.arity_schedule_and_proof_levels 2#usize cap dims =
      RustM.ok (core.result.Result.Ok (sched, pl)) := by
  have hh := pow_heights_le hpow
  obtain ⟨val, hval, hvm⟩ := validate_binary hpow hne
  have hpos : 0 < maxHeight dims := hvm ▸ (validate_ok_val hval).2
  have hv2 : val.val = 2 ^ Nat.log 2 val.val := by rw [hvm]; exact (maxHeight_pow hpow hpos).1
  have hnb := lt_numBits_of_pow hv2
  obtain ⟨order, horder⟩ := tallest_first_total dims
  have hord := tallest_first_ok horder
  obtain ⟨curr, hcurr, hcv⟩ := padded_pow_total hv2
  obtain ⟨lnpt, hlnpt, -⟩ := npt_eq (x := val) (by rw [hv2]; exact Nat.pow_le_pow_right (by omega) (by omega))
  obtain ⟨pos0, hpos0⟩ := sched_leaf_total dims order lnpt hord hh
  have hp0 : pos0.val ≤ order.val.length := by
    rw [sched_leaf_loop_ok dims order lnpt 0#usize pos0 hpos0,
      show (0#usize : Std.Usize).val = 0 from rfl, leafEnd_eq_advance _ _ _ _ 0 rfl, ← ordL_length]
    exact advance_le _ _ _ _ (by simp)
  obtain ⟨sched, hsched⟩ := sched_two_total dims order lnpt hord hh _ curr pos0 _ hcv hp0
    (by
      have hu : UScalarTy.Usize.numBits = System.Platform.numBits := rfl
      show _ + (Slice.new Std.Usize).val.length < _; simp; omega)
  unfold mmcs.hax_reshaped.arity_schedule_and_proof_levels
  rw [hval, bind_ok, branch_ok_eq, bind_ok]
  simp only
  rw [horder, bind_ok, hcurr, bind_ok, hlnpt, bind_ok, hpos0, bind_ok, vec_new_ok, bind_ok, hsched,
    bind_ok, vec_len_eq, bind_ok]
  obtain ⟨e, he, hev⟩ : ∃ e : Std.Usize, (if cap < Slice.len sched then RustM.ok cap
      else RustM.ok (Slice.len sched)) = RustM.ok e ∧ e.val ≤ (Slice.len sched).val := by
    split
    · rename_i h; exact ⟨_, rfl, le_of_lt h⟩
    · exact ⟨_, rfl, le_rfl⟩
  rw [he, bind_ok]
  obtain ⟨i, hi, -⟩ := usize_sub_eq hev
  rw [hi, bind_ok]
  exact ⟨_, _, rfl⟩

/-- The cap size loop returns on a schedule of binary steps shorter than the word size. -/
theorem cap_loop_total {sched : alloc.vec.Vec Std.Usize} {n : ℕ}
    (hs : sched.val.map (fun s => s.val) = List.replicate n 2) (hn : n < UScalarTy.Usize.numBits)
    (pl : Std.Usize) : ∃ e, mmcs.hax_reshaped.check_cap_size_loop sched 1#usize pl = RustM.ok e := by
  have hlen : sched.val.length = n := by simpa using congrArg List.length hs
  have hget : ∀ l (h : l < sched.val.length), (sched.val[l]).val = 2 := fun l h => by
    have := congrArg (fun L => L[l]?) hs
    simp only [List.getElem?_map, List.getElem?_eq_getElem h, Option.map_some] at this
    rw [List.getElem?_replicate, ite_eq_left (by omega)] at this
    exact Option.some.inj this
  have hmax : 2 ^ n ≤ Usize.max := by
    rw [usize_max_eq]
    have : 2 ^ n < 2 ^ UScalarTy.Usize.numBits := Nat.pow_lt_pow_right (by omega) hn
    omega
  unfold mmcs.hax_reshaped.check_cap_size_loop
  refine loop_total _ (fun x : Std.Usize × Std.Usize => x.1.val * 2 ^ (n - x.2.val) ≤ 2 ^ n)
    (fun x => n - x.2.val) ?_ _ (by
      show (1#usize : Std.Usize).val * _ ≤ _
      simp only [show (1#usize : Std.Usize).val = 1 from rfl, one_mul]
      exact Nat.pow_le_pow_right (by omega) (by omega))
  rintro ⟨a, l⟩ hinv
  dsimp only at hinv
  unfold mmcs.hax_reshaped.check_cap_size_loop.body
  simp only [alloc.vec.Vec.len, rust_primitives.sequence.seq_len, bind_ok]
  by_cases hlt : l.val < sched.val.length
  · rw [ite_eq_left (show l < Slice.len sched by simpa using hlt), vec_index_eq sched l hlt, bind_ok]
    have h2 := hget l.val hlt
    have hpow : 2 ^ (n - l.val) = 2 * 2 ^ (n - (l.val + 1)) := by
      rw [← pow_succ']; congr 1; omega
    obtain ⟨a1, ha1, ha1v⟩ := usize_mul_eq (x := a) (y := sched.val[l.val]) (by
      rw [h2]
      have : a.val * 2 ≤ a.val * 2 ^ (n - l.val) := by
        rw [hpow]; nlinarith [Nat.one_le_two_pow (n := n - (l.val + 1))]
      omega)
    rw [ha1, bind_ok]
    have hmw := numBits_lt_max
    obtain ⟨l1, hl1, hl1v⟩ := usize_succ_eq (i := l) (by omega)
    rw [hl1, bind_ok]
    refine ⟨_, rfl, ?_, ?_⟩ <;> dsimp only
    · rw [ha1v, h2, hl1v]
      rw [hpow] at hinv
      nlinarith
    · omega
  · rw [ite_eq_right (show ¬ l < Slice.len sched by simpa using hlt)]
    exact ⟨_, rfl, trivial⟩

/-- The sibling count loop returns on binary steps shorter than the word size. -/
theorem sum_loop_total {sched : alloc.vec.Vec Std.Usize} (h2 : ∀ s ∈ sched.val, s.val = 2)
    (hn : sched.val.length < UScalarTy.Usize.numBits) :
    ∃ e, mmcs.hax_reshaped.verify_batch_loop0 sched 0#usize 0#usize = RustM.ok e := by
  have hmw := numBits_lt_max
  unfold mmcs.hax_reshaped.verify_batch_loop0
  refine loop_total _ (fun x : Std.Usize × Std.Usize => x.1.val ≤ x.2.val)
    (fun x => sched.val.length - x.2.val) ?_ _ (by simp)
  rintro ⟨a, l⟩ hinv
  dsimp only at hinv
  unfold mmcs.hax_reshaped.verify_batch_loop0.body
  simp only [alloc.vec.Vec.len, rust_primitives.sequence.seq_len, bind_ok]
  by_cases hlt : l.val < sched.val.length
  · rw [ite_eq_left (show l < Slice.len sched by simpa using hlt), vec_index_eq sched l hlt, bind_ok]
    have hs := h2 _ (List.getElem_mem hlt)
    obtain ⟨s1, hs1, hs1v⟩ := usize_sub_eq (x := sched.val[l.val]) (y := 1#usize) (by
      rw [hs]; simp)
    rw [hs1, bind_ok]
    obtain ⟨a1, ha1, ha1v⟩ := usize_add_eq (x := a) (y := s1) (by
      rw [hs1v, hs]; simp; omega)
    rw [ha1, bind_ok]
    obtain ⟨l1, hl1, hl1v⟩ := usize_succ_eq (i := l) (by omega)
    rw [hl1, bind_ok]
    refine ⟨_, rfl, ?_, ?_⟩ <;> dsimp only
    · rw [ha1v, hs1v, hs, hl1v]; simp; omega
    · omega
  · rw [ite_eq_right (show ¬ l < Slice.len sched by simpa using hlt)]
    exact ⟨_, rfl, trivial⟩

/-- With arity 2, every batch of power-of-two heights passes the verifier's checks on the dimensions.

So the single-index verifier never panics on such a batch, whatever the cap height. -/
theorem dims_pass_binary {cap : Std.Usize} {dims : Slice p3_matrix.Dimensions}
    (hpow : PowHeights dims) (hne : dims.val ≠ []) : DimsPass 2#usize cap dims := by
  have hh := pow_heights_le hpow
  obtain ⟨val, hval, hvm⟩ := validate_binary hpow hne
  have hpos : 0 < maxHeight dims := hvm ▸ (validate_ok_val hval).2
  have hv2 : val.val = 2 ^ Nat.log 2 val.val := by rw [hvm]; exact (maxHeight_pow hpow hpos).1
  have hnb := lt_numBits_of_pow hv2
  obtain ⟨sched, pl, hsched⟩ := arity_two_total (cap := cap) hpow hne
  obtain ⟨order, horder⟩ := tallest_first_total dims
  have hord := tallest_first_ok horder
  obtain ⟨curr, hcurr, -⟩ := padded_pow_total hv2
  obtain ⟨lnpt, hlnpt, -⟩ := npt_eq (x := val) (by
    rw [hv2]; exact Nat.pow_le_pow_right (by omega) (by omega))
  obtain ⟨pos, hpos⟩ := verify_leaf_total dims order lnpt hord hh
  obtain ⟨-, -, hs, -, -, -⟩ := layout_binary hpow hval hsched horder hcurr hlnpt hpos
  obtain ⟨expected, hexp⟩ := cap_loop_total hs hnb pl
  obtain ⟨sched1, hsched1⟩ := truncate_total sched pl
  have h2 : ∀ s ∈ sched1.val, s.val = 2 := by
    intro s hsm
    rw [vec_truncate_ok hsched1] at hsm
    have : s.val ∈ sched.val.map (fun s => s.val) := List.mem_map_of_mem (List.mem_of_mem_take hsm)
    rw [hs] at this
    exact List.eq_of_mem_replicate this
  have hlen1 : sched1.val.length < UScalarTy.Usize.numBits := by
    have : sched.val.length = Nat.log 2 val.val := by simpa using congrArg List.length hs
    rw [vec_truncate_ok hsched1, List.length_take]; omega
  obtain ⟨epl, hepl⟩ := sum_loop_total h2 hlen1
  exact ⟨val, sched, pl, expected, sched1, epl, order, curr, lnpt, pos, hval, hsched, hexp, hsched1,
    hepl, horder, hcurr, hlnpt, hpos, hh⟩

end Plonky3Lean.Proofs.MerkleTree
