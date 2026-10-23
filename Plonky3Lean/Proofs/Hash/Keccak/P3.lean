module

public import P3Keccak
public import Plonky3Lean.Lib.Slice
public import Plonky3Lean.Proofs.Hash.Keccak.Permutation
public import Plonky3Lean.Proofs.Hash.Keccak.Sponge

@[expose] public section

/-!
# p3-keccak: the permutation on words and on bytes

On `[u64; 25]` the permutation is tiny-keccak's.

On `[u8; 200]` it reads lane `i` from bytes `8 i` to `8 i + 7`, little-endian, permutes, and writes the lanes back the same way.

That is the byte order of FIPS 202, B.1, so the byte permutation is Keccak-f[1600] on the bit string of the bytes.
-/

open Aeneas Aeneas.Std CoreModels
open Plonky3Lean.Spec.Keccak Plonky3Lean.Lib

namespace Plonky3Lean.Proofs.Keccak

/-! ## Words -/

theorem permute_mut_eq (s : Std.Array Std.U64 25#usize) :
    p3_keccak.KeccakF.Insts.P3_symmetricPermutationPermutationArrayU6425.permute_mut () s =
      tiny_keccak.keccakf.keccakf s := by
  unfold p3_keccak.KeccakF.Insts.P3_symmetricPermutationPermutationArrayU6425.permute_mut
  rfl

theorem permute_mut_u64_eq (s : Std.Array Std.U64 25#usize) :
    p3_keccak.hax_roots.permute_mut_u64 s = tiny_keccak.keccakf.keccakf s := by
  unfold p3_keccak.hax_roots.permute_mut_u64
  exact permute_mut_eq s

/-- The impl of the permutation on words, field by field. -/
theorem inst_u64_eq : p3_keccak.KeccakF.Insts.P3_symmetricPermutationPermutationArrayU6425 =
    { corecloneCloneInst := p3_keccak.KeccakF.Insts.CoreCloneClone,
      corecloneCloneInst1 := core.Array.Insts.CoreCloneClone 25#usize core.U64.Insts.CoreCloneClone,
      permute := fun self input => p3_keccak.KeccakF.Insts.P3_symmetricPermutationPermutationArrayU6425.permute_mut
        self input,
      permute_mut := p3_keccak.KeccakF.Insts.P3_symmetricPermutationPermutationArrayU6425.permute_mut } := by
  unfold p3_keccak.KeccakF.Insts.P3_symmetricPermutationPermutationArrayU6425
  rfl

theorem permute_u64_eq (s : Std.Array Std.U64 25#usize) :
    p3_keccak.hax_roots.permute_u64 s = tiny_keccak.keccakf.keccakf s := by
  rw [p3_keccak.hax_roots.permute_u64, p3_symmetric.permutation.Permutation.permute.default.eq_1, inst_u64_eq]
  exact permute_mut_eq s

/-! ## Bytes -/

theorem u64_from_le_bytes_bv (a : Std.Array Std.U8 8#usize) :
    (Aeneas.Std.core.num.U64.from_le_bytes a).bv = wordOfBytes (a.val.map UScalar.bv) := by
  apply BitVec.eq_of_getLsbD_eq
  intro z hz
  rw [getLsbD_wordOfBytes _ _ hz]
  have ha := a.property
  rw [show (Aeneas.Std.core.num.U64.from_le_bytes a).bv =
      (BitVec.fromLEBytes (a.val.map UScalar.bv)).cast (by simp) from rfl, BitVec.getLsbD_cast,
    BitVec.getLsbD_eq_getElem (by simp [ha]; omega), BitVec.fromLEBytes_getElem]
  rw [List.getD_eq_getElem _ _ (by simp [ha]; omega)]
  rfl

/-- Bytes `8 k` to `8 k + 7` of a byte array, zero past the end. -/
def lane8 (b : Std.Array Std.U8 200#usize) (k : ℕ) : Std.Array Std.U8 8#usize :=
  Std.Array.from (((b.val.drop (8 * k)).take 8 ++ List.replicate 8 0#u8).take 8) (by simp)

theorem lane8_val (b : Std.Array Std.U8 200#usize) (k : ℕ) (hk : k < 25) :
    (lane8 b k).val = (b.val.drop (8 * k)).take 8 := by
  have hb := b.property
  simp only [lane8, Std.Array.from_val]
  rw [List.take_append_of_le_length (by simp [hb]; omega), List.take_take, Nat.min_self]

/-- The closure that reads lane `k` from the bytes. -/
theorem read_lane (c : Std.Array Std.U8 200#usize) (k : ℕ) (hk : k < 25) :
    p3_keccak.PermutationKeccakFArrayU8200.permute.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU64.call_mut c
        (usz k) =
      .ok (Aeneas.Std.core.num.U64.from_le_bytes (lane8 c k), c) := by
  have hc := c.property
  unfold p3_keccak.PermutationKeccakFArrayU8200.permute.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU64.call_mut
  rw (occs := .pos [1]) [show (8#usize : Std.Usize) = usz 8 from ofNatCore_eq_usz _ _ (by decide)]
  rw [usz_mul (by omega) (by omega) (by decide), bind_ok,
    index_rangeFrom_eq c _ (by rw [usz_val (by omega), hc]; simp; omega), bind_ok,
    index_rangeTo_eq _ _ (by simp [List.slice, usz_val (show k * 8 < 2 ^ 32 by omega), hc]; omega), bind_ok,
    try_from_eq _ _ _ (by simp [List.slice, usz_val (show k * 8 < 2 ^ 32 by omega), hc]; omega) (by decide)]
  simp only [bind_ok, CoreModels.core.result.Result.unwrap, CoreModels.core.num.U64.from_le_bytes,
    CoreModels.rust_primitives.arithmetic.from_le_bytes_u64]
  congr 3
  apply Std.Array.ext
  rw [lane8_val c k hk]
  simp [List.slice, usz_val (show k * 8 < 2 ^ 32 by omega), hc, Nat.mul_comm, List.take_take]

/-! ## Machine integers of known value -/

/-- The `u32` of value `k`. -/
def u32k (k : ℕ) : Std.U32 := ⟨BitVec.ofNat 32 k⟩

theorem u32k_val {k : ℕ} (h : k < 2 ^ 32) : (u32k k).val = k := by
  show (BitVec.ofNat 32 k).toNat = k
  rw [BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt h

theorem eq_u32k {x : Std.U32} {k : ℕ} (h : k < 2 ^ 32) (hx : x.val = k) : x = u32k k :=
  UScalar.eq_of_val_eq (by rw [hx, u32k_val h])

theorem cast_usz_u32k (j : ℕ) (h : j < 2 ^ 32) : UScalar.cast .U32 (usz j) = u32k j :=
  eq_u32k h (by rw [UScalar.cast_val_eq, usz_val h]; exact Nat.mod_eq_of_lt h)

theorem u32k_mul {a b : ℕ} (h : a * b < 2 ^ 32) (ha : a < 2 ^ 32) (hb : b < 2 ^ 32) :
    (u32k a * u32k b : RustM Std.U32) = .ok (u32k (a * b)) := by
  have hmax : (u32k a).val * (u32k b).val ≤ UScalar.max .U32 := by
    rw [u32k_val ha, u32k_val hb]
    simp only [UScalar.max, UScalarTy.U32_numBits_eq]
    omega
  obtain ⟨z, hz, hv⟩ := spec_imp_exists (UScalar.mul_spec hmax)
  rw [hz, eq_u32k (x := z) h (by rw [hv, u32k_val ha, u32k_val hb])]

theorem u32k_rem {a b : ℕ} (ha : a < 2 ^ 32) (hb : b < 2 ^ 32) (h0 : b ≠ 0) :
    (u32k a % u32k b : RustM Std.U32) = .ok (u32k (a % b)) := by
  obtain ⟨z, hz, hv⟩ := spec_imp_exists
    (UScalar.rem_spec (u32k a) (y := u32k b) (by rw [u32k_val hb]; exact h0))
  rw [hz, eq_u32k (x := z) (k := a % b) (by have := Nat.mod_le a b; omega)
    (by rw [hv, u32k_val ha, u32k_val hb])]

theorem u64_shr (x : Std.U64) (k : ℕ) (hk : k < 64) :
    (x >>> u32k k : RustM Std.U64) = .ok ⟨x.bv >>> k⟩ := by
  show UScalar.shiftRight_UScalar x _ = _
  simp only [UScalar.shiftRight_UScalar, UScalar.shiftRight, u32k_val (show k < 2 ^ 32 by omega)]
  rw [ite_eq_left_of_eq_true _ _ (eq_true (show k < UScalarTy.U64.numBits from hk))]
  rfl

theorem usz_div {a b : ℕ} (ha : a < 2 ^ 32) (hb : b < 2 ^ 32) (h0 : b ≠ 0) :
    (usz a / usz b : RustM Std.Usize) = .ok (usz (a / b)) := by
  obtain ⟨z, hz, hv⟩ := UScalar.div_spec (usz a) (y := usz b) (by rw [usz_val hb]; exact h0)
  rw [hz, eq_usz (x := z) (k := a / b) (by have := Nat.div_le_self a b; omega)
    (by rw [hv, usz_val ha, usz_val hb])]

/-- Byte `j` of the little-endian bytes of a word. -/
theorem le_byte (x : Std.U64) (j : ℕ) (hj : j < 8) :
    CoreModels.core.num.U64.to_le_bytes.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU8.call_mut x (usz j) =
      .ok (⟨x.bv.extractLsb' (8 * j) 8⟩, x) := by
  unfold CoreModels.core.num.U64.to_le_bytes.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU8.call_mut
  rw [show (8#u32 : Std.U32) = u32k 8 from eq_u32k (by decide) rfl,
    show (64#u32 : Std.U32) = u32k 64 from eq_u32k (by decide) rfl]
  simp only [lift_eq, bind_ok, cast_usz_u32k j (by omega), u32k_mul (show 8 * j < 2 ^ 32 by omega)
    (by decide) (by omega), u32k_rem (a := 8 * j) (b := 64) (by omega) (by decide) (by decide),
    Nat.mod_eq_of_lt (show 8 * j < 64 by omega), u64_shr x (8 * j) (by omega)]
  rfl

theorem to_le_bytes_eq (x : Std.U64) :
    CoreModels.core.num.U64.to_le_bytes x =
      .ok (Std.Array.from ((bytesOfWord x.bv).map fun b => ⟨b⟩) (by simp [bytesOfWord])) := by
  unfold CoreModels.core.num.U64.to_le_bytes
  rw [array_from_fn_eq 8#usize _ _ (fun j => ⟨x.bv.extractLsb' (8 * j) 8⟩) (fun j hj => le_byte x j hj)]
  simp only [bytesOfWord, List.map_map]
  rfl

theorem usz_div8 {k : ℕ} (hk : k < 2 ^ 32) : (usz k / 8#usize : RustM Std.Usize) = .ok (usz (k / 8)) := by
  rw [show (8#usize : Std.Usize) = usz 8 from ofNatCore_eq_usz _ _ (by decide)]
  exact usz_div hk (by decide) (by decide)

theorem usz_rem8 {k : ℕ} (hk : k < 2 ^ 32) : (usz k % 8#usize : RustM Std.Usize) = .ok (usz (k % 8)) := by
  rw [show (8#usize : Std.Usize) = usz 8 from ofNatCore_eq_usz _ _ (by decide)]
  exact usz_rem hk (by decide) (by decide)

/-- The closure that writes byte `k` from the lanes. -/
theorem write_byte (c : Std.Array Std.U64 25#usize) (k : ℕ) (hk : k < 200) :
    p3_keccak.PermutationKeccakFArrayU8200.permute.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeU8.call_mut c
        (usz k) =
      .ok (⟨((c.val.map UScalar.bv).flatMap bytesOfWord).getD k 0⟩, c) := by
  have hc := c.property
  unfold p3_keccak.PermutationKeccakFArrayU8200.permute.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeU8.call_mut
  rw [usz_div8 (by omega), bind_ok,
    index_usize_eq _ _ (by rw [usz_val (by omega), hc]; simp; omega), bind_ok, to_le_bytes_eq, bind_ok,
    usz_rem8 (by omega), bind_ok,
    index_usize_eq _ _ (by rw [usz_val (by omega)]; simp [bytesOfWord]; omega)]
  rw [getD_flatMap_uniform (m := 8) _ _ (fun _ => by simp [bytesOfWord]) _ _ 0 (by simp [hc]; omega)]
  simp [usz_val (show k / 8 < 2 ^ 32 by omega), usz_val (show k % 8 < 2 ^ 32 by omega),
    List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show k / 8 < c.val.length by rw [hc]; simp; omega),
    bytesOfWord, List.getElem?_range (show k % 8 < 8 by omega)]

theorem keccakf_eq (a : Std.Array Std.U64 25#usize) :
    tiny_keccak.keccakf.keccakf a =
      .ok (Std.Array.from (tiny_keccak.keccakf.rounds a.val) (rounds_eq a.val (by simp)).2) := by
  simp [tiny_keccak.keccakf.keccakf, (rounds_eq a.val (by simp)).2]

/-- The lanes the byte permutation reads are the little-endian words of the bytes. -/
theorem read_lanes_bv (b : Std.Array Std.U8 200#usize) :
    ((List.range 25).map fun k => Aeneas.Std.core.num.U64.from_le_bytes (lane8 b k)).map UScalar.bv =
      wordsOfBytes (b.val.map UScalar.bv) 25 := by
  simp only [List.map_map, wordsOfBytes]
  apply List.map_congr_left
  intro k hk
  simp only [Function.comp, u64_from_le_bytes_bv, lane8_val b k (List.mem_range.mp hk), List.map_take,
    List.map_drop]

/-- The bytes the byte permutation writes are the little-endian bytes of the lanes. -/
theorem write_bytes_bv (c : List Std.U64) (hc : c.length = 25) :
    ((List.range 200).map fun k => (⟨((c.map UScalar.bv).flatMap bytesOfWord).getD k 0⟩ : Std.U8)).map
        UScalar.bv = (c.map UScalar.bv).flatMap bytesOfWord := by
  apply List.ext_getElem (by
    rw [List.length_flatMap]; simp [bytesOfWord, Function.comp_def, List.map_const', hc])
  intro k h1 h2
  simp only [List.length_map, List.length_range] at h1
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2]

/-- The byte permutation is Keccak-f[1600] on the bit string of the bytes, read back as bytes (FIPS 202, B.1). -/
theorem permute_u8_spec (b : Std.Array Std.U8 200#usize) :
    ∃ out, p3_keccak.hax_roots.permute_u8 b = .ok out ∧
      out.val.map UScalar.bv = bytesOfBits (keccakF (bitsOfBytes (b.val.map UScalar.bv))) := by
  have hb := b.property
  unfold p3_keccak.hax_roots.permute_u8 p3_keccak.KeccakF.Insts.P3_symmetricPermutationPermutationArrayU8200.permute
  simp only [CoreModels.core.array.from_fn]
  rw [array_from_fn_eq 25#usize _ b _ (fun k hk => read_lane b k hk), bind_ok, keccakf_eq, bind_ok,
    array_from_fn_eq 200#usize _ _ _ (fun k hk => write_byte _ k hk)]
  refine ⟨_, rfl, ?_⟩
  obtain ⟨h1, h2⟩ := rounds_eq ((List.range 25).map fun k => Aeneas.Std.core.num.U64.from_le_bytes
        (lane8 b k)) (by simp)
  simp only [Std.Array.from_val, show (25#usize : Std.Usize).val = 25 from rfl,
    show (200#usize : Std.Usize).val = 200 from rfl]
  rw [write_bytes_bv _ h2, h1, read_lanes_bv,
    ← toBits_wordsOfBytes (b.val.map UScalar.bv) 25 (by simp [hb]), keccakF_toBits _ (by simp [wordsOfBytes]),
    bytesOfBits_toBits]

/-! ## The packed state with one lane -/

/-- The words of a one-lane packed state. -/
def unpack (st : Std.Array (Std.Array Std.U64 1#usize) 25#usize) : List Std.U64 :=
  st.val.map fun a => a.val.getD 0 0#u64

/-- A one-lane word. -/
def single (x : Std.U64) : Std.Array Std.U64 1#usize := Std.Array.from [x] rfl

/-- The one-lane packed state of 25 words. -/
def pack (w : List Std.U64) : Std.Array (Std.Array Std.U64 1#usize) 25#usize :=
  Std.Array.from ((List.range 25).map fun i => single (w.getD i 0#u64)) (by simp)

theorem length_unpack (st : Std.Array (Std.Array Std.U64 1#usize) 25#usize) : (unpack st).length = 25 := by
  simp [unpack]

theorem twentyfive_val : (25#usize : Std.Usize).val = 25 := rfl

/-- The words copied out of the packed state before step `k`. -/
def outWords (st : Std.Array (Std.Array Std.U64 1#usize) 25#usize) (k : ℕ) : Std.Array Std.U64 25#usize :=
  Std.Array.from ((unpack st).take k ++ List.replicate (25 - k) 0#u64) (by simp [length_unpack]; omega)

theorem copy_out_step (st : Std.Array (Std.Array Std.U64 1#usize) 25#usize) (k : ℕ) (hk : k < 25) :
    p3_keccak.hax_reshaped.permute_one_lane_loop0.body st { start := usz k, «end» := 25#usize } (outWords st k) =
      .ok (.cont ({ start := usz (k + 1), «end» := 25#usize }, outWords st (k + 1))) := by
  have hs := st.property
  unfold p3_keccak.hax_reshaped.permute_one_lane_loop0.body
  rw [CoreModels.core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next,
    range_step k _ (by rw [twentyfive_val]; exact hk), bind_ok]
  simp only [Aeneas.Std.uncurry_apply_pair]
  rw [index_usize_eq _ _ (by rw [usz_val (by omega), hs]; exact hk), bind_ok,
    index_usize_eq _ _ (by simp), bind_ok,
    update_eq _ _ _ (by simp [outWords, usz_val (show k < 2 ^ 32 by omega), length_unpack]; omega), bind_ok]
  congr 3
  apply Std.Array.ext
  simp only [outWords, Std.Array.from_val, usz_val (show k < 2 ^ 32 by omega)]
  apply List.ext_getElem (by simp [length_unpack]; omega)
  intro j h1 h2
  simp only [List.getElem_set, List.getElem_append, List.length_take, length_unpack, List.getElem_take,
    List.getElem_replicate]
  rcases Nat.lt_trichotomy j k with h | rfl | h
  · simp [show ¬ k = j by omega, show j < min k 25 by omega, show j < min (k + 1) 25 by omega]
  · simp [show j < min (j + 1) 25 by omega, unpack, List.getD_eq_getElem?_getD]
  · simp [show ¬ k = j by omega, show ¬ j < min k 25 by omega, show ¬ j < min (k + 1) 25 by omega]

theorem copy_out_done (st : Std.Array (Std.Array Std.U64 1#usize) 25#usize) :
    p3_keccak.hax_reshaped.permute_one_lane_loop0.body st { start := usz 25, «end» := 25#usize } (outWords st 25) =
      .ok (.done (Std.Array.from (unpack st) (length_unpack st))) := by
  unfold p3_keccak.hax_reshaped.permute_one_lane_loop0.body
  rw [CoreModels.core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next,
    range_next_none _ _ (by rw [twentyfive_val, usz_val (by decide)]), bind_ok]
  simp only [Aeneas.Std.uncurry_apply_pair]
  congr 2
  apply Std.Array.ext
  simp [outWords, length_unpack]

/-- The packed state after the words are copied back into its first `k` entries. -/
def inWords (w : Std.Array Std.U64 25#usize) (st : Std.Array (Std.Array Std.U64 1#usize) 25#usize) (k : ℕ) :
    Std.Array (Std.Array Std.U64 1#usize) 25#usize :=
  Std.Array.from ((List.range (min k 25)).map (fun i => single (w.val.getD i 0#u64)) ++ st.val.drop k)
    (by simp; omega)

theorem set_single (a : Std.Array Std.U64 1#usize) (i : ℕ) (hi : i = 0) (x : Std.U64) (h) :
    Std.Array.from (a.val.set i x) h = single x := by
  apply Std.Array.ext
  obtain ⟨y, hy⟩ := List.length_eq_one_iff.mp (a.property)
  simp [single, hy, hi]

theorem copy_in_step (w : Std.Array Std.U64 25#usize) (st : Std.Array (Std.Array Std.U64 1#usize) 25#usize)
    (k : ℕ) (hk : k < 25) :
    p3_keccak.hax_reshaped.permute_one_lane_loop1.body w { start := usz k, «end» := 25#usize } (inWords w st k) =
      .ok (.cont ({ start := usz (k + 1), «end» := 25#usize }, inWords w st (k + 1))) := by
  have hw := w.property
  unfold p3_keccak.hax_reshaped.permute_one_lane_loop1.body
  rw [CoreModels.core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next,
    range_step k _ (by rw [twentyfive_val]; exact hk), bind_ok]
  simp only [Aeneas.Std.uncurry_apply_pair]
  rw [index_usize_eq _ _ (by rw [usz_val (by omega), hw]; exact hk), bind_ok]
  simp only [Std.Array.index_mut_usize]
  have hi : (usz k).val < (inWords w st k).val.length := by
    rw [usz_val (by omega)]; simp only [inWords, Std.Array.from_val]; simp; omega
  rw [index_usize_eq _ _ hi]
  simp only [bind_tc_ok, bind_ok, Aeneas.Std.uncurry_apply_pair]
  rw [update_eq _ _ _ (by simp), bind_ok]
  congr 3
  apply Std.Array.ext
  simp only [Std.Array.set_val_eq, inWords, Std.Array.from_val, usz_val (show k < 2 ^ 32 by omega)]
  apply List.ext_getElem (by simp; omega)
  intro j h1 h2
  rw [List.getElem_set]
  split
  · subst j
    refine (set_single _ _ rfl _ _).trans ?_
    simp [List.getD_eq_getElem?_getD, hw, hk]
  · simp only [List.getElem_append, List.length_map, List.length_range, List.getElem_map,
      List.getElem_range, List.getElem_drop]
    rcases Nat.lt_or_ge j k with h | h
    · simp [show j < min k 25 by omega, show j < min (k + 1) 25 by omega]
    · simp [show ¬ j < min k 25 by omega, show ¬ j < min (k + 1) 25 by omega]
      congr 1
      omega

theorem copy_in_done (w : Std.Array Std.U64 25#usize) (st : Std.Array (Std.Array Std.U64 1#usize) 25#usize) :
    p3_keccak.hax_reshaped.permute_one_lane_loop1.body w { start := usz 25, «end» := 25#usize } (inWords w st 25) =
      .ok (.done (pack w.val)) := by
  unfold p3_keccak.hax_reshaped.permute_one_lane_loop1.body
  rw [CoreModels.core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next,
    range_next_none _ _ (by rw [twentyfive_val, usz_val (by decide)]), bind_ok]
  simp only [Aeneas.Std.uncurry_apply_pair]
  congr 2
  apply Std.Array.ext
  have hs := st.property
  simp [inWords, pack, hs]

theorem copy_out_loop (st : Std.Array (Std.Array Std.U64 1#usize) 25#usize) :
    p3_keccak.hax_reshaped.permute_one_lane_loop0 { start := usz 0, «end» := 25#usize } st (outWords st 0) =
      .ok (Std.Array.from (unpack st) (length_unpack st)) := by
  unfold p3_keccak.hax_reshaped.permute_one_lane_loop0
  exact loop_of_steps _ (fun k => (({ start := usz k, «end» := 25#usize } : CoreModels.core.ops.range.Range Std.Usize), outWords st k)) 25 _
    (fun k hk => copy_out_step st k hk) (copy_out_done st)

theorem copy_in_loop (w : Std.Array Std.U64 25#usize) (st : Std.Array (Std.Array Std.U64 1#usize) 25#usize) :
    p3_keccak.hax_reshaped.permute_one_lane_loop1 { start := usz 0, «end» := 25#usize } (inWords w st 0) w =
      .ok (pack w.val) := by
  unfold p3_keccak.hax_reshaped.permute_one_lane_loop1
  exact loop_of_steps _ (fun k => (({ start := usz k, «end» := 25#usize } : CoreModels.core.ops.range.Range Std.Usize), inWords w st k)) 25 _
    (fun k hk => copy_in_step w st k hk) (copy_in_done w st)

/-- The one-lane permutation: the words are copied out, permuted, and copied back. -/
theorem permute_one_lane_eq (st : Std.Array (Std.Array Std.U64 1#usize) 25#usize) :
    p3_keccak.hax_reshaped.permute_one_lane st = .ok (pack (tiny_keccak.keccakf.rounds (unpack st))) := by
  unfold p3_keccak.hax_reshaped.permute_one_lane
  rw [repeat_eq 25#usize _ 0#u64 (fun _ => rfl) (by decide), bind_ok]
  have h0 : Std.Array.from (List.replicate (25#usize : Std.Usize).val 0#u64) (by simp) = outWords st 0 := by
    apply Std.Array.ext; simp [outWords]
  have hi : st = inWords (Std.Array.from (tiny_keccak.keccakf.rounds (unpack st))
      (rounds_eq _ (length_unpack st)).2) st 0 := by
    apply Std.Array.ext; simp [inWords]
  rw [h0, show (0#usize : Std.Usize) = usz 0 from ofNatCore_eq_usz _ _ (by decide), copy_out_loop, bind_ok,
    permute_mut_eq, keccakf_eq, bind_ok]
  simp only [Std.Array.from_val]
  conv => lhs; arg 2; rw [hi]
  rw [copy_in_loop, Std.Array.from_val]

end Plonky3Lean.Proofs.Keccak