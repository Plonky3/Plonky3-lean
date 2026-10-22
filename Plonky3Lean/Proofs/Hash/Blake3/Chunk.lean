module

public import Plonky3Lean.Proofs.Hash.Blake3.Load

@[expose] public section

/-!
# p3-blake3 on the portable backend: chunks

A chunk compresses its plain blocks into the chaining value, then its last block with the end flag.
-/

open Aeneas Aeneas.Std CoreModels
open Plonky3Lean.Spec.Blake3 Plonky3Lean.Lib

namespace Plonky3Lean.Proofs.Blake3

/-- The chaining value after the first `k` plain blocks of the chunk at byte `a` of `B`. -/
def plainCv (B : List (BitVec 8)) (a counter : ℕ) : ℕ → List Word
  | 0 => IV
  | k + 1 => (compress (plainCv B a counter k) (blockWords (window B (a + 64 * k) 64)) counter 64
      (if k = 0 then CHUNK_START else 0)).take 8

theorem length_plainCv (B : List (BitVec 8)) (a counter k : ℕ) : (plainCv B a counter k).length = 8 := by
  cases k with
  | zero => rfl
  | succ k => simp [plainCv, compress]

theorem CHUNK_START_eq : p3_blake3.batch.compress.CHUNK_START = .ok ⟨CHUNK_START⟩ := by
  unfold p3_blake3.batch.compress.CHUNK_START
  rw [shiftLeft_i32_eq _ _ (by decide) (by decide)]
  rfl

theorem CHUNK_END_eq : p3_blake3.batch.compress.CHUNK_END = .ok ⟨CHUNK_END⟩ := by
  unfold p3_blake3.batch.compress.CHUNK_END
  rw [shiftLeft_i32_eq _ _ (by decide) (by decide)]
  rfl

theorem PARENT_eq : p3_blake3.batch.compress.PARENT = .ok ⟨PARENT⟩ := by
  unfold p3_blake3.batch.compress.PARENT
  rw [shiftLeft_i32_eq _ _ (by decide) (by decide)]
  rfl

theorem ROOT_eq : p3_blake3.batch.compress.ROOT = .ok ⟨ROOT⟩ := by
  unfold p3_blake3.batch.compress.ROOT
  rw [shiftLeft_i32_eq _ _ (by decide) (by decide)]
  rfl

theorem HASH_flags : p3_blake3.batch.Mode.HASH.flags = 0#u32 := by
  unfold p3_blake3.batch.Mode.HASH; rfl

theorem zero_or_u32 (x : Std.U32) : (0#u32 ||| x) = x := by
  rcases x with ⟨b⟩
  show (⟨0#UScalarTy.U32.numBits ||| b⟩ : Std.U32) = ⟨b⟩
  simp

theorem cast_64 : UScalar.cast .U32 (usz 64) = (⟨64⟩ : Std.U32) := cast_usz_u32 64 (by norm_num)

theorem plain_body (batch : Slice Std.U8) (s start k plain : ℕ) (counter : Std.U64) (hk : k < plain)
    (hB : s + start + 64 * plain ≤ batch.val.length) (h32 : batch.val.length + 64 < 2 ^ 32) :
    p3_blake3.batch.compress_plain_loop.body p3_blake3.U32.Insts.P3_blake3BatchLanesBackend1
      p3_blake3.batch.Mode.HASH batch (sts s) (usz s) (usz start) counter
      { start := usz k, «end» := usz plain } (grp 8#usize (plainCv (sbytes batch) (s + start) counter.val k)) =
      .ok (.cont ({ start := usz (k + 1), «end» := usz plain },
        grp 8#usize (plainCv (sbytes batch) (s + start) counter.val (k + 1)))) := by
  unfold p3_blake3.batch.compress_plain_loop.body
  have hl := load_parts_eq batch s s (start + k * 64) (by nlinarith) (by nlinarith) (by omega)
  simp only [CoreModels.core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next,
    range_step k (usz plain) (by rw [usz_val (by omega)]; exact hk), bind_ok, Aeneas.Std.uncurry_apply_pair,
    BLOCK_LEN_eq, usz_mul (show k * 64 < 2 ^ 32 by nlinarith) (by omega) (by norm_num),
    usz_add (show start + k * 64 < 2 ^ 32 by nlinarith), hl, lift_eq, cast_64, HASH_flags]
  have hf : (if usz k = 0#usize then p3_blake3.batch.compress.CHUNK_START else RustM.ok 0#u32) =
      .ok ⟨if k = 0 then CHUNK_START else 0⟩ := by
    by_cases h0 : k = 0
    · subst h0
      rw [ite_eq_left_of_eq_true _ _ (eq_true lit0.symm), CHUNK_START_eq]
      rfl
    · rw [ite_eq_right_of_eq_false _ _ (eq_false (fun h => h0 (by
        have := congrArg UScalar.val h
        rwa [usz_val (by omega)] at this))), ite_eq_right_of_eq_false _ _ (eq_false h0)]
      rfl
  rw [hf, bind_ok, zero_or_u32, wblock, compress_eq _ _ (length_plainCv ..) (by simp [blockWords]), bind_ok,
    show s + (start + k * 64) = s + start + 64 * k by ring]
  rfl

theorem plain_done (batch : Slice Std.U8) (s start plain : ℕ) (counter : Std.U64)
    (x : Std.Array (Std.Array Std.U32 8#usize) 1#usize) :
    p3_blake3.batch.compress_plain_loop.body p3_blake3.U32.Insts.P3_blake3BatchLanesBackend1
      p3_blake3.batch.Mode.HASH batch (sts s) (usz s) (usz start) counter
      { start := usz plain, «end» := usz plain } x = .ok (.done x) := by
  unfold p3_blake3.batch.compress_plain_loop.body
  simp only [CoreModels.core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next, range_stop,
    bind_ok, Aeneas.Std.uncurry_apply_pair]

theorem compress_plain_eq (batch : Slice Std.U8) (s start plain : ℕ) (counter : Std.U64)
    (hB : s + start + 64 * plain ≤ batch.val.length) (h32 : batch.val.length + 64 < 2 ^ 32) :
    p3_blake3.batch.compress_plain p3_blake3.U32.Insts.P3_blake3BatchLanesBackend1
      p3_blake3.batch.Mode.HASH batch (sts s) (usz s) (usz start) (usz plain) counter (grp 8#usize IV) =
      .ok (grp 8#usize (plainCv (sbytes batch) (s + start) counter.val plain)) := by
  unfold p3_blake3.batch.compress_plain p3_blake3.batch.compress_plain_loop
  rw [lit0]
  exact loop_of_steps (fun x : CoreModels.core.ops.range.Range Std.Usize ×
        Std.Array (Std.Array Std.U32 8#usize) 1#usize =>
      p3_blake3.batch.compress_plain_loop.body p3_blake3.U32.Insts.P3_blake3BatchLanesBackend1
        p3_blake3.batch.Mode.HASH batch (sts s) (usz s) (usz start) counter x.1 x.2)
    (fun k => (({ start := usz k, «end» := usz plain } : CoreModels.core.ops.range.Range Std.Usize),
      grp 8#usize (plainCv (sbytes batch) (s + start) counter.val k))) plain _
    (fun k hk => plain_body batch s start k plain counter hk hB h32) (plain_done _ _ _ _ _ _)

theorem usz_min (a b : ℕ) (ha : a < 2 ^ 32) (hb : b < 2 ^ 32) :
    CoreModels.core.Usize.Insts.CoreCmpOrd.min (usz a) (usz b) = .ok (usz (min a b)) := by
  simp only [CoreModels.core.Usize.Insts.CoreCmpOrd.min, CoreModels.core.cmp.Ord.min.default,
    CoreModels.core.cmp.min, CoreModels.core.Usize.Insts.CoreCmpOrd, CoreModels.core.mkUOrd,
    usz_val ha, usz_val hb]
  rcases Nat.lt_trichotomy a b with h | h | h
  · simp [compare_lt_iff_lt.mpr h, Nat.min_eq_left h.le]
  · subst h; simp
  · simp [compare_gt_iff_gt.mpr h, Nat.min_eq_right h.le]

theorem CHUNK_LEN_eq : blake3.CHUNK_LEN = .ok (usz 1024) := by
  unfold blake3.CHUNK_LEN; exact congrArg _ (eq_usz (by norm_num) rfl)

theorem cast_u64 (j : ℕ) (h : j < 2 ^ 32) : UScalar.cast .U64 (usz j) = (⟨BitVec.ofNat 64 j⟩ : Std.U64) :=
  UScalar.eq_of_val_eq (by
    rw [UScalar.cast_val_eq, usz_val h]
    show j % 2 ^ 64 = (BitVec.ofNat 64 j).toNat
    rw [BitVec.toNat_ofNat])

/-- The chaining value of chunk `idx` of the `len`-byte message at byte `s` of `B`, its last
compression flagged with `root` as well. -/
def chunkCv (B : List (BitVec 8)) (s len idx : ℕ) (root : Word) : List Word :=
  let start := idx * 1024
  let e := min len (start + 1024)
  let plain := (e - start - 1) / 64
  let tail := e - (start + plain * 64)
  (compress (plainCv B (s + start) idx plain) (blockWords (window B (s + (start + plain * 64)) tail)) idx
    (BitVec.ofNat 32 tail) ((if plain = 0 then CHUNK_START else 0) ||| CHUNK_END ||| root)).take 8

theorem usz_sat_sub_one (a : ℕ) (ha : a < 2 ^ 32) :
    CoreModels.core.num.Usize.saturating_sub (usz a) 1#usize = .ok (usz (a - 1)) := by
  rw [lit1]; exact usz_sat_sub a 1 ha (by norm_num)

theorem length_blockWords (x : List (BitVec 8)) : (blockWords x).length = 16 := by simp [blockWords]

theorem u32_or (x y : Std.U32) : (x ||| y) = ⟨x.bv ||| y.bv⟩ := rfl

theorem chunk_eq (batch : Slice Std.U8) (s len idx : ℕ) (root : Std.U32) (hidx : idx * 1024 ≤ len)
    (hB : s + len ≤ batch.val.length) (h32 : batch.val.length + 1024 < 2 ^ 32) :
    p3_blake3.batch.chunk p3_blake3.U32.Insts.P3_blake3BatchLanesBackend1 p3_blake3.batch.Mode.HASH
      (lane1 batch s) (usz len) (usz idx) root =
      .ok (grp 8#usize (chunkCv (sbytes batch) s len idx root.bv)) := by
  unfold p3_blake3.batch.chunk
  have hidx' : idx < 2 ^ 32 := by omega
  rw [CHUNK_LEN_eq, bind_ok, usz_mul (by omega) hidx' (by norm_num), bind_ok, usz_add (by omega), bind_ok,
    usz_min _ _ (by omega) (by omega), bind_ok, usz_sub (by omega) (by omega), bind_ok,
    usz_sat_sub_one _ (by omega), bind_ok,
    BLOCK_LEN_eq, bind_ok, usz_div (by omega) (by norm_num) (by norm_num), bind_ok, lift_eq, bind_ok,
    cast_u64 idx hidx', state_eq, bind_ok]
  unfold chunkCv
  generalize hst : idx * 1024 = st at hidx ⊢
  generalize he : min len (st + 1024) = e
  have he1 : e ≤ len := by omega
  have he2 : st ≤ e := by omega
  have he3 : e ≤ st + 1024 := by omega
  generalize hP : (e - st - 1) / 64 = P
  have hd := Nat.div_mul_le_self (e - st - 1) 64
  have hm := Nat.lt_div_mul_add (a := e - st - 1) (b := 64) (by norm_num)
  rw [hP] at hd hm
  have hP1 : st + P * 64 ≤ e := by omega
  have hP2 : e - (st + P * 64) ≤ 64 := by omega
  erw [compress_plain_eq batch s st P _ (by omega) (by omega)]
  rw [bind_ok, usz_mul (by omega) (by omega) (by norm_num), bind_ok, usz_add (by omega), bind_ok,
    usz_sub hP1 (by omega), bind_ok,
    last_block_eq batch s (st + P * 64) (e - (st + P * 64)) hP2 (by omega) (by omega),
    bind_ok]
  dsimp only
  rw [he, hP]
  have hc : (⟨BitVec.ofNat 64 idx⟩ : Std.U64).val = idx := by
    show (BitVec.ofNat 64 idx).toNat = idx
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  rw [hc]
  by_cases hP0 : P = 0
  · subst hP0
    rw [ite_eq_left_of_eq_true _ _ (eq_true lit0.symm)]
    simp only [CHUNK_START_eq, CHUNK_END_eq, bind_ok, lift_eq, HASH_flags,
      cast_usz_u32 _ (show e - (st + 0 * 64) < 2 ^ 32 by omega), wblock,
      compress_eq _ _ (length_plainCv ..) (length_blockWords _), u32_or, ite_true]
    rw [hc]
    rfl
  · rw [ite_eq_right_of_eq_false _ _ (eq_false (fun h => hP0 (by
      have := congrArg UScalar.val h
      rwa [usz_val (by omega)] at this)))]
    simp only [CHUNK_END_eq, bind_ok, lift_eq, HASH_flags,
      cast_usz_u32 _ (show e - (st + P * 64) < 2 ^ 32 by omega), wblock,
      compress_eq _ _ (length_plainCv ..) (length_blockWords _), u32_or, hP0, ite_false]
    rw [hc]
    rfl

end Plonky3Lean.Proofs.Blake3
