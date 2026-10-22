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

end Plonky3Lean.Proofs.Blake3
